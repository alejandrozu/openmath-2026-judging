"""Hold only the verified dispatcher main thread; reader threads keep pipes drained."""
import ctypes,hashlib,json,os,subprocess,sys,time
from pathlib import Path
from ctypes import wintypes as W
from receipt_io import read_bytes_shared
from resource_metrics import snapshot
from matt_resource_guard import THREADENTRY32,K
import shutil
BASE=Path(__file__).resolve().parent
PID=52644
K.GetThreadTimes.argtypes=[W.HANDLE]+[ctypes.POINTER(W.FILETIME)]*4;K.GetThreadTimes.restype=W.BOOL
K.SuspendThread.argtypes=[W.HANDLE];K.SuspendThread.restype=W.DWORD
K.GetExitCodeProcess.argtypes=[W.HANDLE,ctypes.POINTER(W.DWORD)];K.GetExitCodeProcess.restype=W.BOOL
K.OpenProcess.argtypes=[W.DWORD,W.BOOL,W.DWORD];K.OpenProcess.restype=W.HANDLE
def meta(pid):
    code=f"Get-CimInstance Win32_Process -Filter 'ProcessId = {pid}' | Select-Object ProcessId,ParentProcessId,CreationDate,CommandLine | ConvertTo-Json -Depth 3"
    out=subprocess.run(['powershell.exe','-NoProfile','-NonInteractive','-Command',code],capture_output=True,text=True,check=True).stdout
    return json.loads(out) if out.strip() else None
def verify_owner():
    owner=meta(PID);assert owner and owner['ProcessId']==PID
    assert 'run_source_plan.py htpeo-dms-current 1' in owner['CommandLine']
    return owner
def threads(pid):
    snap=K.CreateToolhelp32Snapshot(4,0);assert snap and snap!=ctypes.c_void_p(-1).value
    rows=[]
    try:
        e=THREADENTRY32();e.dwSize=ctypes.sizeof(e);ok=K.Thread32First(snap,ctypes.byref(e))
        while ok:
            if e.th32OwnerProcessID==pid:
                h=K.OpenThread(0x40|2,False,e.th32ThreadID);assert h
                times=[W.FILETIME() for _ in range(4)]
                try:
                    assert K.GetThreadTimes(h,*[ctypes.byref(t) for t in times])
                    rows.append({'tid':int(e.th32ThreadID),'created_filetime':(int(times[0].dwHighDateTime)<<32)|int(times[0].dwLowDateTime)})
                finally:K.CloseHandle(h)
            ok=K.Thread32Next(snap,ctypes.byref(e))
    finally:K.CloseHandle(snap)
    return sorted(rows,key=lambda r:r['created_filetime'])
def save(file,data):
    temp=file.with_suffix('.json.tmp');temp.write_text(json.dumps(data,indent=2),encoding='utf8');os.replace(temp,file)
def metrics():return {'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()}
def children():
    code=f"Get-CimInstance Win32_Process -Filter 'ParentProcessId = {PID}' | Where-Object Name -EQ 'lean.exe' | Select-Object ProcessId,ParentProcessId,CommandLine | ConvertTo-Json -Depth 3"
    out=subprocess.run(['powershell.exe','-NoProfile','-NonInteractive','-Command',code],capture_output=True,text=True,check=True).stdout
    data=json.loads(out) if out.strip() else []
    return data if isinstance(data,list) else [data]
if sys.argv[1]=='--resume':
    file=Path(sys.argv[2]);receipt=json.loads(file.read_text());owner=verify_owner()
    assert owner==receipt['owner_identity'],'Owner identity changed'
    main=next(t for t in threads(PID) if t['tid']==receipt['suspended_main_thread']['tid'])
    assert main==receipt['suspended_main_thread']
    h=K.OpenThread(0x40|2,False,main['tid']);assert h
    try:previous=K.ResumeThread(h);assert previous==1,previous
    finally:K.CloseHandle(h)
    resumed={'original_hold_receipt':str(file),'original_hold_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),
      'resumed_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'previous_suspension_count':int(previous),
      'held_wall_seconds':round(time.time()-receipt['hold_epoch'],3),'owner_identity':owner,'metrics':metrics()}
    out=file.with_name(file.stem+'.resumed.json');assert not out.exists();save(out,resumed);print(json.dumps(resumed),flush=True)
    raise SystemExit(0)
assert sys.argv[1]=='--hold'
owner=verify_owner();ts=threads(PID)
assert len(ts)>=3,'Dispatcher main plus independent stdout/stderr reader threads required'
assert ts[0]['created_filetime']<ts[1]['created_filetime'],'Main thread must be uniquely oldest'
main=ts[0];h=K.OpenThread(0x40|2,False,main['tid']);assert h
suspended=False;child_handle=None
file=BASE/('dms-dispatcher-hold-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'.json')
try:
    previous=K.SuspendThread(h);assert previous==0,previous;suspended=True
    raw=read_bytes_shared(BASE/'htpeo-dms-current-fresh-build.json');record=json.loads(raw)
    current=record.get('current_module');source=next(m for m in record['modules'] if m['module']==current)
    assert hashlib.sha256(Path(source['file']).read_bytes()).hexdigest()==source['sha256']
    kids=children();assert len(kids)<=1,'Only one directly owned DMS source compiler permitted'
    receipt={'status':'DISPATCHER_MAIN_THREAD_HELD_EXISTING_SOURCE_CHILD_FINISHING','owner_identity':owner,
      'owner_command_sha256':hashlib.sha256(owner['CommandLine'].encode()).hexdigest(),'suspended_main_thread':main,
      'other_threads_left_running':ts[1:],'pipes':'Original subprocess reader threads left running; no pipe/reader handle closed or suspended.',
      'source':source,'source_receipt_before_hold_sha256':hashlib.sha256(raw).hexdigest(),
      'recorded_cold_source_successes_before_hold':sum(r['exit']==0 and not r.get('is_endpoint_audit') for r in record['builds']),
      'hold_epoch':time.time(),'hold_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'metrics_before':metrics()}
    save(file,receipt)
    if kids:
        kid=kids[0];assert str(BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe').lower().replace('/','\\') in kid['CommandLine'].lower().replace('/','\\')
        assert Path(source['file']).name in kid['CommandLine']
        child_handle=K.OpenProcess(0x1000|0x00100000,False,kid['ProcessId']);assert child_handle
        receipt['child_identity']=kid;save(file,receipt)
        while True:
            code=W.DWORD();assert K.GetExitCodeProcess(child_handle,ctypes.byref(code))
            if code.value!=259:break
            if time.time()-receipt['hold_epoch']>1800:raise RuntimeError('Hold observer exceeded current-source completion bound')
            time.sleep(.5)
        receipt['actual_child_exit']=int(code.value);receipt['actual_child_exit_observed_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
    else:receipt['actual_child_exit']='NO_ACTIVE_CHILD_AT_VERIFIED_DISPATCH_BOUNDARY'
    assert not children(),'A DMS source child remains active'
    receipt['status']='DISPATCHER_HELD_NO_ACTIVE_DMS_SOURCE_CHILD';receipt['metrics_after_child_exit']=metrics()
    receipt['source_receipt_finalization']='Original dispatcher resumes later to save the untouched stdout/stderr buffers and row; external child exit is recorded separately.'
    save(file,receipt);print(str(file),flush=True);print(json.dumps(receipt),flush=True)
    suspended=False # Intentional recorded hold; only --resume releases this count.
finally:
    if child_handle:K.CloseHandle(child_handle)
    if suspended:K.ResumeThread(h)
    K.CloseHandle(h)
