"""Prepared owned-dispatcher handoff; OS process limit forbids any next child.

The real DMS action requires --execute after coordinator review.  The self-test
uses only a tiny synthetic Python dispatcher and invokes no Lean compiler.
"""
import ctypes,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path
from native_resource_guard import K,W,EXTENDEDLIMIT,stamp,save_once,processes
from matt_resource_guard import resume_suspended_root,THREADENTRY32
from resource_metrics import snapshot
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent
HOLD=BASE/'dms-dispatcher-hold-20261005T005041Z.json'
REPORT=BASE/'htpeo-dms-current-fresh-build.json'
ASSIGN_ACCESS=0x0001|0x0200|0x0100|0x1000|0x00100000
K.GetExitCodeProcess.argtypes=[W.HANDLE,ctypes.POINTER(W.DWORD)];K.GetExitCodeProcess.restype=W.BOOL
K.GetThreadTimes.argtypes=[W.HANDLE]+[ctypes.POINTER(W.FILETIME)]*4;K.GetThreadTimes.restype=W.BOOL

def verify_owner():
    command="Get-CimInstance Win32_Process -Filter 'ProcessId = 52644' | Select-Object ProcessId,ParentProcessId,CreationDate,CommandLine | ConvertTo-Json -Depth 3"
    raw=subprocess.run(['powershell.exe','-NoProfile','-NonInteractive','-Command',command],capture_output=True,text=True,check=True).stdout
    owner=json.loads(raw);assert owner['ProcessId']==52644
    assert 'run_source_plan.py htpeo-dms-current 1' in owner['CommandLine']
    return owner

def threads(pid):
    snap=K.CreateToolhelp32Snapshot(4,0);assert snap and snap!=ctypes.c_void_p(-1).value
    found=[]
    try:
        entry=THREADENTRY32();entry.dwSize=ctypes.sizeof(entry);ok=K.Thread32First(snap,ctypes.byref(entry))
        while ok:
            if entry.th32OwnerProcessID==pid:
                thread=K.OpenThread(0x40|2,False,entry.th32ThreadID);assert thread
                ts=[W.FILETIME() for _ in range(4)]
                try:
                    assert K.GetThreadTimes(thread,*[ctypes.byref(t) for t in ts])
                    found.append({'tid':int(entry.th32ThreadID),'created_filetime':(int(ts[0].dwHighDateTime)<<32)|int(ts[0].dwLowDateTime)})
                finally:K.CloseHandle(thread)
            ok=K.Thread32Next(snap,ctypes.byref(entry))
    finally:K.CloseHandle(snap)
    return found

def active_children():
    registry=processes();found=[]
    for pid,meta in registry.items():
        if meta['parent']!=52644:continue
        handle=K.OpenProcess(0x1000|0x00100000,False,pid)
        if not handle:continue
        try:
            code=W.DWORD();assert K.GetExitCodeProcess(handle,ctypes.byref(code))
            if code.value==259:found.append({'pid':pid,**meta})
        finally:K.CloseHandle(handle)
    return found

def sha(raw):return hashlib.sha256(raw).hexdigest()
def limited_job():
    job=K.CreateJobObjectW(None,None)
    if not job:raise ctypes.WinError(ctypes.get_last_error())
    limits=EXTENDEDLIMIT();limits.BasicLimitInformation.LimitFlags=0x00000008
    limits.BasicLimitInformation.ActiveProcessLimit=1
    if not K.SetInformationJobObject(job,9,ctypes.byref(limits),ctypes.sizeof(limits)):
        K.CloseHandle(job);raise ctypes.WinError(ctypes.get_last_error())
    verified=EXTENDEDLIMIT()
    assert K.QueryInformationJobObject(job,9,ctypes.byref(verified),ctypes.sizeof(verified),None)
    assert verified.BasicLimitInformation.ActiveProcessLimit==1
    assert verified.BasicLimitInformation.LimitFlags==0x00000008
    return job

def selftest():
    directory=BASE/'dms-boundary-selftest-v4';directory.mkdir(exist_ok=True)
    script=directory/'synthetic_dispatcher.py'
    text="""import json,subprocess,sys
from pathlib import Path
target=Path(sys.argv[1]);marker=Path(sys.argv[2])
target.write_text(json.dumps({'pending_row_flushed':True}))
try:
    subprocess.run([sys.executable,'-c',"from pathlib import Path;import sys;Path(sys.argv[1]).write_text('CHILD_EXECUTED')",str(marker)],check=True)
except OSError as error:
    target.write_text(json.dumps({'pending_row_flushed':True,'child_creation_refused':True,'winerror':error.winerror}))
    raise SystemExit(0)
raise SystemExit(99)
"""
    script.write_text(text,encoding='utf8');result=directory/'result.json'
    marker=directory/'forbidden-child-marker.txt'
    assert not result.exists() and not marker.exists(),'Self-test output already exists'
    out=directory/'stdout.txt';err=directory/'stderr.txt';job=limited_job();outer=K.CreateJobObjectW(None,None);assert outer;child=None
    try:
        with out.open('wb') as stdout,err.open('wb') as stderr:
            child=subprocess.Popen([sys.executable,str(script),str(result),str(marker)],stdout=stdout,stderr=stderr,
                                   creationflags=0x08000000|0x00000004)
            owned_handle=K.OpenProcess(ASSIGN_ACCESS,False,child.pid);assert owned_handle
            try:
                assert K.AssignProcessToJobObject(outer,owned_handle)
                assert K.AssignProcessToJobObject(job,owned_handle)
            finally:K.CloseHandle(owned_handle)
            resume_suspended_root(child.pid)
            assert child.wait(timeout=30)==0
        data=json.loads(result.read_text());assert data['pending_row_flushed'] and data['child_creation_refused'] and not marker.exists()
        receipt={'status':'SELF_TEST_PASS_NO_LEAN_OR_DMS_INVOCATION','finished_utc':stamp(),
            'synthetic_script_sha256':sha(script.read_bytes()),'result':data,
            'stdout_sha256':sha(out.read_bytes()),'stderr_sha256':sha(err.read_bytes()),
            'job_policy':'ActiveProcessLimit=1 only; no KILL_ON_JOB_CLOSE; root assigned before initial resume.',
            'nested_job_assignment':'PASS outer unrestricted job then inner process-only limit',
            'tested_openprocess_access_mask':ASSIGN_ACCESS,
            'forbidden_child_marker_exists':marker.exists(),
            'helper_sha256':sha(Path(__file__).read_bytes())}
        save_once(BASE/'dms-pending-row-boundary-selftest-v4.json',receipt);print(json.dumps(receipt),flush=True)
    finally:
        if child and child.poll() is None:child.kill();child.wait()
        K.CloseHandle(job);K.CloseHandle(outer)

def execute():
    tested=json.loads((BASE/'dms-pending-row-boundary-selftest-v4.json').read_text())
    assert tested['status']=='SELF_TEST_PASS_NO_LEAN_OR_DMS_INVOCATION'
    assert tested['helper_sha256']==sha(Path(__file__).read_bytes())
    hold=json.loads(HOLD.read_text());owner=verify_owner();assert owner==hold['owner_identity']
    assert not active_children(),'No active source child may be present'
    main=hold['suspended_main_thread'];assert main in threads(owner['ProcessId'])
    before=read_bytes_shared(REPORT);record=json.loads(before)
    assert record['status']=='RUNNING' and record['current_module']=='GPn2T'
    assert len(record['builds'])==117 and all(row['exit']==0 for row in record['builds'])
    assert sha(Path(hold['source']['file']).read_bytes())==hold['source']['sha256']
    checkpoint=BASE/('dms-pending-row-handoff-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'.json')
    preserved=checkpoint.with_suffix('.before-receipt.json');preserved.write_bytes(before)
    job=limited_job();handle=K.OpenProcess(ASSIGN_ACCESS,False,owner['ProcessId'])
    assert handle
    row={'status':'PREPARED_DMS_DISPATCHER_ONLY_JOB_BOUNDARY','started_utc':stamp(),'owner_identity':owner,
        'hold_receipt':str(HOLD),'hold_sha256':sha(HOLD.read_bytes()),'original_receipt':str(preserved),
        'original_receipt_sha256':sha(before),'source':hold['source'],
        'job_policy':'ActiveProcessLimit=1; dispatcher only; no kill-on-close; no source child may execute.',
        'helper_sha256':sha(Path(__file__).read_bytes()),'metrics_before':{'disk':shutil.disk_usage(BASE).free,**snapshot()}}
    save_once(checkpoint,row)
    try:
        if not K.AssignProcessToJobObject(job,handle):raise ctypes.WinError(ctypes.get_last_error())
        th=K.OpenThread(0x40|2,False,main['tid']);assert th
        try:assert K.ResumeThread(th)==1
        finally:K.CloseHandle(th)
        began=time.monotonic()
        while True:
            code=W.DWORD();assert K.GetExitCodeProcess(handle,ctypes.byref(code))
            if code.value!=259:break
            assert time.monotonic()-began<60,'Dispatcher did not exit at controlled boundary'
            time.sleep(.1)
        after=read_bytes_shared(REPORT);updated=json.loads(after)
        assert updated['builds'][:117]==record['builds'],'Original successful rows changed'
        assert len(updated['builds'])==118 and updated['builds'][-1]['module']=='GPn2T' and updated['builds'][-1]['exit']==0
        assert not active_children(),'New source child unexpectedly present'
        row.update(status='PENDING_ORIGINAL_ROW_FLUSHED_OS_REFUSED_NEXT_CHILD',finished_utc=stamp(),
          dispatcher_exit=int(code.value),completed_source_rows=118,
          flushed_row=updated['builds'][-1],after_receipt_sha256=sha(after),
          pending_next_module=updated.get('current_module'),held_wall_seconds=time.time()-hold['hold_epoch'],
          metrics_after={'disk':shutil.disk_usage(BASE).free,**snapshot()},
          qualification='Next child was refused operationally, not a Lean proof failure. Original 117 rows and buffered GPn2T output are preserved.')
        out=checkpoint.with_suffix('.completed.json');save_once(out,row);print(json.dumps({'receipt':str(out),'status':row['status'],'rows':118}),flush=True)
    finally:
        K.CloseHandle(handle);K.CloseHandle(job)

if __name__=='__main__':
    if sys.argv[1]=='--selftest':selftest()
    elif sys.argv[1]=='--execute':execute()
    else:raise SystemExit('Use --selftest or explicitly reviewed --execute')
