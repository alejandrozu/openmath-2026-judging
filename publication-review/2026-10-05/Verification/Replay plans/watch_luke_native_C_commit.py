"""Continuous available-commit floor for the one identified native C worker tree.

No system settings, user applications, or mathematical Lean workers are changed.
The exact worker PID and creation time prevent a reused PID from being killed.
"""
from pathlib import Path
import argparse,ctypes,datetime,hashlib,json,os,subprocess,time
from native_resource_guard import K,W,MEMORYSTATUSEX,processes,own_tree,memory,GIB
from receipt_io import read_bytes_shared

B=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--pid',type=int,required=True);args=parser.parse_args()
K.GetProcessTimes.argtypes=[W.HANDLE,ctypes.POINTER(W.FILETIME),ctypes.POINTER(W.FILETIME),ctypes.POINTER(W.FILETIME),ctypes.POINTER(W.FILETIME)];K.GetProcessTimes.restype=W.BOOL
def born(pid):
    h=K.OpenProcess(0x1000,False,pid)
    if not h:return None
    try:
        a,b,c,d=W.FILETIME(),W.FILETIME(),W.FILETIME(),W.FILETIME()
        if not K.GetProcessTimes(h,ctypes.byref(a),ctypes.byref(b),ctypes.byref(c),ctypes.byref(d)):return None
        return (int(a.dwHighDateTime)<<32)+int(a.dwLowDateTime)
    finally:K.CloseHandle(h)
def committed():
    s=MEMORYSTATUSEX();s.dwLength=ctypes.sizeof(s)
    if not K.GlobalMemoryStatusEx(ctypes.byref(s)):raise OSError('GlobalMemoryStatusEx failed')
    return {'available_commit_bytes':int(s.ullAvailPageFile),'current_commit_limit_bytes':int(s.ullTotalPageFile),'available_physical_bytes':int(s.ullAvailPhys)}
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
created=born(args.pid);assert created is not None,'Identified own C worker is not alive'
command=subprocess.run(['powershell','-NoProfile','-Command',f"Get-CimInstance Win32_Process -Filter 'ProcessId={args.pid}' | Select-Object -ExpandProperty CommandLine"],capture_output=True,text=True,encoding='utf8')
assert command.returncode==0 and 'run_luke_isolated_native_preparation.py' in command.stdout and '--stage objects' in command.stdout,'Refuse to watch an unidentified or non-C-preparation process'
first=committed();record={'started_utc':stamp(),'status':'WATCHING','own_root_pid':args.pid,'own_root_creation_FILETIME':created,
    'verified_command_line':command.stdout.strip(),'floor_available_commit_bytes':GIB,'poll_seconds':.25,
    'counter':'Verified 64-byte Win64 MEMORYSTATUSEX via GlobalMemoryStatusEx; ullAvailPageFile/ullTotalPageFile; no pagefile or OS changes',
    'initial_counters':first,'minimum_available_commit_bytes':first['available_commit_bytes'],'minimum_available_physical_bytes':first['available_physical_bytes'],
    'minimum_current_commit_limit_bytes':first['current_commit_limit_bytes'],'samples':0,'guard_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope':'Only this exact own native C-preparation Python process and its descendants; original Luke/DMS/A000 Lean workers are outside this tree'}
p=B/('luke-native-C-commit-guard-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'.json')
def save():
    tmp=p.with_suffix('.json.tmp')
    with tmp.open('w',encoding='utf8') as f:json.dump(record,f,indent=2);f.flush();os.fsync(f.fileno())
    os.replace(tmp,p)
save();lastsave=time.monotonic()
while True:
    nowborn=born(args.pid)
    if nowborn is None:record['status']='OWN_C_WORKER_FINISHED_GUARD_RELEASED';break
    if nowborn!=created:record['status']='OWN_C_WORKER_ENDED_PID_REUSED_NO_ACTION';break
    s=committed();record['samples']+=1
    record['minimum_available_commit_bytes']=min(record['minimum_available_commit_bytes'],s['available_commit_bytes'])
    record['minimum_available_physical_bytes']=min(record['minimum_available_physical_bytes'],s['available_physical_bytes'])
    record['minimum_current_commit_limit_bytes']=min(record['minimum_current_commit_limit_bytes'],s['current_commit_limit_bytes'])
    if s['available_commit_bytes']<GIB:
        registry=processes();tree=own_tree(args.pid,registry)
        record['status']='ENVIRONMENT_BLOCKED_AVAILABLE_COMMIT_RESERVE';record['stop_counters']=s
        record['stopped_own_tree']=[{'pid':pid,'exe':registry.get(pid,{}).get('exe'),'memory':memory(pid)} for pid in sorted(tree)]
        receipt=read_bytes_shared(B/'luke-native-isolated-preparation.json')
        record['last_preparation_receipt_sha256']=hashlib.sha256(receipt).hexdigest()
        record['last_preparation_operation']=json.loads(receipt).get('current_operation')
        result=subprocess.run(['taskkill','/PID',str(args.pid),'/T','/F'],capture_output=True,text=True,encoding='utf8')
        record['own_tree_stop_command']=['taskkill','/PID',str(args.pid),'/T','/F'];record['stop_command_exit']=result.returncode
        record['stop_command_stdout']=result.stdout;record['stop_command_stderr']=result.stderr
        break
    if time.monotonic()-lastsave>=30:record['last_checked_utc']=stamp();record['last_counters']=s;save();lastsave=time.monotonic()
    time.sleep(.25)
record['finished_utc']=stamp();record['last_counters']=committed();save()
print(json.dumps({'guard_receipt':str(p),**record},indent=2),flush=True)
