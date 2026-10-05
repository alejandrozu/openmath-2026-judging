"""Prepared storage-only own-output guard core; no standalone operation."""
from pathlib import Path
from datetime import datetime,timezone
from ctypes import wintypes as W
import ctypes,hashlib,json,mmap,os,shutil,subprocess,time
from native_resource_guard import K,EXTENDEDLIMIT,memory,processes,own_tree
from matt_resource_guard import resume_suspended_root
from resource_metrics import snapshot
BASE=Path(__file__).resolve().parent
GIB=2**30
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()

def stamp():return datetime.now(timezone.utc).isoformat()

def write_new(p,d):
    with Path(p).open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')

def wof_info(p):
    dll=ctypes.WinDLL('Wofutil.dll');fn=dll.WofIsExternalFile
    fn.argtypes=[W.LPCWSTR,ctypes.POINTER(W.BOOL),ctypes.POINTER(W.ULONG),ctypes.c_void_p,ctypes.POINTER(W.ULONG)]
    fn.restype=ctypes.c_long
    external=W.BOOL();provider=W.ULONG();buf=ctypes.create_string_buffer(64);length=W.ULONG(64)
    result=fn(str(p),ctypes.byref(external),ctypes.byref(provider),buf,ctypes.byref(length))
    assert result==0 and length.value<=64
    return {'HRESULT':result,'external':bool(external.value),'provider':provider.value,
        'info_length':length.value,'info_hex':buf.raw[:length.value].hex(),
        'algorithm':int.from_bytes(buf.raw[:4],'little') if external.value and provider.value==2 else None}

def read_and_mmap(p):
    ordinary=sha(p)
    with Path(p).open('rb') as f:
        with mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as mm:mapped=hashlib.sha256(mm).hexdigest()
    assert ordinary==mapped
    return {'ordinary_read_sha256':ordinary,'Windows_read_only_mmap_sha256':mapped,'byte_equality':True}

def quiescence(completed_lean_root_pid):
    cmd="Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake|leantar|compact|python|clang|lld|7z|tar)\\.exe$' } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Compress"
    r=subprocess.run(['powershell','-NoProfile','-Command',cmd],capture_output=True,text=True,encoding='utf8',errors='replace',check=True)
    rows=json.loads(r.stdout or '[]');rows=[rows] if isinstance(rows,dict) else rows
    blocked=[]
    for row in rows:
        if row['ProcessId']==os.getpid():continue # reviewed source runner owns its replay lock
        cli=(row.get('CommandLine') or '').lower();name=row['Name'].lower()
        if row['ProcessId']==completed_lean_root_pid:
            blocked.append(row)
        elif name in {'compact.exe','leantar.exe','7z.exe','tar.exe'}:
            blocked.append(row)
        elif any(t in cli for t in ('sakana-a000224','quadraticresidue224','compress_','compact_','cache get','force_official_cache')):
            blocked.append(row)
    assert not blocked,('Own source job/readers or competing compressor must actually exit before output compression',blocked)
    return rows

def gates(target):
    m=snapshot();disk=shutil.disk_usage(BASE).free
    assert disk>=4_000_000_000 and m['free_physical_bytes']>=6*GIB and m['available_commit_bytes']>=5*GIB
    assert disk-target.stat().st_size>=1_000_000_000
    return {'disk_free_bytes':disk,**m}

def guarded_compact(command,prefix,target,completed_pid):
    initial=gates(target);registry=quiescence(completed_pid)
    out=BASE/(prefix+'.stdout.bin');err=BASE/(prefix+'.stderr.bin')
    assert not out.exists() and not err.exists()
    job=K.CreateJobObjectW(None,None);assert job
    limits=EXTENDEDLIMIT();limits.BasicLimitInformation.LimitFlags=0x2000|0x100|0x200
    limits.ProcessMemoryLimit=256*2**20;limits.JobMemoryLimit=256*2**20
    assert K.SetInformationJobObject(job,9,ctypes.byref(limits),ctypes.sizeof(limits))
    row={'command':command,'started_utc':stamp(),'initial_counters':initial,'preflight_processes':registry,
        'own_process_and_job_cap_bytes':256*2**20,'minimum_disk_free_bytes':initial['disk_free_bytes'],
        'minimum_physical_available_bytes':initial['free_physical_bytes'],'minimum_available_commit_bytes':initial['available_commit_bytes']}
    proc=None;stop=None;start=time.monotonic();peak_private=peak_rss=0
    try:
        with out.open('xb') as stdout,err.open('xb') as stderr:
            proc=subprocess.Popen(command,cwd=BASE,stdout=stdout,stderr=stderr,creationflags=0x08000000|0x4)
            if not K.AssignProcessToJobObject(job,W.HANDLE(int(proc._handle))):
                proc.kill();proc.wait(timeout=15);raise ctypes.WinError(ctypes.get_last_error())
            row.update(owned_pid=proc.pid,created_suspended=True,assigned_to_own_job_before_resume=True)
            resume_suspended_root(proc.pid)
            while True:
                tree=own_tree(proc.pid,processes());metrics=[m for pid in tree if (m:=memory(pid))]
                peak_private=max(peak_private,sum(m['private_bytes'] for m in metrics));peak_rss=max(peak_rss,sum(m['rss_bytes'] for m in metrics))
                m=snapshot();disk=shutil.disk_usage(BASE).free
                row['minimum_disk_free_bytes']=min(row['minimum_disk_free_bytes'],disk)
                row['minimum_physical_available_bytes']=min(row['minimum_physical_available_bytes'],m['free_physical_bytes'])
                row['minimum_available_commit_bytes']=min(row['minimum_available_commit_bytes'],m['available_commit_bytes'])
                if disk<1_000_000_000:stop='DISK_RESERVE'
                elif m['free_physical_bytes']<3*GIB:stop='PHYSICAL_RESERVE'
                elif m['available_commit_bytes']<GIB:stop='COMMIT_RESERVE'
                elif time.monotonic()-start>180:stop='OWN_STORAGE_OPERATION_TIMEOUT'
                if stop:K.TerminateJobObject(job,77);proc.wait(timeout=15);break
                if proc.poll() is not None:break
                time.sleep(.1)
            proc.wait(timeout=15)
            final=EXTENDEDLIMIT();assert K.QueryInformationJobObject(job,9,ctypes.byref(final),ctypes.sizeof(final),None)
            row.update(exit=proc.returncode,job_peak_private_bytes=int(final.PeakJobMemoryUsed),process_peak_private_bytes=int(final.PeakProcessMemoryUsed))
    except Exception as error:
        stop='OWN_STORAGE_OPERATIONAL_ERROR';row['operational_error']=str(error)
    finally:
        if proc is not None and proc.poll() is None:K.TerminateJobObject(job,78);proc.wait(timeout=15)
        K.CloseHandle(job)
    row.update(finished_utc=stamp(),seconds=round(time.monotonic()-start,3),stop_reason=stop,
        polled_peak_private_bytes=peak_private,polled_peak_rss_bytes=peak_rss,stdout_file=str(out),stderr_file=str(err),
        stdout_sha256=sha(out) if out.exists() else None,stderr_sha256=sha(err) if err.exists() else None,
        stdout=out.read_bytes().decode('mbcs',errors='replace') if out.exists() else None,
        stderr=err.read_bytes().decode('mbcs',errors='replace') if err.exists() else None)
    return row

if __name__=="__main__":raise SystemExit("Prepared guard library only; no standalone operation.")
