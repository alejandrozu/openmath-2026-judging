"""Prepared reversible one-file LZX pilot; no operation without SHA-bound root approval.

Never invokes Lean, deletes evidence, changes sources, touches shared/active output,
or applies directory/global compression. Only its exact approved file is operated on.
"""
from pathlib import Path
from datetime import datetime, timezone
from ctypes import wintypes as W
import ctypes, hashlib, json, mmap, msvcrt, os, shutil, subprocess, sys, time
from native_resource_guard import K, EXTENDEDLIMIT, memory, processes, own_tree
from matt_resource_guard import resume_suspended_root
from resource_metrics import snapshot

BASE=Path(__file__).resolve().parent
PROPOSAL=BASE/'completed-own-HTRamsey-B0-strong-LZX-single-pilot-preparation-20261005.json'
TARGET=BASE/'builds/htpeo-ramsey-current/RamseyCert/Chunk/B0.olean'
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
def metadata(proposal):
    p=BASE/'assess_completed_own_artifact_storage_readonly.py'
    assert sha(p)==proposal['native_metadata_helper_sha256']
    prefix,marker,_=p.read_text(encoding='utf8').partition('before_processes=process_snapshot()');assert marker
    ns={'__file__':str(p),'__name__':'reviewed_native_metadata_definitions_only'}
    exec(compile(prefix,str(p),'exec'),ns)
    return ns['native_metadata']
def exact_identity(a,b):
    return all(a[k]==b[k] for k in ('volume_serial','file_index_high','file_index_low','link_count','last_write_FILETIME','logical_bytes'))
def quiescence():
    cmd="Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake|leantar|compact|python|clang|lld|7z|tar)\\.exe$' } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Compress"
    r=subprocess.run(['powershell','-NoProfile','-Command',cmd],capture_output=True,text=True,encoding='utf8',errors='replace',check=True)
    records=json.loads(r.stdout or '[]');records=[records] if isinstance(records,dict) else records
    blocked=[]
    for row in records:
        if row['ProcessId']==os.getpid():continue
        cli=(row.get('CommandLine') or '').lower();name=row['Name'].lower()
        if name in {'compact.exe','leantar.exe','7z.exe','tar.exe'} or 'htpeo-ramsey-current' in cli or 'ramseycert' in cli:
            blocked.append(row)
        elif any(x in cli for x in ('compress_','compact_','cache get','force_official_cache')):blocked.append(row)
    assert not blocked,('Family writer/reader or compressor/extractor must be quiescent',blocked)
    return records
def gates():
    m=snapshot();disk=shutil.disk_usage(BASE).free
    assert disk>=4_000_000_000 and m['free_physical_bytes']>=6*GIB and m['available_commit_bytes']>=5*GIB
    assert disk-TARGET.stat().st_size>=1_000_000_000
    return {'disk_free_bytes':disk,**m}

def guarded_command(command,prefix):
    initial=gates();registry=quiescence();out=BASE/(prefix+'.stdout.bin');err=BASE/(prefix+'.stderr.bin')
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
                elif time.monotonic()-start>180:stop='OWN_STORAGE_PILOT_TIMEOUT'
                if stop:K.TerminateJobObject(job,77);proc.wait(timeout=15);break
                if proc.poll() is not None:break
                time.sleep(.1)
            proc.wait(timeout=15)
            final=EXTENDEDLIMIT();assert K.QueryInformationJobObject(job,9,ctypes.byref(final),ctypes.sizeof(final),None)
            row.update(exit=proc.returncode,job_peak_private_bytes=int(final.PeakJobMemoryUsed),
                process_peak_private_bytes=int(final.PeakProcessMemoryUsed))
    except Exception as error:
        stop='OWN_STORAGE_PILOT_OPERATIONAL_ERROR';row['operational_error']=str(error)
    finally:
        if proc is not None and proc.poll() is None:K.TerminateJobObject(job,78);proc.wait(timeout=15)
        K.CloseHandle(job)
    row.update(finished_utc=stamp(),seconds=round(time.monotonic()-start,3),stop_reason=stop,
        polled_peak_private_bytes=peak_private,polled_peak_rss_bytes=peak_rss,stdout_file=str(out),stderr_file=str(err),
        stdout_sha256=sha(out) if out.exists() else None,stderr_sha256=sha(err) if err.exists() else None,
        stdout=out.read_bytes().decode('mbcs',errors='replace') if out.exists() else None,
        stderr=err.read_bytes().decode('mbcs',errors='replace') if err.exists() else None)
    return row

def execute(mode,approval_path,approval_sha):
    approval_path=Path(approval_path).resolve();assert approval_path.is_relative_to(BASE) and sha(approval_path)==approval_sha
    approval=json.loads(approval_path.read_bytes());assert approval['reviewed_helper_sha256']==sha(__file__)
    assert sha(PROPOSAL)==approval['reviewed_proposal_sha256'];proposal=json.loads(PROPOSAL.read_bytes())
    assert proposal['helper_sha256']==sha(__file__)
    assert TARGET.resolve()==Path(proposal['exact_target']).resolve()
    assert TARGET.resolve().is_relative_to(BASE/'builds/htpeo-ramsey-current') and not TARGET.is_symlink()
    for p,h in proposal['frozen_input_bindings'].items():assert sha(p)==h
    compact=Path(os.environ['SystemRoot'])/'System32/compact.exe';assert sha(compact)==proposal['compact_executable_sha256']
    native=metadata(proposal);before=native(TARGET);backing=wof_info(TARGET);read=read_and_mmap(TARGET)
    assert before['link_count']==1 and not before['FILE_ATTRIBUTE_ENCRYPTED']
    assert exact_identity(before,proposal['native_before'])
    assert read['ordinary_read_sha256']==proposal['content_sha256_before']
    if mode=='compress':
        assert approval['status']=='ROOT_APPROVED_ONE_COMPLETED_OWN_OUTPUT_STRONG_LZX_PILOT'
        assert not backing['external'] and before['FILE_ATTRIBUTE_COMPRESSED'] and not before['FILE_ATTRIBUTE_REPARSE_POINT']
        commands=[[str(compact),'/C','/F','/Q','/EXE:LZX',str(TARGET)]]
    else:
        assert mode=='restore' and approval['status']=='ROOT_APPROVED_EXACT_STRONG_LZX_PILOT_ORDINARY_NTFS_RESTORATION'
        actual=Path(approval['actual_pilot_receipt']).resolve();assert actual.is_relative_to(BASE)
        assert sha(actual)==approval['actual_pilot_receipt_sha256'];d=json.loads(actual.read_bytes())
        assert d['status']=='PASS_BYTE_IDENTICAL_READABLE_STRONG_LZX_PILOT' and d['helper_sha256']==sha(__file__)
        assert exact_identity(before,d['native_after']) and backing==d['WOF_after']
        assert backing['external'] and backing['provider']==2 and backing['algorithm']==1
        commands=[[str(compact),'/U','/EXE','/Q',str(TARGET)],[str(compact),'/C','/F','/Q',str(TARGET)]]
    assert approval['reviewed_exact_commands']==commands
    quiescence();gates()
    # Hold the existing HT replay byte lock; no source dispatcher may overlap this pilot.
    replay_lock=BASE/'builds/htpeo-ramsey-current/.fresh-replay.lock'
    assert replay_lock.is_file() and replay_lock.stat().st_size==1
    replay=replay_lock.open('r+b');replay.seek(0)
    try:msvcrt.locking(replay.fileno(),msvcrt.LK_NBLCK,1)
    except OSError:
        replay.close();raise RuntimeError('HT dispatcher still owns its replay lock')
    # An exclusive named mutex has no disk evidence to remove and is released on process exit.
    K.CreateMutexW.argtypes=[ctypes.c_void_p,W.BOOL,W.LPCWSTR];K.CreateMutexW.restype=W.HANDLE
    mutex=K.CreateMutexW(None,True,'Local\\OpenMathSingleCompletedOutputStoragePilot')
    assert mutex and ctypes.get_last_error()!=183,'Another reviewed own storage operation holds the mutex'
    serial=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    record={'status':'STARTED_EXACT_SINGLE_FILE_'+mode.upper(),'started_utc':stamp(),'helper_sha256':sha(__file__),
        'root_approval':str(approval_path),'root_approval_sha256':approval_sha,'proposal_sha256':sha(PROPOSAL),
        'target':str(TARGET),'native_before':before,'WOF_before':backing,'read_and_mmap_before':read,
        'resource_policy':'256MiB ownjob/process; dispatch4GBdisk/6GiBphysical/5GiBcommit; continuous1GBdisk/3GiBphysical/1GiBcommit;180spercommand',
        'commands':commands,'compact_executable_sha256':sha(compact),'frozen_input_bindings':proposal['frozen_input_bindings'],
        'sources_runtime_providers_DMS_shared_or_other_output_targets':0}
    write_new(BASE/(serial+'-single-own-output-'+mode+'-started.json'),record)
    rows=[]
    try:
        for n,cmd in enumerate(commands):
            r=guarded_command(cmd,serial+'-single-own-output-'+mode+'-'+str(n));rows.append(r)
            if r.get('exit')!=0 or r['stop_reason']:break
        after=native(TARGET);wafter=wof_info(TARGET);read_after=read_and_mmap(TARGET)
        same=exact_identity(before,after) and read_after['ordinary_read_sha256']==read['ordinary_read_sha256']
        for p,h in proposal['frozen_input_bindings'].items():assert sha(p)==h
        successful=len(rows)==len(commands) and all(r.get('exit')==0 and not r['stop_reason'] for r in rows)
        state_ok=(wafter['external'] and wafter['provider']==2 and wafter['algorithm']==1) if mode=='compress' else (not wafter['external'] and after['FILE_ATTRIBUTE_COMPRESSED'] and not after['FILE_ATTRIBUTE_REPARSE_POINT'])
        record.update(native_after=after,WOF_after=wafter,read_and_mmap_after=read_after,actual_command_rows=rows,
            content_inode_linkcount_size_mtime_preserved=same,actual_stored_bytes_saved=before['stored_bytes_GetCompressedFileSizeW']-after['stored_bytes_GetCompressedFileSizeW'],
            actual_allocation_bytes_saved=before['standard_allocation_bytes']-after['standard_allocation_bytes'],
            final_counters={'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()},finished_utc=stamp())
        record['status']=('PASS_BYTE_IDENTICAL_READABLE_STRONG_LZX_PILOT' if mode=='compress' else 'PASS_BYTE_IDENTICAL_ORDINARY_NTFS_STATE_RESTORED') if successful and same and state_ok else 'STORAGE_PILOT_OPERATIONAL_REVIEW_REQUIRED_NO_PROOF_FAILURE_INFERENCE'
        out=BASE/(serial+'-single-own-output-'+mode+'-actual.json');write_new(out,record)
        print(json.dumps({'record':str(out),'sha256':sha(out),'status':record['status'],'actual_allocation_bytes_saved':record['actual_allocation_bytes_saved']}))
        assert same,'Preserve current state; root must review any unexpected content/identity change'
    finally:
        K.ReleaseMutex.argtypes=[W.HANDLE];K.ReleaseMutex.restype=W.BOOL
        K.ReleaseMutex(mutex);K.CloseHandle(mutex)
        replay.seek(0);msvcrt.locking(replay.fileno(),msvcrt.LK_UNLCK,1);replay.close()

if __name__=='__main__':
    assert len(sys.argv)==4 and sys.argv[1] in {'--root-approved-strong-lzx-pilot','--root-approved-ordinary-state-restoration'}
    execute('compress' if sys.argv[1]=='--root-approved-strong-lzx-pilot' else 'restore',sys.argv[2],sys.argv[3])
