"""Prepared A000 storage-only interface; inert unless a reviewed runner calls it.

No standalone execution. Future root policy must bind this interface, its separate
runner copy/specification and an actual A000 LZX pilot. Only a new completed own
source .olean can be compressed, after its Lean job has actually exited. All proof
rows/scientific source/options/current installed dependencies remain unchanged.
"""
from pathlib import Path
from datetime import datetime,timezone
from ctypes import wintypes as W
import ctypes,hashlib,json,mmap,os,shutil,subprocess,sys,time
from native_resource_guard import K,EXTENDEDLIMIT,memory,processes,own_tree
from matt_resource_guard import resume_suspended_root
from resource_metrics import snapshot

BASE=Path(__file__).resolve().parent
STAGE=(BASE/'builds/sakana-a000224').resolve()
GIB=2**30
SPEC=BASE/'proposals/a000-post-exit-owned-artifact-lzx-interface-preparation-20261005.json'

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

def native_helper(spec):
    p=BASE/'assess_completed_own_artifact_storage_readonly.py'
    assert sha(p)==spec['native_metadata_helper_sha256']
    prefix,marker,_=p.read_text(encoding='utf8').partition('before_processes=process_snapshot()');assert marker
    ns={'__file__':str(p),'__name__':'reviewed_native_metadata_definitions_only'}
    exec(compile(prefix,str(p),'exec'),ns)
    return ns['native_metadata']

def same_identity(a,b):
    return all(a[k]==b[k] for k in ('volume_serial','file_index_high','file_index_low','link_count','last_write_FILETIME','logical_bytes'))

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

def compress_after_own_source_exit(*,approval_file,approval_sha256,source_receipt_file,
        source_receipt_sha256,completed_module,caller_runner_file,caller_runner_sha256,replay_lock):
    """Synchronous callback only; returns additive storage record, never proof rows.

    The exact reviewed caller holds replay_lock across this callback and dispatches
    no next Lean until it returns. Any error checkpoints storage only.
    """
    self_sha=sha(__file__);caller=Path(caller_runner_file).resolve()
    assert caller==Path(sys.argv[0]).resolve() and sha(caller)==caller_runner_sha256
    assert not replay_lock.closed and Path(replay_lock.name).resolve()==STAGE/'.fresh-replay.lock'
    assert replay_lock.fileno()>=0 # ownership is established in exact reviewed caller code
    spec=json.loads(SPEC.read_bytes());assert spec['interface_sha256']==self_sha
    assert spec['prepared_runner_sha256']==caller_runner_sha256
    ap=Path(approval_file).resolve();assert ap.is_relative_to(BASE) and sha(ap)==approval_sha256
    a=json.loads(ap.read_bytes())
    assert a['status']=='ROOT_APPROVED_A000_POST_EXIT_OWN_OUTPUT_LZX_INTERFACE'
    assert a['interface_sha256']==self_sha and a['runner_sha256']==caller_runner_sha256
    assert a['specification_sha256']==sha(SPEC)
    pilot=Path(a['actual_A000_single_file_pilot_receipt']).resolve()
    assert pilot.is_relative_to(BASE) and sha(pilot)==a['actual_A000_single_file_pilot_receipt_sha256']
    pd=json.loads(pilot.read_bytes())
    assert pd['status']=='PASS_BYTE_IDENTICAL_READABLE_STRONG_LZX_PILOT'
    assert Path(pd['target']).resolve()==STAGE/'OpHack/QuadraticResidue224/CertificateP127Part0033.olean'
    assert pd['content_inode_linkcount_size_mtime_preserved'] is True
    assert a['allow_only_remaining_original95_modules'] is True and a['previous_original76_outputs_not_targets'] is True
    assert completed_module in spec['future_remaining95_source_names'] and completed_module not in spec['original76_source_pass_names']
    for path,h in spec['protected_frozen_input_bindings'].items():assert sha(path)==h,path
    rp=Path(source_receipt_file).resolve();assert rp==BASE/'sakana-a000224-fresh-build.json' and sha(rp)==source_receipt_sha256
    receipt_bytes=rp.read_bytes();d=json.loads(receipt_bytes)
    assert d['id']=='sakana-a000224' and d['modules']==spec['exact_original_source_plan_modules']
    actual=[r for r in d['builds'] if r['module']==completed_module]
    assert len(actual)==1
    r=actual[0];guard=r['own_job_resource_receipt']
    assert r['exit']==guard['exit']==0 and not r.get('stop_reason') and not r.get('is_endpoint_audit')
    assert guard['state']=='PASS' and guard['attempted'] is True and guard['own_job_assignment_before_resume']=='PASS'
    assert guard['finished_utc'] and guard['command']==r['command'] and '-j1' in r['command']
    assert r['source_sha256']==spec['source_hashes_by_module'][completed_module]
    assert d.get('current_module') is None # reviewed caller clears stale marker only after actual job exit
    expected=STAGE.joinpath(*completed_module.split('.')).with_suffix('.olean').resolve()
    matches=[x for x in r['artifacts'] if Path(x['file']).resolve()==expected]
    assert len(matches)==1 and len(r['artifacts'])==1 # original4.34 invocation exports this one .olean
    target=expected;artifact=matches[0]
    assert target.is_relative_to(STAGE) and target.suffix=='.olean' and not target.is_symlink()
    native=native_helper(spec);before=native(target);wb=wof_info(target);read=read_and_mmap(target)
    assert before['link_count']==1 and not before['FILE_ATTRIBUTE_ENCRYPTED'] and not before['FILE_ATTRIBUTE_REPARSE_POINT']
    assert before['logical_bytes']==artifact['bytes'] and read['ordinary_read_sha256']==artifact['sha256']
    assert not wb['external'] and before['FILE_ATTRIBUTE_COMPRESSED']
    # Prove no loader currently keeps the exact inode open before touching storage.
    K.CreateFileW.argtypes=[W.LPCWSTR,W.DWORD,W.DWORD,ctypes.c_void_p,W.DWORD,W.DWORD,W.HANDLE];K.CreateFileW.restype=W.HANDLE
    h=K.CreateFileW(str(target),0x80,0,None,3,0,None)
    assert h!=ctypes.c_void_p(-1).value,'Target has an active writer/reader or cannot be exclusively opened'
    K.CloseHandle(h)
    quiescence(guard['root_pid']);gates(target)
    compact=Path(os.environ['SystemRoot'])/'System32/compact.exe';assert sha(compact)==spec['compact_executable_sha256']
    cmd=[str(compact),'/C','/F','/Q','/EXE:LZX',str(target)]
    K.CreateMutexW.argtypes=[ctypes.c_void_p,W.BOOL,W.LPCWSTR];K.CreateMutexW.restype=W.HANDLE
    mutex=K.CreateMutexW(None,True,'Local\\OpenMathSingleCompletedOutputStoragePilot')
    assert mutex and ctypes.get_last_error()!=183,'Global own-output compressor lease already held'
    serial=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    history=BASE/'operational_history/a000-post-exit-storage';history.mkdir(exist_ok=True)
    record={'status':'STARTED_EXACT_A000_NEW_OWN_COMPLETED_SOURCE_OUTPUT_STORAGE_OPERATION',
        'started_utc':stamp(),'interface_sha256':self_sha,'runner_sha256':caller_runner_sha256,
        'root_policy_file':str(ap),'root_policy_sha256':approval_sha256,'specification_sha256':sha(SPEC),
        'source_receipt_sha256_before':source_receipt_sha256,'source_module':completed_module,
        'actual_completed_source_row':r,'target':str(target),'native_before':before,'WOF_before':wb,'read_and_mmap_before':read,
        'actual_compact_command':cmd,'resource_policy':spec['storage_resource_policy'],
        'original76_or_any_scientific_source_or_runtime_provider_targets':0}
    write_new(history/(serial+'-started.json'),record)
    try:
        result=guarded_compact(cmd,serial+'-a000-post-exit-storage',target,guard['root_pid'])
        after=native(target);wa=wof_info(target);read_after=read_and_mmap(target)
        same=same_identity(before,after) and read_after['ordinary_read_sha256']==artifact['sha256']
        assert rp.read_bytes()==receipt_bytes,'Storage callback must not modify source receipt'
        for path,h in spec['protected_frozen_input_bindings'].items():assert sha(path)==h,path
        successful=result.get('exit')==0 and not result.get('stop_reason') and same and wa['external'] and wa['provider']==2 and wa['algorithm']==1
        record.update(status='PASS_BYTE_IDENTICAL_A000_POST_EXIT_OWN_OUTPUT_LZX' if successful else 'STORAGE_OPERATION_REVIEW_REQUIRED_PRESERVE_SOURCE_PASS',
            finished_utc=stamp(),actual_command_row=result,native_after=after,WOF_after=wa,read_and_mmap_after=read_after,
            content_inode_linkcount_size_mtime_preserved=same,
            actual_allocation_bytes_saved=before['standard_allocation_bytes']-after['standard_allocation_bytes'],
            source_receipt_bytes_unchanged=True,actual_source_PASS_row_not_reclassified=True,
            final_counters={'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()})
        out=history/(serial+'-actual.json');write_new(out,record)
        return {'status':record['status'],'record':str(out),'sha256':sha(out),'source_pass_preserved':True,'may_dispatch_next_source':successful}
    finally:
        K.ReleaseMutex.argtypes=[W.HANDLE];K.ReleaseMutex.restype=W.BOOL
        K.ReleaseMutex(mutex);K.CloseHandle(mutex)

if __name__=='__main__':
    raise SystemExit('Prepared interface only; invoke solely from separately root-reviewed own-source runner after actual owned Lean exit.')
