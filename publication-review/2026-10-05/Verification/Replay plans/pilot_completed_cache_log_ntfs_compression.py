"""Prepared-only, root-reviewed ordinary NTFS compression of exactly one own log.

No WOF/LZX, proof input/output, source, runtime or dependency content is targeted.
An execution requires a fresh SHA-bound root approval of this exact helper.
"""
from pathlib import Path
from datetime import datetime, timezone
import ctypes, hashlib, json, os, shutil, subprocess, sys, time
from native_resource_guard import K, W, EXTENDEDLIMIT, memory, processes, own_tree
from matt_resource_guard import resume_suspended_root
from resource_metrics import snapshot

BASE = Path(__file__).resolve().parent
ASSESSMENT = BASE/'completed-own-stronger-lzx-and-stable-metadata-storage-assessment-20261005.json'
ASSESSMENT_SHA = '656ca687679ecccda0a1b03896370f874afa8ff555567d4129ac4dce6921b956'
TARGET = BASE/'mathlib-4.34.1-cache-batched-force.log'
TARGET_BYTES = 26_488_890
PRODUCER = BASE/'assess_completed_own_artifact_storage_readonly.py'

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def stamp(): return datetime.now(timezone.utc).isoformat()
def save(path, doc):
    with Path(path).open('x',encoding='utf8',newline='\n') as stream:
        json.dump(doc,stream,indent=2);stream.write('\n')

def inactive_cache_and_compression_writers():
    command = "Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake|leantar|compact|python|7z|tar)\\.exe$' } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Compress"
    result = subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True,text=True,encoding='utf8',errors='replace',check=True)
    records = json.loads(result.stdout or '[]')
    if isinstance(records,dict):records=[records]
    import re
    offenders=[]
    for row in records:
        if row['ProcessId']==os.getpid():continue
        name=row['Name'].lower();cli=row.get('CommandLine') or ''
        if name in {'compact.exe','leantar.exe','7z.exe','tar.exe'}:
            offenders.append(row)
        elif re.search(r'(?i)(Cache[/\\.]Main|cache\s+get(?:-|!|\b)|force_official_cache|install_lean|compact_|compress_|run_matt_core_cache|run_.*cache_download)',cli):
            offenders.append(row)
    assert not offenders,('Existing cache/extractor/compression writer; exact one-pilot lease cannot qualify',offenders)
    return records

def execute(approval_path, approval_sha):
    approval_path=Path(approval_path).resolve()
    assert approval_path.is_relative_to(BASE.resolve()) and sha(approval_path)==approval_sha
    approval=json.loads(approval_path.read_bytes())
    assert approval['status']=='ROOT_APPROVED_SINGLE_COMPLETED_CACHE_LOG_ORDINARY_NTFS_COMPRESSION_PILOT'
    assert approval['reviewed_helper_sha256']==sha(__file__)
    assert approval['reviewed_assessment_sha256']==ASSESSMENT_SHA and sha(ASSESSMENT)==ASSESSMENT_SHA
    data=json.loads(ASSESSMENT.read_bytes())
    selected=[r for r in data['stable_generated_metadata'] if Path(r['file']).resolve()==TARGET.resolve()]
    assert len(selected)==1
    selected=selected[0]
    # AST-free prefix extraction executes only reviewed native metadata definitions.
    original=PRODUCER.read_text(encoding='utf8')
    prefix, marker, _=original.partition('before_processes=process_snapshot()')
    assert marker and sha(PRODUCER)==data['native_metadata_definition_producer_sha256']
    namespace={'__file__':str(PRODUCER),'__name__':'metadata_definitions_only'}
    exec(compile(prefix,str(PRODUCER),'exec'),namespace)
    native=namespace['native_metadata']
    target=TARGET.resolve()
    assert target.parent==BASE.resolve() and target.name=='mathlib-4.34.1-cache-batched-force.log'
    assert not TARGET.is_symlink() and target.is_relative_to(BASE.resolve())
    before=native(target)
    assert before['link_count']==1 and not before['FILE_ATTRIBUTE_REPARSE_POINT'] and not before['FILE_ATTRIBUTE_ENCRYPTED']
    assert before['logical_bytes']==TARGET_BYTES==selected['logical_bytes']
    assert sha(target)==selected['content_sha256']==approval['reviewed_target_content_sha256']
    for key in ['volume_serial','file_index_high','file_index_low','link_count','last_write_FILETIME']:
        assert before[key]==selected[key],('Target identity changed since reviewed metadata',key)
    assert not before['FILE_ATTRIBUTE_COMPRESSED'],'Only the measured uncompressed pilot is approved'
    initial_disk=shutil.disk_usage(BASE).free
    assert initial_disk>=4_000_000_000 and initial_disk-TARGET_BYTES>=1_000_000_000
    compact=Path(os.environ['SystemRoot'])/'System32/compact.exe'
    assert compact.is_file()
    command=[str(compact),'/C','/F','/Q',str(target)]
    assert approval['reviewed_exact_command']==command
    process_before=inactive_cache_and_compression_writers()
    lock=BASE/'ordinary-ntfs-single-log-compression-pilot.lock'
    lock_handle=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY)
    os.write(lock_handle,json.dumps({'owner_pid':os.getpid(),'target':str(target),'started_utc':stamp()}).encode());os.close(lock_handle)
    report=BASE/'completed-cache-log-ordinary-ntfs-pilot-actual-20261005.json'
    assert not report.exists()
    row={'status':'STARTED_SINGLE_ORDINARY_NTFS_PILOT','started_utc':stamp(),'helper_sha256':sha(__file__),
        'approval':str(approval_path),'approval_sha256':approval_sha,'assessment_sha256':ASSESSMENT_SHA,
        'target':str(target),'target_content_sha256_before':sha(target),'native_before':before,
        'exact_native_command':command,'compact_executable_sha256':sha(compact),'initial_disk_free_bytes':initial_disk,
        'maximum_single_target_logical_bytes':TARGET_BYTES,'initial_system_resources':snapshot(),
        'minimum_disk_free_bytes':initial_disk,'cache_and_compressor_process_snapshot_before':process_before,
        'algorithm':'ordinary NTFS LZNT1 via compact.exe /C /F /Q; no /EXE option or WOF/LZX',
        'source_proof_output_runtime_dependency_or_archive_target_count':0}
    job=K.CreateJobObjectW(None,None);assert job
    limits=EXTENDEDLIMIT();limits.BasicLimitInformation.LimitFlags=0x2000|0x0100|0x0200
    limits.ProcessMemoryLimit=256*2**20;limits.JobMemoryLimit=256*2**20
    assert K.SetInformationJobObject(job,9,ctypes.byref(limits),ctypes.sizeof(limits))
    stdout=BASE/'completed-cache-log-ordinary-ntfs-pilot.stdout.txt'
    stderr=BASE/'completed-cache-log-ordinary-ntfs-pilot.stderr.txt'
    assert not stdout.exists() and not stderr.exists()
    proc=None;stop=None;start=time.monotonic();peak_private=peak_rss=0
    row['minimum_physical_available_bytes']=row['initial_system_resources']['free_physical_bytes']
    row['minimum_available_commit_bytes']=row['initial_system_resources']['available_commit_bytes']
    try:
        assert shutil.disk_usage(BASE).free>=4_000_000_000
        with stdout.open('xb') as out,stderr.open('xb') as err:
            proc=subprocess.Popen(command,cwd=BASE,stdout=out,stderr=err,creationflags=0x08000000|0x00000004)
            if not K.AssignProcessToJobObject(job,W.HANDLE(int(proc._handle))):
                proc.kill();proc.wait(timeout=15)
                raise ctypes.WinError(ctypes.get_last_error())
            row.update(owned_compact_pid=proc.pid,own_job_assignment_before_resume='PASS')
            resume_suspended_root(proc.pid)
            while True:
                registry=processes();metrics=[m for pid in own_tree(proc.pid,registry) if (m:=memory(pid))]
                peak_private=max(peak_private,sum(m['private_bytes'] for m in metrics))
                peak_rss=max(peak_rss,sum(m['rss_bytes'] for m in metrics))
                system=snapshot()
                row['minimum_physical_available_bytes']=min(row['minimum_physical_available_bytes'],system['free_physical_bytes'])
                row['minimum_available_commit_bytes']=min(row['minimum_available_commit_bytes'],system['available_commit_bytes'])
                free=shutil.disk_usage(BASE).free;row['minimum_disk_free_bytes']=min(row['minimum_disk_free_bytes'],free)
                if free<1_000_000_000:stop='OWN_PILOT_DISK_RESERVE_STOP'
                elif time.monotonic()-start>120:stop='OWN_PILOT_TIMEOUT'
                if stop:K.TerminateJobObject(job,77);proc.wait(timeout=15);break
                if proc.poll() is not None:break
                time.sleep(.1)
            proc.wait(timeout=15);row['native_exit_code']=proc.returncode
            final=EXTENDEDLIMIT();assert K.QueryInformationJobObject(job,9,ctypes.byref(final),ctypes.sizeof(final),None)
            row.update(job_peak_aggregate_private_bytes=int(final.PeakJobMemoryUsed),job_peak_process_private_bytes=int(final.PeakProcessMemoryUsed))
    except Exception as error:
        stop='OWN_PILOT_OPERATIONAL_ERROR';row['operational_error']=str(error)
    finally:
        if proc is not None and proc.poll() is None:K.TerminateJobObject(job,78);proc.wait(timeout=15)
        K.CloseHandle(job)
    if proc is not None:row['native_exit_code']=proc.returncode
    else:row['native_exit_code']=None
    after=native(target);after_sha=sha(target)
    same=after_sha==row['target_content_sha256_before']
    identities=all(before[k]==after[k] for k in ['volume_serial','file_index_high','file_index_low','link_count','logical_bytes','last_write_FILETIME'])
    assert after['link_count']==1 and not after['FILE_ATTRIBUTE_REPARSE_POINT'] and not after['FILE_ATTRIBUTE_ENCRYPTED']
    row.update(native_after=after,target_content_sha256_after=after_sha,byte_identity_preserved=same,
        native_inode_linkcount_and_mtime_preserved=identities,stop_reason=stop,
        actual_stored_bytes_saved=before['stored_bytes_GetCompressedFileSizeW']-after['stored_bytes_GetCompressedFileSizeW'],
        actual_standard_allocation_bytes_saved=before['standard_allocation_bytes']-after['standard_allocation_bytes'],
        final_disk_free_bytes=shutil.disk_usage(BASE).free,final_system_resources=snapshot(),
        polled_peak_owned_private_bytes=peak_private,polled_peak_owned_rss_bytes=peak_rss,
        native_stdout=stdout.read_bytes().decode('mbcs',errors='replace'),native_stderr=stderr.read_bytes().decode('mbcs',errors='replace'),
        stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),finished_utc=stamp(),seconds=round(time.monotonic()-start,3))
    row['status']='PASS_BYTE_IDENTICAL_SINGLE_ORDINARY_NTFS_PILOT' if same and identities and not stop and row['native_exit_code']==0 else 'PILOT_REVIEW_REQUIRED'
    save(report,row)
    # This helper-created lock is the only filesystem object removed; no directory or user material.
    assert json.loads(lock.read_bytes())['owner_pid']==os.getpid();lock.unlink()
    print(json.dumps({'report':str(report),'sha256':sha(report),'status':row['status'],'actual_stored_bytes_saved':row['actual_stored_bytes_saved'],'disk_free':row['final_disk_free_bytes']},indent=2))
    assert same and identities,'Pilot content or inode identity requires immediate review'

if __name__=='__main__':
    if len(sys.argv)!=4 or sys.argv[1]!='--root-approved-single-log-pilot':
        raise SystemExit('Prepared only: --root-approved-single-log-pilot approval_path approval_sha is required after root review')
    execute(sys.argv[2],sys.argv[3])
