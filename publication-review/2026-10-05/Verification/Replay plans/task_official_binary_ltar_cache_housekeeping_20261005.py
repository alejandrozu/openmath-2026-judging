"""Preflight or explicitly root-reviewed deletion of exact task binary cache files.

No recursive operations, source ZIPs/tars, extracted providers, or proof outputs.
Preparation does not call this helper. Execute requires a concrete SHA-bound approval.
"""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, shutil, subprocess

BASE=Path(__file__).resolve().parent
CACHE=(BASE/'download-cache').resolve()
POLICY=BASE/'proposals/official-binary-ltar-cache-storage-assessment-20261005/all-cache-housekeeping-policy.json'
MANIFEST_SHA='a833366f8f7f35102ad204be351655605e04e7ca53e37ea5ea520592cac910cd'
ASSESSMENT_SHA='5539f9727babf819d1db83caa09347ec26bf85398d4b6d861054505d4076f910'
COUNT=25906
VERSIONS={'4.30.0-rc2','4.33.1','4.34.1'}
KINDS=['.olean','.olean.private','.olean.server','.ilean','.ir']
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def read_bound(ref):
    path=Path(ref['file']);assert sha(path)==ref['sha256'],('Bound input changed',str(path))
    return json.loads(path.read_text(encoding='utf8'))
def cache_users():
    # Return only matching task process IDs/names, never unrelated command lines.
    code=f"""$taskRoot = '{BASE}'; $exclude = @($PID,{os.getpid()}); $tokens = @('install_pinned_lean.py','prepare_dependency_sources.py','force_official_cache','core_only','Cache/Main.lean','exe cache','cache get','leantar','ExportOfficialCachePlan','assess_official_binary_download_caches','estimate_htpeo_ramsey_source_workload','recheck_htpeo_ramsey_original_sources'); @((Get-CimInstance Win32_Process) | Where-Object {{ $c=$_.CommandLine; $e=$_.ExecutablePath; ($_.ProcessId -notin $exclude) -and $c -and (($c.Contains($taskRoot)) -or ($e -and $e.Contains($taskRoot))) -and (@($tokens | Where-Object {{$c.Contains($_)}}).Count -gt 0) }} | ForEach-Object {{ [pscustomobject]@{{ProcessId=$_.ProcessId;Name=$_.Name;MatchedTaskCacheOperation=$true}} }}) | ConvertTo-Json -Compress"""
    result=subprocess.run(['powershell','-NoProfile','-Command',code],capture_output=True,text=True,check=True)
    data=json.loads(result.stdout) if result.stdout.strip() else []
    return data if isinstance(data,list) else [data]
def contained_path(row):
    relative=Path(row['relative_file'])
    assert not relative.is_absolute() and len(relative.parts)==2
    version,name=relative.parts
    assert version in VERSIONS and version==row['version']
    assert re.fullmatch(r'[0-9a-f]{16}\.ltar',name),name
    assert not CACHE.is_junction() and not CACHE.is_symlink()
    root=CACHE/version
    assert root.is_dir() and not root.is_junction() and not root.is_symlink()
    path=root/name
    assert path.resolve()==path and path.resolve().is_relative_to(root.resolve())
    assert path.is_file() and not path.is_symlink()
    return path
def check_archive(row,full_hash=True):
    path=contained_path(row);st=path.stat()
    assert st.st_size==row['logical_bytes'] and st.st_mtime_ns==row['mtime_ns'],str(path)
    assert (st.st_dev,st.st_ino)==(row['NTFS_volume_stat_dev'],row['NTFS_file_id_stat_ino']),str(path)
    assert st.st_nlink==row['observed_link_count']==1,('Archive alias appeared',str(path))
    if full_hash:assert sha(path)==row['sha256'],str(path)
    return path
def providers_available(policy):
    counts={}
    for entry in policy['preserved_provider_bindings']:
        version=entry['version']
        install=read_bound(entry['installation_receipt']);assert install['complete'] is True
        passed=read_bound(entry['official_cache_PASS_receipt']);assert passed['status']=='PASS'
        plan=read_bound(entry['official_cache_plan'])
        runtime_binary=Path(entry['runtime_lean_binary']['file'])
        assert sha(runtime_binary)==entry['runtime_lean_binary']['sha256']
        source=Path(entry['official_mathlib_source']['file']);assert sha(source)==entry['official_mathlib_source']['sha256']
        artifact=Path(entry['official_mathlib_olean']['file']);assert sha(artifact)==entry['official_mathlib_olean']['sha256']
        dep=Path(entry['dependency_source_root'])
        actual=subprocess.run(['git','--no-optional-locks','rev-parse','HEAD'],cwd=dep,capture_output=True,text=True,check=True).stdout.strip()
        assert actual==entry['mathlib_pin']
        n=0;optional={k:0 for k in KINDS}
        for row in plan:
            trace=Path(row['trace']).resolve();assert trace.is_relative_to((BASE/'dependencies'/version).resolve())
            for suffix in KINDS:
                file=trace.with_suffix(suffix)
                if file.is_file():optional[suffix]+=1
            assert trace.with_suffix('.olean').is_file(),str(trace)
            n+=1
        assert n==entry['cache_plan_module_count']
        counts[version]={'cached_provider_interfaces_present':n,'artifact_kind_presence':optional}
    return counts
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--mode',choices=['preflight','execute'],required=True)
    parser.add_argument('--approval')
    args=parser.parse_args()
    policy=json.loads(POLICY.read_text(encoding='utf8'))
    assert policy['assessment']['sha256']==ASSESSMENT_SHA and policy['candidate_manifest']['sha256']==MANIFEST_SHA
    read_bound(policy['assessment'])
    rows=read_bound(policy['candidate_manifest'])
    assert len(rows)==COUNT and len({r['relative_file'] for r in rows})==COUNT
    assert sum(r['logical_bytes'] for r in rows)==1_312_369_944
    expected=set()
    for entry in policy['preserved_provider_bindings']:
        for row in read_bound(entry['official_cache_plan']):
            path=Path(row['file']).resolve();assert path.is_relative_to(CACHE/entry['version'])
            expected.add(str(path.relative_to(CACHE)))
    assert expected=={r['relative_file'] for r in rows}
    assert not cache_users(),'An active task cache reader/writer/extractor is present'
    preserved=providers_available(policy)
    # Hash every candidate before any removal. No first-file mutation until all pass.
    for i,row in enumerate(rows,1):
        check_archive(row,True)
        if i%4000==0:print('CACHE_ONLY_PREFLIGHT_HASHED',i,flush=True)
    assert not cache_users(),'A task cache reader/writer started during preflight'
    approval=None
    if args.mode=='execute':
        assert args.approval,'Deletion requires an explicit concrete root approval record'
        approval_path=Path(args.approval).resolve();assert approval_path.is_relative_to(BASE.resolve())
        approval=json.loads(approval_path.read_text(encoding='utf8'))
        assert approval['approved'] is True
        assert approval['purpose']=='TASK_OWNED_OFFICIAL_BINARY_LTAR_CACHE_ONLY_HOUSEKEEPING'
        assert approval['approved_helper_sha256']==sha(__file__)
        assert approval['approved_policy_sha256']==sha(POLICY)
        assert approval['approved_manifest_sha256']==MANIFEST_SHA
        assert approval['approved_archive_count']==COUNT
        assert approval['no_active_cache_writer_or_extractor_required'] is True
        assert approval['preserve_all_source_runtime_compiled_provider_and_proof_outputs'] is True
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    record_dir=BASE/'operational_history/cache-only-housekeeping'
    record_dir.mkdir(exist_ok=True,parents=True)
    final=record_dir/(stamp+'-'+args.mode+'.json')
    record={'status':'PREFLIGHT_COMPLETE_NO_DELETION','mode':args.mode,'prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'helper_sha256':sha(__file__),'policy_sha256':sha(POLICY),'manifest_sha256':MANIFEST_SHA,
        'archive_count':COUNT,'preserved_provider_presence':preserved,'initial_disk_free_bytes':shutil.disk_usage(BASE).free,
        'current_cache_users':[],'archive_bytes_verified':1_312_369_944,'deleted_files':0,
        'historical_archive_exists_fields_are_preserved_dated_snapshots':True,
        'no_original_plan_receipt_source_runtime_dependency_or_proof_output_changes':True}
    if args.mode=='execute':
        record['approval_record']={'file':str(approval_path),'sha256':sha(approval_path)}
        kernel=ctypes.WinDLL('kernel32',use_last_error=True)
        kernel.DeleteFileW.argtypes=[ctypes.c_wchar_p];kernel.DeleteFileW.restype=ctypes.c_int
        log=record_dir/(stamp+'-exact-binary-cache-removals.jsonl')
        record['exact_removed_file_log']=str(log)
        try:
            with log.open('x',encoding='utf8',newline='\n') as stream:
                for i,row in enumerate(rows):
                    if i%128==0:assert not cache_users(),'Task cache use resumed; stop without further deletion'
                    path=check_archive(row,True)
                    # Native single-file operation; no recursive delete or cross-shell paths.
                    if not kernel.DeleteFileW('\\\\?\\'+str(path)):
                        raise OSError(ctypes.get_last_error(),str(path))
                    stream.write(json.dumps({'relative_file':row['relative_file'],'sha256':row['sha256'],
                        'logical_bytes':row['logical_bytes'],'NTFS_file_id':row['NTFS_file_id_stat_ino'],
                        'removed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},separators=(',',':'))+'\n')
                    stream.flush();record['deleted_files']+=1
            assert all(not (CACHE/row['relative_file']).exists() for row in rows)
            assert providers_available(policy)==preserved
            record['status']='TASK_BINARY_DOWNLOAD_CACHE_REMOVED_EXTRACTED_PROVIDERS_PRESERVED'
        except BaseException as error:
            record['status']='PARTIAL_CACHE_ONLY_HOUSEKEEPING_STOPPED'
            record['error']=repr(error)
            raise
        finally:
            record['remaining_disk_free_bytes']=shutil.disk_usage(BASE).free
            record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
            record['exact_removed_file_log_sha256']=sha(log) if log.exists() else None
            with final.open('x',encoding='utf8') as stream:json.dump(record,stream,ensure_ascii=False,indent=2)
            print(json.dumps({'record':str(final),'sha256':sha(final),'status':record['status'],'deleted_files':record['deleted_files']},indent=2),flush=True)
    else:
        with final.open('x',encoding='utf8') as stream:json.dump(record,stream,ensure_ascii=False,indent=2)
        print(json.dumps({'record':str(final),'sha256':sha(final),'status':record['status'],'deleted_files':0},indent=2),flush=True)
if __name__=='__main__':main()
