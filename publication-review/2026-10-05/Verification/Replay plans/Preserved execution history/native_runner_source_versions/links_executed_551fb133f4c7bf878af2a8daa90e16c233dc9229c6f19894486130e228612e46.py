"""Two bounded native links; no plugin load or Lean invocation.

Prepared under the root's planning request. It must not be dispatched until
the root explicitly authorizes linking and grants the coordinated slot.
"""
from pathlib import Path
import argparse,ctypes,datetime,hashlib,json,os,shutil,subprocess,time
from native_resource_guard import K,W,EXTENDEDLIMIT,MEMORYSTATUSEX,GIB,processes,own_tree,memory,allocated
from native_PE_tools import inspect_pe,sha256
from receipt_io import read_bytes_shared

B=Path(__file__).resolve().parent;R=B/'runtimes/lean-4.34.1-windows'
D=B/'builds/luke-k4-ramsey-native-isolated';P=B/'luke-native-isolated-links.json'
PREPARED_RUNNER_SHA256='0bcbbf2112e891a33a8554a8ed5458d019021c6e615121393dd77baafb35789f'
N=ctypes.WinDLL('ntdll')
N.NtResumeProcess.argtypes=[W.HANDLE];N.NtResumeProcess.restype=ctypes.c_long

def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def counters():
    s=MEMORYSTATUSEX();s.dwLength=ctypes.sizeof(s)
    if not K.GlobalMemoryStatusEx(ctypes.byref(s)):raise ctypes.WinError(ctypes.get_last_error())
    return {'disk_free_bytes':shutil.disk_usage(B).free,'physical_available_bytes':int(s.ullAvailPhys),
      'available_commit_bytes':int(s.ullAvailPageFile),'commit_limit_bytes':int(s.ullTotalPageFile)}
def workspace():return sum(p.stat().st_size for p in D.rglob('*') if p.is_file())
def immutable_save(path,data):
    assert not path.exists(),'Preserve previous attempt; do not overwrite an immutable native receipt'
    tmp=path.with_suffix(path.suffix+'.tmp')
    with tmp.open('w',encoding='utf8') as f:json.dump(data,f,indent=2);f.flush();os.fsync(f.fileno())
    for attempt in range(60):
        try:os.replace(tmp,path);return
        except PermissionError:
            if attempt==59:raise
            time.sleep(.1)
def guarded(command,tag,first_cluster_pilot=False):
    cap=GIB if first_cluster_pilot else 2*GIB
    initial_physical=(4 if first_cluster_pilot else 6)*GIB
    initial_commit=(3 if first_cluster_pilot else 5)*GIB
    first=counters();row={'command':command,'started_utc':stamp(),'attempted':False,'dispatch_counters':first,
      'minimum_counters':dict(first),'own_private_cap_bytes':cap,'workspace_bytes_before':workspace(),
      'resource_policy':{'initial_disk_bytes':4_000_000_000,'initial_physical_bytes':initial_physical,'initial_available_commit_bytes':initial_commit,'continuous_disk_bytes':1_000_000_000,'continuous_physical_bytes':3*GIB,'continuous_available_commit_bytes':GIB,'own_job_and_process_private_cap_bytes':cap,'native_workspace_bytes':1_000_000_000},
      'first_cluster_only_pilot_adaptation':first_cluster_pilot}
    if first['disk_free_bytes']<4_000_000_000 or first['physical_available_bytes']<initial_physical or first['available_commit_bytes']<initial_commit:
        row['state']='NOT_INVOKED_RESOURCE_DISPATCH_GATE';return row
    if row['workspace_bytes_before']>1_000_000_000:row['state']='NOT_INVOKED_NATIVE_WORKSPACE_BOUND';return row
    logs=D/'logs';logs.mkdir(exist_ok=True);so=logs/(tag+'.stdout.txt');se=logs/(tag+'.stderr.txt')
    assert not so.exists() and not se.exists(),'Link logs must be cold'
    job=K.CreateJobObjectW(None,None);assert job,'Cannot create own link job'
    limits=EXTENDEDLIMIT();limits.BasicLimitInformation.LimitFlags=0x2000|0x0100|0x0200
    limits.ProcessMemoryLimit=limits.JobMemoryLimit=cap
    assert K.SetInformationJobObject(job,9,ctypes.byref(limits),ctypes.sizeof(limits)),'Cannot install link limits'
    env=dict(os.environ);assert not env.get('LEAN_CC') and not env.get('LEAN_SYSROOT')
    env['PATH']=str(R/'bin')+';'+env['PATH'];env['LEAN_NUM_THREADS']='1'
    temp=D/'tmp';temp.mkdir(exist_ok=True);env['TEMP']=env['TMP']=str(temp)
    start=time.monotonic();peak=0;seen={};samples=0;stop=None
    try:
        with so.open('wb') as out,se.open('wb') as err:
            proc=subprocess.Popen(command,cwd=D,env=env,stdout=out,stderr=err,creationflags=0x08000000|0x00000004)
            row.update(attempted=True,root_pid=proc.pid,created_suspended=True)
            if not K.AssignProcessToJobObject(job,W.HANDLE(int(proc._handle))):
                proc.kill();proc.wait();raise OSError('Own suspended link root job assignment failed')
            row['assigned_to_own_job_before_resume']=True
            resume_status=int(N.NtResumeProcess(W.HANDLE(int(proc._handle))))
            row['NtResumeProcess_status']=resume_status
            if resume_status<0:raise OSError('NtResumeProcess failed NTSTATUS='+hex(resume_status & 0xffffffff))
            row['resumed_after_own_job_assignment']=True
            while True:
                now=counters();row['minimum_counters']={k:min(row['minimum_counters'][k],v) for k,v in now.items()}
                registry=processes();values=[]
                for pid in own_tree(proc.pid,registry):
                    m=memory(pid)
                    if m:
                        values.append(m);e=seen.setdefault(str(pid),{'exe':registry.get(pid,{}).get('exe',''),'peak_private_bytes':0,'peak_rss_bytes':0})
                        e['peak_private_bytes']=max(e['peak_private_bytes'],m['private_bytes']);e['peak_rss_bytes']=max(e['peak_rss_bytes'],m['peak_rss_bytes'])
                current=sum(m['private_bytes'] for m in values);peak=max(peak,current);samples+=1
                if now['disk_free_bytes']<1_000_000_000:stop='ENVIRONMENT_BLOCKED_DISK_RESERVE'
                elif now['physical_available_bytes']<3*GIB:stop='ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE'
                elif now['available_commit_bytes']<GIB:stop='ENVIRONMENT_BLOCKED_AVAILABLE_COMMIT_RESERVE'
                elif current>cap:stop='ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT'
                elif workspace()>1_000_000_000:stop='ENVIRONMENT_BLOCKED_NATIVE_WORKSPACE_BOUND'
                elif time.monotonic()-start>900:stop='OPERATIONAL_LINK_TIMEOUT'
                if stop:K.TerminateJobObject(job,77);proc.wait(timeout=15);break
                if proc.poll() is not None:break
                time.sleep(.25)
            proc.wait(timeout=15);row['exit']=proc.returncode
            measured=EXTENDEDLIMIT();assert K.QueryInformationJobObject(job,9,ctypes.byref(measured),ctypes.sizeof(measured),None)
            row['job_peak_process_private_bytes']=int(measured.PeakProcessMemoryUsed)
            row['job_peak_aggregate_private_bytes']=int(measured.PeakJobMemoryUsed)
            row['state']=stop or ('PASS' if proc.returncode==0 else 'LINKER_FAILED')
    except Exception as exc:
        K.TerminateJobObject(job,78);row.update(state='OPERATIONAL_ERROR',error=str(exc))
    finally:K.CloseHandle(job)
    row.update(finished_utc=stamp(),seconds=round(time.monotonic()-start,3),polled_peak_tree_private_bytes=peak,
      observed_own_processes=seen,counter_samples=samples,stdout_file=str(so),stderr_file=str(se),
      stdout_sha256=sha256(so),stderr_sha256=sha256(se),stdout_excerpt=so.read_text(encoding='utf8',errors='replace')[:32768],
      stderr_excerpt=se.read_text(encoding='utf8',errors='replace')[:32768],workspace_bytes_after=workspace())
    return row

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--authorization',required=True)
    parser.add_argument('--stage',choices=['first','second','both'],default='first');parser.add_argument('--retry-not-invoked',action='store_true');args=parser.parse_args()
    receipt_path=B/('luke-native-isolated-first-link.json' if args.stage=='first' else 'luke-native-isolated-links.json')
    assert args.authorization=='ROOT_EXPLICIT_NATIVE_LINK_AUTHORIZATION','Do not dispatch without root authorization and slot handoff'
    previous=None
    if receipt_path.exists():
        assert args.stage=='first' and args.retry_not_invoked,'Preserve the earlier immutable link attempt'
        earlier_bytes=read_bytes_shared(receipt_path);earlier=json.loads(earlier_bytes)
        assert earlier['status']=='LINK_ATTEMPT_HELD' and earlier['links'] and all(not r['attempted'] for r in earlier['links'])
        for name in ['luke_nonmath_native.dll','libluke_nonmath_native.dll.a','luke_mathlib_count_native.dll','libluke_mathlib_count_native.dll.a']:
            assert not (D/'bin'/name).exists(),'No-attempt retry must have no DLL/import-library output'
        for r in earlier['response_files']:assert sha256(r['file'])==r['sha256'],'Earlier frozen response hash changed'
        h=hashlib.sha256(earlier_bytes).hexdigest();archive=B/'native_link_attempts'/('first-not-invoked-'+earlier['started_utc'][:19].replace(':','').replace('-','')+'-'+h[:12]+'.json')
        archive.parent.mkdir(exist_ok=True);assert not archive.exists();receipt_path.rename(archive)
        assert sha256(archive)==h
        previous={'file':str(archive),'sha256':h,'status':earlier['status'],'no_child_was_invoked':True,'response_files':earlier['response_files'],'runner_sha256':earlier['runner_sha256']}
    elif args.retry_not_invoked:
        archives=sorted((B/'native_link_attempts').glob('first-not-invoked-*.json'));assert len(archives)==1,'Require the sole exact preserved no-attempt receipt'
        archive=archives[0];earlier_bytes=archive.read_bytes();earlier=json.loads(earlier_bytes);h=hashlib.sha256(earlier_bytes).hexdigest()
        assert earlier['status']=='LINK_ATTEMPT_HELD' and all(not r['attempted'] for r in earlier['links'])
        for name in ['luke_nonmath_native.dll','libluke_nonmath_native.dll.a','luke_mathlib_count_native.dll','libluke_mathlib_count_native.dll.a']:assert not (D/'bin'/name).exists()
        for r in earlier['response_files']:assert sha256(r['file'])==r['sha256']
        previous={'file':str(archive),'sha256':h,'status':earlier['status'],'no_child_was_invoked':True,'response_files':earlier['response_files'],'runner_sha256':earlier['runner_sha256']}
    prep_bytes=read_bytes_shared(B/'luke-native-isolated-preparation.json');prep=json.loads(prep_bytes)
    abi_bytes=(B/'luke-native-isolated-object-ABI-audit.json').read_bytes();abi=json.loads(abi_bytes)
    auto_bytes=(B/'luke-native-auto-import-qualification.json').read_bytes();auto=json.loads(auto_bytes)
    assert auto['initial_object_ABI_audit_sha256']==hashlib.sha256(abi_bytes).hexdigest()
    assert auto['status']=='ALL_182_GENUINE_AUTO_IMPORT_DATA_PROVIDERS_VERIFIED_LINK_UNTESTED'
    assert auto['all_aliases_exact_x64_data_imports'] and auto['all_core_targets_actual_nonexecuting_data_exports']
    assert {r['symbol'] for r in auto['rows']}==set(abi['strong_undefined_symbols_not_in_object_or_pinned_library_indexes'])
    assert prep['status']=='OBJECTS_PASS_LINK_AND_INIT_UNTESTED' and len([r for r in prep['objects'] if r['state']=='PASS'])==951
    assert abi['preparation_receipt_sha256']==hashlib.sha256(prep_bytes).hexdigest()
    assert abi['both_clusters_within_export_limit'] and abi['all_Count_closed_cache_data_cases_match']
    for key in ['unresolved_non_COMDAT_definition_collisions','cross_cluster_hidden_symbol_references',
      'non_mathlib_to_mathlib_custom_reverse_references',
      'missing_explicit_link_flag_libraries','changed_official_dependency_artifacts']:
        assert not abi[key],key+' requires resolution before linking'
    groups={'non_mathlib':[],'mathlib_custom':[]};expected={k:set() for k in groups}
    for row in prep['objects']:
        if row['state']!='PASS':continue
        assert row['state']=='PASS' and sha256(row['object_file'])==row['object_sha256']
        group='mathlib_custom' if row['package'] in ['mathlib','custom-default-none'] else 'non_mathlib'
        groups[group].append(row['object_file'])
        exports=json.loads(Path(row['actual_COFF_exports_file']).read_text(encoding='utf8'))
        expected[group].update(e.split(',')[0] for e in exports)
    linkdir=D/'link';bindir=D/'bin';linkdir.mkdir(exist_ok=True);bindir.mkdir(exist_ok=True)
    responses={};response_rows=[]
    for group,objects in groups.items():
        p=linkdir/(group+'_objects.rsp');text=''.join('"'+Path(o).as_posix()+'"\n' for o in objects)
        if args.stage=='second' or previous:assert p.exists() and p.read_text(encoding='utf8')==text,'Only own identical first-stage response file may be reused'
        else:
            assert not p.exists(),'Response file must be cold'
            p.write_text(text,encoding='utf8')
        responses[group]=p;response_rows.append({'group':group,'file':str(p),'sha256':sha256(p),'object_count':len(objects)})
    record={'started_utc':stamp(),'status':'LINKING_ONLY','family_id':'luke-k4-ramsey-current',
      'scope':'Two isolated DLL links plus actual PE metadata audit. No plugin/DLL load, initializer execution, counting or theorem certification.',
      'source_commit':prep['source_commit'],'lean_version':prep['lean_version'],'mathlib_pin':prep['mathlib_pin'],
      'preparation_receipt_sha256':hashlib.sha256(prep_bytes).hexdigest(),'object_ABI_audit_sha256':hashlib.sha256(abi_bytes).hexdigest(),
      'genuine_automatic_data_import_qualification_sha256':hashlib.sha256(auto_bytes).hexdigest(),
      'genuine_automatic_data_import_provider_count':auto['qualified_count'],
      'runner_sha256':sha256(__file__),'prepared_runner_sha256':PREPARED_RUNNER_SHA256,'startup_policy':'CREATE_SUSPENDED|CREATE_NO_WINDOW; assign exact root to own job before NtResumeProcess; descendants inherit own caps','PE_helper_sha256':sha256(B/'native_PE_tools.py'),
      'response_files':response_rows,'previous_not_invoked_attempt':previous,'links':[],'dlls':[],'no_plugin_or_DLL_load':True,
      'native_selection_notice':'Actual native selection will later be a deterministic inference from pinned lookup/mangling/default preference and loaded exports; no release call trace is claimed.'}
    first=bindir/'luke_nonmath_native.dll';second=bindir/'luke_mathlib_count_native.dll'
    commands=[('non_mathlib',first,bindir/'libluke_nonmath_native.dll.a',[]),
      ('mathlib_custom',second,bindir/'libluke_mathlib_count_native.dll.a',['-L'+str(bindir),'-lluke_nonmath_native'])]
    if args.stage=='first':commands=commands[:1]
    elif args.stage=='second':
        first_path=B/'luke-native-isolated-first-link.json';first_bytes=first_path.read_bytes();earlier=json.loads(first_bytes)
        assert earlier['status']=='FIRST_ACTUAL_LINK_AND_PE_PASS_SECOND_LINK_UNTESTED'
        assert earlier['preparation_receipt_sha256']==record['preparation_receipt_sha256'] and earlier['response_files']==response_rows
        for dll in earlier['dlls']:
            assert sha256(dll['file'])==dll['sha256'] and sha256(dll['import_library']['file'])==dll['import_library']['sha256']
        record['reused_own_first_link_receipt']={'file':str(first_path),'sha256':hashlib.sha256(first_bytes).hexdigest()}
        record['links']=list(earlier['links']);record['dlls']=list(earlier['dlls']);commands=commands[1:]
    for group,dll,library,extra in commands:
        assert not dll.exists() and not library.exists(),'Do not overwrite a partial native link output'
        command=[str(R/'bin/leanc.exe'),'-shared','-v','-o',str(dll),'@'+str(responses[group]),*extra,
          '-Wl,--threads=1','-Wl,--enable-auto-import','-Wl,--enable-runtime-pseudo-reloc','-Wl,--out-implib,'+str(library)]
        row=guarded(command,'link_'+group,first_cluster_pilot=(args.stage=='first' and group=='non_mathlib'));row['group']=group;record['links'].append(row)
        if row['state']!='PASS':record['status']='LINK_ATTEMPT_HELD';break
        assert dll.exists() and library.exists(),'Successful linker omitted requested outputs'
        pe=inspect_pe(dll);actual=set(pe['exports']);pe['group']=group
        pe['missing_actual_COFF_exports']=sorted(expected[group]-actual)
        pe['additional_PE_exports']=sorted(actual-expected[group])
        pe['source_owned_exports_have_no_forwarders']=all(not pe['exports'][e]['forwarder'] for e in actual&expected[group])
        pe['import_library']={'file':str(library),'bytes':library.stat().st_size,'allocated_bytes':allocated(library),'sha256':sha256(library)}
        pe['allocated_bytes']=allocated(dll);record['dlls'].append(pe)
        if pe['missing_actual_COFF_exports'] or not pe['source_owned_exports_have_no_forwarders']:
            record['status']='ACTUAL_PE_EXPORT_REVIEW_REQUIRED';break
    else:
        if args.stage=='first':
            record['status']='FIRST_ACTUAL_LINK_AND_PE_PASS_SECOND_LINK_UNTESTED'
            record['finished_utc']=stamp();record['final_counters']=counters();record['workspace_logical_bytes']=workspace()
            immutable_save(receipt_path,record)
            print(json.dumps({'receipt':str(receipt_path),'status':record['status'],'actual_export_count':record['dlls'][0]['actual_export_count'],
              'actual_import_DLLs':list(record['dlls'][0]['imports']),'links':record['links']},indent=2),flush=True);return
        a,b=record['dlls'];record['two_DLL_DAG_import_checks']={
          'nonmath_does_not_import_mathlib_custom':second.name.lower() not in {s.lower() for s in a['imports']},
          'mathlib_custom_imports_actual_nonmath_DLL':first.name.lower() in {s.lower() for s in b['imports']}}
        cache_cases=[]
        for cache in ['bCache','dCache','pathsCache']:
            symbol='l_K4Ramsey_Final3840_Count_'+cache;value=b['exports'][symbol]
            cache_cases.append({'cache':cache,'symbol':symbol,**value,'actual_data_slot_is_nonexecuting_writable':not value['executable'] and value['writable']})
        record['actual_Count_closed_cache_PE_data_slots']=cache_cases
        record['actual_Count_initializer_is_exported_executable']=b['exports']['initialize_K4Ramsey_Constructions_Final3840_Count']['executable']
        clean=all(record['two_DLL_DAG_import_checks'].values()) and all(r['actual_data_slot_is_nonexecuting_writable'] for r in cache_cases) and record['actual_Count_initializer_is_exported_executable']
        record['status']='ACTUAL_LINKS_AND_PE_PASS_INITIALIZATION_UNTESTED' if clean else 'ACTUAL_PE_ABI_REVIEW_REQUIRED'
    record['finished_utc']=stamp();record['final_counters']=counters();record['workspace_logical_bytes']=workspace()
    immutable_save(receipt_path,record)
    print(json.dumps({'receipt':str(receipt_path),'status':record['status'],'links':[{'group':r['group'],'state':r['state'],'seconds':r.get('seconds'),'peak_private_bytes':r.get('job_peak_aggregate_private_bytes')} for r in record['links']]},indent=2),flush=True)

if __name__=='__main__':main()
