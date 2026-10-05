"""Prepared-only remaining-kernel -j2 continuation; NEW SHA-approved mode/boundary lease required.

One parent owns the HT byte lock and every canonical receipt write. Workers only
compile distinct original chunk files with the unchanged pinned own-job guard.
Only remaining cold kernels; approved one-with-A000 or two-HT-only mode. No audit/storage/native build.
"""
from pathlib import Path
from datetime import datetime,timezone
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import copy,hashlib,json,msvcrt,os,re,shutil,subprocess,sys,time
from lean_imports import read_imports
from receipt_io import read_bytes_shared
from matt_resource_guard import guarded_tree
from native_resource_guard import processes,own_tree
from resource_metrics import snapshot
BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-ramsey-current'
PLAN=STAGE/'build-plan.json'
PLAN_SHA='94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
REPORT=BASE/'htpeo-ramsey-current-fresh-build.json'
MANIFEST=BASE/'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
LEAN=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
LEAN_SHA='af49bacfabaa1fea71332ca0feae0fa1a60912219d5902291adc79f905bffb8d'
GUARD_SHA='ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71'
COUNTERS_SHA='0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4'
COMMIT_COUNTERS_SHA='1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed'
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean']
A000_DISPATCHER=BASE/'run_a000_source_plan_with_post_exit_storage_v2_prepared.py'
A000_DISPATCHER_SHA='d73aa5d2218f358e79d5479de20b5082b345a994d0d4dd35d0a23516876eda28'
IMPORT_READER_SHA='4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa'
RECEIPT_READER_SHA='2e189122fe360f1925dda2e0409c321b775fe7eb6edf17c3f13ef067d1776362'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def stamp():return datetime.now(timezone.utc).isoformat()
def artifacts(source):return [source.with_suffix(s) for s in SUFFIXES if source.with_suffix(s).is_file()]
def artifact_inventory(source):return [{'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size} for p in artifacts(source)]
def save_atomic(path,value):
    temp=path.with_suffix('.json.tmp');temp.write_text(json.dumps(value,indent=2)+'\n',encoding='utf8',newline='\n')
    for attempt in range(60):
        try:os.replace(temp,path);return
        except PermissionError:
            if attempt==59:raise
            time.sleep(.1)
def lean_registry():
    registry=processes();owned=own_tree(os.getpid(),registry)
    leans={pid:r for pid,r in registry.items() if r.get('exe','').lower()=='lean.exe'}
    return {'checked_utc':stamp(),'own_Lean_pids':sorted(set(leans)&set(owned)),
      'foreign_Lean_processes':{str(pid):r for pid,r in leans.items() if pid not in owned}}
def initial_resources():return {'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()}
def detailed_process_registry():
    # Commands are hashed before recording; no unrelated command text is exposed.
    script="$OutputEncoding=[System.Text.UTF8Encoding]::new($false); Get-CimInstance Win32_Process | Where-Object { $_.Name -ieq 'lean.exe' -or $_.Name -ieq 'python.exe' } | ForEach-Object { [pscustomobject]@{pid=[int]$_.ProcessId;parent=[int]$_.ParentProcessId;name=$_.Name;command=$_.CommandLine;created_utc=$_.CreationDate.ToUniversalTime().ToString('o')} } | ConvertTo-Json -Depth 3 -Compress"
    p=subprocess.run(['powershell.exe','-NoLogo','-NoProfile','-NonInteractive','-Command',script],capture_output=True,text=True,encoding='utf8',check=True)
    raw=json.loads(p.stdout) if p.stdout.strip() else []
    return {int(r['pid']):r for r in ([raw] if isinstance(raw,dict) else raw)}

def compiler_lease(approved,thorough=False):
    registry=processes();owned=own_tree(os.getpid(),registry)
    leans={pid for pid,r in registry.items() if r.get('exe','').lower()=='lean.exe'}
    own_leans=leans&set(owned);allowed=set();violations=[]
    companion=approved['allowed_A000_dispatcher_identity']
    max_workers=approved['maximum_own_parallel_kernel_jobs']
    details=detailed_process_registry() if thorough else {}
    identity={'present':False,'exact_creation_and_command_checked_this_snapshot':False}
    if companion is not None:
        root=int(companion['pid'])
        if root in registry:
            identity.update(present=True,pid=root)
            valid=registry[root].get('exe','').lower()=='python.exe'
            if thorough:
                row=details.get(root)
                valid=bool(row and row['name'].lower()=='python.exe' and row['created_utc']==companion['created_utc']
                    and hashlib.sha256((row['command'] or '').encode('utf8')).hexdigest()==companion['command_utf8_sha256']
                    and A000_DISPATCHER.name in (row['command'] or '')) and valid
                identity['exact_creation_and_command_checked_this_snapshot']=True
                identity['matches_root_bound_identity']=valid
            if valid:allowed=own_tree(root,registry)
            else:violations.append('A000_COMPANION_IDENTITY_MISMATCH_OR_TRANSIENT_INCONSISTENT_SNAPSHOT')
    foreign=leans-set(owned)
    if not foreign<=allowed:violations.append('UNBOUND_FOREIGN_LEAN_PROCESS')
    if len(foreign)>1:violations.append('MORE_THAN_ONE_A000_LEAN_COMPANION')
    if len(own_leans)>max_workers or len(leans)>2:violations.append('GLOBAL_OR_OWN_LEAN_COUNT_EXCEEDS_APPROVED_MODE')
    if thorough:
        for pid,row in details.items():
            if pid==os.getpid() or row['name'].lower()!='python.exe':continue
            command=row['command'] or ''
            if re.search(r'\brun_(?:ht_ramsey|htpeo_ramsey)',command,re.I):violations.append('OTHER_HT_DISPATCHER_ACTIVE:'+str(pid))
            if A000_DISPATCHER.name.lower() in command.lower() and (companion is None or pid!=int(companion['pid'])):
                violations.append('UNBOUND_OR_MODE_TWO_A000_DISPATCHER_ACTIVE:'+str(pid))
    return {'checked_utc':stamp(),'thorough_CIM_identity_check':thorough,'global_Lean_pids':sorted(leans),
        'own_Lean_pids':sorted(own_leans),'allowed_A000_Lean_pids':sorted(foreign&allowed),
        'A000_identity_observation':identity,'maximum_own_parallel_kernel_jobs':max_workers,
        'maximum_total_global_Lean_importers':2,'violations':violations,
        'global_exclusion_is_snapshot_and_scheduler_not_a_foreign_process_kill_policy':True}

def sources_ready(plan,passed,manifest):
    entries={r['module']:r for r in plan['modules']};assert len(entries)==2103
    for r in plan['modules']:assert sha(r['file'])==r['sha256']
    chunkset=set(manifest['independent2048_kernel_chunk_names']);assert len(chunkset)==2048
    assert chunkset=={n for n in entries if '.Chunk.' in n}
    for item in manifest['kernel_sources']:
        name=item['module'];source=Path(entries[name]['file'])
        assert sha(source)==item['source_sha256'] and [x for x in read_imports(source) if x!='all']==item['direct_imports']
        assert not set(item['entire_custom_prerequisite_closure'])&chunkset
        for dep in item['entire_custom_prerequisite_closure']:
            assert dep in passed and passed[dep]['source_sha256']==entries[dep]['sha256']
    for n,row in passed.items():
        assert row['source_sha256']==entries[n]['sha256']
        assert set(Path(a['file']).resolve() for a in row['artifacts'])==set(p.resolve() for p in artifacts(Path(entries[n]['file'])))
        for a in row['artifacts']:assert sha(a['file'])==a['sha256'] and Path(a['file']).stat().st_size==a['bytes']
    return entries,chunkset
def main():
    assert len(sys.argv)==4 and sys.argv[1]=='--root-approved-kernel-j2-continuation'
    approval_path=Path(sys.argv[2]).resolve();approval_sha=sys.argv[3]
    assert approval_path.is_relative_to(BASE) and sha(approval_path)==approval_sha
    approved=json.loads(approval_path.read_bytes())
    allowed={'ROOT_APPROVED_HT_RAMSEY_REMAINING_KERNELS_ONE_J2_WITH_OPTIONAL_BOUND_A000':1,
      'ROOT_APPROVED_HT_RAMSEY_REMAINING_KERNELS_TWO_J2_ONLY':2}
    assert approved['status'] in allowed
    max_workers=allowed[approved['status']]
    assert approved['status'] in allowed and approved['reviewed_controller_sha256']==sha(__file__)
    assert sha(MANIFEST)==approved['reviewed_kernel_source_manifest_sha256']
    assert sha(PLAN)==approved['reviewed_original2103_plan_sha256']==PLAN_SHA
    assert sha(LEAN)==LEAN_SHA and sha(BASE/'matt_resource_guard.py')==GUARD_SHA
    assert sha(BASE/'native_resource_guard.py')==COUNTERS_SHA and sha(BASE/'resource_metrics.py')==COMMIT_COUNTERS_SHA
    assert approved['all_whole_importer_leases_held'] is True
    assert approved['maximum_total_global_Lean_importers']==2 and approved['maximum_own_parallel_kernel_jobs']==max_workers
    assert approved['endpoint_audit_invocations_this_lease']==0 and approved['all_non_kernel_HT_source_leases_held'] is True
    assert approved['selection_rule']=='ALL_STILL_COLD_INDEPENDENT_KERNELS_IN_FRESH_APPROVED_BOUNDARY_ORDER'
    assert sha(BASE/'lean_imports.py')==approved['reviewed_import_reader_sha256']==IMPORT_READER_SHA
    assert sha(BASE/'receipt_io.py')==approved['reviewed_receipt_reader_sha256']==RECEIPT_READER_SHA
    companion=approved['allowed_A000_dispatcher_identity']
    if max_workers==2:
        assert companion is None and approved['actual_A000_slot_returned_and_no_other_source_dispatcher'] is True
    elif companion is not None:
        assert sha(A000_DISPATCHER)==A000_DISPATCHER_SHA==companion['reviewed_dispatcher_source_sha256']
    exit_record=Path(approved['actual_natural_other_dispatcher_exit_record_file']).resolve()
    assert exit_record.is_relative_to(BASE) and sha(exit_record)==approved['actual_natural_other_dispatcher_exit_record_sha256']
    registry=processes()
    assert all(int(pid) not in registry for pid in approved['naturally_exited_other_source_dispatcher_pids'])
    initial_lease=compiler_lease(approved,thorough=True)
    assert not initial_lease['violations'] and not initial_lease['own_Lean_pids']
    lockfile=STAGE/'.fresh-replay.lock';assert lockfile.is_file() and lockfile.stat().st_size==1
    lock=lockfile.open('r+b');lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1)
    try:
        assert not REPORT.with_suffix('.json.tmp').exists(),'A pending prior canonical temporary receipt requires separate recovery review'
        raw=read_bytes_shared(REPORT);assert hashlib.sha256(raw).hexdigest()==approved['actual_quiescent_boundary_receipt_sha256']
        prior=json.loads(raw);assert prior['status']=='SCHEDULED_RESOURCE_CHECKPOINT' and prior.get('finished_utc')
        assert prior['modules']==json.loads(PLAN.read_bytes())['modules']
        assert not prior.get('failed_invocations') and not any(r['is_endpoint_audit'] for r in prior['builds'])
        passed={r['module']:r for r in prior['builds'] if r['exit']==0 and not r.get('stop_reason')}
        assert len(passed)==len(prior['builds'])
        plan=json.loads(PLAN.read_bytes());manifest=json.loads(MANIFEST.read_bytes());entries,chunkset=sources_ready(plan,passed,manifest)
        pending=[n for n in prior['compilation_order'] if n in chunkset and n not in passed]
        assert set(pending)==chunkset-set(passed)
        assert pending==approved['exact_current_remaining_kernel_names']
        for n in pending:
            p=Path(entries[n]['file'])
            assert not artifacts(p) and not p.with_suffix('.ir').exists(),'Unrecorded or partial output requires separate recovery review'
        for n,row in passed.items():
            if n not in chunkset:continue
            p=Path(entries[n]['file']).relative_to(STAGE)
            assert row['command'][1] in {'-j1','-j2'}
            expected=[str(LEAN),row['command'][1],'-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(p.with_suffix('.olean')),str(p)]
            assert row['command']==expected,'Previous kernel semantic command differs from the reviewed mixed-j1/j2 baseline'
        assert pending and approved['maximum_new_sources_this_lease']==len(pending)
        maximum_new_sources=len(pending)
        assert not plan.get('additional_dependency_libs'),'Any additional custom-library path requires a separately bound design'
        dependencies=BASE/'dependencies/4.33.1/mathlib'
        assert plan['version']=='4.33.1' and plan['mathlib_pin']=='0df444a360eaa60ab8c11dca51a86af692955474'
        cache_receipt=BASE/'mathlib-4.33.1-cache-retry.json'
        assert sha(cache_receipt)==approved['reviewed_official_cache_receipt_sha256']
        assert json.loads(cache_receipt.read_bytes())['status']=='PASS'
        assert sha(dependencies/'lake-manifest.json')==approved['reviewed_official_lake_manifest_sha256']
        gitrecord=BASE/'dependencies-4.33.1-verified-git.json'
        assert sha(gitrecord)==approved['reviewed_exact_nine_dependency_git_record_sha256']
        for pin in json.loads(gitrecord.read_bytes()):
            directory=dependencies if pin['name']=='mathlib' else dependencies/'.lake/packages'/pin['name']
            actual=subprocess.run(['git','rev-parse','HEAD'],cwd=directory,capture_output=True,text=True,check=True).stdout.strip()
            origin=subprocess.run(['git','remote','get-url','origin'],cwd=directory,capture_output=True,text=True,check=True).stdout.strip()
            assert actual==pin['rev'] and origin==pin['url']
        paths=[str(STAGE),str(dependencies/'.lake/build/lib/lean')]
        paths += [str(p/'.lake/build/lib/lean') for p in (dependencies/'.lake/packages').iterdir() if p.is_dir()]
        env=dict(os.environ);env['LEAN_PATH']=';'.join(paths);env['PATH']=str(LEAN.parent)+';'+env['PATH'];env['LEAN_NUM_THREADS']='2'
        serial=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        fresh_lease=compiler_lease(approved,thorough=True)
        assert not fresh_lease['violations'] and not fresh_lease['own_Lean_pids']
        old=BASE/('ht-ramsey-kernel-j2-continuation-'+serial+'-immutable-boundary.json')
        with old.open('xb') as f:f.write(raw)
        report=copy.deepcopy(prior);report.update(status='RUNNING',started_utc=stamp(),builds=list(prior['builds']))
        report.pop('finished_utc',None);report.pop('current_module',None);report.pop('waiting_for_module',None)
        report['preserved_boundary_resource_settings']=copy.deepcopy(prior.get('resource_settings',{}))
        report['preserved_boundary_parallel_kernel_source_policy']=copy.deepcopy(prior.get('parallel_kernel_source_policy',{}))
        report.setdefault('resource_settings',{}).update(runner_file=str(Path(__file__).resolve()),
          runner_source_sha256=sha(__file__),explicit_lean_threads_per_job=2,lean_shell_worker_flag='-j2',LEAN_NUM_THREADS='2',maximum_parallel_own_kernel_jobs=max_workers,
          own_job_guard_sha256=GUARD_SHA,counter_helper_sha256=COUNTERS_SHA,commit_counter_helper_sha256=COMMIT_COUNTERS_SHA)
        report['parallel_kernel_source_policy']={'controller_sha256':sha(__file__),'source_manifest_sha256':sha(MANIFEST),
          'root_approval':str(approval_path),'root_approval_sha256':approval_sha,'actual_immutable_boundary':str(old),
          'actual_immutable_boundary_sha256':sha(old),'maximum_parallel_jobs':max_workers,'maximum_new_sources_this_lease':maximum_new_sources,
          'no_nonchunk_or_whole_or_audit_sources':True,'original_source_bytes_pins_semantic_flags_and_guard_unchanged':True,
          'parent_is_only_canonical_receipt_writer':True,'no_storage_alias_copy_native_library_or_compaction_operations':True,
          'selection_rule':approved['selection_rule'],'exact_remaining_kernel_names_this_lease':list(pending),
          'actual_LEAN_NUM_THREADS':'2','approved_mode_status':approved['status'],'initial_global_lease':initial_lease,
          'immediate_pre_write_global_lease':fresh_lease,'allowed_A000_dispatcher_identity':companion,
          'no_actual_source_retry_or_non_kernel_auto_continuation_or_endpoint_audit':True,'prior_mixed_j1_j2_rows_preserved_literally':True,
          'no_attempt_resource_dispatch_may_wait_without_a_compiler':True,'selected_axioms_remain_a_separate_root_review_scope':True,
          'strict_per_child_guard_sha256':GUARD_SHA,'own_guard_policy':'6GiBown/5GiBcommit/6GiBphysical/4GBdisk dispatch;1GiBcommit/3GiBphysical/1GBdisk continuous;-j2'}
        report.setdefault('prior_attempt_receipts',[]).append({'file':str(old),'sha256':sha(old),'status':prior['status']})
        active={};new_invocations=0;stop_dispatch=False;stop_reason=None;failures=[];last_visible_active=None
        def worker(name):
            source=Path(entries[name]['file']);relative=source.relative_to(STAGE)
            assert sha(source)==entries[name]['sha256'] and not artifacts(source) and not source.with_suffix('.ir').exists()
            command=[str(LEAN),'-j2','-DmaxHeartbeats=0','-DmaxRecDepth=100000']
            for key,value in plan.get('lean_options',{}).items():command.append('-D'+key+'='+str(value).lower())
            command+=['-o',str(relative.with_suffix('.olean')),str(relative)]
            prefix=BASE/'guarded-source-logs'/('ht-kernel-j2-continuation-'+serial+'-'+hashlib.sha256(name.encode()).hexdigest()[:16])
            assert not Path(str(prefix)+'.stdout.txt').exists() and not Path(str(prefix)+'.stderr.txt').exists()
            return name,command,guarded_tree(command,STAGE,env,prefix,timeout=3600)
        save_atomic(REPORT,report)
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            while pending or active:
                registry=compiler_lease(approved)
                if registry['violations']:
                    stop_dispatch=True;stop_reason='EXTERNAL_COMPILER_LEASE_CONFLICT';report['foreign_Lean_lease_conflict']=registry
                if (BASE/'hold-third-worker-dispatch').exists():stop_dispatch=True;stop_reason=stop_reason or 'ROOT_COMPLETED_MODULE_BOUNDARY_HOLD'
                while pending and len(active)<max_workers and not stop_dispatch:
                    limit=maximum_new_sources
                    if new_invocations+len(active)>=limit:break
                    metrics=initial_resources()
                    if metrics['disk_free_bytes']<4_000_000_000 or metrics['free_physical_bytes']<6*2**30 or metrics['available_commit_bytes']<5*2**30:
                        report['parallel_continuation_waiting_dispatch_gates']=metrics
                        break
                    lease=compiler_lease(approved,thorough=True)
                    if lease['violations']:
                        stop_dispatch=True;stop_reason='EXTERNAL_COMPILER_LEASE_CONFLICT';report['foreign_Lean_lease_conflict']=lease;break
                    report['last_thorough_pre_dispatch_compiler_lease']=lease
                    if (BASE/'hold-third-worker-dispatch').exists():
                        stop_dispatch=True;stop_reason='ROOT_COMPLETED_MODULE_BOUNDARY_HOLD';break
                    name=pending.pop(0);future=pool.submit(worker,name);active[future]=name
                if list(active.values())!=last_visible_active:
                    report['current_modules']=list(active.values());save_atomic(REPORT,report);last_visible_active=list(active.values())
                if not active:
                    if stop_dispatch:break
                    if new_invocations>=maximum_new_sources:break
                    # No owned compiler is active while a resource dispatch gate
                    # waits. Recheck root hold/lease every2s; no hot retry or override.
                    time.sleep(2);continue
                completed,_=wait(active,timeout=.5,return_when=FIRST_COMPLETED)
                for future in completed:
                    name=active.pop(future)
                    try:name,command,guard=future.result()
                    except Exception as e:
                        stop_dispatch=True;stop_reason='OWN_CONTROLLER_OPERATIONAL_ERROR'
                        report.setdefault('parallel_controller_operational_errors',[]).append({'module':name,'error':str(e),'no_source_failure_inference':True});continue
                    if not guard['attempted']:
                        report.setdefault('parallel_no_attempt_dispatch_gates',[]).append({'module':name,'guard':guard})
                        pending.insert(0,name);save_atomic(REPORT,report)
                        time.sleep(2);continue
                    new_invocations+=1
                    stdout=Path(guard['stdout_file']).read_text(encoding='utf8',errors='replace');stderr=Path(guard['stderr_file']).read_text(encoding='utf8',errors='replace')
                    stops={'ENVIRONMENT_BLOCKED_DISK_RESERVE':'DISK_RESERVE','ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE':'PHYSICAL_MEMORY_RESERVE',
                      'ENVIRONMENT_BLOCKED_COMMIT_RESERVE':'COMMIT_RESERVE','ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT':'PRIVATE_MEMORY_CEILING',
                      'ENVIRONMENT_BLOCKED_OWN_ALLOCATION_FAILURE':'OWN_ALLOCATION_FAILURE','OPERATIONAL_ERROR':'OPERATIONAL_GUARD_ERROR','OPERATIONAL_TIMEOUT':'TIMEOUT'}
                    stop=stops.get(guard['state']);source=Path(entries[name]['file'])
                    row={'module':name,'command':command,'seconds':guard['seconds'],'exit':guard.get('exit'),'stdout':stdout,'stderr':stderr,
                      'is_endpoint_audit':False,'minimum_free_bytes':guard['minimum_disk_free_bytes'],'stop_reason':stop,
                      'started_utc':guard['started_utc'],'finished_utc':guard['finished_utc'],'owned_process_stop_output':guard['state'] if stop else None,
                      'own_job_resource_receipt':guard,'source_sha256':sha(source),
                      'executed_parallel_controller_source_sha256':sha(__file__),'exact_LEAN_NUM_THREADS':'2',
                      'explicit_lean_shell_worker_flag':'-j2','maximum_new_sources_this_lease':maximum_new_sources,'approved_parallel_worker_count':max_workers,
                      'third_worker_memory_observations':{'minimum_free_physical_bytes':guard['minimum_physical_available_bytes'],
                        'minimum_available_commit_bytes':guard['minimum_available_commit_bytes'],'peak_owned_private_bytes':guard.get('job_peak_aggregate_private_bytes')}}
                    assert row['source_sha256']==entries[name]['sha256']
                    if row['exit']==0 and not stop:
                        assert source.with_suffix('.olean').is_file()
                        row.update(artifacts=artifact_inventory(source),artifact_hash_provenance='MEASURED_IMMEDIATELY_AFTER_FRESH_PARALLEL_INDEPENDENT_KERNEL_COMPILATION')
                    report['builds'].append(row);save_atomic(REPORT,report);print(name,row['exit'],row['seconds'],flush=True)
                    if stop:stop_dispatch=True;stop_reason=stop
                    elif row['exit']!=0:failures.append(name);report.setdefault('failed_invocations',[]).append(name)
                if not pending and not active:break
                if stop_dispatch and not active:break
        report.pop('current_modules',None);report['finished_utc']=stamp()
        report['parallel_kernel_actual_new_invocations']=new_invocations
        report['parallel_kernel_pending_names_not_attempted']=pending
        report['kernel_j2_continuation_new_sources_attempted']=new_invocations
        assert new_invocations<=maximum_new_sources and report['builds'][:len(prior['builds'])]==prior['builds']
        sources_ready(plan,passed,manifest)
        for n in pending:
            p=Path(entries[n]['file'])
            assert not artifacts(p) and not p.with_suffix('.ir').exists()
        assert sha(old)==hashlib.sha256(raw).hexdigest() and sha(PLAN)==PLAN_SHA
        report['kernel_j2_continuation_selected_axiom_qualification']='NOT_ATTEMPTED_REQUIRES_SEPARATE_ROOT_REVIEW'
        report['final_global_Lean_registry']=compiler_lease(approved,thorough=True)
        report['final_resources']=initial_resources()
        if stop_reason and stop_reason not in {'ROOT_COMPLETED_MODULE_BOUNDARY_HOLD'}:
            report['status']='ENVIRONMENT_BLOCKED_PARALLEL_KERNEL_SCOPE' if stop_reason!='OWN_CONTROLLER_OPERATIONAL_ERROR' else 'OPERATIONAL_CHECKPOINT_PARALLEL_KERNEL_SCOPE'
            report['checkpoint_reason']=stop_reason
        elif failures:report['status']='BUILD_FAILED_OR_TIMED_OUT'
        else:
            report['status']='SCHEDULED_RESOURCE_CHECKPOINT'
            report['checkpoint_reason']='ROOT_COMPLETED_MODULE_BOUNDARY_HOLD' if stop_reason else 'ALL_REMAINING_INDEPENDENT_KERNELS_COMPLETE_NONCHUNK_NINE_WHOLE_ELEVEN_AND_AUDITS_WITHHELD'
        save_atomic(REPORT,report);print('KERNEL_J2_CONTINUATION_STATUS',report['status'],flush=True)
    finally:
        lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_UNLCK,1);lock.close()
if __name__=='__main__':main()
