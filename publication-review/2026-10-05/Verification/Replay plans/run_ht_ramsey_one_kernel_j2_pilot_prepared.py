"""Prepared-only source-identical HT -j2 pilot; no execution without SHA-bound root lease.

Exactly one still-cold independent kernel source is selected from the freshly
approved quiescent receipt. Prior rows/artifacts are preserved. This source-only
pilot does not launch an axiom audit or qualify the three selected declarations.
"""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,msvcrt,os,re,subprocess,sys
from lean_imports import read_imports,stripped
from run_ht_ramsey_two_kernel_controller_prepared import (
    BASE,STAGE,PLAN,PLAN_SHA,REPORT,MANIFEST,LEAN,LEAN_SHA,GUARD_SHA,
    COUNTERS_SHA,COMMIT_COUNTERS_SHA,sha,stamp,artifacts,artifact_inventory,
    save_atomic,initial_resources,sources_ready,guarded_tree,processes,own_tree,
)
BASE_CONTROLLER_SHA='1994efb38b409b5e12bbec589128c348d110308a49069e656b027100a48ee52e'
MANIFEST_SHA='2c5963c0b5c5094b77206b80d9e02866a504d56991459a2f0ec3bacef147da15'
A000_DISPATCHER=BASE/'run_a000_source_plan_with_post_exit_storage_v2_prepared.py'
A000_DISPATCHER_SHA='d73aa5d2218f358e79d5479de20b5082b345a994d0d4dd35d0a23516876eda28'
IMPORT_READER_SHA='4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa'
RECEIPT_READER_SHA='2e189122fe360f1925dda2e0409c321b775fe7eb6edf17c3f13ef067d1776362'

def detailed_process_registry():
    # Commands are hashed before recording; no unrelated command text is exposed.
    script="$OutputEncoding=[System.Text.UTF8Encoding]::new($false); Get-CimInstance Win32_Process | Where-Object { $_.Name -ieq 'lean.exe' -or $_.Name -ieq 'python.exe' } | ForEach-Object { [pscustomobject]@{pid=[int]$_.ProcessId;parent=[int]$_.ParentProcessId;name=$_.Name;command=$_.CommandLine;created_utc=$_.CreationDate.ToUniversalTime().ToString('o')} } | ConvertTo-Json -Depth 3 -Compress"
    p=subprocess.run(['powershell.exe','-NoLogo','-NoProfile','-NonInteractive','-Command',script],capture_output=True,text=True,encoding='utf8',check=True)
    raw=json.loads(p.stdout) if p.stdout.strip() else []
    return {int(r['pid']):r for r in ([raw] if isinstance(raw,dict) else raw)}

def fresh_compiler_lease(approved):
    registry=processes();details=detailed_process_registry();mine=own_tree(os.getpid(),registry)
    assert not {p for p in mine if registry[p].get('exe','').lower()=='lean.exe'},'Pilot already has a Lean child'
    old=approved['actual_naturally_exited_HT_dispatcher']
    assert old['pid'] not in registry,'The approved old HT dispatcher PID is still present; no overlap or PID reuse is accepted'
    assert old['actual_exit_record_sha256'] and old['actual_exit_record_file']
    exit_record=Path(old['actual_exit_record_file']).resolve()
    assert exit_record.is_relative_to(BASE) and sha(exit_record)==old['actual_exit_record_sha256']
    companion=approved['allowed_A000_dispatcher_identity']
    allowed=set();companion_present=False
    if companion is not None:
        assert sha(A000_DISPATCHER)==A000_DISPATCHER_SHA==companion['reviewed_dispatcher_source_sha256']
        root=int(companion['pid'])
        if root in registry:
            r=details[root]
            assert r['name'].lower()=='python.exe' and r['created_utc']==companion['created_utc']
            assert hashlib.sha256((r['command'] or '').encode('utf8')).hexdigest()==companion['command_utf8_sha256']
            assert A000_DISPATCHER.name in (r['command'] or '')
            allowed=own_tree(root,registry);companion_present=True
    ht_dispatchers=[]
    for pid,r in details.items():
        if pid==os.getpid() or r['name'].lower()!='python.exe':continue
        if re.search(r'\brun_(?:ht_ramsey|htpeo_ramsey)',r['command'] or '',re.I):ht_dispatchers.append(pid)
    assert not ht_dispatchers,'Another HT dispatcher is active'
    leans={p for p,r in registry.items() if r.get('exe','').lower()=='lean.exe'}
    assert leans<=allowed and len(leans)<=1,'Only one identity-bound A000 Lean companion is allowed'
    return {'checked_utc':stamp(),'global_Lean_pids':sorted(leans),'allowed_A000_dispatcher_present':companion_present,
        'allowed_A000_Lean_pids':sorted(leans&allowed),'old_HT_dispatcher_absent':True,
        'other_HT_dispatchers_absent':True,'maximum_total_Lean_importers_with_new_pilot':2,
        'global_process_exclusion_is_a_fresh_boundary_snapshot_not_a_foreign_process_kill_policy':True}

def selected_source_profile(source):
    s=stripped(source.read_text(encoding='utf8'))
    declarations=re.findall(r'^\s*theorem\s+(\S+)\s*:',s,re.M)
    assert len(declarations)==len(set(declarations))==3
    assert len(re.findall(r'\bdecide\s+\+kernel\b',s))==3
    assert not re.search(r'\b(?:native_decide|bv_decide|sorry|axiom)\b',s)
    assert re.findall(r'^\s*namespace\s+(\S+)',s,re.M)==['RamseyCert']
    assert not re.search(r'^\s*#print\s+axioms\b',s,re.M),'No audit is part of this source-only pilot'
    return {'source_sha256':sha(source),'requested_future_selected_declarations':['RamseyCert.'+n for n in declarations],
        'literal_decide_kernel_sites':3,'static_native_or_admission_tokens':False,
        'selected_axiom_audit_attempted':False,'selected_standard_only_qualification':False,
        'future_audit_requires_separate_root_approval':True}

def main():
    assert len(sys.argv)==4 and sys.argv[1]=='--root-approved-one-kernel-j2-source-pilot'
    approval_path=Path(sys.argv[2]).resolve();approval_sha=sys.argv[3]
    assert approval_path.is_relative_to(BASE) and sha(approval_path)==approval_sha
    approved=json.loads(approval_path.read_bytes())
    assert approved['status']=='ROOT_APPROVED_HT_RAMSEY_ONE_NEW_KERNEL_J2_SOURCE_PILOT_ONLY'
    assert approved['reviewed_pilot_runner_sha256']==sha(__file__)
    assert sha(BASE/'run_ht_ramsey_two_kernel_controller_prepared.py')==BASE_CONTROLLER_SHA
    assert sha(MANIFEST)==approved['reviewed_kernel_source_manifest_sha256']==MANIFEST_SHA
    assert sha(PLAN)==approved['reviewed_original2103_plan_sha256']==PLAN_SHA
    assert sha(LEAN)==LEAN_SHA and sha(BASE/'matt_resource_guard.py')==GUARD_SHA
    assert sha(BASE/'native_resource_guard.py')==COUNTERS_SHA and sha(BASE/'resource_metrics.py')==COMMIT_COUNTERS_SHA
    assert sha(BASE/'lean_imports.py')==approved['reviewed_import_reader_sha256']==IMPORT_READER_SHA
    assert sha(BASE/'receipt_io.py')==approved['reviewed_receipt_reader_sha256']==RECEIPT_READER_SHA
    assert approved['maximum_total_global_Lean_importers']==2 and approved['maximum_new_sources_this_lease']==1
    assert approved['endpoint_audit_invocations_this_lease']==0 and approved['all_whole_importer_leases_held'] is True
    assert approved['selection_rule']=='FIRST_STILL_COLD_INDEPENDENT_KERNEL_IN_FRESH_APPROVED_BOUNDARY_ORDER'
    assert not (BASE/'hold-third-worker-dispatch').exists(),'Root boundary hold remains present'
    initial_lease=fresh_compiler_lease(approved)
    lockfile=STAGE/'.fresh-replay.lock';assert lockfile.is_file() and lockfile.stat().st_size==1
    lock=lockfile.open('r+b');lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1)
    try:
        assert not REPORT.with_suffix('.json.tmp').exists(),'A pending prior canonical temporary receipt requires separate recovery review'
        raw=read_bytes_shared(REPORT)
        assert hashlib.sha256(raw).hexdigest()==approved['actual_quiescent_boundary_receipt_sha256']
        prior=json.loads(raw);plan=json.loads(PLAN.read_bytes());manifest=json.loads(MANIFEST.read_bytes())
        assert prior['status']=='SCHEDULED_RESOURCE_CHECKPOINT' and prior.get('finished_utc')
        assert not prior.get('current_module') and not prior.get('current_modules')
        assert prior['modules']==plan['modules'] and not prior.get('failed_invocations')
        assert not any(r['is_endpoint_audit'] for r in prior['builds'])
        passed={r['module']:r for r in prior['builds'] if r['exit']==0 and not r.get('stop_reason')}
        assert len(passed)==len(prior['builds'])
        entries,chunkset=sources_ready(plan,passed,manifest)
        pending=[n for n in prior['compilation_order'] if n in chunkset and n not in passed]
        assert set(pending)==chunkset-set(passed) and pending==approved['exact_current_remaining_kernel_names']
        assert pending,'No remaining kernel source'
        for n in pending:
            p=Path(entries[n]['file'])
            assert not artifacts(p) and not p.with_suffix('.ir').exists(),'All pending kernel outputs must remain cold before dispatch'
        for n,row in passed.items():
            if n not in chunkset:continue
            p=Path(entries[n]['file']).relative_to(STAGE)
            assert row['command']==[str(LEAN),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(p.with_suffix('.olean')),str(p)],'Previous kernel semantic command differs from the reviewed -j1 baseline'
        name=pending[0];source=Path(entries[name]['file']);relative=source.relative_to(STAGE)
        assert not artifacts(source) and not source.with_suffix('.ir').exists(),'The selected source must be cold; no overwrite/recovery is authorized'
        item=next(x for x in manifest['kernel_sources'] if x['module']==name)
        assert all(d in passed for d in item['entire_custom_prerequisite_closure'])
        profile=selected_source_profile(source)
        assert not plan.get('additional_dependency_libs') and plan.get('lean_options',{})=={}
        assert plan['version']=='4.33.1' and plan['mathlib_pin']=='0df444a360eaa60ab8c11dca51a86af692955474'
        dependencies=BASE/'dependencies/4.33.1/mathlib'
        cache_receipt=BASE/'mathlib-4.33.1-cache-retry.json';gitrecord=BASE/'dependencies-4.33.1-verified-git.json'
        assert sha(cache_receipt)==approved['reviewed_official_cache_receipt_sha256']
        assert json.loads(cache_receipt.read_bytes())['status']=='PASS'
        assert sha(dependencies/'lake-manifest.json')==approved['reviewed_official_lake_manifest_sha256']
        assert sha(gitrecord)==approved['reviewed_exact_nine_dependency_git_record_sha256']
        pins=json.loads(gitrecord.read_bytes());assert len(pins)==9
        for pin in pins:
            directory=dependencies if pin['name']=='mathlib' else dependencies/'.lake/packages'/pin['name']
            assert subprocess.run(['git','rev-parse','HEAD'],cwd=directory,capture_output=True,text=True,check=True).stdout.strip()==pin['rev']
            assert subprocess.run(['git','remote','get-url','origin'],cwd=directory,capture_output=True,text=True,check=True).stdout.strip()==pin['url']
        paths=[str(STAGE),str(dependencies/'.lake/build/lib/lean')]
        paths += [str(p/'.lake/build/lib/lean') for p in (dependencies/'.lake/packages').iterdir() if p.is_dir()]
        env=dict(os.environ);env['LEAN_PATH']=';'.join(paths);env['PATH']=str(LEAN.parent)+';'+env['PATH'];env['LEAN_NUM_THREADS']='2'
        command=[str(LEAN),'-j2','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(relative.with_suffix('.olean')),str(relative)]
        final_preflight_lease=fresh_compiler_lease(approved)
        serial=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        old=BASE/('ht-ramsey-j2-one-source-'+serial+'-immutable-boundary.json')
        with old.open('xb') as f:f.write(raw)
        prefix=BASE/'guarded-source-logs'/('ht-j2-one-source-'+serial+'-'+hashlib.sha256(name.encode()).hexdigest()[:16])
        assert not Path(str(prefix)+'.stdout.txt').exists() and not Path(str(prefix)+'.stderr.txt').exists()
        report=copy.deepcopy(prior);report.update(status='RUNNING',started_utc=stamp(),builds=list(prior['builds']),current_module=name)
        report.pop('finished_utc',None);report.pop('waiting_for_module',None)
        report['preserved_boundary_resource_settings']=copy.deepcopy(prior.get('resource_settings',{}))
        report.setdefault('resource_settings',{}).update(runner_file=str(Path(__file__).resolve()),runner_source_sha256=sha(__file__),
            explicit_lean_threads_per_job=2,LEAN_NUM_THREADS='2',maximum_parallel_own_kernel_jobs=1,
            own_job_guard_sha256=GUARD_SHA,counter_helper_sha256=COUNTERS_SHA,commit_counter_helper_sha256=COMMIT_COUNTERS_SHA)
        report['one_kernel_j2_source_only_pilot_policy']={'runner_sha256':sha(__file__),'reviewed_base_controller_sha256':BASE_CONTROLLER_SHA,
            'root_approval_file':str(approval_path),'root_approval_sha256':approval_sha,'source_manifest_sha256':MANIFEST_SHA,
            'immutable_boundary_file':str(old),'immutable_boundary_sha256':sha(old),'prior_rows_preserved':len(prior['builds']),
            'selected_module':name,'selection_rule':approved['selection_rule'],'selected_source_profile':profile,
            'exact_command':command,'exact_LEAN_NUM_THREADS':'2','unchanged_semantic_lean_options':plan['lean_options'],
            'exact_LEAN_PATH':paths,'only_operational_worker_count_changed':True,'no_audit_or_continuation_or_native_library_or_storage_operations':True,
            'initial_global_lease':initial_lease,'immediate_pre_dispatch_global_lease':final_preflight_lease,
            'owned_guard_policy':'6GiBown/5GiBcommit/6GiBphysical/4GBdisk dispatch;1GiBcommit/3GiBphysical/1GBdisk continuous',
            'selected_three_axiom_classes_unqualified_until_separately_approved_audit':True}
        report.setdefault('prior_attempt_receipts',[]).append({'file':str(old),'sha256':sha(old),'status':prior['status']})
        save_atomic(REPORT,report)
        guard=guarded_tree(command,STAGE,env,prefix,timeout=3600)
        report.pop('current_module',None)
        if not guard['attempted']:
            report.setdefault('j2_pilot_no_attempt_dispatch_gates',[]).append({'module':name,'guard':guard})
            report['status']='SCHEDULED_RESOURCE_CHECKPOINT';report['checkpoint_reason']='ONE_KERNEL_J2_PILOT_NOT_INVOKED_RESOURCE_DISPATCH_GATE'
        else:
            assert sha(guard['stdout_file'])==guard['stdout_sha256'] and sha(guard['stderr_file'])==guard['stderr_sha256']
            stdout=Path(guard['stdout_file']).read_text(encoding='utf8',errors='replace');stderr=Path(guard['stderr_file']).read_text(encoding='utf8',errors='replace')
            stops={'ENVIRONMENT_BLOCKED_DISK_RESERVE':'DISK_RESERVE','ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE':'PHYSICAL_MEMORY_RESERVE',
                'ENVIRONMENT_BLOCKED_COMMIT_RESERVE':'COMMIT_RESERVE','ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT':'PRIVATE_MEMORY_CEILING',
                'ENVIRONMENT_BLOCKED_OWN_ALLOCATION_FAILURE':'OWN_ALLOCATION_FAILURE','OPERATIONAL_ERROR':'OPERATIONAL_GUARD_ERROR','OPERATIONAL_TIMEOUT':'TIMEOUT'}
            stop=stops.get(guard['state'])
            row={'module':name,'command':command,'seconds':guard['seconds'],'exit':guard.get('exit'),'stdout':stdout,'stderr':stderr,
                'is_endpoint_audit':False,'minimum_free_bytes':guard['minimum_disk_free_bytes'],'stop_reason':stop,
                'started_utc':guard['started_utc'],'finished_utc':guard['finished_utc'],'owned_process_stop_output':guard['state'] if stop else None,
                'own_job_resource_receipt':guard,'source_sha256':sha(source),'executed_j2_one_source_pilot_sha256':sha(__file__),
                'exact_LEAN_NUM_THREADS':'2','selected_source_profile':profile,
                'third_worker_memory_observations':{'minimum_free_physical_bytes':guard['minimum_physical_available_bytes'],
                    'minimum_available_commit_bytes':guard['minimum_available_commit_bytes'],'peak_owned_private_bytes':guard.get('job_peak_aggregate_private_bytes')}}
            assert row['source_sha256']==entries[name]['sha256']
            if guard['state']=='PASS' and row['exit']==0:
                assert source.with_suffix('.olean').is_file()
                row.update(artifacts=artifact_inventory(source),artifact_hash_provenance='MEASURED_AFTER_ONE_FRESH_SOURCE_IDENTICAL_J2_KERNEL_COMPILATION')
                report['status']='SCHEDULED_RESOURCE_CHECKPOINT';report['checkpoint_reason']='ONE_NEW_KERNEL_J2_SOURCE_PILOT_COMPLETE_NO_AUDIT_OR_CONTINUATION'
            elif stop:
                report['status']='ENVIRONMENT_BLOCKED_J2_ONE_SOURCE_PILOT';report['checkpoint_reason']=stop
            else:
                report['status']='BUILD_FAILED_OR_TIMED_OUT';report.setdefault('failed_invocations',[]).append(name)
            report['builds'].append(row)
        # Rehash every prior successful output and every original source. No prior
        # source row is replaced, and no other pending output is permitted to appear.
        assert report['builds'][:len(prior['builds'])]==prior['builds']
        sources_ready(plan,passed,manifest)
        for n in pending[1:]:assert not artifacts(Path(entries[n]['file'])) and not Path(entries[n]['file']).with_suffix('.ir').exists()
        assert sha(old)==hashlib.sha256(raw).hexdigest() and sha(PLAN)==PLAN_SHA and sha(MANIFEST)==MANIFEST_SHA
        report['finished_utc']=stamp();report['final_global_compiler_lease']=fresh_compiler_lease(approved)
        report['final_resources']=initial_resources();report['j2_source_pilot_selected_axiom_qualification']='NOT_ATTEMPTED_REQUIRES_SEPARATE_ROOT_REVIEW'
        save_atomic(REPORT,report);print('HT_ONE_KERNEL_J2_PILOT_STATUS',report['status'],flush=True)
    finally:
        lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_UNLCK,1);lock.close()

from receipt_io import read_bytes_shared
if __name__=='__main__':main()
