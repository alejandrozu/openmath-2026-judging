"""Qualify only actual R52/R53 pilot records; read-only except one new metadata file."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
from lean_imports import read_imports,stripped
from receipt_io import read_bytes_shared
from native_resource_guard import processes
from resource_metrics import snapshot
import shutil
BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-ramsey-current'
REPORT=BASE/'htpeo-ramsey-current-fresh-build.json'
PLAN=STAGE/'build-plan.json'
MANIFEST=BASE/'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
CONTROLLER=BASE/'run_ht_ramsey_two_kernel_controller_prepared.py'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def jbytes(x):return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode('utf8')
raw=read_bytes_shared(REPORT);current=json.loads(raw);policy=current['parallel_kernel_source_policy']
assert current['status']=='SCHEDULED_RESOURCE_CHECKPOINT' and current.get('finished_utc')
assert current['checkpoint_reason']=='TWO_NEW_KERNEL_PILOT_COMPLETE_NO_CONTINUATION'
assert current['parallel_kernel_actual_new_invocations']==2 and not current.get('failed_invocations')
assert sha(CONTROLLER)==policy['controller_sha256']=='1994efb38b409b5e12bbec589128c348d110308a49069e656b027100a48ee52e'
assert sha(PLAN)=='94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
assert sha(MANIFEST)==policy['source_manifest_sha256']=='2c5963c0b5c5094b77206b80d9e02866a504d56991459a2f0ec3bacef147da15'
approval=Path(policy['root_approval']);assert sha(approval)==policy['root_approval_sha256']=='5758b0f2ec94628fc9beb9572818345fcc6ca9b8880b1d99d09f2eda2fc41293'
approved=json.loads(approval.read_bytes());assert approved['status']=='ROOT_APPROVED_HT_RAMSEY_TWO_INDEPENDENT_NEW_KERNEL_PILOT_ONLY'
old_file=Path(policy['actual_immutable_boundary']);assert sha(old_file)==policy['actual_immutable_boundary_sha256']==approved['actual_quiescent_boundary_receipt_sha256']=='28caa3bd84c930a8e4ddd995f234636464224d4dccf547c236bcd5abeebc86e2'
old=json.loads(old_file.read_bytes());assert len(old['builds'])==88 and len(current['builds'])==90
assert current['builds'][:88]==old['builds'],'Prior88 row content changed'
assert current['preserved_boundary_resource_settings']==old['resource_settings']
assert current['modules']==old['modules']==json.loads(PLAN.read_bytes())['modules']
plan=json.loads(PLAN.read_bytes());entries={r['module']:r for r in plan['modules']}
manifest=json.loads(MANIFEST.read_bytes());kernel={r['module']:r for r in manifest['kernel_sources']}
lean=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
assert sha(lean)=='af49bacfabaa1fea71332ca0feae0fa1a60912219d5902291adc79f905bffb8d'
cache=BASE/'mathlib-4.33.1-cache-retry.json'
assert sha(cache)==approved['reviewed_official_cache_receipt_sha256'] and json.loads(cache.read_bytes())['status']=='PASS'
gitfile=BASE/'dependencies-4.33.1-verified-git.json'
assert sha(gitfile)==approved['reviewed_exact_nine_dependency_git_record_sha256']
pins=[]
for pin in json.loads(gitfile.read_bytes()):
    path=BASE/'dependencies/4.33.1/mathlib'
    if pin['name']!='mathlib':path=path/'.lake/packages'/pin['name']
    head=subprocess.run(['git','rev-parse','HEAD'],cwd=path,capture_output=True,text=True,check=True).stdout.strip()
    origin=subprocess.run(['git','remote','get-url','origin'],cwd=path,capture_output=True,text=True,check=True).stdout.strip()
    assert head==pin['rev'] and origin==pin['url']
    pins.append({'name':pin['name'],'actual_HEAD':head,'actual_origin':origin})
for item in entries.values():assert sha(item['file'])==item['sha256']
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean']
for row in current['builds']:
    assert row['exit']==0 and not row.get('stop_reason') and not row['is_endpoint_audit']
    source=Path(entries[row['module']]['file']);assert row['source_sha256']==entries[row['module']]['sha256']
    actual=[p for suffix in SUFFIXES if (p:=source.with_suffix(suffix)).is_file()]
    assert set(p.resolve() for p in actual)=={Path(r['file']).resolve() for r in row['artifacts']}
    for artifact in row['artifacts']:
        assert sha(artifact['file'])==artifact['sha256'] and Path(artifact['file']).stat().st_size==artifact['bytes']
pilot=current['builds'][88:];assert {r['module'] for r in pilot}=={'RamseyCert.Chunk.R52','RamseyCert.Chunk.R53'}
assert [r['module'] for r in pilot]==approved['exact_current_remaining_kernel_names'][:2]
names={r['module'] for r in current['builds'][:88]};scope_rows=[];log_identity=[]
guard_sha=sha(BASE/'matt_resource_guard.py');assert guard_sha=='ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71'
counter_sha=sha(BASE/'native_resource_guard.py');commit_sha=sha(BASE/'resource_metrics.py')
expected_policy={'initial_disk_bytes':4_000_000_000,'initial_physical_bytes':6*2**30,'initial_available_commit_bytes':5*2**30,
    'continuous_disk_bytes':1_000_000_000,'continuous_physical_bytes':3*2**30,'continuous_available_commit_bytes':2**30,
    'own_job_private_bytes':6*2**30,'own_process_private_bytes':6*2**30,'poll_seconds':.25,'timeout_seconds':3600}
for row in pilot:
    name=row['module'];entry=entries[name];source=Path(entry['file']);relative=source.relative_to(STAGE)
    assert set(kernel[name]['entire_custom_prerequisite_closure'])<=names
    assert [d for d in read_imports(source) if d!='all']==kernel[name]['direct_imports']
    command=[str(BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000']
    for key,value in plan.get('lean_options',{}).items():command.append('-D'+key+'='+str(value).lower())
    command+=['-o',str(relative.with_suffix('.olean')),str(relative)]
    guard=row['own_job_resource_receipt']
    assert row['command']==guard['command']==command and Path(guard['cwd']).resolve()==STAGE.resolve()
    assert row['executed_parallel_controller_source_sha256']==sha(CONTROLLER)
    assert guard['attempted'] is True and guard['state']=='PASS' and guard['exit']==0
    assert guard['own_job_assignment_before_resume']=='PASS' and guard['resource_policy']==expected_policy
    assert guard['counter_helper_sha256']==counter_sha and guard['commit_counter_helper_sha256']==commit_sha
    assert row['started_utc']==guard['started_utc'] and row['finished_utc']==guard['finished_utc'] and row['seconds']==guard['seconds']
    assert guard['minimum_disk_free_bytes']>=1_000_000_000 and guard['minimum_physical_available_bytes']>=3*2**30 and guard['minimum_available_commit_bytes']>=2**30
    assert guard['job_peak_aggregate_private_bytes']<=6*2**30 and guard['job_peak_process_private_bytes']<=6*2**30
    initial=guard['initial_system_memory_snapshot'];assert initial['free_physical_bytes']>=6*2**30 and initial['available_commit_bytes']>=5*2**30
    for channel in ['stdout','stderr']:
        file=Path(guard[channel+'_file']);data=file.read_bytes()
        assert sha(file)==guard[channel+'_sha256'] and data.decode('utf8',errors='replace')==row[channel]
        assert row[channel]=='','Unexpected pilot diagnostic requires review'
        log_identity.append({'module':name,'channel':channel,'file':str(file),'sha256':sha(file),'bytes':len(data)})
    text=source.read_text(encoding='utf8');clean=stripped(text)
    assert clean.count('decide +kernel')==kernel[name]['literal_kernel_decide_sites']==3
    assert not re.search(r'\bnative_decide\b|\bsorry\b|^\s*axiom\s',clean,re.M)
    assert not set(kernel[name]['entire_custom_prerequisite_closure'])&set(manifest['independent2048_kernel_chunk_names'])
    scope_rows.append({'module':name,'source_sha256':sha(source),'unchanged_scientific_source_bytes':True,
        'frozen_source_internal_set_options':re.findall(r'^\s*set_option\s+(\S+)\s+(\S+)',clean,re.M),
        'semantic_CLI_options':plan.get('lean_options',{}),'literal_kernel_certificate_statements':re.findall(r'^theorem\s+[^\n]+',clean,re.M),
        'actual_command':command,'complete_shared_custom_prerequisite_count':len(kernel[name]['entire_custom_prerequisite_closure']),
        'current_own_artifacts':row['artifacts']})
registry=processes();leans={str(pid):r for pid,r in registry.items() if r.get('exe','').lower()=='lean.exe'}
assert not set(leans)&{str(r['own_job_resource_receipt']['root_pid']) for r in pilot},'A pilot root PID is still a live Lean process'
assert current['final_global_Lean_registry']['own_Lean_pids']==[] and current['final_global_Lean_registry']['foreign_Lean_processes']=={}
assert read_bytes_shared(REPORT)==raw,'Actual pilot receipt changed during read-only review'
parallel_start=max(datetime.fromisoformat(r['started_utc']) for r in pilot)
parallel_end=min(datetime.fromisoformat(r['finished_utc']) for r in pilot)
assert parallel_end>parallel_start
guards=[r['own_job_resource_receipt'] for r in pilot]
out=BASE/'ht-two-kernel-actual-R52-R53-readonly-qualified-20261005.json'
record={'status':'QUALIFIED_ACTUAL_TWO_INDEPENDENT_KERNEL_SOURCE_PILOT_ONLY_FULL_HT_PROJECT_INCOMPLETE',
    'qualified_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(__file__),
    'actual_pilot_receipt':str(REPORT),'actual_pilot_receipt_historical_sha256':hashlib.sha256(raw).hexdigest(),
    'root_pilot_approval_sha256':sha(approval),'exact_controller_sha256':sha(CONTROLLER),'original2103_plan_sha256':sha(PLAN),
    'kernel_source_manifest_sha256':sha(MANIFEST),'shared_guard_sha256':guard_sha,
    'current_pinned_runtime_sha256':sha(lean),'current_official_cache_PASS_receipt_sha256':sha(cache),'current_nine_HEAD_and_origin_rechecks':pins,
    'original88_immutable_boundary':str(old_file),'original88_immutable_boundary_sha256':sha(old_file),
    'prior88_rows_content_preserved_exactly':True,'prior88_row_sequence_canonical_content_sha256':hashlib.sha256(jbytes(old['builds'])).hexdigest(),
    'original2103_scientific_source_hashes_rechecked':2103,'all90_current_recorded_source_artifact_hashes_rechecked':True,
    'actual_new_source_checks':2,'actual_new_kernel_certificate_declarations_typechecked':6,
    'actual_source_scope_rows':scope_rows,'actual_complete_two_raw_invocations':pilot,'actual_raw_log_identities':log_identity,
    'actual_timing_overlap_seconds':(parallel_end-parallel_start).total_seconds(),
    'observed_global_resource_minima_across_both_guard_invocations':{
        'disk_free_bytes':min(g['minimum_disk_free_bytes'] for g in guards),
        'physical_available_bytes':min(g['minimum_physical_available_bytes'] for g in guards),
        'available_commit_bytes':min(g['minimum_available_commit_bytes'] for g in guards)},
    'per_own_job_private_peaks_bytes':{r['module']:r['own_job_resource_receipt']['job_peak_aggregate_private_bytes'] for r in pilot},
    'sum_of_separate_job_peak_private_bytes_not_a_synchronized_combined_measurement':sum(g['job_peak_aggregate_private_bytes'] for g in guards),
    'actual_controller_exit_all_Lean_absent_snapshot':current['final_global_Lean_registry'],
    'later_current_global_Lean_snapshot_not_the_pilot_interval':leans,
    'later_resource_and_process_snapshot_qualification':'Root has separately dispatched sole originalE65 after the pilot; the current snapshot is not claimed quiescent and this read-only helper starts no job.',
    'current_resources':{'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()},
    'scope_limits':['Exactly two new original R52/R53 sources with unchanged options/bodies; no selected endpoint axiom audit invoked.',
        'Quarter-second sampled global minima are observations over the two guarded intervals; no continuous mathematical lower bound or synchronized aggregate peak is claimed.',
        'Only this two-source concurrency pilot is qualified. Remaining kernel chunks may have different memory/runtime; no whole-library or future-continuation authorization follows.',
        'Full2103-source project, nine later granular modules, eleven whole modules and both organizer audits remain incomplete; no novelty/score/publication upgrade follows.'],
    'current_qualified_source_checkpoint_count':90,'full_project_source_count':2103,
    'full_project_or_selected_endpoint_scope_complete':False,'receipt_source_runner_register_docs_or_job_mutations':0}
with out.open('x',encoding='utf8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
print(json.dumps({'qualification':str(out),'qualification_sha256':sha(out),
    'actual_pilot_receipt_sha256':hashlib.sha256(raw).hexdigest(),'actual_sources':2,'prior88_preserved':True,
    'resource_minima':record['observed_global_resource_minima_across_both_guard_invocations'],
    'no_extra_jobs_or_source_mutations':True},indent=2))
