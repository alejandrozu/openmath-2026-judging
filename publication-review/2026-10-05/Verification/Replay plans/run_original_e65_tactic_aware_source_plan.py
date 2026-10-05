"""Prepared exact recovered E65 source replay, separate from original-container execution.
No process starts unless this concrete adapter and a resource lease are root reviewed.
Initially only183 recovered FC sources without Mathlib or Mathlib.Tactic exposure; all whole resource descendants/audits deferred.
The separately verified Std-only source/audit is a candidate witness, never copied or
automatically counted as a new PASS here. Future whole mode requires183 own hashed
passes and an exact-plan sole lease, with10/11 GiB guard. Source bodies stay unchanged.
"""
from pathlib import Path
import json,re,subprocess,os,sys,time,hashlib,shutil,msvcrt
from lean_imports import read_imports,stripped as stripped_lean
from audit_axioms import parse as parse_axioms
from resource_metrics import snapshot as memory_snapshot
from receipt_io import read_bytes_shared,read_json_shared
BASE=Path(__file__).resolve().parent
RUNNER_SOURCE_SHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
AXIOM_PARSER_SOURCE_SHA256=hashlib.sha256((BASE/'audit_axioms.py').read_bytes()).hexdigest()
PROJECT='sundai-erdos3-original-image-source'
PREPARATION_SHA256='96f74d38af628c8763632c3a0869d7fa2404796ecf66de70fd13d6b0652e1e06'
PLAN_SHA256='0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15'
TACTIC_RESOURCE_SCOPE_SHA256='47ed60dae2f8c65df991072ece7152e80f5594f79f54fd51d5e88d5e31b738ab'
project=sys.argv[1]
worker_threads=int(sys.argv[2])
flags=sys.argv[3:]
assert project==PROJECT and worker_threads==1,'Exact original-source project and -j1 only'
assert '--original-e65-source-replay-authorized' in flags and '--resource-lease-confirmed' in flags,'Concrete root scope review and resource handoff required'
assert '--reviewed-runner-sha256='+RUNNER_SOURCE_SHA256 in flags,'Exact executed adapter SHA must match root-reviewed command'
third_worker_pilot='--pilot-third-slot' in flags
third_worker_continuation='--guarded-third-slot' in flags
assert third_worker_pilot != third_worker_continuation,'Choose one-source pilot or guarded continuation'
third_worker_guarded=third_worker_tree_guarded=True
full_mathlib_source_mode='--full-mathlib-source-mode' in flags
assert full_mathlib_source_mode != ('--defer-whole-imports' in flags),'Choose granular withholding or future exact whole-only lease'
a000_whole_scope_only=False
independent_resource_mode=False
defer_whole_import_mode=True
legacy_a000_single_pilot=False
def sha_file(file):return hashlib.sha256(Path(file).read_bytes()).hexdigest()
prep_file=BASE/'original-E65-source-replay-preparation-20261005.json'
assert sha_file(prep_file)==PREPARATION_SHA256,'Reviewed preparation changed'
prepared=json.loads(prep_file.read_text(encoding='utf8'))
assert sha_file(BASE/'original-E65-FC193-replay-inventory-20261005.json')==prepared['inventory_sha256']
for filename,digest_value in prepared['helper_hashes'].items():
 assert sha_file(BASE/filename)==digest_value,'Reviewed helper changed: '+filename
dest=BASE/'builds'/PROJECT
assert sha_file(dest/'build-plan.json')==PLAN_SHA256,'Frozen original-source plan changed'
plan=json.loads((dest/'build-plan.json').read_text(encoding='utf8'))
assert len(plan['modules'])==200 and len(plan['audit_modules'])==7 and len(set(plan['endpoints']))==56
assert not plan.get('additional_dependency_libs'),'No compatible FC library may be admitted'
for row in plan['modules']:
 assert sha_file(row['file'])==row['sha256'],'Frozen staged source changed: '+row['module']
for row in prepared['audits']:
 assert sha_file(row['file'])==row['source_sha256'],'Frozen selected audit changed'
compiler=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
assert sha_file(compiler)==prepared['compiler_binary_sha256'],'Compiler binary changed'
for row in prepared['exact_original_nine_packages']:
 actual=subprocess.run(['git','rev-parse','HEAD'],cwd=row['prepared_source_path'],capture_output=True,text=True,check=True).stdout.strip()
 assert actual==row['original_manifest_rev'],'Original package pin mismatch: '+row['name']
cache_raw=read_bytes_shared(BASE/'mathlib-4.33.1-cache-retry.json')
assert hashlib.sha256(cache_raw).hexdigest()==prepared['official_cache_PASS_receipt_sha256']
assert json.loads(cache_raw)['status']=='PASS','Exact official cache validation required'
from full_mathlib_scope import classify as classify_full_mathlib
full_scope=classify_full_mathlib(plan)
assert full_scope==prepared['exact_frozen_import_scope'],'Frozen import scope changed'
resource_scope_file=BASE/'original-E65-tactic-aware-resource-scope-20261005.json'
assert sha_file(resource_scope_file)==TACTIC_RESOURCE_SCOPE_SHA256,'Reviewed Tactic resource scope changed'
resource_scope=json.loads(resource_scope_file.read_text(encoding='utf8'))
assert resource_scope['source_plan_sha256']==PLAN_SHA256
assert sha_file(BASE/'original-E65-granular189-prerequisite-exposure-graph-20261005.json')==resource_scope['complete189_prerequisite_graph_sha256']
assert sha_file(BASE/'original-E65-granular189-official-source-artifact-manifest-20261005.json')==resource_scope['complete189_provider_manifest_sha256']
granular_names=set(resource_scope['truly_no_Mathlib_or_Tactic_custom_closed_subset']);assert len(granular_names)==183
whole_names=set(resource_scope['future_whole_resource_sources']);assert len(whole_names)==16
assert granular_names|whole_names|{prepared['Std_existing_qualified_reuse_candidate_only']['module']}=={m['module'] for m in plan['modules']}
candidate=prepared['Std_existing_qualified_reuse_candidate_only']
assert sha_file(candidate['qualified_record_file'])==candidate['qualified_record_sha256']
deferred_whole_names={candidate['module'],candidate['audit']}
if not full_mathlib_source_mode:
 deferred_whole_names.update(whole_names)
 deferred_whole_names.update(row['audit'] for row in prepared['audits'] if row['deferred_whole_scope'])
deferred_whole_scope={**full_scope,'Tactic_aware_resource_scope':resource_scope,'Tactic_aware_resource_scope_sha256':TACTIC_RESOURCE_SCOPE_SHA256,'Std_witness_candidate_pending':candidate,
 'qualification':'Only exact recovered source bodies; withheld whole descendants and separately qualified Std candidate are never silently counted as this route PASS.'}
if full_mathlib_source_mode:
 current_file=BASE/(PROJECT+'-fresh-build.json');current_raw=read_bytes_shared(current_file);current=json.loads(current_raw)
 assert current['source_plan_sha256']==PLAN_SHA256
 assert current.get('finished_utc') and current['status']=='SCHEDULED_RESOURCE_CHECKPOINT','Actual completed granular checkpoint required'
 frozen={m['module']:m for m in plan['modules']}
 successes={r['module']:r for r in current['builds'] if r.get('exit')==0 and not r.get('stop_reason') and not r.get('is_endpoint_audit')}
 assert granular_names<=set(successes),'All183 no-Mathlib/Tactic own granular successes required before any whole resource invocation'
 for name in granular_names:
  row=successes[name];assert row['source_sha256']==frozen[name]['sha256'] and '-o' in row['command']
  assert row.get('effective_lean_options')==frozen[name]['lean_options'],'Recorded FC semantic options required'
  file=Path(frozen[name]['file']);expected_paths=[p for p in [file.with_suffix('.olean'),file.with_suffix('.olean.private'),file.with_suffix('.olean.server'),file.with_suffix('.ilean'),file.with_suffix('.ir')] if p.exists()]
  actual=[{'file':str(p),'sha256':sha_file(p),'bytes':p.stat().st_size} for p in expected_paths]
  assert row.get('artifacts')==actual and file.with_suffix('.olean').exists(),'Own granular artifacts changed or missing'
 lease_raw=read_bytes_shared(BASE/'original-e65-source-replay-sole-lease.json');lease=json.loads(lease_raw)
 assert lease['holder_project']==PROJECT and lease['source_plan_sha256']==PLAN_SHA256
 assert lease['granular_completed_receipt_sha256']==hashlib.sha256(current_raw).hexdigest()
 assert lease['whole_library_solo_authorized'] is True and lease['other_source_compilers_confirmed_held_or_finished'] is True
 assert set(lease['allowed_source_names'])==whole_names
 assert set(lease['allowed_audit_names'])=={r['audit'] for r in prepared['audits'] if r['deferred_whole_scope']}
 assert lease['reviewed_runner_sha256']==RUNNER_SOURCE_SHA256
 full_lock=(BASE/'.exclusive-full-mathlib-source.lock').open('a+b')
 if full_lock.seek(0,2)==0:full_lock.write(b'0');full_lock.flush()
 full_lock.seek(0);msvcrt.locking(full_lock.fileno(),msvcrt.LK_NBLCK,1)
third_disk_dispatch_bytes=4_000_000_000
third_commit_dispatch_bytes=(11 if full_mathlib_source_mode else 5)*2**30
third_private_limit_bytes=(10 if full_mathlib_source_mode else 6)*2**30
resource_guard_name='full_mathlib_resource_guard.py' if full_mathlib_source_mode else 'matt_resource_guard.py'
assert shutil.disk_usage(BASE).free>=third_disk_dispatch_bytes,'Initial4GB disk dispatch gate'
initial_metrics=memory_snapshot()
assert initial_metrics['free_physical_bytes']>=6*2**30 and initial_metrics['available_commit_bytes']>=third_commit_dispatch_bytes,'Initial physical/commit gates'
if full_mathlib_source_mode:from full_mathlib_resource_guard import guarded_tree
else:from matt_resource_guard import guarded_tree
assert dest.resolve().is_relative_to((BASE/'builds').resolve())
# Persistent one-byte file; OS releases its byte lock on process exit. No deletion.
lock=(dest/'.fresh-replay.lock').open('a+b')
if lock.seek(0,2)==0:lock.write(b'0');lock.flush()
while True:
 lock.seek(0)
 try:msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1);break
 except OSError:time.sleep(5)
lean=BASE/'runtimes'/('lean-'+plan['version']+'-windows')/'bin/lean.exe'
assert lean.exists(),str(lean)
dependencies=BASE/'dependencies'/plan['version']/'mathlib'
if plan.get('mathlib_pin'):
 actual=subprocess.run(['git','rev-parse','HEAD'],cwd=dependencies,capture_output=True,text=True,check=True).stdout.strip()
 assert actual==plan['mathlib_pin'],(actual,plan['mathlib_pin'])
 assert (dependencies/'.lake/build/lib/lean/Mathlib.olean').exists(),'Required official Mathlib cache not ready'
 assert read_json_shared(BASE/('mathlib-'+plan['version']+'-cache-retry.json'))['status']=='PASS','Full official dependency cache import validation has not passed'
report=BASE/(project+'-fresh-build.json')
prior=None
if report.exists():
 prior=read_json_shared(report)
 if prior.get('finished_utc') and prior.get('status')!='RUNNING':
  assert prior['version']==plan['version'] and prior.get('mathlib_pin')==plan.get('mathlib_pin')
  assert prior['modules']==plan['modules'],'Completed receipt source plan changed'
  for m in plan['modules']:assert hashlib.sha256(Path(m['file']).read_bytes()).hexdigest()==m['sha256'],m['module']
  if not (prior.get('status','').startswith('ENVIRONMENT_BLOCKED') or prior.get('status')=='SCHEDULED_RESOURCE_CHECKPOINT'):
   print('COORDINATED_REPLAY_ALREADY_RECORDED',project,prior['status'],flush=True)
   raise SystemExit(0)
 elif prior.get('status')=='RUNNING':
  raise RuntimeError('Previous replay ended without a finished receipt; explicit recovery audit is required')
if a000_whole_scope_only:
 assert prior,'The A000 granular closure must have an actual checkpoint first'
 whole_names=set(full_scope['authored_transitive_whole_Mathlib_closure'])
 granular_names={m['module'] for m in plan['modules']}-whole_names
 actual_passes={r['module'] for r in prior['builds'] if r['exit']==0 and not r.get('stop_reason')}
 assert granular_names<=actual_passes,'Every one of the166 granular sources must first have its own successful cold output'
paths=[str(dest)]
for extra in plan.get('additional_dependency_libs',[]):
 extra_path=Path(extra).resolve()
 assert extra_path.is_relative_to(BASE.resolve()),'Dependency library outside this verification workspace'
 paths.append(str(extra_path))
if plan.get('mathlib_pin'):
 paths += [str(dependencies/'.lake/build/lib/lean')]
 paths += [str(p/'.lake/build/lib/lean') for p in (dependencies/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ);env['LEAN_PATH']=';'.join(paths);env['PATH']=str(lean.parent)+';'+env['PATH']
env['LEAN_NUM_THREADS']=str(worker_threads)
canonical=lambda n:n.replace('«','').replace('»','')
modules={canonical(m['module']):m for m in plan['modules']}
def imports(file):
 return read_imports(file)
ordered=[];seen=set();visiting=set()
def visit(n):
 if n in seen:return
 if n in visiting:raise RuntimeError('Import cycle: '+n)
 visiting.add(n)
 for dep in imports(modules[n]['file']):
  if dep in modules:visit(dep)
 visiting.remove(n);seen.add(n);ordered.append(n)
for n in modules:visit(n)
plan['compiler_version']=subprocess.run([str(lean),'--version'],capture_output=True,text=True).stdout.strip()
assert 'version '+plan['version']+',' in plan['compiler_version'],'Compiler version differs from frozen plan'
plan['status']='RUNNING';plan['builds']=[];plan['compilation_order']=ordered;plan['started_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
plan['execution_route']='EXACT_RECOVERED_E65_SOURCE_WINDOWS_OPERATIONAL_REPLAY_NOT_ORIGINAL_CONTAINER_EXECUTION'
plan['source_plan_sha256']=PLAN_SHA256
plan['preparation_sha256']=PREPARATION_SHA256
plan['Tactic_aware_resource_scope_sha256']=TACTIC_RESOURCE_SCOPE_SHA256
plan['baseline_runner_sha256']='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'
plan['original_container_executed']=False
plan['Std_external_witness_candidate_accepted']=False
plan['failed_invocations']=[]
plan['selected_audit_axiom_review']=[]
plan['resource_settings']={'LEAN_NUM_THREADS':worker_threads,'lean_shell_worker_flag':'-j'+str(worker_threads),'maxHeartbeats':0,'maxRecDepth':100000,
 'runner_file':str(Path(__file__).resolve()),'runner_source_sha256':RUNNER_SOURCE_SHA256,'axiom_parser_source_sha256':AXIOM_PARSER_SOURCE_SHA256}
if third_worker_guarded:
 plan['resource_settings']['third_worker_pilot' if third_worker_pilot else 'guarded_third_worker_continuation']={'maximum_new_source_invocations':1 if third_worker_pilot else None,'initial_disk_bytes':third_disk_dispatch_bytes,
  'initial_free_physical_bytes':6*2**30,'continuous_disk_reserve_bytes':1_000_000_000,
  'continuous_free_physical_reserve_bytes':3*2**30,'owned_compiler_private_memory_ceiling_bytes':third_private_limit_bytes,
  'initial_memory_snapshot':memory_snapshot(),'qualification':'ROOT_AUTHORIZED_MEASURED_THIRD_WORKER_PILOT' if third_worker_pilot else 'ROOT_AUTHORIZED_GUARDED_THIRD_WORKER_CONTINUATION'}
 if third_worker_tree_guarded:
  plan['resource_settings']['third_worker_pilot' if third_worker_pilot else 'guarded_third_worker_continuation'].update({
   'initial_available_commit_bytes':third_commit_dispatch_bytes,'continuous_available_commit_reserve_bytes':1*2**30,
   'owned_job_private_memory_ceiling_bytes':third_private_limit_bytes,'own_job_assignment_before_resume':'REQUIRED',
   'resource_guard_file':str(BASE/resource_guard_name),'resource_guard_sha256':hashlib.sha256((BASE/resource_guard_name).read_bytes()).hexdigest()})
 if full_mathlib_source_mode:
  plan['resource_settings']['full_mathlib_source_mode']={'authorization':'ROOT_APPROVED_FUTURE_10_GIB_WINDOWS_WHOLE_LIBRARY_MODE',
   'exact_frozen_import_classification':full_scope,'coordinated_lease':lease,'lease_sha256':hashlib.sha256(lease_raw).hexdigest(),
   'serialization':'Exclusive mode lock plus explicit verified handoff; legacy or narrower workers are governed by that handoff and are not silently stopped by this mode.'}
  if a000_whole_scope_only:
   plan['resource_settings']['full_mathlib_source_mode']['a000_exception']={'qualification':'EXPLICIT_ROOT_APPROVED_SEPARATE_FIVE_WHOLE_MODULES_PLUS_SELECTED_AUDIT_AFTER_166_GRANULAR_SUCCESSFUL_SOURCES',
     'source_boundary_evidence':str(BASE/'a000224-whole-module-audit-boundary-evidence.json'),
     'whole_modules':sorted(whole_names),'granular_actual_source_successes_required':len(granular_names)}
 if third_worker_continuation and project=='sakana-a000224':
  plan['resource_settings']['guarded_third_worker_continuation']['disk_gate_amendment']='ROOT_AUTHORIZED_4_GB_DISPATCH_AFTER_MEASURED_4_77_MB_PILOT_ARTIFACT'
 if project=='matt-unitary-current':
  plan['resource_settings']['third_worker_pilot' if third_worker_pilot else 'guarded_third_worker_continuation']['source_scope_authorization']='ROOT_AUTHORIZED_EXACT_26_AUTHORED_SOURCES_SELECTED_GENERIC_ENDPOINTS_AND_SEPARATE_NON_ACCEPTANCE_BASELINE_AUDITS_AFTER_ACTUAL_FULL_IMPORT_PASS'
if defer_whole_import_mode:
 plan['deferred_whole_import_policy']={'qualification':'EXACT_RECOVERED_ORIGINAL_SOURCE_ROUTE_WITH_PENDING_WHOLE_LEASE_AND_EXTERNAL_STD_WITNESS_NOT_CONTAINER_EXECUTION',
  'exact_frozen_import_classification':deferred_whole_scope,'unattempted_whole_invocations':[]}
def digest(file):return hashlib.sha256(file.read_bytes()).hexdigest()
def artifacts(file):
 return [p for p in [file.with_suffix('.olean'),file.with_suffix('.olean.private'),file.with_suffix('.olean.server'),file.with_suffix('.ilean'),file.with_suffix('.ir')] if p.exists()]
def artifact_inventory(file):
 return [{'file':str(p),'sha256':digest(p),'bytes':p.stat().st_size} for p in artifacts(file)]
retained={};past_rows={}
resource_stop_reasons={'DISK_RESERVE','SCHEDULED_RESOURCE_CHECKPOINT','PHYSICAL_MEMORY_RESERVE','PRIVATE_MEMORY_CEILING','COMMIT_RESERVE','OWN_ALLOCATION_FAILURE','OPERATIONAL_GUARD_ERROR'}
deferred_resource_roots={}
if prior:
 attempt=len(prior.get('prior_attempt_receipts',[]))+1
 archived=BASE/(project+'-fresh-build-attempt-'+str(attempt)+'.json')
 assert not archived.exists(),'Immutable attempt receipt already exists'
 # Preserve the exact interrupted receipt, including killed invocations, before updating the main view.
 archived.write_bytes(read_bytes_shared(report))
 plan['prior_attempt_receipts']=prior.get('prior_attempt_receipts',[])+[{'file':str(archived),'sha256':digest(archived),'status':prior['status']}]
 plan['resume_provenance']='OWN_FRESH_SUCCESSFUL_ARTIFACTS_AFTER_RESOURCE_INTERRUPTION'
 for row in prior['builds']:past_rows[row['module']]=row
 # Independent-DAG runs preserve deferred roots as actual historical resource
 # invocations. Restore those rows for a later ordinary retry and for safe
 # preservation of any partial artifacts; never reuse them as successful builds.
 for n,meta in prior.get('resource_deferred_roots',{}).items():
  if n not in past_rows:past_rows[n]=meta['invocation']
 if independent_resource_mode:
  for n in ordered:
   row=past_rows.get(n)
   if row and row.get('stop_reason') in resource_stop_reasons and row.get('exit')!=0:
    deferred_resource_roots[n]={'invocation':row,'immutable_previous_attempt_receipt':str(archived),'reason':row['stop_reason']}
 for n in ordered:
  row=past_rows.get(n)
  if not row or row.get('stop_reason') in resource_stop_reasons:continue
  file=Path(modules[n]['file'])
  assert digest(file)==modules[n]['sha256'],n
  if row['exit']==0:
   assert file.with_suffix('.olean').exists(),'Missing successful own artifact: '+n
   # Older successful receipts did not hash their output. Those are identified by their
   # cold-build exit-0 command and source hash, and hashed explicitly on this continuation.
   assert str(file.relative_to(dest)) in row['command'] and '-o' in row['command'],n
   current=artifact_inventory(file)
   if row.get('artifacts'):
    assert current==row['artifacts'],'Own successful artifact changed after recorded compilation: '+n
   row=dict(row);row['artifacts']=current;row['artifact_hash_provenance']=row.get('artifact_hash_provenance','MEASURED_ON_RESOURCE_CONTINUATION_OF_RECEIPT_MATCHED_COLD_BUILD')
   retained[n]=row;plan['builds'].append(row)
  else:
   # Do not repeat a genuine source failure merely because another module later hit a resource limit.
   retained[n]=row;plan['builds'].append(row);plan['failed_invocations'].append(n)
 plan['retained_successful_custom_modules']=sum(row['exit']==0 for row in retained.values())
if independent_resource_mode:
 plan['resource_settings']['independent_resource_dag_mode']={'authorization':'ROOT_AUTHORIZED_E169_INDEPENDENT_MODULE_ATTEMPTS_WITH_RESOURCE_ROOTS_AND_DESCENDANTS_EXPLICITLY_DEFERRED',
  'source_or_statement_changes':False,'resource_limits_unchanged':True,'deferred_is_never_pass':True}
 plan['resource_deferred_roots']=deferred_resource_roots
 plan['resource_deferred_invocations']=[]
source_dependencies={n:[dep for dep in imports(modules[n]['file']) if dep in modules] for n in ordered}
def blocked_resource_roots(n):
 if n in deferred_resource_roots:return {n}
 deps=source_dependencies[n] if n in source_dependencies else [dep for dep in imports(dest/n) if dep in modules]
 return set().union(*(blocked_resource_roots(dep) for dep in deps)) if deps else set()
def save():
 temporary=report.with_suffix('.json.tmp')
 temporary.write_text(json.dumps(plan,indent=2),encoding='utf8')
 for attempt in range(101):
  try:os.replace(temporary,report);break
  except PermissionError:
   if attempt==100:raise
   time.sleep(.05)
save()
new_source_invocations=0
for n in ordered+plan['audit_modules']+plan.get('non_acceptance_audit_modules',[]):
 if n in retained:continue
 if n in deferred_whole_names:
  plan['deferred_whole_import_policy']['unattempted_whole_invocations'].append({'module':n,'attempted':False,
    'is_endpoint_audit':n.endswith('.lean'),'classification':'EXTERNAL_STD_WITNESS_REVIEW_PENDING' if n in {candidate['module'],candidate['audit']} else 'SEPARATE_SOLE_MATHLIB_OR_TACTIC_RESOURCE_IMPORTER_LEASE_REQUIRED'})
  save();print('WHOLE_IMPORT_LEASE_DEFERRED',project,n,flush=True);continue
 if third_worker_pilot and new_source_invocations>=1:
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='ROOT_AUTHORIZED_SINGLE_THIRD_WORKER_PILOT_COMPLETED';save();break
 if third_worker_continuation and (BASE/'hold-original-e65-dispatch').exists():
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='THIRD_WORKER_LEASE_HANDOFF_AT_COMPLETED_MODULE_BOUNDARY';save();break
 if independent_resource_mode:
  blockers=sorted(blocked_resource_roots(n))
  if blockers:
   plan['resource_deferred_invocations'].append({'module':n,'attempted':False,'is_endpoint_audit':n.endswith('.lean'),
    'blocked_by_resource_roots':blockers,'classification':'RESOURCE_ROOT_RETRY_DEFERRED' if n in deferred_resource_roots else 'RESOURCE_DEPENDENCY_BLOCK'})
   save();print('RESOURCE_DAG_DEFERRED',project,n,','.join(blockers),flush=True);continue
 audit=n.endswith('.lean');m={'file':str(dest/n),'module':n} if audit else modules[n]
 file=Path(m['file']);relative=file.relative_to(dest)
 if not audit:assert hashlib.sha256(file.read_bytes()).hexdigest()==m['sha256'],n
 if third_worker_guarded:
  waiting=False
  while True:
   if third_worker_continuation and (BASE/'hold-original-e65-dispatch').exists():
    plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='THIRD_WORKER_LEASE_HANDOFF_WHILE_WAITING_WITHOUT_COMPILER'
    plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save();raise SystemExit(0)
   metrics=memory_snapshot();free=shutil.disk_usage(BASE).free
   if free>=third_disk_dispatch_bytes and metrics['free_physical_bytes']>=6*2**30 and metrics['available_commit_bytes']>=third_commit_dispatch_bytes:break
   if not waiting:
    waiting=True;plan['status']='WAITING_THIRD_WORKER_DISPATCH_GATES';plan.pop('current_module',None)
    plan['waiting_for_module']=n
    plan['dispatch_wait_initial_metrics']={'free_disk_bytes':free,**metrics};save()
    print('RESOURCE_GATE_WAIT',project,n,'disk',free,'physical',metrics['free_physical_bytes'],flush=True)
   time.sleep(2)
  if waiting:
   plan['status']='RUNNING';plan.pop('waiting_for_module',None)
   plan['dispatch_wait_recovery_metrics']={'free_disk_bytes':free,**metrics};save()
 if shutil.disk_usage(BASE).free<1_000_000_000:plan['status']='ENVIRONMENT_BLOCKED';plan['failure']='Disk free below 1 GB reserved threshold';save();break
 existing=artifacts(file)
 if existing:
  previous=past_rows.get(n)
  assert prior and previous and (previous.get('stop_reason') in resource_stop_reasons or audit),'Unattributed compiled artifact in fresh workspace: '+str(file)
  # A compiler killed for capacity may leave a partial output. Preserve its bytes without using it.
  preserved=[]
  for old in existing:
   target=old.with_name(old.name+'.interrupted-attempt-'+str(len(plan['prior_attempt_receipts'])))
   assert old.resolve().is_relative_to(dest.resolve()) and target.resolve().is_relative_to(dest.resolve())
   assert not target.exists(),str(target)
   sha=digest(old);old.rename(target);preserved.append({'file':str(target),'sha256':sha})
  plan.setdefault('preserved_partial_or_reaudited_outputs',[]).extend(preserved);save()
 args=[str(lean),'-j'+str(worker_threads),'-DmaxHeartbeats=0','-DmaxRecDepth=100000']
 effective_options=plan.get('lean_options',{}) if audit else m['lean_options']
 for key,value in effective_options.items():args.append('-D'+key+'='+str(value).lower())
 args+=['-o',str(relative.with_suffix('.olean')),str(relative)]
 plan['current_module']=n;save();start=time.monotonic()
 if third_worker_tree_guarded:
  logkey=hashlib.sha256(n.encode('utf8')).hexdigest()[:16]
  prefix=BASE/'guarded-source-logs'/(project+'-'+logkey+'-attempt-'+str(len(plan.get('prior_attempt_receipts',[]))))
  while True:
   guard=guarded_tree(args,dest,env,prefix,timeout=3600)
   if guard['attempted']:break
   if guard['state']!='NOT_INVOKED_RESOURCE_DISPATCH_GATE':
    plan['status']='ENVIRONMENT_BLOCKED_OPERATIONAL_GUARD';plan['unattempted_guard_failure']=guard
    plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save();raise SystemExit(0)
   plan['status']='WAITING_THIRD_WORKER_DISPATCH_GATES';plan.pop('current_module',None);plan['waiting_for_module']=n;save()
   if (BASE/'hold-original-e65-dispatch').exists():
    plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='THIRD_WORKER_LEASE_HANDOFF_WITHOUT_COMPILER'
    plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save();raise SystemExit(0)
   time.sleep(2)
  plan['status']='RUNNING';plan.pop('waiting_for_module',None)
  stdout=Path(guard['stdout_file']).read_text(encoding='utf8',errors='replace');stderr=Path(guard['stderr_file']).read_text(encoding='utf8',errors='replace')
  stop_reason={'ENVIRONMENT_BLOCKED_DISK_RESERVE':'DISK_RESERVE','ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE':'PHYSICAL_MEMORY_RESERVE',
   'ENVIRONMENT_BLOCKED_COMMIT_RESERVE':'COMMIT_RESERVE','ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT':'PRIVATE_MEMORY_CEILING',
   'ENVIRONMENT_BLOCKED_OWN_ALLOCATION_FAILURE':'OWN_ALLOCATION_FAILURE','OPERATIONAL_ERROR':'OPERATIONAL_GUARD_ERROR',
   'OPERATIONAL_TIMEOUT':'TIMEOUT'}.get(guard['state'])
  row={'module':n,'command':args,'seconds':guard['seconds'],'exit':guard.get('exit'), 'stdout':stdout,'stderr':stderr,
   'is_endpoint_audit':audit,'minimum_free_bytes':guard['minimum_disk_free_bytes'],'stop_reason':stop_reason,
   'started_utc':guard['started_utc'],'finished_utc':guard['finished_utc'],'owned_process_stop_output':guard.get('state') if stop_reason else None,
   'own_job_resource_receipt':guard}
  memory_observations={'minimum_free_physical_bytes':guard['minimum_physical_available_bytes'],
   'minimum_available_commit_bytes':guard['minimum_available_commit_bytes'],'peak_owned_private_bytes':guard.get('job_peak_aggregate_private_bytes')}
 else:
  p=subprocess.Popen(args,cwd=dest,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding='utf8')
  minimum_free=shutil.disk_usage(BASE).free;stop_reason=None;stop_output=None
  memory_observations={'minimum_free_physical_bytes':None,'peak_owned_private_bytes':0} if third_worker_guarded else None
  while True:
   free=shutil.disk_usage(BASE).free;minimum_free=min(minimum_free,free)
   if free<1_000_000_000:stop_reason='DISK_RESERVE'
   elif time.monotonic()-start>3600:stop_reason='TIMEOUT'
   if third_worker_guarded and p.poll() is None:
    metrics=memory_snapshot(p._handle)
    previous=memory_observations['minimum_free_physical_bytes']
    memory_observations['minimum_free_physical_bytes']=metrics['free_physical_bytes'] if previous is None else min(previous,metrics['free_physical_bytes'])
    memory_observations['peak_owned_private_bytes']=max(memory_observations['peak_owned_private_bytes'],metrics['private_bytes'])
    if not stop_reason and metrics['free_physical_bytes']<3*2**30:stop_reason='PHYSICAL_MEMORY_RESERVE'
    elif not stop_reason and metrics['private_bytes']>6*2**30:stop_reason='PRIVATE_MEMORY_CEILING'
   if stop_reason:
    killed=subprocess.run(['taskkill.exe','/PID',str(p.pid),'/T','/F'],capture_output=True,text=True,encoding='utf8',errors='replace')
    stop_output=killed.stdout+killed.stderr;stdout,stderr=p.communicate();break
   try:stdout,stderr=p.communicate(timeout=.5);break
   except subprocess.TimeoutExpired:pass
  row={'module':n,'command':args,'seconds':round(time.monotonic()-start,2),'exit':p.returncode,'stdout':stdout,'stderr':stderr,
       'is_endpoint_audit':audit,'minimum_free_bytes':minimum_free,'stop_reason':stop_reason,'owned_process_stop_output':stop_output}
 row['source_sha256']=digest(file)
 row['effective_lean_options']=effective_options
 row['semantic_option_qualification']='Explicit recovered FC strong options; entrant/audit options separately recorded, historical author invocation not inferred'
 if memory_observations is not None:row['third_worker_memory_observations']=memory_observations
 if row['exit']==0:row['artifacts']=artifact_inventory(file);row['artifact_hash_provenance']='MEASURED_IMMEDIATELY_AFTER_FRESH_COMPILATION'
 plan['builds'].append(row);save();print(project,n,row['exit'],row['seconds'],flush=True)
 if stop_reason in resource_stop_reasons:
  if independent_resource_mode:
   deferred_resource_roots[n]={'invocation':row,'reason':stop_reason,'current_attempt':True}
   plan['resource_deferred_roots']=deferred_resource_roots;save()
   if not audit:new_source_invocations+=1
   continue
  plan['status']='ENVIRONMENT_BLOCKED_DISK_RESERVE' if stop_reason=='DISK_RESERVE' else 'ENVIRONMENT_BLOCKED_THIRD_WORKER_MEMORY';save();break
 if not audit:new_source_invocations+=1
 if row['exit']!=0:
  plan['failed_invocations'].append(n);save()
  if third_worker_pilot:plan['status']='BUILD_FAILED_OR_TIMED_OUT';save();break
  continue
 if audit and n not in plan.get('non_acceptance_audit_modules',[]):
  review=parse_axioms(row['stdout']);plan['selected_audit_axiom_review']+=review
  requested=[canonical(x) for x in re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped_lean(file.read_text(encoding='utf8')),re.M)]
  printed={canonical(r['endpoint']) for r in review}
  missing=sorted(set(requested)-printed)
  row['selected_endpoint_print_coverage']={'requested_endpoints':requested,'parsed_endpoints':sorted(printed),
   'missing_endpoints':missing,'status':'PASS' if requested and not missing else 'INCOMPLETE'}
  if not requested or missing:plan.setdefault('selected_incomplete_print_audits',[]).append(n)
  if any(r['native_axioms'] for r in review):plan['selected_native_evaluation']=True
  if any(r['unrecognized_axioms'] for r in review):plan['selected_unrecognized_axioms']=True
 if audit and re.search(r'\bsorryAx\b',row['stdout']):
  if n in plan.get('non_acceptance_audit_modules',[]):plan['unfinished_baseline_axioms']=True
  else:plan['selected_endpoint_uses_sorry']=True;save()
else:
 if plan['failed_invocations']:plan['status']='BUILD_FAILED_OR_TIMED_OUT'
 elif defer_whole_import_mode and plan['deferred_whole_import_policy']['unattempted_whole_invocations']:
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='EXACT_RECOVERED_SCOPE_PARTIAL_WITH_WHOLE_LEASE_OR_EXTERNAL_STD_WITNESS_STILL_PENDING'
 elif deferred_resource_roots:plan['status']='ENVIRONMENT_BLOCKED_RESOURCE_DEPENDENCIES'
 elif plan.get('selected_incomplete_print_audits'):plan['status']='ENDPOINT_AUDIT_OUTPUT_INCOMPLETE'
 elif plan.get('selected_endpoint_uses_sorry'):plan['status']='COMPILES_BUT_ENDPOINT_USES_SORRY'
 elif plan.get('selected_unrecognized_axioms'):plan['status']='SELECTED_ENDPOINT_USES_UNRECOGNIZED_AXIOMS'
 elif plan.get('selected_native_evaluation'):plan['status']='PASS_WITH_NATIVE_EVALUATION'
 else:plan['status']='PASS_SELECTED_ENDPOINTS_WITH_UNFINISHED_BASELINES' if plan.get('unfinished_baseline_axioms') else 'PASS'
plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());plan.pop('current_module',None);save();print('PROJECT_STATUS',project,plan['status'],flush=True)
