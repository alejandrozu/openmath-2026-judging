"""Fresh topological compilation of every custom module, then endpoint axiom audits.

Uses only the plan's exact Lean version and verified pinned official dependencies.
Exactly97 SHA-bound previous-own DMS cold outputs may be reused as reviewed NTFS
links; they are separate from new M2 compilation and never overwritten. Existing
M2 StarCore pilot remains independent and immutable. Only3 new granular sources
and4 scoped prints may run. All21 whole-source modules/audits remain unattempted.
"""
from pathlib import Path
import json,re,subprocess,os,sys,time,hashlib,shutil,msvcrt
from lean_imports import read_imports,stripped as stripped_lean
from audit_axioms import parse as parse_axioms
from resource_metrics import snapshot as memory_snapshot
BASE=Path(__file__).resolve().parent
RUNNER_SOURCE_SHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
AXIOM_PARSER_SOURCE_SHA256=hashlib.sha256((BASE/'audit_axioms.py').read_bytes()).hexdigest()
project=sys.argv[1]

# This adapter is prepared only. Execution requires a separately reviewed slot.
M2_PROJECT_PLAN_HASHES = {'htpeo-erdos-m2': 'd75af96c5e21e79909e7a95646d0bf766609a46dd40bb0fc44e6308a6eb60ef6'}
M2_PREPARATION_SHA256 = 'c2eb16e66fd9f5bacf75ad470cd25846d412ca8780a8a7d24c119d4b366c6ee5'
assert project in M2_PROJECT_PLAN_HASHES, 'Exact reviewed HTP M2 project only'
assert '--htpeo-m2-reuse-execution-authorized' in sys.argv[3:], 'Separate root-approved reuse/source lease required'
from htpeo_m2_original97_hardlink_seed import verify_seed as m2_verify_seed
from htpeo_m2_original97_hardlink_seed import digest as m2_bound_digest
M2_LINK_POLICY_SHA256 = 'bab7476a702cb7ccf182e5c051f70ecc30a3b21dc14cec8c872487558f9a5092'
M2_LINK_HELPER_SHA256 = 'cf35eb78ccf5e36e7775eb0d4d676de2cf6cf57d5ee5b8cbb8878827a0f5ae4e'
assert m2_bound_digest(BASE/'htpeo_m2_original97_hardlink_seed.py') == M2_LINK_HELPER_SHA256
def m2_flag(name):
 assert name in sys.argv and sys.argv.index(name)+1<len(sys.argv), name
 return sys.argv[sys.argv.index(name)+1]
m2_execution_approval_path=Path(m2_flag('--reuse-execution-approval')).resolve()
m2_execution_approval_sha=m2_flag('--reuse-execution-approval-sha256')
assert m2_execution_approval_path.is_relative_to(BASE.resolve()) and m2_bound_digest(m2_execution_approval_path)==m2_execution_approval_sha
m2_execution_approval=json.loads(m2_execution_approval_path.read_bytes())
assert m2_execution_approval['status']=='ROOT_APPROVED_HTPEO_M2_EXACT97_REUSE_PLUS3_COLD_SOURCES_AND4_SCOPED_PRINTS'
assert m2_execution_approval['reviewed_runner_sha256']==RUNNER_SOURCE_SHA256
assert m2_execution_approval['reviewed_policy_sha256']==M2_LINK_POLICY_SHA256
assert m2_execution_approval['reviewed_seed_helper_sha256']==M2_LINK_HELPER_SHA256
m2_seed_sha=m2_flag('--reuse-seed-receipt-sha256')
assert m2_execution_approval['reviewed_completed_seed_receipt_sha256']==m2_seed_sha
m2_seed_check=m2_verify_seed(M2_LINK_POLICY_SHA256,m2_seed_sha)
m2_link_policy=json.loads((BASE/'htpeo-m2-original97-hardlink-policy-20261005.json').read_bytes())
m2_reuse_names=set(m2_link_policy['eligible97_module_names'])
m2_own_prior_pilot_name='StarCore'
m2_required_new_names=set(m2_link_policy['required3_new_cold_module_names'])
m2_allowed_scoped_audits={row['audit'] for row in m2_link_policy['audit_records']}
assert len(m2_reuse_names)==97 and len(m2_required_new_names)==3 and len(m2_allowed_scoped_audits)==1
m2_protected_output_paths={Path(row['M2_target']).resolve() for row in m2_link_policy['output_links']}
m2_protected_output_paths.update(Path(row['file']).resolve() for row in m2_link_policy['M2_StarCore_pilot_artifacts'])
assert len(m2_protected_output_paths)==98
assert m2_execution_approval['approved97_module_names']==m2_link_policy['eligible97_module_names']
assert m2_execution_approval['approved3_new_source_names']==m2_link_policy['required3_new_cold_module_names']
assert m2_execution_approval['approved4_endpoint_names']==m2_link_policy['selected4_endpoint_names']
assert m2_execution_approval['whole_scope_remains_deferred'] is True
assert '--m2-granular-execution-authorized' in sys.argv[3:] and '--resource-lease-confirmed' in sys.argv[3:], 'Root-reviewed granular scope and confirmed lease required'
assert '--defer-whole-imports' in sys.argv[3:] and '--full-mathlib-source-mode' not in sys.argv[3:], 'All literal whole-Mathlib descendants must remain deferred'
def m2_sha(file):
 h=hashlib.sha256()
 with Path(file).open('rb') as stream:
  for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
prepared_file=BASE/'m2-granular-execution-preparation-20261005.json'
assert m2_sha(prepared_file)==M2_PREPARATION_SHA256, 'Prepared scope changed'
m2_prepared=json.loads(prepared_file.read_text(encoding='utf8'))
m2_project=next(row for row in m2_prepared['projects'] if row['id']==project)
assert m2_sha(BASE/'m2-novel-formalization-source-scope-inventory-20261005.json')==m2_prepared['inventory_sha256'], 'Inventory changed'
assert m2_sha(BASE/'builds'/project/'build-plan.json')==M2_PROJECT_PLAN_HASHES[project], 'Exact source plan changed'
m2_frozen_plan=json.loads((BASE/'builds'/project/'build-plan.json').read_text(encoding='utf8'))
for row in m2_frozen_plan['modules']:
 assert m2_sha(row['file'])==row['sha256'], 'Frozen authored source changed: '+row['module']
assert m2_sha(BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe')==m2_prepared['compiler_binary_sha256'], 'Frozen compiler binary changed'
for filename,key in [('matt_resource_guard.py','guard_sha256'),('audit_axioms.py','axiom_parser_sha256'),('lean_imports.py','import_parser_sha256')]:
 assert m2_sha(BASE/filename)==m2_prepared[key], 'Reviewed helper changed: '+filename
for row in m2_project['exact_additional_library_closure']:
 assert m2_sha(row['file'])==row['source_sha256'], 'Additional library source changed: '+row['module']
for packet in m2_project['library_plans']:
 assert m2_sha(BASE/'builds'/packet['id']/'build-plan.json')==packet['plan_sha256'], 'Additional library plan changed'
for row in m2_project['audits']:
 assert m2_sha(BASE/'builds'/project/row['audit'])==row['source_sha256'], 'Frozen audit changed'
assert all(not row['additional_library_prerequisites'] for row in m2_project['sources'] if not row['deferred_whole_scope']), 'No uncompiled additional custom library may be silently admitted into a granular invocation'
worker_threads=int(sys.argv[2]) if len(sys.argv)>2 else 4
assert 1<=worker_threads<=4
third_worker_pilot='--pilot-third-slot' in sys.argv[3:]
third_worker_continuation='--guarded-third-slot' in sys.argv[3:]
third_worker_guarded=third_worker_pilot or third_worker_continuation
full_mathlib_source_mode='--full-mathlib-source-mode' in sys.argv[3:]
a000_whole_scope_only='--a000-whole-scope-only' in sys.argv[3:]
if a000_whole_scope_only:
 assert project=='sakana-a000224' and full_mathlib_source_mode and third_worker_guarded, 'Explicit prepared A000 five-module whole-library exception only'
independent_resource_mode='--continue-independent-after-resource-block' in sys.argv[3:]
defer_whole_import_mode='--defer-whole-imports' in sys.argv[3:]
if defer_whole_import_mode:
 assert project in M2_PROJECT_PLAN_HASHES and third_worker_guarded and not full_mathlib_source_mode, 'Only exact root-reviewed M2 granular scopes; whole descendants remain deferred'
if independent_resource_mode:
 assert project=='sakana-erdos169-fourap' and third_worker_continuation and not third_worker_pilot, 'Only the explicitly authorized E169 independent-DAG continuation'
novel_third_projects={'sakana-a000224','sakana-erdos169-fourap','htpeo-kobon471','sakana-a060957','sakana-a100475','sakana-ferrers',
 'sakana-erdos1060-uniform-partial','sakana-erdos829-log-five-thirds','sakana-opdp89-parity-sharp','sakana-FOCUS-E3','sakana-FOCUS-E3-pullback',
 'sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2','matt-unitary-current','htpeo-dms-current'}
if full_mathlib_source_mode:
 assert third_worker_guarded and project!='matt-unitary-current' and (project!='sakana-a000224' or a000_whole_scope_only),'Future selected full-library mode only; narrower Matt/A000 policies remain unchanged outside explicit A000 whole-scope mode'
legacy_a000_single_pilot=third_worker_pilot and project=='sakana-a000224' and not full_mathlib_source_mode
third_worker_tree_guarded=third_worker_guarded and not legacy_a000_single_pilot
third_disk_dispatch_bytes=8_000_000_000 if legacy_a000_single_pilot else 4_000_000_000
third_commit_dispatch_bytes=(11 if full_mathlib_source_mode else 5)*2**30 if third_worker_tree_guarded else 0
third_private_limit_bytes=(10 if full_mathlib_source_mode else 6)*2**30
resource_guard_name='full_mathlib_resource_guard.py' if full_mathlib_source_mode else 'matt_resource_guard.py'
novel_third_projects=set(M2_PROJECT_PLAN_HASHES)
if third_worker_guarded:
 assert project in novel_third_projects and worker_threads==1,'Only the explicitly authorized novelty-family guarded third-slot projects'
 assert shutil.disk_usage(BASE).free>=third_disk_dispatch_bytes,'Guarded third-worker initial disk gate'
 assert memory_snapshot()['free_physical_bytes']>=6*2**30,'Third-worker pilot requires initial 6 GiB free physical memory'
 assert memory_snapshot()['available_commit_bytes']>=third_commit_dispatch_bytes,'Guarded third-worker initial commit gate'
 if third_worker_tree_guarded:
  if full_mathlib_source_mode:from full_mathlib_resource_guard import guarded_tree
  else:from matt_resource_guard import guarded_tree
dest=BASE/'builds'/project
plan=json.loads((dest/'build-plan.json').read_text())
deferred_whole_names=set()
if defer_whole_import_mode:
 deferred_whole_names={row['module'] for row in m2_project['sources'] if row['deferred_whole_scope']}
 deferred_whole_names.update(row['audit'] for row in m2_project['audits'] if row['deferred_whole_scope'])
 deferred_whole_scope={'preparation_sha256':M2_PREPARATION_SHA256,
  'authored_transitive_whole_Mathlib_closure':{row['module']:row['whole_Mathlib_roots'] for row in m2_project['sources'] if row['deferred_whole_scope']},
  'audits_with_whole_Mathlib_roots':{row['audit']:row['whole_Mathlib_roots'] for row in m2_project['audits'] if row['deferred_whole_scope']},
  'additional_library_whole_scope':{row['module']:row['whole_Mathlib_roots'] for row in m2_project['exact_additional_library_closure'] if row['whole_Mathlib_roots']},
  'qualification':'No additional library is compiled by this adapter. Every reachable literal whole-library source and all authored/audit descendants are withheld.'}
if full_mathlib_source_mode:
 from full_mathlib_scope import classify as classify_full_mathlib
 from receipt_io import read_bytes_shared
 full_scope=classify_full_mathlib(plan)
 if a000_whole_scope_only:
  evidence=json.loads((BASE/'a000224-whole-module-audit-boundary-evidence.json').read_text())
  assert evidence['source_plan_sha256']==hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()
  expected={m['module']:m['source_sha256'] for m in evidence['five_authored_whole_modules']}
  assert set(full_scope['authored_transitive_whole_Mathlib_closure'])==set(expected) and len(expected)==5
  for m in plan['modules']:
   if m['module'] in expected:assert m['sha256']==expected[m['module']]
  for audit in evidence['selected_audits']:
   assert hashlib.sha256((dest/audit['audit']).read_bytes()).hexdigest()==audit['source_sha256']
 assert full_scope['direct_whole_Mathlib_import_modules'],'Whole-library mode must be justified by actual frozen imports'
 lease_file=BASE/'full-mathlib-source-lease.json';lease_raw=read_bytes_shared(lease_file);lease=json.loads(lease_raw)
 assert lease['holder_project']==project and lease['source_plan_sha256']==hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()
 if a000_whole_scope_only:assert lease.get('a000_whole_scope_only_authorized') is True,'Separate root review/lease required for this A000 five-module whole-import exception'
 assert lease['other_umbrella_compilers_confirmed_held_or_finished'] is True,'Explicit scientific-import handoff required'
 full_lock=(BASE/'.exclusive-full-mathlib-source.lock').open('a+b')
 if full_lock.seek(0,2)==0:full_lock.write(b'0');full_lock.flush()
 full_lock.seek(0);msvcrt.locking(full_lock.fileno(),msvcrt.LK_NBLCK,1)
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
 assert json.loads((BASE/('mathlib-'+plan['version']+'-cache-retry.json')).read_text())['status']=='PASS','Full official dependency cache import validation has not passed'
report=BASE/(project+'-linked-granular-fresh-build.json')
prior=None
if report.exists():
 prior=json.loads(report.read_text(encoding='utf8'))
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
# This exact granular closure has no additional custom-library prerequisite.
# DMS outputs are admitted only by reviewed links inside this M2 destination.
assert all(not row['additional_library_prerequisites'] for row in m2_project['sources'] if not row['deferred_whole_scope'])
if plan.get('mathlib_pin'):
 paths += [str(dependencies/'.lake/build/lib/lean')]
 paths += [str(p/'.lake/build/lib/lean') for p in (dependencies/'.lake/packages').iterdir() if p.is_dir()]
assert all(not Path(path).resolve().is_relative_to(Path(forbidden)) for path in paths for forbidden in m2_seed_check['forbidden_custom_LEAN_PATH_roots'])
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
plan['execution_route']='SEPARATE_ROOT_REVIEWED_HTPEO_M2_EXACT97_PRIOR_OWN_REUSE_PLUS3_NEW_GRANULAR_SOURCES'
plan['source_plan_sha256']=M2_PROJECT_PLAN_HASHES[project]
plan['m2_preparation_sha256']=M2_PREPARATION_SHA256
plan['baseline_runner_sha256']='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'
plan['failed_invocations']=[]
plan['selected_audit_axiom_review']=[]
plan['prior_own_DMS_cold_sources_reused']=m2_link_policy['modules']
plan['independent_existing_M2_StarCore_pilot']={'file':m2_link_policy['M2_StarCore_pilot'],
 'sha256':m2_link_policy['M2_StarCore_pilot_sha256'],'actual_row':m2_link_policy['M2_StarCore_pilot_actual_row'],
 'qualification':'Previously completed independent M2 pilot, not a current new source invocation'}
plan['reuse_identity_check']=m2_seed_check
plan['reuse_execution_approval']={'file':str(m2_execution_approval_path),'sha256':m2_execution_approval_sha}
plan['hard_no_write_policy']={'skip97_prior_own_linked_source_names':sorted(m2_reuse_names),
 'preserve_independent_own_StarCore_pilot':True,'protected_output_paths':[str(p) for p in sorted(m2_protected_output_paths)],
 'required3_new_cold_source_names':sorted(m2_required_new_names),'required_scoped_audits':sorted(m2_allowed_scoped_audits),
 'original_DMS119_receipt_immutable':m2_link_policy['original119_receipt_sha256'],
 'M2_StarCore_pilot_receipt_immutable':m2_link_policy['M2_StarCore_pilot_sha256'],
 'previous_own_cold_output_is_never_a_new_current_M2_compilation':True}
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
 plan['deferred_whole_import_policy']={'qualification':'ROOT_REVIEWED_M2_GRANULAR_ADAPTER_ONLY_WHOLE_MODULES_AND_AUDITS_NEED_SEPARATE_LITERAL_IMPORTER_LEASE',
  'exact_frozen_import_classification':deferred_whole_scope,'unattempted_whole_invocations':[]}
def digest(file):return hashlib.sha256(file.read_bytes()).hexdigest()
def artifacts(file):
 return [p for p in [file.with_suffix('.olean'),file.with_suffix('.olean.private'),file.with_suffix('.olean.server'),file.with_suffix('.ilean')] if p.exists()]
def artifact_inventory(file):
 return [{'file':str(p),'sha256':digest(p),'bytes':p.stat().st_size} for p in artifacts(file)]
retained={m2_own_prior_pilot_name:m2_link_policy['M2_StarCore_pilot_actual_row']};past_rows={}
resource_stop_reasons={'DISK_RESERVE','SCHEDULED_RESOURCE_CHECKPOINT','PHYSICAL_MEMORY_RESERVE','PRIVATE_MEMORY_CEILING','COMMIT_RESERVE','OWN_ALLOCATION_FAILURE','OPERATIONAL_GUARD_ERROR'}
deferred_resource_roots={}
if prior:
 attempt=len(prior.get('prior_attempt_receipts',[]))+1
 archived=BASE/(project+'-linked-granular-fresh-build-attempt-'+str(attempt)+'.json')
 assert not archived.exists(),'Immutable attempt receipt already exists'
 # Preserve the exact interrupted receipt, including killed invocations, before updating the main view.
 archived.write_bytes(report.read_bytes())
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
 if n in m2_reuse_names:continue
 if n in deferred_whole_names:
  plan['deferred_whole_import_policy']['unattempted_whole_invocations'].append({'module':n,'attempted':False,
    'is_endpoint_audit':n.endswith('.lean'),'classification':'SEPARATE_SOLE_LITERAL_IMPORTER_LEASE_REQUIRED'})
  save();print('WHOLE_IMPORT_LEASE_DEFERRED',project,n,flush=True);continue
 if third_worker_pilot and new_source_invocations>=1:
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='ROOT_AUTHORIZED_SINGLE_THIRD_WORKER_PILOT_COMPLETED';save();break
 if third_worker_continuation and (BASE/'hold-third-worker-dispatch').exists():
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='THIRD_WORKER_LEASE_HANDOFF_AT_COMPLETED_MODULE_BOUNDARY';save();break
 if independent_resource_mode:
  blockers=sorted(blocked_resource_roots(n))
  if blockers:
   plan['resource_deferred_invocations'].append({'module':n,'attempted':False,'is_endpoint_audit':n.endswith('.lean'),
    'blocked_by_resource_roots':blockers,'classification':'RESOURCE_ROOT_RETRY_DEFERRED' if n in deferred_resource_roots else 'RESOURCE_DEPENDENCY_BLOCK'})
   save();print('RESOURCE_DAG_DEFERRED',project,n,','.join(blockers),flush=True);continue
 assert n not in m2_reuse_names and n!=m2_own_prior_pilot_name,'Protected prior-own source must never dispatch'
 assert n in m2_required_new_names or n in m2_allowed_scoped_audits,'Only3 cold sources and one four-print audit may dispatch'
 audit=n.endswith('.lean');m={'file':str(dest/n),'module':n} if audit else modules[n]
 file=Path(m['file']);relative=file.relative_to(dest)
 protected_candidates=[file.with_suffix(s).resolve() for s in ['.olean','.olean.private','.olean.server','.ilean']]
 assert not any(p in m2_protected_output_paths for p in protected_candidates),'Cannot overwrite or rename a protected linked/pilot output'
 if not audit:assert hashlib.sha256(file.read_bytes()).hexdigest()==m['sha256'],n
 if third_worker_guarded:
  waiting=False
  while True:
   if third_worker_continuation and (BASE/'hold-third-worker-dispatch').exists():
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
 for key,value in plan.get('lean_options',{}).items():args.append('-D'+key+'='+str(value).lower())
 args+=['-o',str(relative.with_suffix('.olean')),str(relative)]
 plan['current_module']=n;save();start=time.monotonic()
 if third_worker_tree_guarded:
  logkey=hashlib.sha256(n.encode('utf8')).hexdigest()[:16]
  prefix=BASE/'guarded-source-logs'/(project+'-linked-granular-'+logkey+'-attempt-'+str(len(plan.get('prior_attempt_receipts',[]))))
  while True:
   guard=guarded_tree(args,dest,env,prefix,timeout=3600)
   if guard['attempted']:break
   if guard['state']!='NOT_INVOKED_RESOURCE_DISPATCH_GATE':
    plan['status']='ENVIRONMENT_BLOCKED_OPERATIONAL_GUARD';plan['unattempted_guard_failure']=guard
    plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save();raise SystemExit(0)
   plan['status']='WAITING_THIRD_WORKER_DISPATCH_GATES';plan.pop('current_module',None);plan['waiting_for_module']=n;save()
   if (BASE/'hold-third-worker-dispatch').exists():
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
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT';plan['checkpoint_reason']='GRANULAR_REMAINDER_FINISHED_WHOLE_IMPORT_LEASE_STILL_REQUIRED'
 elif deferred_resource_roots:plan['status']='ENVIRONMENT_BLOCKED_RESOURCE_DEPENDENCIES'
 elif plan.get('selected_incomplete_print_audits'):plan['status']='ENDPOINT_AUDIT_OUTPUT_INCOMPLETE'
 elif plan.get('selected_endpoint_uses_sorry'):plan['status']='COMPILES_BUT_ENDPOINT_USES_SORRY'
 elif plan.get('selected_unrecognized_axioms'):plan['status']='SELECTED_ENDPOINT_USES_UNRECOGNIZED_AXIOMS'
 elif plan.get('selected_native_evaluation'):plan['status']='PASS_WITH_NATIVE_EVALUATION'
 else:plan['status']='PASS_SELECTED_ENDPOINTS_WITH_UNFINISHED_BASELINES' if plan.get('unfinished_baseline_axioms') else 'PASS'
m2_final_identity_check=m2_verify_seed(M2_LINK_POLICY_SHA256,m2_seed_sha)
plan['final_reused_link_and_independent_pilot_identity_check']=m2_final_identity_check
actual_new_rows=[r for r in plan['builds'] if not r.get('is_endpoint_audit')]
assert all(r['module'] in m2_required_new_names for r in actual_new_rows)
actual_passes={r['module'] for r in actual_new_rows if r['exit']==0 and not r.get('stop_reason')}
actual_audits=[r for r in plan['builds'] if r.get('is_endpoint_audit')]
assert all(r['module'] in m2_allowed_scoped_audits for r in actual_audits)
scoped_complete=(actual_passes==m2_required_new_names and len(actual_audits)==1 and actual_audits[0]['exit']==0
 and actual_audits[0].get('selected_endpoint_print_coverage',{}).get('status')=='PASS'
 and not plan.get('selected_endpoint_uses_sorry') and not plan.get('selected_unrecognized_axioms')
 and not plan.get('selected_incomplete_print_audits'))
plan['granular_scope_qualification']={'status':('PASS_SCOPED_GRANULAR_WITH_NATIVE_EVALUATION' if plan.get('selected_native_evaluation') else 'PASS_SCOPED_GRANULAR_STANDARD_AXIOMS') if scoped_complete else 'INCOMPLETE_OR_UNQUALIFIED',
 'prior_own_DMS_cold_sources_reused':97,'independent_existing_M2_pilot_sources':1,
 'new_actual_current_cold_source_passes':len(actual_passes),'required_new_current_cold_sources':3,
 'scoped_selected_prints_required':4,'actual_selected_axiom_rows':plan['selected_audit_axiom_review'],
 'full122_project_PASS':False,'whole21_authored_sources_attempted':False,
 'qualification':'A granular exact101-body route consisting of97 previous-owned cold checks, one independent earlier M2 pilot and3 actual new source checks. Every whole-scope theorem/audit remains deferred; no novelty, score or placement consequence follows.'}
assert all(r['module'] not in deferred_whole_names for r in plan['builds'])
assert plan['status'] not in ['PASS','PASS_WITH_NATIVE_EVALUATION','PASS_SELECTED_ENDPOINTS_WITH_UNFINISHED_BASELINES'],'Cannot mark full frozen122-source project PASS on a granular-only route'
plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());plan.pop('current_module',None);save();print('PROJECT_STATUS',project,plan['status'],flush=True)
