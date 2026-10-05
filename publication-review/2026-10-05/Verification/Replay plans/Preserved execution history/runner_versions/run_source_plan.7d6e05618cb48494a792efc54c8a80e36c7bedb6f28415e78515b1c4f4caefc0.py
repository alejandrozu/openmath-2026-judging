"""Fresh topological compilation of every custom module, then endpoint axiom audits.

Uses only the plan's exact Lean version and verified pinned official dependencies.
Original entrant artifacts are never reused. A resource-interrupted replay can retain
its own successful, receipt-matched artifacts; partial outputs are preserved by rename.
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
worker_threads=int(sys.argv[2]) if len(sys.argv)>2 else 4
assert 1<=worker_threads<=4
third_worker_pilot='--pilot-third-slot' in sys.argv[3:]
third_worker_continuation='--guarded-third-slot' in sys.argv[3:]
third_worker_guarded=third_worker_pilot or third_worker_continuation
full_mathlib_source_mode='--full-mathlib-source-mode' in sys.argv[3:]
independent_resource_mode='--continue-independent-after-resource-block' in sys.argv[3:]
if independent_resource_mode:
 assert project=='sakana-erdos169-fourap' and third_worker_continuation and not third_worker_pilot, 'Only the explicitly authorized E169 independent-DAG continuation'
novel_third_projects={'sakana-a000224','sakana-erdos169-fourap','htpeo-kobon471','sakana-a060957','sakana-a100475','sakana-ferrers',
 'sakana-erdos1060-uniform-partial','sakana-erdos829-log-five-thirds','sakana-opdp89-parity-sharp','sakana-FOCUS-E3','sakana-FOCUS-E3-pullback',
 'sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2','matt-unitary-current','htpeo-dms-current'}
if full_mathlib_source_mode:
 assert third_worker_guarded and project not in {'sakana-a000224','matt-unitary-current'},'Future selected full-library mode only; narrower Matt/A000 policies remain unchanged'
legacy_a000_single_pilot=third_worker_pilot and project=='sakana-a000224'
third_worker_tree_guarded=third_worker_guarded and not legacy_a000_single_pilot
third_disk_dispatch_bytes=8_000_000_000 if legacy_a000_single_pilot else 4_000_000_000
third_commit_dispatch_bytes=(11 if full_mathlib_source_mode else 5)*2**30 if third_worker_tree_guarded else 0
third_private_limit_bytes=(10 if full_mathlib_source_mode else 6)*2**30
resource_guard_name='full_mathlib_resource_guard.py' if full_mathlib_source_mode else 'matt_resource_guard.py'
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
if full_mathlib_source_mode:
 from full_mathlib_scope import classify as classify_full_mathlib
 from receipt_io import read_bytes_shared
 full_scope=classify_full_mathlib(plan)
 assert full_scope['direct_whole_Mathlib_import_modules'],'Whole-library mode must be justified by actual frozen imports'
 lease_file=BASE/'full-mathlib-source-lease.json';lease_raw=read_bytes_shared(lease_file);lease=json.loads(lease_raw)
 assert lease['holder_project']==project and lease['source_plan_sha256']==hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()
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
report=BASE/(project+'-fresh-build.json')
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
 if third_worker_continuation and project=='sakana-a000224':
  plan['resource_settings']['guarded_third_worker_continuation']['disk_gate_amendment']='ROOT_AUTHORIZED_4_GB_DISPATCH_AFTER_MEASURED_4_77_MB_PILOT_ARTIFACT'
 if project=='matt-unitary-current':
  plan['resource_settings']['third_worker_pilot' if third_worker_pilot else 'guarded_third_worker_continuation']['source_scope_authorization']='ROOT_AUTHORIZED_EXACT_26_AUTHORED_SOURCES_SELECTED_GENERIC_ENDPOINTS_AND_SEPARATE_NON_ACCEPTANCE_BASELINE_AUDITS_AFTER_ACTUAL_FULL_IMPORT_PASS'
def digest(file):return hashlib.sha256(file.read_bytes()).hexdigest()
def artifacts(file):
 return [p for p in [file.with_suffix('.olean'),file.with_suffix('.olean.private'),file.with_suffix('.olean.server'),file.with_suffix('.ilean')] if p.exists()]
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
 audit=n.endswith('.lean');m={'file':str(dest/n),'module':n} if audit else modules[n]
 file=Path(m['file']);relative=file.relative_to(dest)
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
  prefix=BASE/'guarded-source-logs'/(project+'-'+logkey+'-attempt-'+str(len(plan.get('prior_attempt_receipts',[]))))
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
 elif deferred_resource_roots:plan['status']='ENVIRONMENT_BLOCKED_RESOURCE_DEPENDENCIES'
 elif plan.get('selected_incomplete_print_audits'):plan['status']='ENDPOINT_AUDIT_OUTPUT_INCOMPLETE'
 elif plan.get('selected_endpoint_uses_sorry'):plan['status']='COMPILES_BUT_ENDPOINT_USES_SORRY'
 elif plan.get('selected_unrecognized_axioms'):plan['status']='SELECTED_ENDPOINT_USES_UNRECOGNIZED_AXIOMS'
 elif plan.get('selected_native_evaluation'):plan['status']='PASS_WITH_NATIVE_EVALUATION'
 else:plan['status']='PASS_SELECTED_ENDPOINTS_WITH_UNFINISHED_BASELINES' if plan.get('unfinished_baseline_axioms') else 'PASS'
plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());plan.pop('current_module',None);save();print('PROJECT_STATUS',project,plan['status'],flush=True)
