"""Cold source replay with bounded parallelism and a dependency-aware scheduler.

Only distinct custom module files run concurrently. Entrant sources are immutable.
All source modules and all generated endpoint audits are attempted and recorded.
"""
from pathlib import Path
import json,re,subprocess,os,sys,time,hashlib,shutil,concurrent.futures,msvcrt
from lean_imports import read_imports
from audit_axioms import parse as parse_axioms
BASE=Path(__file__).resolve().parent;project=sys.argv[1];dest=BASE/'builds'/project
plan=json.loads((dest/'build-plan.json').read_text());version=plan['version']
assert dest.resolve().is_relative_to((BASE/'builds').resolve())
lock=(dest/'.fresh-replay.lock').open('a+b')
if lock.seek(0,2)==0:lock.write(b'0');lock.flush()
while True:
 lock.seek(0)
 try:msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1);break
 except OSError:time.sleep(5)
report=BASE/(project+'-fresh-build.json');prior=None
if '--resume' in sys.argv[2:]:
 prior=json.loads(report.read_text(encoding='utf8'))
 assert prior['status'].startswith('ENVIRONMENT_BLOCKED') or prior['status']=='SCHEDULED_RESOURCE_CHECKPOINT',prior['status']
 assert prior['modules']==plan['modules'] and prior['version']==version and prior.get('mathlib_pin')==plan.get('mathlib_pin')
elif report.exists():
 raise RuntimeError('Existing replay receipt requires explicit --resume; no outputs will be overwritten')
lean=BASE/'runtimes'/('lean-'+version+'-windows')/'bin/lean.exe'
dependencies=BASE/'dependencies'/version/'mathlib'
assert lean.exists()
if plan.get('mathlib_pin'):
 actual=subprocess.run(['git','rev-parse','HEAD'],cwd=dependencies,capture_output=True,text=True,check=True).stdout.strip()
 assert actual==plan['mathlib_pin']
 cache=json.loads((BASE/('mathlib-'+version+'-cache-retry.json')).read_text())
 assert cache['status']=='PASS','Exact official dependency cache has not passed its full import validation'
paths=[str(dest)]+plan.get('additional_dependency_libs',[])
if plan.get('mathlib_pin'):
 paths+=[str(dependencies/'.lake/build/lib/lean')]+[str(p/'.lake/build/lib/lean') for p in (dependencies/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ);env['LEAN_PATH']=';'.join(paths);env['PATH']=str(lean.parent)+';'+env['PATH']
env['LEAN_NUM_THREADS']='2'
canonical=lambda n:n.replace('«','').replace('»','')
modules={canonical(m['module']):m for m in plan['modules']}
assert len(modules)==len(plan['modules'])
def imports(file):
 return read_imports(file)
needs={n:set(imports(m['file']))&modules.keys() for n,m in modules.items()}
for m in modules.values():
 file=Path(m['file']);assert hashlib.sha256(file.read_bytes()).hexdigest()==m['sha256']
slots=int(next((a for a in sys.argv[2:] if a.isdigit()),plan.get('max_parallel_modules',2)));assert 1<=slots<=4
shell_threads=1
env['LEAN_NUM_THREADS']=str(shell_threads)
plan.update({'compiler_version':subprocess.run([str(lean),'--version'],capture_output=True,text=True).stdout.strip(),
 'status':'RUNNING','builds':[],'failed_invocations':[],'selected_audit_axiom_review':[],'max_parallel_modules':slots,
 'resource_settings':{'LEAN_NUM_THREADS_per_process':shell_threads,'lean_shell_worker_flag':'-j'+str(shell_threads),'maxHeartbeats':0,'maxRecDepth':100000},
 'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'freshness':'All custom oleans absent before replay; source SHA256 checked before every invocation.'})
assert 'version '+version+',' in plan['compiler_version'],'Compiler version differs from frozen plan'
def digest(file):return hashlib.sha256(file.read_bytes()).hexdigest()
def artifacts(file):return [p for p in [file.with_suffix('.olean'),file.with_suffix('.olean.private'),file.with_suffix('.olean.server'),file.with_suffix('.ilean')] if p.exists()]
def inventory(file):return [{'file':str(p),'sha256':digest(p),'bytes':p.stat().st_size} for p in artifacts(file)]
retained={};past_rows={};resource_reasons={'DISK_RESERVE','SCHEDULED_RESOURCE_CHECKPOINT','PHYSICAL_MEMORY_RESERVE','PRIVATE_MEMORY_CEILING'}
if prior:
 attempt=len(prior.get('prior_attempt_receipts',[]))+1
 archived=BASE/(project+'-fresh-build-attempt-'+str(attempt)+'.json');assert not archived.exists();archived.write_bytes(report.read_bytes())
 plan['prior_attempt_receipts']=prior.get('prior_attempt_receipts',[])+[{'file':str(archived),'sha256':digest(archived),'status':prior['status']}]
 plan['freshness']='Own receipt-matched cold outputs retained after explicit resource/scheduling checkpoint; no entrant outputs are used.'
 for row in prior['builds']:past_rows[row['module']]=row
 for n in modules:
  row=past_rows.get(n)
  if not row or row.get('stop_reason') in resource_reasons:continue
  if row['exit']==0:
   file=Path(modules[n]['file']);assert file.with_suffix('.olean').exists(),n
   current=inventory(file)
   if row.get('artifacts'):assert current==row['artifacts'],'Own successful artifact changed: '+n
   assert str(file.relative_to(dest)) in row['command'] and '-o' in row['command'],n
   row=dict(row);row['artifacts']=current;row['artifact_hash_provenance']=row.get('artifact_hash_provenance','MEASURED_ON_RESOURCE_CONTINUATION_OF_RECEIPT_MATCHED_COLD_BUILD')
  else:plan['failed_invocations'].append(n)
  retained[n]=row;plan['builds'].append(row)
 plan['retained_successful_custom_modules']=sum(r['exit']==0 for r in retained.values())
for n,m in list(modules.items())+[(a,{'file':str(dest/a)}) for a in plan['audit_modules']+plan.get('non_acceptance_audit_modules',[])]:
 if n in retained:continue
 file=Path(m['file']);existing=artifacts(file)
 if existing:
  previous=past_rows.get(n)
  assert prior and previous and (previous.get('stop_reason') in resource_reasons or n.endswith('.lean')),'Unattributed compiled output: '+n
  for old in existing:
   target=old.with_name(old.name+'.interrupted-attempt-'+str(len(plan['prior_attempt_receipts'])))
   assert old.resolve().is_relative_to(dest.resolve()) and target.resolve().is_relative_to(dest.resolve()) and not target.exists()
   sha=digest(old);old.rename(target);plan.setdefault('preserved_partial_or_reaudited_outputs',[]).append({'file':str(target),'sha256':sha})
def save():
 tmp=report.with_suffix('.json.tmp');tmp.write_text(json.dumps(plan,indent=2),encoding='utf8')
 for attempt in range(101):
  try:os.replace(tmp,report);break
  except PermissionError:
   if attempt==100:raise
   time.sleep(.05)
save()
def invoke(n,audit=False):
 m={'file':str(dest/n),'module':n} if audit else modules[n]
 file=Path(m['file']);relative=file.relative_to(dest)
 if not audit:assert hashlib.sha256(file.read_bytes()).hexdigest()==m['sha256']
 assert not file.with_suffix('.olean').exists()
 args=[str(lean),'-j'+str(shell_threads),'-DmaxHeartbeats=0','-DmaxRecDepth=100000']
 for key,value in plan.get('lean_options',{}).items():args.append('-D'+key+'='+str(value).lower())
 args+=['-o',str(relative.with_suffix('.olean')),str(relative)]
 start=time.monotonic()
 p=subprocess.Popen(args,cwd=dest,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding='utf8')
 minimum_free=shutil.disk_usage(BASE).free;stop_reason=None;stop_output=None
 while True:
  free=shutil.disk_usage(BASE).free;minimum_free=min(minimum_free,free)
  if free<1_000_000_000:stop_reason='DISK_RESERVE'
  elif time.monotonic()-start>7200:stop_reason='TIMEOUT'
  if stop_reason:
   killed=subprocess.run(['taskkill.exe','/PID',str(p.pid),'/T','/F'],capture_output=True,text=True,encoding='utf8',errors='replace')
   stop_output=killed.stdout+killed.stderr;stdout,stderr=p.communicate();break
  try:stdout,stderr=p.communicate(timeout=.5);break
  except subprocess.TimeoutExpired:pass
 row={'module':n,'command':args,'seconds':round(time.monotonic()-start,2),'exit':p.returncode,'stdout':stdout,'stderr':stderr,
         'is_endpoint_audit':audit,'minimum_free_bytes':minimum_free,'stop_reason':stop_reason,'owned_process_stop_output':stop_output}
 row['source_sha256']=digest(file)
 if row['exit']==0:row['artifacts']=inventory(file);row['artifact_hash_provenance']='MEASURED_IMMEDIATELY_AFTER_FRESH_COMPILATION'
 return row
pending=[n for n in modules if n not in retained];completed=set(retained);passed={n for n,r in retained.items() if r['exit']==0};running={};environment_stop=False
plan['blocked_custom_imports']=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=slots) as pool:
 while pending or running:
  made_progress=False
  if shutil.disk_usage(BASE).free<1_000_000_000:environment_stop=True
  if not environment_stop:
   for n in list(pending):
    if len(running)>=slots:break
    if needs[n]<=completed and not needs[n]<=passed:
     pending.remove(n);completed.add(n);made_progress=True;plan['blocked_custom_imports'].append({'module':n,'failed_or_blocked_dependencies':sorted(needs[n]-passed)});continue
    if needs[n]<=passed:
     pending.remove(n);running[pool.submit(invoke,n)]=n;made_progress=True
  plan['current_modules']=list(running.values());plan['pending_module_count']=len(pending);save()
  if not running:
   if pending and not environment_stop and made_progress:continue
   if pending and not environment_stop:raise RuntimeError('Custom source import cycle or scheduler deadlock')
   break
  done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED,timeout=30)
  for future in done:
   n=running.pop(future);row=future.result();completed.add(n);plan['builds'].append(row)
   if row['exit']==0:passed.add(n)
   if row.get('stop_reason')=='DISK_RESERVE':environment_stop=True
   if row['exit']!=0:plan['failed_invocations'].append(n)
   save();print(project,len(completed),'/',len(modules),n,row['exit'],row['seconds'],flush=True)
if not environment_stop:
 for n in plan['audit_modules']+plan.get('non_acceptance_audit_modules',[]):
  if shutil.disk_usage(BASE).free<1_000_000_000:environment_stop=True;break
  plan['current_modules']=[n];save();row=invoke(n,True);plan['builds'].append(row)
  if row.get('stop_reason')=='DISK_RESERVE':environment_stop=True;save();break
  if row['exit']!=0:plan['failed_invocations'].append(n)
  if n not in plan.get('non_acceptance_audit_modules',[]):
   review=parse_axioms(row['stdout']);plan['selected_audit_axiom_review']+=review
   if any(r['native_axioms'] for r in review):plan['selected_native_evaluation']=True
   if any(r['unrecognized_axioms'] for r in review):plan['selected_unrecognized_axioms']=True
  if re.search(r'\bsorryAx\b',row['stdout']):
   if n in plan.get('non_acceptance_audit_modules',[]):plan['unfinished_baseline_axioms']=True
   else:plan['selected_endpoint_uses_sorry']=True
  save();print(project,n,row['exit'],row['seconds'],flush=True)
if environment_stop:plan['status']='ENVIRONMENT_BLOCKED_DISK_RESERVE'
elif plan['failed_invocations'] or plan['blocked_custom_imports']:plan['status']='BUILD_FAILED_OR_TIMED_OUT'
elif plan.get('selected_endpoint_uses_sorry'):plan['status']='COMPILES_BUT_ENDPOINT_USES_SORRY'
elif plan.get('selected_unrecognized_axioms'):plan['status']='SELECTED_ENDPOINT_USES_UNRECOGNIZED_AXIOMS'
elif plan.get('selected_native_evaluation'):plan['status']='PASS_WITH_NATIVE_EVALUATION'
elif plan.get('unfinished_baseline_axioms'):plan['status']='PASS_SELECTED_ENDPOINTS_WITH_UNFINISHED_BASELINES'
else:plan['status']='PASS'
plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());plan.pop('current_modules',None);save()
print('PROJECT_STATUS',project,plan['status'],flush=True)
