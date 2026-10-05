"""Independently replay every frozen Luke source through direct Lean CLI.

This adapter is distinct from the authors' native-Lake precompile policy.
Only outputs attributable to this fresh replay may be reused with --resume.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,time

parser=argparse.ArgumentParser();parser.add_argument('--resume',action='store_true');parser.add_argument('--jobs',type=int,choices=[1,4],default=1);args=parser.parse_args()
base=Path(__file__).resolve().parent
dest=base/'builds/luke-k4-ramsey-current-direct'
frozen=json.loads((dest/'build-plan.json').read_text(encoding='utf8'))
report=base/'luke-k4-ramsey-current-direct-fresh-build.json'
assert json.loads((base/'mathlib-4.34.1-cache-retry.json').read_text(encoding='utf8'))['status']=='PASS'
lean=base/'runtimes/lean-4.34.1-windows/bin/lean.exe'
out=dest/'.lake/build/lib/lean';out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ);env['PATH']=str(lean.parent)+';'+env['PATH'];env['LEAN_NUM_THREADS']=str(args.jobs)
env['LEAN_PATH']=';'.join([str(out),*frozen['dependency_library_paths']])
modules={m['module']:m for m in frozen['modules']}
custom_deps={n:[d for d in re.findall(r'^\s*import\s+(\S+)',Path(m['file']).read_text(encoding='utf8'),re.M) if d in modules] for n,m in modules.items()}
ordered=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for d in custom_deps[n]:visit(d)
 ordered.append(n)
for n in modules:visit(n)
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def artifacts():
 return {str(p.relative_to(out)):{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in out.rglob('*') if p.is_file()}
def dependency_objects():
 result={}
 for library in frozen['dependency_library_paths']:
  build=Path(library).parent.parent
  for p in build.rglob('*'):
   if p.is_file() and p.name.endswith(('.c.o','.cpp.o','.dll','.a','.lib')):
    stat=p.stat();result[str(p)]={'bytes':stat.st_size,'mtime_ns':stat.st_mtime_ns}
 return result

if args.resume:
 assert report.exists(),'Only our existing receipt can authorize resource resume'
 prior_bytes=report.read_bytes();prior=json.loads(prior_bytes)
 assert prior['status']=='ENVIRONMENT_BLOCKED_DISK_RESERVE','Resume is restricted to an explicitly recorded resource stop'
 for k in ['id','commit','version','mathlib_pin','route']:assert prior[k]==frozen[k], 'Frozen route identity changed'
 assert {m['module']:m['sha256'] for m in prior['modules']}=={n:m['sha256'] for n,m in modules.items()}
 assert artifacts()==prior['fresh_custom_artifact_inventory'],'Our preserved partial output inventory changed'
 plan=prior
 plan.setdefault('resume_attempts',[]).append({'started_utc':stamp(),'prior_receipt_sha256':hashlib.sha256(prior_bytes).hexdigest(),
  'reuse_scope':'Only PASS module artifacts recorded by this own fresh replay; no author-supplied proof cache',
  'starting_free_bytes':shutil.disk_usage(base).free})
 states={n:s for n,s in prior.get('module_states',{}).items() if s=='PASS'}
 plan['status']='RUNNING_RESUMED';plan.pop('finished_utc',None);plan.setdefault('resume_reused_modules',[])
else:
 assert not list(out.rglob('*')),'This independent direct route must start with no custom proof outputs'
 assert not report.exists(),'Do not overwrite an existing replay receipt; use explicit reviewed resource resume'
 plan=dict(frozen);states={}
 plan.update({'status':'RUNNING','builds':[],'started_utc':stamp(),'compilation_order':ordered,
  'resume_attempts':[],'resume_reused_modules':[], 'initial_custom_artifact_count':0,
  'resource_environment':{'LEAN_NUM_THREADS':str(args.jobs)},
  'CLI_worker_flags':'Explicit -j'+str(args.jobs)+' on each Lean process; the frozen WeightedCandidate resource policy -j1 is preserved',
  'external_dependency_objects_before':dependency_objects()})

def save():
 tmp=report.with_suffix('.json.tmp')
 with tmp.open('w',encoding='utf8') as f:json.dump(plan,f,indent=2);f.flush();os.fsync(f.fileno())
 for attempt in range(60):
  try:
   os.replace(tmp,report);break
  except PermissionError:
   if attempt==59:raise
   time.sleep(.1)
plan['current_resource_environment']={'LEAN_NUM_THREADS':str(args.jobs),'CLI_jobs':args.jobs,'WeightedCandidate_CLI_jobs':1}
save()
compiler=subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf8',env=env)
plan['compiler_version_output']=compiler.stdout.strip()
assert compiler.returncode==0 and ('version '+frozen['version']+',') in compiler.stdout,'Installed compiler does not match frozen toolchain'
for n,m in modules.items():
 assert hashlib.sha256(Path(m['file']).read_bytes()).hexdigest()==m['sha256'],n+' staged source changed'
 assert hashlib.sha256(Path(m['frozen_source']).read_bytes()).hexdigest()==m['sha256'],n+' frozen author source changed'
manifest=json.loads((dest/'lake-manifest.json').read_text(encoding='utf8'))
identity_root=Path(frozen['dependency_identity_root']);plan['dependency_preflight']=[]
for package in manifest['packages']:
 path=identity_root/manifest['packagesDir']/package['name']
 head=subprocess.run(['git','-C',str(path),'rev-parse','HEAD'],capture_output=True,text=True,encoding='utf8')
 origin=subprocess.run(['git','-C',str(path),'remote','get-url','origin'],capture_output=True,text=True,encoding='utf8')
 match=head.returncode==0 and origin.returncode==0 and head.stdout.strip()==package['rev'] and origin.stdout.strip()==package['url']
 plan['dependency_preflight'].append({'name':package['name'],'expected_head':package['rev'],'actual_head':head.stdout.strip(),
  'expected_origin':package['url'],'actual_origin':origin.stdout.strip(),'match':match})
 if not match:
  plan['status']='ENVIRONMENT_BLOCKED_DEPENDENCY_IDENTITY';save();raise SystemExit('Dependency identity mismatch before any proof invocation: '+package['name'])
save()
RESERVE=1_000_000_000
def guarded(command):
 start=time.monotonic();minimum=shutil.disk_usage(base).free
 if minimum<RESERVE:return {'exit':None,'stdout':'','stderr':'Not invoked below reserve','disk_reserve_stopped':True,'minimum_free_bytes':minimum,'seconds':0}
 p=subprocess.Popen(command,cwd=dest,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding='utf8')
 stopped=False;timedout=False;stoplog=None
 while True:
  free=shutil.disk_usage(base).free;minimum=min(minimum,free)
  if p.poll() is None and (free<RESERVE or time.monotonic()-start>14400):
   stopped=free<RESERVE;timedout=not stopped
   kill=subprocess.run(['taskkill','/PID',str(p.pid),'/T','/F'],capture_output=True,text=True,encoding='utf8')
   stoplog={'own_lean_pid':p.pid,'command':['taskkill','/PID',str(p.pid),'/T','/F'],'exit':kill.returncode,'stdout':kill.stdout,'stderr':kill.stderr}
   try:stdout,stderr=p.communicate(timeout=30)
   except subprocess.TimeoutExpired:
    p.kill();stdout,stderr=p.communicate(timeout=30)
   break
  try:stdout,stderr=p.communicate(timeout=.5);break
  except subprocess.TimeoutExpired:pass
 return {'exit':p.returncode,'stdout':stdout,'stderr':stderr,'seconds':round(time.monotonic()-start,2),
  'disk_reserve_stopped':stopped,'timeout':timedout,'minimum_free_bytes':minimum,'owned_process_tree_stop':stoplog}
source_failures=[];axiom_failures=[]
for n in ordered:
 if states.get(n)=='PASS':
  plan['resume_reused_modules'].append(n);continue
 m=modules[n];assert hashlib.sha256(Path(m['file']).read_bytes()).hexdigest()==m['sha256']
 blocked=[d for d in custom_deps[n] if states.get(d)!='PASS']
 if blocked:
  states[n]='BLOCKED_BY_FAILED_IMPORT';plan['builds'].append({'module':n,'state':states[n],'dependency_failures':blocked,'attempted':False})
  plan['module_states']=states;save();print(n,states[n],flush=True);continue
 target=out.joinpath(*n.split('.'));target.parent.mkdir(parents=True,exist_ok=True)
 workers='-j1' if n=='Executables.WeightedCandidate' else '-j'+str(args.jobs)
 command=[str(lean),workers,'-o',str(target)+'.olean','-i',str(target)+'.ilean',str(Path(m['file']).relative_to(dest))]
 plan['current_module']=n;save();print('INVOKE',n,workers,flush=True)
 row=guarded(command);row.update({'module':n,'command':command,'attempted':True,'is_endpoint_audit':n.startswith('Audits.'),'source_sha256':m['sha256']})
 plan['builds'].append(row)
 if row.get('disk_reserve_stopped'):
  states[n]='ENVIRONMENT_BLOCKED_DISK_RESERVE';plan['status']='ENVIRONMENT_BLOCKED_DISK_RESERVE';plan['module_states']=states;save();break
 if row['exit']!=0 or row.get('timeout'):
  states[n]='BUILD_FAILED_OR_TIMED_OUT';source_failures.append(n)
 elif row['is_endpoint_audit'] and re.search(r'\bsorryAx\b',row['stdout']):
  states[n]='COMPILES_BUT_ENDPOINT_USES_SORRY';axiom_failures.append(n)
 else:states[n]='PASS'
 plan['module_states']=states;save();print(n,row['exit'],row['seconds'],flush=True)
else:
 plan['status']='BUILD_FAILED_WITH_INDEPENDENT_MODULES_ATTEMPTED' if source_failures else 'COMPILES_BUT_ENDPOINT_USES_SORRY' if axiom_failures else 'PASS_WITH_NATIVE_EVALUATION'
plan.update({'module_states':states,'source_failures':source_failures,'axiom_failures':axiom_failures,
 'fresh_custom_artifact_inventory':artifacts(),'disk_reserve_bytes':RESERVE,
 'native_tactic_execution_requirement':'Every frozen source containing native_decide must actually compile from the cold or own-receipt-resumed custom outputs; a native evaluation failure is recorded as a failed invocation, never replaced by a claimed arithmetic fact.',
 'watchdog_scope':'Stops only the own Lean process tree below reserve; preserves all partial output files for explicitly verified resource resume.'})
after=dependency_objects();before=plan['external_dependency_objects_before']
plan['external_dependency_objects_after']=after
plan['external_dependency_native_object_changes']={'created':sorted(set(after)-set(before)),
 'removed':sorted(set(before)-set(after)), 'modified':sorted(k for k in set(after)&set(before) if after[k]!=before[k])}
plan['finished_utc']=stamp();plan.pop('current_module',None);save()
print('PROJECT_STATUS',plan['status'],flush=True)
