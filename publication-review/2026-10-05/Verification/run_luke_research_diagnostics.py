"""Supplementary type-checks only; never execute these counting main functions.

Explicit route selection permits the completed native replay. The original
direct-route runner is preserved under native_source_attempts. Execution requires
the completed formal receipt's exact hash and an explicit coordinated lease.
"""
from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess,time
import argparse
from receipt_io import read_json_shared,read_bytes_shared
from luke_native_source_guard import guarded
base=Path(__file__).resolve().parent
plan=read_json_shared(base/'luke-research-diagnostics-plan.json')
parser=argparse.ArgumentParser()
parser.add_argument('--formal-route',choices=['direct','native'],required=True)
parser.add_argument('--formal-receipt-sha256',required=True)
parser.add_argument('--resource-lease-confirmed',action='store_true')
args=parser.parse_args()
assert args.resource_lease_confirmed,'Coordinate the source-import lease before dispatch'
formal_path=base/('luke-k4-ramsey-current-'+args.formal_route+'-fresh-build.json')
formal_raw=read_bytes_shared(formal_path)
assert hashlib.sha256(formal_raw).hexdigest()==args.formal_receipt_sha256
formal=json.loads(formal_raw)
assert formal['status'] in {'PASS_WITH_NATIVE_EVALUATION','BUILD_FAILED_WITH_INDEPENDENT_MODULES_ATTEMPTED','COMPILES_BUT_ENDPOINT_USES_SORRY'},'The complete independent formal-package attempt must finish before these checks'
assert len(formal['module_states'])==len(formal['modules'])==51,'All 51 formal-package modules must have a recorded final state'
assert not formal.get('current_module'),'A formal-package source invocation is still active'
assert formal['commit']==plan['source_commit']
report=base/'luke-research-diagnostics-typechecks.json'
assert not report.exists(),'Preserve an existing supplementary receipt rather than overwriting it'
out=base/'builds/luke-research-diagnostics'
out.mkdir(parents=True,exist_ok=True)
assert not list(out.iterdir()),'Supplementary outputs must begin cold'
lean=base/'runtimes/lean-4.34.1-windows/bin/lean.exe'
if formal.get('pinned_tool_binary_hashes'):
 assert hashlib.sha256(lean.read_bytes()).hexdigest()==formal['pinned_tool_binary_hashes'][str(lean)]
env=dict(os.environ);env['PATH']=str(lean.parent)+';'+env['PATH'];env['LEAN_NUM_THREADS']='1';env.pop('LEAN_PATH',None)
r=dict(plan);r.update({'id':'luke-k4-ramsey-research-diagnostics','status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'builds':[], 'main_executed':False,'formal_package_receipt_status':formal['status'],'formal_package_source_commit':formal['commit'],'resource_environment':{'LEAN_NUM_THREADS':'1','CLI_workers':'-j1'},'reserve_bytes':1_000_000_000})
r.update({'formal_package_receipt_file':str(formal_path),'formal_package_receipt_sha256':args.formal_receipt_sha256,'formal_package_reproduction_route':args.formal_route,'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'guard_sha256':hashlib.sha256((base/'luke_native_source_guard.py').read_bytes()).hexdigest(),'diagnostic_only_notice':'No main function is run; no output of a counting diagnostic is certified by these type-checks.'})
def save():
 temp=report.with_suffix('.json.tmp')
 with temp.open('w',encoding='utf8') as f:json.dump(r,f,indent=2);f.flush();os.fsync(f.fileno())
 for attempt in range(60):
  try:os.replace(temp,report);break
  except PermissionError:
   if attempt==59:raise
   time.sleep(.1)
save()
version=subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf8',env=env)
assert version.returncode==0 and 'version 4.34.1,' in version.stdout
r['compiler_version_output']=version.stdout.strip();save()
for index,item in enumerate(plan['sources']):
 source=Path(item['path']);assert hashlib.sha256(source.read_bytes()).hexdigest()==item['sha256']
 command=[str(lean),'-j1','-o',str(out/(source.stem+'.olean')),'-i',str(out/(source.stem+'.ilean')),str(source)]
 row=guarded(command,source.parent,env,out/'logs'/f'{index:02d}-{source.stem}',native_images=None,timeout=600,whole_mathlib=False)
 row.update(source=str(source),source_sha256=item['sha256'],sha256=item['sha256'],main_executed=False,supplementary_typecheck_only=True)
 r['builds'].append(row);save();print(source.name,row['state'],row.get('seconds'),flush=True)
 if not row.get('attempted') or row['state'].startswith('ENVIRONMENT_') or row['state'] in {'OPERATIONAL_ERROR','OPERATIONAL_TIMEOUT'}:
  r['status']=row['state'];save();break
else:r['status']='PASS_TYPECHECK_ONLY' if all(v['state']=='PASS' for v in r['builds']) else 'DIAGNOSTIC_TYPECHECK_FAILURE'
r['artifacts']={str(p.relative_to(out)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in out.rglob('*') if p.is_file()}
r['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print(r['status'],len(r['builds']),'standalone diagnostics; no main functions executed',flush=True)
