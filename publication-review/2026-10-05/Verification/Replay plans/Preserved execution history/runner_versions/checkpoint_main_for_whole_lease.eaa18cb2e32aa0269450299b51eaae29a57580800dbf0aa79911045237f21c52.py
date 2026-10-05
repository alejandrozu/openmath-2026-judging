"""Safe coordinator flag at a completed main-granular source boundary, no kill."""
from pathlib import Path
import hashlib,json,shutil,sys,time
from receipt_io import read_bytes_shared
from resource_metrics import snapshot
from native_resource_guard import stamp,save_once
BASE=Path(__file__).resolve().parent;FLAG=BASE/'hold-third-worker-dispatch'
allowed={'htpeo-kobon471','sakana-ferrers','sakana-a060957','sakana-a100475',
 'sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2','sakana-a000224'}
if sys.argv[1]=='--request':
 project=sys.argv[2];assert project in allowed and not FLAG.exists()
 raw=read_bytes_shared(BASE/(project+'-fresh-build.json'));current=json.loads(raw)
 assert current['status'] in {'RUNNING','WAITING_THIRD_WORKER_DISPATCH_GATES'}
 token=json.dumps({'reason':'ROOT_AUTHORIZED_MAIN_BOUNDARY_FOR_SOLE_WHOLE_IMPORTER',
   'project':project,'requested_utc':stamp()}).encode('utf8')
 with FLAG.open('xb') as f:f.write(token)
 evidence={'status':'MAIN_COMPANION_BOUNDARY_REQUESTED_NO_SOURCE_STOP','project':project,
   'flag':str(FLAG),'flag_sha256':hashlib.sha256(token).hexdigest(),
   'main_receipt_before_sha256':hashlib.sha256(raw).hexdigest(),
   'completed_rows_before':len(current['builds']),'current_module_before':current.get('current_module'),
   'qualification':'Existing source compiler finishes normally; source runner checks the flag before any next source dispatch.'}
 out=BASE/('main-whole-lease-boundary-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'.json')
 save_once(out,evidence);print(json.dumps({'receipt':str(out)}),flush=True)
elif sys.argv[1]=='--finish':
 file=Path(sys.argv[2]).resolve();assert file.is_relative_to(BASE.resolve())
 evidence=json.loads(file.read_bytes());project=evidence['project'];assert project in allowed
 assert hashlib.sha256(FLAG.read_bytes()).hexdigest()==evidence['flag_sha256']
 raw=read_bytes_shared(BASE/(project+'-fresh-build.json'));current=json.loads(raw)
 assert current['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
 assert current['checkpoint_reason'] in {'THIRD_WORKER_LEASE_HANDOFF_AT_COMPLETED_MODULE_BOUNDARY',
   'THIRD_WORKER_LEASE_HANDOFF_WHILE_WAITING_WITHOUT_COMPILER','THIRD_WORKER_LEASE_HANDOFF_WITHOUT_COMPILER',
   'ROOT_AUTHORIZED_SINGLE_THIRD_WORKER_PILOT_COMPLETED'}
 result={'status':'MAIN_COMPANION_ACTUAL_CHECKPOINT_OWN_FLAG_RELEASED','project':project,
  'boundary_request':str(file),'completed_source_passes':sum(r['exit']==0 and not r['is_endpoint_audit'] for r in current['builds']),
  'source_receipt_sha256':hashlib.sha256(raw).hexdigest(),'last_completed_module':current['builds'][-1]['module'],
  'flag_sha256':evidence['flag_sha256'],'finished_utc':stamp(),
  'metrics':{'disk':shutil.disk_usage(BASE).free,**snapshot()},
  'qualification':'Coordinator separately confirmed exact source runner/tool session exit before this flag release; no source was terminated.'}
 assert FLAG.resolve().parent==BASE.resolve();FLAG.unlink()
 out=file.with_name(file.stem+'.completed.json');save_once(out,result);print(json.dumps(result),flush=True)
else:raise SystemExit('Use --request project or --finish receipt after actual runner exit')
