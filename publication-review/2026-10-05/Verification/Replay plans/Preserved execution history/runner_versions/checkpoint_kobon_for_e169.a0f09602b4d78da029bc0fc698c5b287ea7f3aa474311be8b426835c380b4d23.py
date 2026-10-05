"""Root-authorized no-kill companion boundary and exact owned flag release."""
from pathlib import Path
import hashlib,json,os,shutil,sys,time
from receipt_io import read_bytes_shared
from resource_metrics import snapshot
from native_resource_guard import processes,stamp,save_once
BASE=Path(__file__).resolve().parent;flag=BASE/'hold-third-worker-dispatch'
evidence=BASE/'kobon-e169-serialized-boundary.json'
if sys.argv[1]=='--request':
    assert not flag.exists() and not evidence.exists()
    raw=json.dumps({'reason':'ROOT_AUTHORIZED_E169_WHOLE_IMPORT_SERIALIZATION',
      'requested_utc':stamp(),'holder_project':'htpeo-kobon471'}).encode('utf8')
    with flag.open('xb') as f:f.write(raw)
    save_once(evidence,{'status':'OWNED_COMPANION_BOUNDARY_REQUESTED_NO_CHILD_STOP',
      'flag':str(flag),'flag_sha256':hashlib.sha256(raw).hexdigest(),
      'qualification':'Existing source child finishes normally; source runner checkpoints before its next dispatch.'})
    print('KOBON_BOUNDARY_REQUESTED',flush=True)
elif sys.argv[1]=='--finish':
    doc=json.loads(evidence.read_bytes());assert hashlib.sha256(flag.read_bytes()).hexdigest()==doc['flag_sha256']
    raw=read_bytes_shared(BASE/'htpeo-kobon471-fresh-build.json');result=json.loads(raw)
    assert result['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
    assert result['checkpoint_reason']=='THIRD_WORKER_LEASE_HANDOFF_AT_COMPLETED_MODULE_BOUNDARY'
    # The invoking coordinator separately waits for the exact PTY/runner to exit.
    rows=[r for r in result['builds'] if not r['is_endpoint_audit']]
    assert all(r['exit']==0 for r in rows)
    released={'status':'COMPANION_CHECKPOINTED_TASK_OWNED_FLAG_RELEASED',
      'requested_boundary':str(evidence),'source_receipt_sha256':hashlib.sha256(raw).hexdigest(),
      'completed_sources':len(rows),'last_completed_module':rows[-1]['module'],
      'source_errors':[], 'flag_sha256':doc['flag_sha256'],'finished_utc':stamp(),
      'metrics':{'disk':shutil.disk_usage(BASE).free,**snapshot()}}
    assert flag.resolve().parent==BASE.resolve();flag.unlink()
    save_once(evidence.with_name(evidence.stem+'.completed.json'),released)
    print(json.dumps(released),flush=True)
else:raise SystemExit('Use --request or --finish after actual runner exit')
