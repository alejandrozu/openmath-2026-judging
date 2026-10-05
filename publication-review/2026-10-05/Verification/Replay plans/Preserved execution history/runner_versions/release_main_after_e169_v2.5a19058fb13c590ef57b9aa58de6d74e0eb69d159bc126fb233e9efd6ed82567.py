"""Release only the SHA-bound own outer hold after the actual E169 v2 exit."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,shutil
from resource_metrics import snapshot
BASE=Path(__file__).resolve().parent
record=BASE/'main-queue-hold-for-e169-v2-20261005T024847Z.json'
old=json.loads(record.read_bytes())
flag=Path(old['flag']).resolve()
assert flag.parent==BASE.resolve() and flag.name=='hold-main-granular-queue'
raw=flag.read_bytes()
assert hashlib.sha256(raw).hexdigest()==old['flag_sha256']=='b81d74d5754df609302bc442af822a2f6cc015655a6801fee19c1f03658f7293'
peer=BASE/'sakana-erdos169-fourap-tactic-specific-v2-fresh-build.json'
assert hashlib.sha256(peer.read_bytes()).hexdigest()=='b0a0157e0b277a9e20c11f22f342663ae3b11b91ec6aba1fa8f7bbe036c284c6'
assert json.loads(peer.read_bytes())['status'].startswith('PASS')
a060=BASE/'sakana-a060957-fresh-build.json'
assert hashlib.sha256(a060.read_bytes()).hexdigest()=='a153d6e0cbe193bd155a8710c65197b9c03c2243bec385179fe33728685314db'
assert sum(r['exit']==0 and not r['is_endpoint_audit'] for r in json.loads(a060.read_bytes())['builds'])==30
assert not (BASE/'hold-third-worker-dispatch').exists()
release={'status':'ROOT_AUTHORIZED_MAIN_GRANULAR_ONLY_OUTER_HOLD_RELEASED',
    'released_utc':datetime.now(timezone.utc).isoformat(),
    'original_hold_receipt':str(record),'original_hold_receipt_sha256':hashlib.sha256(record.read_bytes()).hexdigest(),
    'released_flag':str(flag),'released_flag_sha256':old['flag_sha256'],
    'actual_completed_e169_v2_receipt_sha256':hashlib.sha256(peer.read_bytes()).hexdigest(),
    'a060_checkpoint_before_resume_sha256':hashlib.sha256(a060.read_bytes()).hexdigest(),
    'current_resource_metrics':dict(disk=shutil.disk_usage(BASE).free,**snapshot()),
    'authorization_scope':'Root explicitly releases main A06030/45 then A100/MATRIX granular queue only. No whole source mode, original DMS, second worker or judging promotion.',
    'qualification':'Root and peer confirmed actual E169 v2 session exit and no child; prior hold and all scientific receipts remain byte-identical.'}
out=record.with_name(record.stem+'.released.json')
assert not out.exists()
flag.unlink()
out.write_text(json.dumps(release,indent=2)+'\n',encoding='utf8')
print(json.dumps({'released_receipt':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}),flush=True)
