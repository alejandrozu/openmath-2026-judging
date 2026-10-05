"""Metadata-only rebind of unexecuted parallel controller; no proof or storage operation."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json
BASE=Path(__file__).resolve().parent
CONTROLLER=BASE/'run_ht_ramsey_two_kernel_controller_prepared.py'
OLD=BASE/'ht-ramsey-two-kernel-controller-design-preparation-20261005.json'
MANIFEST=BASE/'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
FULL=BASE/'ht-ramsey-two-kernel-controller-v2-full-prepared-implementation.diff'
MINIMAL=BASE/'ht-ramsey-two-kernel-controller-v2-receipt-provenance-minimal.diff'
NEW=BASE/'ht-ramsey-two-kernel-controller-v2-design-preparation-20261005.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,d):
    with Path(p).open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')
old=json.loads(OLD.read_bytes())
assert sha(OLD)=='16ec439abf5da39e15533819c3f4f4d158090a720ad39a6a1457350bc293314c'
assert sha(MANIFEST)==old['source_manifest_sha256']=='2c5963c0b5c5094b77206b80d9e02866a504d56991459a2f0ec3bacef147da15'
old_code=list((BASE/'proposals/ht-two-kernel-initial-unexecuted-draft').glob('run_ht_ramsey_two_kernel_controller_prep*-cd2074037eebbfcbdd47278b5507c58fd098bcda62dd91d94ad24029df54ba2b.preserved'))
assert len(old_code)==1 and sha(old_code[0])==old['controller_sha256']
ast.parse(CONTROLLER.read_text(encoding='utf8'))
with FULL.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff([],CONTROLLER.read_text(encoding='utf8').splitlines(True),fromfile='/dev/null',tofile=CONTROLLER.name))
with MINIMAL.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff(old_code[0].read_text(encoding='utf8').splitlines(True),CONTROLLER.read_text(encoding='utf8').splitlines(True),fromfile='preserved-unexecuted-initial-controller',tofile=CONTROLLER.name))
new=dict(old);new.update(created_utc=datetime.now(timezone.utc).isoformat(),producer_sha256=sha(__file__),
    controller_sha256=sha(CONTROLLER),full_prepared_implementation=str(FULL),full_prepared_implementation_sha256=sha(FULL),
    minimal_unexecuted_operational_correction=str(MINIMAL),minimal_unexecuted_operational_correction_sha256=sha(MINIMAL),
    preserved_original_preparation=str(OLD),preserved_original_preparation_sha256=sha(OLD),
    dated_snapshot_is_historical_and_not_current_dispatch_evidence=True,
    operational_preparation_changes=['Bind exact counter helpers and current official cache receipt','Check actual nine origin URLs as well as HEADs','Preserve old resource settings and label new controller/rows explicitly','Persist guard no-attempt evidence and apply bounded backpressure'],
    actual_compiler_alias_source_storage_operations=0)
new['future_root_pilot_approval_fields']=dict(old['future_root_pilot_approval_fields'])
new['future_root_pilot_approval_fields'].update(reviewed_controller_sha256=sha(CONTROLLER),
    reviewed_official_cache_receipt_sha256=sha(BASE/'mathlib-4.33.1-cache-retry.json'))
save(NEW,new)
print(json.dumps({'design':str(NEW),'design_sha256':sha(NEW),'controller_sha256':sha(CONTROLLER),
    'full_implementation_sha256':sha(FULL),'minimal_diff_sha256':sha(MINIMAL),'source_manifest_sha256':sha(MANIFEST),
    'actual_proof_compilers_or_aliases':0},indent=2))
