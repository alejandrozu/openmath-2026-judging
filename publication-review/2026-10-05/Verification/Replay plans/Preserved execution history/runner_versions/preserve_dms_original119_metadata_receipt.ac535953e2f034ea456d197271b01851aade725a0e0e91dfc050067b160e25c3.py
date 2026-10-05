"""Preserve receipt bytes only; never copy Lean source or compiled artifacts."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
BASE=Path(__file__).resolve().parent
def digest(raw):return hashlib.sha256(raw).hexdigest()
src=BASE/'htpeo-dms-current-fresh-build.json'
raw=src.read_bytes()
expected='feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238'
assert digest(raw)==expected
dest=BASE/'proposals/htpeo-dms-current-import-pruned-diagnostic'/('original119-fresh-receipt.'+expected+'.json')
if dest.exists():assert dest.read_bytes()==raw
else:
    with dest.open('xb') as stream:stream.write(raw)
complete=BASE/'dms-full228-complete-official-closure-and-reuse-proposal-20261005.json'
assert digest(complete.read_bytes())=='620fe0d86aff72859d8b9d97d8f793988710a145f200ae3cb4f05ea322f2bd2a'
reuse=dest.parent/'original119-owned-unaffected-reuse-eligibility.json'
record={'status':'IMMUTABLE_ORIGINAL119_RECEIPT_METADATA_SNAPSHOT_ONLY_NO_COMPILED_OUTPUT_COPY',
    'prepared_utc':datetime.now(timezone.utc).isoformat(),
    'canonical_receipt_at_snapshot':str(src),'immutable_original119_receipt':str(dest),
    'original119_receipt_sha256':expected,'all_receipt_bytes_identical':dest.read_bytes()==raw,
    'complete_closure_and_reuse_proposal':str(complete),'complete_closure_and_reuse_proposal_sha256':digest(complete.read_bytes()),
    'reuse_eligibility_inventory':str(reuse),'reuse_eligibility_inventory_sha256':digest(reuse.read_bytes()),
    'actual_source_PASS_count':sum(row.get('exit')==0 and not row.get('is_endpoint_audit') for row in json.loads(raw)['builds']),
    'qualification':'This additive binding remains immutable if the canonical original route later resumes. No proof source/artifact is copied or marked reusable.'}
out=BASE/'dms-original119-immutable-receipt-binding-20261005.json'
assert not out.exists()
out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
assert src.read_bytes()==raw
print(json.dumps({'metadata_receipt':str(out),'metadata_receipt_sha256':digest(out.read_bytes()),
    'immutable_receipt':str(dest),'original119_receipt_sha256':expected}))
