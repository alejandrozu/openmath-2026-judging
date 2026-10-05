"""Prepare a separate organizer-only import supplement; never invoke Lean here."""
from pathlib import Path
import json,hashlib,re,difflib
from lean_imports import stripped
from audit_axioms import parse
BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-dms-current-import-pruned-v4-vector'
SCIENCE=BASE/'htpeo-dms-current-import-pruned-v4-vector-fresh-build.json'
SCIENCE_SHA='fb428dd280da30ba25480be5420157dfa7bbeb268c603b05edb0a17dd9eeb7ba'
SEED=BASE/'dms-v4-vector122-link99-readonly-seed-completed-20261005.json'
SEED_SHA='2187c885a9145a847db040c2fe8b3ad03db6e6093a6f400117d1a60c84a3dbf3'
MISSING=['Star6.colourable_of_dms_cubic','Star6.dms_iff_cubic16','Star6.leaf_of_dms']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(SCIENCE)==SCIENCE_SHA and sha(SEED)==SEED_SHA
receipt=json.loads(SCIENCE.read_bytes())
sources=[r for r in receipt['builds'] if not r['is_endpoint_audit']]
assert len(sources)==7 and all(r['exit']==0 and not r.get('stop_reason') for r in sources)
audit=[r for r in receipt['builds'] if r['is_endpoint_audit']];assert len(audit)==1 and audit[0]['exit']==1
original=STAGE/'FreshAudit1.lean';raw=original.read_bytes()
requested=re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(raw.decode('utf8')),re.M)
old=parse(audit[0]['stdout']);assert len(old)==120 and len(requested)==len(set(requested))==123
assert sorted(set(requested)-{r['endpoint'] for r in old})==MISSING
assert sorted(re.findall(r'Unknown constant `([^`]+)`',audit[0]['stdout']))==MISSING
proposal_dir=BASE/'proposals/dms-v4-equivalence-organizer-audit';proposal_dir.mkdir(exist_ok=True)
draft=proposal_dir/'FreshAuditSupplement.lean'
if draft.exists():assert draft.read_bytes()==b'import Star6Equiv\n'+raw
else:draft.write_bytes(b'import Star6Equiv\n'+raw)
assert re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(draft.read_text(encoding='utf8')),re.M)==requested
provider=STAGE/'Star6Equiv.lean';assert provider.is_file()
diff=BASE/'dms-v4-equivalence-audit-exact-import-only.diff'
diff_text=''.join(difflib.unified_diff(raw.decode().replace('\r\n','\n').splitlines(keepends=True),draft.read_bytes().decode().replace('\r\n','\n').splitlines(keepends=True),fromfile='Frozen-FreshAudit1.lean',tofile='Separate-FreshAuditSupplement.lean'))
if diff.exists():assert diff.read_bytes()==diff_text.encode('utf8')
else:diff.write_bytes(diff_text.encode('utf8'))
packet=BASE/'dms-v4-equivalence-supplemental-audit-preparation-20261005.json';assert not packet.exists()
data={'status':'PREPARED_ONLY_SEPARATE_ORGANIZER_AUDIT_NO_LEAN_NO_SOURCE_REBUILD',
    'source_receipt':str(SCIENCE),'source_receipt_sha256':SCIENCE_SHA,'source_actual_PASS':7,'original_audit_exit':1,
    'original_actual_print_count':120,'original_missing_exact3':MISSING,'original_raw_audit_row':audit[0],
    'source_plan':str(STAGE/'build-plan.json'),'source_plan_sha256':sha(STAGE/'build-plan.json'),
    'seed_receipt_sha256':SEED_SHA,'original_audit':str(original),'original_audit_sha256':sha(original),
    'supplement_draft':str(draft),'supplement_sha256':sha(draft),'minimal_import_diff':str(diff),'minimal_import_diff_sha256':sha(diff),
    'only_change':'Add importStar6Equiv before the exact original audit bytes;123 requests unchanged; no scientific source changes.',
    'Star6Equiv_source':str(provider),'Star6Equiv_source_sha256':sha(provider),
    'Star6Equiv_previous_own_V3_new122_cold_pass_linked_into_V4_olean':str(STAGE/'Star6Equiv.olean'),
    'Star6Equiv_linked_olean_sha256':sha(STAGE/'Star6Equiv.olean'),
    'requested123_exact':requested,'no_original_plan_or_audit_modification':True,'output_aliases':0,'compiler_invocations':0,
    'future_composite_qualification':'Require actual7 V4+221 previous own passes and a separate successful123-print supplement; retain/disclose frozen original audit120/123 exit1.',
    'resource_policy':'One audit only, unchanged6/5/-j1 ownjob guard and continuous floors;maximum2 actualcompilers.'}
packet.write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
print(json.dumps({'packet':str(packet),'packet_sha256':sha(packet),'draft_sha256':sha(draft),'original_audit_sha256':sha(original),'diff_sha256':sha(diff)},indent=2))
