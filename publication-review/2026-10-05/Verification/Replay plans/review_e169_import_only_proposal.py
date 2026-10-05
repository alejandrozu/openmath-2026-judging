"""Root's read-only identity review; this never invokes Lean or grants a lease."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

BASE=Path(__file__).resolve().parent
proposal_path=BASE/'e169-import-pruned-diagnostic-proposal-2026-10-05.json'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
proposal=json.loads(proposal_path.read_text(encoding='utf8'))
assert sha(proposal_path)=='4723490c13d587c24df7b842bbc6fb60f8a10c4640f3185cb6ffa290652029ae'
for key in ['original_source_plan','original_partial_receipt','diagnostic_plan']:
    assert sha(proposal[key])==proposal[key+'_sha256'],key
old=json.loads(Path(proposal['original_source_plan']).read_text(encoding='utf8'))
new=json.loads(Path(proposal['diagnostic_plan']).read_text(encoding='utf8'))
assert len(old['modules'])==len(new['modules'])==22
assert old['version']==new['version']=='4.34.1'
assert old['mathlib_pin']==new['mathlib_pin']==proposal['mathlib_pin']
assert old['endpoints']==new['endpoints']
original={r['module']:r for r in old['modules']}
modified={r['module']:r for r in proposal['source_changes']}
assert len(modified)==7
identities=[]
for item in new['modules']:
    name=item['module'];prior=original[name]
    a=Path(prior['file']).read_bytes();b=Path(item['file']).read_bytes()
    assert hashlib.sha256(a).hexdigest()==prior['sha256']==item['original_sha256']
    assert hashlib.sha256(b).hexdigest()==item['sha256']
    if name in modified:
        row=modified[name]
        aa=row['original_replaced_span'];bb=row['replacement_span']
        assert aa['start_byte']==bb['start_byte']==0
        assert a[:aa['end_byte_exclusive']]==b'import Mathlib\n'
        assert a[aa['end_byte_exclusive']:]==b[bb['end_byte_exclusive']:]
        assert hashlib.sha256(a[aa['end_byte_exclusive']:]).hexdigest()==row['original_body_sha256']==row['diagnostic_body_sha256']
        header=''.join('import '+s+'\n' for s in row['diagnostic_imports']).encode()
        assert b[:bb['end_byte_exclusive']]==header
        assert 'Mathlib' not in row['diagnostic_imports']
        assert sha(row['diff'])==row['diff_sha256']
    else:assert a==b
    identities.append({'module':name,'body_unchanged':True,'original_sha256':prior['sha256'],'diagnostic_sha256':item['sha256']})
audit=proposal['unchanged_selected_audit']
for root in [Path(old['source_dir']),Path(new['source_dir'])]:
    assert sha(root/audit['file'])==audit['sha256']
for row in proposal['official_direct_imports']:
    assert sha(row['source'])==row['source_sha256']
    assert sha(row['official_cached_olean'])==row['official_cached_olean_sha256']
for row in proposal['dependency_identity']:assert sha(row['file'])==row['sha256']
closure=proposal['official_closure']
assert sha(closure['closure_source_manifest'])==closure['closure_source_manifest_sha256']
manifest=json.loads(Path(closure['closure_source_manifest']).read_text(encoding='utf8'))
assert len(manifest)==closure['diagnostic_reachable_mathlib_sources']==2815
mathlib=BASE/'dependencies/4.34.1/mathlib'
assert all(sha(mathlib/(row['module'].replace('.','/')+'.lean'))==row['source_sha256'] for row in manifest)
assert closure['original_reachable_mathlib_sources']==8530
assert closure['removed_reachable_mathlib_sources']==5715
assert not closure['literal_Mathlib_umbrella_reachable']
assert not closure['new_mathlib_sources_outside_original_umbrella']
assert not list(Path(new['source_dir']).rglob('*.olean'))
record={'reviewed_by':'/root','reviewed_utc':datetime.now(timezone.utc).isoformat(),
    'status':'IDENTITY_REVIEW_PASS_NO_DISPATCH_AUTHORIZATION',
    'proposal_sha256':sha(proposal_path),'diagnostic_plan_sha256':sha(proposal['diagnostic_plan']),
    'source_identity_checks':identities,'selected_audit_sha256':audit['sha256'],
    'official_mathlib_source_closure_hashes_checked':len(manifest),
    'resource_policy':'Unchanged guarded6GiB own/5GiB dispatch with existing continuous reserves',
    'actual_compilation':'NOT_RUN; import sufficiency and resource use remain unmeasured',
    'scope':'Separate changed-import environment. The original frozen-source15/22 partial replay and two resource failures remain unchanged. All22 shadow sources and exact selected audit must be built cold for any diagnostic completion claim.'}
target=BASE/'e169-import-only-root-identity-review.json'
assert not target.exists(),'Do not replace a prior dated root review'
target.write_text(json.dumps(record,indent=2),encoding='utf8')
print(json.dumps({'status':record['status'],'sources_checked':22,'official_sources_checked':len(manifest),'root_review_sha256':sha(target)}))
