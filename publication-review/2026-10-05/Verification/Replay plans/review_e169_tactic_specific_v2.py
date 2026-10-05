"""Independent cold identity/closure review; never invokes Lean or grants a lease."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
from lean_imports import stripped

BASE=Path(__file__).resolve().parent
def sha(path):
    digest=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for part in iter(lambda:stream.read(1024*1024),b''):digest.update(part)
    return digest.hexdigest()
def load(path):return json.loads(Path(path).read_text(encoding='utf8'))
def imports(path):
    text=stripped(Path(path).read_text(encoding='utf8'))
    result=[]
    for line in text.splitlines():
        match=re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$',line)
        if match:result.extend(x.replace('«','').replace('»','') for x in match.group(1).split() if x!='all')
    return result,not bool(re.search(r'^\s*prelude\s*$',text,re.M))

proposal_path=BASE/'e169-tactic-specific-v2-proposal-2026-10-05.json'
assert sha(proposal_path)=='6734d4fd8ac626a8cbfe1199167a401a085a1359693bcd95e74431139810d48f'
q=load(proposal_path);plan_path=Path(q['diagnostic_plan']);plan=load(plan_path)
assert sha(plan_path)==q['diagnostic_plan_sha256']=='8b183de4ccdcc543b46a8a54fd17a7b41a37ebd13afb8b53c9598e226f2b1e09'
old_path=Path(plan['original_source_plan']);old=load(old_path)
assert sha(old_path)==plan['original_source_plan_sha256']==q['original_source_plan_sha256']
assert old['version']==plan['version']=='4.34.1'
assert old['mathlib_pin']==plan['mathlib_pin']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
assert old['endpoints']==plan['endpoints'] and old['audit_modules']==plan['audit_modules']
assert old['lean_options']==plan['lean_options']
assert len(old['modules'])==len(plan['modules'])==22
prior={row['module']:row for row in old['modules']}
changes={row['module']:row for row in q['source_changes']};assert len(changes)==7
identities=[];external=set()
for row in plan['modules']:
    name=row['module'];a=Path(prior[name]['file']).read_bytes();b=Path(row['file']).read_bytes()
    assert hashlib.sha256(a).hexdigest()==prior[name]['sha256']==row['original_sha256']
    assert hashlib.sha256(b).hexdigest()==row['sha256']
    if name in changes:
        change=changes[name];aa=change['original_replaced_span'];bb=change['replacement_span']
        assert aa['start_byte']==bb['start_byte']==0 and a[:aa['end_byte_exclusive']]==b'import Mathlib\n'
        assert a[aa['end_byte_exclusive']:]==b[bb['end_byte_exclusive']:]
        assert hashlib.sha256(a[aa['end_byte_exclusive']:]).hexdigest()==change['original_body_sha256']==change['diagnostic_body_sha256']
        assert b[:bb['end_byte_exclusive']]==''.join('import '+x+'\n' for x in change['diagnostic_imports']).encode()
        assert 'Mathlib' not in change['diagnostic_imports'] and 'Mathlib.Tactic' not in change['diagnostic_imports']
        assert sha(change['diff'])==change['diff_sha256']
    else:assert a==b
    direct,_=imports(row['file']);external.update(x for x in direct if x not in prior)
    identities.append({'module':name,'scientific_body_options_comments_identical':True,
                       'original_sha256':prior[name]['sha256'],'diagnostic_sha256':row['sha256']})
for name in plan['audit_modules']:
    assert sha(Path(old['source_dir'])/name)==sha(Path(plan['source_dir'])/name)==q['unchanged_audit_source_sha256']
for row in q['unchanged_original_and_v1_receipts']:
    assert sha(row['receipt'])==row['sha256']
for row in q['runtime_and_cache_receipt_identities']:assert sha(row['file'])==row['sha256']
direct={row['module']:row for row in q['official_direct_module_identity']}
assert external==set(direct) and len(direct)==29
for row in direct.values():
    assert sha(row['source'])==row['source_sha256']
    assert sha(row['official_olean'])==row['official_olean_sha256']
closure=q['complete_dependency_source_closure'];closure_path=Path(closure['source_closure_manifest'])
assert sha(closure_path)==closure['source_closure_manifest_sha256']=='d8f9d535a03052006a4a75503483ff9752ad0efab6602cfc37e865a4940c213d'
rows=load(closure_path);by_name={row['module']:row for row in rows}
assert len(rows)==len(by_name)==2492 and sum(row['identity_root']=='mathlib' for row in rows)==738
assert not {'Mathlib','Mathlib.Tactic'}&set(by_name)
official_artifacts=[];edges={}
for row in rows:
    assert sha(row['source'])==row['source_sha256']
    actual,implicit=imports(row['source'])
    assert actual==row['imports'] and implicit==row['implicit_Init_included'],row['module']
    edges[row['module']]=set(actual)|({'Init'} if implicit else set())
    assert edges[row['module']]<=set(by_name),row['module']
    artifact=Path(row['official_olean']);assert artifact.is_file() and artifact.stat().st_size==row['official_olean_bytes']
    official_artifacts.append({'module':row['module'],'source_sha256':row['source_sha256'],
                               'official_cached_olean_sha256':sha(artifact)})
reachable=set();pending=list(external|{'Init'})
while pending:
    name=pending.pop()
    if name not in reachable:reachable.add(name);pending.extend(edges[name]-reachable)
assert reachable==set(by_name),'Closure contains an unreachable or omitted official module'
assert not list(Path(plan['source_dir']).rglob('*.olean')),'Root review requires the cold own-output tree'
record={'reviewed_by':'/root','reviewed_utc':datetime.now(timezone.utc).isoformat(),
        'status':'IDENTITY_AND_FULL_CLOSURE_REVIEW_PASS_NO_DISPATCH_AUTHORIZATION',
        'proposal_sha256':sha(proposal_path),'diagnostic_plan_sha256':sha(plan_path),
        'source_identity_checks':identities,'direct_official_imports':29,
        'official_dependency_source_and_cached_artifact_hashes_checked':2492,
        'mathlib_source_count':738,'core_and_package_source_count':1754,
        'like_for_like_v1_mathlib_source_count':2815,
        'official_artifact_identities':official_artifacts,
        'selected_audit_sha256':q['unchanged_audit_source_sha256'],
        'resource_policy':'Unchanged guarded 6GiB own/5GiB dispatch; explicit scheduling lease required',
        'actual_compilation':'NOT_RUN; import sufficiency and resource consumption unmeasured',
        'scope':'Separate import-only diagnostic; no original-source PASS or final endpoint verification is inferred.'}
target=BASE/'e169-tactic-specific-v2-root-identity-review.json'
assert not target.exists(),'Do not replace a dated root review'
target.write_text(json.dumps(record,indent=2),encoding='utf8')
print(json.dumps({'status':record['status'],'sources':22,'official_closure':2492,'root_review_sha256':sha(target)}))
