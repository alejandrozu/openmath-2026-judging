"""Read-only V4 body/header/pin/closure and conditional221-owned-pass verifier."""
from pathlib import Path
import hashlib,json,re
from lean_imports import read_imports,stripped
from receipt_io import read_bytes_shared
from verify_dms_v3_stage import verify_stage as verify_v3_stage
from dms_v3_copy99_hardlink_seed import file_identity,protected_routes_check,inode_key

BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-dms-current-import-pruned-v4-vector'
V3=BASE/'builds/htpeo-dms-current-import-pruned-v3'
V1=BASE/'builds/htpeo-dms-current-import-pruned-diagnostic'
PLAN_SHA='30f7b071fbcd9ddb37e48a059126daf8e37dd65dae9b2733614af926589a7308'
PROPOSAL_SHA='bab8fca1cf9a016db0dab7e237fe555bb5373da3c53da6d65512cab2274e0280'
V3_RECEIPT_SHA='ff1dd1a5c1666631992bffb93f51271c6c4e162cb075f2ec80eddf15e741ccd4'
V3_POLICY_SHA='a4b795b071135118af94868726b9ac45af0579540d5856e9aaf7d48a9e3717e6'
V3_SEED_SHA='a1395c3617d8c813048b0ecfb34be453c058636216659583090ad1defb771c83'

def digest(path):
    d=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):d.update(block)
    return d.hexdigest()
def load(path):return json.loads(Path(path).read_bytes())
def closure(name,deps):
    seen=set();pending=[name]
    while pending:
        item=pending.pop()
        if item not in seen:seen.add(item);pending.extend(deps[item]-seen)
    return seen

def protected99_identity():
    pp=BASE/'dms-v3-v1copy99-hardlink-policy-20261005.json'
    sp=BASE/'dms-v3-v1copy99-hardlink-seed-completed-20261005.json'
    assert digest(pp)==V3_POLICY_SHA and digest(sp)==V3_SEED_SHA
    policy=load(pp);seed=load(sp)
    assert seed['protected_routes_after']==policy['protected_original_v1_v2_routes']==protected_routes_check()
    for expected,actual in zip(policy['output_links'],seed['output_links']):
        source=file_identity(expected['v1_proven_copied_output_seed_source']);target=file_identity(expected['diagnostic_target'])
        assert source==target==actual['v1_copy_NTFS_identity_after_link']==actual['target_NTFS_identity_after_link']
        assert source['link_count']==2 and inode_key(source)==inode_key(target)
        assert digest(expected['original_owned_output'])==digest(expected['v1_proven_copied_output_seed_source'])==digest(expected['diagnostic_target'])==expected['sha256']
    return {'protected_original_V2_and_V1_V3_99_alias_counts_unchanged':True,'seed99_sha256':V3_SEED_SHA}

def verify_stage(require_cold=True,linked122_allowed=False):
    assert digest(STAGE/'build-plan.json')==PLAN_SHA
    proposal_path=BASE/'dms-v4-vector-cold-stage-complete221-reuse-proposal-20261005.json'
    assert digest(proposal_path)==PROPOSAL_SHA
    proposal=load(proposal_path);plan=load(STAGE/'build-plan.json')
    assert plan['version']=='4.33.1' and plan['mathlib_pin']=='0df444a360eaa60ab8c11dca51a86af692955474' and plan.get('lean_options',{})=={}
    legacy=verify_v3_stage(require_cold=False)
    assert len(plan['modules'])==228
    names={m['module'] for m in plan['modules']};entries={m['module']:m for m in plan['modules']}
    source_identities=[]
    for m in plan['modules']:
        file=Path(m['file']);assert file.is_relative_to(STAGE.resolve()) and digest(file)==m['sha256']
        previous=Path(m['V3_file']);assert digest(previous)==m['V3_sha256']
        raw=previous.read_bytes();actual=file.read_bytes()
        if m['module']=='InflationA':
            first=raw.splitlines(keepends=True)[0];offset=len(first)
            assert first.rstrip(b'\r\n')==b'import InflationDefs'
            assert actual==raw[:offset]+b'import Mathlib.Data.Fin.VecNotation\n'+raw[offset:]
        else:assert actual==raw
        source_identities.append({'module':m['module'],'source_sha256':m['sha256'],'body_identical_to_V3_and_frozen_original':True})
    imports={name:set(read_imports(m['file']))-{'all'} for name,m in entries.items()}
    deps={name:roots&names for name,roots in imports.items()}
    affected={name for name in names if 'InflationA' in closure(name,deps)}
    assert affected==set(proposal['affected7_new_required_sources']) and len(affected)==7
    graph_path=STAGE/'official-full-source-artifact-closure.json'
    assert digest(graph_path)==proposal['official_full2735_source_artifact_manifest_sha256']=='936867aecf295ca4892a97b173db0227c403c7177c6bd68859d7b6e8a45b8fcd'
    graph={r['module']:r for r in load(graph_path)}
    assert len(graph)==2735 and 'Mathlib.Data.Fin.VecNotation' in graph and not {'Mathlib','Mathlib.Tactic'}&set(graph)
    assert digest(graph['Mathlib.Data.Fin.VecNotation']['source'])=='08b3449fd3135bb1b4123e74445bad9317b2aa7515a0464aaddc0d656971568e'
    assert read_bytes_shared(BASE/'htpeo-dms-current-import-pruned-v3-fresh-build.json')==Path(BASE/'htpeo-dms-current-import-pruned-v3-fresh-build.json').read_bytes()
    assert digest(BASE/'htpeo-dms-current-import-pruned-v3-fresh-build.json')==V3_RECEIPT_SHA
    v3receipt=load(BASE/'htpeo-dms-current-import-pruned-v3-fresh-build.json')
    rows={r['module']:r for r in v3receipt['builds'] if r['exit']==0 and not r['is_endpoint_audit']}
    assert len(rows)==122 and not set(rows)&affected
    lean=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe';reuse=[]
    for candidate in proposal['actual122_V3_new_unaffected_source_PASS_reuse_candidates']:
        name=candidate['module'];row=rows[name];assert row==candidate['actual_V3_source_PASS_row']
        full=closure(name,deps);assert not full&affected and set(candidate['full_unchanged_custom_closure'])==full
        assert all(digest(entries[n]['file'])==digest(entries[n]['V3_file']) for n in full)
        source=Path(entries[name]['V3_file']);relative=source.relative_to(V3)
        cmd=[str(lean),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(relative.with_suffix('.olean')),str(relative)]
        guard=row['own_job_resource_receipt']
        assert row['command']==guard['command']==cmd and row['source_sha256']==entries[name]['sha256']
        assert row['exit']==guard['exit']==0 and row.get('stop_reason') is None and guard['state']=='PASS'
        assert guard['own_job_assignment_before_resume']=='PASS' and Path(guard['cwd']).resolve()==V3.resolve()
        for channel in ['stdout','stderr']:
            file=Path(guard[channel+'_file']);raw=file.read_bytes()
            assert hashlib.sha256(raw).hexdigest()==guard[channel+'_sha256'] and raw==row[channel].encode('utf8')
        for a in candidate['artifacts']:
            assert digest(a['file'])==a['sha256'];info=file_identity(a['file'])
            original=a['current_source_identity']
            if linked122_allowed:
                assert all(info[k]==original[k] for k in original if k!='link_count') and info['link_count']==2
            else:assert info==original and info['link_count']==1
        reuse.append(name)
    assert len(reuse)==122
    readonly99=proposal['existing99_original_owned_V1_COPY_readonly_inputs'];assert len(readonly99)==99
    input_names={r['module'] for r in readonly99}
    actual_v1_names={str(p.relative_to(V1).with_suffix('')).replace('\\','.') for p in V1.rglob('*.olean')}
    assert actual_v1_names==input_names and not input_names&set(reuse)
    for record in readonly99:
        assert digest(record['readonly_V1_copy_olean'])==record['sha256'] and file_identity(record['readonly_V1_copy_olean'])==record['file_identity']
        for n in closure(record['module'],deps):
            v1source=V1/Path(n.replace('.','/')+'.lean')
            assert digest(v1source)==entries[n]['sha256']
    protected=protected99_identity()
    requests=[]
    for audit in proposal['unchanged123_audit']:
        f=Path(audit['file']);assert digest(f)==audit['sha256']==digest(V3/audit['audit'])
        actual=re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(f.read_text(encoding='utf8')),re.M)
        assert actual==audit['requested123_axioms'];requests+=actual
    assert len(requests)==len(set(requests))==123
    if require_cold:assert not list(STAGE.rglob('*.olean'))
    return {'status':'READ_ONLY_V4_BODY_HEADER_FULL_PIN_CLOSURE_AND221_CONDITIONAL_OWN_OUTPUT_ELIGIBILITY_PASS',
        'source_plan_sha256':PLAN_SHA,'proposal_sha256':PROPOSAL_SHA,'source_count':228,'body_identity_records':source_identities,
        'prior_V3_complete_body_official_runtime_git_identity':legacy,'protected_original_V2_and_V1_V3_99':protected,
        '122_unaffected_V3_new_PASS_candidates':reuse,'99_original_owned_readonly_V1_copy_names':sorted(input_names),
        'required7_new_source_names':sorted(affected),'requested123_unchanged_axioms':requests,
        'linked122_allowed':linked122_allowed,'compiler_or_output_transfer_actions':0}

if __name__=='__main__':
    assert __import__('sys').argv[1:]==['--verify-cold']
    result=verify_stage();out=BASE/'dms-v4-vector-cold-stage-verifier-result-20261005.json';assert not out.exists()
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'result':str(out),'sha256':digest(out),'status':result['status']},indent=2))
