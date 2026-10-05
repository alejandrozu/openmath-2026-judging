"""Separate v3 source stage/complete graph/verifier; no links or Lean invoked."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,difflib,copy,ast
from lean_imports import read_imports,stripped
BASE=Path(__file__).resolve().parent
PROJECT='htpeo-dms-current-import-pruned-v3'
DEST=BASE/'builds'/PROJECT
ORIGINAL=BASE/'builds/htpeo-dms-current'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def h(b):return hashlib.sha256(b).hexdigest()
def save_new(p,v):
    assert not p.exists();p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8');return sha(p)
v1_receipt=BASE/'htpeo-dms-current-import-pruned-diagnostic-fresh-build.json'
v1_plan=BASE/'builds/htpeo-dms-current-import-pruned-diagnostic/build-plan.json'
v1_seed=BASE/'dms-original99-output-transfer-completed-20261005.json'
preserved=[(v1_receipt,'fb939c9bcf589a1152d346aaae430cc602c4c0b29c9000023c299e92a35adc4b'),
    (v1_plan,'749292bbe2ed1cf05901d278aee752e3404324037a501d0da7d19c8e1893c93e'),
    (v1_seed,'8d2ad36c44b26ef747585e78eb86a60baf1cdfaeebb0dee465b25713dc4570ca')]

preserved.extend([
 (BASE/'htpeo-dms-current-import-pruned-modeq-v2-fresh-build.json','664b36b905611c46616af5b67bd98d593f62c03dd3c04e13b6d7325fb7946bea'),
 (BASE/'builds/htpeo-dms-current-import-pruned-modeq-v2/build-plan.json','a690d9c1ae4acc0de5fc20d6510d9bc0055552fe50f10d9fb9f76e1150284eea'),
 (BASE/'dms-modeq-v2-original99-hardlink-seed-completed-20261005.json','a5ce596e15b1c35a9c67bbda9ae912e83341c0f1956cbd4c069637587271815b')])
scan_file=BASE/'dms-all125-final-import-sufficiency-recommendations-20261005.json'
assert sha(scan_file)=='473795425c230299d305fa4d13c9741b8b92e81bbfc0875dcefb279545994817'
from dms_modeq_v2_original99_hardlink_seed import verify_seed as verify_v2_seed
v2_identity=verify_v2_seed('bfd720d9afbd3774f1cbce465dddf749b5d45e4ba28b755eed2421e078bfa814',
 'a5ce596e15b1c35a9c67bbda9ae912e83341c0f1956cbd4c069637587271815b')
v2_receipt=json.loads((BASE/'htpeo-dms-current-import-pruned-modeq-v2-fresh-build.json').read_bytes())
for row in v2_receipt['builds']:
 if row['exit']==0:
  for artifact in row['artifacts']:assert sha(artifact['file'])==artifact['sha256']
for file,expected in preserved:assert sha(file)==expected
complete_file=BASE/'dms-full228-complete-official-closure-and-reuse-proposal-20261005.json'
assert sha(complete_file)=='620fe0d86aff72859d8b9d97d8f793988710a145f200ae3cb4f05ea322f2bd2a'
complete=copy.deepcopy(json.loads(complete_file.read_bytes()))
original_plan=json.loads((ORIGINAL/'build-plan.json').read_bytes())
assert len(original_plan['modules'])==228 and not DEST.exists()
DEST.mkdir()
changes={r['module']:dict(r) for r in complete['all_original_three_header_diffs_unchanged']}
modules=[];identities=[]
for entry in original_plan['modules']:
    source=Path(entry['file']);raw=source.read_bytes();name=entry['module']
    assert h(raw)==entry['sha256']
    if name in changes:
        r=changes[name];a,b=r['replaced_bytes_start'],r['replaced_bytes_end']
        roots=r['proposed_header_span'].split('\n')
        assert roots[0]=='import Mathlib.Data.Nat.Basic'
        roots.insert(1,'import Mathlib.Data.Nat.ModEq')
        roots.insert(2,'import Mathlib.Data.Fin.SuccPred')
        roots.insert(3,'import Mathlib.Data.Fintype.Prod')
        header='\n'.join(roots).encode('utf8')
        staged=raw[:a]+header+raw[b:]
        assert raw[:a]+raw[b:]==staged[:a]+staged[a+len(header):]
        assert h(raw[:a]+raw[b:])==r['remainder_body_sha256']
        r['proposed_header_span']=header.decode('utf8');r['proposed_source_sha256']=h(staged)
        r['unified_diff']=''.join(difflib.unified_diff(raw.decode().splitlines(True),staged.decode().splitlines(True),
            fromfile=name+'.frozen-original.lean',tofile=name+'.proposed-modeq-v3.lean'))
        body=h(raw[:a]+raw[b:])
    else:staged=raw;body=h(raw)
    target=DEST/source.relative_to(ORIGINAL)
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as stream:stream.write(staged)
    modules.append(dict(entry,file=str(target.resolve()),sha256=h(staged),original_file=str(source),original_sha256=h(raw)))
    identities.append({'module':name,'original_source':str(source),'original_source_sha256':h(raw),
        'staged_source':str(target.resolve()),'proposed_source_sha256':h(staged),'scientific_body_sha256':body,
        'entire_source_unchanged':name not in changes,'body_options_comments_identical':True,
        'imports':[n for n in read_imports(target) if n!='all'],
        'staged_source_identity':'ACTUAL_COLD_V3_BYTE_IDENTICAL_OUTSIDE_THREE_HEADER_SPANS'})
audits=[]
for audit in original_plan['audit_modules']:
    source=ORIGINAL/audit;target=DEST/audit
    with target.open('xb') as stream:stream.write(source.read_bytes())
    previous=next(r for r in complete['audit_identity'] if r['audit_module']==audit)
    audits.append(dict(previous,proposed_file=str(target.resolve()),staged_file=str(target.resolve()),
                       staged_source_identity='ACTUAL_UNCHANGED_COLD_V3_AUDIT'))

# Rebuild the closed reachable graph against the actual v3 import roots, then
# rehash every original official source/olean. Existing unit identities may be
# shared as metadata, never inferred merely from the same module name.
old_graph_path=Path(complete['complete_official_graph']['source_artifact_manifest'])
assert sha(old_graph_path)=='936867aecf295ca4892a97b173db0227c403c7177c6bd68859d7b6e8a45b8fcd'
graph=json.loads(old_graph_path.read_bytes());by_name={r['module']:r for r in graph}
for i,row in enumerate(graph,1):
    source=Path(row['source']);artifact=Path(row['official_olean'])
    assert sha(source)==row['source_sha256'] and sha(artifact)==row['official_olean_sha256']
    actual=list(dict.fromkeys(n for n in read_imports(source) if n!='all'))
    prelude=bool(re.search(r'^\s*prelude\s*$',stripped(source.read_text(encoding='utf8')),re.M))
    implicit=row['module']!='Init' and not prelude
    assert actual==row['imports'] and implicit==row['implicit_Init_included']
    assert set(actual)|({'Init'} if implicit else set())==set(row['effective_import_dependencies'])
    if i%500==0:print('V3 exact official source/artifact graph checked',i,'/',len(graph),flush=True)
custom_names={r['module'] for r in modules};direct={'Init'}
for entry in modules:
    direct.update(n for n in read_imports(entry['file']) if n not in custom_names and n!='all')
for audit in original_plan['audit_modules']:
    direct.update(n for n in read_imports(DEST/audit) if n not in custom_names and n!='all')
assert 'Mathlib.Data.Nat.ModEq' in direct and direct<=set(by_name)
reached=set();pending=list(direct)
while pending:
    name=pending.pop()
    if name not in reached:reached.add(name);pending.extend(set(by_name[name]['effective_import_dependencies'])-reached)
assert reached==set(by_name) and len(reached)==2735
assert not {'Mathlib','Mathlib.Tactic'}&reached
graphpath=DEST/'official-full-source-artifact-closure.json'
with graphpath.open('xb') as stream:stream.write(old_graph_path.read_bytes())
assert sha(graphpath)==sha(old_graph_path)
direct_ids=[]
for name in sorted(direct):
    row=dict(by_name[name]);artifact=Path(row['official_olean']);siblings=[]
    for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
        file=artifact.with_suffix(suffix)
        if file.is_file():siblings.append({'file':str(file),'bytes':file.stat().st_size,'sha256':sha(file)})
    row['direct_compiled_artifact_identity']=siblings;direct_ids.append(row)
plan=dict(original_plan,id=PROJECT,source_dir=str(DEST.resolve()),modules=modules,
    status='PREPARED_COLD_IMPORT_ONLY_FINITE_PROVIDER_V3_NO_HARD_LINKS_NO_COMPILATION',builds=[],
    original_family_id='htpeo-dms-current',original_plan_sha256=complete['original_source_plan_sha256'],
    original119_immutable_receipt=complete['immutable_original119_receipt_binding']['file'],
    original119_immutable_receipt_sha256=complete['immutable_original119_receipt_binding']['sha256'],
    exact_full_official_closure=str(graphpath),exact_full_official_closure_sha256=sha(graphpath),
    operational_difference='Separate body-identical v3 adding Nat.ModEq, Fin.SuccPred and Fintype.Prod through the same three original header spans;99 reuse from proven v1 copied outputs remains unperformed. Original/v2 file link counts stay2.')
# Bind the true immutable metadata snapshot, rather than its mutable canonical view.
binding=json.loads((BASE/'dms-original119-immutable-receipt-binding-20261005.json').read_bytes())
plan['original119_immutable_receipt']=binding['immutable_original119_receipt']
planpath=DEST/'build-plan.json';plan_sha=save_new(planpath,plan)
complete['status']='ACTUAL_COLD_FINITE_PROVIDER_V3_COMPLETE_GRAPH_STAGE_PROPOSAL_NO_LINKS_NO_LEAN'
complete['prepared_utc']=datetime.now(timezone.utc).isoformat()
complete['hypothetical_plan']=str(planpath);complete['hypothetical_plan_sha256']=plan_sha
complete['all_original_three_header_diffs_unchanged']=list(changes.values())
complete['all228_custom_source_identity_and_closed_custom_graph']=identities
complete['audit_identity']=audits
complete['immutable_original119_receipt_binding']['file']=binding['immutable_original119_receipt']
complete['complete_official_graph']['all_direct_roots_including_custom_implicit_Init']=sorted(direct)
complete['complete_official_graph']['source_artifact_manifest']=str(graphpath)
complete['complete_official_graph']['source_artifact_manifest_sha256']=sha(graphpath)
complete['complete_official_graph']['direct_official_artifact_identities']=direct_ids
complete['preserved_v1_receipt_plan_seed']=[{'file':str(p),'sha256':s} for p,s in preserved]
complete['previous_route_failure_qualification']='Original v1 lacked Nat.ModEq exposure; v2 lacked Fin.castLE_injective exposure, and static checks found Finset/Fintype provider gaps. No scientific body is repaired. These import-only static candidates require actual v3 elaboration.'
complete['preserved_v2_NTFS99_identity']=v2_identity
complete['all125_static_exposure_scan']={'file':str(scan_file),'sha256':sha(scan_file),'qualification':'Static provider candidates only, not a promise of elaboration.'}
complete['proposed99_seed_source']='Proven original-owned cold outputs already COPIED into v1; no new original-output links permitted.'
complete['owned_output_eligibility_inventory']['stage_exists']=True
complete['owned_output_eligibility_inventory']['outputs_copied_or_marked_reusable']=False
proposalpath=BASE/'dms-v3-complete-stage-proposal-20261005.json'
proposal_sha=save_new(proposalpath,complete)
identitypath=DEST/'stage-source-identity-manifest.json'
identity_sha=save_new(identitypath,{'sources':identities,'audits':audits,'custom_outputs':[]})
prep={'status':'COLD_FINITE_PROVIDER_V3_STAGE_GRAPH_VERIFIER_PREPARATION_ONLY_NO_LINKS_NO_LEAN',
    'prepared_utc':datetime.now(timezone.utc).isoformat(),'stage':str(DEST.resolve()),
    'diagnostic_source_plan':str(planpath),'diagnostic_source_plan_sha256':plan_sha,
    'stage_identity_manifest':str(identitypath),'stage_identity_manifest_sha256':identity_sha,
    'immutable_original119_receipt':binding['immutable_original119_receipt'],
    'immutable_original119_receipt_sha256':binding['original119_receipt_sha256'],
    'official_full_source_artifact_closure':str(graphpath),'official_full_source_artifact_closure_sha256':sha(graphpath),
    'complete_stage_proposal':str(proposalpath),'complete_stage_proposal_sha256':proposal_sha,
    'all228_scientific_bodies_options_comments_identical':True,'selected123_audits_unchanged':True,
    'official_graph_units':2735,'additional_new_direct_exposure':['Mathlib.Data.Nat.ModEq','Mathlib.Data.Fin.SuccPred','Mathlib.Data.Fintype.Prod'],
    'original119_and_failed_v1_receipts_unchanged':True,'own_outputs_present':0,
    'original_and_v2_NTFS_link_counts_preserved':2,'v2_own_outputs_not_reused':True,
    'proposed99_seed_source':'V1_PROVEN_OWN_COPIES_ONLY_NO_NEW_ORIGINAL_LINKS',
    'hard_link_policy_and_guarded_runner':'TO_BE_PREPARED_SEPARATELY_NO_ACTION_AUTHORIZED_BY_THIS_RECORD'}
preppath=BASE/'dms-v3-cold-stage-and-link-adapter-preparation-20261005.json'
prep_sha=save_new(preppath,prep)
old_verifier=BASE/'verify_dms_full228_stage.py';text=old_verifier.read_text(encoding='utf8')
text=text.replace('htpeo-dms-current-import-pruned-diagnostic',PROJECT)
text=text.replace('dms-full228-cold-stage-and-adapter-preparation-20261005.json',preppath.name)
text=text.replace('dms-full228-complete-official-closure-and-reuse-proposal-20261005.json',proposalpath.name)
text=text.replace('620fe0d86aff72859d8b9d97d8f793988710a145f200ae3cb4f05ea322f2bd2a',proposal_sha)
text=text.replace('dms-full228-stage-identity-and-conditional99-reuse-review-20261005.json',
    'dms-v3-stage-identity-and-conditional99-link-review-20261005.json')
text=text.replace('READ_ONLY_STAGE_BODY_FULL_OFFICIAL_IDENTITY_AND99_CONDITIONAL_REUSE_CHECK_PASS',
    'READ_ONLY_V3_STAGE_BODY_FULL_OFFICIAL_IDENTITY_AND99_CONDITIONAL_HARD_LINK_CHECK_PASS')
ast.parse(text)
verifier=BASE/'verify_dms_v3_stage.py'
assert not verifier.exists();verifier.write_text(text,encoding='utf8',newline='')
diffpath=BASE/'dms-v3-stage-verifier.diff'
assert not diffpath.exists();diffpath.write_text(''.join(difflib.unified_diff(
    old_verifier.read_text().splitlines(True),text.splitlines(True),fromfile=old_verifier.name,tofile=verifier.name)),encoding='utf8')
for file,expected in preserved:assert sha(file)==expected
assert sha(BASE/'htpeo-dms-current-fresh-build.json')=='feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238'
assert verify_v2_seed('bfd720d9afbd3774f1cbce465dddf749b5d45e4ba28b755eed2421e078bfa814',
 'a5ce596e15b1c35a9c67bbda9ae912e83341c0f1956cbd4c069637587271815b')==v2_identity
assert not list(DEST.rglob('*.olean'))
print(json.dumps({'stage_preparation':str(preppath),'stage_preparation_sha256':prep_sha,
    'complete_proposal_sha256':proposal_sha,'plan_sha256':plan_sha,'stage_verifier_sha256':sha(verifier),
    'verifier_diff_sha256':sha(diffpath),'official_units':2735,'stage_outputs':0,'links':0,'new_Lean_invocations':0},indent=2),flush=True)
