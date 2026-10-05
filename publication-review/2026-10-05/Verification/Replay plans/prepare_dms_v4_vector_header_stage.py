"""Separate cold V4 source/graph and conditional owned-output reuse proposal only.

One extra import is added solely to InflationA; all scientific bodies/options and
the original123-print audit stay byte-identical. No output copy/link or Lean runs.
"""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re,difflib
from lean_imports import read_imports,stripped
from receipt_io import read_bytes_shared
from dms_v3_copy99_hardlink_seed import file_identity

BASE=Path(__file__).resolve().parent
V3=BASE/'builds/htpeo-dms-current-import-pruned-v3'
ORIGINAL=BASE/'builds/htpeo-dms-current'
DEST=BASE/'builds/htpeo-dms-current-import-pruned-v4-vector'
PROJECT=DEST.name
V3_PLAN_SHA='eea74ffbc9321a0663d6c77d8e7c79ee7de3da914c9af1bc66e9b3ed3750f7ba'
V3_RECEIPT_SHA='ff1dd1a5c1666631992bffb93f51271c6c4e162cb075f2ec80eddf15e741ccd4'
GRAPH_SHA='936867aecf295ca4892a97b173db0227c403c7177c6bd68859d7b6e8a45b8fcd'
DECISION_SHA='1ef3a8f282e99a393b802409b1d6faa399f48214b2fb5a3ebf0f75efe2adfb41'

def h(raw):return hashlib.sha256(raw).hexdigest()
def sha(path):
    d=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):d.update(block)
    return d.hexdigest()
def save(path,data):
    assert not path.exists()
    with path.open('x',encoding='utf8',newline='\n') as stream:json.dump(data,stream,indent=2);stream.write('\n')
    return sha(path)
def custom_closure(name,deps):
    seen=set();pending=[name]
    while pending:
        item=pending.pop()
        if item not in seen:seen.add(item);pending.extend(deps[item]-seen)
    return seen
def official_closure(names,graph):
    seen=set();pending=list(names)
    while pending:
        name=pending.pop()
        assert name in graph,('Unresolved exact official unit',name)
        if name not in seen:seen.add(name);pending.extend(set(graph[name]['effective_import_dependencies'])-seen)
    return seen

assert sha(V3/'build-plan.json')==V3_PLAN_SHA
receipt_path=BASE/'htpeo-dms-current-import-pruned-v3-fresh-build.json'
receipt_raw=read_bytes_shared(receipt_path);assert h(receipt_raw)==V3_RECEIPT_SHA
receipt=json.loads(receipt_raw);assert receipt['status']=='BUILD_FAILED_OR_TIMED_OUT' and receipt.get('current_module') is None
assert sha(BASE/'dms-v4-raw228-header-DAG-minimal-vector-provider-decision-20261005.json')==DECISION_SHA
decision=json.loads((BASE/'dms-v4-raw228-header-DAG-minimal-vector-provider-decision-20261005.json').read_bytes())
affected=set(decision['InflationA_change_affected_source_names']);assert len(affected)==7
plan=json.loads((V3/'build-plan.json').read_bytes());original=json.loads((ORIGINAL/'build-plan.json').read_bytes())
original_by_name={r['module']:r for r in original['modules']}
proposal3=json.loads((BASE/'dms-v3-complete-stage-proposal-20261005.json').read_bytes())
changes3={r['module']:r for r in proposal3['all_original_three_header_diffs_unchanged']}
assert not DEST.exists();DEST.mkdir()
identities=[];modules=[];extra_diff=None
for entry in plan['modules']:
    source=Path(entry['file']);raw=source.read_bytes();assert h(raw)==entry['sha256']
    name=entry['module'];frozen=Path(original_by_name[name]['file']).read_bytes()
    assert h(frozen)==original_by_name[name]['sha256']
    staged=raw
    if name=='InflationA':
        first=raw.splitlines(keepends=True)[0];assert first.rstrip(b'\r\n')==b'import InflationDefs'
        addition=b'import Mathlib.Data.Fin.VecNotation\n';offset=len(first)
        staged=raw[:offset]+addition+raw[offset:]
        assert staged[:offset]+staged[offset+len(addition):]==raw
        assert raw==frozen
        body=h(raw[offset:]);extra_diff={'module':name,'inserted_at_byte':offset,'inserted_header_bytes_utf8':addition.decode(),
            'original_header_span':first.decode(),'scientific_body_after_original_header_sha256':body,
            'V3_source_sha256':h(raw),'V4_source_sha256':h(staged),
            'exact_unified_diff':''.join(difflib.unified_diff(raw.decode().splitlines(True),staged.decode().splitlines(True),fromfile='InflationA.V3.lean',tofile='InflationA.V4.lean'))}
    elif name in changes3:
        c=changes3[name];a,b=c['replaced_bytes_start'],c['replaced_bytes_end'];header=c['proposed_header_span'].encode()
        assert raw==frozen[:a]+header+frozen[b:];body=h(frozen[:a]+frozen[b:])
        assert body==c['remainder_body_sha256']
    else:
        assert raw==frozen;body=h(frozen)
    target=DEST/source.relative_to(V3);target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as stream:stream.write(staged)
    modules.append(dict(entry,file=str(target.resolve()),sha256=h(staged),V3_file=str(source),V3_sha256=h(raw)))
    identities.append({'module':name,'frozen_original_source_sha256':h(frozen),'V3_source_sha256':h(raw),
        'V4_source':str(target.resolve()),'V4_source_sha256':h(staged),'scientific_body_sha256':body,
        'body_options_comments_identical_to_frozen_original':True,'entire_source_identical_to_V3':staged==raw,
        'exact_V4_imports':[n for n in read_imports(target) if n!='all']})
audits=[]
for audit in plan['audit_modules']:
    raw=(V3/audit).read_bytes();assert raw==(ORIGINAL/audit).read_bytes()
    with (DEST/audit).open('xb') as stream:stream.write(raw)
    audits.append({'audit':audit,'file':str((DEST/audit).resolve()),'sha256':h(raw),
        'identical_to_original_and_V3':True,'requested123_axioms':re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(raw.decode()),re.M)})
assert sum(len(a['requested123_axioms']) for a in audits)==123
graph_path=V3/'official-full-source-artifact-closure.json';assert sha(graph_path)==GRAPH_SHA
graph_rows=json.loads(graph_path.read_bytes());graph={r['module']:r for r in graph_rows};assert len(graph)==2735
for index,row in enumerate(graph_rows,1):
    assert sha(row['source'])==row['source_sha256'] and sha(row['official_olean'])==row['official_olean_sha256']
    if index%500==0:print('V4 exact2735 official source/artifact rehashed',index,flush=True)
with (DEST/graph_path.name).open('xb') as stream:stream.write(graph_path.read_bytes())
names={m['module'] for m in modules};imports={m['module']:set(read_imports(m['file']))-{'all'} for m in modules}
deps={name:roots&names for name,roots in imports.items()}
all_direct={'Init'}|set().union(*(roots-names for roots in imports.values()))
for audit in plan['audit_modules']:all_direct.update(set(read_imports(DEST/audit))-names-{'all'})
assert official_closure(all_direct,graph)==set(graph) and not {'Mathlib','Mathlib.Tactic'}&set(graph)
per_source=[]
for name in sorted(names):
    closure=custom_closure(name,deps);roots={'Init'}|set().union(*(imports[n]-names for n in closure))
    reached=official_closure(roots,graph)
    per_source.append({'module':name,'full_custom_dependency_names':sorted(closure),'direct_and_inherited_official_roots':sorted(roots),
        'full_exact_official_provider_names':sorted(reached),'official_provider_count':len(reached)})
plan4=copy.deepcopy(plan);plan4.update(id=PROJECT,source_dir=str(DEST.resolve()),modules=modules,
    status='COLD_MINIMAL_ONE_EXTRA_INFLATIONA_VECTOR_IMPORT_V4_NO_OUTPUTS_NO_LEAN',builds=[],
    exact_full_official_closure=str((DEST/graph_path.name).resolve()),
    previous_v3_source_plan_sha256=V3_PLAN_SHA,previous_v3_actual_receipt_sha256=V3_RECEIPT_SHA,
    operational_difference='Only one additional InflationA import header.221 previous OWN source-pass outputs are conditional reuse candidates (99 existing V1 copy inputs plus122 unaffected V3-new outputs);7 new sources and123 prints still required.')
plan_sha=save(DEST/'build-plan.json',plan4)
identity_sha=save(DEST/'stage-source-identity-manifest.json',{'sources':identities,'audits':audits,'own_outputs_present':0})
closure_sha=save(DEST/'per-source-complete-custom-and-official-exposure.json',per_source)
by_module={m['module']:m for m in modules};reuse=[]
for row in receipt['builds']:
    if row['is_endpoint_audit'] or row['exit']!=0:continue
    name=row['module'];assert name not in affected and not row.get('stop_reason')
    assert row['source_sha256']==by_module[name]['sha256']
    full=custom_closure(name,deps);assert not full&affected
    assert all(next(x for x in identities if x['module']==n)['entire_source_identical_to_V3'] for n in full)
    artifacts=[]
    for artifact in row['artifacts']:
        source=Path(artifact['file']);assert source.is_relative_to(V3.resolve()) and sha(source)==artifact['sha256']
        info=file_identity(source);assert info['link_count']==1 and info['bytes']==artifact['bytes']
        artifacts.append({**artifact,'current_source_identity':info,'proposed_target':str((DEST/source.relative_to(V3)).resolve()),
            'proposal_only':'Hardlink source is V3 NEW single-link output, not any protected99 inode. Link policy/approval remains unperformed.'})
    reuse.append({'module':name,'actual_V3_source_PASS_row':row,'full_unchanged_custom_closure':sorted(full),
        'conditional_reuse_eligible_given_future_full_identity_validation':True,'artifacts':artifacts})
assert len(reuse)==122
v1=BASE/'builds/htpeo-dms-current-import-pruned-diagnostic'
seed=json.loads((BASE/'dms-v3-v1copy99-hardlink-seed-completed-20261005.json').read_bytes())
eligible=set(seed['eligible99_module_names']);assert len(eligible)==99 and not eligible&affected
current_v1_olean={str(p.relative_to(v1).with_suffix('')).replace('\\','.') for p in v1.rglob('*.olean')}
assert current_v1_olean==eligible,'Readonly V1 fallback must contain exactly the reviewed99 output modules'
native99=[]
for module in sorted(eligible):
    file=v1/Path(module.replace('.','/')+'.olean');info=file_identity(file);assert info['link_count']==2
    native99.append({'module':module,'readonly_V1_copy_olean':str(file.resolve()),'sha256':sha(file),'file_identity':info})
provider=graph['Mathlib.Data.Fin.VecNotation'];assert provider['source_sha256']=='08b3449fd3135bb1b4123e74445bad9317b2aa7515a0464aaddc0d656971568e'
proposal={'status':'ACTUAL_COLD_MINIMAL_VECTOR_PROVIDER_V4_STAGE_AND_CONDITIONAL221_OWN_REUSE_PROPOSAL_NO_ALIASES_NO_LEAN',
    'prepared_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
    'source_plan':str((DEST/'build-plan.json').resolve()),'source_plan_sha256':plan_sha,
    'stage_identity_manifest_sha256':identity_sha,'per_source_complete_exposure_manifest_sha256':closure_sha,
    'source_plan_V3_sha256':V3_PLAN_SHA,'preserved_V3_actual_failure_receipt_sha256':V3_RECEIPT_SHA,
    'original119_receipt_sha256':'feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238',
    'original_three_V3_header_diffs_unchanged':list(changes3.values()),'only_additional_V4_header_diff':extra_diff,
    'all228_bodies_options_comments_unchanged':True,'unchanged123_audit':audits,
    'official_full2735_source_artifact_manifest_sha256':GRAPH_SHA,'exact_newly_exposed_vector_provider':provider,
    'full_official_union_unchanged_but_actual_InflationA_exposure_expanded':True,
    'affected7_new_required_sources':sorted(affected),'actual122_V3_new_unaffected_source_PASS_reuse_candidates':reuse,
    'existing99_original_owned_V1_COPY_readonly_inputs':native99,
    'reuse_policy_proposal':'Use existing V1 copied99 outputs read-only without extra aliases; only122 V3-new single-link outputs may be proposed as aliases intoV4 after explicit review. No original/V2/99 V1-V3 inode counts changed.',
    'qualified_reuse_count_proposed':221,'actual_new_source_invocations_required':7,'actual_audit_invocations_required':1,
    'positive_qualification_inference':False,'own_outputs_currently_present_in_V4':0,
    'source_output_links_copies_or_Lean_invocations_performed':0,
    'seed_policy_stage_verifier_and_guarded_runner':'TO_BE_PREPARED_SEPARATELY;NO_ACTION_AUTHORIZED_BY_THIS_PACKET'}
out=BASE/'dms-v4-vector-cold-stage-complete221-reuse-proposal-20261005.json';out_sha=save(out,proposal)
assert read_bytes_shared(receipt_path)==receipt_raw and not list(DEST.rglob('*.olean'))
print(json.dumps({'proposal':str(out),'proposal_sha256':out_sha,'plan_sha256':plan_sha,'identity_sha256':identity_sha,
    'per_source_exposure_sha256':closure_sha,'V4_outputs':0,'aliases':0,'Lean_invocations':0,'reuse_candidates':221,'new_sources':7},indent=2),flush=True)
