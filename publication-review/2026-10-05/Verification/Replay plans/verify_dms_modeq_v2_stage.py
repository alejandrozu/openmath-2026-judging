"""Read-only verification of actual DMS stage and conditional own-output reuse.

No compiler, copy, reuse label or source mutation is performed here. This verifier
is also the prepared route's identity preflight; it does not grant a resource lease.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,subprocess,sys
from lean_imports import read_imports,stripped
BASE=Path(__file__).resolve().parent
PROJECT='htpeo-dms-current-import-pruned-modeq-v2'
def digest(path):
    d=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):d.update(block)
    return d.hexdigest()
def load(path):return json.loads(Path(path).read_bytes())
def graph_closure(name,edges):
    reached=set();pending=[name]
    while pending:
        item=pending.pop()
        if item not in reached:reached.add(item);pending.extend(edges[item])
    return reached

def verify_stage(require_cold=True):
    preparation_path=BASE/'dms-modeq-v2-cold-stage-and-link-adapter-preparation-20261005.json'
    prep=load(preparation_path)
    complete_path=BASE/'dms-modeq-v2-complete-stage-proposal-20261005.json'
    assert digest(complete_path)=='d65e7f7a81149ab7c6988c4aa9450a228279f984de302dec8bf6852763488fcc'
    complete=load(complete_path)
    immutable=Path(prep['immutable_original119_receipt'])
    assert digest(immutable)==prep['immutable_original119_receipt_sha256']=='feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238'
    original_receipt=load(immutable)
    original_plan_path=BASE/'builds/htpeo-dms-current/build-plan.json'
    assert digest(original_plan_path)==complete['original_source_plan_sha256']
    original_plan=load(original_plan_path)
    original={row['module']:row for row in original_plan['modules']}
    proposed=load(complete['hypothetical_plan'])
    assert digest(complete['hypothetical_plan'])==complete['hypothetical_plan_sha256']
    hypothetical={row['module']:row for row in proposed['modules']}
    stage=BASE/'builds'/PROJECT
    assert Path(prep['stage']).resolve()==stage.resolve()
    plan_path=stage/'build-plan.json'
    assert digest(plan_path)==prep['diagnostic_source_plan_sha256']
    plan=load(plan_path)
    for key in ['version','mathlib_pin','lean_options','endpoints','audit_modules','roots','commit']:
        assert plan[key]==original_plan[key],('Semantic plan field changed',key)
    assert plan['id']==PROJECT and plan['version']=='4.33.1'
    assert plan['mathlib_pin']=='0df444a360eaa60ab8c11dca51a86af692955474'
    assert len(plan['modules'])==len(original)==len(hypothetical)==228
    changes={row['module']:row for row in complete['all_original_three_header_diffs_unchanged']}
    assert set(changes)=={'BlockStar','SeamSeq','InflationDefs'}
    custom_edges={};source_identity=[]
    stage_names={row['module'] for row in plan['modules']}
    assert stage_names==set(original)
    for row in plan['modules']:
        name=row['module'];file=Path(row['file']).resolve()
        assert file.is_relative_to(stage.resolve())
        raw=file.read_bytes();old=Path(original[name]['file']).read_bytes()
        assert hashlib.sha256(old).hexdigest()==original[name]['sha256']==row['original_sha256']
        assert hashlib.sha256(raw).hexdigest()==row['sha256']==hypothetical[name]['sha256']
        if name in changes:
            change=changes[name];a,b=change['replaced_bytes_start'],change['replaced_bytes_end']
            replacement=change['proposed_header_span'].encode('utf8')
            assert old[a:b]==b'import Mathlib' and raw==old[:a]+replacement+old[b:]
            assert old[:a]+old[b:]==raw[:a]+raw[a+len(replacement):]
            assert hashlib.sha256(old[:a]+old[b:]).hexdigest()==change['remainder_body_sha256']
        else:assert raw==old
        imports=[n for n in read_imports(file) if n!='all']
        assert not {'Mathlib','Mathlib.Tactic'}&set(imports)
        custom_edges[name]=[n for n in imports if n in original]
        source_identity.append({'module':name,'staged_sha256':row['sha256'],
            'original_sha256':row['original_sha256'],'all_body_options_comments_identical':True,
            'whole_source_identical':name not in changes})
    for audit in plan['audit_modules']:
        assert digest(stage/audit)==digest(Path(original_plan['source_dir'])/audit)
    requested=[]
    for audit in plan['audit_modules']:
        requested.extend(re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped((stage/audit).read_text(encoding='utf8')),re.M))
    assert len(requested)==len(set(requested))==123
    assert set(requested)==set(complete['audit_identity'][0]['requested_prints'])

    full_path=Path(prep['official_full_source_artifact_closure'])
    assert digest(full_path)==prep['official_full_source_artifact_closure_sha256']=='936867aecf295ca4892a97b173db0227c403c7177c6bd68859d7b6e8a45b8fcd'
    graph=load(full_path);by_name={row['module']:row for row in graph}
    assert len(graph)==len(by_name)==2735
    official_edges={}
    for row in graph:
        source=Path(row['source']);artifact=Path(row['official_olean'])
        assert digest(source)==row['source_sha256']
        assert digest(artifact)==row['official_olean_sha256']
        actual=[n for n in read_imports(source) if n!='all']
        actual=list(dict.fromkeys(actual))
        assert actual==row['imports'],row['module']
        prelude=bool(re.search(r'^\s*prelude\s*$',stripped(source.read_text(encoding='utf8')),re.M))
        implicit=row['module']!='Init' and not prelude
        assert implicit==row['implicit_Init_included']
        edges=set(actual)|({'Init'} if implicit else set())
        assert edges==set(row['effective_import_dependencies']) and edges<=set(by_name)
        official_edges[row['module']]=edges
    roots=set(complete['complete_official_graph']['all_direct_roots_including_custom_implicit_Init'])
    reached=set();pending=list(roots)
    while pending:
        item=pending.pop()
        if item not in reached:reached.add(item);pending.extend(official_edges[item]-reached)
    assert reached==set(by_name) and not {'Mathlib','Mathlib.Tactic'}&reached
    for row in complete['complete_official_graph']['direct_official_artifact_identities']:
        for artifact in row['direct_compiled_artifact_identity']:
            assert digest(artifact['file'])==artifact['sha256']
    mathlib=BASE/'dependencies/4.33.1/mathlib'
    for pin in complete['current_actual_git_pins']:
        directory=mathlib if pin['name']=='mathlib' else mathlib/'.lake/packages'/pin['name']
        actual=subprocess.run(['git','-C',str(directory),'rev-parse','HEAD'],capture_output=True,text=True,check=True).stdout.strip()
        origin=subprocess.run(['git','-C',str(directory),'remote','get-url','origin'],capture_output=True,text=True,check=True).stdout.strip()
        assert actual==pin['rev'] and origin==pin['url']
    for item in [complete['exact_runtime_receipt'],complete['exact_official_cache_receipt']]:
        assert digest(item['file'])==item['sha256']
    assert load(complete['exact_official_cache_receipt']['file'])['status']=='PASS'

    eligibility_path=Path(complete['owned_output_eligibility_inventory']['file'])
    assert digest(eligibility_path)==complete['owned_output_eligibility_inventory']['sha256']=='10b72fd70150dde29421f0cd20b99db01634ecda06906c8169ae3fe2c8cd55f2'
    eligibility=load(eligibility_path)
    original_pass={row['module']:row for row in original_receipt['builds']
        if row.get('exit')==0 and not row.get('is_endpoint_audit') and row.get('stop_reason') is None}
    assert len(original_pass)==119
    eligible=[];eligible_identity=[]
    for row in eligibility['modules']:
        if not row['eligible_on_original_identity_checks_only']:continue
        name=row['module'];closure=graph_closure(name,custom_edges)
        assert closure==set(row['custom_dependency_closure']) and not closure&set(changes)
        assert closure<=set(original_pass)
        identity=[]
        for dependency in sorted(closure):
            old_entry=original[dependency]
            staged=stage/Path(old_entry['file']).relative_to(Path(original_plan['source_dir']))
            assert staged.read_bytes()==Path(old_entry['file']).read_bytes()
            assert digest(staged)==old_entry['sha256']==original_pass[dependency]['source_sha256']
            outputs=[]
            for artifact in original_pass[dependency]['artifacts']:
                assert digest(artifact['file'])==artifact['sha256']
                assert Path(artifact['file']).stat().st_size==artifact['bytes']
                outputs.append(dict(artifact,current_identity_matches=True))
            identity.append({'module':dependency,'original_and_staged_source_sha256':old_entry['sha256'],
                             'current_original_owned_output_identity':outputs})
        eligible.append(name)
        eligible_identity.append({'module':name,'verified_staged_and_original_full_custom_closure':identity,
            'official_dependencies':'COMPLETE2735_UNIT_SOURCE_AND_OLEAN_HASH_GRAPH_AND_EXACT_RUNTIME/GIT/CACHE_IDENTITIES_RECHECKED',
            'eligibility':'STAGE_IDENTITY_VERIFIED_CONDITIONAL_ROOT_POLICY_REQUIRED_NO_REUSE_PERFORMED'})
    assert len(eligible)==99 and set(eligible)==set(eligibility['eligible_candidate_modules'])
    affected=[name for name in original if graph_closure(name,custom_edges)&set(changes)]
    assert len(affected)==125 and set(affected).isdisjoint(eligible)
    unpassed=set(original)-set(original_pass)
    assert len(unpassed)==109
    must_cold=set(original)-set(eligible)
    assert len(must_cold)==129 and set(affected)|unpassed==must_cold
    own_oleans=list(stage.rglob('*.olean'))+list(stage.rglob('*.ilean'))
    if require_cold:assert not own_oleans,'No custom proof outputs are permitted in the cold preparation'
    return {'status':'READ_ONLY_V2_STAGE_BODY_FULL_OFFICIAL_IDENTITY_AND99_CONDITIONAL_HARD_LINK_CHECK_PASS',
        'checked_utc':datetime.now(timezone.utc).isoformat(),
        'diagnostic_plan_sha256':digest(plan_path),'preparation_sha256':digest(preparation_path),
        'verifier_source_sha256':digest(__file__),
        'immutable_original119_receipt_sha256':digest(immutable),
        'all228_source_body_identity':source_identity,'selected123_audit_requests_unchanged':requested,
        'official2735_source_and_olean_hashes_rechecked':True,
        'eligible99_module_names':sorted(eligible),'eligible99_actual_stage_identity':eligible_identity,
        'all125_affected_sources_must_remain_cold':sorted(affected),
        'all129_required_cold_sources':sorted(must_cold),'custom_outputs_present':len(own_oleans),
        'outputs_copied_or_marked_reusable':False,
        'qualification':'Exact stage identity is established only. Import sufficiency, mathematical PASS, cross-route output reuse and any source dispatch remain separately unapproved.'}

if __name__=='__main__':
    assert sys.argv[1:]==['--check-cold-stage'],'This preparation supports the explicit read-only cold check only'
    result=verify_stage(require_cold=True)
    out=BASE/'dms-modeq-v2-stage-identity-and-conditional99-link-review-20261005.json'
    assert not out.exists()
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'review':str(out),'review_sha256':digest(out),'status':result['status'],
                      'stage_sources':228,'eligible_conditional_outputs':99,'required_cold_sources':129}),flush=True)
