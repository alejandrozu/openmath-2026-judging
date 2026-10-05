"""Prepared read-only qualifier for the unchanged Groth 2-source/5-print route.

No Lean, source edits, aliases or qualification execution during preparation.
An eventual invocation needs a new root-reviewed SHA-bound approval and completed receipt.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys
from audit_axioms import parse
from receipt_io import read_bytes_shared

BASE=Path(__file__).resolve().parent
PLAN=BASE/'builds/sakana-FOCUS-GROTH/build-plan.json'
PLAN_SHA='1d9db618520db9b9651018b4b4c77192616c5af911963fc3391055b6646ece7a'
RUNNER=BASE/'run_held_novelty_plan.py'
RUNNER_SHA='56952859e73e8773c44c84328e50144580527b82280da9d22229a2862ecedc10'
GRAPH=BASE/'proposals/held-original-granular-source-review/sakana-FOCUS-GROTH-complete-official-source-artifact-closure.json'
GRAPH_SHA='86bd08537eea030f2860f96e6efbd681c48da2d02057d64d9bd38816cd5a49b2'
REVIEW=BASE/'proposals/held-original-granular-source-review/sakana-FOCUS-GROTH-read-only-original-granular-review.json'
RECEIPT=BASE/'sakana-FOCUS-GROTH-fresh-build.json'
RUNTIME=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
RUNTIME_SHA='af49bacfabaa1fea71332ca0feae0fa1a60912219d5902291adc79f905bffb8d'
PREP=BASE/'original-E65-source-replay-preparation-20261005.json'
PREP_SHA='96f74d38af628c8763632c3a0869d7fa2404796ecf66de70fd13d6b0652e1e06'
AUDIT_SHA='2a43c7da7651a65f5de70d04a81ea77d53c5e2645ab7b2efc4e8e283644236e2'
PARSER_SHA='1ee59639204140430c088023539a648f9007cc26c1856cf8cd2e3c2e59d7143f'

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def exact(p, digest):
    assert sha(p)==digest,('SHA mismatch',str(p))
    return json.loads(read_bytes_shared(p))
def git_value(path, args):
    r=subprocess.run(['git','-C',str(path),*args],capture_output=True,text=True,encoding='utf8',check=True)
    return r.stdout.strip()

def qualify(receipt_sha, approval_path, approval_sha):
    approval_path=Path(approval_path).resolve()
    assert approval_path.is_relative_to(BASE)
    approval=exact(approval_path,approval_sha)
    assert approval['status']=='ROOT_APPROVED_GROTH_EXACT2_SOURCE5_OUTPUT_QUALIFICATION'
    assert approval['reviewed_helper_sha256']==sha(__file__)
    assert approval['completed_receipt_sha256']==receipt_sha
    assert approval['source_plan_sha256']==PLAN_SHA and approval['official_graph_sha256']==GRAPH_SHA
    assert approval['source_fidelity_review_sha256']==sha(REVIEW)
    assert sha(RUNNER)==RUNNER_SHA and sha(RUNTIME)==RUNTIME_SHA
    assert sha(BASE/'audit_axioms.py')==PARSER_SHA
    plan=exact(PLAN,PLAN_SHA);graph=exact(GRAPH,GRAPH_SHA)
    review=json.loads(REVIEW.read_bytes());receipt=exact(RECEIPT,receipt_sha)
    assert receipt['id']=='sakana-FOCUS-GROTH' and receipt['status']=='PASS' and receipt['finished_utc']
    assert not receipt.get('current_module') and not receipt['failed_invocations']
    assert receipt['version']==plan['version']=='4.33.1'
    assert receipt['mathlib_pin']==plan['mathlib_pin']=='0df444a360eaa60ab8c11dca51a86af692955474'
    assert receipt['lean_options']==plan['lean_options']=={}
    assert receipt['resource_settings']['runner_source_sha256']==RUNNER_SHA
    assert len(plan['modules'])==2 and len(plan['endpoints'])==5
    assert len(set(plan['endpoints']))==5
    assert {r['module'] for r in plan['modules']}=={'Row3Granular','SemanticTestGranular'}
    assert plan['audit_modules']==['FreshAudit1.lean']
    audit=Path(plan['source_dir'])/'FreshAudit1.lean';assert sha(audit)==AUDIT_SHA
    assert review['modified_import_spans']==[] and review['header_changes']==0
    assert review['original_plan_sha256']==PLAN_SHA
    source_by_name={r['module']:r for r in plan['modules']}
    source_identities=[]
    for source in plan['modules']:
        assert sha(source['file'])==source['sha256']
        old=next(r for r in review['source_identity_records'] if r['module']==source['module'])
        assert old['whole_file_byte_identity'] and old['original_source_sha256']==old['proposed_source_sha256']==source['sha256']
        source_identities.append(source)

    # All3954 pinned source/olean providers, not just a cached global node count.
    assert len(graph)==3954 and len({r['module'] for r in graph})==3954
    providers={r['module']:r for r in graph}
    assert not {'Mathlib','Mathlib.Tactic'} & set(providers)
    for row in graph:
        assert sha(row['source'])==row['source_sha256'] and Path(row['source']).stat().st_size==row['source_bytes']
        assert sha(row['official_olean'])==row['official_olean_sha256']
        assert Path(row['official_olean']).stat().st_size==row['official_olean_bytes']
        assert all(x in providers for x in row['dependency_names'])
    reachable=set();todo=list(review['official_direct_imports'])+['Init']
    while todo:
        name=todo.pop()
        if name in reachable:continue
        assert name in providers
        reachable.add(name);todo.extend(providers[name]['dependency_names'])
    assert reachable==set(providers)
    prep=exact(PREP,PREP_SHA);pins=[]
    assert len(prep['exact_original_nine_packages'])==9
    for dep in prep['exact_original_nine_packages']:
        path=Path(dep['prepared_source_path'])
        head=git_value(path,['rev-parse','HEAD']);origin=git_value(path,['remote','get-url','origin'])
        assert head==dep['original_manifest_rev']==dep['actual_prepared_Git_HEAD']
        assert origin==dep['actual_prepared_origin']==dep['original_manifest_url']
        rp=next(r for r in review['exact_dependency_pins'] if r['name']==dep['name'])
        assert rp['rev']==head
        pins.append({'name':dep['name'],'current_Git_HEAD':head,'current_origin':origin})

    sources=[r for r in receipt['builds'] if not r['is_endpoint_audit']]
    audits=[r for r in receipt['builds'] if r['is_endpoint_audit']]
    assert len(sources)==2 and {r['module'] for r in sources}==set(source_by_name)
    assert len(audits)==1 and audits[0]['module']=='FreshAudit1.lean'
    guards=[];outputs=[];raw_bindings=[]
    for row in receipt['builds']:
        assert row['exit']==0 and not row.get('stop_reason')
        expected_source=audit if row['is_endpoint_audit'] else Path(source_by_name[row['module']]['file'])
        assert row['source_sha256']==sha(expected_source)
        relative=expected_source.relative_to(Path(plan['source_dir']))
        expected_cmd=[str(RUNTIME),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000',
            '-o',str(relative.with_suffix('.olean')),str(relative)]
        assert row['command']==expected_cmd
        g=row['own_job_resource_receipt'];policy=g['resource_policy']
        assert g['command']==row['command'] and Path(g['cwd']).resolve()==Path(plan['source_dir']).resolve()
        assert g['attempted'] and g['exit']==0 and g['state']=='PASS' and g['own_job_assignment_before_resume']=='PASS'
        for key,value in {'initial_disk_bytes':4_000_000_000,'initial_physical_bytes':6*2**30,
            'initial_available_commit_bytes':5*2**30,'continuous_disk_bytes':1_000_000_000,
            'continuous_physical_bytes':3*2**30,'continuous_available_commit_bytes':2**30,
            'own_job_private_bytes':6*2**30,'own_process_private_bytes':6*2**30}.items():assert policy[key]==value
        assert g['minimum_disk_free_bytes']>=1_000_000_000 and g['minimum_physical_available_bytes']>=3*2**30
        assert g['minimum_available_commit_bytes']>=2**30 and g['job_peak_aggregate_private_bytes']<=6*2**30
        assert g['initial_system_memory_snapshot']['free_physical_bytes']>=6*2**30
        assert g['initial_system_memory_snapshot']['available_commit_bytes']>=5*2**30
        assert g['counter_helper_sha256']=='0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4'
        assert g['commit_counter_helper_sha256']=='1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed'
        for kind in ('stdout','stderr'):
            p=Path(g[kind+'_file']);assert sha(p)==g[kind+'_sha256']
            text=p.read_bytes().decode('utf8',errors='replace')
            assert text==row[kind]
            raw_bindings.append({'module':row['module'],'kind':kind,'file':str(p),'sha256':sha(p)})
        assert row['artifacts']
        for art in row['artifacts']:
            p=Path(art['file']).resolve();assert p.is_relative_to(Path(plan['source_dir']).resolve())
            assert p.stat().st_size==art['bytes'] and sha(p)==art['sha256']
            outputs.append({**art,'module':row['module']})
        guards.append({'module':row['module'],'actual_guard':g})
    actual=parse(audits[0]['stdout'])
    assert len(actual)==5 and {r['endpoint'] for r in actual}==set(plan['endpoints'])
    assert len({r['endpoint'] for r in actual})==5
    assert all(r['classification'] in {'AXIOM_FREE','STANDARD_KERNEL_AXIOMS'} and not r['native_axioms']
        and not r['unrecognized_axioms'] and 'sorryAx' not in r['axioms'] for r in actual)
    assert actual==receipt['selected_audit_axiom_review']
    assert audits[0]['selected_endpoint_print_coverage']['status']=='PASS'
    assert sha(RECEIPT)==receipt_sha
    result={'status':'PASS_EXACT_UNCHANGED_GROTH2_SOURCE5_SELECTED_OUTPUT_STANDARD_SCOPE',
        'qualified_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(__file__),
        'root_approval_sha256':approval_sha,'completed_receipt_sha256':receipt_sha,'source_plan_sha256':PLAN_SHA,
        'runner_sha256':RUNNER_SHA,'source_fidelity_review_sha256':sha(REVIEW),'official_graph_sha256':GRAPH_SHA,
        'runtime_sha256':RUNTIME_SHA,'current_nine_dependency_pins':pins,
        'current3954_official_source_and_olean_providers_rehashed':True,'exact_source_identities':source_identities,
        'authored_source_passes':2,'selected_audit_invocations':1,'selected_unique_prints':5,
        'actual_selected_axiom_classifications':actual,'raw_log_identities':raw_bindings,'current_own_artifact_identities':outputs,
        'actual_resource_guards':guards,'scientific_scope':'Universal three-row sign-matrix upper bound sqrt(3/2), and four specific-sign-matrix upper bounds sqrt2 in arbitrary real inner-product spaces. These are restricted upper bounds. sqrt(3/2)>6/5, so this does not improve the stronger ordinary6/5 comparison for the three-row sign-restricted class or establish a lower bound on the unrestricted constant.',
        'novel_priority_competition_score_class_or_publication_acceptance_upgraded':False,
        'historical_pilot_and_original_records_preserved':True,'compiler_alias_source_or_output_mutation':False}
    out=BASE/'groth-exact2-source5-completed-qualification-20261005.json'
    with out.open('x',encoding='utf8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({'qualification':str(out),'sha256':sha(out),'status':result['status']}))

if __name__=='__main__':
    assert len(sys.argv)==5 and sys.argv[1]=='--root-approved-exact-groth-qualification'
    qualify(sys.argv[2],sys.argv[3],sys.argv[4])
