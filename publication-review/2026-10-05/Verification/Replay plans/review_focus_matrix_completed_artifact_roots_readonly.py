"""Read-only rehash/qualification after all3 actual PASS and explicit root approval.
Never compiles, copies outputs, updates canonical manuscripts or renders PDFs.
"""
from pathlib import Path
import argparse,hashlib,json,re
from datetime import datetime,timezone
from audit_axioms import parse as parse_axioms
from lean_imports import stripped

BASE=Path(__file__).resolve().parent
PROPOSAL_SHA='9f45428eb9f3a8edd85cbfebc49182f2b1626396f605faa4b8fef23a7231c55d'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
parser=argparse.ArgumentParser()
parser.add_argument('--root-approval-file',required=True)
parser.add_argument('--root-approval-sha256',required=True)
args=parser.parse_args()
approval_path=Path(args.root_approval_file);assert sha(approval_path)==args.root_approval_sha256
approval=json.loads(approval_path.read_text(encoding='utf-8'))
assert approval['status']=='ROOT_APPROVED_READ_ONLY_FOCUS_MATRIX_THREE_SEED_COMPLETION_REHASH'
assert approval['proposal_sha256']==PROPOSAL_SHA
proposal_path=BASE/'proposals/focus-matrix-three-seed-completion-proposal-20261005.json'
assert sha(proposal_path)==PROPOSAL_SHA
proposal=json.loads(proposal_path.read_text(encoding='utf-8'))
canonical_paths=[BASE.parent/n for n in ['novel_results_content.json','novel_proof_expansions.json','novel_proof_coverage_2026-10-04.json']]
canonical_before={str(p):sha(p) for p in canonical_paths}
standard=['propext','Classical.choice','Quot.sound']
seeds=[];all_output_count=0;all_print_count=0;all_source_count=0
for prepared in proposal['source_records']:
    seed=prepared['seed'];project=prepared['project_id'];plan_path=Path(prepared['plan_file'])
    assert sha(plan_path)==prepared['plan_sha256']==approval['source_plan_sha256'][str(seed)]
    plan=json.loads(plan_path.read_text(encoding='utf-8'));dest=plan_path.parent
    receipt_path=BASE/(project+'-fresh-build.json')
    expected_receipt=approval['receipt_sha256'][str(seed)];assert re.fullmatch(r'[a-f0-9]{64}',expected_receipt)
    assert sha(receipt_path)==expected_receipt
    if seed<2:assert expected_receipt==prepared['actual_completed_seed_record']['receipt_sha256']
    receipt=json.loads(receipt_path.read_text(encoding='utf-8'))
    assert receipt['status']=='PASS' and receipt.get('finished_utc')
    assert receipt['version']==plan['version']=='4.33.1'
    assert receipt['mathlib_pin']==plan['mathlib_pin']=='0df444a360eaa60ab8c11dca51a86af692955474'
    assert receipt['modules']==plan['modules']
    assert len(plan['modules'])==71 and len(plan['audit_modules'])==1 and len(set(plan['endpoints']))==6
    rows=receipt['builds'];sources=[r for r in rows if not r['is_endpoint_audit']];audits=[r for r in rows if r['is_endpoint_audit']]
    assert len(sources)==71 and len(audits)==1 and len(rows)==72
    by_name={r['module']:r for r in sources};assert len(by_name)==71
    outputs=[];raw_audits=[]
    for module in plan['modules']:
        name=module['module'];file=Path(module['file']);row=by_name[name]
        assert file.resolve().is_relative_to(dest.resolve())
        assert sha(file)==module['sha256']==row['source_sha256']
        assert row['exit']==0 and not row.get('stop_reason')
        assert '-j1' in row['command'] and '-o' in row['command'] and str(file.relative_to(dest)) in row['command']
        assert not re.search(r'\b(sorry|admit|native_decide)\b',stripped(file.read_text(encoding='utf-8'))),name
        expected_artifacts=row['artifacts'];assert expected_artifacts
        actual=[]
        for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
            p=file.with_suffix(ext)
            if p.exists():actual.append({'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
        assert actual==expected_artifacts and file.with_suffix('.olean').exists(),name
        outputs.append({'module':name,'source_sha256':sha(file),'actual_artifacts':actual})
        g=row.get('own_job_resource_receipt');assert g and g['state']=='PASS' and g['exit']==0 and g['attempted']
        assert g['own_job_assignment_before_resume']=='PASS'
        for stream in ['stdout','stderr']:
            lp=Path(g[stream+'_file']);assert sha(lp)==g[stream+'_sha256']
            assert lp.read_text(encoding='utf-8')==row[stream]
    for row in audits:
        file=dest/row['module'];assert row['module'] in plan['audit_modules']
        assert row['exit']==0 and not row.get('stop_reason') and sha(file)==row['source_sha256']
        assert '-j1' in row['command'] and '-o' in row['command']
        actual=[]
        for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
            p=file.with_suffix(ext)
            if p.exists():actual.append({'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
        assert actual==row['artifacts'] and file.with_suffix('.olean').exists()
        g=row['own_job_resource_receipt'];assert g['state']=='PASS' and g['exit']==0
        for stream in ['stdout','stderr']:
            lp=Path(g[stream+'_file']);assert sha(lp)==g[stream+'_sha256'] and lp.read_text(encoding='utf-8')==row[stream]
        actual_stdout=Path(g['stdout_file']).read_text(encoding='utf-8');parsed=parse_axioms(actual_stdout)
        requested=re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(file.read_text(encoding='utf-8')),re.M)
        assert len(requested)==6 and set(requested)==set(plan['endpoints'])
        assert len(parsed)==6 and {a['endpoint'] for a in parsed}==set(requested)
        assert all(a['classification']=='STANDARD_KERNEL_AXIOMS' and a['axioms']==standard and not a['native_axioms'] and not a['unrecognized_axioms'] for a in parsed)
        raw_audits.append({'audit':row['module'],'source_sha256':sha(file),'actual_stdout':actual_stdout,'stdout_file':g['stdout_file'],'stdout_sha256':g['stdout_sha256'],'six_actual_selected_prints':parsed,'actual_artifacts':actual})
    count=sum(len(o['actual_artifacts']) for o in outputs)+sum(len(a['actual_artifacts']) for a in raw_audits)
    all_output_count+=count;all_source_count+=len(sources);all_print_count+=6
    assert sha(receipt_path)==expected_receipt and sha(plan_path)==prepared['plan_sha256']
    seeds.append({'seed':seed,'project_id':project,'plan':str(plan_path),'plan_sha256':sha(plan_path),'receipt':str(receipt_path),'receipt_sha256':expected_receipt,'finished_utc':receipt['finished_utc'],'source_count':71,'selected_print_count':6,'all_current_own_output_hashes_rechecked':True,'own_output_file_count':count,'source_artifact_roots':outputs,'actual_selected_audits':raw_audits,'typed_selected_statements':prepared['typed_selected_statements']})
assert all_source_count==213 and all_print_count==18
assert {str(p):sha(p) for p in canonical_paths}==canonical_before
result={'status':'PASS_EXACT_THREE_SEED_213_SOURCE_18_STANDARD_SELECTED_ENDPOINT_SCOPE','qualified_utc':datetime.now(timezone.utc).isoformat(),'root_approval':str(approval_path),'root_approval_sha256':sha(approval_path),'prepared_proposal':str(proposal_path),'prepared_proposal_sha256':PROPOSAL_SHA,'family':'FOCUS-MATRIX','projects':seeds,'authored_sources_passed':213,'requested_selected_prints_passed':18,'current_owned_outputs_rehashed':all_output_count,'selected_axioms':standard,'selected_native_admitted_unknown_axioms':0,'scoped_conclusion':'Injectivity for each literal paired-factor matrix over Q and arbitrary remaining-factor matrix equality when B X = B Y. Full rank23 is the ordinary linear-algebra interpretation; fixed two-factor lists only. No global or multi-factor rigidity, support minimality, or new sparse scheme follows.','family_fresh_verification_proposal':{'status':'PASS','seed_projects':3,'authored_sources_passed':213,'authored_sources_planned':213,'selected_endpoint_prints_passed':18,'selected_endpoint_prints_requested':18,'selected_axiom_classification':'STANDARD_KERNEL_AXIOMS','route':'UNCHANGED_FROZEN_THREE_SEED_ORIGINAL_SOURCE_SCOPES','compiler_version':'Lean4.33.1','mathlib_pin':'0df444a360eaa60ab8c11dca51a86af692955474','seed_receipts':[{'seed':s['seed'],'receipt':s['receipt'],'receipt_sha256':s['receipt_sha256'],'source_plan_sha256':s['plan_sha256'],'finished_utc':s['finished_utc']} for s in seeds],'novelty_score_or_placement_upgrade_implied':False},'canonical_files_unchanged':canonical_before,'canonical_PDF_or_Lean_sources_modified':False,'Lean_or_compiler_executed':False}
dest=BASE/'focus-matrix-three-seed-completed-artifact-roots-qualified-20261005.json'
with dest.open('x',encoding='utf-8',newline='\n') as out:json.dump(result,out,ensure_ascii=False,indent=2);out.write('\n')
print(json.dumps({'file':str(dest),'sha256':sha(dest),'status':result['status'],'sources':213,'prints':18,'owned_outputs_rehashed':all_output_count}))
