"""Prepared editorial helper: requires root approval and actual7+221/123 V4 qualification.
No Lean or PDF invocation. Only one DMS paragraph and additive fresh metadata change.
"""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import argparse,copy,hashlib,json,os,sys
BASE=Path(__file__).resolve().parent;VERIFY=BASE/'verification'
sys.path.insert(0,str(VERIFY))
from audit_axioms import parse as parse_axioms
PROPOSAL_SHA='93bf0bb15dc359e82d515f0dcd9ca3904428b4f5ffefae99b705ba5c1ba04561'
QUALIFIER_SHA='3fb5241d60f619b0b9e7be287b38d4c5c6fe5a7792a52e1dca50c717d88e9836'
SELF_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def enc(s):return json.dumps(s,ensure_ascii=False)
parser=argparse.ArgumentParser()
parser.add_argument('--root-approval-file',required=True)
parser.add_argument('--root-approval-sha256',required=True)
args=parser.parse_args()
ap=Path(args.root_approval_file).resolve();assert ap.is_relative_to(VERIFY.resolve())
assert sha(ap)==args.root_approval_sha256
a=json.loads(ap.read_text(encoding='utf8'))
assert a['status']=='ROOT_APPROVED_NARROW_DMS_V4_COMPOSITE_SUPPLEMENT_CANONICAL_INCORPORATION'
assert a['incorporation_helper_sha256']==SELF_SHA and a['proposal_sha256']==PROPOSAL_SHA
assert a['qualification_helper_sha256']==QUALIFIER_SHA
assert sha(VERIFY/'qualify_dms_v4_supplement_composite.py')==QUALIFIER_SHA
pp=VERIFY/'proposals/dms-v4-composite-supplement-narrow-editorial-proposal-20261005.json';assert sha(pp)==PROPOSAL_SHA
p=json.loads(pp.read_text(encoding='utf8'))
qp=Path(a['qualification_file']).resolve();assert qp.is_relative_to(VERIFY.resolve())
assert sha(qp)==a['qualification_sha256']
q=json.loads(qp.read_text(encoding='utf8'))
assert q['qualified'] is True and q['qualification_helper_sha256']==QUALIFIER_SHA
assert q['status'] in p['future_template_render_gate']['allowed_actual_statuses']
assert q['source_plan_sha256']=='30f7b071fbcd9ddb37e48a059126daf8e37dd65dae9b2733614af926589a7308'
assert q['new_V4_cold_source_passes']==7
assert q['prior_own_original_cold_source_outputs_reused_readonly99']==99
assert q['prior_V3_new_own_cold_source_passes_reused_linked122']==122
assert q['actual_unique_print_count']==q['requested_endpoint_count']==123
assert len(set(q['new_actual_source_module_names']))==7
assert set(q['new_actual_source_module_names'])==set(q['required_new7_module_names'])=={'InflationA','InflationB','InflationC','InflationD','InflationE','Inflation','All'}
assert q['current_pinned_compiler_executable_sha256']=='af49bacfabaa1fea71332ca0feae0fa1a60912219d5902291adc79f905bffb8d'
assert q['existing_V1_copy99_readonly_inputs_and_original_V2_V1_V3_protected99_linkcount2_preservation'] is True
for key in p['future_template_render_gate']['must_have_empty']:assert not q[key],key
assert sha(q['final_source_receipt'])==q['final_source_receipt_sha256']
for key in ['original119','failed_v1','failed_v2','failed_v3']:
    identity=p['current_evidence'][key];assert sha(identity['file'])==identity['sha256']
for preserved in p['preserved_predecessors'].values():assert sha(preserved['file'])==preserved['sha256']
assert sha(VERIFY/'audit_axioms.py')==q['axiom_parser_sha256']
assert sha(VERIFY/'runtimes/lean-4.33.1-windows/bin/lean.exe')==q['current_pinned_compiler_executable_sha256']
stage=(VERIFY/'builds/htpeo-dms-current-import-pruned-v4-vector').resolve()
plan_file=stage/'build-plan.json';assert sha(plan_file)==q['source_plan_sha256']
frozen_plan=json.loads(plan_file.read_text(encoding='utf8'))
for source in frozen_plan['modules']:assert sha(source['file'])==source['sha256']
for artifact in q['current7_V4_artifact_hashes']:
    path=Path(artifact['file']).resolve();assert path.is_relative_to(stage)
    assert sha(path)==artifact['sha256'] and path.stat().st_size==artifact['bytes']
for invocation in q['actual7_V4_source_CLI_guard_raw_log_identities']:
    for channel in invocation['current_raw_logs']:
        path=Path(channel['file']).resolve();assert path.is_relative_to((VERIFY/'guarded-source-logs').resolve())
        assert sha(path)==channel['sha256'] and path.stat().st_size==channel['bytes']
# The actual original120/123 exit1 remains an independent preserved input defect.
assert q['final_source_receipt_sha256']=='fb428dd280da30ba25480be5420157dfa7bbeb268c603b05edb0a17dd9eeb7ba'
assert sha(q['organizer_supplemental_audit_receipt'])==q['organizer_supplemental_audit_receipt_sha256']
assert q['original120_axiom_classes_and_sets_match_successful_supplement'] is True
original_audit=q['frozen_original_audit_exit1_120of123_fully_preserved']
assert original_audit['original_source_receipt_sha256']==q['final_source_receipt_sha256']
assert len(original_audit['parsed120'])==120 and len(original_audit['actual_raw_audit_receipt'])==1
assert original_audit['missing_exact3']==['Star6.colourable_of_dms_cubic','Star6.dms_iff_cubic16','Star6.leaf_of_dms']
original_raw=original_audit['actual_raw_audit_receipt'][0];assert original_raw['actual_exit']==1
original_row=original_raw['actual_row'];assert original_row['exit']==1 and original_row.get('stop_reason') is None
for channel in ['stdout','stderr']:
    guard=original_row['own_job_resource_receipt'];path=Path(guard[channel+'_file']).resolve()
    assert path.is_relative_to((VERIFY/'guarded-source-logs').resolve())
    content=path.read_bytes();assert hashlib.sha256(content).hexdigest()==guard[channel+'_sha256']
    assert content==original_row[channel].encode('utf8')==original_raw['actual_'+channel].encode('utf8')
assert parse_axioms(original_raw['actual_stdout'])==original_audit['parsed120']
supplement=stage/'FreshAuditSupplement.lean'
assert sha(supplement)=='0496d62e6a5cc83f98a73fc0c534eaa0469b1f9cd28f5e13f0fe9cbc1dcd0001'
assert supplement.read_bytes()==b'import Star6Equiv\n'+(stage/'FreshAudit1.lean').read_bytes()
# Reparse every selected actual raw output and compare all123 endpoint classifications.
parsed=[]
for audit in q['actual_raw_print_receipts']:
    row=audit['actual_row'];guard=row['own_job_resource_receipt']
    assert audit['actual_exit']==row['exit']==0 and row.get('stop_reason') is None
    for channel in ['stdout','stderr']:
        file=Path(guard[channel+'_file']).resolve();assert file.is_relative_to((VERIFY/'guarded-source-logs').resolve())
        raw=file.read_bytes();assert hashlib.sha256(raw).hexdigest()==guard[channel+'_sha256']
        assert raw==row[channel].encode('utf8')==audit['actual_'+channel].encode('utf8')
    parsed+=parse_axioms(audit['actual_stdout'])
assert parsed==q['selected123_actual_axiom_classifications']
assert len(parsed)==len({r['endpoint'] for r in parsed})==123
counts=dict(Counter(r['classification'] for r in parsed));assert counts==q['selected_classification_counts']
allowed={'AXIOM_FREE','STANDARD_KERNEL_AXIOMS','NATIVE_EVALUATION_TRUST'}
assert set(counts)<=allowed
standard=counts.get('STANDARD_KERNEL_AXIOMS',0);free=counts.get('AXIOM_FREE',0);native=counts.get('NATIVE_EVALUATION_TRUST',0)
assert standard+free+native==123 and native==len(q['selected_native_trust'])
sentence=f'{standard} use standard kernel axioms, {free} are axiom-free, and {native} depend on recognized native evaluation trust; none contain selected admissions or unrecognized axioms.'
if native:
    sentence+=' The native outputs rely on the pinned evaluator, compiler and runtime and are disclosed separately from standard kernel proof dependencies.'
else:
    sentence+=' No selected endpoint uses native evaluation trust.'
target=p['single_existing_paragraph_target']
after=target['qualified_replacement_template_NOT_ACTUAL_COMPLETION'].replace('{actual_trust_classification_sentence}',sentence)
assert '{actual_' not in after
paths={n:BASE/n for n in ['novel_results_content.json','novel_proof_expansions.json','novel_proof_coverage_2026-10-04.json','nonnovel_paper_content.txt','nonnovel_source_status_inventory.json']}
raw={n:f.read_bytes() for n,f in paths.items()};before={n:hashlib.sha256(v).hexdigest() for n,v in raw.items()}
assert before==a['current_canonical_sha256'],'Current canonical versions need separate exact root approval'
base=json.loads(raw['novel_results_content.json']);exp=json.loads(raw['novel_proof_expansions.json'])
expected_base=copy.deepcopy(base);expected_exp=copy.deepcopy(exp)
fi=next(i for i,f in enumerate(base['families']) if f['id']=='DMS');family=base['families'][fi]
si=target['section_index'];pi=target['paragraph_index']
assert family['category']=='original_candidate' and family['sections'][si]['heading']==target['section_heading']
assert family['sections'][si]['paragraphs'][pi]==target['before']
assert 'fresh_verification' not in family and 'fresh_verification' not in exp['families']['DMS']
meta={
 'status':q['status'],'qualification_record':'Verification/'+qp.name,'qualification_record_sha256':sha(qp),
 'qualification_helper_sha256':QUALIFIER_SHA,'actual_source_receipt_sha256':q['final_source_receipt_sha256'],
 'route':'htpeo-dms-current-import-pruned-v4-vector-with-organizer-only-supplement','source_plan_sha256':q['source_plan_sha256'],
 'unchanged_scientific_source_bodies':228,'header_only_modified_sources':4,
 'only_additional_V3_to_V4_header_source':'InflationA','only_additional_provider':'Mathlib.Data.Fin.VecNotation',
 'actual_new_V4_cold_source_invocations_passed':7,'previous_own_cold_source_outputs_separately_reused':221,
 'previous_original_own_readonly_V1_copy_inputs':99,'previous_V3_new_own_unaffected_passes':122,
 'frozen_original_organizer_audit_exit':1,'frozen_original_organizer_audit_prints':120,'frozen_original_organizer_audit_requests':123,
 'frozen_original_missing3':['Star6.colourable_of_dms_cubic','Star6.dms_iff_cubic16','Star6.leaf_of_dms'],
 'supplemental_organizer_audit_record_sha256':q['organizer_supplemental_audit_receipt_sha256'],
 'supplemental_organizer_audit_source_sha256':'0496d62e6a5cc83f98a73fc0c534eaa0469b1f9cd28f5e13f0fe9cbc1dcd0001',
 'supplemental_change':'Only import Star6Equiv added to separate organizer audit; original123 requests and all228 scientific bodies/options unchanged.',
 'original120_classifications_and_axiom_sets_match_supplement':True,
 'actual_selected_unique_endpoint_prints':123,'selected_standard_kernel_outputs':standard,
 'selected_axiom_free_outputs':free,'selected_native_evaluation_outputs':native,
 'actual_selected_endpoint_classifications':parsed,'native_trust_disclosure':q['native_trust_qualification'],
 'original_fresh_verification':copy.deepcopy(p['additive_metadata_recommendation_not_applied']['original_fresh_verification']),
 'original119_V1_V2_V3_receipt_sha256':{k:p['current_evidence'][k]['sha256'] for k in ['original119','failed_v1','failed_v2','failed_v3']},
 'original_frozen_route_complete':False,'body_identical_import_only_route_qualified':True,
 'five_open_structural_hypotheses':['FEEXTD10','FEEXISTD10','POLE','TDTRI','IID'],
 'finite_refinements_do_not_prove_infinite_instances':['FEEXISTD18','IID16'],
 'competition_p':0.15,'score_novelty_priority_or_placement_upgrade_implied':False,
 'scope':'Qualified composite route: 228 identical scientific bodies, 99 original-owned inputs, 122 previous V3-owned passes and seven new V4 sources. Original organizer audit exit1 with120/123 remains preserved; separate organizer-only same123 supplement completes selected auditing. General DMS remains unproved; competition p=.15 retained.'
}
expected_base['families'][fi]['sections'][si]['paragraphs'][pi]=after
expected_base['families'][fi]['fresh_verification']=meta
expected_exp['families']['DMS']['fresh_verification']=copy.deepcopy(meta)
def append_member(text,start,key,value):
    obj,length=json.JSONDecoder().raw_decode(text[start:]);end=start+length
    assert key not in obj and text[end-1]=='}'
    content=text[start:end-1];pos=start+len(content.rstrip())
    line=content.splitlines()[1];indent=line[:len(line)-len(line.lstrip())]
    addition=',\n'+indent+enc(key)+': '+json.dumps(value,ensure_ascii=False,indent=2).replace('\n','\n'+indent)
    return text[:pos]+addition+text[pos:]
base_text=raw['novel_results_content.json'].decode('utf8');token=enc(target['before']);assert base_text.count(token)==1
base_text=base_text.replace(token,enc(after),1)
pos=base_text.index('"id": "DMS"');start=base_text.rfind('{',0,pos)
assert json.JSONDecoder().raw_decode(base_text[start:])[0]['id']=='DMS'
base_text=append_member(base_text,start,'fresh_verification',meta)
exp_text=raw['novel_proof_expansions.json'].decode('utf8');pos=exp_text.index('"DMS":');start=exp_text.index('{',pos)
exp_text=append_member(exp_text,start,'fresh_verification',meta)
updates={'novel_results_content.json':base_text.encode('utf8'),'novel_proof_expansions.json':exp_text.encode('utf8')}
assert json.loads(updates['novel_results_content.json'])==expected_base
assert json.loads(updates['novel_proof_expansions.json'])==expected_exp
assert expected_base['families'][fi]['formal_endpoints']==family['formal_endpoints']
assert expected_base['families'][fi]['source_claim_card']==family['source_claim_card']
assert expected_base['families'][fi].get('source_claim_card_context')==family.get('source_claim_card_context')
# Exact before snapshots are reversible and only created after both root/qualification gates.
snapdir=BASE/'dms_completion_canonical_snapshots';snapdir.mkdir(exist_ok=True);snapshots=[]
for n,old in raw.items():
    sp=snapdir/(Path(n).stem+'.before.'+before[n]+'.json')
    if sp.exists():assert sp.read_bytes()==old
    else:
        with sp.open('xb') as stream:stream.write(old)
    snapshots.append({'file':str(sp),'sha256':sha(sp),'canonical':n})
assert {n:f.read_bytes() for n,f in paths.items()}==raw
for n,new in updates.items():
    temp=paths[n].with_name(paths[n].name+'.dms-incorporation.tmp')
    with temp.open('xb') as stream:stream.write(new)
    assert paths[n].read_bytes()==raw[n];os.replace(temp,paths[n])
for protected in ['novel_proof_coverage_2026-10-04.json','nonnovel_paper_content.txt','nonnovel_source_status_inventory.json']:assert paths[protected].read_bytes()==raw[protected]
record={'status':'APPLIED_ROOT_APPROVED_ACTUAL_DMS_V4_COMPOSITE_7_NEW221_PRIOR_SUPPLEMENT123_SCOPE_ONLY',
 'updated_utc':datetime.now(timezone.utc).isoformat(),'root_approval':str(ap),'root_approval_sha256':sha(ap),
 'incorporation_helper_sha256':SELF_SHA,'qualification':str(qp),'qualification_sha256':sha(qp),
 'proposal_sha256':PROPOSAL_SHA,'before_canonical_sha256':before,
 'after_canonical_sha256':{n:sha(f) for n,f in paths.items()},'preserved_before_versions':snapshots,
 'single_DMS_existing_paragraph_changed':{'before':target['before'],'after':after},
 'actual_selected_classification_counts':counts,'7_actual99_original122_V3_prior_source_scope_separated':True,
 'only_additive_DMS_family_and_expansion_fresh_verification_metadata':True,
 'all_other_families_source_cards_formal_endpoints_ordinary_prose_coverage_bytes_unchanged':True,
 'five_open_hypotheses_and_p_15_preserved':True,'source_compilation_or_PDF_regeneration_performed':False}
out=VERIFY/'dms-v4-composite-supplement-actual-qualified-narrow-incorporation-20261005.json'
with out.open('x',encoding='utf8',newline='\n') as stream:json.dump(record,stream,ensure_ascii=False,indent=2);stream.write('\n')
print(json.dumps({'record':str(out),'sha256':sha(out),'after_canonical_sha256':record['after_canonical_sha256']}))
