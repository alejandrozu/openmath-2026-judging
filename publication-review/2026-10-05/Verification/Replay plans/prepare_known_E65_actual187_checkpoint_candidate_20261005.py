"""Prepare only exact checkpoint prose/appendix candidates; never apply or render."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import json, hashlib, difflib, os
BASE=Path(__file__).resolve().parent.parent;VER=BASE/'verification'
OUT=VER/'proposals/known-E65-actual187-completed-checkpoint-wording-20261005'
OUT.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_once(p,data):
    with p.open('xb') as f:f.write(data);f.flush();os.fsync(f.fileno())
prose=BASE/'nonnovel_paper_content.txt';inventory=BASE/'nonnovel_source_status_inventory.json'
prose_sha='5e0ce91a43c53269408b7b4f295436cd4b1ddb7dc9e64305e2d44bbbe839b341'
inventory_sha='7e43ea4b74b4e7e8eafa2079fc97f8a02af54272c59288b6bac576e9eb82186a'
actual_path=VER/'original-E65-actual187-natural-memory-wait-boundary-immutable-20261005.json'
actual_sha='34c04a3ef0599486ed4f2396dd7d96f1a2cefea73472ba8ec0d0031f6ab46acb'
review_path=VER/'root-original-E65-actual187-natural-boundary-reviewed-sole-slot-returned-20261005.json'
review_sha='9aa2fd1a05d523839b61d305bf57045943467cd4d1e7613ab8172a596daf22bf'
for p,h in [(prose,prose_sha),(inventory,inventory_sha),(actual_path,actual_sha),(review_path,review_sha)]:assert sha(p)==h
actual=json.loads(actual_path.read_bytes());review=json.loads(review_path.read_bytes())
assert review['status']=='ROOT_QUALIFIED_ACTUAL_E65_187_SOURCE_NATURAL_CHECKPOINT_AND_SOLE_SLOT_RETURN'
assert review['actual_finished_receipt_sha256']==actual_sha
assert actual['status']=='SCHEDULED_RESOURCE_CHECKPOINT' and actual['finished_utc']=='2026-10-05T07:05:52Z'
assert actual['checkpoint_reason']=='THIRD_WORKER_LEASE_HANDOFF_WHILE_WAITING_WITHOUT_COMPILER'
modules={m['module']:m for m in actual['modules']}
ok={r['module'] for r in actual['builds'] if r.get('exit')==0 and not r.get('stop_reason') and r['module'] in modules}
assert len(ok)==187 and Counter(modules[n]['source_class'] for n in ok)=={'RECOVERED_ORIGINAL_FC_SOURCE':187}
assert not any(r.get('is_endpoint_audit') for r in actual['builds']) and not actual['selected_audit_axiom_review']
assert review['granular_source_successes']==183 and review['whole_source_successes']==4
assert review['no_source_child_terminated'] is True and review['full_project_or_novelty_or_score_upgrade'] is False
assert review['retained_waiting_label_is_unattempted_no_active_Lean']=='FormalConjecturesForMathlib.Data.Nat.PerfectPower'
assert not actual.get('current_module')
for p in [prose,inventory]:write_once(OUT/(sha(p)+p.suffix),p.read_bytes())
old1='The six FC-dependent companion modules, the organizer\'s Set/cardinality/Filter bridge and the original recovered-image proof replay have not run. This partial audit confers no original-novelty score or full-project PASS.'
old2='No independent original proof replay has run at this checkpoint.'
after1=('The isolated Windows replay of the recovered original dependency bytes reached a completed checkpoint at 07:05:52 UTC on 5 October 2026, with 187/199 own source modules checked: 183 granular modules and four whole-resource modules. All 187 successes are recovered FC dependency-library modules. Six further FC modules and the six FC-dependent entrant modules remain pending, together with their six organizer audits and 42 current selected outputs. The earlier exact Std one-source/14-print witness remains separately accepted; the final 200-body/56-output evidence composition has not been qualified. The retained PerfectPower waiting label is an unattempted source, with no active E65 Lean process. This is partial dependency execution and known-mathematics verification, with no full-project PASS, new originality score or unconditional reciprocal-divergence theorem.')
after2=('Independent checking of the recovered bytes has therefore begun in the separate Windows source route, with the completed partial checkpoint recorded above. The original Linux container was not executed by this review. FC sources use explicit pp.unicode.fun=true, autoImplicit=false and relaxedAutoImplicit=false; historical author invocation options remain unverified. The checkpoint establishes neither the unrun selected FC-dependent theorems nor axiom cleanliness of all unselected dependency theorems.')
before=prose.read_text(encoding='utf8');assert before.count(old1)==before.count(old2)==1
after=before.replace(old1,after1).replace(old2,after2)
candidate=OUT/'nonnovel_paper_content.actual187-checkpoint.UNAPPLIED-candidate.txt'
write_once(candidate,after.encode('utf8'))
diff=OUT/'actual187-checkpoint-two-clause-only.diff'
write_once(diff,''.join(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),fromfile='nonnovel_paper_content.frozen5e0ce91a',tofile='nonnovel_paper_content.actual187-checkpoint-candidate')).encode('utf8'))
data=json.loads(inventory.read_bytes());rows={r['id']:r for r in data['rows']}
old_elementary='The six FC-dependent modules, organizer Set/cardinality/Filter bridge and original recovered-image proof replay remain unrun. This is partial known-mathematics verification, not full-project PASS or an original reciprocal-divergence result.'
assert rows['E65-ELEMENTARY']['formal_status_record'].count(old_elementary)==1
new_status={
 'E65-DYADIC':('The completed exact recovered-source Windows checkpoint at 07:05:52 UTC on 5 October 2026 checked 187 dependency-library modules: 183 granular and four whole-resource. Six remaining FC dependency modules and the six FC-dependent entrant modules, including the dyadic endpoint, are still pending; no current FC-dependent organizer audit or selected output has run. The separate earlier exact Std one-source/14-print witness is accepted for possible later evidence composition. The final 200-body/56-output composite is not qualified. Historical author logs and the answer(sorry) statement-wrapper caveat are retained. No full-project PASS or originality score is conferred.'),
 'E65-THREE':rows['E65-THREE']['formal_status_record']+' The independently reviewed completed checkpoint at 07:05:52 UTC on 5 October 2026 contains 187 recovered FC dependency source successes (183 granular plus four whole), with the six FC-dependent entrant modules and six current audits/42 selected outputs still pending. It does not certify those unrun conditional endpoints or discharge their analytic premises; the prior exact Std one-source/14-print witness remains separate.',
 'E65-ELEMENTARY':rows['E65-ELEMENTARY']['formal_status_record'].replace(old_elementary,
     'The recovered-source Windows replay separately reached a completed checkpoint at 07:05:52 UTC on 5 October 2026 with 187 FC dependency-library modules checked (183 granular plus four whole). Six further FC modules and all six FC-dependent entrant modules, including the organizer Set/cardinality/Filter bridge, remain pending; zero of their six current audits/42 selected outputs have run. The exact prior Std one-source/14-print witness is separately accepted, but a 200-body/56-output final composition is not qualified. This is partial known-mathematics verification, with no full-project PASS, original-container execution or new reciprocal-divergence result.')}
field_changes=[]
for identifier in ['E65-DYADIC','E65-THREE','E65-ELEMENTARY']:
    row=rows[identifier];old=row['formal_status_record']
    assert 'archived_pre_original187_checkpoint_formal_status_record' not in row
    row['archived_pre_original187_checkpoint_formal_status_record']=old
    row['formal_status_record']=new_status[identifier]
    row['current_original_source_replay_checkpoint_reference']='current_original_E65_source_replay_checkpoint'
    field_changes.append({'id':identifier,'field':'formal_status_record','exact_before':old,'after':new_status[identifier]})
overlay={
 'status':'ROOT_QUALIFIED_PARTIAL_RECOVERED_SOURCE_CHECKPOINT_NOT_SELECTED_THEOREM_OR_COMPOSITE_COMPLETION',
 'actual_finished_utc':actual['finished_utc'],'actual_receipt_basename':actual_path.name,'actual_receipt_sha256':actual_sha,
 'root_review_basename':review_path.name,'root_review_sha256':review_sha,
 'source_plan_sha256':actual['source_plan_sha256'],'runner_sha256':'a2e5931c838e8b348de9fae4945b9f16ceb0883eaed51ca55f93e797deaa9e6d',
 'own_source_successes':187,'granular_source_successes':183,'whole_resource_source_successes':4,
 'compiled_source_class_counts':{'RECOVERED_ORIGINAL_FC_SOURCE':187,'EXACT_FROZEN_ENTRANT_SOURCE':0},
 'remaining_FC_sources':6,'remaining_FC_dependent_entrant_sources':6,
 'own_route_source_scope_total_excluding_external_Std':199,'current_organizer_audits_passed':0,'current_selected_outputs_passed':0,
 'pending_current_audits':6,'pending_current_selected_outputs':42,
 'separate_previous_Std_source_count':1,'separate_previous_Std_selected_outputs':14,
 'separate_Std_evidence_only_root_acceptance_sha256':'5fcee11b0573d3187ef9fb37de9de8663a4ae2f2a94e76b3ac6bd0e5e48dc9eb',
 'final_200_source56_output_composition_qualified':False,'full_project_PASS':False,
 'original_container_executed_by_this_review':False,'original_FC_whole_Git_revision_verified':False,
 'historical_author_invocation_options_verified':False,
 'FC_replay_explicit_options':{'pp.unicode.fun':True,'autoImplicit':False,'relaxedAutoImplicit':False},
 'all193_unselected_theorems_axiom_clean_claimed':False,
 'retained_unattempted_waiting_label':'FormalConjecturesForMathlib.Data.Nat.PerfectPower',
 'no_active_E65_Lean_at_reviewed_boundary':True,'no_source_child_terminated':True,
 'novelty_score_M2_award_or_open_AP_claim_upgraded':False,
 'historical_nested_records_retained_exact':['original_environment_provenance','fresh_Std_partial_replay','archived_pre_fresh_Std_formal_status_record'],
 'history_policy':'Earlier source recovery and Std-only nested records retain their dated false flags. This current overlay updates only the later completed dependency replay; the conditional AP hypotheses and statement-fidelity caveats are unchanged.'}
assert 'current_original_E65_source_replay_checkpoint' not in data
data['current_original_E65_source_replay_checkpoint']=overlay
inventory_candidate=OUT/'nonnovel_source_status_inventory.actual187-checkpoint.UNAPPLIED-candidate.json'
new_inventory=json.dumps(data,ensure_ascii=False,indent=2)
write_once(inventory_candidate,new_inventory.encode('utf8'))
inventory_diff=OUT/'actual187-checkpoint-three-visible-fields-current-overlay-only.diff'
write_once(inventory_diff,''.join(difflib.unified_diff(inventory.read_text(encoding='utf8').splitlines(keepends=True),new_inventory.splitlines(keepends=True),fromfile='nonnovel_source_status_inventory.frozen7e43ea4',tofile='nonnovel_source_status_inventory.actual187-checkpoint-candidate')).encode('utf8'))
# Verify every other row, every historical object, all claims/affiliations and source fields remain exact.
prior=json.loads(inventory.read_bytes())
for old in prior['rows']:
    new=rows[old['id']]
    if old['id'] not in new_status:assert old==new
    else:
        for key,value in old.items():
            if key!='formal_status_record':assert new[key]==value
assert data['row_count']==119 and len(data['rows'])==119
write_once(OUT/'exact-three-field-before-after.json',json.dumps(field_changes,ensure_ascii=False,indent=2).encode('utf8'))
future_final=VER/'proposals/known-E65-final-or-checkpoint-wording-20261005/nonnovel_paper_content.final-completion.UNAPPLIED-candidate.txt'
assert sha(future_final)=='7b37d2159492e40409c2053f52116fa0f60d9421315317dd6e4f49cb194a4648'
packet={
 'status':'PREPARED_ACTUAL_COMPLETED187_CHECKPOINT_WORDING_ONLY_NOT_APPLIED_OR_RENDERED',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'original_prose_sha256':prose_sha,'original_inventory_sha256':inventory_sha,
 'actual_completed_receipt_sha256':actual_sha,'root_actual187_review_sha256':review_sha,
 'prose_candidate':str(candidate),'prose_candidate_sha256':sha(candidate),'prose_diff':str(diff),'prose_diff_sha256':sha(diff),
 'inventory_candidate':str(inventory_candidate),'inventory_candidate_sha256':sha(inventory_candidate),
 'inventory_diff':str(inventory_diff),'inventory_diff_sha256':sha(inventory_diff),
 'exact_replacements':[{'line':185,'exact_before':old1,'after':after1},{'line':189,'exact_before':old2,'after':after2}],
 'visible_appendix_fields':field_changes,'current_evidence_overlay':overlay,
 'interpretation':'All187 current source successes are recovered FC dependencies, not the six FC-dependent entrant theorem modules. Zero current42 prints have run. Earlier Std1/14 is separate accepted evidence, with no200/56 composition qualified.',
 'application_preflight_required':{'root_editorial_approval':True,'current_prose_equals_frozen_SHA':prose_sha,
   'current_inventory_equals_frozen_SHA':inventory_sha,'actual_checkpoint_equals_SHA':actual_sha,'root_review_equals_SHA':review_sha},
 'future_final_candidate_unchanged_and_unapplied_sha256':sha(future_final),
 'actual_operations':{'qualifier_executions':0,'Lean':0,'aliases':0,'canonical_edits':0,'PDF_rendering':0},
 'all_current_source_and_canonical_inputs_unchanged':sha(prose)==prose_sha and sha(inventory)==inventory_sha and sha(actual_path)==actual_sha and sha(review_path)==review_sha}
packet_path=OUT/'root-review-packet.json';write_once(packet_path,json.dumps(packet,ensure_ascii=False,indent=2).encode('utf8'))
print(json.dumps({'packet':str(packet_path),'packet_sha256':sha(packet_path),'prose_candidate_sha256':sha(candidate),
 'prose_diff_sha256':sha(diff),'inventory_candidate_sha256':sha(inventory_candidate),'inventory_diff_sha256':sha(inventory_diff),
 'source_successes':187,'all_dependencies':True,'current_selected_outputs':0,'no_apply':True},ensure_ascii=False))
