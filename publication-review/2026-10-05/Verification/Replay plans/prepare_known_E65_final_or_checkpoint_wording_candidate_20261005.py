"""Prepare unapplied E65 prose/appendix patches with future qualification gates."""
from pathlib import Path
from datetime import datetime, timezone
import sys, json, hashlib, difflib, os
BASE=Path(__file__).resolve().parent.parent; VER=BASE/'verification'
sys.path.insert(0,str(VER))
from receipt_io import read_bytes_shared
OUT=VER/'proposals/known-E65-final-or-checkpoint-wording-20261005'
OUT.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_once(p,data):
    with p.open('xb') as f:f.write(data);f.flush();os.fsync(f.fileno())
prose=BASE/'nonnovel_paper_content.txt'; inventory=BASE/'nonnovel_source_status_inventory.json'
prose_sha='5e0ce91a43c53269408b7b4f295436cd4b1ddb7dc9e64305e2d44bbbe839b341'
inventory_sha='7e43ea4b74b4e7e8eafa2079fc97f8a02af54272c59288b6bac576e9eb82186a'
assert sha(prose)==prose_sha and sha(inventory)==inventory_sha
for p in [prose,inventory]:write_once(OUT/(sha(p)+p.suffix),p.read_bytes())
original=prose.read_text(encoding='utf8')
old1='The six FC-dependent companion modules, the organizer\'s Set/cardinality/Filter bridge and the original recovered-image proof replay have not run. This partial audit confers no original-novelty score or full-project PASS.'
old2='No independent original proof replay has run at this checkpoint.'
assert original.count(old1)==original.count(old2)==1
final1=('The six FC-dependent companion modules and their six selected organizer audits have now been checked in an isolated Windows source replay using the recovered original dependency bytes, Lean 4.33.1 and the nine pinned official packages. A separate SHA-bound final qualification composes 199 actual own source checks and 42 current selected outputs with the previously accepted exact Std one-source/14-print witness, giving coverage of 200 distinct source bodies and 56 selected outputs. The Std outputs remain in their original route, with no copied or aliased outputs and no invented new invocation. This certifies the selected formalization scope; the three-term analytic inputs remain hypotheses, the k≥4 equivalence does not prove either side, and no original-novelty score or solution of the reciprocal-divergence conjecture follows.')
final2=('The later Windows source-based verification is separately qualified through the 199-own-source/42-current-output route and the accepted previous Std one-source/14-print witness. The original Linux container was not executed. Recovered FC sources use explicit pp.unicode.fun=true, autoImplicit=false and relaxedAutoImplicit=false; the historical author invocation remains unverified. Selected endpoint checking does not certify every unselected theorem in the 193-module dependency library.')
final_text=original.replace(old1,final1).replace(old2,final2)
final_path=OUT/'nonnovel_paper_content.final-completion.UNAPPLIED-candidate.txt'
write_once(final_path,final_text.encode('utf8'))
final_diff=OUT/'final-completion-two-clause-only.diff'
write_once(final_diff,''.join(difflib.unified_diff(original.splitlines(keepends=True),final_text.splitlines(keepends=True),fromfile='nonnovel_paper_content.frozen5e0ce91a',tofile='nonnovel_paper_content.future-final-qualified')).encode('utf8'))

live_path=VER/'sundai-erdos3-original-image-source-fresh-build.json'
live_raw=read_bytes_shared(live_path); live_sha=hashlib.sha256(live_raw).hexdigest(); live=json.loads(live_raw)
stamp=datetime.now(timezone.utc).isoformat()
source_names={m['module'] for m in live['modules']}
success=[r for r in live['builds'] if r.get('exit')==0 and not r.get('stop_reason')]
source_passes={r['module'] for r in success if r['module'] in source_names}
scope=json.loads((VER/'original-E65-tactic-aware-resource-scope-20261005.json').read_bytes())
safe=set(scope['truly_no_Tactic_topological_order']); whole=set(scope['future_whole_resource_sources'])
assert len(safe)==183 and len(whole)==16 and source_passes<=safe|whole
audits=[r for r in success if r.get('is_endpoint_audit')]
prints=live.get('selected_audit_axiom_review',[])
assert len({r['endpoint'] for r in prints})==len(prints)
counts={'own_source_successes':len(source_passes),'safe_successes':len(source_passes&safe),'whole_successes':len(source_passes&whole),
        'successful_current_organizer_audits':len(audits),'successful_current_selected_prints':len(prints)}
snapshot=OUT/(live_sha+'.json');write_once(snapshot,live_raw)
partial_template=('At {checkpoint_utc}, the exact recovered-source Windows replay had completed {own_source_successes}/199 own source modules: {safe_successes}/183 safe granular modules and {whole_successes}/16 whole-resource modules. It had completed {successful_current_organizer_audits}/6 FC-dependent organizer audits and {successful_current_selected_prints}/42 current selected outputs. Its status was {actual_receipt_status}; the active or unfinished invocation and any resource stop are preserved in the dated receipt. The earlier exact Std one-source/14-print witness remains separately accepted for evidence composition. A final 200-body/56-output composition has not been qualified at this checkpoint. The analytic premises and full Erdős3 claim remain open, and this partial record confers no new originality score.')
partial_values={**counts,'checkpoint_utc':stamp,'actual_receipt_status':live['status']}
partial1=partial_template.format(**partial_values)
partial2=('A source-based Windows replay has therefore begun; its dated partial counts are recorded above. The original Linux container has not been executed, the deleted whole FC Git revision remains unidentified, and historical author invocation options are unverified. The current partial source receipt and the earlier accepted Std witness remain separate.')
partial_text=original.replace(old1,partial1).replace(old2,partial2)
partial_path=OUT/'nonnovel_paper_content.dated-partial-example.UNAPPLIED-candidate.txt'
write_once(partial_path,partial_text.encode('utf8'))
partial_diff=OUT/'dated-partial-example-two-clause-only.diff'
write_once(partial_diff,''.join(difflib.unified_diff(original.splitlines(keepends=True),partial_text.splitlines(keepends=True),fromfile='nonnovel_paper_content.frozen5e0ce91a',tofile='nonnovel_paper_content.dated-partial-example-only')).encode('utf8'))

inv=json.loads(inventory.read_bytes())
rows=next(v for v in inv.values() if isinstance(v,list) and any(isinstance(r,dict) and r.get('id')=='E65-DYADIC' for r in v))
by_id={r['id']:r for r in rows}
elementary_old='The six FC-dependent modules, organizer Set/cardinality/Filter bridge and original recovered-image proof replay remain unrun. This is partial known-mathematics verification, not full-project PASS or an original reciprocal-divergence result.'
assert by_id['E65-ELEMENTARY']['formal_status_record'].count(elementary_old)==1
final_status={
 'E65-DYADIC':('A separately SHA-bound final qualification composes the exact recovered-source Windows route of 199 actual own source modules and 42 current selected outputs with the accepted prior Std one-source/14-print witness, covering all 200 distinct scientific bodies and 56 selected outputs. The dyadic equivalence is checked under its literal k≥4 hypotheses; neither equivalent assertion is thereby proved. The answer(sorry) statement wrapper remains subject to the separately described elaboration and statement-fidelity review. Original Linux-container execution and the deleted whole FC Git revision are not established. No original Erdős3 score or formal-library novelty award is implied.'),
 'E65-THREE':('The selected conditional three-term bridges are covered by the separately qualified 199-own-source/42-current-output route plus the accepted prior Std one-source/14-print witness. Analytic parameters remain explicit hypotheses; clean selected axiom output does not discharge Kelley–Meka, logarithmic-barrier or other density assumptions. This is source-based Windows verification of the preserved packet, with no original-container execution or new originality score.'),
 'E65-ELEMENTARY':by_id['E65-ELEMENTARY']['formal_status_record'].replace(elementary_old,
     'The six FC-dependent companion modules and their organizer Set/cardinality/Filter bridge checks are now included in the independently qualified recovered-source Windows scope. Its final evidence composition preserves 199 actual own-source/42-current-output checks and the separately accepted prior exact Std one-source/14-print witness, totaling 200 bodies/56 selected outputs. It preserves the intentionally partial original-route receipt and establishes no original-container execution or new reciprocal-divergence result.')}
changes=[]
for identifier in ['E65-DYADIC','E65-THREE','E65-ELEMENTARY']:
    row=by_id[identifier]
    changes.append({'id':identifier,'field':'formal_status_record','exact_before':row['formal_status_record'],
                    'future_final_after':final_status[identifier],
                    'dated_partial_example_after':row['formal_status_record'].replace('No fresh independent build.',partial1).replace(elementary_old,partial1)
                       if identifier!='E65-THREE' else row['formal_status_record']+' '+partial1,
                    'preserve_before_in_new_archived_pre_original_source_composite_formal_status_record':True})
patch_path=OUT/'E65-three-appendix-status-field-UNAPPLIED-patches.json'
write_once(patch_path,json.dumps({'changes':changes,
 'future_current_verification_field_from_actual_final_qualification':{
     'field':'current_original_source_replay_verification','entries':['E65-DYADIC','E65-THREE','E65-ELEMENTARY'],
     'actual_final_record_basename':'original-E65-composite199-42-plus-acceptedStd1-14-final-qualification-20261005.json',
     'actual_record_sha256':'ROOT_MUST_BIND_FUTURE_ACTUAL_RECORD_NO_CURRENT_PLACEHOLDER_ACCEPTANCE',
     'copy_fields_from_actual_qualification':['status','checked_utc','actual_original_source_receipt_sha256','actual_this_route_fresh_own_source_count','actual_granular_sources','actual_sole_whole_sources','actual_this_route_audit_files','actual_this_route_unique_selected_prints','accepted_previous_exact_Std_source_count','accepted_previous_Std_actual_unique_prints','composite_distinct_scientific_source_body_coverage','composite_unique_selected_print_coverage','original_container_executed','historical_author_invocation_options_verified','original_FC_whole_Git_revision','selected_correctness_scope','open_AP_claim_qualification'],
     'all193_unselected_clean_claim':False,'novelty_score_or_M2_award_upgraded':False},
 'historical_nested_objects_retained_exact':['original_environment_provenance','fresh_Std_partial_replay','archived_pre_fresh_Std_formal_status_record'],
 'historical_false_flags_policy':'These nested objects are dated evidence of the earlier recovery/Std-only check; do not rewrite their past false flags as if later work existed at capture. Add separate current SHA-bound verification metadata and current visible formal-status prose.',
 'auxiliary_metadata_policy':'known_companion_m2_fresh_scope_metadata_20261005.json and source-locked fidelity audit are dated historical records. Preserve them; if necessary add a current composite overlay referencing actual final qualification, rather than overwriting the earlier remaining-holds snapshot.'},ensure_ascii=False,indent=2).encode('utf8'))
qualifier=VER/'qualify_original_e65_composite_199plusStd.py'
qualifier_sha='2a33dca5490be72972a10e0af9e4091525f08910a82448d86a59d001998bb53b'
assert sha(qualifier)==qualifier_sha
packet={'status':'PREPARED_WORDING_AND_FIELD_PATCHES_ONLY_NO_APPLY_RENDER_OR_QUALIFICATION',
 'created_utc':stamp,'producer_sha256':sha(__file__),'original_prose_sha256':prose_sha,'original_inventory_sha256':inventory_sha,
 'final_prose_candidate':str(final_path),'final_prose_candidate_sha256':sha(final_path),'final_minimal_diff':str(final_diff),'final_minimal_diff_sha256':sha(final_diff),
 'partial_example_candidate':str(partial_path),'partial_example_candidate_sha256':sha(partial_path),'partial_minimal_diff':str(partial_diff),'partial_minimal_diff_sha256':sha(partial_diff),
 'inventory_patch_candidate':str(patch_path),'inventory_patch_candidate_sha256':sha(patch_path),
 'original_clauses':[{'line_at_frozen_source':185,'exact_before':old1,'final_after':final1},{'line_at_frozen_source':189,'exact_before':old2,'final_after':final2}],
 'final_application_gates':{
    'qualifier_source_sha256':qualifier_sha,
    'requires_actual_final_qualification_status':'QUALIFIED_EXACT_RECOVERED_199_OWN_SOURCE42_ENDPOINTS_WITH_SEPARATE_ACCEPTED_STD1_14_EVIDENCE',
    'requires_actual_final_qualification_SHA_and_root_editorial_review':True,
    'counts':{'fresh_own_sources':199,'current_selected_outputs':42,'previous_accepted_Std_sources':1,'previous_Std_outputs':14,'distinct_source_bodies':200,'selected_outputs':56},
    'not200_newly_cold_or7_new_audits':True,'original_container_executed_must_be_false':True,
    'historical_author_options_verified_must_be_false':True,'FC_whole_Git_unknown_retained':True,
    'all193_unselected_theorem_axioms_not_asserted_clean':True,'baseline_admissions_retained':True,
    'analytic_assumptions_and_macro_statement_fidelity_caveats_retained':True,
    'frozen_prose_inventory_SHA_match_required_before_atomic_future_application':True},
 'partial_fallback':{'template':partial_template,'dated_live_snapshot_file':str(snapshot),'dated_live_snapshot_sha256':live_sha,
     'captured_receipt_status':live['status'],'captured_current_module':live.get('current_module'),'captured_counts':counts,
     'captured_time':stamp,'current_live_snapshot_is_not_a_future_finished_checkpoint':True,
     'future_partial_application':'Re-read a genuinely finished resource/scheduling checkpoint, bind its exact SHA/timestamp and actual source/audit/print counts, then substitute this template. This live-count example may not be applied as a later held/final status.'},
 'changed_scope':'Two stale prose clauses and the three matching E65 visible appendix status fields, with a separate current qualification overlay. All other maths, author/affiliation prose and dated evidence remain exact.',
 'actual_operations':{'Lean':0,'aliases':0,'qualification_execution':0,'canonical_or_inventory_edits':0,'PDF_rendering':0},
 'source_helpers_and_canonical_unchanged':sha(prose)==prose_sha and sha(inventory)==inventory_sha and sha(qualifier)==qualifier_sha}
review=OUT/'root-review-packet.json';write_once(review,json.dumps(packet,ensure_ascii=False,indent=2).encode('utf8'))
print(json.dumps({'packet':str(review),'packet_sha256':sha(review),'final_candidate_sha256':sha(final_path),'final_diff_sha256':sha(final_diff),
 'inventory_patch_sha256':sha(patch_path),'live_snapshot_status':live['status'],'live_counts':counts,'no_apply':True},ensure_ascii=False))
