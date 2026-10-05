"""Preparation only; no final receipt read, no proof or qualification execution."""
from pathlib import Path
import hashlib,difflib,ast,json
BASE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
old=BASE/'qualify_dms_v3_complete_route.py'
text=old.read_text(encoding='utf8')
text=text.replace('The original scientific bodies are preserved.99 original-owned cold outputs linked only from proven V1 COPIES are\nexplicitly reused;129 body-identical diagnostic sources must have actual new\ncompilation rows.',
    'All228 scientific bodies/options/audits remain unchanged.99 original-owned passes\nare imported from proven V1 copies read-only,122 unaffected V3-new passes are\nlinked into V4, and seven affected sources must have actual new V4 rows.')
text=text.replace('from verify_dms_v3_stage import verify_stage','from verify_dms_v4_vector_stage import verify_stage')
text=text.replace('from dms_v3_copy99_hardlink_seed import verify_seed,preserved_check','from dms_v4_vector122_seed import verify_seed\nfrom dms_v3_copy99_hardlink_seed import preserved_check')
text=text.replace("PROJECT='htpeo-dms-current-import-pruned-v3'","PROJECT='htpeo-dms-current-import-pruned-v4-vector'")
text=text.replace("PLAN_SHA='eea74ffbc9321a0663d6c77d8e7c79ee7de3da914c9af1bc66e9b3ed3750f7ba'","PLAN_SHA='30f7b071fbcd9ddb37e48a059126daf8e37dd65dae9b2733614af926589a7308'")
text=text.replace("RUNNER_SHA='832e875054d76b597652a37edc197f47182253172581be1ab962b1ae6187ee3d'", "RUNNER_SHA="+repr(sha(BASE/'run_dms_v4_vector_plan.py')))
text=text.replace("POLICY_SHA='a4b795b071135118af94868726b9ac45af0579540d5856e9aaf7d48a9e3717e6'","POLICY_SHA='0af7feab4fc55f1b7ecade9b60491c2507ac3687d2899f0f74116afd40a93a8f'")
text=text.replace("SEED_SHA='a1395c3617d8c813048b0ecfb34be453c058636216659583090ad1defb771c83'", "# Actual future seed SHA must be explicitly reviewed in the root final approval.")
text=text.replace("VERIFIER_SHA='be19344e55bb6a50930bbd2b660385447cfe5fd721861f2fa6c4253094b927c5'","VERIFIER_SHA="+repr(sha(BASE/'verify_dms_v4_vector_stage.py')))
text=text.replace("SEED_HELPER_SHA='772423ad135bddde4487ff381bc39c4d2cf2a1022229943f37e4d7c03fadaa92'","SEED_HELPER_SHA="+repr(sha(BASE/'dms_v4_vector122_seed.py')))
text=text.replace("assert approved['status']=='ROOT_APPROVED_DMS_V3_FINAL_QUALIFICATION_READ_ONLY'","assert approved['status']=='ROOT_APPROVED_DMS_V4_FINAL_QUALIFICATION_READ_ONLY'\n    SEED_SHA=approved['reviewed_seed_receipt_sha256'];assert re.fullmatch('[0-9a-f]{64}',SEED_SHA)")
text=text.replace("run_dms_v3_linked_plan.py","run_dms_v4_vector_plan.py").replace("verify_dms_v3_stage.py","verify_dms_v4_vector_stage.py").replace("dms_v3_copy99_hardlink_seed.py","dms_v4_vector122_seed.py")
text=text.replace("assert receipt['runner_source_sha256']==RUNNER_SHA","assert receipt['resource_settings']['runner_source_sha256']==RUNNER_SHA\n    assert receipt['modules']==plan['modules'] and receipt.get('finished_utc'), 'Actual final scoped receipt required'")
text=text.replace("stage_identity=verify_stage(require_cold=False)","stage_identity=verify_stage(require_cold=False,linked122_allowed=True)")
text=text.replace("required=set(seed_identity['required129_new_cold_module_names'])\n    reused={r['module'] for r in seed_identity['modules']}\n    assert len(required)==129 and len(reused)==99 and required.isdisjoint(reused)",
    "required=set(seed_identity['required7_new_cold_module_names'])\n    reused=set(seed_identity['prior221_names'])\n    assert len(required)==7 and len(reused)==221 and required.isdisjoint(reused)")
text=text.replace("'original_scientific_and_scored_scope':'UNALTERED228_SCIENTIFIC_BODIES_AND123_ORIGINAL_ENDPOINTS;ONLY_THREE_IMPORT_HEADERS_CHANGED'",
    "'original_scientific_and_scored_scope':'UNALTERED228_SCIENTIFIC_BODIES_OPTIONS_COMMENTS_AND123_ORIGINAL_ENDPOINTS;ORIGINAL_THREE_IMPORT_HEADER_SPANS_PLUS_DIRECT_INFLATIONA_VECNOTATION_IMPORT'")
text=text.replace("'post_run99_v1_copy_V3_NTFS_identity_and_all_original_v2_sha':seed_identity", "'post_run221_readonly99_and_linked122_identity_and_all_original_V1_V2_V3_protection':seed_identity")
text=text.replace("'copy_source_only_reuse_and_original_v2_linkcount2_preservation':True", "'existing_V1_copy99_readonly_inputs_and_original_V2_V1_V3_protected99_linkcount2_preservation':True")
text=text.replace("'prior_own_original_cold_source_outputs_reused':99,'new_cold_source_passes':len(actual_pass)",
    "'prior_own_original_cold_source_outputs_reused_readonly99':99,'prior_V3_new_own_cold_source_passes_reused_linked122':122,'new_V4_cold_source_passes':len(actual_pass)")
text=text.replace("required_new129_module_names","required_new7_module_names").replace("current129_artifact_hashes","current7_V4_artifact_hashes").replace("actual129_source_CLI_guard_raw_log_identities","actual7_V4_source_CLI_guard_raw_log_identities")
text=text.replace("dms-v3-complete-route-final-qualification-20261005.json","dms-v4-vector-complete-route-final-qualification-20261005.json")
text=text.replace("'prior_owned_reused':99", "'prior_owned_reused':221")
new=BASE/'qualify_dms_v4_vector_complete_route.py';assert not new.exists();ast.parse(text)
new.write_text(text,encoding='utf8',newline='\n')
diff=BASE/'dms-v4-final-qualification-full-operational-diff-20261005.txt';assert not diff.exists()
diff.write_text(''.join(difflib.unified_diff(old.read_text(encoding='utf8').splitlines(keepends=True),text.splitlines(keepends=True),fromfile=old.name,tofile=new.name)),encoding='utf8')
packet=BASE/'dms-v4-final-qualification-helper-preparation-20261005.json';assert not packet.exists()
packet.write_text(json.dumps({'status':'PREPARED_ONLY_NOT_EXECUTED_FINAL_ROOT_REVIEW_AND_ACTUAL7_PLUS123_REQUIRED',
    'files':[{'file':str(p),'sha256':sha(p)} for p in [new,diff]],'prior_pass_counts':{'original99':99,'V3_new122':122},
    'new_V4_sources_required':7,'selected_fresh_prints_required':123,'actions_performed':{'compiler':0,'output_alias':0,'qualification':0},
    'limits':'Final SHA-bound approval separately binds actual completed source receipt and seed; all raw logs/CLI/guards/source/artifacts rechecked. No scientific scoring or novelty change.'},indent=2)+'\n',encoding='utf8')
print(json.dumps({'helper':str(new),'helper_sha256':sha(new),'diff_sha256':sha(diff),'packet_sha256':sha(packet)},indent=2))
