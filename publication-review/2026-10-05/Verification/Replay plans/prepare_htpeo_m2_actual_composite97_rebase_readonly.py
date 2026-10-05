"""Separate HT M2 exact97 rebase to actual DMS composite; metadata only, no aliases/Lean."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,difflib,hashlib,json
BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,d):
    with Path(p).open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')
OLD_HELPER=BASE/'htpeo_m2_original97_hardlink_seed.py'
OLD_HELPER_SHA='cf35eb78ccf5e36e7775eb0d4d676de2cf6cf57d5ee5b8cbb8878827a0f5ae4e'
OLD_POLICY=BASE/'htpeo-m2-original97-hardlink-policy-20261005.json'
OLD_POLICY_SHA='bab7476a702cb7ccf182e5c051f70ecc30a3b21dc14cec8c872487558f9a5092'
OLD_RUNNER=BASE/'run_htpeo_m2_linked_granular_plan.py'
OLD_RUNNER_SHA='2ef3c3e84a32f9ebebd83c37941f2f9205ee8c511be26cf04355396b2b1f3ae3'
QUAL=BASE/'dms-v4-vector-composite-supplement-final-qualification-20261005.json'
QUAL_SHA='7d401ae5c7003a1520dac33288b2335645bbd095a3327cc8ddefb2d17aa417ab'
assert sha(OLD_HELPER)==OLD_HELPER_SHA and sha(OLD_POLICY)==OLD_POLICY_SHA and sha(OLD_RUNNER)==OLD_RUNNER_SHA and sha(QUAL)==QUAL_SHA
from htpeo_m2_original97_hardlink_seed import source_and_runtime_check,file_identity,stable_identity,inode_key,digest
oldpolicy=json.loads(OLD_POLICY.read_bytes());plan,prep=source_and_runtime_check(oldpolicy)
qualified=json.loads(QUAL.read_bytes());assert qualified['qualified'] is True
assert qualified['prior_own_original_cold_source_outputs_reused_readonly99']==99
assert qualified['prior_V3_new_own_cold_source_passes_reused_linked122']==122 and qualified['new_V4_cold_source_passes']==7
assert qualified['requested_endpoint_count']==qualified['actual_unique_print_count']==123
assert qualified['selected_classification_counts']=={'STANDARD_KERNEL_AXIOMS':120,'AXIOM_FREE':3}
assert not qualified['selected_admitted'] and not qualified['selected_unknown_axioms']
assert qualified['original120_axiom_classes_and_sets_match_successful_supplement'] is True
for key,hashkey in [('final_source_receipt','final_source_receipt_sha256'),('organizer_supplemental_audit_receipt','organizer_supplemental_audit_receipt_sha256')]:assert sha(qualified[key])==qualified[hashkey]
fullsources=[]
for route,expected in [('htpeo-dms-current','55627b070d16fa8027c02a94d8d97b22d5e24d5598bd09ef76e724d14d1426a3'),('htpeo-dms-current-import-pruned-v4-vector','30f7b071fbcd9ddb37e48a059126daf8e37dd65dae9b2733614af926589a7308')]:
    p=BASE/'builds'/route/'build-plan.json';assert sha(p)==expected
    doc=json.loads(p.read_bytes());assert len(doc['modules'])==228
    for r in doc['modules']:
        assert sha(r['file'])==r['sha256'];fullsources.append({'route':route,'module':r['module'],'file':r['file'],'sha256':r['sha256']})
assert len(fullsources)==456
body_records=qualified['all228_body_identity_and2735_official_source_artifact_runtime_git_cache_identity']['body_identity_records']
assert len(body_records)==228 and all(r['body_identical_to_V3_and_frozen_original'] for r in body_records)
v2=BASE/'dms-modeq-v2-original99-hardlink-seed-completed-20261005.json'
v3=BASE/'dms-v3-v1copy99-hardlink-seed-completed-20261005.json'
v4=BASE/'dms-v4-vector122-link99-readonly-seed-completed-20261005.json'
v2d,v3d,v4d=[json.loads(p.read_bytes()) for p in [v2,v3,v4]]
assert len(v2d['output_links'])==len(v3d['output_links'])==99 and len(v4d['output_links'])==122
protected=[]
def addpair(item,left,right,label,release_names):
    a,b=Path(item[left]),Path(item[right]);ia,ib=file_identity(a),file_identity(b)
    assert inode_key(ia)==inode_key(ib) and stable_identity(ia)==stable_identity(ib)
    assert ia['link_count']==ib['link_count']==2 and sha(a)==sha(b)==item['sha256']
    protected.append({'module':item['module'],'left':str(a),'right':str(b),'sha256':item['sha256'],'identity_before':ia,
      'classification':label,'future_original_V2_increment_only_for_eligible97':item['module'] in release_names})
eligible=set(oldpolicy['eligible97_module_names']);assert len(eligible)==97
for r in v2d['output_links']:addpair(r,'original_owned_output','diagnostic_target','ORIGINAL_V2_PROTECTED99',eligible)
for r in v3d['output_links']:addpair(r,'v1_proven_copied_output_seed_source','diagnostic_target','V1_COPY_V3_READONLY99',set())
for r in v4d['output_links']:addpair(r,'source','target','V3_NEW_V4_LINKED122',set())
assert len(protected)==320 and sum(r['classification']!='ORIGINAL_V2_PROTECTED99' for r in protected)==221
assert sum(r['future_original_V2_increment_only_for_eligible97'] for r in protected)==97
for r in oldpolicy['output_links']:
    assert not Path(r['M2_target']).exists() and sha(r['original_owned_output'])==r['sha256']
for name in oldpolicy['required3_new_cold_module_names']:
    entry=next(m for m in plan['modules'] if m['module']==name)
    for suffix in ['.olean','.olean.private','.olean.server','.ilean']:assert not Path(entry['file']).with_suffix(suffix).exists()
INVENTORY=BASE/'htpeo-m2-composite-qualified97-protected221-and-originalV2-identity-inventory-20261005.json'
save(INVENTORY,{'status':'READ_ONLY_ACTUAL_COMPOSITE_QUALIFIED_SOURCE_AND_PROTECTED_INODE_REBASE_NO_LINK',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'composite_qualification_file':str(QUAL),'composite_qualification_sha256':QUAL_SHA,
 'all456_original_and_V4_scientific_source_identities':fullsources,'qualified_body228_records':body_records,
 'protected_originalV2_99_plus_qualified_inputs221_pairs':protected,
 'protected221_alias_counts_must_remain_exactly2':True,'prospective_originalV2_only97_increment_requires_root_release':True,
 'bound_seed_receipts':[{'file':str(p),'sha256':sha(p)} for p in [v2,v3,v4]],
 'original97_source_and_98_custom_closure_identity_recheck':'PASS','complete2711official_source_and_olean_recheck':'PASS',
 'original97_M2_targets_absent':True,'three_required_new_M2_sources_cold':True,'aliases_or_compilers':0})
HELPER=BASE/'htpeo_m2_composite_qualified97_hardlink_seed.py'
POLICY=BASE/'htpeo-m2-composite-qualified97-hardlink-policy-20261005.json'
SEED=BASE/'htpeo-m2-composite-qualified97-hardlink-seed-completed-20261005.json'
RUNNER=BASE/'run_htpeo_m2_composite_qualified_linked_granular_plan.py'
function='''
def composite_protection_check(policy, after_seed=False):
    composite=policy['actual_DMS_composite_qualification']
    assert digest(composite['file'])==composite['sha256']==COMPOSITE_SHA
    q=load(composite['file'])
    assert q['qualified'] is True and q['status']==composite['status']
    assert q['prior_own_original_cold_source_outputs_reused_readonly99']==99
    assert q['prior_V3_new_own_cold_source_passes_reused_linked122']==122 and q['new_V4_cold_source_passes']==7
    assert q['requested_endpoint_count']==q['actual_unique_print_count']==123
    assert not q['selected_admitted'] and not q['selected_unknown_axioms']
    assert q['frozen_original_audit_exit1_120of123_fully_preserved'] and q['original120_axiom_classes_and_sets_match_successful_supplement'] is True
    for key,hkey in [('final_source_receipt','final_source_receipt_sha256'),('organizer_supplemental_audit_receipt','organizer_supplemental_audit_receipt_sha256')]:assert digest(q[key])==q[hkey]
    inv=policy['actual_composite_protected_identity_inventory']
    assert digest(inv['file'])==inv['sha256'];records=load(inv['file'])
    for binding in records['all456_original_and_V4_scientific_source_identities']:assert digest(binding['file'])==binding['sha256']
    assert len(records['qualified_body228_records'])==228 and all(r['body_identical_to_V3_and_frozen_original'] for r in records['qualified_body228_records'])
    for binding in records['bound_seed_receipts']:assert digest(binding['file'])==binding['sha256']
    for row in records['protected_originalV2_99_plus_qualified_inputs221_pairs']:
        left,right=file_identity(row['left']),file_identity(row['right']);before=row['identity_before']
        assert inode_key(left)==inode_key(right)==inode_key(before)
        assert stable_identity(left)==stable_identity(right)==stable_identity(before)
        increment=1 if after_seed and row['future_original_V2_increment_only_for_eligible97'] else 0
        assert left['link_count']==right['link_count']==before['link_count']+increment
        assert digest(row['left'])==digest(row['right'])==row['sha256']
    return {'status':'ACTUAL_DMS_COMPOSITE_BODY_AND_PROTECTED221_RECHECKED_ORIGINALV2_ONLY_APPROVED97_INCREMENT' if after_seed else 'ACTUAL_DMS_COMPOSITE_BODY_AND_ALL_PROTECTED_COUNTS_RECHECKED_BEFORE_SEED',
      'actual_composite_sha256':COMPOSITE_SHA,'protected221_unchanged':True,'originalV2_approved97_link_increment':1 if after_seed else 0}

'''.replace('COMPOSITE_SHA',repr(QUAL_SHA))
old=OLD_HELPER.read_text(encoding='utf8');new=old
replacement={
 "POLICY = BASE / 'htpeo-m2-original97-hardlink-policy-20261005.json'":"POLICY = BASE / 'htpeo-m2-composite-qualified97-hardlink-policy-20261005.json'",
 "SEED_RECEIPT = BASE / 'htpeo-m2-original97-hardlink-seed-completed-20261005.json'":"SEED_RECEIPT = BASE / 'htpeo-m2-composite-qualified97-hardlink-seed-completed-20261005.json'",
 "'run_htpeo_m2_linked_granular_plan.py' in text":"'run_htpeo_m2_composite_qualified_linked_granular_plan.py' in text",
 "progress = BASE/'htpeo-m2-original97-hardlink-seed-progress-20261005.json'":"progress = BASE/'htpeo-m2-composite-qualified97-hardlink-seed-progress-20261005.json'",
 "assert qualified['prior_own_original_cold_source_outputs_reused']+qualified['new_cold_source_passes']==228":"assert qualified['prior_own_original_cold_source_outputs_reused_readonly99']==99\n    assert qualified['prior_V3_new_own_cold_source_passes_reused_linked122']==122 and qualified['new_V4_cold_source_passes']==7",
 "    source_and_runtime_check(policy); inactive = route_inactive()":"    source_and_runtime_check(policy); composite_protection_check(policy,after_seed=False); inactive = route_inactive()",
 "    preserve(); result['source_routes_inactive_after'] = route_inactive()":"    preserve(); result['composite_protected221_and_originalV2_postseed_identity']=composite_protection_check(policy,after_seed=True)\n    result['source_routes_inactive_after'] = route_inactive()",
 "    inactive = route_inactive(allow_own_reviewed_M2_runner=True)":"    protection=composite_protection_check(policy,after_seed=True)\n    inactive = route_inactive(allow_own_reviewed_M2_runner=True)",
 "      'source_route_inactivity_check': inactive,":"      'source_route_inactivity_check': inactive,'actual_composite_protection_check':protection,",
 "    if sys.argv[1:] == ['--prepare-policy']: prepare()\n    elif len(sys.argv) == 4 and sys.argv[1] == '--seed-root-approved': seed(sys.argv[2], sys.argv[3])":"    if len(sys.argv) == 4 and sys.argv[1] == '--seed-root-approved': seed(sys.argv[2], sys.argv[3])",
}
for a,b in replacement.items():
    # One own-runner exemption and one blocked-name occurrence deliberately rebind together.
    assert new.count(a)==(2 if a=="'run_htpeo_m2_linked_granular_plan.py' in text" else 1),(a,new.count(a));new=new.replace(a,b)
needle='def seed(approval_path, approval_sha):\n';assert new.count(needle)==1;new=new.replace(needle,function+needle,1)
needle="    assert released['approved97_module_names']==policy['eligible97_module_names']\n";assert new.count(needle)==1
new=new.replace(needle,needle+"    assert released['actual_DMS_composite_qualification_sha256']==policy['actual_DMS_composite_qualification']['sha256']\n    assert released['protected221_identity_inventory_sha256']==policy['actual_composite_protected_identity_inventory']['sha256']\n    assert released['only_originalV2_eligible97_linkcounts_may_increment_once'] is True and released['all_qualified221_inputs_must_stay_unchanged'] is True\n",1)
ast.parse(new)
with HELPER.open('x',encoding='utf8',newline='\n') as f:f.write(new)
helper_diff=BASE/'htpeo-m2-composite-qualified97-seed-helper-minimal-operational.diff'
with helper_diff.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=OLD_HELPER.name,tofile=HELPER.name))
policy=copy.deepcopy(oldpolicy)
policy.update(status='PREPARED_EXACT97_ACTUAL_COMPOSITE_QUALIFIED_REBASE_NO_LINK_NO_LEAN',prepared_utc=datetime.now(timezone.utc).isoformat(),
 preserved_prior_policy=str(OLD_POLICY),preserved_prior_policy_sha256=OLD_POLICY_SHA,
 actual_DMS_composite_qualification={'file':str(QUAL),'sha256':QUAL_SHA,'status':qualified['status']},
 actual_composite_protected_identity_inventory={'file':str(INVENTORY),'sha256':sha(INVENTORY)},
 seed_helper=str(HELPER),seed_helper_sha256=sha(HELPER),seed_receipt_future_file=str(SEED),
 link_count_release_requirements={'originalV2_only97_count2_to3_requires_explicit_root_release':True,'all_qualified221_counts_stay2':True,'all_original_and_V4_scientific_source_bytes_and_five_premises_retained015_unchanged':True},
 required_separate_seed_approval_status='ROOT_APPROVED_HTPEO_M2_EXACT97_LINK_SEED_ONLY_AFTER_COMPLETE_DMS_ROUTE_AND_V2_LOCK_RELEASE_NO_LEAN',
 execution_qualification='Prepared rebase only. Exact97 prior original own cold passes retain original provenance; independentStarCore1+required3new/4prints remain separate. No alias/Lean/score/novelty/publication change.')
save(POLICY,policy);policy_sha=sha(POLICY)
rold=OLD_RUNNER.read_text(encoding='utf8');rnew=rold
replacements={
 'from htpeo_m2_original97_hardlink_seed import':'from htpeo_m2_composite_qualified97_hardlink_seed import',
 "'htpeo_m2_original97_hardlink_seed.py'":"'htpeo_m2_composite_qualified97_hardlink_seed.py'",
 "'htpeo-m2-original97-hardlink-policy-20261005.json'":"'htpeo-m2-composite-qualified97-hardlink-policy-20261005.json'",
 OLD_POLICY_SHA:policy_sha,OLD_HELPER_SHA:sha(HELPER),
}
for a,b in replacements.items():assert a in rnew,a;rnew=rnew.replace(a,b)
ast.parse(rnew)
with RUNNER.open('x',encoding='utf8',newline='\n') as f:f.write(rnew)
runner_diff=BASE/'htpeo-m2-composite-qualified97-runner-minimal-operational.diff'
with runner_diff.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff(rold.splitlines(True),rnew.splitlines(True),fromfile=OLD_RUNNER.name,tofile=RUNNER.name))
packet=BASE/'htpeo-m2-actual-composite-qualified97-rebase-root-review-packet-20261005.json'
save(packet,{'status':'PREPARED_ONLY_SEPARATE_ACTUAL_COMPOSITE97_REBASE_ROOT_REVIEW_REQUIRED_NO_LINK_NO_LEAN',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'actual_DMS_composite_qualification_sha256':QUAL_SHA,'policy':str(POLICY),'policy_sha256':policy_sha,
 'protected221_and_originalV2_inventory':str(INVENTORY),'protected_inventory_sha256':sha(INVENTORY),
 'seed_helper':str(HELPER),'seed_helper_sha256':sha(HELPER),'minimal_helper_diff':str(helper_diff),'minimal_helper_diff_sha256':sha(helper_diff),
 'runner':str(RUNNER),'runner_sha256':sha(RUNNER),'minimal_runner_diff':str(runner_diff),'minimal_runner_diff_sha256':sha(runner_diff),
 'exact_scope':{'original_owned_cold_output_reuse':97,'independent_prior_M2_StarCore':1,'required_new_M2_sources':3,'required_selected_prints':4,'whole_sources_unattempted':21},
 'old_original119_failedV2_and_all_prepared_files_unchanged':True,
 'protection':'Allqualified221 V1/V3/V4 inputinodepairs remain unchanged/count2. Onlyoriginal/V2 eligible97 may gain one alias after separate SHA-bound root release; no actualaliases here.',
 'next_actions_require_separate_root_review':['root fullhelper/policy/runnerdiff review','root release original/V2 exact97 linkcountlock','root seed-only approval','root completedseed independentverification','actual resource lease and separate3source/4print approval'],
 'compiler_guard_resource_floors_semantic_options_five_DMS_premises_retained015_changed':False,
 'alias_copy_Lean_source_or_existing_receipt_mutations':0})
print(json.dumps({'packet':str(packet),'packet_sha256':sha(packet),'policy_sha256':policy_sha,'inventory_sha256':sha(INVENTORY),
 'helper_sha256':sha(HELPER),'helper_diff_sha256':sha(helper_diff),'runner_sha256':sha(RUNNER),'runner_diff_sha256':sha(runner_diff),'aliases':0,'Lean':0},indent=2))
