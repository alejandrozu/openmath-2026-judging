"""Prepare-only exact operational derivative of the reviewed V3 runner."""
from pathlib import Path
import hashlib,json,difflib,ast
BASE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
old=BASE/'run_dms_v3_linked_plan.py'
assert sha(old)=='832e875054d76b597652a37edc197f47182253172581be1ab962b1ae6187ee3d'
policy=BASE/'dms-v4-vector122-link99-readonly-policy-20261005.json'
assert policy.exists()
helper=BASE/'dms_v4_vector122_seed.py'
verifier=BASE/'verify_dms_v4_vector_stage.py'
text=old.read_text(encoding='utf8').replace('htpeo-dms-current-import-pruned-v3','htpeo-dms-current-import-pruned-v4-vector')
text=text.replace('Original entrant artifacts are never reused. A resource-interrupted replay can retain',
    'Only qualified previous OWN cold passes are reused (99 original plus122 V3-new). A resource-interrupted replay can retain')
start=text.index('# Qualified exact99 previous-own-output')
end=text.index('\ndeferred_whole_names=set()',start)
block='''# V4 exact221 previous OWN cold passes; no invented compiler rows.
assert project=='htpeo-dms-current-import-pruned-v4-vector' and worker_threads==1
assert third_worker_guarded and not full_mathlib_source_mode and not independent_resource_mode and not defer_whole_import_mode
assert third_worker_pilot != third_worker_continuation
assert not plan.get('additional_dependency_libs'),'Only the exact99 verified V1 read-only directory is admitted explicitly'
policy_flag='--reviewed-policy-sha256';seed_flag='--seed-receipt-sha256'
assert sys.argv.count(policy_flag)==sys.argv.count(seed_flag)==1
dms_policy_sha=sys.argv[sys.argv.index(policy_flag)+1]
dms_seed_sha=sys.argv[sys.argv.index(seed_flag)+1]
assert dms_policy_sha==POLICY_SHA_PLACEHOLDER and re.fullmatch('[0-9a-f]{64}',dms_seed_sha)
assert hashlib.sha256((BASE/'verify_dms_v4_vector_stage.py').read_bytes()).hexdigest()==VERIFIER_SHA_PLACEHOLDER
assert hashlib.sha256((BASE/'dms_v4_vector122_seed.py').read_bytes()).hexdigest()==HELPER_SHA_PLACEHOLDER
from verify_dms_v4_vector_stage import verify_stage
from dms_v4_vector122_seed import verify_seed
dms_stage_preflight=verify_stage(require_cold=False,linked122_allowed=True)
dms_seed_preflight=verify_seed(dms_policy_sha,dms_seed_sha)
seed_receipt=json.loads((BASE/'dms-v4-vector122-link99-readonly-seed-completed-20261005.json').read_bytes())
plan['import_only_stage_identity_preflight']=dms_stage_preflight
plan['qualified_previous221_own_cold_passes']=dms_seed_preflight
plan['cross_route_own_output_reuse_labels']={'original_route_own_cold_passes_reused_via_existing_V1_readonly_copies':99,
 'V3_new_own_cold_passes_reused_via_V4_links':122,'new_V4_source_compilations_required':7,'outputs_described_as_new_compilation_rows':False}
'''
block=block.replace('POLICY_SHA_PLACEHOLDER',repr(sha(policy))).replace('VERIFIER_SHA_PLACEHOLDER',repr(sha(verifier))).replace('HELPER_SHA_PLACEHOLDER',repr(sha(helper)))
text=text[:start]+block+text[end:]
text=text.replace('paths=[str(dest)]','paths=[str(dest),str(Path(dms_seed_preflight[\'readonly99_import_directory\']).resolve())]')
start=text.index('# Original custom outputs may be read by the verifier')
end=text.index('\ncanonical=lambda',start)
block='''# Original/V2/V3 custom directories forbidden; exact99 proven V1 copies are read-only inputs.
forbidden_custom_dirs=[Path(p).resolve() for p in dms_seed_preflight['forbidden_custom_import_directories']]
assert not any(Path(p).resolve().is_relative_to(forbidden) for p in paths for forbidden in forbidden_custom_dirs)
readonly99=Path(dms_seed_preflight['readonly99_import_directory']).resolve()
assert paths[1]==str(readonly99) and readonly99==(BASE/'builds/htpeo-dms-current-import-pruned-diagnostic').resolve()
plan['diagnostic_LEAN_PATH_policy']={'actual_import_paths':paths,'readonly99_proven_V1_input_directory':str(readonly99),
 'forbidden_custom_output_directories':[str(p) for p in forbidden_custom_dirs],
 'prior221_outputs_never_compiler_targets':True}
'''
text=text[:start]+block+text[end:]
start=text.index('# Seeded modules are skip metadata')
end=text.index('\nif independent_resource_mode:',start)
block='''# Prior221 modules are skip metadata, never simulated V4 invocation rows.
dms_seed_names=set(dms_seed_preflight['prior221_names'])
dms_linked_output_paths={Path(p).resolve() for p in dms_seed_preflight['122_linked_output_paths']}
assert len(dms_linked_output_paths)==122
plan['hard_link_write_policy']='Skip221 prior own passes;122 V3-new V4 links and99 V1 read-only outputs are never written. Protected original/V2 and V1/V3 count2 remain unchanged.'
assert len(dms_seed_names)==221 and dms_seed_names.isdisjoint(dms_seed_preflight['required7_new_cold_module_names'])
for n in dms_seed_names:
 assert n not in retained and n not in {row['module'] for row in plan['builds']},'Prior221 outputs must never become fresh V4 invocation rows'
 retained[n]={'exit':0,'reuse_kind':'QUALIFIED_PREVIOUS_OWN_COLD_OUTPUT_READONLY99_OR_LINKED122','fresh_V4_compilation':False}
plan['verified_previous_own_cold_source_output_modules']=sorted(dms_seed_names)
'''
text=text[:start]+block+text[end:]
start=text.index('def save():')
end=text.index('\n temporary=report.with_suffix',start)
block='''def save():
 actual_passes={row['module'] for row in plan['builds'] if row['exit']==0 and not row['is_endpoint_audit'] and not row.get('stop_reason')}
 assert actual_passes.isdisjoint(dms_seed_names)
 required_new=set(dms_seed_preflight['required7_new_cold_module_names'])
 assert actual_passes<=required_new
 plan['source_coverage_summary']={'original_route_own_cold_passes_reused_via_existing_V1_readonly_copies':99,
  'V3_new_own_cold_passes_reused_via_new_V4_links':122,'new_cold_V4_source_passes':len(actual_passes),
  'new_cold_V4_source_names':sorted(actual_passes),'unattempted_or_unpassed_required_new_source_modules':sorted(required_new-actual_passes),
  'scientific_body_sources_verified_in_this_route':221+len(actual_passes),'scientific_body_source_total':228,
  'selected123_print_audit_always_requires_new_invocation':True,
  'qualification':'221 previous OWN cold passes with complete unchanged source/custom/official closure,99 read-only proven V1 copies and122 V3-new hardlinks; only actual seven-new V4 source invocations appear in builds.'}
 if plan['status'].startswith('PASS'):
  assert actual_passes==required_new,'V4 PASS requires all seven NEW sources plus221 separately qualified prior OWN passes'
  plan['completed221_identity_recheck']=verify_seed(dms_policy_sha,dms_seed_sha)
'''
text=text[:start]+block+text[end:]
target=BASE/'run_dms_v4_vector_plan.py';assert not target.exists()
ast.parse(text)
target.write_text(text,encoding='utf8',newline='\n')
diff=BASE/'dms-v4-vector-runner-full-operational-diff-20261005.txt';assert not diff.exists()
diff.write_text(''.join(difflib.unified_diff(old.read_text(encoding='utf8').splitlines(keepends=True),text.splitlines(keepends=True),fromfile=old.name,tofile=target.name)),encoding='utf8')
helper_diff=BASE/'dms-v4-vector-seed-helper-full-implementation-20261005.txt';assert not helper_diff.exists()
helper_diff.write_text(''.join(difflib.unified_diff([],helper.read_text(encoding='utf8').splitlines(keepends=True),fromfile='/dev/null',tofile=helper.name)),encoding='utf8')
packet=BASE/'dms-v4-vector122-link99-readonly-execution-preparation-20261005.json';assert not packet.exists()
record={'status':'PREPARED_V4_NO_ALIAS_OR_LEAN_ROOT_FULL_REVIEW_REQUIRED','scientific_source_changes':'One additional VecNotation header at InflationA only; all228 scientific bodies/options/comments and123 audit requests unchanged',
 'prior_source_passes':{'original_route_via_existing99_V1_readonly_copies':99,'V3_new_via122_future_V4_hardlinks':122},
 'required_new_sources':7,'required_new_audits':1,'selected_print_count':123,'aliases_created':0,'compiler_invocations':0,
 'source_plan':str(BASE/'builds/htpeo-dms-current-import-pruned-v4-vector/build-plan.json'),
 'files':[{'file':str(p),'sha256':sha(p)} for p in [policy,helper,verifier,target,diff,helper_diff]],
 'first_new_source':'InflationA','first_new_command':['EXACT_PINNED_LEAN_4.33.1','-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o','InflationA.olean','InflationA.lean'],
 'resource_policy':'Unchanged6GiB own job/process;5GiB commit/6GiB physical/4GB disk dispatch;continuous1GiB commit/3GiB physical/1GB disk;-j1;max2 granular workers; no whole route.'}
packet.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
print(json.dumps({'runner':str(target),'runner_sha256':sha(target),'policy_sha256':sha(policy),'helper_sha256':sha(helper),'preparation':str(packet),'preparation_sha256':sha(packet)},indent=2))
