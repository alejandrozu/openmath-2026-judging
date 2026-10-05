"""Prepare the exact99 reuse adapter; performs no transfers or Lean invocations."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,difflib,ast
BASE=Path(__file__).resolve().parent
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
POLICY=BASE/'dms-original99-output-transfer-policy-20261005.json'
policy_sha=digest(POLICY)
assert policy_sha=='79b4fa2274995fa3a819fc77082847435fd2abe611d4a57968e62dff79e45f1e'
policy=json.loads(POLICY.read_bytes());assert policy['module_count']==policy['artifact_count']==99
assert not (BASE/'dms-original99-output-transfer-completed-20261005.json').exists()
stage=BASE/'builds/htpeo-dms-current-import-pruned-diagnostic'
assert not list(stage.rglob('*.olean')) and not list(stage.rglob('*.ilean'))
base=BASE/'run_source_plan.py';base_raw=base.read_bytes()
assert hashlib.sha256(base_raw).hexdigest()=='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'
previous=BASE/'run_dms_import_pruned_plan.py';previous_raw=previous.read_bytes()
assert hashlib.sha256(previous_raw).hexdigest()=='678aba8a1e9251575ec8a8639411346b92208bfcced509f772d9ff6f075b9b9c'
archive=BASE/'runner_source_archives/dms-original99-reuse-adapter-preparation-20261005'
archive.mkdir(exist_ok=True)
for path in [previous,BASE/'dms-import-pruned-runner-prepared.diff',BASE/'dms_original99_output_transfer.py',BASE/'verify_dms_full228_stage.py']:
    raw=path.read_bytes();target=archive/(path.stem+'.'+hashlib.sha256(raw).hexdigest()+path.suffix)
    assert not target.exists();target.write_bytes(raw)
text=base_raw.decode('utf8')
needle=" 'sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2','matt-unitary-current','htpeo-dms-current'}"
assert text.count(needle)==1
text=text.replace(needle,needle[:-1]+",'htpeo-dms-current-import-pruned-diagnostic'}")
stage_verifier_sha=digest(BASE/'verify_dms_full228_stage.py')
seed_helper_sha=digest(BASE/'dms_original99_output_transfer.py')
extra=f'''
# Qualified exact99 previous-own-output transfer; no invented compilation rows.
assert project=='htpeo-dms-current-import-pruned-diagnostic' and worker_threads==1
assert third_worker_guarded and not full_mathlib_source_mode and not independent_resource_mode and not defer_whole_import_mode
assert third_worker_pilot != third_worker_continuation
policy_flag='--reviewed-policy-sha256';seed_flag='--seed-receipt-sha256'
assert sys.argv.count(policy_flag)==sys.argv.count(seed_flag)==1
dms_policy_sha=sys.argv[sys.argv.index(policy_flag)+1]
dms_seed_sha=sys.argv[sys.argv.index(seed_flag)+1]
assert dms_policy_sha=='{policy_sha}' and re.fullmatch('[0-9a-f]{{64}}',dms_seed_sha)
assert hashlib.sha256((BASE/'verify_dms_full228_stage.py').read_bytes()).hexdigest()=='{stage_verifier_sha}'
assert hashlib.sha256((BASE/'dms_original99_output_transfer.py').read_bytes()).hexdigest()=='{seed_helper_sha}'
from verify_dms_full228_stage import verify_stage
from dms_original99_output_transfer import verify_seed
dms_stage_preflight=verify_stage(require_cold=False)
dms_stage_preflight['identity_verifier_performed_output_transfer']=dms_stage_preflight.pop('outputs_copied_or_marked_reusable')
dms_seed_preflight=verify_seed(dms_policy_sha,dms_seed_sha)
seed_receipt=json.loads((BASE/'dms-original99-output-transfer-completed-20261005.json').read_bytes())
assert hashlib.sha256(Path(seed_receipt['approval_receipt']).read_bytes()).hexdigest()==seed_receipt['approval_receipt_sha256']
assert seed_receipt['seed_helper_sha256']=='{seed_helper_sha}'
plan['import_only_stage_identity_preflight']=dms_stage_preflight
plan['qualified_previous_own_original99_transfer']=dms_seed_preflight
plan['cross_route_own_output_reuse_labels']={{'previous_own_original_route_cold_outputs_reused':99,'new_cold_diagnostic_sources_required':129,'outputs_described_as_new_compilation_rows':False}}
'''
needle="plan=json.loads((dest/'build-plan.json').read_text())"
assert text.count(needle)==1;text=text.replace(needle,needle+'\n'+extra)
needle="env['LEAN_NUM_THREADS']=str(worker_threads)"
assert text.count(needle)==1
text=text.replace(needle,needle+'''
# Original custom outputs may be read by the verifier, never imported by Lean.
original_custom_dir=(BASE/'builds/htpeo-dms-current').resolve()
assert not any(Path(p).resolve().is_relative_to(original_custom_dir) for p in paths)
plan['diagnostic_LEAN_PATH_policy']={'actual_import_paths':paths,'original_custom_output_directory_forbidden':str(original_custom_dir)}
''')
needle='if independent_resource_mode:\n' # actual base uses CRLF; match complete section via normalized view.
text=text.replace('\r\n','\n')
needle="if independent_resource_mode:\n plan['resource_settings']['independent_resource_dag_mode']="
assert text.count(needle)==1
new="""# Seeded modules are skip metadata, not simulated compiler invocation rows.
dms_seed_names={m['module'] for m in dms_seed_preflight['modules']}
assert len(dms_seed_names)==99 and dms_seed_names.isdisjoint(dms_seed_preflight['required129_new_cold_module_names'])
for n in dms_seed_names:
 assert n not in retained and n not in {row['module'] for row in plan['builds']},'Transferred99 outputs must never become fresh compilation rows'
 retained[n]={'exit':0,'reuse_kind':'PREVIOUS_OWN_ORIGINAL_ROUTE_COLD_OUTPUT_TRANSFER','fresh_diagnostic_compilation':False}
plan['verified_previous_own_cold_source_output_modules']=sorted(dms_seed_names)
if independent_resource_mode:
 plan['resource_settings']['independent_resource_dag_mode']="""
text=text.replace(needle,new)
needle='def save():\n temporary=report.with_suffix(\'.json.tmp\')'
assert text.count(needle)==1
new="""def save():
 actual_passes={row['module'] for row in plan['builds'] if row['exit']==0 and not row['is_endpoint_audit'] and not row.get('stop_reason')}
 assert actual_passes.isdisjoint(dms_seed_names)
 required_new=set(dms_seed_preflight['required129_new_cold_module_names'])
 assert actual_passes<=required_new
 plan['source_coverage_summary']={'reused_previous_own_original_cold_source_outputs':99,
  'new_cold_diagnostic_source_passes':len(actual_passes),'new_cold_source_module_names':sorted(actual_passes),
  'unattempted_or_unpassed_required_new_source_modules':sorted(required_new-actual_passes),
  'scientific_body_sources_verified_in_this_qualified_route':99+len(actual_passes),
  'scientific_body_source_total':228,'selected_audit_always_requires_new_invocation':True,
  'qualification':'99 previous own original-route cold outputs transferred with full unaffected-closure identities; only actual new source invocations appear in builds.'}
 if plan['status'].startswith('PASS'):assert actual_passes==required_new,'A diagnostic PASS requires all129 new cold sources plus99 separately qualified prior own outputs'
 temporary=report.with_suffix('.json.tmp')"""
text=text.replace(needle,new)
ast.parse(text)
previous.write_text(text,encoding='utf8',newline='')
new_sha=digest(previous)
diff=''.join(difflib.unified_diff(base_raw.decode().splitlines(True),text.splitlines(True),
    fromfile='run_source_plan.py@70ff209c',tofile=previous.name+'@qualified99'))
diff_path=BASE/'dms-original99-reuse-runner-full.diff'
assert not diff_path.exists();diff_path.write_text(diff,encoding='utf8',newline='')
out=BASE/'dms-original99-transfer-and-reuse-adapter-preparation-20261005.json'
assert not out.exists()
record={'status':'PREPARED_ONLY_EXACT99_TRANSFER_HELPER_AND_REUSE_ADAPTER_NO_COPY_NO_LEAN',
 'prepared_utc':datetime.now(timezone.utc).isoformat(),'policy':str(POLICY),'policy_sha256':policy_sha,
 'transfer_helper':str(BASE/'dms_original99_output_transfer.py'),'transfer_helper_sha256':seed_helper_sha,
 'stage_verifier_sha256':stage_verifier_sha,'prepared_runner':str(previous),'prepared_runner_sha256':new_sha,
 'full_diff':str(diff_path),'full_diff_sha256':digest(diff_path),'base_runner_sha256':digest(base),
 'previous_cold_runner_sha256':hashlib.sha256(previous_raw).hexdigest(),
 'source_plan_sha256':digest(stage/'build-plan.json'),'own_output_files_present':0,
 'reused_previous_own_cold_sources_proposed':99,'required_new_cold_diagnostic_sources':129,
 'allowed_output_artifacts':99,'planned_output_bytes':policy['total_output_bytes'],
 'unchanged_guard':'6GiBown/5GiBcommit dispatch/6GiBphysical/4GBdisk;continuous1GiBcommit/3GiBphysical/1GBdisk;-j1',
 'pilot_scope_after_separate_approved_transfer':'Exactly one NEW required cold source;99 transferred helpers skipped without compilation rows.',
 'minimum_LEAN_PATH':'Newstage+verifiedofficialdependencies; original custom directory explicitly forbidden.',
 'execution_approval':'PENDING_ROOT_REVIEW. No transfer receipt or source invocation exists.',
 'qualification':'The full diff normalizes Python CRLF to LF only outside its explicitly listed operational additions; scientific Lean sources/options/comments/audits remain unchanged.'}
out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
print(json.dumps({'preparation':str(out),'preparation_sha256':digest(out),'policy_sha256':policy_sha,
 'helper_sha256':seed_helper_sha,'runner_sha256':new_sha,'full_diff_sha256':digest(diff_path),
 'copies_performed':0,'new_Lean_invocations':0},indent=2),flush=True)
