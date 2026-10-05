"""Create a separate review-only M2 adapter and full diff; never run Lean or link."""
from pathlib import Path
from datetime import datetime, timezone
import ast, difflib, hashlib, json

BASE = Path(__file__).resolve().parent
BASELINE = BASE/'run_m2_granular_source_plan.py'
BASELINE_SHA = '6055abb09b2c9b985b69392af5cb3e8d2747a2027a3108fead72ed57ccc4e67c'
HELPER = BASE/'htpeo_m2_original97_hardlink_seed.py'
POLICY = BASE/'htpeo-m2-original97-hardlink-policy-20261005.json'
RUNNER = BASE/'run_htpeo_m2_linked_granular_plan.py'
DIFF = BASE/'htpeo-m2-linked-granular-runner-full.diff'
PACKET = BASE/'htpeo-m2-exact97-conditional-reuse-root-review-packet-20261005.json'

def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def new_json(path, value):
    with path.open('x', encoding='utf8') as stream: json.dump(value, stream, indent=2); stream.write('\n')
    return digest(path)

assert digest(BASELINE) == BASELINE_SHA
assert not RUNNER.exists() and not DIFF.exists() and not PACKET.exists()
policy = json.loads(POLICY.read_bytes()); policy_sha = digest(POLICY); helper_sha = digest(HELPER)
assert policy['status'] == 'PREPARED_EXACT97_CONDITIONAL_REUSE_POLICY_NO_LINK_NO_LEAN'
original = BASELINE.read_text(encoding='utf8')
source = original
changes = []
def replace(old, new, label):
    global source
    assert source.count(old) == 1, (label, source.count(old))
    source = source.replace(old, new)
    changes.append(label)

replace('Original entrant artifacts are never reused. A resource-interrupted replay can retain\nits own successful, receipt-matched artifacts; partial outputs are preserved by rename.',
'''Exactly97 SHA-bound previous-own DMS cold outputs may be reused as reviewed NTFS
links; they are separate from new M2 compilation and never overwritten. Existing
M2 StarCore pilot remains independent and immutable. Only3 new granular sources
and4 scoped prints may run. All21 whole-source modules/audits remain unattempted.''', 'truthful separate reuse/new scope documentation')
start = source.index('M2_PROJECT_PLAN_HASHES = ')
end = source.index('\nM2_PREPARATION_SHA256', start)
old = source[start:end]
replace(old, "M2_PROJECT_PLAN_HASHES = {'htpeo-erdos-m2': 'd75af96c5e21e79909e7a95646d0bf766609a46dd40bb0fc44e6308a6eb60ef6'}", 'single exact M2 project whitelist')
replace("assert project in M2_PROJECT_PLAN_HASHES, 'Exact eight-entry M2 whitelist only'", f'''assert project in M2_PROJECT_PLAN_HASHES, 'Exact reviewed HTP M2 project only'
assert '--htpeo-m2-reuse-execution-authorized' in sys.argv[3:], 'Separate root-approved reuse/source lease required'
from htpeo_m2_original97_hardlink_seed import verify_seed as m2_verify_seed
from htpeo_m2_original97_hardlink_seed import digest as m2_bound_digest
M2_LINK_POLICY_SHA256 = '{policy_sha}'
M2_LINK_HELPER_SHA256 = '{helper_sha}'
assert m2_bound_digest(BASE/'htpeo_m2_original97_hardlink_seed.py') == M2_LINK_HELPER_SHA256
def m2_flag(name):
 assert name in sys.argv and sys.argv.index(name)+1<len(sys.argv), name
 return sys.argv[sys.argv.index(name)+1]
m2_execution_approval_path=Path(m2_flag('--reuse-execution-approval')).resolve()
m2_execution_approval_sha=m2_flag('--reuse-execution-approval-sha256')
assert m2_execution_approval_path.is_relative_to(BASE.resolve()) and m2_bound_digest(m2_execution_approval_path)==m2_execution_approval_sha
m2_execution_approval=json.loads(m2_execution_approval_path.read_bytes())
assert m2_execution_approval['status']=='ROOT_APPROVED_HTPEO_M2_EXACT97_REUSE_PLUS3_COLD_SOURCES_AND4_SCOPED_PRINTS'
assert m2_execution_approval['reviewed_runner_sha256']==RUNNER_SOURCE_SHA256
assert m2_execution_approval['reviewed_policy_sha256']==M2_LINK_POLICY_SHA256
assert m2_execution_approval['reviewed_seed_helper_sha256']==M2_LINK_HELPER_SHA256
m2_seed_sha=m2_flag('--reuse-seed-receipt-sha256')
assert m2_execution_approval['reviewed_completed_seed_receipt_sha256']==m2_seed_sha
m2_seed_check=m2_verify_seed(M2_LINK_POLICY_SHA256,m2_seed_sha)
m2_link_policy=json.loads((BASE/'htpeo-m2-original97-hardlink-policy-20261005.json').read_bytes())
m2_reuse_names=set(m2_link_policy['eligible97_module_names'])
m2_own_prior_pilot_name='StarCore'
m2_required_new_names=set(m2_link_policy['required3_new_cold_module_names'])
m2_allowed_scoped_audits={{row['audit'] for row in m2_link_policy['audit_records']}}
assert len(m2_reuse_names)==97 and len(m2_required_new_names)==3 and len(m2_allowed_scoped_audits)==1
m2_protected_output_paths={{Path(row['M2_target']).resolve() for row in m2_link_policy['output_links']}}
m2_protected_output_paths.update(Path(row['file']).resolve() for row in m2_link_policy['M2_StarCore_pilot_artifacts'])
assert len(m2_protected_output_paths)==98
assert m2_execution_approval['approved97_module_names']==m2_link_policy['eligible97_module_names']
assert m2_execution_approval['approved3_new_source_names']==m2_link_policy['required3_new_cold_module_names']
assert m2_execution_approval['approved4_endpoint_names']==m2_link_policy['selected4_endpoint_names']
assert m2_execution_approval['whole_scope_remains_deferred'] is True''', 'SHA-bound seed/execution approval and exact97/1/3/4 identities')
replace("report=BASE/(project+'-m2-granular-fresh-build.json')", "report=BASE/(project+'-linked-granular-fresh-build.json')", 'separate mutable route receipt preserving existing pilot')
replace("paths=[str(dest)]\nfor extra in plan.get('additional_dependency_libs',[]):\n extra_path=Path(extra).resolve()\n assert extra_path.is_relative_to(BASE.resolve()),'Dependency library outside this verification workspace'\n paths.append(str(extra_path))",
'''paths=[str(dest)]
# This exact granular closure has no additional custom-library prerequisite.
# DMS outputs are admitted only by reviewed links inside this M2 destination.
assert all(not row['additional_library_prerequisites'] for row in m2_project['sources'] if not row['deferred_whole_scope'])''', 'exclude all original DMS/v2 and unused additional custom library roots from LEAN_PATH')
replace("env=dict(os.environ);env['LEAN_PATH']=';'.join(paths);env['PATH']=str(lean.parent)+';'+env['PATH']", "assert all(not Path(path).resolve().is_relative_to(Path(forbidden)) for path in paths for forbidden in m2_seed_check['forbidden_custom_LEAN_PATH_roots'])\nenv=dict(os.environ);env['LEAN_PATH']=';'.join(paths);env['PATH']=str(lean.parent)+';'+env['PATH']", 'explicit forbidden custom dependency-path check')
replace("plan['execution_route']='SEPARATE_ROOT_REVIEWED_M2_GRANULAR_SOURCE_ADAPTER'", "plan['execution_route']='SEPARATE_ROOT_REVIEWED_HTPEO_M2_EXACT97_PRIOR_OWN_REUSE_PLUS3_NEW_GRANULAR_SOURCES'", 'route-specific execution label')
replace("plan['selected_audit_axiom_review']=[]", '''plan['selected_audit_axiom_review']=[]
plan['prior_own_DMS_cold_sources_reused']=m2_link_policy['modules']
plan['independent_existing_M2_StarCore_pilot']={'file':m2_link_policy['M2_StarCore_pilot'],
 'sha256':m2_link_policy['M2_StarCore_pilot_sha256'],'actual_row':m2_link_policy['M2_StarCore_pilot_actual_row'],
 'qualification':'Previously completed independent M2 pilot, not a current new source invocation'}
plan['reuse_identity_check']=m2_seed_check
plan['reuse_execution_approval']={'file':str(m2_execution_approval_path),'sha256':m2_execution_approval_sha}
plan['hard_no_write_policy']={'skip97_prior_own_linked_source_names':sorted(m2_reuse_names),
 'preserve_independent_own_StarCore_pilot':True,'protected_output_paths':[str(p) for p in sorted(m2_protected_output_paths)],
 'required3_new_cold_source_names':sorted(m2_required_new_names),'required_scoped_audits':sorted(m2_allowed_scoped_audits),
 'original_DMS119_receipt_immutable':m2_link_policy['original119_receipt_sha256'],
 'M2_StarCore_pilot_receipt_immutable':m2_link_policy['M2_StarCore_pilot_sha256'],
 'previous_own_cold_output_is_never_a_new_current_M2_compilation':True}''', 'receipt separates97 previous cold,1 pilot and3 new compilation rows')
replace("retained={};past_rows={}", "retained={m2_own_prior_pilot_name:m2_link_policy['M2_StarCore_pilot_actual_row']};past_rows={}", 'protect existing pilot without inserting it into new build rows')
replace("archived=BASE/(project+'-m2-granular-fresh-build-attempt-'+str(attempt)+'.json')", "archived=BASE/(project+'-linked-granular-fresh-build-attempt-'+str(attempt)+'.json')", 'separate immutable resumed route attempts')
replace(" if n in retained:continue\n if n in deferred_whole_names:", " if n in retained:continue\n if n in m2_reuse_names:continue\n if n in deferred_whole_names:", 'hard skip every linked source before dispatch or artifact handling')
replace(" audit=n.endswith('.lean');m={'file':str(dest/n),'module':n} if audit else modules[n]\n file=Path(m['file']);relative=file.relative_to(dest)", """ assert n not in m2_reuse_names and n!=m2_own_prior_pilot_name,'Protected prior-own source must never dispatch'
 assert n in m2_required_new_names or n in m2_allowed_scoped_audits,'Only3 cold sources and one four-print audit may dispatch'
 audit=n.endswith('.lean');m={'file':str(dest/n),'module':n} if audit else modules[n]
 file=Path(m['file']);relative=file.relative_to(dest)
 protected_candidates=[file.with_suffix(s).resolve() for s in ['.olean','.olean.private','.olean.server','.ilean']]
 assert not any(p in m2_protected_output_paths for p in protected_candidates),'Cannot overwrite or rename a protected linked/pilot output'""", 'hard no-write/no-rename guard on all artifact candidates before partial-output manipulation')
replace("prefix=BASE/'guarded-source-logs'/(project+'-m2-granular-'+logkey+'-attempt-'+str(len(plan.get('prior_attempt_receipts',[]))))", "prefix=BASE/'guarded-source-logs'/(project+'-linked-granular-'+logkey+'-attempt-'+str(len(plan.get('prior_attempt_receipts',[]))))", 'separate guard log namespace')
replace("plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());plan.pop('current_module',None);save();print('PROJECT_STATUS',project,plan['status'],flush=True)", '''m2_final_identity_check=m2_verify_seed(M2_LINK_POLICY_SHA256,m2_seed_sha)
plan['final_reused_link_and_independent_pilot_identity_check']=m2_final_identity_check
actual_new_rows=[r for r in plan['builds'] if not r.get('is_endpoint_audit')]
assert all(r['module'] in m2_required_new_names for r in actual_new_rows)
actual_passes={r['module'] for r in actual_new_rows if r['exit']==0 and not r.get('stop_reason')}
actual_audits=[r for r in plan['builds'] if r.get('is_endpoint_audit')]
assert all(r['module'] in m2_allowed_scoped_audits for r in actual_audits)
scoped_complete=(actual_passes==m2_required_new_names and len(actual_audits)==1 and actual_audits[0]['exit']==0
 and actual_audits[0].get('selected_endpoint_print_coverage',{}).get('status')=='PASS'
 and not plan.get('selected_endpoint_uses_sorry') and not plan.get('selected_unrecognized_axioms')
 and not plan.get('selected_incomplete_print_audits'))
plan['granular_scope_qualification']={'status':('PASS_SCOPED_GRANULAR_WITH_NATIVE_EVALUATION' if plan.get('selected_native_evaluation') else 'PASS_SCOPED_GRANULAR_STANDARD_AXIOMS') if scoped_complete else 'INCOMPLETE_OR_UNQUALIFIED',
 'prior_own_DMS_cold_sources_reused':97,'independent_existing_M2_pilot_sources':1,
 'new_actual_current_cold_source_passes':len(actual_passes),'required_new_current_cold_sources':3,
 'scoped_selected_prints_required':4,'actual_selected_axiom_rows':plan['selected_audit_axiom_review'],
 'full122_project_PASS':False,'whole21_authored_sources_attempted':False,
 'qualification':'A granular exact101-body route consisting of97 previous-owned cold checks, one independent earlier M2 pilot and3 actual new source checks. Every whole-scope theorem/audit remains deferred; no novelty, score or placement consequence follows.'}
assert all(r['module'] not in deferred_whole_names for r in plan['builds'])
assert plan['status'] not in ['PASS','PASS_WITH_NATIVE_EVALUATION','PASS_SELECTED_ENDPOINTS_WITH_UNFINISHED_BASELINES'],'Cannot mark full frozen122-source project PASS on a granular-only route'
plan['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());plan.pop('current_module',None);save();print('PROJECT_STATUS',project,plan['status'],flush=True)''', 'final immutable alias/pilot recheck and route-qualified granular verdict never full PASS')
ast.parse(source); ast.parse(HELPER.read_text(encoding='utf8'))
with RUNNER.open('x', encoding='utf8', newline='\n') as stream: stream.write(source)
with DIFF.open('x', encoding='utf8', newline='\n') as stream:
    stream.write(''.join(difflib.unified_diff(original.splitlines(True), source.splitlines(True),
      fromfile=BASELINE.name, tofile=RUNNER.name)))
packet = {'status':'PREPARED_CONCRETE_EXACT97_REUSE_HELPER_AND_SEPARATE_GUARDED_RUNNER_NO_LINK_NO_LEAN',
 'prepared_utc':datetime.now(timezone.utc).isoformat(),
 'baseline_runner':str(BASELINE),'baseline_runner_sha256':digest(BASELINE),
 'prepared_runner':str(RUNNER),'prepared_runner_sha256':digest(RUNNER),
 'full_runner_diff':str(DIFF),'full_runner_diff_sha256':digest(DIFF),
 'reviewed_changes':changes,'seed_helper':str(HELPER),'seed_helper_sha256':digest(HELPER),
 'policy':str(POLICY),'policy_sha256':digest(POLICY),
 'complete_official_closure':policy['complete_official_closure'],
 'complete_official_closure_sha256':policy['complete_official_closure_sha256'],
 'official_closure_count':policy['official_closure_count'],'official_closure_identity_counts':policy['official_closure_identity_counts'],
 'frozen_plan_sha256':policy['source_plan_sha256'],
 'source_scope_counts':policy['source_scope_counts'],
 'original_DMS119_receipt_sha256':policy['original119_receipt_sha256'],
 'independent_M2_StarCore_pilot_receipt_sha256':policy['M2_StarCore_pilot_sha256'],
 'strict_resource_policy':{'worker_threads':1,'dispatch_disk_bytes':4_000_000_000,
   'dispatch_physical_bytes':6*2**30,'dispatch_available_commit_bytes':5*2**30,
   'own_Windows_job_private_limit_bytes':6*2**30,'continuous_disk_floor_bytes':1_000_000_000,
   'continuous_physical_floor_bytes':3*2**30,'continuous_commit_floor_bytes':1*2**30,
   'guarded_tree_and_semantic_compiler_options_unchanged':True},
 'actual_actions':{'metadata_and_separate_scripts_created':True,'baseline_runner_changed':False,
   'current_original_DMS_or_M2_receipts_changed':False,'hard_links_created':0,'artifacts_copied':0,
   'Lean_or_compiler_invocations':0,'existing_frozen_plan_or_source_edits':0},
 'AST_syntax_checks':'PASS_ONLY_NO_SCRIPT_EXECUTION',
 'required_next_review':'Root must review exact helper/policy/full runner diff; M2 links must wait for completed DMSv2 qualification and released exact link-count lock. Then separately approve exact97 seed; independently verify concrete seed before approving new3 source/four-print execution with an actual resource lease.',
 'example_future_invocation_NOT_AUTHORIZATION':'Python run_htpeo_m2_linked_granular_plan.py htpeo-erdos-m2 1 --m2-granular-execution-authorized --resource-lease-confirmed --defer-whole-imports --guarded-third-slot --htpeo-m2-reuse-execution-authorized --reuse-execution-approval <reviewed-approval.json> --reuse-execution-approval-sha256 <sha> --reuse-seed-receipt-sha256 <sha>',
 'qualification':'Prepared conditional route only. No actual source/audit run or full project PASS, no mathematical priority/novelty/score upgrade.'}
sha = new_json(PACKET, packet)
assert digest(BASELINE)==BASELINE_SHA
print(json.dumps({'packet':str(PACKET),'packet_sha256':sha,'runner_sha256':digest(RUNNER),
 'policy_sha256':policy_sha,'helper_sha256':helper_sha,'diff_sha256':digest(DIFF),
 'hard_links_created':0,'Lean_invocations':0}),flush=True)
