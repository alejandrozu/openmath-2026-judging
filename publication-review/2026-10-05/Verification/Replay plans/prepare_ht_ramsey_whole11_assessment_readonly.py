"""Metadata-only future HT whole-route assessment; no project imports or processes."""
from pathlib import Path
import hashlib, json, re
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parent
DEST = BASE / 'builds/htpeo-ramsey-current'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def bound(p): return {'file': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def load(p): return json.loads(p.read_text(encoding='utf8'))

plan_file = DEST / 'build-plan.json'
plan = load(plan_file)
assert sha(plan_file) == '94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
graph_file = BASE / 'proposals/htpeo-ramsey-current-original-provider-recheck-20261005/exact-original2103-sources-and-import-graph.json'
graph = load(graph_file)
G = {r['module']: r for r in graph}
M = {r['module']: r for r in plan['modules']}
assert len(G) == len(M) == 2103 and set(G) == set(M)
for n, m in M.items():
    assert sha(Path(m['file'])) == m['sha256'] == G[n]['source_sha256'], n
evidence_file = BASE / 'ht-ramsey-mixed-source-boundary-evidence.json'
evidence = load(evidence_file)
whole = {r['module'] for r in evidence['whole_authored_modules']}
assert len(whole) == 11
granular = set(M) - whole
assert len(granular) == 2092

seen, ordered = set(), []
def visit(n):
    if n in seen: return
    seen.add(n)
    for dep in G[n]['custom_imports']: visit(dep)
    ordered.append(n)
for n in M: visit(n)
def closure(roots):
    reached = set()
    def rec(n):
        if n in reached: return
        reached.add(n)
        for d in G[n]['custom_imports']: rec(d)
    for n in roots: rec(n)
    return [n for n in ordered if n in reached]

original = DEST / 'FreshAudit1.lean'
supplement = DEST / 'FreshAuditSupplement.lean'
assert sha(original) == 'dff144f1890c6c255e9463a7e1fa29284166684ae96289b7949f1a363c6e9868'
assert sha(supplement) == '4c570ea840ac2283717a34b5f83294def83edd27a056ad747cf60f273f91a80d'
typed_file = BASE / 'proposals/htpeo-ramsey-current-original-provider-recheck-20261005/all24-exact-typed-statements-and-preserved-audits.json'
typed = load(typed_file)
mappings = typed['typed_mappings']
assert len(mappings) == 24
requests = lambda p: re.findall(r'^\s*#print\s+axioms\s+(\S+)', p.read_text(encoding='utf8'), re.M)
original_requests, supplement_requests = requests(original), requests(supplement)
assert len(original_requests) == len(supplement_requests) == len(set(supplement_requests)) == 24
assert original_requests == [r['original_requested_name'] for r in mappings]
assert supplement_requests == [r['fully_qualified_name'] for r in mappings]
audit_roots = {'FreshAudit1.lean': ['RamseyCert'], 'FreshAuditSupplement.lean': ['RamseyCert.Final', 'RamseyCert.Native']}
audit_closures = {n: closure(roots) for n, roots in audit_roots.items()}
selected = []
for r in mappings:
    p = Path(r['declaration_source'])
    assert sha(p) == r['declaration_source_sha256'] == M[r['declaration_module']]['sha256']
    selected.append({**r,
        'original_request_is_namespace_qualified': r['original_requested_name'].startswith('RamseyCert.'),
        'declaration_module_reachable_from_original_audit': r['declaration_module'] in audit_closures['FreshAudit1.lean'],
        'declaration_module_reachable_from_supplement': r['declaration_module'] in audit_closures['FreshAuditSupplement.lean'],
        'actual_endpoint_axioms_observed_by_this_assessment': False})
assert all(r['declaration_module_reachable_from_supplement'] for r in selected)

runner = BASE / 'run_htpeo_ramsey_supplemented_plan.py'
assert sha(runner) == 'b0293550ae7afaf65c1a0bd03c543d39213de48b4523aa4568547c1a1f78518a'
runtime = BASE / 'runtimes/lean-4.33.1-windows/bin/lean.exe'
immutable138 = BASE / 'ht-ramsey-kernel-j2-continuation-20261005T075820161512Z-immutable-boundary.json'
assert sha(immutable138) == '91ac7d8306ea4640f4a126c1bf1aa4ed4b16c16a46cdfabeb768b7f21c66c88c'
prior = load(immutable138)
assert len(prior['builds']) == 138
prior_flags = {flag: sum(flag in r['command'] for r in prior['builds']) for flag in ['-j1', '-j2']}
assert prior_flags == {'-j1': 135, '-j2': 3}

producer = bound(Path(__file__))
bindings = {n: bound(BASE / n) for n in [
    'run_htpeo_ramsey_supplemented_plan.py', 'full_mathlib_resource_guard.py',
    'full_mathlib_scope.py', 'audit_axioms.py', 'lean_imports.py', 'receipt_io.py',
    'native_resource_guard.py', 'resource_metrics.py',
    'htpeo-ramsey-supplemental-audit-materialization-2026-10-05.json',
    'htpeo-ramsey-supplemental-runner-preparation-20261005.json',
    'proposals/htpeo-ramsey-current-original-provider-recheck-20261005/complete-official-source-and-all-present-artifact-closure.json',
    'proposals/held-original-granular-source-review/htpeo-ramsey-supplemental-audit-custom-import-closure.json']}
bindings.update(plan=bound(plan_file), original2103_graph=bound(graph_file),
    whole_boundary=bound(evidence_file), typed24_statements=bound(typed_file),
    original_audit=bound(original), supplemental_audit=bound(supplement),
    immutable138_context=bound(immutable138), runtime=bound(runtime))
python = 'C:/Users/Propietario/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
args = [python, '-X', 'utf8', str(runner), 'htpeo-ramsey-current', '1',
    '--guarded-third-slot', '--full-mathlib-source-mode', '--with-reviewed-supplemental-audit']
pilot_args = [a if a != '--guarded-third-slot' else '--pilot-third-slot' for a in args]
policy = {'cli_worker_flag': '-j1', 'LEAN_NUM_THREADS': '1',
    'initial_disk_bytes': 4_000_000_000, 'initial_physical_bytes': 6 * 2**30,
    'initial_available_commit_bytes': 11 * 2**30,
    'continuous_disk_bytes': 1_000_000_000, 'continuous_physical_bytes': 3 * 2**30,
    'continuous_available_commit_bytes': 1 * 2**30,
    'own_job_private_bytes': 10 * 2**30, 'own_process_private_bytes': 10 * 2**30,
    'timeout_seconds_per_invocation': 3600,
    'global_source_importers': 1, 'other_Lean_compilers_at_dispatch': 0}
whole_records = []
for n in ordered:
    if n not in whole: continue
    c = closure([n])
    whole_records.append({'module': n, 'source': bound(Path(M[n]['file'])),
        'literal_imports': G[n]['literal_source_imports'],
        'direct_custom_imports': G[n]['custom_imports'],
        'whole_custom_predecessors': [d for d in c if d in whole and d != n],
        'granular_prerequisite_count': sum(d in granular for d in c),
        'full_custom_closure_count': len(c),
        'custom_closure_names_sha256': hashlib.sha256(json.dumps(c).encode()).hexdigest(),
        'static_token_counts_from_exact_source_graph': G[n]['static_token_counts'],
        'explicit_custom_axiom_declarations_from_exact_source_graph': G[n]['custom_axiom_declarations'],
        'static_native_sites': G[n]['exact_native_rows']})

assessment = {'status': 'READ_ONLY_PREPARED_FUTURE_SCOPE_NO_DISPATCH_NO_CURRENT_RESULT',
    'prepared_utc': datetime.now(timezone.utc).isoformat(), 'producer': producer,
    'bindings': bindings, 'entrant': plan['entrant'], 'entrant_commit': plan['commit'],
    'Lean_version': plan['version'], 'Mathlib_pin': plan['mathlib_pin'], 'semantic_lean_options': plan['lean_options'],
    'immutable_context_only': {'prior_source_count': 138, 'literal_prior_flags': prior_flags,
        'actual_future2092_receipt_not_read_or_available_here': True,
        'live_canonical_not_read': True, 'active_controller_not_imported_or_changed': True},
    'existing_runner_compatible_without_code_change': True,
    'future_required_actual_successful_granular_names': [n for n in ordered if n in granular],
    'future_new_source_count': 11, 'future_new_audit_count': 2,
    'exact_whole_source_topological_order': [r['module'] for r in whole_records],
    'whole_sources': whole_records,
    'selected24_endpoint_declarations_and_exact_scope': selected,
    'audit_custom_dependency_closures': {n: {'roots': audit_roots[n], 'count': len(c),
        'whole_count': sum(d in whole for d in c), 'modules': c,
        'excluded_source_modules': [d for d in ordered if d not in c]} for n, c in audit_closures.items()},
    'static_original_audit_concerns_not_actual_failure': {
        'unqualified_requests_inside_RamseyCert_namespace_without_local_open': [r['original_requested_name'] for r in selected if not r['original_request_is_namespace_qualified']],
        'requests_whose_declaration_module_is_not_imported': [r['original_requested_name'] for r in selected if not r['declaration_module_reachable_from_original_audit']],
        'original_audit_has_not_been_executed_by_this_assessment': True,
        'no_invented_exit_code_diagnostic_or_failure_count': True,
        'required_behavior': 'Attempt the unchanged original audit once after actual prerequisite closure and preserve all raw diagnostics/prints. Then separately attempt unchanged supplement; no entrant source, original audit, or plan edits.'},
    'runner_control_findings': [
        'Full mode requires actual frozen direct Mathlib roots, exact HT11 set/source hashes and all2092 prior exit0/no-stop rows. It requires ht_ramsey_whole_scope_only_authorized=true in the source-plan-bound lease.',
        'The retained-row path checks original relative source and -o but has no j1-only historical assertion. Prior literal mixed j1/j2 commands, logs, guards and artifact hashes are preserved by module; canonical list is rebuilt topologically, so compare by module instead of chronological prefix.',
        'Actual retained artifacts must exactly equal prior inventory. The raw previous checkpoint is copied byte-identically to a new numbered attempt before canonical replacement.',
        'Dispatch loop is the complete topological source order followed by original FreshAudit1.lean then FreshAuditSupplement.lean. After all2092 are retained, exactly11 authored sources and both audits remain.',
        'An ordinary original audit exit!=0 is retained in failed_invocations and continuation proceeds to the supplement. Final status remains BUILD_FAILED_OR_TIMED_OUT even if the supplement has24 clean prints. This is correct raw provenance; a future separate selected-scope composite qualification must disclose the original audit defect.',
        'Successful supplement is parsed for all24 requested prints, missing coverage, sorryAx, unrecognized/native axioms. An unsuccessful original audit is not parsed by the runner, so its actual partial prints still need additive raw analysis.',
        'The existing per-project lock and exclusive whole lock are necessary but do not census other granular workers. Root sole scheduling and current no-other-Lean proof remain mandatory.',
        'hold-third-worker-dispatch naturally checkpoints this runner too. Root must first establish/drain all other dispatchers under a global hold, then explicitly coordinate this sole holder before removing only the hold that would stop it. No other scheduler may resume during the lease.',
        'No exact future2092 canonical SHA, .json.tmp absence, full nine dependency HEAD/origin snapshot or global process identity is enforced by this runner alone. Root preflight must bind these before dispatch.',
        'A genuine failed source is retained and not retried automatically; later independent sources/audits can produce import failures. Resource roots/unfinished output bytes remain environmental, never a proof rejection or successful pass.',
    ],
    'source_and_theorem_trust_exclusions': {
        'kernel_proof_scope': 'All2048 original chunk modules use three decide +kernel certificates each; finite symmetry checks use decide +kernel. Static syntax is not a substitute for actual selected endpoint axioms.',
        'native_crosscheck_only_selected_names': ['RamseyCert.native_fastK_B', 'RamseyCert.native_fastK_R'],
        'native_exact_source': bound(DEST / 'RamseyCert/Native.lean'),
        'Native_module_proof_bodies': 'Two native_decide computations in RamseyCert.Native; retain compiler/runtime/GMP trust labels after actual matching prints. Do not claim all24 are standard kernel.',
        'general_and_kernel_bound_import_exclusion': 'Final/Main do not import Native. The bound proof source route remains distinct from separate native cross-checks, but actual22 other print outputs must still be examined.',
        'no_source_or_score_change': True,
        'no_novelty_priority_event_placement_or_publication_conclusion': True,
        'potential_operational_cost': 'Native.fastK crosschecks and whole import mapping/Glue assembly may be costly. Fixed3600s per invocation remains; timeouts/allocation limits are preserved as bounded attempts, not guessed mathematical failures.'},
    'future_guard_policy_unchanged': policy,
    'future_full_scope_command_template': args, 'optional_separately_root_approved_first_Fast_source_pilot_command': pilot_args,
    'future_external_root_checks_required': [
        'Exact quiescent2092 finished raw checkpoint and additive artifact/CLI/source qualification; source matches all2103 original SHA; all retained sibling artifacts unchanged and all11 future outputs cold or specifically attributed.',
        'No live old HT/controller/serial process, no other Lean/native/Lake worker, natural source-boundary parent exit, no orphan compiler and no leftover canonical .json.tmp. All other dispatchers held or finished with dated identity records.',
        'Exact reviewedb029 runner/all helper bytes, pinned4.33.1 runtime version+SHA, nine genuine dependency HEAD+origin/manifest and whole official source/artifact closure/cache validation rechecked; current historical manifests are not a new verification.',
        'Separate root authorization binding exact11 sources and both literal audit SHAs, original audit preserved,24 supplement requests, no source-body/options edit and maximum one source compiler globally.',
        'New source-plan-bound full lease holder HT, explicit ht_ramsey_whole_scope_only_authorized true, all other importers confirmed inactive, fresh11GiB commit/6GiB physical/4GB disk and unchanged continuous/job caps; do not reuse stale lease.',
        'Global hold/drain/exclusive-lock handoff performed by root without terminating user apps or changing system resources. No sidecar, A000, E65, other Mathlib or kernel worker overlaps this sole route.'
    ],
    'mutation_scope': 'Only this producer and two new preparation JSON files. No existing runner/source/plan/audit/canonical/hold/lease/output/alias edit; no existing project/guard imports, process census or compiler invocation.'}

out = BASE / 'ht-ramsey-eleven-whole-both-audits-existing-runner-assessment-20261005.json'
assert not out.exists()
out.write_text(json.dumps(assessment, ensure_ascii=False, indent=2), encoding='utf8')
template = {'status': 'INACTIVE_TEMPLATE_ONLY_NO_DISPATCH_AUTHORIZATION',
    'assessment': bound(out), 'prepared_utc': assessment['prepared_utc'],
    'holder_project': 'htpeo-ramsey-current', 'source_plan_sha256': sha(plan_file),
    'ht_ramsey_whole_scope_only_authorized': None,
    'other_umbrella_compilers_confirmed_held_or_finished': None,
    'all_other_source_native_Lake_compilers_confirmed_inactive': None,
    'reviewed_runner_sha256': sha(runner), 'reviewed_whole_guard_sha256': sha(BASE/'full_mathlib_resource_guard.py'),
    'actual_finished2092_boundary_receipt_file': 'REQUIRES_FUTURE_ROOT_BOUNDARY',
    'actual_finished2092_boundary_receipt_sha256': 'REQUIRES_FUTURE_ROOT_BOUNDARY',
    'actual_finished2092_source_output_qualification_sha256': 'REQUIRES_FUTURE_ROOT_REVIEW',
    'actual_zeroOtherLean_and_natural_dispatcher_exit_record_sha256': 'REQUIRES_FUTURE_ROOT_SNAPSHOT',
    'current_global_hold_drain_and_sole_handoff_record_sha256': 'REQUIRES_FUTURE_ROOT_HANDOFF',
    'root_exact11_plus_original_and_supplement24_scope_approval_sha256': 'REQUIRES_FUTURE_ROOT_APPROVAL',
    'current_runtime9dependencies_fullcache_recheck_sha256': 'REQUIRES_FUTURE_ROOT_RECHECK',
    'actual_dispatch_resource_snapshot': None, 'maximum_global_source_importers': 1,
    'whole_source_order': [r['module'] for r in whole_records],
    'new_authored_sources': 11, 'new_audits': ['FreshAudit1.lean', 'FreshAuditSupplement.lean'],
    'original_audit_source_sha256': sha(original), 'supplement24_source_sha256': sha(supplement),
    'supplement24_requests': supplement_requests, 'guard_policy': policy,
    'future_command': args,
    'scope_note': 'Template fields do not confer approval. Preserve all2092 mixed literal prior rows; all2103 source coverage and selected24 classification require actual completion and additive review. Any real original audit failure remains visible even with a successful supplement.'}
template_file = BASE / 'ht-ramsey-eleven-whole-both-audits-inactive-sole-lease-template-20261005.json'
assert not template_file.exists()
template_file.write_text(json.dumps(template, ensure_ascii=False, indent=2), encoding='utf8')
print(json.dumps({'assessment': bound(out), 'inactive_template': bound(template_file),
    'source_count': 2103, 'whole_count': 11, 'required_granular': 2092,
    'audit_closure_counts': {n: len(c) for n,c in audit_closures.items()},
    'original_unqualified_requests': sum(not r['original_request_is_namespace_qualified'] for r in selected),
    'original_out_of_import_scope_requests': sum(not r['declaration_module_reachable_from_original_audit'] for r in selected)}, indent=2))
