"""Read-only additive qualification of the exact finished177 HT checkpoint.

No project/guard imports, compiler calls, canonical writes or scheduling changes.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

BASE = Path(__file__).resolve().parent
STAGE = BASE / 'builds/htpeo-ramsey-current'
REPORT = BASE / 'htpeo-ramsey-current-fresh-build.json'
EXPECTED177 = '5b827c653d1a07d5de5e8486a6451b33782a5a0b8788625d8fe10ac4b852ed6e'
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def bind(p):
    p = Path(p)
    return {'file': str(p), 'sha256': digest(p), 'bytes': p.stat().st_size}
def load(p): return json.loads(Path(p).read_bytes())
raw = REPORT.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED177
current = json.loads(raw)
priorfile = BASE/'ht-ramsey-kernel-j2-continuation-20261005T075820161512Z-immutable-boundary.json'
assert digest(priorfile) == '91ac7d8306ea4640f4a126c1bf1aa4ed4b16c16a46cdfabeb768b7f21c66c88c'
prior = load(priorfile)
assert len(current['builds']) == 177 and len(prior['builds']) == 138
assert current['builds'][:138] == prior['builds'], 'Literal138 row prefix changed'
assert current['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT' and current['finished_utc'] == '2026-10-05T08:17:14.160919+00:00'
assert not current.get('failed_invocations') and not any(r['is_endpoint_audit'] for r in current['builds'])
assert not REPORT.with_suffix('.json.tmp').exists()
planfile = STAGE/'build-plan.json'
assert digest(planfile) == '94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
plan = load(planfile)
assert current['modules'] == plan['modules'] and plan['lean_options'] == current['lean_options'] == {}
entries = {r['module']: r for r in plan['modules']}
assert len(entries) == 2103
source_checks = []
for n, m in entries.items():
    p = Path(m['file'])
    assert p.resolve().is_relative_to(STAGE.resolve()) and digest(p) == m['sha256'], n
    source_checks.append({'module': n, 'source': bind(p)})

controller = BASE/'run_ht_ramsey_kernel_j2_continuation_prepared.py'
approvalfile = BASE/'root-HT-actual138-remaining1945-one-j2-with-A000-actual-dispatch-approval-20261005.json'
assert digest(controller) == 'e551e318748425f8672e73e670aaddda6533af58facefc0ebbef229bf42c6a23'
assert digest(approvalfile) == '79a16440b12a6050ca311d3d7ddf513e414bd4e919f5f326563ca87bc3a86a5f'
approval = load(approvalfile)
assert approval['status'] == 'ROOT_APPROVED_HT_RAMSEY_REMAINING_KERNELS_ONE_J2_WITH_OPTIONAL_BOUND_A000'
assert approval['maximum_own_parallel_kernel_jobs'] == 1 and approval['maximum_total_global_Lean_importers'] == 2
assert approval['maximum_new_sources_this_lease'] == 1945 and approval['endpoint_audit_invocations_this_lease'] == 0
assert approval['allowed_A000_dispatcher_identity'] == {
    'pid': 55864, 'created_utc': '2026-10-05T07:52:08.7785550Z',
    'command_utf8_sha256': '31f7ab879d4c113b46edf9c44c04d7f7763a617359a9176270450dae67145bf5',
    'reviewed_dispatcher_source_sha256': 'd73aa5d2218f358e79d5479de20b5082b345a994d0d4dd35d0a23516876eda28'}
manifestfile = BASE/'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
assert digest(manifestfile) == approval['reviewed_kernel_source_manifest_sha256'] == '2c5963c0b5c5094b77206b80d9e02866a504d56991459a2f0ec3bacef147da15'
manifest = load(manifestfile)
kernel = {r['module']: r for r in manifest['kernel_sources']}
assert len(kernel) == 2048
new = current['builds'][138:]
assert [r['module'] for r in new] == ['RamseyCert.Chunk.R'+str(i) for i in range(102,141)]
assert [r['module'] for r in new] == approval['exact_current_remaining_kernel_names'][:39]
lean = BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
assert digest(lean) == 'af49bacfabaa1fea71332ca0feae0fa1a60912219d5902291adc79f905bffb8d'
assert plan['version'] == '4.33.1' and plan['mathlib_pin'] == '0df444a360eaa60ab8c11dca51a86af692955474'
helper_expected = {
    'matt_resource_guard.py': 'ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71',
    'native_resource_guard.py': '0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4',
    'resource_metrics.py': '1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed',
    'ht-ramsey-kernel-j2-continuation-preparation-20261005.json': 'abc3a76dbe912a2f9182a391f2dc593b36609348e392dc18f1a50672decabfe9',
    'ht-ramsey-kernel-j2-continuation-readonly-peer-review-20261005.json': 'b1b607e98fb8a51d98f89b6e3a48b0c1f0d3e6293d98a6acbfdc8e6b2a6ee821'}
for n,h in helper_expected.items(): assert digest(BASE/n) == h, n
cachefile = BASE/'mathlib-4.33.1-cache-retry.json'
lakefile = BASE/'dependencies/4.33.1/mathlib/lake-manifest.json'
gitfile = BASE/'dependencies-4.33.1-verified-git.json'
assert digest(cachefile) == approval['reviewed_official_cache_receipt_sha256'] and load(cachefile)['status'] == 'PASS'
assert digest(lakefile) == approval['reviewed_official_lake_manifest_sha256']
assert digest(gitfile) == approval['reviewed_exact_nine_dependency_git_record_sha256']
assert len(load(gitfile)) == 9

artifact_checks = []
for row in current['builds']:
    n = row['module']; source = Path(entries[n]['file'])
    assert row['source_sha256'] == entries[n]['sha256'] and row['exit'] == 0 and not row.get('stop_reason')
    expected_paths = {p.resolve() for p in [source.with_suffix(s) for s in ['.olean','.olean.private','.olean.server','.ilean']] if p.exists()}
    assert expected_paths == {Path(a['file']).resolve() for a in row['artifacts']}
    assert source.with_suffix('.olean').exists()
    for a in row['artifacts']:
        p = Path(a['file']); assert p.resolve().is_relative_to(STAGE.resolve())
        assert digest(p) == a['sha256'] and p.stat().st_size == a['bytes'], n
    assert not source.with_suffix('.ir').exists(), 'Unexpected unrecordedIR sibling: '+n
    artifact_checks.append({'module': n, 'source_sha256': row['source_sha256'],
        'artifacts': row['artifacts'], 'row_canonical_json_sha256': hashlib.sha256(json.dumps(row,sort_keys=True,ensure_ascii=False).encode()).hexdigest()})

POLICY = {'initial_disk_bytes': 4_000_000_000, 'initial_physical_bytes': 6*2**30,
    'initial_available_commit_bytes': 5*2**30, 'continuous_disk_bytes': 1_000_000_000,
    'continuous_physical_bytes': 3*2**30, 'continuous_available_commit_bytes': 1*2**30,
    'own_job_private_bytes': 6*2**30, 'own_process_private_bytes': 6*2**30,
    'poll_seconds': .25, 'timeout_seconds': 3600}
new_checks = []
for row in new:
    n = row['module']; p = Path(entries[n]['file']); relative = p.relative_to(STAGE)
    command = [str(lean),'-j2','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(relative.with_suffix('.olean')),str(relative)]
    assert row['command'] == command
    assert row['explicit_lean_shell_worker_flag'] == '-j2' and row['exact_LEAN_NUM_THREADS'] == '2'
    assert row['executed_parallel_controller_source_sha256'] == digest(controller)
    assert row['approved_parallel_worker_count'] == 1 and row['maximum_new_sources_this_lease'] == 1945
    guard = row['own_job_resource_receipt']
    assert guard['command'] == command and Path(guard['cwd']).resolve() == STAGE.resolve()
    assert guard['resource_policy'] == POLICY and guard['attempted'] is True
    assert guard['own_job_assignment_before_resume'] == 'PASS' and guard['state'] == 'PASS' and guard['exit'] == 0
    assert guard['counter_helper_sha256'] == helper_expected['native_resource_guard.py']
    assert guard['commit_counter_helper_sha256'] == helper_expected['resource_metrics.py']
    assert row['started_utc'] == guard['started_utc'] and row['finished_utc'] == guard['finished_utc']
    assert row['seconds'] == guard['seconds'] and row['minimum_free_bytes'] == guard['minimum_disk_free_bytes']
    assert guard['minimum_disk_free_bytes'] >= POLICY['continuous_disk_bytes']
    assert guard['minimum_physical_available_bytes'] >= POLICY['continuous_physical_bytes']
    assert guard['minimum_available_commit_bytes'] >= POLICY['continuous_available_commit_bytes']
    assert guard['job_peak_process_private_bytes'] <= POLICY['own_process_private_bytes']
    assert guard['job_peak_aggregate_private_bytes'] <= POLICY['own_job_private_bytes']
    assert guard['initial_system_memory_snapshot']['free_physical_bytes'] >= POLICY['initial_physical_bytes']
    assert guard['initial_system_memory_snapshot']['available_commit_bytes'] >= POLICY['initial_available_commit_bytes']
    logs = {}
    for kind in ['stdout','stderr']:
        logfile = Path(guard[kind+'_file'])
        assert logfile.resolve().is_relative_to(BASE.resolve()) and digest(logfile) == guard[kind+'_sha256']
        assert logfile.read_text(encoding='utf8',errors='replace') == row[kind] == '', n
        logs[kind] = bind(logfile)
    item = kernel[n]
    assert item['source_sha256'] == row['source_sha256'] and not set(item['entire_custom_prerequisite_closure']) & set(kernel)
    passed = {r['module'] for r in current['builds']}
    assert set(item['entire_custom_prerequisite_closure']) <= passed
    new_checks.append({'module': n, 'exact_command': command, 'exact_LEAN_NUM_THREADS': '2',
        'source_sha256': row['source_sha256'], 'logs': logs, 'guard': guard,
        'artifacts': row['artifacts'], 'selected_endpoint_audit_invoked': False})

passed = {r['module'] for r in current['builds']}
assert len(passed) == 177
pending = [n for n in current['compilation_order'] if n in kernel and n not in passed]
assert len(pending) == 1906 and pending == current['parallel_kernel_pending_names_not_attempted']
assert pending == approval['exact_current_remaining_kernel_names'][39:]
for n in pending:
    p = Path(entries[n]['file'])
    assert not any(p.with_suffix(s).exists() for s in ['.olean','.olean.private','.olean.server','.ilean','.ir']), n
whole_file = BASE/'ht-ramsey-mixed-source-boundary-evidence.json'
whole = {r['module'] for r in load(whole_file)['whole_authored_modules']}
assert len(whole) == 11 and not whole & passed
tail = {n for n in entries if n not in kernel and n not in whole and n not in passed}
assert tail == {'RamseyCert.SymDefs'} | {'RamseyCert.SymChk'+str(i) for i in range(8)}
assert set(entries)-passed == set(pending)|tail|whole
assert current['kernel_j2_continuation_new_sources_attempted'] == 39
assert current['resource_settings']['LEAN_NUM_THREADS'] == '2' and current['resource_settings']['lean_shell_worker_flag'] == '-j2'
assert digest(REPORT) == EXPECTED177, 'Canonical changed during read-only review'

immutable = BASE/'ht-ramsey-actual177-mode1-j2-natural-checkpoint-immutable-20261005.json'
assert not immutable.exists(); immutable.write_bytes(raw); assert digest(immutable) == EXPECTED177
resource_totals = {'actual_new_source_seconds_sum': sum(r['seconds'] for r in new),
    'actual_new_source_seconds_min': min(r['seconds'] for r in new),
    'actual_new_source_seconds_max': max(r['seconds'] for r in new),
    'maximum_owned_job_private_bytes': max(r['own_job_resource_receipt']['job_peak_aggregate_private_bytes'] for r in new),
    'maximum_owned_process_private_bytes': max(r['own_job_resource_receipt']['job_peak_process_private_bytes'] for r in new),
    'minimum_disk_free_bytes': min(r['own_job_resource_receipt']['minimum_disk_free_bytes'] for r in new),
    'minimum_physical_available_bytes': min(r['own_job_resource_receipt']['minimum_physical_available_bytes'] for r in new),
    'minimum_available_commit_bytes': min(r['own_job_resource_receipt']['minimum_available_commit_bytes'] for r in new)}
out = {'status': 'QUALIFIED_PARTIAL177_SOURCE_CHECKPOINT_NO_MAIN24_AUDIT_UPGRADE',
    'checked_utc': datetime.now(timezone.utc).isoformat(), 'producer': bind(Path(__file__)),
    'immutable_actual177': bind(immutable), 'preserved138': bind(priorfile),
    'original2103_plan': bind(planfile), 'executed_controller': bind(controller),
    'actual_mode1_root_approval': bind(approvalfile),
    'reviewed_controller_preparation': bind(BASE/'ht-ramsey-kernel-j2-continuation-preparation-20261005.json'),
    'reviewed_controller_peer': bind(BASE/'ht-ramsey-kernel-j2-continuation-readonly-peer-review-20261005.json'),
    'pinned_runtime': bind(lean), 'unchanged_guard_helpers': {n: bind(BASE/n) for n in helper_expected if n.endswith('.py')},
    'official_cache_receipt': bind(cachefile), 'official_lake_manifest': bind(lakefile), 'exact_nine_dependency_record': bind(gitfile),
    'dependency_qualification': 'Current recorded runtime/helper/cache/manifest/nine-pin metadata hashes match actual root-approved replay. No newGitprocess or full official-provider byte rehash executed by this qualification.',
    'all2103_original_source_identity_checks': source_checks,
    'all177_owned_artifact_identity_checks': artifact_checks,
    'preserved_literal138_prefix_exact': True,
    'literal_total_command_counts': {f: sum(f in r['command'] for r in current['builds']) for f in ['-j1','-j2']},
    'new39_exact_source_guard_log_artifact_checks': new_checks,
    'new39_j2_env2_sourceonly_allPASS': True, 'new39_resource_totals': resource_totals,
    'source_partial_scope': {'actual_total_sources_PASS': 177, 'shared_prerequisite_sources_PASS': 35,
        'actual_kernel_sources_PASS': 142, 'all_kernel_sources': 2048,
        'remaining_kernel_count': 1906, 'remaining_kernel_order': pending,
        'remaining_nine_granular_sources': sorted(tail), 'remaining_eleven_whole_sources': sorted(whole),
        'remaining_total_authored_sources': 1926},
    'main_selected_audit_status': 'UNCHANGED24_ORIGINAL_AND24_SUPPLEMENT_BOTH_UNRUN',
    'trust_scope': 'New39 unchanged original finite certificate sources compiled with-j2/env2 and explicitdecide+kernel bodies. No native proof or selected main24audit executed here; actualR99/R100/R101 selected audits remain separately qualified in preserved root evidence, not extended to new39.',
    'score_novelty_publication_upgrade': False,
    'quiescence_qualification': 'Parent reports natural controller exit at08:17:14Z/PID56304 absent and zeroLean at08:17:48Z. This read-only review confirms finished/status/byte-stable rawcheckpoint and absent json.tmp; it doesnotissue a newprocesscensus or establish a future dispatch lease.',
    'no_canonical_source_lease_hold_output_alias_compression_or_compiler_mutation': True}
outfile = BASE/'ht-ramsey-actual177-mode1-j2-readonly-partial-qualification-20261005.json'
assert not outfile.exists(); outfile.write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf8')
assert digest(REPORT) == EXPECTED177
print(json.dumps({'immutable177': bind(immutable), 'qualification': bind(outfile),
    'new39_resource_totals': resource_totals, 'remaining_kernels': 1906},indent=2))
