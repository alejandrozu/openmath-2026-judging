"""Prepared future read-only qualification of completed166 granular A000 sources.

Writes only a byte-identical immutable receipt copy and a new additive review.
No compiler, compression, aliases, source edits, or proof-coverage promotion.
"""
import collections
import datetime as dt
import hashlib
import json
import pathlib
import re
import sys

V = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(V))
from receipt_io import read_bytes_shared
from full_mathlib_scope import classify
from lean_imports import read_imports

G = 2**30
assert len(sys.argv) == 3 and sys.argv[1] == '--completed166-receipt-sha256', 'Explicit root-reviewed future166 quiescent receipt SHA is required'
EXPECTED_RAW = sys.argv[2]
assert re.fullmatch('[0-9a-f]{64}', EXPECTED_RAW), 'Malformed future receipt SHA'
BOUND = {
    'qualify_A000114_checkpoint_readonly_20261005.py': '624876f2a4f6fa456fb27852886d060f993d19c8f820c84e6dd8ff5cc726bacb',
    'operational_history/a000114/99eb7c9441573e8b.json': '99eb7c9441573e8bfb5088f9cdb75bc4eacc12f0e9b3a3512f08709eb9b7540f',
    'A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json': '4bcd0f7a9cc51d3cf83085cec858774fcd261d4709937b9d09ff1cd160ceba04',
    'root-A000-actual114-remaining52-granular-postexit-storage-actual-dispatch-20261005.json': 'fb494377a8c64e9e16cb691264e4ca1a340ec0f2062ad0d854bcb7850b719281',
    'sakana-a000224-original76-storage-checkpoint-receipt-20261005.json': 'd8226e2920788365d04ccd7c4a1cab829c5c0c192b4fa155aa4e4e4b11e3a552',
    'builds/sakana-a000224/build-plan.json': '0f6338f72ff570e79847995bac7cf6f6c56c8a1c2cc8dedf55181bc764180fe7',
    'root-A000-exact90-postexit-storage-actual-fresh-dispatch-20261005.json': 'd5f3d98cf7160f68fb5e944b91bb86e2630bf8522b093187ae073b5bc7f28d3e',
    'root-A000-post-exit-storage-v2-interface-granular90-approval-20261005.json': '984cc1aa2baad60e4809cee35c4d6a4046252a34705c25355a48ee3b57363aab',
    'run_a000_source_plan_with_post_exit_storage_v2_prepared.py': 'd73aa5d2218f358e79d5479de20b5082b345a994d0d4dd35d0a23516876eda28',
    'a000_post_exit_lzx_interface_v2_prepared.py': '03a6f7118d97e97e646b81cdb5508fab512eb23f65dc1465cd28d141d9cbd99b',
    'proposals/a000-post-exit-owned-artifact-storage-interface-v2-preparation-20261005.json': '00740b6897357d58e7546252f9299981248457fdef7a7f212db029ad400952fa',
    'run_source_plan.py': '70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534',
    'full_mathlib_scope.py': '1698d525e0bac93cd241c499dc0a132e5c9477cabd7ca7899e4574645714a3ab',
    'lean_imports.py': '4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa',
    'receipt_io.py': '2e189122fe360f1925dda2e0409c321b775fe7eb6edf17c3f13ef067d1776362',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    h = hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def at(s):
    return dt.datetime.fromisoformat(s.replace('Z', '+00:00'))

def ensure(test, message):
    if not test:
        raise AssertionError(message)

def logs(row, label):
    found = []
    for stream in ('stdout', 'stderr'):
        path = pathlib.Path(row[stream + '_file'])
        data = path.read_bytes()
        digest = sha(data)
        ensure(digest == row[stream + '_sha256'], label + ' ' + stream + ' hash')
        found.append({'stream': stream, 'file': str(path), 'bytes': len(data), 'sha256': digest})
    return found

def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        ensure(path.read_bytes() == data, 'Existing immutable output has different bytes: ' + str(path))
    else:
        with path.open('xb') as f:
            f.write(data)

started = dt.datetime.now(dt.timezone.utc)
raw_path = V / 'sakana-a000224-fresh-build.json'
raw = read_bytes_shared(raw_path)
ensure(sha(raw) == EXPECTED_RAW, 'Current A000 receipt differs from explicit future166 quiescent identity')
r = json.loads(raw)
bound_records = {}
loaded = {}
for name, wanted in BOUND.items():
    data = read_bytes_shared(V / name)
    ensure(sha(data) == wanted, 'Bound source/record changed: ' + name)
    bound_records[name] = {'sha256': wanted, 'bytes': len(data)}
    if name.endswith('.json'):
        loaded[name] = json.loads(data)

original76 = loaded['sakana-a000224-original76-storage-checkpoint-receipt-20261005.json']
old = loaded['operational_history/a000114/99eb7c9441573e8b.json']
prior114_qualification = loaded['A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json']
ensure(prior114_qualification['immutable114_receipt']['sha256'] == BOUND['operational_history/a000114/99eb7c9441573e8b.json'], 'Prior114 qualification ancestry')
ensure(prior114_qualification['counts']['successful_original_source_modules'] == 114 and len(original76['builds']) == 76, 'Prior dated scope')
p = loaded['builds/sakana-a000224/build-plan.json']
dispatch = loaded['root-A000-actual114-remaining52-granular-postexit-storage-actual-dispatch-20261005.json']
ensure(dispatch['status'] == 'ROOT_APPROVED_ACTUAL_A000114_TO166_GRANULAR52_POSTEXIT_STORAGE_CONTINUATION', 'Future166 dispatch status')
ensure(dispatch['independent114_qualification_sha256'] == BOUND['A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json'], 'Dispatch independent114 qualification')
ensure(r['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT', 'Not completed natural checkpoint')
ensure(r['checkpoint_reason'] == 'GRANULAR_REMAINDER_FINISHED_WHOLE_IMPORT_LEASE_STILL_REQUIRED', 'Not the completed166 granular boundary')
ensure(len(r['builds']) == 166 and len(old['builds']) == 114 and len(p['modules']) == 171, 'Future166 counts changed')
ensure(not r.get('failed_invocations') and not r.get('selected_audit_axiom_review'), 'Unexpected failure/audit rows')
ensure('current_module' not in r, 'Active source module still recorded')
for key in ('id', 'entrant', 'version', 'mathlib_pin', 'source_dir', 'modules', 'endpoints', 'roots', 'audit_modules', 'lean_options'):
    ensure(r[key] == p[key], 'Receipt/plan identity mismatch: ' + key)
ensure(r['version'] == '4.34.1' and r['mathlib_pin'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'Wrong pinned environment')
ensure(dispatch['runner_sha256'] == BOUND['run_a000_source_plan_with_post_exit_storage_v2_prepared.py'], 'Dispatch runner')
ensure(dispatch['storage_interface_sha256'] == BOUND['a000_post_exit_lzx_interface_v2_prepared.py'], 'Dispatch interface')
ensure(dispatch['source_plan_sha256'] == BOUND['builds/sakana-a000224/build-plan.json'], 'Dispatch plan')
ensure(dispatch['completed_starting114_checkpoint_sha256'] == BOUND['operational_history/a000114/99eb7c9441573e8b.json'], 'Dispatch exact114 ancestry')
ensure(dispatch['root_storage_policy_sha256'] == BOUND['root-A000-post-exit-storage-v2-interface-granular90-approval-20261005.json'], 'Dispatch policy')

snapshot = V / 'operational_history' / 'a000166' / (EXPECTED_RAW[:16] + '.json')
write_new(snapshot, raw)
current = {b['module']: b for b in r['builds']}
prior = {b['module']: b for b in old['builds']}
ensure(len(current) == 166 and len(prior) == 114, 'Duplicate future166 source rows')
ensure(set(prior).issubset(current), 'Missing preserved114 module')
ensure(all(prior[n] == current[n] for n in prior), 'Prior114 row changed BY MODULE')
original76_by_module = {b['module']: b for b in original76['builds']}
ensure(len(original76_by_module) == 76 and set(original76_by_module).issubset(prior), 'Historical76 ancestry')
ensure(all(original76_by_module[n] == current[n] for n in original76_by_module), 'Historical76 row changed BY MODULE')
new_names = set(current) - set(prior)
ensure(len(new_names) == 52, 'Not exactly52 new source rows')
all_names = {m['module'] for m in p['modules']}
ensure(set(current).issubset(all_names), 'Unplanned compiled module')

sources = []
for m in p['modules']:
    path = pathlib.Path(m['file'])
    actual = file_sha(path)
    ensure(actual == m['sha256'], 'Scientific source changed: ' + m['module'])
    sources.append({'module': m['module'], 'file': str(path), 'bytes': path.stat().st_size, 'sha256': actual})
scope = classify(p)
whole = set(scope['authored_transitive_whole_Mathlib_closure'])
ensure(len(whole) == 5 and not (set(current) & whole), 'Unexpected whole-source execution')
granular = all_names - whole
ensure(len(granular) == 166 and set(current) == granular, 'Not all166 granular sources completed')
deferred = r['deferred_whole_import_policy']['unattempted_whole_invocations']
ensure({x['module'] for x in deferred} == whole | set(p['audit_modules']), 'Exact five whole sources and selected audit must remain deferred')
ensure(len(deferred) == 6 and all(x['attempted'] is False for x in deferred), 'Whole or audit invocation occurred')
ensure(all(x['classification'] == 'SEPARATE_SOLE_LITERAL_IMPORTER_LEASE_REQUIRED' for x in deferred), 'Unexpected whole/audit deferral classification')
plan_by_name = {m['module']: m for m in p['modules']}

artifact_checks = []
for ix, (name, b) in enumerate(current.items(), 1):
    ensure(b['exit'] == 0 and not b.get('is_endpoint_audit') and not b.get('stop_reason'), 'Non-success/audit row: ' + name)
    ensure(b.get('source_sha256', plan_by_name[name]['sha256']) == plan_by_name[name]['sha256'], 'Row source SHA: ' + name)
    ensure(b.get('artifacts'), 'Missing own output receipt: ' + name)
    for a in b['artifacts']:
        path = pathlib.Path(a['file'])
        ensure(path.is_file() and path.stat().st_size == a['bytes'], 'Artifact size/path: ' + name)
        digest = file_sha(path)
        ensure(digest == a['sha256'], 'Own artifact hash changed: ' + name)
        artifact_checks.append({'module': name, 'file': str(path), 'bytes': a['bytes'], 'sha256': digest})
    if ix % 20 == 0:
        print('Own artifacts verified', ix, '/166', flush=True)

source_policy = {'initial_disk_bytes': 4000000000, 'initial_physical_bytes': 6*G,
    'initial_available_commit_bytes': 5*G, 'continuous_disk_bytes': 1000000000,
    'continuous_physical_bytes': 3*G, 'continuous_available_commit_bytes': G,
    'own_job_private_bytes': 6*G, 'own_process_private_bytes': 6*G,
    'poll_seconds': 0.25, 'timeout_seconds': 3600}
ordered_new = sorted((current[n] for n in new_names), key=lambda b: at(b['started_utc']))
available = set(prior)
new_checks = []
for b in ordered_new:
    name = b['module']
    g = b['own_job_resource_receipt']
    expected_command = [str(V / 'runtimes/lean-4.34.1-windows/bin/lean.exe'), '-j1', '-DmaxHeartbeats=0', '-DmaxRecDepth=100000', '-o', name.replace('.', '\\') + '.olean', name.replace('.', '\\') + '.lean']
    ensure(b['command'] == expected_command and g['command'] == expected_command, 'New source CLI: ' + name)
    ensure(pathlib.Path(g['cwd']) == pathlib.Path(p['source_dir']), 'New source cwd')
    ensure(g['resource_policy'] == source_policy, 'New source resource policy')
    ensure(g['attempted'] is True and g['state'] == 'PASS' and g['exit'] == 0, 'Guard source state')
    ensure(g['own_job_assignment_before_resume'] == 'PASS', 'Guard own job assignment')
    ensure(g['counter_helper_sha256'] == '0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4', 'Guard counter identity')
    ensure(g['commit_counter_helper_sha256'] == '1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed', 'Guard commit identity')
    ensure(g['minimum_disk_free_bytes'] >= 1000000000 and g['minimum_physical_available_bytes'] >= 3*G and g['minimum_available_commit_bytes'] >= G, 'New source continuous reserve')
    ensure(g['job_peak_aggregate_private_bytes'] <= 6*G and g['job_peak_process_private_bytes'] <= 6*G, 'New source hard cap')
    initial = g['initial_system_memory_snapshot']
    ensure(initial['free_physical_bytes'] >= 6*G and initial['available_commit_bytes'] >= 5*G, 'New source dispatch memory')
    ensure(b['started_utc'] == g['started_utc'] and b['finished_utc'] == g['finished_utc'], 'New source actual times')
    ensure(at(b['started_utc']) >= at(dispatch['checked_utc']), 'Source before dispatch approval')
    log_checks = logs(g, name)
    for stream in ('stdout', 'stderr'):
        data = pathlib.Path(g[stream + '_file']).read_bytes()
        ensure(data.decode('utf-8', errors='replace') == b[stream], 'Actual source raw log/full receipt mismatch')
    deps = set(read_imports(plan_by_name[name]['file'])) & all_names
    ensure(deps.issubset(available), 'Unavailable custom prerequisite: ' + name)
    available.add(name)
    new_checks.append({'module': name, 'source_sha256': b['source_sha256'], 'started_utc': b['started_utc'], 'finished_utc': b['finished_utc'],
        'source_command': b['command'], 'custom_prerequisites_already_completed': sorted(deps), 'raw_logs': log_checks,
        'minimum_disk_free_bytes': g['minimum_disk_free_bytes'], 'minimum_physical_available_bytes': g['minimum_physical_available_bytes'],
        'minimum_available_commit_bytes': g['minimum_available_commit_bytes'], 'job_peak_aggregate_private_bytes': g['job_peak_aggregate_private_bytes']})

sidecars = collections.defaultdict(list)
for path in (V / 'operational_history/a000-post-exit-storage').glob('*-actual.json'):
    data = path.read_bytes()
    s = json.loads(data)
    if s.get('source_module') in new_names:
        sidecars[s['source_module']].append((path, sha(data), s))
ensure(set(sidecars) == new_names and all(len(v) == 1 for v in sidecars.values()), 'Storage actual sidecars not one per new52')
storage_checks = []
classes = collections.Counter()
stable_keys = ('logical_bytes', 'volume_serial', 'file_index_high', 'file_index_low', 'link_count', 'last_write_FILETIME')
for index, b in enumerate(ordered_new):
    name = b['module']
    path, digest, s = sidecars[name][0]
    ensure(s['actual_completed_source_row'] == b, 'Storage callback actual source row changed')
    ensure(s['runner_sha256'] == BOUND['run_a000_source_plan_with_post_exit_storage_v2_prepared.py'], 'Storage runner')
    ensure(s['interface_sha256'] == BOUND['a000_post_exit_lzx_interface_v2_prepared.py'], 'Storage interface')
    ensure(s['root_policy_sha256'] == BOUND['root-A000-post-exit-storage-v2-interface-granular90-approval-20261005.json'], 'Storage root policy')
    ensure(s['specification_sha256'] == BOUND['proposals/a000-post-exit-owned-artifact-storage-interface-v2-preparation-20261005.json'], 'Storage specification')
    a = b['artifacts'][0]
    ensure(len(b['artifacts']) == 1 and s['target'] == a['file'], 'Storage own single target')
    before, after = s['native_before'], s['native_after']
    ensure(all(before[k] == after[k] for k in stable_keys), 'Storage native identity changed')
    ensure(before['link_count'] == 1 and before['logical_bytes'] == a['bytes'], 'Storage own single-link/size')
    ensure(not before['FILE_ATTRIBUTE_REPARSE_POINT'] and not before['FILE_ATTRIBUTE_ENCRYPTED'], 'Storage target type')
    ensure(s['content_inode_linkcount_size_mtime_preserved'] is True and s['allocation_nonincreasing'] is True, 'Storage preservation flags')
    ensure(s['source_receipt_bytes_unchanged'] is True and s['actual_source_PASS_row_not_reclassified'] is True, 'Storage scientific status preservation')
    ensure(s['original76_or_any_scientific_source_or_runtime_provider_targets'] == 0, 'Storage protected targets')
    ensure(after['stored_bytes_GetCompressedFileSizeW'] <= before['stored_bytes_GetCompressedFileSizeW'], 'Storage allocation increased')
    ensure(s['actual_allocation_bytes_saved'] == before['stored_bytes_GetCompressedFileSizeW'] - after['stored_bytes_GetCompressedFileSizeW'], 'Storage measured saved bytes')
    for label in ('read_and_mmap_before', 'read_and_mmap_after'):
        test = s[label]
        ensure(test['ordinary_read_sha256'] == a['sha256'] and test['Windows_read_only_mmap_sha256'] == a['sha256'] and test['byte_equality'] is True, 'Storage read/mmap measured hash')
    state = s['status']
    ensure(state in ('PASS_BYTE_IDENTICAL_A000_POST_EXIT_WOF_LZX', 'PASS_BYTE_IDENTICAL_A000_POST_EXIT_ORDINARY_NON_WOF_NONINCREASING_ALLOCATION'), 'Storage actual success class')
    if state == 'PASS_BYTE_IDENTICAL_A000_POST_EXIT_WOF_LZX':
        ensure(s['WOF_after']['external'] is True and s['WOF_after']['provider'] == 2 and s['WOF_after']['algorithm'] == 1, 'WOF installed class')
    else:
        ensure(s['WOF_after']['external'] is False, 'Non-WOF class')
    classes[state] += 1
    c = s['actual_command_row']
    ensure(c['command'] == s['actual_compact_command'] and c['command'][1:] == ['/C', '/F', '/Q', '/EXE:LZX', a['file']], 'Storage actual CLI')
    ensure(c['created_suspended'] is True and c['assigned_to_own_job_before_resume'] is True, 'Storage suspended own job')
    ensure(c['exit'] == 0 and c.get('stop_reason') is None, 'Storage actual exit/stop')
    ensure(c['own_process_and_job_cap_bytes'] == 256*2**20 and c['job_peak_private_bytes'] <= 256*2**20 and c['process_peak_private_bytes'] <= 256*2**20, 'Storage cap')
    ensure(c['minimum_disk_free_bytes'] >= 1000000000 and c['minimum_physical_available_bytes'] >= 3*G and c['minimum_available_commit_bytes'] >= G, 'Storage continuous resource floors')
    init = c['initial_counters']
    ensure(init['disk_free_bytes'] >= 4000000000 and init['free_physical_bytes'] >= 6*G and init['available_commit_bytes'] >= 5*G, 'Storage dispatch resource gates')
    ensure(init['disk_free_bytes'] - a['bytes'] >= 1000000000, 'Storage inverse capacity reserve')
    ensure(at(b['finished_utc']) <= at(s['started_utc']) <= at(c['started_utc']) <= at(c['finished_utc']) <= at(s['finished_utc']), 'Storage post-exit chronology')
    if index + 1 < len(ordered_new):
        ensure(at(s['finished_utc']) <= at(ordered_new[index+1]['started_utc']), 'Next source started before storage completed')
    else:
        # The source dispatcher records its checkpoint time to whole seconds.
        ensure(at(s['finished_utc']).replace(microsecond=0) <= at(r['finished_utc']), 'Last storage after completed checkpoint timestamp')
    raw_logs = logs(c, name + ' storage')
    storage_checks.append({'module': name, 'sidecar': str(path), 'sidecar_sha256': digest, 'status': state,
        'target_source_artifact_sha256': a['sha256'], 'logical_bytes': a['bytes'],
        'native_identity_preserved': {k: after[k] for k in stable_keys},
        'before_allocated_bytes': before['stored_bytes_GetCompressedFileSizeW'], 'after_allocated_bytes': after['stored_bytes_GetCompressedFileSizeW'],
        'actual_allocated_bytes_saved': s['actual_allocation_bytes_saved'], 'source_completed_before_storage_and_next_dispatch': True,
        'raw_storage_logs': raw_logs, 'source_receipt_sha256_before_historical_sidecar_attestation_only': s['source_receipt_sha256_before']})

ensure(sha(read_bytes_shared(raw_path)) == EXPECTED_RAW, 'Current receipt mutated during review')
for name, wanted in BOUND.items():
    ensure(sha(read_bytes_shared(V/name)) == wanted, 'Bound record/code mutated during review')
ensure(all(file_sha(m['file']) == m['sha256'] for m in p['modules']), 'Scientific source changed during review')
finished = dt.datetime.now(dt.timezone.utc)
record = {
    'status': 'QUALIFIED_ACTUAL_A000166_GRANULAR_SOURCE_COMPLETION_FIVE_WHOLE_AND_SELECTED3_UNRUN',
    'started_utc': started.isoformat(), 'finished_utc': finished.isoformat(), 'reviewer': '/root/nonnovel_and_affiliations',
    'producer': {'file': str(pathlib.Path(__file__).resolve()), 'sha256': file_sha(__file__)},
    'immutable166_receipt': {'file': str(snapshot), 'sha256': EXPECTED_RAW, 'bytes': len(raw)},
    'current_receipt': {'file': str(raw_path), 'sha256': EXPECTED_RAW, 'status': r['status'], 'finished_utc': r['finished_utc'], 'checkpoint_reason': r['checkpoint_reason'], 'unchanged_through_review': True},
    'frozen_record_and_operational_source_bindings': bound_records,
    'counts': {'planned_original_source_modules': 171, 'successful_original_source_modules': 166, 'prior_immutable_successes': 114, 'new_source_successes': 52, 'historical_original76_successes': 76, 'previous_qualified_guarded38_successes': 38,
        'planned_granular_modules': 166, 'pending_granular_modules': 0, 'pending_whole_modules': 5,
        'selected_endpoint_audit_invocations': 0, 'selected_printed_outputs': 0, 'post_exit_storage_actual_sidecars': 52},
    'source_plan_compiler': r['version'], 'source_plan_mathlib_pin': r['mathlib_pin'], 'source_plan_lean_options': r['lean_options'],
    'prior114_preservation': {'comparison': 'BY MODULE, exact full row values; chronology/prefix ordering not assumed', 'all114_rows_identical': True, 'historical76_rows_also_identical': True,
        'original76_guard_diversity_and_dated_prior38_guard_scope_preserved': True, 'new52_guard_not_retroactively_attributed_to166': True,
        'prior114_qualification_file': str(V/'A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json'), 'prior114_qualification_sha256': BOUND['A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json']},
    'all171_current_source_byte_checks': sources,
    'all166_current_owned_artifact_stream_hash_checks': artifact_checks,
    'new52_source_guard_and_raw_log_checks': new_checks,
    'new52_source_policy_exact': source_policy,
    'new52_resource_aggregate': {'maximum_own_job_peak_private_bytes': max(x['job_peak_aggregate_private_bytes'] for x in new_checks),
        'minimum_measured_disk_free_bytes': min(x['minimum_disk_free_bytes'] for x in new_checks),
        'minimum_measured_physical_available_bytes': min(x['minimum_physical_available_bytes'] for x in new_checks),
        'minimum_measured_available_commit_bytes': min(x['minimum_available_commit_bytes'] for x in new_checks),
        'total_actual_source_wall_seconds': round(sum(b['seconds'] for b in ordered_new), 3)},
    'post_exit_storage_actual_class_counts': dict(classes), 'post_exit_storage_sidecar_checks': storage_checks,
    'total_actual_stored_allocation_bytes_saved_by_new52_sidecars': sum(x['actual_allocated_bytes_saved'] for x in storage_checks),
    'pending_granular_modules': sorted(granular - set(current)), 'pending_whole_modules': sorted(whole),
    'limitations': [
        'All166 granular sources only: five whole sources and three selected endpoint prints remain unrun; no complete171-source qualification, score or release conclusion.',
        'The selected three axiom outputs remain unrun; source exit0 and preserved artifact bytes are not an endpoint axiom audit.',
        'Original76 guard diversity and prior38 phase remain dated and exact; the current52 phase does not retroactively qualify all166 under one new guard.',
        'Read/mmap byte identity for compression is rechecked against dated actual sidecar evidence; this review streams current own artifact hashes and performs no new mmap/compression.',
        'Intermediate source_receipt_sha256_before values are dated storage-sidecar attestations; their original transient receipt snapshots are not reconstructed by this review.',
        'No bulk official dependency artifact rehash or fresh runtime/compiler invocation is performed; exact plan and operational source/approval bindings remain explicit.',
        'A root-confirmed naturally completed/quiescent166 boundary and its explicit receipt SHA are prerequisites; this review does not itself stop, suspend or inspect running processes.'
    ],
    'actions': {'compiler_invoked': False, 'source_or_current_receipt_modified': False, 'proof_output_copied_or_aliased': False, 'storage_operation_invoked': False,
        'editor_or_pdf_operation': False, 'only_new_outputs': ['immutable byte-identical166 JSON receipt copy', 'additive qualification JSON', 'this read-only review producer']}
}
out = V / ('A000-actual166-granular-completion-readonly-qualification-' + finished.strftime('%Y%m%dT%H%M%S%fZ') + '.json')
data = (json.dumps(record, ensure_ascii=False, indent=2) + '\n').encode('utf-8')
write_new(out, data)
print(json.dumps({'status': record['status'], 'file': str(out), 'sha256': sha(data), 'snapshot': str(snapshot), 'snapshot_sha256': EXPECTED_RAW,
    'counts': record['counts'], 'storage_classes': dict(classes), 'stored_bytes_saved': record['total_actual_stored_allocation_bytes_saved_by_new52_sidecars']}, ensure_ascii=False), flush=True)
