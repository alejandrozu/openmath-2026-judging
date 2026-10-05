"""Prepare, never import or execute, the future partial166 checkpoint verifier."""
import datetime
import difflib
import hashlib
import json
import pathlib

V = pathlib.Path(__file__).resolve().parent
base = V / 'qualify_A000114_checkpoint_readonly_20261005.py'
base_bytes = base.read_bytes()
base_sha = hashlib.sha256(base_bytes).hexdigest()
assert base_sha == '624876f2a4f6fa456fb27852886d060f993d19c8f820c84e6dd8ff5cc726bacb'
original = base_bytes.decode('utf-8')
candidate = original

def change(before, after):
    global candidate
    assert candidate.count(before) == 1, before[:120]
    candidate = candidate.replace(before, after, 1)

change('"""Read-only qualification of the quiescent, partial 114-source A000 receipt.',
       '"""Prepared future read-only qualification of completed166 granular A000 sources.')
change('import pathlib\nimport sys', 'import pathlib\nimport re\nimport sys')
change("EXPECTED_RAW = '99eb7c9441573e8bfb5088f9cdb75bc4eacc12f0e9b3a3512f08709eb9b7540f'", "assert len(sys.argv) == 3 and sys.argv[1] == '--completed166-receipt-sha256', 'Explicit root-reviewed future166 quiescent receipt SHA is required'\nEXPECTED_RAW = sys.argv[2]\nassert re.fullmatch('[0-9a-f]{64}', EXPECTED_RAW), 'Malformed future receipt SHA'")
change('BOUND = {', "BOUND = {\n    'qualify_A000114_checkpoint_readonly_20261005.py': '624876f2a4f6fa456fb27852886d060f993d19c8f820c84e6dd8ff5cc726bacb',\n    'operational_history/a000114/99eb7c9441573e8b.json': '99eb7c9441573e8bfb5088f9cdb75bc4eacc12f0e9b3a3512f08709eb9b7540f',\n    'A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json': '4bcd0f7a9cc51d3cf83085cec858774fcd261d4709937b9d09ff1cd160ceba04',\n    'root-A000-actual114-remaining52-granular-postexit-storage-actual-dispatch-20261005.json': 'fb494377a8c64e9e16cb691264e4ca1a340ec0f2062ad0d854bcb7850b719281',")
change("'A000 receipt differs from reviewed quiescent114 identity'", "'Current A000 receipt differs from explicit future166 quiescent identity'")
change("old = loaded['sakana-a000224-original76-storage-checkpoint-receipt-20261005.json']", "original76 = loaded['sakana-a000224-original76-storage-checkpoint-receipt-20261005.json']\nold = loaded['operational_history/a000114/99eb7c9441573e8b.json']\nprior114_qualification = loaded['A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json']\nensure(prior114_qualification['immutable114_receipt']['sha256'] == BOUND['operational_history/a000114/99eb7c9441573e8b.json'], 'Prior114 qualification ancestry')\nensure(prior114_qualification['counts']['successful_original_source_modules'] == 114 and len(original76['builds']) == 76, 'Prior dated scope')")
change("dispatch = loaded['root-A000-exact90-postexit-storage-actual-fresh-dispatch-20261005.json']", "dispatch = loaded['root-A000-actual114-remaining52-granular-postexit-storage-actual-dispatch-20261005.json']\nensure(dispatch['status'] == 'ROOT_APPROVED_ACTUAL_A000114_TO166_GRANULAR52_POSTEXIT_STORAGE_CONTINUATION', 'Future166 dispatch status')\nensure(dispatch['independent114_qualification_sha256'] == BOUND['A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json'], 'Dispatch independent114 qualification')")
change("ensure(r['checkpoint_reason'] == 'THIRD_WORKER_LEASE_HANDOFF_AT_COMPLETED_MODULE_BOUNDARY', 'Unexpected checkpoint boundary')", "ensure(r['checkpoint_reason'] == 'GRANULAR_REMAINDER_FINISHED_WHOLE_IMPORT_LEASE_STILL_REQUIRED', 'Not the completed166 granular boundary')")
change("ensure(len(r['builds']) == 114 and len(old['builds']) == 76 and len(p['modules']) == 171, 'Counts changed')", "ensure(len(r['builds']) == 166 and len(old['builds']) == 114 and len(p['modules']) == 171, 'Future166 counts changed')")
change("ensure(dispatch['prior_actual76_receipt_sha256'] == BOUND['sakana-a000224-original76-storage-checkpoint-receipt-20261005.json'], 'Dispatch ancestry')", "ensure(dispatch['completed_starting114_checkpoint_sha256'] == BOUND['operational_history/a000114/99eb7c9441573e8b.json'], 'Dispatch exact114 ancestry')")
change("ensure(dispatch['future_policy_sha256'] == BOUND['root-A000-post-exit-storage-v2-interface-granular90-approval-20261005.json'], 'Dispatch policy')", "ensure(dispatch['root_storage_policy_sha256'] == BOUND['root-A000-post-exit-storage-v2-interface-granular90-approval-20261005.json'], 'Dispatch policy')")
change("snapshot = V / 'operational_history' / 'a000114' / (EXPECTED_RAW[:16] + '.json')", "snapshot = V / 'operational_history' / 'a000166' / (EXPECTED_RAW[:16] + '.json')")
change("ensure(len(current) == 114 and len(prior) == 76, 'Duplicate source build rows')", "ensure(len(current) == 166 and len(prior) == 114, 'Duplicate future166 source rows')")
change("ensure(set(prior).issubset(current), 'Missing original76 module')", "ensure(set(prior).issubset(current), 'Missing preserved114 module')")
change("ensure(all(prior[n] == current[n] for n in prior), 'Original row changed by module')", "ensure(all(prior[n] == current[n] for n in prior), 'Prior114 row changed BY MODULE')\noriginal76_by_module = {b['module']: b for b in original76['builds']}\nensure(len(original76_by_module) == 76 and set(original76_by_module).issubset(prior), 'Historical76 ancestry')\nensure(all(original76_by_module[n] == current[n] for n in original76_by_module), 'Historical76 row changed BY MODULE')")
change("ensure(len(new_names) == 38, 'Not exactly38 new source rows')", "ensure(len(new_names) == 52, 'Not exactly52 new source rows')")
change("ensure(len(granular) == 166 and len(granular - set(current)) == 52, 'Pending granular count')", "ensure(len(granular) == 166 and set(current) == granular, 'Not all166 granular sources completed')\ndeferred = r['deferred_whole_import_policy']['unattempted_whole_invocations']\nensure({x['module'] for x in deferred} == whole | set(p['audit_modules']), 'Exact five whole sources and selected audit must remain deferred')\nensure(len(deferred) == 6 and all(x['attempted'] is False for x in deferred), 'Whole or audit invocation occurred')\nensure(all(x['classification'] == 'SEPARATE_SOLE_LITERAL_IMPORTER_LEASE_REQUIRED' for x in deferred), 'Unexpected whole/audit deferral classification')")
change("print('Own artifacts verified', ix, '/114', flush=True)", "print('Own artifacts verified', ix, '/166', flush=True)")
change("ensure(set(sidecars) == new_names and all(len(v) == 1 for v in sidecars.values()), 'Storage actual sidecars not one per new38')", "ensure(set(sidecars) == new_names and all(len(v) == 1 for v in sidecars.values()), 'Storage actual sidecars not one per new52')")
change("'status': 'QUALIFIED_ACTUAL_A000114_PARTIAL_SOURCE_CHECKPOINT_WITH38_GUARDED_BYTE_IDENTICAL_STORAGE'", "'status': 'QUALIFIED_ACTUAL_A000166_GRANULAR_SOURCE_COMPLETION_FIVE_WHOLE_AND_SELECTED3_UNRUN'")
change("'immutable114_receipt': {'file': str(snapshot)", "'immutable166_receipt': {'file': str(snapshot)")
change("'successful_original_source_modules': 114, 'prior_immutable_successes': 76, 'new_source_successes': 38", "'successful_original_source_modules': 166, 'prior_immutable_successes': 114, 'new_source_successes': 52, 'historical_original76_successes': 76, 'previous_qualified_guarded38_successes': 38")
change("'pending_granular_modules': 52", "'pending_granular_modules': 0")
change("'post_exit_storage_actual_sidecars': 38", "'post_exit_storage_actual_sidecars': 52")
change("'prior76_preservation': {'comparison': 'BY MODULE, exact full row values; chronology/prefix ordering not assumed', 'all76_rows_identical': True,\n        'historical_guard_diversity_preserved': True, 'new6GiB5GiBguard_not_retroactively_attributed_to76': True}", "'prior114_preservation': {'comparison': 'BY MODULE, exact full row values; chronology/prefix ordering not assumed', 'all114_rows_identical': True, 'historical76_rows_also_identical': True,\n        'original76_guard_diversity_and_dated_prior38_guard_scope_preserved': True, 'new52_guard_not_retroactively_attributed_to166': True,\n        'prior114_qualification_file': str(V/'A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json'), 'prior114_qualification_sha256': BOUND['A000-actual114-checkpoint-readonly-qualification-20261005T074611923593Z.json']}")
change("'all114_current_owned_artifact_stream_hash_checks'", "'all166_current_owned_artifact_stream_hash_checks'")
for before, after in [('new38_source_guard_and_raw_log_checks', 'new52_source_guard_and_raw_log_checks'), ('new38_source_policy_exact', 'new52_source_policy_exact'), ('new38_resource_aggregate', 'new52_resource_aggregate'), ('total_actual_stored_allocation_bytes_saved_by_new38_sidecars', 'total_actual_stored_allocation_bytes_saved_by_new52_sidecars')]:
    assert before in candidate
    candidate = candidate.replace(before, after)
change("'Partial checkpoint only: no complete 171-source or selected-endpoint qualification, no new score/release conclusion.'", "'All166 granular sources only: five whole sources and three selected endpoint prints remain unrun; no complete171-source qualification, score or release conclusion.'")
change("'The original76 rows retain their historical commands/resource practices and are not all attributed to the later6/5 guard.'", "'Original76 guard diversity and prior38 phase remain dated and exact; the current52 phase does not retroactively qualify all166 under one new guard.'")
change("'Dispatcher natural exit/no A000 importer is provided by root dated completion instruction and the finished quiescent receipt; this review does not itself suspend or inspect running processes.'", "'A root-confirmed naturally completed/quiescent166 boundary and its explicit receipt SHA are prerequisites; this review does not itself stop, suspend or inspect running processes.'")
change("'immutable byte-identical114 JSON receipt copy'", "'immutable byte-identical166 JSON receipt copy'")
change("out = V / ('A000-actual114-checkpoint-readonly-qualification-'", "out = V / ('A000-actual166-granular-completion-readonly-qualification-'")

target = V / 'qualify_A000166_granular_completion_readonly_prepared_20261005.py'
candidate_bytes = candidate.encode('utf-8')
candidate_sha = hashlib.sha256(candidate_bytes).hexdigest()
diff = ''.join(difflib.unified_diff(original.splitlines(keepends=True), candidate.splitlines(keepends=True), fromfile=base.name, tofile=target.name))
folder = V / 'proposals' / 'A000166-qualifier-prepared-20261005'
folder.mkdir(parents=True, exist_ok=True)

def exclusive(path, data):
    if path.exists():
        assert path.read_bytes() == data
    else:
        with path.open('xb') as f:
            f.write(data)

baseline_copy = folder / ('baseline-' + base_sha[:16] + '.py')
exclusive(baseline_copy, base_bytes)
exclusive(target, candidate_bytes)
diff_file = folder / 'A000166-qualifier-full-minimal.diff'
exclusive(diff_file, diff.encode('utf-8'))
packet = {'status': 'PREPARED_UNEXECUTED_FUTURE_A000166_GRANULAR_COMPLETION_READ_ONLY_QUALIFIER',
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'baseline': {'file': str(base), 'sha256': base_sha, 'immutable_copy': str(baseline_copy)},
    'candidate': {'file': str(target), 'sha256': candidate_sha, 'bytes': len(candidate_bytes)},
    'full_minimal_diff': {'file': str(diff_file), 'sha256': hashlib.sha256(diff.encode('utf-8')).hexdigest(), 'lines': len(diff.splitlines())},
    'required_future_cli': ['python', '-X', 'utf8', str(target), '--completed166-receipt-sha256', '<ROOT_CONFIRMED_ACTUAL_QUIESCENT166_RECEIPT_SHA256>'],
    'frozen_ancestry': {'original76_sha256': 'd8226e2920788365d04ccd7c4a1cab829c5c0c192b4fa155aa4e4e4b11e3a552', 'actual114_sha256': '99eb7c9441573e8bfb5088f9cdb75bc4eacc12f0e9b3a3512f08709eb9b7540f', 'qualified114_sha256': '4bcd0f7a9cc51d3cf83085cec858774fcd261d4709937b9d09ff1cd160ceba04', 'new52_dispatch_sha256': 'fb494377a8c64e9e16cb691264e4ca1a340ec0f2062ad0d854bcb7850b719281'},
    'future_required_checks': ['Root-confirmed166 completed/quiescent current receipt exact CLI SHA; final granular-completion reason only', 'All171 scientific source bytes; all166 current own output hashes/sizes', 'All114 previous rows BY MODULE exact values; original76 independently retained exact', 'Exactly52 new source invocations -j1/maxHeartbeats0/maxRecDepth100000 with unchanged6GiB5GiB own guard and raw logs', 'Exactly52 source-matched actual postexit sidecars, approved03a6/d73/984, identity/read+mmap/allocation/raw storage logs and nonoverlap chronology', 'Exactlyfive whole sources and FreshAudit1 explicitly deferred; zero selected prints'],
    'future_permitted_outputs': ['One short-path byte-identical immutable166 JSON copy', 'One newly dated additive partial-scope qualification JSON'],
    'prior_phase_qualification': 'Original76 practices retain dated diversity; prior38 qualification remains separately bound; new52 guard scope is not applied retroactively to all166.',
    'no_completed166_claim_yet': True, 'actions': {'qualifier_imported_or_executed': False, 'live_receipt_read': False, 'compiler_invoked': False, 'source_current_receipt_alias_storage_or_canonical_modified': False}}
packet_path = folder / 'A000166-qualifier-preparation-review-packet.json'
packet_bytes = (json.dumps(packet, indent=2) + '\n').encode('utf-8')
exclusive(packet_path, packet_bytes)
print(json.dumps({'candidate_file': str(target), 'candidate_sha256': candidate_sha, 'diff_file': str(diff_file), 'diff_sha256': packet['full_minimal_diff']['sha256'], 'packet_file': str(packet_path), 'packet_sha256': hashlib.sha256(packet_bytes).hexdigest()}))
