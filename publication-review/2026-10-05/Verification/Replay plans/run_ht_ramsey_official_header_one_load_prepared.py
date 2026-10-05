"""PREPARED ONLY: one separately approved R141 or R142 official header load.

Imports the exact reviewed seed helpers, without running their main function.
No save, audit, original/canonical write, self-relaunch or automatic next source.
Requires actual seed, outer exit, complete role/source/runtime qualification.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, msvcrt, os, sys, threading

BASE = Path(__file__).resolve().parent
SEED_HELPER = BASE / 'run_ht_ramsey_official_header_r141_seed_only_prepared.py'
SEED_SHA = 'c7cb7c743b497c4e80f553631ef625f587bc0e15b071feb891d75557664c344c'
TARGETS = {
    'RamseyCert.Chunk.R141': ('d38f94725cbbe0294637f92e6b747ae1da6274de67f5af29b29317f901e1321e', 'B'),
    'RamseyCert.Chunk.R142': ('75e8d8fcd30c1f86571d3a6f21db13bdda43c6457bdf58abae6edd1b255b5b6f', 'C'),
}
STATUS = 'ROOT_APPROVED_SOLO_ONE_R141_OR_R142_OFFICIAL_HEADER_LOAD_AFTER_ACTUAL_COMPLETE_SEED_FIDELITY_REVIEW'

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()

def stamp(): return datetime.now(timezone.utc).isoformat()

def imported_seed():
    assert sha(SEED_HELPER) == SEED_SHA
    spec = importlib.util.spec_from_file_location('ht_actual_header_seed_helpers', SEED_HELPER)
    seed = importlib.util.module_from_spec(spec); spec.loader.exec_module(seed)
    return seed

def actual_seed_inputs(seed, approval, root, own_sources, env, paths):
    seed_file = seed.bound_file(approval['actual_seed_receipt'])
    assert seed_file == root / 'actual-seed.json'
    actual = json.loads(seed_file.read_bytes())
    assert actual['status'] == 'PASS_SOURCE_ONLY_HEADER_SEED_REQUIRES_SEPARATE_LOAD_APPROVAL'
    assert actual['controller_source_sha256'] == SEED_SHA
    assert actual['actual_owned_child_exit'] == 0 and actual['own_job_resource_receipt']['state'] == 'PASS'
    assert actual['new_source_invocations_this_phase'] == 1 and actual['new_audit_invocations_this_phase'] == 0
    assert actual['exact_source_sha256'] == seed.SOURCE_SHA and actual['original_source_outputs_still_absent'] is True
    assert actual['source_flags'] == ['-j2', '-DmaxHeartbeats=0', '-DmaxRecDepth=100000']
    assert actual['plan_additional_lean_options'] == {} and actual['source_body_maxRecDepth_option'] == 1000000
    assert actual['literal_LEAN_NUM_THREADS'] == '2' and actual['literal_LEAN_PATH'] == env['LEAN_PATH']
    assert actual['dependency_root_order'] == paths and actual['cwd'] == str(seed.STAGE)
    assert actual['inherited_LEAN_IMPORT_WORKERS'] == env.get('LEAN_IMPORT_WORKERS')
    outer = json.loads(seed.bound_file(approval['actual_seed_outer_tool_exit_record']).read_bytes())
    assert outer['status'] == 'ROOT_CONFIRMED_ACTUAL_HEADER_SEED_CONTROLLER_TOOL_EXIT_ZERO'
    assert outer['actual_controller_exit_code'] == 0 and outer['actual_seed_receipt_sha256'] == sha(seed_file)
    qualification_file = seed.bound_file(approval['actual_seed_complete_region_runtime_source_qualification'])
    qualification = json.loads(qualification_file.read_bytes())
    assert qualification['status'] == 'ROOT_REVIEWED_ACTUAL_HEADER_SEED_COMPLETE_ROLE_SOURCE_RUNTIME_FIDELITY_FOR_ONE_OFFICIAL_LOAD'
    assert qualification['actual_seed_receipt_sha256'] == sha(seed_file)
    assert qualification['reviewed_seed_controller_sha256'] == SEED_SHA
    assert qualification['exact_runtime_executable_sha256'] == seed.LEAN_SHA
    for flag in ['full_header_source_artifact_closure_rehashed', 'implicit_Init_and_meta_IR_roles_included',
                 'every_actual_deps_role_bound_to_exact_official_or_original_common35_provider',
                 'same_executable_and_relevant_dependent_library_build_identity_proven',
                 'only_own_header_snapshot_not_full_or_external_snapshot',
                 'no_changed_trust_option_import_roots_or_approved_runtime_flags']:
        assert qualification[flag] is True
    snapshot = root / 'header/R141.header'; deps = Path(str(snapshot) + '.deps')
    assert actual['header_snapshot']['file'] == str(snapshot) and actual['header_snapshot_deps']['file'] == str(deps)
    seed.check_inventory([actual['header_snapshot'], actual['header_snapshot_deps']])
    assert qualification['snapshot_sha256'] == sha(snapshot) and qualification['deps_sha256'] == sha(deps)
    parsed, regions = seed.parse_actual_regions(snapshot, own_sources)
    assert parsed == actual['actual_deps_JSON'] and regions == actual['snapshot_dependency_regions']
    assert qualification['actual_region_inventory_canonical_sha256'] == seed.csha(regions)
    assert seed.csha(regions) == actual['actual_region_inventory_canonical_sha256']
    closure = qualification['complete_source_artifact_identity_records']; assert closure
    provider_files = set()
    for unit in closure:
        assert sha(unit['source_file']) == unit['source_sha256']
        seed.check_inventory(unit['artifacts'])
        provider_files.update(str(Path(r['file']).resolve()) for r in unit['artifacts'])
    assert {r['file'] for r in regions} <= provider_files
    assert seed.native_library_candidates(paths) == actual['conservative_native_library_inventory']
    seed.check_inventory(actual['conservative_native_library_inventory'])
    libraries = qualification['complete_relevant_executable_library_identity_records']; assert libraries
    seed.check_inventory(libraries); library_files = {r['file'] for r in libraries}
    assert {r['file'] for r in actual['conservative_native_library_inventory']} <= library_files
    observation = actual['loaded_image_observation']
    assert not observation.get('foreign_Lean_observations') and not observation['postexit_image_hash_errors']
    assert observation['successful_toolhelp_snapshots'] > 0 and observation['observed_loaded_images']
    assert any(r['file'] == str(seed.LEAN) and r['sha256'] == seed.LEAN_SHA for r in observation['observed_loaded_images'])
    seed.check_inventory(observation['observed_loaded_images'])
    assert {r['file'] for r in observation['observed_loaded_images']} <= library_files
    assert qualification['actual_seed_image_observation_canonical_sha256'] == seed.csha(observation)
    # A ToolHelp error never silently becomes clean=true. A limited observation
    # may be used only after a separate exact root evidence record proves the
    # relevant executable/library identity by independent positive/static data.
    if observation['toolhelp_errors']:
        limit_file = seed.bound_file(qualification['separate_limited_image_observation_and_library_fidelity_review'])
        limited = json.loads(limit_file.read_bytes())
        assert limited['status'] == 'ROOT_REVIEWED_LIMITED_TOOLHELP_OBSERVATION_WITH_SEPARATELY_COMPLETE_POSITIVE_STATIC_LIBRARY_IDENTITY'
        assert limited['actual_seed_receipt_sha256'] == sha(seed_file)
        assert limited['actual_seed_image_observation_canonical_sha256'] == seed.csha(observation)
        assert limited['complete_relevant_library_inventory_canonical_sha256'] == seed.csha(libraries)
        assert limited['observer_errors_preserved_not_relabelled_clean'] is True
        assert limited['source_proof_pass_does_not_by_itself_qualify_library_fidelity'] is True
        assert limited['independent_positive_or_static_complete_library_fidelity_evidence_bindings']
        for evidence in limited['independent_positive_or_static_complete_library_fidelity_evidence_bindings']:
            seed.bound_file(evidence)
    else:
        assert qualification['image_observation_policy'] == 'SAMPLED_POSITIVE_TOOLHELP_TRACE_WITH_NO_ERRORS_AND_COMPLETE_INDEPENDENT_LIBRARY_IDENTITY'
    seed.check_inventory(actual['isolated_output_artifacts'])
    return actual, snapshot, qualification_file, libraries

def target_inventory(seed, library, short_name):
    rows = []
    for path in sorted(library.rglob('*')):
        if not path.is_file(): continue
        assert path.name.startswith(short_name + '.')
        assert any(str(path).endswith(s) for s in seed.OUTPUT_SUFFIXES)
        row = seed.inventory(path); row['relative_file'] = str(path.relative_to(library)); rows.append(row)
    return rows

def compare(a, b):
    left = {r['relative_file']: r for r in a}; right = {r['relative_file']: r for r in b}
    return [{'relative_file': name, 'baseline_sha256': left.get(name, {}).get('sha256'),
             'load_sha256': right.get(name, {}).get('sha256'),
             'binary_identical': bool(name in left and name in right and left[name]['sha256'] == right[name]['sha256']
                                      and left[name]['bytes'] == right[name]['bytes'])}
            for name in sorted(set(left) | set(right))]

def main():
    assert len(sys.argv) == 4 and sys.argv[1] == '--root-approved-one-official-header-load'
    seed = imported_seed(); approval_path = Path(sys.argv[2]).resolve(); approval_sha = sys.argv[3]
    assert approval_path.is_relative_to(BASE) and sha(approval_path) == approval_sha
    approval = json.loads(approval_path.read_bytes())
    assert approval['status'] == STATUS and approval['reviewed_controller_sha256'] == sha(__file__)
    assert approval['reviewed_seed_helper_sha256'] == SEED_SHA
    module = approval['exact_target_module']; assert module in TARGETS
    source_sha, variant = TARGETS[module]
    assert approval['exact_target_source_sha256'] == source_sha
    assert approval['maximum_total_global_Lean_importers'] == 2 and approval['maximum_own_parallel_Lean_jobs'] == 1
    for key in ['no_other_source_compiler_or_dispatcher_admitted', 'no_save_audit_next_source_or_remaining_continuation_authorized',
                'source_options_proofs_original_outputs_and_canonical_receipts_unchanged',
                'direct_guarded_subprocess_only_no_execv_or_detached_stdout']:
        assert approval[key] is True
    assert approval['endpoint_audit_invocations_this_phase'] == 0 and approval['new_source_invocations_this_phase'] == 1
    assert approval['actual_other_dispatcher_exit_confirmed_not_inferred_from_WAITING_label'] is True
    seed.bound_file(approval['actual_other_dispatcher_exit_record'])
    common = seed.import_checked(seed.READER, seed.READER_SHA, 'ht_header_load_reviewed_common')
    observer = seed.import_checked(BASE / 'luke_native_image_observer.py',
                                  'd25a05c7b3e15d349c94416f675af79d5e5ca2db9dd050f1ff9387eb4ea613d6', 'ht_header_load_images')
    assert sha(BASE / 'luke_native_image_observer.py') == approval['reviewed_loaded_image_observer_sha256']
    root = Path(approval['actual_pilot_root']).resolve()
    assert root.parent == BASE / 'isolated-header-pilots' and root.is_dir()
    receipt = root / ('actual-load-' + variant + '.json')
    library = root / variant
    assert not receipt.exists() and not receipt.with_suffix('.json.tmp').exists() and not library.exists()
    lockfile = seed.STAGE / '.fresh-replay.lock'; assert lockfile.is_file() and lockfile.stat().st_size == 1
    lock = lockfile.open('r+b'); lock.seek(0); msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
    report = None
    try:
        assert not seed.CANONICAL.with_suffix('.json.tmp').exists()
        original_raw, plan, manifest, entries, passed, own_sources = seed.runtime_and_sources(approval, common)
        source = Path(entries[module]['file']); assert sha(source) == source_sha and module not in passed
        assert not seed.source_outputs(source)
        kernel = next(r for r in manifest['kernel_sources'] if r['module'] == module)
        assert kernel['entire_custom_prerequisite_closure'] == next(r for r in manifest['kernel_sources'] if r['module'] == seed.MODULE)['entire_custom_prerequisite_closure']
        assert common.read_imports(source) == common.read_imports(seed.SOURCE)
        env, paths = seed.make_env(); assert paths == approval['exact_original_LEAN_PATH_roots_in_order']
        assert len(passed) == approval['actual_completed_HT_source_row_count']
        actual_seed, snapshot, qualification_file, libraries = actual_seed_inputs(seed, approval, root, own_sources, env, paths)
        process_gate = seed.process_gate(common, approval)
        library.mkdir(); target = library / Path(*module.split('.')).with_suffix('.olean'); target.parent.mkdir(parents=True)
        command = [str(seed.LEAN), '-j2', '-DmaxHeartbeats=0', '-DmaxRecDepth=100000', '--incr-load=' + str(snapshot),
                   '-o', str(target), str(source.relative_to(seed.STAGE))]
        report = {'status': 'RUNNING_ONE_OWN_OFFICIAL_HEADER_LOAD', 'started_utc': stamp(), 'target_module': module,
                  'target_source_sha256': source_sha, 'variant': variant, 'controller_source_sha256': sha(__file__),
                  'reviewed_seed_helper_sha256': SEED_SHA, 'root_approval': str(approval_path), 'root_approval_sha256': approval_sha,
                  'actual_seed_receipt': approval['actual_seed_receipt'],
                  'actual_seed_complete_region_runtime_source_qualification': approval['actual_seed_complete_region_runtime_source_qualification'],
                  'actual_pre_dispatch_process_gate': process_gate, 'command': command, 'cwd': str(seed.STAGE),
                  'literal_LEAN_PATH': env['LEAN_PATH'], 'literal_LEAN_NUM_THREADS': '2',
                  'inherited_LEAN_IMPORT_WORKERS': env.get('LEAN_IMPORT_WORKERS'),
                  'original_canonical_receipt_sha256': hashlib.sha256(original_raw).hexdigest(),
                  'new_source_invocations_this_phase': 0, 'new_audit_invocations_this_phase': 0,
                  'no_original_source_output_or_canonical_receipt_writes': True,
                  'no_audit_save_next_source_or_continuation': True,
                  'source_import_header_only_reuse_no_seed_authored_commands_reused': True,
                  'selected_axiom_outputs': 'NOT_ATTEMPTED_REQUIRES_SEPARATE_APPROVAL',
                  'loaded_image_errors_never_relabelled_clean': True}
        seed.save_atomic(receipt, report)
        done = threading.Event(); images = {}
        thread = threading.Thread(target=seed.loaded_image_observer, args=(done, common, observer, images), daemon=False)
        prefix = root / ('logs-load-' + variant)
        assert not Path(str(prefix) + '.stdout.txt').exists() and not Path(str(prefix) + '.stderr.txt').exists()
        seed.process_gate(common, approval); thread.start()
        try: guard = common.guarded_tree(command, seed.STAGE, env, prefix, timeout=3600)
        finally: done.set(); thread.join()
        if guard['attempted']: report['new_source_invocations_this_phase'] = 1
        report.update(own_job_resource_receipt=guard, actual_owned_child_exit=guard.get('exit'),
                      actual_owned_child_finished_utc=guard.get('finished_utc'), actual_command_state=guard['state'],
                      loaded_image_observation=images, isolated_output_artifacts=target_inventory(seed, library, module.split('.')[-1]))
        assert sha(source) == source_sha and not seed.source_outputs(source)
        assert common.read_bytes_shared(seed.CANONICAL) == original_raw and sha(seed.PLAN) == seed.PLAN_SHA
        common.sources_ready(plan, passed, manifest); seed.exact_hold_bindings(approval)
        actual_seed_inputs(seed, approval, root, own_sources, env, paths)
        seed.check_inventory(libraries)
        positive_files = {r['file']: r['sha256'] for r in libraries}
        report['load_positive_image_records_not_in_qualified_library_inventory'] = [r for r in images.get('observed_loaded_images', [])
                   if positive_files.get(r['file']) != r['sha256']]
        report['load_image_fidelity_error_or_missing_sample'] = bool(images.get('toolhelp_errors') or images.get('postexit_image_hash_errors')
                    or not images.get('successful_toolhelp_snapshots') or not images.get('observed_loaded_images')
                    or not any(r['file'] == str(seed.LEAN) and r['sha256'] == seed.LEAN_SHA
                               for r in images.get('observed_loaded_images', [])))
        if guard['state'] != 'PASS' or guard.get('exit') != 0:
            report['status'] = 'NOT_INVOKED_OR_ENVIRONMENT_OR_SOURCE_LOAD_CHECKPOINT_NO_PRIORITY_INFERENCE'
        else:
            assert target.is_file() and report['isolated_output_artifacts']
            if variant == 'B':
                comparison = compare(actual_seed['isolated_output_artifacts'], report['isolated_output_artifacts'])
                report['same_R141_binary_comparison'] = comparison
                report['all_same_R141_output_roles_binary_identical'] = all(r['binary_identical'] for r in comparison)
                report['status'] = ('PASS_SOURCE_ONLY_R141_HEADER_LOAD_BINARY_IDENTICAL_REQUIRES_ROOT_QUALIFICATION'
                                    if all(r['binary_identical'] for r in comparison) else 'PASS_SOURCE_ONLY_R141_HEADER_LOAD_BINARY_DIFFERENCES_REQUIRE_ROOT_REVIEW')
            else:
                report['status'] = 'PASS_SOURCE_ONLY_R142_CROSS_FILE_HEADER_LOAD_REQUIRES_ROOT_AND_EXACT_THREE_ENDPOINT_AUDIT'
                report['no_R142_ordinary_baseline_binary_equivalence_claim'] = True
        if images.get('foreign_Lean_observations') or report['load_positive_image_records_not_in_qualified_library_inventory']:
            report['status'] = 'ACTUAL_SOURCE_RESULT_PRESERVED_BUT_LEASE_OR_LIBRARY_FIDELITY_CONFLICT_REQUIRES_ROOT_REVIEW'
        report.update(finished_utc=stamp(), original_receipt_byte_identical_after=True,
                      all_prior_owned_source_and_artifact_identities_rehashed_after=True,
                      actual_selected_axiom_qualification='NOT_PERFORMED_NO_MAIN24_PROJECT_COMPLETION_CLAIM',
                      outer_actual_tool_exit_receipt_required_not_inferred_from_saved_label=True)
        seed.save_atomic(receipt, report)
        return 0 if report['status'].startswith('PASS_SOURCE_ONLY_') else 2
    except Exception as error:
        if report is not None:
            report.update(status='OWN_OPERATIONAL_OR_INPUT_FIDELITY_CHECKPOINT_REQUIRES_ROOT_REVIEW', error=repr(error),
                          finished_utc=stamp(), no_mathematical_or_priority_failure_inference=True)
            seed.save_atomic(receipt, report)
        raise
    finally:
        lock.seek(0); msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1); lock.close()

if __name__ == '__main__':
    # Direct caller must wait this actual outer exit. No execv/stdout detachment.
    sys.exit(main())
