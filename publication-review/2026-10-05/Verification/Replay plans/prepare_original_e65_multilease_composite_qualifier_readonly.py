"""Prepare only a SEPARATE multi-lease qualifier; no candidate import/execution.
Preserve the 2a33 original qualifier/packet/diffs, original runner and receipts.
"""
from pathlib import Path
from datetime import datetime, timezone
import ast, difflib, hashlib, json
B = Path(__file__).resolve().parent
OLD = B / 'qualify_original_e65_composite_199plusStd.py'
NEW = B / 'qualify_original_e65_multilease_composite_199plusStd.py'
OUT = B / 'proposals' / 'e65qual-multilease'


def sha(file):
    return hashlib.sha256(Path(file).read_bytes()).hexdigest()


CHAIN_FUNCTION = '''
def iso_utc(value):
    stamp = datetime.fromisoformat(value.replace('Z', '+00:00'))
    require(stamp.tzinfo is not None, 'Actual UTC-aware timestamp required')
    return stamp.astimezone(timezone.utc)


def validate_dispatch_chain(actual, actual_sha, review, report_file, previous_attempts,
                            sources, granular, whole, own_audits):
    first_checkpoint_sha = '2c8c10816da83a7e50ddf69b3d55fdbaf39bd3a5862d4ba2efc54da77d521b6c'
    first_lease_sha = '473930ee70fe1ca41bc93f244d4d2cc3e44433b899fbbcd20d0a3b6db09d6cb9'
    first_approval_sha = 'dcc4498db4d9ab834de346ccb2b5e23d61aa4e8c34ad805cc78398ac63986322'
    first_root183_sha = 'f778804b0fc1e1c547d5aa69c9e26d04d190235ced844b50eac6a481ff66a4da'
    segments = review.get('sole_dispatch_segments')
    if segments is None:
        # Preserve the original one-lease input schema without granting an
        # unreviewed restart. A noninitial final lease always needs the chain.
        require(review['sole_lease_sha256'] == first_lease_sha, 'Restart requires an explicit reviewed dispatch chain')
        segments = [{
            'lease_file': review['preserved_actual_dispatch_sole_lease_file'],
            'lease_sha256': first_lease_sha,
            'dispatch_approval_file': str(BASE / 'root-original-E65-solewhole16-sixAudit42-actual-dispatch-approval-20261005.json'),
            'dispatch_approval_sha256': first_approval_sha,
            'completed_start_checkpoint_file': str(BASE / 'original-E65-actual183-granular-immutable-checkpoint-20261005.json'),
            'completed_start_checkpoint_sha256': first_checkpoint_sha,
            'completed_end_checkpoint_file': str(report_file),
            'completed_end_checkpoint_sha256': actual_sha,
        }]
    require(isinstance(segments, list) and segments, 'An actual nonempty reviewed dispatch chain is required')
    require(len({r['lease_sha256'] for r in segments}) == len(segments), 'Dispatch leases must be unique')
    preserved_hashes = {row['sha256'] for row in previous_attempts} | {actual_sha}
    initial, unused = exact_json(BASE / 'original-E65-actual183-granular-immutable-checkpoint-20261005.json', first_checkpoint_sha)
    initial_rows = {row['module']: row for row in initial['builds']}
    require(set(initial_rows) == granular and all(row['exit'] == 0 and not row.get('stop_reason') and not row.get('is_endpoint_audit') for row in initial_rows.values()),
            'Initial checkpoint must contain exactly the actual183 successful own granular rows')
    original183_review, unused = exact_json(BASE / 'root-original-E65-actual183-granular-boundary-review-20261005.json', first_root183_sha)
    require(original183_review['actual_receipt_sha256'] == first_checkpoint_sha and
            original183_review['all183_raw_CLI_guard_options_logs_source_output_hashes_verified'] is True,
            'The initial actual183 root review is not preserved')
    prior_end_sha = first_checkpoint_sha
    covered_new_rows = {}
    summaries = []
    for index, segment in enumerate(segments):
        paths = {}
        records = {}
        for kind in ('lease', 'dispatch_approval', 'completed_start_checkpoint', 'completed_end_checkpoint'):
            paths[kind] = Path(segment[kind + '_file']).resolve()
            require(paths[kind].is_relative_to(BASE.resolve()), 'Dispatch history must be task-owned metadata')
            records[kind], unused = exact_json(paths[kind], segment[kind + '_sha256'])
        lease = records['lease']
        approval = records['dispatch_approval']
        start = records['completed_start_checkpoint']
        end = records['completed_end_checkpoint']
        require(segment['completed_start_checkpoint_sha256'] == prior_end_sha,
                'Every sole restart must bind the immediately preceding completed partial checkpoint')
        require(segment['completed_start_checkpoint_sha256'] in preserved_hashes and
                segment['completed_end_checkpoint_sha256'] in preserved_hashes,
                'A dispatch checkpoint is not preserved among the exact actual attempt receipts')
        if index == 0:
            require(segment['lease_sha256'] == first_lease_sha and segment['dispatch_approval_sha256'] == first_approval_sha,
                    'The original reviewed473930/dcc449 dispatch must begin the chain')
            require(approval['status'] == 'ROOT_APPROVED_ACTUAL_E65_SOLE_WHOLE16_SIX_AUDITS42_DISPATCH' and
                    approval['actual183_receipt_sha256'] == first_checkpoint_sha and
                    approval['root183_qualification_sha256'] == first_root183_sha, 'First dispatch approval differs')
        else:
            require(approval['status'] == 'ROOT_APPROVED_ACTUAL_E65_SOLE_WHOLE_RESTART_FROM_COMPLETED_PARTIAL_CHECKPOINT',
                    'An exact later root restart approval is required')
            require(approval['completed_partial_checkpoint_sha256'] == segment['completed_start_checkpoint_sha256'] and
                    approval['starting_checkpoint_all_owned_processes_finished'] is True and
                    approval['starting_checkpoint_no_owned_Lean_children'] is True,
                    'Later approval must qualify the actual completed, quiescent starting checkpoint')
        require(approval['source_plan_sha256'] == PLAN_SHA and approval['reviewed_runner_sha256'] == RUNNER_SHA,
                'Dispatch approval source/runner identity differs')
        require(approval['actual_sole_dispatch_lease_sha256'] == segment['lease_sha256'] and
                Path(approval['preserved_actual_sole_dispatch_lease_file']).resolve() == paths['lease'],
                'Dispatch approval does not bind the exact preserved lease')
        require(approval['global_Lean_processes_at_dispatch'] == {} and approval['maximum_global_Lean_jobs'] == 1,
                'Actual sole-dispatch approval must record no concurrent source compiler')
        require(approval['guard_private_limit_bytes'] == 10*GIB and approval['initial_commit_gate_bytes'] == 11*GIB,
                'Sole10/11 policy cannot change across restarts')
        dispatch_resources = approval['actual_fresh_resources']
        require(approval['free_disk_bytes'] >= 4_000_000_000 and dispatch_resources['free_physical_bytes'] >= 6*GIB and
                dispatch_resources['available_commit_bytes'] >= 11*GIB, 'Actual reviewed sole dispatch gate did not qualify')
        require(lease['holder_project'] == PROJECT and lease['source_plan_sha256'] == PLAN_SHA and
                lease['reviewed_runner_sha256'] == RUNNER_SHA and
                lease['whole_library_solo_authorized'] is True and
                lease['other_source_compilers_confirmed_held_or_finished'] is True and
                lease['granular_completed_receipt_sha256'] == segment['completed_start_checkpoint_sha256'] and
                set(lease['allowed_source_names']) == whole and set(lease['allowed_audit_names']) == own_audits,
                'Exact per-dispatch source/audit/checkpoint sole lease invalid')
        for name, checkpoint in (('start', start), ('end', end)):
            require(checkpoint['source_plan_sha256'] == PLAN_SHA and checkpoint['modules'] == actual['modules'] and
                    checkpoint['audit_modules'] == actual['audit_modules'] and checkpoint['endpoints'] == actual['endpoints'],
                    'Checkpoint frozen scientific/audit scope changed')
            require(checkpoint['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT' and checkpoint.get('finished_utc') and
                    not checkpoint.get('current_module') and not checkpoint.get('failed_invocations'),
                    'A completed successful partial boundary is required; no live/source-failure checkpoint may be relabeled')
            # An intermediate natural while-waiting boundary can retain its
            # dated waiting_for_module label. The next approval separately
            # confirms actual dispatcher exit and no owned child; final cannot.
            if name == 'end' and index == len(segments) - 1:
                require(not checkpoint.get('waiting_for_module'), 'Final completed scope must not retain a waiting label')
            rows = {row['module']: row for row in checkpoint['builds']}
            require(len(rows) == len(checkpoint['builds']) and granular <= set(rows) <= granular | whole | own_audits,
                    'Checkpoint rows duplicated or outside exact199/six scope')
            require(all(rows[module] == initial_rows[module] for module in granular),
                    'Any original183 successful source row changed across a restart')
            require(all(row['exit'] == 0 and not row.get('stop_reason') for row in rows.values()),
                    'Unsuccessful checkpoint rows cannot be composed as successful evidence')
        start_rows = {row['module']: row for row in start['builds']}
        end_rows = {row['module']: row for row in end['builds']}
        require(set(start_rows) <= set(end_rows) and all(end_rows[name] == row for name, row in start_rows.items()),
                'Previously successful whole/audit row/options/artifacts changed or disappeared')
        end_settings = end['resource_settings']['full_mathlib_source_mode']
        require(end_settings['lease_sha256'] == segment['lease_sha256'] and end_settings['coordinated_lease'] == lease and
                end['resource_settings']['runner_source_sha256'] == RUNNER_SHA,
                'Completed dispatch receipt does not preserve the corresponding actual lease/adapter')
        approval_time = iso_utc(approval['checked_utc'])
        lease_time = iso_utc(lease['checked_utc'])
        start_time = iso_utc(start['finished_utc'])
        end_time = iso_utc(end['finished_utc'])
        require(start_time <= approval_time and start_time <= lease_time and approval_time <= end_time and lease_time <= end_time,
                'Approval/lease timestamps do not follow a completed checkpoint')
        new_names = set(end_rows) - set(start_rows)
        require(new_names <= whole | own_audits, 'Restart manufactured new granular or external Std rows')
        for name in new_names:
            row = end_rows[name]
            require(name not in covered_new_rows and approval_time <= iso_utc(row['started_utc']) and
                    lease_time <= iso_utc(row['started_utc']) <= iso_utc(row['finished_utc']) <= end_time,
                    'A whole/audit invocation is duplicated or falls outside its approved sole lease interval')
            expected_cap = row['own_job_resource_receipt']['resource_policy']
            require(expected_cap['own_job_private_bytes'] == 10*GIB and expected_cap['initial_available_commit_bytes'] == 11*GIB,
                    'Corresponding actual invocation did not use the sole10/11 guard')
            require(row == next(current for current in actual['builds'] if current['module'] == name),
                    'An actual whole/audit row changed after its completed lease interval')
            covered_new_rows[name] = segment['lease_sha256']
        summaries.append({
            'dispatch_number': index + 1, 'lease_file': str(paths['lease']), 'lease_sha256': segment['lease_sha256'],
            'dispatch_approval_file': str(paths['dispatch_approval']), 'dispatch_approval_sha256': segment['dispatch_approval_sha256'],
            'completed_start_checkpoint_sha256': segment['completed_start_checkpoint_sha256'],
            'completed_end_checkpoint_sha256': segment['completed_end_checkpoint_sha256'],
            'retained_source_and_audit_rows': len(start_rows), 'new_whole_source_rows': sorted(new_names & whole),
            'new_audit_rows': sorted(new_names & own_audits), 'approved_dispatch_utc': approval['checked_utc'],
            'completed_interval_finished_utc': end['finished_utc'],
            'original183_and_all_previous_successful_rows_unchanged': True,
        })
        prior_end_sha = segment['completed_end_checkpoint_sha256']
    require(prior_end_sha == actual_sha and set(covered_new_rows) == whole | own_audits,
            'The chain does not cover all16 actual whole sources and allsix actual audits exactly once')
    last = segments[-1]
    require(actual['resource_settings']['full_mathlib_source_mode']['lease_sha256'] == last['lease_sha256'] and
            review['sole_lease_sha256'] == last['lease_sha256'], 'Final completion review/receipt does not bind the last actual lease')
    return summaries

'''


def main():
    assert sha(OLD) == '2a33dca5490be72972a10e0af9e4091525f08910a82448d86a59d001998bb53b'
    assert not NEW.exists() and not OUT.exists()
    old = OLD.read_text(encoding='utf8')
    old_packet = B / 'proposals/e65qual-final-v2/review-packet.json'
    assert sha(old_packet) == 'ed6d9c2508c3ac3fbf754dc8dc9be2571c161a89a2ff81fdc569b0ef6ea3dd77'
    old_full = B / 'proposals/e65qual-final-v2/candidate.full.diff'
    assert sha(old_full) == 'a9887aef3046e0e5673a5f5499b3b0b9346c1609881026c206c56133086602bc'
    OUT.mkdir(parents=True)
    preserved = OUT / 'preserved'
    preserved.mkdir()
    for source, name in ((OLD, 'prior_helper.py'), (old_packet, 'prior_packet.json'), (old_full, 'prior_full.diff')):
        (preserved / name).write_bytes(source.read_bytes())
        assert sha(preserved / name) == sha(source)
    new = old.replace('This starts no Lean, Lake, compiler, process guard or artifact-copy operation.',
                      'This multi-lease revision starts no Lean, Lake, compiler, process guard or artifact-copy operation.', 1)
    anchor = '\ndef main():\n'
    assert new.count(anchor) == 1
    new = new.replace(anchor, '\n' + CHAIN_FUNCTION + anchor, 1)
    a = new.index("        whole_settings = settings['full_mathlib_source_mode']\n")
    b = new.index('        previous_attempts = []\n', a)
    new = new[:a] + "        whole_settings = settings['full_mathlib_source_mode']\n        lease = whole_settings['coordinated_lease']\n" + new[b:]
    a = new.index("        require(lease['granular_completed_receipt_sha256'] in {a['sha256'] for a in previous_attempts},")
    b = new.index("        builds = actual['builds']\n", a)
    new = new[:a] + new[b:]
    anchor = "        require(set(lease['allowed_audit_names']) == own_audits, 'Actual sole audit lease changed')\n"
    assert new.count(anchor) == 1
    new = new.replace(anchor, anchor + "        dispatch_chain = validate_dispatch_chain(actual, arguments.actual_source_receipt_sha256, review, report_file,\n                                                 previous_attempts, sources, granular, whole, own_audits)\n", 1)
    anchor = "            'preserved_prior_attempts': previous_attempts, 'actual_sole_lease_sha256': whole_settings['lease_sha256'],\n"
    assert new.count(anchor) == 1
    new = new.replace(anchor, anchor + "            'actual_reviewed_sole_dispatch_chain': dispatch_chain,\n            'each_whole_and_audit_actual_row_covered_by_exact_reviewed_sole10_11_lease': True,\n", 1)
    ast.parse(new, filename=str(NEW))
    NEW.write_text(new, encoding='utf8', newline='\n')
    diff = OUT / 'multi-lease.minimal.diff'
    diff.write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True),
                                               fromfile=str(OLD), tofile=str(NEW))), encoding='utf8', newline='\n')
    full = OUT / 'multi-lease.NEW_FULL.diff'
    full.write_text(''.join(difflib.unified_diff([], new.splitlines(keepends=True), fromfile='/dev/null', tofile=str(NEW))), encoding='utf8', newline='\n')
    packet = {
        'status': 'PREPARED_ONLY_SEPARATE_MULTI_LEASE_E65_FINAL_COMPOSITE_QUALIFIER_NOT_EXECUTED',
        'created_utc': datetime.now(timezone.utc).isoformat(), 'producer_sha256': sha(__file__),
        'new_separate_helper': str(NEW), 'new_separate_helper_sha256': sha(NEW), 'passive_AST_parse': 'PASS_ONLY',
        'original_qualifier_file': str(OLD), 'original_qualifier_sha256_unchanged': sha(OLD),
        'preserved_original_helper': str(preserved / 'prior_helper.py'), 'preserved_original_helper_sha256': sha(preserved / 'prior_helper.py'),
        'preserved_original_packet_sha256': sha(preserved / 'prior_packet.json'),
        'preserved_original_full_diff_sha256': sha(preserved / 'prior_full.diff'),
        'minimal_diff': str(diff), 'minimal_diff_sha256': sha(diff), 'full_new_file_diff': str(full), 'full_new_file_diff_sha256': sha(full),
        'frozen_runner_sha256_unchanged': sha(B / 'run_original_e65_tactic_aware_source_plan.py'),
        'frozen200_plan_sha256_unchanged': sha(B / 'builds/sundai-erdos3-original-image-source/build-plan.json'),
        'fixed_first_actual_history': {
            'root183_review_sha256': 'f778804b0fc1e1c547d5aa69c9e26d04d190235ced844b50eac6a481ff66a4da',
            'actual183_checkpoint_sha256': '2c8c10816da83a7e50ddf69b3d55fdbaf39bd3a5862d4ba2efc54da77d521b6c',
            'actual_first_sole_lease_sha256': '473930ee70fe1ca41bc93f244d4d2cc3e44433b899fbbcd20d0a3b6db09d6cb9',
            'root_first_dispatch_approval_sha256': 'dcc4498db4d9ab834de346ccb2b5e23d61aa4e8c34ad805cc78398ac63986322',
        },
        'later_root_completion_review_additive_schema_TEMPLATE_ONLY': {
            'qualification_helper_sha256': sha(NEW), 'sole_lease_sha256': '<exact final lease SHA>',
            'sole_dispatch_segments': [{
                'lease_file': '<actual preserved dispatch lease file>', 'lease_sha256': '<actual lease SHA>',
                'dispatch_approval_file': '<actual per-dispatch root approval file>', 'dispatch_approval_sha256': '<actual root approval SHA>',
                'completed_start_checkpoint_file': '<actual completed starting checkpoint file>', 'completed_start_checkpoint_sha256': '<actual starting checkpoint SHA>',
                'completed_end_checkpoint_file': '<actual completed end-of-dispatch checkpoint file>', 'completed_end_checkpoint_sha256': '<actual ending checkpoint SHA>',
            }],
        },
        'later_restart_dispatch_approval_required_schema_TEMPLATE_ONLY': {
            'status': 'ROOT_APPROVED_ACTUAL_E65_SOLE_WHOLE_RESTART_FROM_COMPLETED_PARTIAL_CHECKPOINT',
            'source_plan_sha256': '0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15',
            'reviewed_runner_sha256': 'a2e5931c838e8b348de9fae4945b9f16ceb0883eaed51ca55f93e797deaa9e6d',
            'completed_partial_checkpoint_sha256': '<actual completed checkpoint SHA>',
            'starting_checkpoint_all_owned_processes_finished': '<future actual true>',
            'starting_checkpoint_no_owned_Lean_children': '<future actual true>',
            'actual_sole_dispatch_lease_sha256': '<actual reviewed lease SHA>',
            'preserved_actual_sole_dispatch_lease_file': '<same exact preserved lease file>',
            'global_Lean_processes_at_dispatch': '<actual empty process snapshot>', 'maximum_global_Lean_jobs': 1,
            'guard_private_limit_bytes': 10*2**30, 'initial_commit_gate_bytes': 11*2**30,
            'actual_fresh_resources': '<actual physical >=6GiB and commit >=11GiB>',
            'free_disk_bytes': '<actual >=4GB>', 'checked_utc': '<actual approval time>',
        },
        'intermediate_waiting_label_qualification': 'A finished natural while-waiting checkpoint may preserve its dated waiting_for_module label only with the next explicit root approval confirming dispatcher exit and no owned child. The final199/42 receipt must contain neither current_module nor waiting_for_module.',
        'exact_retention_and_dispatch_checks': ['All183 original raw successful rows unchanged in every checkpoint',
            'Every previously successful whole/audit row remains identical including source, command, options, guards, logs and artifact inventories',
            'Each later lease starts at exactly the preceding completed checkpoint SHA preserved in actual attempt history',
            'Every new whole/audit row appears once within its approval/lease-to-completed-boundary time interval under unchanged10/11 guard',
            'No interruption uses the original exact one-lease branch; restarts require explicit full chain',
            'Exactly199 own sources/six audits42prints plus separate prior accepted Std1/14, no fake200fresh or aliased output rows'],
        'candidate_imported_or_executed': False, 'Lean_or_compiler_or_guard_invoked': False,
        'existing_runner_receipt_source_guard_caps_canonical_PDF_or_artifacts_mutated': False,
    }
    output = OUT / 'review-packet.json'
    output.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + '\n', encoding='utf8', newline='\n')
    assert sha(OLD) == '2a33dca5490be72972a10e0af9e4091525f08910a82448d86a59d001998bb53b'
    print(json.dumps({'new_helper_sha256': sha(NEW), 'packet': str(output), 'packet_sha256': sha(output),
                      'minimal_diff_sha256': sha(diff), 'full_diff_sha256': sha(full), 'executed': False}))


if __name__ == '__main__':
    main()
