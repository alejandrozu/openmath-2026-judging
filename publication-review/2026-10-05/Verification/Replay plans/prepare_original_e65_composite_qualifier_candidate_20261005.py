"""Preparation only: passive AST review, full new-file diff, future gate schema.
Does not import or execute the candidate, launch any process, hash active proof
outputs, alter existing metadata, or claim completion of the future whole scope.
"""
from pathlib import Path
import ast, difflib, hashlib, json
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parent
TARGET = BASE / 'qualify_original_e65_composite_199plusStd.py'
OUT = BASE / 'proposals' / 'original-E65-final-composite-qualifier-candidate-20261005'


def sha(file):
    return hashlib.sha256(Path(file).read_bytes()).hexdigest()


def main():
    assert not OUT.exists(), 'Preserve the first concrete proposal; do not overwrite it'
    text = TARGET.read_text(encoding='utf8')
    ast.parse(text, filename=str(TARGET))
    tree = ast.parse(text)
    imports = sorted({node.name for item in ast.walk(tree) if isinstance(item, (ast.Import, ast.ImportFrom))
                      for node in (item.names if isinstance(item, ast.Import) else [])})
    assert not {'subprocess', 'ctypes', 'shutil'} & set(imports), 'Candidate must not launch or compile'
    plan = BASE / 'builds' / 'sundai-erdos3-original-image-source' / 'build-plan.json'
    assert sha(plan) == '0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15'
    runner = BASE / 'run_original_e65_tactic_aware_source_plan.py'
    assert sha(runner) == 'a2e5931c838e8b348de9fae4945b9f16ceb0883eaed51ca55f93e797deaa9e6d'
    current_file = BASE / 'sundai-erdos3-original-image-source-fresh-build.json'
    current_bytes = current_file.read_bytes()
    current = json.loads(current_bytes)
    OUT.mkdir(parents=True)
    diff = ''.join(difflib.unified_diff([], text.splitlines(keepends=True), fromfile='/dev/null', tofile=str(TARGET)))
    diff_file = OUT / 'qualify_original_e65_composite_199plusStd.NEW_FULL.diff'
    diff_file.write_text(diff, encoding='utf8', newline='\n')
    future_template = {
        'status': 'ROOT_APPROVED_ACTUAL_ORIGINAL_E65_199_42_AND_ACCEPTED_STD_COMPOSITE_QUALIFICATION',
        'qualification_authorized': '<future true only after root review of completed actual scopes>',
        'project': 'sundai-erdos3-original-image-source',
        'source_plan_sha256': sha(plan), 'runner_sha256': sha(runner),
        'qualification_helper_sha256': sha(TARGET),
        'actual_source_receipt_sha256': '<future exact finished own199/sixAudit42 raw receipt SHA>',
        'completed_own_source_count': 199, 'completed_granular_source_count': 183,
        'completed_sole_whole_source_count': 16, 'completed_sole_audit_count': 6,
        'selected_own_print_count': 42, 'accepted_Std_source_count': 1, 'accepted_Std_print_count': 14,
        'Std_acceptance_sha256': '5fcee11b0573d3187ef9fb37de9de8663a4ae2f2a94e76b3ac6bd0e5e48dc9eb',
        'all_owned_E65_source_processes_finished': '<future actual confirmation>',
        'actual_sole_whole_completion_reviewed': '<future actual confirmation>',
        'other_compilers_at_whole_dispatch_confirmed_held': '<future actual confirmation>',
        'Std_outputs_copied_linked_or_aliased': False,
        'sole_lease_sha256': '<exact original dispatch lease SHA, not a later RELEASED metadata revision>',
        'preserved_actual_dispatch_sole_lease_file': '<same exact saved original dispatch lease bytes>',
    }
    packet = {
        'status': 'PREPARED_ONLY_ORIGINAL_E65_FINAL_COMPOSITE_READ_ONLY_QUALIFIER_NOT_EXECUTED',
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'producer_file': str(Path(__file__).resolve()), 'producer_sha256': sha(__file__),
        'candidate_helper': str(TARGET), 'candidate_helper_sha256': sha(TARGET),
        'passive_AST_parse': 'PASS_ONLY_NO_IMPORT_OR_EXECUTION',
        'full_new_file_diff': str(diff_file), 'full_new_file_diff_sha256': sha(diff_file),
        'existing_runner_sha256_unchanged': sha(runner), 'frozen_original200_plan_sha256_unchanged': sha(plan),
        'dated_raw_receipt_snapshot_not_final_qualification': {
            'file': str(current_file), 'sha256': hashlib.sha256(current_bytes).hexdigest(),
            'status': current['status'], 'finished_utc': current.get('finished_utc'),
            'actual_own_source_passes_at_read': sum(r.get('exit') == 0 and not r.get('is_endpoint_audit') for r in current['builds']),
            'actual_own_audit_passes_at_read': sum(r.get('exit') == 0 and r.get('is_endpoint_audit') for r in current['builds']),
        },
        'future_root_completion_review_schema_TEMPLATE_ONLY_NO_ACTIVE_APPROVAL': future_template,
        'future_command_template_UNEXECUTED': [
            '<bundled Python>', '-X', 'utf8', str(TARGET), '--root-completion-review', '<future actual reviewed file>',
            '--root-completion-review-sha256', '<future actual review SHA>',
            '--actual-source-receipt-sha256', '<future actual completed raw receipt SHA>',
        ],
        'exact_future_qualification_scope': {
            'actual_this_route_scientific_sources': 199, 'actual_this_route_selected_prints': 42,
            'actual_this_route_organizer_audits': 6,
            'separately_accepted_previous_exact_Std_source': 1,
            'separately_accepted_previous_Std_selected_prints': 14,
            'separately_accepted_previous_Std_audits': 1,
            'distinct_scientific_bodies_with_composed_evidence': 200,
            'not_a_200_fresh_source_or_seven_new_audit_claim': True,
        },
        'qualification_checks_in_concrete_candidate': [
            'Exact frozen original193 recovered FC plus7 entrant scientific bytes, per-source explicit options and all7 unchanged organizer audit request files',
            'Exact pinned compiler binary, nine package HEAD/origin pairs and historical complete-cache PASS; current6223 recorded provider and1114 Std core source/artifact closures rehashed without claiming a new complete umbrella scan',
            'Actual199 unique successful own source rows and six successful own audit rows only, with exact actual command/cwd/options/raw log SHA/timestamps/own Windows-job resource policy and measured floors/caps',
            'The original183 checkpoint and historical attempts remain preserved by SHA; actual16/6 sole dispatch lease and later root completion-review SHA required',
            'Every present fresh own output type is current-hashed, receipt-matched and single-link; no donor output is reused',
            'Actual42 unique selected outputs independently reparsed standard/axiom-free only and matched to literal frozen requests',
            'Exact root5fcee acceptance binds immutable previous Std source1/audit1/raw14; current primary historical output hashes and present secondary current hashes remain distinguished',
            'Original route Std outputs must remain absent; no aliases, copies, fake rows or relabeled intentionally partial receipt',
            'Final separate additive JSON requires later root approval; source/scientific/canonical/PDF/status histories remain unchanged',
        ],
        'scientific_limits_retained': {
            'source_image_whole_FC_Git_revision_unknown': True,
            'original_Linux_container_executed': False,
            'historical_author_invocation_options_verified': False,
            'selected42_plus14_axiom_scope_only': True,
            'upstream_baseline_admissions_outside_selected_set_not_erased': True,
            'AP_equivalences_and_analytic_hypotheses_are_not_unconditional_open_problem_solutions': True,
            'no_novelty_priority_or_score_promotion': True,
        },
        'candidate_executed_or_imported': False, 'Lean_Lake_or_compiler_invoked': False,
        'aliases_or_existing_outputs_written': False, 'existing_runners_receipts_plans_sources_canonical_PDFs_modified': False,
    }
    out_file = OUT / 'review-packet.json'
    out_file.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + '\n', encoding='utf8', newline='\n')
    print(json.dumps({'status': packet['status'], 'packet': str(out_file), 'packet_sha256': sha(out_file),
                      'helper_sha256': sha(TARGET), 'diff_sha256': sha(diff_file)}))


if __name__ == '__main__':
    main()
