"""Qualify an actual completed import-only replay; never invokes Lean.

The independently supplied completed receipt digest is required. This record
cannot turn the original frozen-source replay into PASS.
"""
from pathlib import Path
import datetime
import hashlib
import json
import sys
from audit_axioms import parse

base = Path(__file__).resolve().parent
assert len(sys.argv) == 2, 'Completed receipt SHA-256 required'
expected_receipt_sha = sys.argv[1]

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

receipt_file = base / 'sakana-erdos169-fourap-tactic-specific-v2-fresh-build.json'
assert sha(receipt_file) == expected_receipt_sha
receipt = json.loads(receipt_file.read_bytes())
assert receipt['status'] == 'PASS' and len(receipt['modules']) == 22
assert not receipt['failed_invocations']
assert receipt['version'] == '4.34.1'
assert receipt['mathlib_pin'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
proposal_file = base / 'e169-tactic-specific-v2-proposal-2026-10-05.json'
assert sha(proposal_file) == '6734d4fd8ac626a8cbfe1199167a401a085a1359693bcd95e74431139810d48f'
q = json.loads(proposal_file.read_bytes())
plan_file = Path(q['diagnostic_plan'])
assert sha(plan_file) == q['diagnostic_plan_sha256'] == '8b183de4ccdcc543b46a8a54fd17a7b41a37ebd13afb8b53c9598e226f2b1e09'
plan = json.loads(plan_file.read_bytes())
review_file = base / 'e169-tactic-specific-v2-root-identity-review.json'
assert sha(review_file) == 'bded1e27d1a92e1d505bb51c984aa5a1f1b2a42537afcf9e37c83b5bb19ad64f'
review = json.loads(review_file.read_bytes())
runner = base / 'run_e169_tactic_specific_v2.py'
assert sha(runner) == '1a191a331fc672e4ae369c51d819d13274cd28b1ca47300f023f19907fc516b6'
assert receipt['resource_settings']['runner_source_sha256'] == sha(runner)
for prior in q['unchanged_original_and_v1_receipts']:
    assert sha(prior['receipt']) == prior['sha256']
original_plan_file = Path(plan['original_source_plan'])
assert sha(original_plan_file) == '48d697f923d0013aa348581e3733f754ffaf35c3491ff6b30e22c783632b8abe'
original_plan = json.loads(original_plan_file.read_bytes())
assert plan['lean_options'] == original_plan['lean_options']
assert plan['endpoints'] == original_plan['endpoints']
original = {row['module']: row for row in original_plan['modules']}
changes = {row['module']: row for row in q['source_changes']}
source_identities = []
for row in plan['modules']:
    name = row['module']
    a = Path(original[name]['file']).read_bytes()
    b = Path(row['file']).read_bytes()
    assert hashlib.sha256(a).hexdigest() == original[name]['sha256'] == row['original_sha256']
    assert hashlib.sha256(b).hexdigest() == row['sha256']
    if name in changes:
        c = changes[name]
        assert a[c['original_replaced_span']['end_byte_exclusive']:] == b[c['replacement_span']['end_byte_exclusive']:]
    else:
        assert a == b
    source_identities.append({'module': name, 'scientific_body_options_comments_identical': True,
        'original_source_sha256': original[name]['sha256'], 'diagnostic_source_sha256': row['sha256']})
for audit in plan['audit_modules']:
    assert sha(Path(plan['source_dir']) / audit) == sha(Path(original_plan['source_dir']) / audit) == q['unchanged_audit_source_sha256']
closure_file = Path(q['complete_dependency_source_closure']['source_closure_manifest'])
assert sha(closure_file) == q['complete_dependency_source_closure']['source_closure_manifest_sha256']
closure = {row['module']: row for row in json.loads(closure_file.read_bytes())}
for artifact in review['official_artifact_identities']:
    entry = closure[artifact['module']]
    assert sha(entry['source']) == artifact['source_sha256']
    assert sha(entry['official_olean']) == artifact['official_cached_olean_sha256']

source_builds = [row for row in receipt['builds'] if not row['is_endpoint_audit']]
audit_builds = [row for row in receipt['builds'] if row['is_endpoint_audit']]
assert len(source_builds) == 22 and len({row['module'] for row in source_builds}) == 22
assert {row['module'] for row in source_builds} == {row['module'] for row in plan['modules']}
assert len(audit_builds) == 1
output_identities = []
guards = []
for row in receipt['builds']:
    assert row['exit'] == 0 and row.get('stop_reason') is None
    g = row['own_job_resource_receipt']
    assert g['state'] == 'PASS' and g['own_job_assignment_before_resume'] == 'PASS'
    assert g['resource_policy']['own_job_private_bytes'] == 6 * 2**30
    assert g['resource_policy']['initial_available_commit_bytes'] == 5 * 2**30
    assert g['minimum_disk_free_bytes'] >= 1_000_000_000
    assert g['minimum_physical_available_bytes'] >= 3 * 2**30
    assert g['minimum_available_commit_bytes'] >= 2**30
    assert g['job_peak_aggregate_private_bytes'] <= 6 * 2**30
    assert '-j1' in row['command']
    for artifact in row['artifacts']:
        assert sha(artifact['file']) == artifact['sha256']
        output_identities.append(dict(artifact, module=row['module']))
    guards.append({'module': row['module'], 'seconds': row['seconds'],
        'owned_job_private_peak_bytes': g['job_peak_aggregate_private_bytes'],
        'minimum_disk_bytes': g['minimum_disk_free_bytes'],
        'minimum_physical_bytes': g['minimum_physical_available_bytes'],
        'minimum_available_commit_bytes': g['minimum_available_commit_bytes']})
actual = parse(audit_builds[0]['stdout'])
assert audit_builds[0]['selected_endpoint_print_coverage']['status'] == 'PASS'
selected = receipt['selected_audit_axiom_review']
assert len(selected) == 1 and selected[0]['endpoint'] == 'Erdos3Candidate.explicit_four_ap_free_reciprocal_gt'
assert selected[0]['classification'] == 'STANDARD_KERNEL_AXIOMS'
assert not selected[0]['native_axioms'] and not selected[0]['unrecognized_axioms']
assert 'sorryAx' not in selected[0]['axioms']
assert actual == selected
result = {
    'status': 'PASS_BODY_IDENTICAL_IMPORT_ONLY_ROUTE_SELECTED_ENDPOINT_STANDARD_AXIOMS',
    'qualified_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'receipt': str(receipt_file), 'receipt_sha256': expected_receipt_sha,
    'finished_utc': receipt['finished_utc'], 'runner_sha256': sha(runner),
    'source_plan_sha256': sha(plan_file), 'proposal_sha256': sha(proposal_file),
    'cold_root_identity_review_sha256': sha(review_file),
    'authored_source_modules_passed': 22, 'selected_endpoint_prints': 1,
    'scientific_body_identity_checks': source_identities,
    'actual_output_identities': output_identities, 'actual_selected_axiom_review': actual,
    'guard_measurements': guards,
    'official_dependency_source_and_artifact_hashes_rechecked': 2492,
    'closure_units': {'Mathlib_sources': 738, 'core_or_package_sources': 1754,
        'total_sources': 2492, 'v1_Mathlib_sources': 2815},
    'original_and_v1_receipts_unchanged': q['unchanged_original_and_v1_receipts'],
    'qualification': 'Exact scientific bodies/options/comments and unchanged selected audit verified using seven import-only header replacements. This qualifies the separate operational route, not original frozen-source PASS; original15/22 and v1 7/22 remain historical resource-limited receipts.',
    'publication_decisions': 'Originality, competition scoring and author approval unchanged and separate',
}
out = base / 'e169-tactic-specific-v2-completed-qualification.json'
assert not out.exists(), 'Never replace a dated complete qualification'
out.write_text(json.dumps(result, indent=2), encoding='utf-8')
print(json.dumps({'status': result['status'], 'output': str(out),
    'qualification_sha256': sha(out), 'receipt_sha256': expected_receipt_sha,
    'sources': 22, 'selected_actual_axioms': actual}, indent=2))
