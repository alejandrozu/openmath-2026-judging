"""Clone the preserved v1 adapter with exact reviewed v2 identity bindings.

Preparation only: Python syntax check; never invokes Lean or the adapter.
The root-review path and digest must be supplied after the review is final.
"""
from pathlib import Path
import datetime
import difflib
import hashlib
import json
import py_compile
import sys

base = Path(__file__).resolve().parent
assert len(sys.argv) == 3, 'Root review file and exact SHA-256 are required'
review = Path(sys.argv[1]).resolve()
review_sha = sys.argv[2]
assert review.is_relative_to(base)
assert len(review_sha) == 64 and hashlib.sha256(review.read_bytes()).hexdigest() == review_sha
source = base / 'run_e169_import_pruned_diagnostic.py'
target = base / 'run_e169_tactic_specific_v2.py'
raw = source.read_bytes()
source_sha = hashlib.sha256(raw).hexdigest()
assert source_sha == 'e7fc2f56fd446e259f4be07617ed0aed6ac334e5048626aecbdd5c50ccec8eb2'
proposal_file = base / 'e169-tactic-specific-v2-proposal-2026-10-05.json'
proposal_raw = proposal_file.read_bytes()
assert hashlib.sha256(proposal_raw).hexdigest() == '6734d4fd8ac626a8cbfe1199167a401a085a1359693bcd95e74431139810d48f'
proposal = json.loads(proposal_raw)
assert hashlib.sha256(Path(proposal['diagnostic_plan']).read_bytes()).hexdigest() == proposal['diagnostic_plan_sha256']
text = raw.decode('utf-8')
old_project = 'sakana-erdos169-fourap-import-pruned-diagnostic'
new_project = 'sakana-erdos169-fourap-tactic-specific-v2'
assert text.count(old_project) == 2
text = text.replace(old_project, new_project)
start = text.index('# Separate operational diagnostic:')
end = text.index('deferred_whole_names=set()', start)
binding = f'''# Separate second operational diagnostic: both prior source replay receipts
# remain immutable. Only seven import headers differ; the exact scientific
# statements, proofs, options and comments outside those spans are preserved.
assert project=={new_project!r}, 'Dedicated second diagnostic runner only'
assert third_worker_guarded and not full_mathlib_source_mode and worker_threads==1
diagnostic_proposal_file=BASE/'e169-tactic-specific-v2-proposal-2026-10-05.json'
diagnostic_review_file=BASE/{review.relative_to(base).as_posix()!r}
assert hashlib.sha256(diagnostic_proposal_file.read_bytes()).hexdigest()=='6734d4fd8ac626a8cbfe1199167a401a085a1359693bcd95e74431139810d48f'
assert hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()=='8b183de4ccdcc543b46a8a54fd17a7b41a37ebd13afb8b53c9598e226f2b1e09'
assert hashlib.sha256(diagnostic_review_file.read_bytes()).hexdigest()=={review_sha!r}
diagnostic_proposal=json.loads(diagnostic_proposal_file.read_bytes())
for diagnostic_prior in diagnostic_proposal['unchanged_original_and_v1_receipts']:
 assert hashlib.sha256(Path(diagnostic_prior['receipt']).read_bytes()).hexdigest()==diagnostic_prior['sha256']
for diagnostic_module in plan['modules']:
 original=Path(diagnostic_module['original_file'])
 copied=Path(diagnostic_module['file'])
 assert hashlib.sha256(original.read_bytes()).hexdigest()==diagnostic_module['original_sha256']
 assert hashlib.sha256(copied.read_bytes()).hexdigest()==diagnostic_module['sha256']
diagnostic_changed_paths=set()
for diagnostic_change in diagnostic_proposal['source_changes']:
 original=BASE/'builds/sakana-erdos169-fourap'/diagnostic_change['relative_path']
 copied=dest/diagnostic_change['relative_path']
 diagnostic_changed_paths.add(str(copied))
 assert original.read_bytes()[diagnostic_change['original_replaced_span']['end_byte_exclusive']:] == copied.read_bytes()[diagnostic_change['replacement_span']['end_byte_exclusive']:]
for diagnostic_module in plan['modules']:
 if diagnostic_module['file'] not in diagnostic_changed_paths:
  assert Path(diagnostic_module['original_file']).read_bytes()==Path(diagnostic_module['file']).read_bytes()
assert hashlib.sha256((dest/'FreshAudit1.lean').read_bytes()).hexdigest()==diagnostic_proposal['unchanged_audit_source_sha256']
for diagnostic_import in diagnostic_proposal['official_direct_module_identity']:
 assert hashlib.sha256(Path(diagnostic_import['source']).read_bytes()).hexdigest()==diagnostic_import['source_sha256']
 assert hashlib.sha256(Path(diagnostic_import['official_olean']).read_bytes()).hexdigest()==diagnostic_import['official_olean_sha256']
diagnostic_closure_file=Path(diagnostic_proposal['complete_dependency_source_closure']['source_closure_manifest'])
assert hashlib.sha256(diagnostic_closure_file.read_bytes()).hexdigest()==diagnostic_proposal['complete_dependency_source_closure']['source_closure_manifest_sha256']
for diagnostic_dep in json.loads(diagnostic_closure_file.read_bytes()):
 assert hashlib.sha256(Path(diagnostic_dep['source']).read_bytes()).hexdigest()==diagnostic_dep['source_sha256']
for diagnostic_receipt in diagnostic_proposal['runtime_and_cache_receipt_identities']:
 assert hashlib.sha256(Path(diagnostic_receipt['file']).read_bytes()).hexdigest()==diagnostic_receipt['sha256']
plan['import_pruned_diagnostic_provenance']={{'proposal_file':str(diagnostic_proposal_file),'proposal_sha256':hashlib.sha256(diagnostic_proposal_file.read_bytes()).hexdigest(),'root_identity_review':str(diagnostic_review_file),'root_identity_review_sha256':hashlib.sha256(diagnostic_review_file.read_bytes()).hexdigest(),'prior_receipt_identities':diagnostic_proposal['unchanged_original_and_v1_receipts'],'qualification':'SECOND_SEPARATE_OPERATIONAL_ROUTE_IMPORT_ONLY_SEVEN_HEADERS_SCIENTIFIC_BODIES_BYTE_IDENTICAL_NOT_ORIGINAL_SOURCE_PASS','closure_units':{{'Mathlib_modules':738,'official_core_or_package_modules':1754,'total_modules':2492,'v1_Mathlib_modules':2815}}}}

'''
text = text[:start] + binding + text[end:]
target.write_text(text, encoding='utf-8', newline='')
py_compile.compile(str(target), doraise=True)
assert source.read_bytes() == raw
for prior in proposal['unchanged_original_and_v1_receipts']:
    assert hashlib.sha256(Path(prior['receipt']).read_bytes()).hexdigest() == prior['sha256']
diff = ''.join(difflib.unified_diff(raw.decode('utf-8').splitlines(True), text.splitlines(True),
    fromfile='immutable-v1-diagnostic-runner', tofile='separate-v2-tactic-specific-runner'))
diff_file = base / 'e169-tactic-specific-v2-runner-only.diff'
diff_file.write_text(diff, encoding='utf-8', newline='')
manifest = {
    'status': 'PREPARED_SYNTAX_CHECKED_NO_LEAN_DISPATCH',
    'prepared_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'immutable_v1_runner': str(source), 'immutable_v1_runner_sha256': source_sha,
    'v1_runner_unchanged': True, 'live_main_runner_not_read_or_modified': True,
    'separate_v2_runner': str(target), 'separate_v2_runner_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
    'runner_diff': str(diff_file), 'runner_diff_sha256': hashlib.sha256(diff_file.read_bytes()).hexdigest(),
    'root_review_file': str(review), 'root_review_sha256': review_sha,
    'proposal_sha256': hashlib.sha256(proposal_raw).hexdigest(),
    'source_plan_sha256': proposal['diagnostic_plan_sha256'],
    'original_and_v1_receipts_unchanged': proposal['unchanged_original_and_v1_receipts'],
    'only_code_changes': ['Dedicated diagnostic project whitelist identifier',
        'Exact v2 proposal/plan/root-review, source-body, original/v1 receipt, official-import and closure identity bindings/provenance'],
    'resource_semantics': 'Unchanged -j1 six-GiB owned Windows job/five-GiB initial commit; four-billion-byte initial disk/six-GiB physical and one-GiB commit/three-GiB physical/one-billion-byte disk floors',
    'custom_artifact_reuse': 'None on first invocation; v2 starts without original/v1 custom artifacts',
    'prepared_pilot_command': ['Python', '-X', 'utf8', str(target), new_project, '1', '--pilot-third-slot'],
    'dispatch_authorization': 'NONE; wait for explicit root runner review and resource lease',
}
manifest_file = base / 'e169-tactic-specific-v2-runner-preparation.json'
manifest_file.write_text(json.dumps(manifest, indent=2), encoding='utf-8')
print(json.dumps(manifest, indent=2))
