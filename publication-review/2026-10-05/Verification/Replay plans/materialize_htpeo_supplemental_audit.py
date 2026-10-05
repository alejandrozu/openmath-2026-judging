"""Materialize one root-reviewed organizer audit; never compile or alter plan."""
from pathlib import Path
import datetime, hashlib, json
from lean_imports import read_imports

BASE = Path(__file__).resolve().parent
proposal_path = BASE / 'proposals/held-original-granular-source-review/htpeo-ramsey-supplemental-audit-root-review-proposal.json'
EXPECTED_PROPOSAL = '8e287337edef36637db8f8ce5869f1b399d8879ebb71a2a8c12c9307b4949fed'
EXPECTED_SUPPLEMENT = '4c570ea840ac2283717a34b5f83294def83edd27a056ad747cf60f273f91a80d'
EXPECTED_PLAN = '94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
EXPECTED_ORIGINAL_AUDIT = 'dff144f1890c6c255e9463a7e1fa29284166684ae96289b7949f1a363c6e9868'

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

assert digest(proposal_path) == EXPECTED_PROPOSAL
proposal = json.loads(proposal_path.read_bytes())
plan_path = Path(proposal['original_plan'])
assert digest(plan_path) == proposal['original_plan_sha256'] == EXPECTED_PLAN
plan_raw = plan_path.read_bytes()
plan = json.loads(plan_raw)
assert plan['id'] == 'htpeo-ramsey-current' and len(plan['modules']) == 2103
original_audit_path = Path(proposal['original_frozen_audit']['file'])
original_audit_raw = original_audit_path.read_bytes()
assert digest(original_audit_path) == EXPECTED_ORIGINAL_AUDIT
assert original_audit_raw.decode('utf-8') == proposal['original_frozen_audit']['exact_utf8_content']
graph_path = Path(proposal['complete_custom_import_closure']['original_full_source_graph'])
assert digest(graph_path) == proposal['complete_custom_import_closure']['original_full_source_graph_sha256']
graph = {row['module']: row for row in json.loads(graph_path.read_bytes())}
closure_path = Path(proposal['complete_custom_import_closure']['manifest'])
assert digest(closure_path) == proposal['complete_custom_import_closure']['sha256']
closure = {row['module']: row for row in json.loads(closure_path.read_bytes())}

target = Path(plan['source_dir']) / 'FreshAuditSupplement.lean'
receipt_path = BASE / 'htpeo-ramsey-supplemental-audit-materialization-2026-10-05.json'
assert not target.exists(), ('NO_OVERWRITE_TARGET_EXISTS', str(target))
assert not receipt_path.exists(), ('NO_OVERWRITE_RECEIPT_EXISTS', str(receipt_path))
verified_sources = {}
for entry in plan['modules']:
    file = Path(entry['file'])
    actual = digest(file)
    assert actual == entry['sha256'] == graph[entry['module']]['source_sha256'], ('FROZEN_SOURCE_IDENTITY_MISMATCH', entry['module'])
    verified_sources[entry['module']] = actual

path_modules = set()
for row in proposal['all_24_typed_declaration_and_import_mappings']:
    declaration_path = Path(row['declaration_source'])
    assert digest(declaration_path) == row['declaration_source_sha256'] == verified_sources[row['declaration_module']]
    path = row['supplement_import_path']
    assert path[0] in proposal['supplemental_audit_proposal']['minimal_direct_imports']
    assert path[-1] == row['declaration_module']
    for index, module in enumerate(path):
        assert module in closure and module in verified_sources
        assert closure[module]['source_sha256'] == verified_sources[module]
        source = Path(graph[module]['source'])
        actual_imports = [name for name in read_imports(source) if name != 'all']
        assert actual_imports == graph[module]['custom_imports'] + graph[module]['official_direct_imports'] or set(actual_imports) == set(graph[module]['custom_imports'] + graph[module]['official_direct_imports'])
        if index + 1 < len(path):
            assert path[index + 1] in actual_imports
        path_modules.add(module)
    text = declaration_path.read_text(encoding='utf-8')
    assert row['exact_statement_before_proof'] in text

supplement_bytes = proposal['supplemental_audit_proposal']['exact_utf8_content_proposal_only'].encode('utf-8')
assert len(supplement_bytes) == 1027 == proposal['supplemental_audit_proposal']['bytes']
assert hashlib.sha256(supplement_bytes).hexdigest() == EXPECTED_SUPPLEMENT
assert len(proposal['all_24_typed_declaration_and_import_mappings']) == 24
assert proposal['supplemental_audit_proposal']['fully_qualified_requests'] == [r['fully_qualified_name'] for r in proposal['all_24_typed_declaration_and_import_mappings']]

# Root approved this exact single path/content; exclusive creation forbids overwrite.
with target.open('xb') as stream:
    stream.write(supplement_bytes)
assert digest(target) == EXPECTED_SUPPLEMENT
assert plan_path.read_bytes() == plan_raw
assert original_audit_path.read_bytes() == original_audit_raw
assert digest(proposal_path) == EXPECTED_PROPOSAL
assert all(digest(Path(entry['file'])) == verified_sources[entry['module']] for entry in plan['modules'])

receipt = {
    'status': 'MATERIALIZED_EXACT_ROOT_APPROVED_SUPPLEMENTAL_ORGANIZER_AUDIT_NOT_COMPILED',
    'materialized_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'project': plan['id'], 'target': str(target), 'target_sha256': digest(target), 'target_bytes': len(supplement_bytes),
    'approved_proposal': str(proposal_path), 'approved_proposal_sha256': EXPECTED_PROPOSAL,
    'approval_scope': 'Root approved only exact1027-byte separately named FreshAuditSupplement.lean with SHA4c570ea840ac2283717a34b5f83294def83edd27a056ad747cf60f273f91a80d; no runner/plan/compiler action.',
    'original_audit': str(original_audit_path), 'original_audit_sha256_unchanged': EXPECTED_ORIGINAL_AUDIT,
    'original_plan': str(plan_path), 'original_plan_sha256_unchanged': EXPECTED_PLAN,
    'frozen_source_hashes_independently_checked_before_and_after': len(verified_sources),
    'all_24_declaration_source_and_import_path_identities_rechecked': True,
    'actual_import_path_modules_rechecked': sorted(path_modules),
    'supplement_import_roots': proposal['supplemental_audit_proposal']['minimal_direct_imports'],
    'selected_fully_qualified_names': proposal['supplemental_audit_proposal']['fully_qualified_requests'],
    'source_body_or_import_change': False, 'runner_or_plan_change': False,
    'Lean_invocations': 0, 'compiler_or_axiom_audit_verdict': 'NOT_RUN',
    'canonical_or_PDF_mutation': False, 'helper': str(Path(__file__).resolve()), 'helper_sha256': digest(Path(__file__)),
}
receipt['approval_scope'] = receipt['approval_scope'].replace('exact1027-byte', 'exact 1027-byte').replace('SHA4c570', 'SHA 4c570')
with receipt_path.open('x', encoding='utf-8') as stream:
    json.dump(receipt, stream, ensure_ascii=False, indent=2)
print(json.dumps({'status': receipt['status'], 'target': str(target), 'target_sha256': digest(target),
    'target_bytes': len(supplement_bytes), 'receipt': str(receipt_path), 'receipt_sha256': digest(receipt_path),
    'verified_frozen_sources': len(verified_sources), 'verified_import_path_modules': sorted(path_modules),
    'Lean_invocations': 0}, indent=2))
