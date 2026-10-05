"""Resolve an exact official/core closure and inspect owned-output eligibility only.

This creates metadata, never stages Lean source, copies compiled output or invokes
Lean. The three reviewed hypothetical import replacements are kept unchanged.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
from collections import Counter
from lean_imports import stripped

BASE = Path(__file__).resolve().parent
ORIGINAL = BASE / 'builds/htpeo-dms-current'
MATHLIB = BASE / 'dependencies/4.33.1/mathlib'
RUNTIME = BASE / 'runtimes/lean-4.33.1-windows'
DEST = BASE / 'proposals/htpeo-dms-current-import-pruned-diagnostic'
PRIOR = BASE / 'dms-full228-import-only-diagnostic-preparation-20261005.json'
RECEIPT = BASE / 'htpeo-dms-current-fresh-build.json'
EXPECTED_RECEIPT = 'feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238'
PLAN = ORIGINAL / 'build-plan.json'

def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()

def sha_file(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()

def read(path):
    return json.loads(Path(path).read_bytes())

def save_new(path, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8')
    if path.exists():
        raise RuntimeError('Refusing to replace an existing immutable preparation: ' + str(path))
    path.write_bytes(raw)
    return sha_bytes(raw)

def imports_of(raw):
    cleaned = stripped(raw.decode('utf-8'))
    clauses, names = [], []
    for line in cleaned.splitlines():
        match = re.match(r'^\s*(?P<public>public\s+)?(?P<meta>meta\s+)?import\s+(?P<names>.*)$', line)
        if not match:
            continue
        tokens = match.group('names').split()
        all_modifier = bool(tokens and tokens[0] == 'all')
        actual = [name.replace('«', '').replace('»', '') for name in tokens if name != 'all']
        clauses.append({'modules': actual, 'public': bool(match.group('public')),
                        'meta': bool(match.group('meta')), 'import_all': all_modifier})
        names.extend(actual)
    prelude = bool(re.search(r'^\s*prelude\s*$', cleaned, re.MULTILINE))
    return list(dict.fromkeys(names)), prelude, clauses

assert sha_file(PRIOR) == '21ff23bd735d882378c99ade5ba069ce3b2ec998caebe68994faeb8548e603a3'
prior = read(PRIOR)
assert sha_file(PLAN) == prior['original_plan_sha256'] == '55627b070d16fa8027c02a94d8d97b22d5e24d5598bd09ef76e724d14d1426a3'
plan = read(PLAN)
proposed_plan_path = Path(prior['proposed_plan_file']).resolve()
assert sha_file(proposed_plan_path) == prior['proposed_plan_sha256'] == 'ecc8404e39c79c81799d42148170b1a70e16a8103d059ea7998e13508c413742'
proposed_plan = read(proposed_plan_path)
assert sha_file(RECEIPT) == EXPECTED_RECEIPT
receipt = read(RECEIPT)
assert len(plan['modules']) == len(proposed_plan['modules']) == 228
assert plan['lean_options'] == proposed_plan['lean_options']
assert plan['endpoints'] == proposed_plan['endpoints'] and plan['audit_modules'] == proposed_plan['audit_modules']
assert not Path(proposed_plan['source_dir']).exists(), 'This preparation must remain metadata-only.'

changes = {row['module']: row for row in prior['only_import_changes']}
assert set(changes) == {'BlockStar', 'SeamSeq', 'InflationDefs'}
original_entries = {row['module']: row for row in plan['modules']}
proposed_entries = {row['module']: row for row in proposed_plan['modules']}
custom = {}
for name, entry in original_entries.items():
    raw = Path(entry['file']).read_bytes()
    assert sha_bytes(raw) == entry['sha256'] == proposed_entries[name]['original_sha256']
    if name in changes:
        row = changes[name]
        start, end = row['replaced_bytes_start'], row['replaced_bytes_end']
        assert raw[start:end] == b'import Mathlib'
        replacement = row['proposed_header_span'].encode('utf-8')
        hypothetical = raw[:start] + replacement + raw[end:]
        assert raw[:start] + raw[end:] == hypothetical[:start] + hypothetical[start+len(replacement):]
        assert sha_bytes(raw[:start]+raw[end:]) == row['remainder_body_sha256']
        assert sha_bytes(hypothetical) == row['proposed_source_sha256']
    else:
        hypothetical = raw
    assert sha_bytes(hypothetical) == proposed_entries[name]['sha256']
    explicit, prelude, clauses = imports_of(hypothetical)
    custom[name] = {'module': name, 'original_source': entry['file'],
        'original_source_sha256': sha_bytes(raw), 'proposed_source_sha256': sha_bytes(hypothetical),
        'staged_source_identity': 'NOT_STAGED_READ_ONLY_HYPOTHETICAL_BYTES_ONLY',
        'imports': explicit, 'prelude': prelude, 'implicit_Init_included': not prelude,
        'import_clauses': clauses, 'body_options_comments_identical': True,
        'entire_source_unchanged': name not in changes}
assert not any('Mathlib' in row['imports'] or 'Mathlib.Tactic' in row['imports'] for row in custom.values())

roots = [(MATHLIB, MATHLIB / '.lake/build/lib/lean', 'mathlib')]
roots += [(p, p / '.lake/build/lib/lean', p.name)
          for p in sorted((MATHLIB / '.lake/packages').iterdir()) if p.is_dir()]
roots += [(RUNTIME / 'src/lean', RUNTIME / 'lib/lean', 'official_lean_core'),
          (RUNTIME / 'src/lean/lake', RUNTIME / 'lib/lean', 'official_lake')]
official = {}
missing = set()

def visit(name):
    if name in official:
        return
    relative = Path(name.replace('.', '/') + '.lean')
    for source_root, lib_root, identity in roots:
        source = source_root / relative
        if source.is_file():
            break
    else:
        missing.add(name)
        return
    raw = source.read_bytes()
    explicit, prelude, clauses = imports_of(raw)
    implicit = name != 'Init' and not prelude
    dependencies = list(dict.fromkeys(explicit + (['Init'] if implicit else [])))
    artifact = lib_root / Path(name.replace('.', '/') + '.olean')
    assert artifact.is_file(), ('Missing official olean', name, str(artifact))
    official[name] = {'module': name, 'identity_root': identity, 'source': str(source),
        'source_sha256': sha_bytes(raw), 'source_bytes': len(raw),
        'official_olean': str(artifact), 'official_olean_bytes': artifact.stat().st_size,
        'imports': explicit, 'prelude': prelude, 'implicit_Init_included': implicit,
        'import_clauses': clauses, 'effective_import_dependencies': dependencies,
        'import_all_exposure_preserved_in_official_source_bytes': any(row['import_all'] for row in clauses)}
    for dependency in dependencies:
        visit(dependency)

external = set()
custom_edges = {}
for name, row in custom.items():
    custom_edges[name] = [dep for dep in row['imports'] if dep in custom]
    external.update(dep for dep in row['imports'] if dep not in custom)
    if row['implicit_Init_included']:
        external.add('Init')

audits = []
for row in prior['original_and_proposed_audit_identity_inventory']:
    source = Path(row['original_file'])
    assert sha_file(source) == row['original_and_proposed_sha256']
    explicit, prelude, clauses = imports_of(source.read_bytes())
    external.update(dep for dep in explicit if dep not in custom)
    if not prelude:
        external.add('Init')
    audits.append(dict(row, imports=explicit, prelude=prelude, implicit_Init_included=not prelude,
                       import_clauses=clauses, staged_source_identity='NOT_STAGED_READ_ONLY_HYPOTHETICAL_BYTES_ONLY'))
for name in sorted(external):
    visit(name)
assert not missing, sorted(missing)
assert not {'Mathlib', 'Mathlib.Tactic'} & set(official)
official_edges = {name: set(row['effective_import_dependencies']) for name, row in official.items()}
assert all(deps <= set(official) for deps in official_edges.values())
reachable, todo = set(), list(external)
while todo:
    name = todo.pop()
    if name not in reachable:
        reachable.add(name)
        todo.extend(official_edges[name] - reachable)
assert reachable == set(official), 'Unreachable or missing official graph nodes.'

# Exact package identity is checked again without any Lean/cache invocation.
pins_file = BASE / 'dependencies-4.33.1-verified-git.json'
pins = read(pins_file)
actual_pins = []
for pin in pins:
    directory = MATHLIB if pin['name'] == 'mathlib' else MATHLIB / '.lake/packages' / pin['name']
    rev = subprocess.run(['git', '-C', str(directory), 'rev-parse', 'HEAD'], capture_output=True,
                         text=True, check=True).stdout.strip()
    origin = subprocess.run(['git', '-C', str(directory), 'remote', 'get-url', 'origin'], capture_output=True,
                            text=True, check=True).stdout.strip()
    assert rev == pin['rev'] and origin == pin['url'], (pin['name'], rev, origin)
    actual_pins.append(dict(pin, actual_HEAD=rev, actual_origin=origin, matches_expected=True))

# A complete source graph plus actual compiled-artifact identity is stronger than
# merely stopping at core roots or assuming artifacts from a version label.
for index, name in enumerate(sorted(official), 1):
    row = official[name]
    row['official_olean_sha256'] = sha_file(row['official_olean'])
    if index % 500 == 0:
        print('Hashed official source/artifact units:', index, '/', len(official), flush=True)
direct = []
for name in sorted(external):
    row = dict(official[name])
    artifact = Path(row['official_olean'])
    siblings = []
    for suffix in ['.olean', '.olean.private', '.olean.server', '.ilean']:
        candidate = artifact.with_suffix(suffix)
        if candidate.is_file():
            siblings.append({'file': str(candidate), 'bytes': candidate.stat().st_size,
                             'sha256': sha_file(candidate)})
    row['direct_compiled_artifact_identity'] = siblings
    direct.append(row)

def custom_closure(name):
    result, pending = set(), [name]
    while pending:
        item = pending.pop()
        if item not in result:
            result.add(item)
            pending.extend(custom_edges[item])
    return result

passed = {}
for row in receipt['builds']:
    if (not row.get('is_endpoint_audit') and row.get('exit') == 0
            and row.get('stop_reason') is None and row.get('artifacts')):
        passed[row['module']] = row
assert len(passed) == 119
own_artifact_identity = {}
for name, row in passed.items():
    assert row['source_sha256'] == original_entries[name]['sha256']
    artifacts = []
    for old in row['artifacts']:
        file = Path(old['file'])
        assert file.is_file() and file.stat().st_size == old['bytes']
        assert sha_file(file) == old['sha256'], ('Changed owned output', name)
        artifacts.append(dict(old, measured_current_sha256=old['sha256'], matches_receipt=True))
    own_artifact_identity[name] = artifacts

reuse = []
for name in sorted(passed):
    closure = custom_closure(name)
    changed_reachable = sorted(closure & set(changes))
    not_passed = sorted(closure - set(passed))
    eligible = not changed_reachable and not not_passed
    deps = sorted({dep for item in closure for dep in custom[item]['imports'] if dep not in custom} | {'Init'})
    reuse.append({'module': name,
        'eligibility': 'VERIFIED_ORIGINAL_UNAFFECTED_CANDIDATE_PENDING_STAGED_IDENTITY_AND_ROOT_REUSE_POLICY' if eligible
                       else 'MUST_REMAIN_COLD_CHANGED_HEADER_REACHABLE_OR_UNVERIFIED_CUSTOM_DEPENDENCY',
        'eligible_on_original_identity_checks_only': eligible,
        'original_PASS_row_source_sha256': passed[name]['source_sha256'],
        'original_PASS_row_sha256': sha_bytes(json.dumps(passed[name], sort_keys=True, ensure_ascii=False).encode()),
        'current_owned_artifacts': own_artifact_identity[name],
        'custom_dependency_closure': sorted(closure), 'changed_headers_reachable': changed_reachable,
        'custom_dependencies_without_fresh_original_PASS': not_passed,
        'all_custom_closure_sources_whole_byte_unchanged': not changed_reachable,
        'whole_byte_identity_hypothetically_preserved': custom[name]['entire_source_unchanged'],
        'official_direct_roots_for_complete_custom_closure': deps,
        'official_dependency_identity': 'EXACT_CURRENT_GIT_PINS_AND_COMPLETE_OFFICIAL_SOURCE/OLEAN_HASH_GRAPH',
        'staged_source_identity': 'NOT_STAGED; MUST_VALIDATE_ACTUAL_STAGE_AND_EVERY_CUSTOM_DEPENDENCY_BEFORE_REUSE',
        'copied_or_marked_reusable': False})

DEST.mkdir(exist_ok=True)
closure_file = DEST / 'official-full-source-artifact-closure.json'
closure_sha = save_new(closure_file, [official[name] for name in sorted(official)])
reuse_file = DEST / 'original119-owned-unaffected-reuse-eligibility.json'
eligible_names = [row['module'] for row in reuse if row['eligible_on_original_identity_checks_only']]
reuse_sha = save_new(reuse_file, {'status': 'READ_ONLY_ELIGIBILITY_NO_COPY_NO_REUSE_MARK_NO_STAGED_SOURCES',
    'original119_receipt': str(RECEIPT), 'original119_receipt_sha256': EXPECTED_RECEIPT,
    'original119_PASS_count': 119, 'eligible_candidate_count': len(eligible_names),
    'eligible_candidate_modules': eligible_names, 'must_remain_cold_original_pass_count': 119-len(eligible_names),
    'unpassed_original_sources_must_remain_cold': 228-119,
    'actual_staged_identity_and_reuse_policy': 'NOT_YET_SATISFIED; ROOT_REVIEW_REQUIRED',
    'official_complete_identity_manifest': str(closure_file), 'official_complete_identity_manifest_sha256': closure_sha,
    'modules': reuse})
summary = {
    'status': 'READ_ONLY_COMPLETE_OFFICIAL_CLOSURE_AND_OWNED_OUTPUT_ELIGIBILITY_NO_SOURCE_STAGE_OR_LEAN_INVOCATION',
    'prepared_utc': datetime.now(timezone.utc).isoformat(),
    'prior_full228_proposal': str(PRIOR), 'prior_full228_proposal_sha256': sha_file(PRIOR),
    'hypothetical_plan': str(proposed_plan_path), 'hypothetical_plan_sha256': sha_file(proposed_plan_path),
    'original_source_plan': str(PLAN), 'original_source_plan_sha256': sha_file(PLAN),
    'immutable_original119_receipt_binding': {'file': str(RECEIPT), 'sha256': EXPECTED_RECEIPT,
        'actual_original_cold_source_PASS_count': 119,
        'completed_boundary': str(BASE/'dms-119-waiting-boundary-20261005T022853Z.completed.json'),
        'completed_boundary_sha256': sha_file(BASE/'dms-119-waiting-boundary-20261005T022853Z.completed.json'),
        'source_bytes_and_receipt_unchanged': True},
    'all_original_three_header_diffs_unchanged': prior['only_import_changes'],
    'all228_custom_source_identity_and_closed_custom_graph': list(custom.values()),
    'audit_identity': audits, 'original_audit_and_endpoint_ids_unchanged': True,
    'expected_selected_print_count': prior['expected_selected_print_count'],
    'exact_runtime_receipt': {'file': str(BASE/'lean-4.33.1-installation.json'),
        'sha256': sha_file(BASE/'lean-4.33.1-installation.json')},
    'exact_official_cache_receipt': {'file': str(BASE/'mathlib-4.33.1-cache-retry.json'),
        'sha256': sha_file(BASE/'mathlib-4.33.1-cache-retry.json')},
    'dependency_pin_receipt_sha256': sha_file(pins_file), 'current_actual_git_pins': actual_pins,
    'complete_official_graph': {'all_direct_roots_including_custom_implicit_Init': sorted(external),
        'total_official_source_and_olean_units': len(official),
        'mathlib_only_units': sum(row['identity_root']=='mathlib' for row in official.values()),
        'by_identity_root': dict(sorted(Counter(row['identity_root'] for row in official.values()).items())),
        'total_with228_custom_units_and_audits': len(official)+len(custom)+len(audits),
        'missing_or_unresolved_modules': [], 'all_import_dependencies_resolved_and_reachable': True,
        'implicit_Init_prelude_and_import_all_exposure_accounted_for': True,
        'all_official_source_and_olean_sha256_measured': True,
        'literal_Mathlib_and_Mathlib_Tactic_reachable': False,
        'source_artifact_manifest': str(closure_file), 'source_artifact_manifest_sha256': closure_sha,
        'direct_official_artifact_identities': direct},
    'owned_output_eligibility_inventory': {'file': str(reuse_file), 'sha256': reuse_sha,
        'eligible_original_unaffected_candidate_count': len(eligible_names),
        'eligible_modules': eligible_names, 'all_affected_sources_and_descendants_must_remain_cold': True,
        'outputs_copied_or_marked_reusable': False, 'stage_exists': False},
    'qualifications': ['Static identity/closure does not demonstrate import sufficiency, compilation PASS or endpoint axioms.',
        'No original Lean source, audit, receipt or compiled artifact was changed.',
        'All228 scientific bodies and all audit requests remain identical; only the reviewed three hypothetical header spans differ.',
        'Eligible candidates are a read-only policy proposal. Actual staged identities and explicit root reuse approval remain absent.',
        'Any eventual import-only replay must remain labeled separately from the exact original119/228 replay.'],
}
assert sha_file(RECEIPT)==EXPECTED_RECEIPT and sha_file(PRIOR)==summary['prior_full228_proposal_sha256']
out = BASE / 'dms-full228-complete-official-closure-and-reuse-proposal-20261005.json'
out_sha = save_new(out, summary)
print(json.dumps({'proposal': str(out), 'proposal_sha256': out_sha,
    'total_official_units': len(official), 'mathlib_units': summary['complete_official_graph']['mathlib_only_units'],
    'by_identity_root': summary['complete_official_graph']['by_identity_root'],
    'eligible_owned_unaffected_candidates': len(eligible_names),
    'reuse_inventory_sha256': reuse_sha, 'closure_manifest_sha256': closure_sha,
    'status': summary['status']}, indent=2), flush=True)
