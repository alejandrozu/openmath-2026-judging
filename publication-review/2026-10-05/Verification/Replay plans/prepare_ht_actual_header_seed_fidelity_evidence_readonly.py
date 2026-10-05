"""PREPARED: read-only actual header-seed source/role/runtime evidence producer.

No compiler, guard, snapshot loader, native DLL loading, lease/hold/receipt edit.
Only a fresh own metadata directory is written after exact root approval. The
output is evidence for root review, never a load authorization or clean observer.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re, subprocess, sys

BASE = Path(__file__).resolve().parent
SEED_HELPER = BASE / 'run_ht_ramsey_official_header_r141_seed_only_prepared.py'
SEED_HELPER_SHA = 'c7cb7c743b497c4e80f553631ef625f587bc0e15b071feb891d75557664c344c'
ROOT = BASE / 'isolated-header-pilots/root-r141-header-seed-20261005-0913'
SEED_RECEIPT = ROOT / 'actual-seed.json'
SEED_RECEIPT_SHA = 'a466829aff3ae9182471fcd8cb7c00041909b91fca6c077ff05af0da66790aab'
OUTER = BASE / 'root-HT-official-header-seed-93768-actual-outer-controller-exit0-20261005.json'
OUTER_SHA = '803d32ee4e0793d546fd5cbcef64593dc731a84664b363e39dabc9f8e857a44d'
BASELINE = BASE / 'proposals/htpeo-ramsey-current-original-provider-recheck-20261005/complete-official-source-and-all-present-artifact-closure.json'
BASELINE_SHA = 'a6359588ec1fb5dbbae82a248d7b70e52fdfdce0055dfaebd91afb271d020289'
READ_IMPORTS_SHA = '4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa'

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''): h.update(block)
    return h.hexdigest()

def stamp(): return datetime.now(timezone.utc).isoformat()

def binding(path):
    path = Path(path).resolve()
    return {'file': str(path), 'sha256': sha(path), 'bytes': path.stat().st_size}

def loaded_checked(path, digest, name):
    assert sha(path) == digest
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

def write_new(path, value):
    with path.open('x', encoding='utf8', newline='\n') as f: f.write(json.dumps(value, indent=2) + '\n')

def clauses(file, stripped):
    # Byte spans use exact decoded file bytes, not universal-newline read_text.
    # The reviewed pure mask preserves character positions but can mask an LF
    # in a quoted backslash pair; restore only raw LF positions for this optional
    # clause metadata. The literal dependency-graph parser stays unchanged.
    raw_text = file.read_bytes().decode('utf8')
    masked = stripped(raw_text)
    assert len(masked) == len(raw_text), ('Clause-mask character alignment', str(file))
    masked = ''.join('\n' if c == '\n' else masked[i] for i, c in enumerate(raw_text))
    original = raw_text.split('\n'); cleaned = masked.split('\n')
    if original[-1] == '':
        original.pop(); cleaned.pop()  # no terminal empty/fake source line
    assert len(original) == len(cleaned)
    rows = []; byte_offset = 0; LF_count = raw_text.count('\n')
    for index, (fragment, text) in enumerate(zip(original, cleaned)):
        raw_line = fragment + ('\n' if index < LF_count else '')
        match = re.match(r'^\s*(?P<public>public\s+)?(?P<meta>meta\s+)?import\s+(?P<all>all\s+)?(?P<names>.*?)\s*$', text)
        if match:
            rows.append({'line': index + 1, 'byte_start': byte_offset, 'byte_end': byte_offset + len(raw_line.encode('utf8')),
                         'public': bool(match.group('public')), 'meta': bool(match.group('meta')),
                         'import_all': bool(match.group('all')),
                         'modules': [n.replace('«', '').replace('»', '') for n in match.group('names').split()]})
        byte_offset += len(raw_line.encode('utf8'))
    assert byte_offset == len(raw_text.encode('utf8'))
    return rows


def main():
    assert len(sys.argv) == 4 and sys.argv[1] == '--root-approved-readonly-actual-header-fidelity-evidence'
    approval_path = Path(sys.argv[2]).resolve(); approval_sha = sys.argv[3]
    assert approval_path.is_relative_to(BASE) and sha(approval_path) == approval_sha
    approval = json.loads(approval_path.read_bytes())
    assert approval['status'] == 'ROOT_APPROVED_READ_ONLY_ACTUAL_HEADER_SEED_SOURCE_ROLE_RUNTIME_EVIDENCE_PRODUCTION_ONLY'
    assert approval['reviewed_producer_sha256'] == sha(__file__)
    assert approval['no_compiler_guard_snapshot_load_or_source_dispatch'] is True
    assert approval['no_observer_error_waiver_or_load_authorization'] is True
    assert sha(SEED_HELPER) == SEED_HELPER_SHA and sha(SEED_RECEIPT) == SEED_RECEIPT_SHA
    assert sha(OUTER) == OUTER_SHA and sha(BASELINE) == BASELINE_SHA
    assert approval['actual_seed_receipt_sha256'] == SEED_RECEIPT_SHA
    assert approval['actual_outer_tool_exit_record_sha256'] == OUTER_SHA
    assert approval['reviewed_historical_official_provider_source_artifact_baseline_sha256'] == BASELINE_SHA
    seed = loaded_checked(SEED_HELPER, SEED_HELPER_SHA, 'actual_seed_fidelity_reviewed_helpers')
    imports = loaded_checked(BASE / 'lean_imports.py', READ_IMPORTS_SHA, 'actual_seed_fidelity_import_reader')
    actual = json.loads(SEED_RECEIPT.read_bytes()); outer = json.loads(OUTER.read_bytes())
    assert actual['status'] == 'PASS_SOURCE_ONLY_HEADER_SEED_REQUIRES_SEPARATE_LOAD_APPROVAL'
    assert actual['controller_source_sha256'] == SEED_HELPER_SHA
    assert actual['actual_owned_child_exit'] == 0 and actual['own_job_resource_receipt']['state'] == 'PASS'
    assert outer['status'] == 'ROOT_CONFIRMED_ACTUAL_HEADER_SEED_CONTROLLER_TOOL_EXIT_ZERO'
    assert outer['actual_controller_exit_code'] == 0 and outer['actual_seed_receipt_sha256'] == SEED_RECEIPT_SHA
    assert sha(seed.PLAN) == seed.PLAN_SHA and sha(seed.MANIFEST) == seed.MANIFEST_SHA
    assert sha(seed.LEAN) == seed.LEAN_SHA and sha(seed.SOURCE) == seed.SOURCE_SHA
    plan = json.loads(seed.PLAN.read_bytes()); custom = {r['module']: r for r in plan['modules']}
    manifest = json.loads(seed.MANIFEST.read_bytes())
    kernel = next(r for r in manifest['kernel_sources'] if r['module'] == seed.MODULE)
    common35 = set(kernel['entire_custom_prerequisite_closure']); assert len(common35) == 35
    assert not seed.source_outputs(seed.SOURCE)
    original_raw = seed.CANONICAL.read_bytes()
    assert hashlib.sha256(original_raw).hexdigest() == actual['original_canonical_receipt_sha256']
    prior = json.loads(original_raw); passed = {r['module']: r for r in prior['builds'] if r['exit'] == 0 and not r.get('stop_reason')}
    assert common35 <= set(passed)
    baseline = {r['module']: r for r in json.loads(BASELINE.read_bytes())}
    assert len(baseline) == 10498
    roots = [{'name': 'official_lean_core', 'source_root': seed.LEAN.parent.parent / 'src/lean',
              'artifact_root': seed.LEAN.parent.parent / 'lib/lean',
              'pin': '4.33.1;819816b2e0a3bf405af45ae5c7af2491d8f5bee6'}]
    pins_file = BASE / 'dependencies-4.33.1-verified-git.json'
    pins = json.loads(pins_file.read_bytes()); assert len(pins) == 9
    for pin in pins:
        directory = seed.DEPENDENCIES if pin['name'] == 'mathlib' else seed.DEPENDENCIES / '.lake/packages' / pin['name']
        head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=directory, capture_output=True, text=True, check=True).stdout.strip()
        origin = subprocess.run(['git', 'remote', 'get-url', 'origin'], cwd=directory, capture_output=True, text=True, check=True).stdout.strip()
        assert head == pin['rev'] and origin == pin['url']
        roots.append({'name': pin['name'], 'source_root': directory, 'artifact_root': directory / '.lake/build/lib/lean', 'pin': head})
    roots.append({'name': 'original_common35', 'source_root': seed.STAGE, 'artifact_root': seed.STAGE,
                  'pin': 'ORIGINAL_FROZEN_HT_2103_PLAN_' + seed.PLAN_SHA})
    def resolve(name):
        relative = Path(name.replace('.', '/') + '.lean')
        matches = [(root, root['source_root'] / relative) for root in roots if (root['source_root'] / relative).is_file()]
        assert len(matches) == 1, ('Ambiguous or missing source provider', name, matches)
        root, file = matches[0]
        assert file.resolve().is_relative_to(root['source_root'].resolve())
        if root['name'] == 'original_common35': assert name in common35
        else: assert name in baseline, ('Provider absent from independently recorded pinned baseline', name)
        return root, file
    units = {}; pending = ['RamseyCert.Data.Ents', 'Init']
    while pending:
        name = pending.pop()
        if name in units: continue
        root, source = resolve(name); source_sha = sha(source)
        if name in common35:
            assert source_sha == custom[name]['sha256'] == passed[name]['source_sha256']
        else:
            old = baseline[name]
            assert source_sha == old['source_sha256'] and root['name'] == old['identity_root'] and root['pin'] == old['exact_pin']
        literal = list(dict.fromkeys(n for n in imports.read_imports(source) if n != 'all'))
        cleaned = imports.stripped(source.read_text(encoding='utf8'))
        prelude = bool(re.search(r'^\s*prelude\s*$', cleaned, re.M))
        implicit = name != 'Init' and not prelude and 'Init' not in literal
        effective = literal + (['Init'] if implicit else [])
        if name not in common35:
            assert literal == old['literal_source_imports'] and prelude == old['prelude']
            assert effective == old['effective_import_dependencies']
        artifact = root['artifact_root'] / Path(name.replace('.', '/') + '.olean')
        assert artifact.is_file()
        artifact_records = [seed.inventory(artifact.with_suffix(s)) for s in seed.OUTPUT_SUFFIXES if artifact.with_suffix(s).is_file()]
        if name in common35:
            for recorded in passed[name]['artifacts']:
                matched = next(r for r in artifact_records if r['file'] == str(Path(recorded['file']).resolve()))
                assert matched['sha256'] == recorded['sha256'] and matched['bytes'] == recorded['bytes']
        else:
            for recorded in old['official_artifacts']:
                matched = next(r for r in artifact_records if r['file'] == str(Path(recorded['file']).resolve()))
                assert matched['sha256'] == recorded['sha256'] and matched['bytes'] == recorded['bytes']
        units[name] = {'module': name, 'identity_root': root['name'], 'exact_pin': root['pin'],
                       'source_file': str(source.resolve()), 'source_sha256': source_sha,
                       'source_bytes': source.stat().st_size, 'literal_source_imports': literal,
                       'import_clauses': clauses(source, imports.stripped), 'prelude': prelude,
                       'implicit_Init_added': implicit, 'effective_import_dependencies': effective,
                       'artifacts': artifact_records}
        pending.extend(n for n in effective if n not in units)
    assert all(set(r['effective_import_dependencies']) <= set(units) for r in units.values())
    assert common35 == {n for n, r in units.items() if r['identity_root'] == 'original_common35'}
    artifact_to_module = {r['file']: name for name, unit in units.items() for r in unit['artifacts']}
    source_records = [custom[n] for n in sorted(common35)]
    snapshot_path = ROOT / 'header/R141.header'
    parsed, regions = seed.parse_actual_regions(snapshot_path, source_records)
    assert parsed == actual['actual_deps_JSON'] and regions == actual['snapshot_dependency_regions']
    seed.check_inventory([actual['header_snapshot'], actual['header_snapshot_deps']])
    assert seed.csha(regions) == actual['actual_region_inventory_canonical_sha256']
    unresolved_roles = [r for r in regions if r['file'] not in artifact_to_module]
    actual_modules = {artifact_to_module[r['file']] for r in regions if r['file'] in artifact_to_module}
    source_closure_only = sorted(set(units) - actual_modules)
    memberships = [{'deps_item_index': r['deps_item_index'], 'role': r['role'], 'file': r['file'],
                    'source_module': artifact_to_module.get(r['file']), 'sha256': r['sha256']}
                   for r in regions]
    grouped = {}
    for row in memberships:
        if row['source_module'] is not None: grouped.setdefault(row['deps_item_index'], set()).add(row['source_module'])
    assert all(len(names) == 1 for names in grouped.values())
    assert len(grouped) == len(parsed) or unresolved_roles
    observation = actual['loaded_image_observation']
    seed.check_inventory(actual['conservative_native_library_inventory'])
    seed.check_inventory(observation['observed_loaded_images'])
    assert observation['observed_loaded_images'] and any(r['file'] == str(seed.LEAN) and r['sha256'] == seed.LEAN_SHA for r in observation['observed_loaded_images'])
    assert not observation['postexit_image_hash_errors'] and not observation.get('foreign_Lean_observations')
    candidates_now = seed.native_library_candidates(actual['dependency_root_order'])
    assert candidates_now == actual['conservative_native_library_inventory']
    union = {r['file']: r for r in candidates_now}
    for image in observation['observed_loaded_images']:
        if image['file'] in union: assert image == union[image['file']]
        union[image['file']] = image
    library_records = [union[p] for p in sorted(union)]
    start = datetime.fromisoformat(actual['own_job_resource_receipt']['started_utc'])
    errors = [{**r, 'seconds_after_guard_started': (datetime.fromisoformat(r['checked_utc']) - start).total_seconds()}
              for r in observation['toolhelp_errors']]
    seed.check_inventory(actual['isolated_output_artifacts'])
    assert seed.CANONICAL.read_bytes() == original_raw and sha(SEED_RECEIPT) == SEED_RECEIPT_SHA and sha(OUTER) == OUTER_SHA
    assert sha(BASELINE) == BASELINE_SHA and sha(seed.PLAN) == seed.PLAN_SHA and sha(seed.SOURCE) == seed.SOURCE_SHA
    assert not seed.source_outputs(seed.SOURCE)
    output = Path(approval['fresh_evidence_directory']).resolve()
    assert output.parent == ROOT and not output.exists()
    output.mkdir()
    units_file = output / 'complete-source-artifact-closure.json'
    membership_file = output / 'actual-deps-role-source-membership.json'
    library_file = output / 'positive-and-conservative-library-identities.json'
    write_new(units_file, [units[n] for n in sorted(units)])
    write_new(membership_file, memberships); write_new(library_file, library_records)
    record = {
        'status': 'READ_ONLY_ACTUAL_SOURCE_ROLE_RUNTIME_EVIDENCE_FOR_ROOT_REVIEW_NOT_A_LOAD_QUALIFICATION',
        'finished_utc': stamp(), 'producer_sha256': sha(__file__), 'root_approval': binding(approval_path),
        'actual_seed_receipt': binding(SEED_RECEIPT), 'actual_outer_exit_record': binding(OUTER),
        'historical_pinned_official_provider_baseline': binding(BASELINE),
        'complete_source_artifact_closure': binding(units_file), 'actual_deps_role_source_membership': binding(membership_file),
        'positive_and_conservative_library_identity_union': binding(library_file),
        'header_source_roots': ['RamseyCert.Data.Ents', 'Init'], 'derived_source_modules': len(units),
        'implicit_Init_and_public_meta_import_clauses_preserved': True,
        'all_source_graph_edges_closed': True, 'all_derived_sources_and_present_artifact_types_rehashed': True,
        'actual_region_items': len(parsed), 'actual_region_roles': len(regions),
        'actual_region_logical_bytes': sum(r['bytes'] for r in regions),
        'actual_region_inventory_canonical_sha256': seed.csha(regions),
        'source_closure_modules_without_snapshot_role': source_closure_only,
        'unresolved_actual_region_role_records': unresolved_roles,
        'source_and_snapshot_module_sets_match_exactly': not source_closure_only and not unresolved_roles,
        'snapshot_sha256': actual['header_snapshot']['sha256'], 'deps_sha256': actual['header_snapshot_deps']['sha256'],
        'observer_successful_samples': observation['successful_toolhelp_snapshots'],
        'positive_images': len(observation['observed_loaded_images']), 'conservative_candidates': len(candidates_now),
        'actual_seed_image_observation_canonical_sha256': seed.csha(observation),
        'observer_errors_preserved_with_actual_relative_times': errors,
        'observer_errors_relabelled_clean': False,
        'observer_is_sampled_not_complete_loader_trace': True,
        'no_unloading_or_startup_cause_inferred_from_timing': True,
        'no_static_PE_or_dynamic_library_completeness_inferred_by_this_producer': True,
        'independent_static_and_positive_relevant_library_assessment_still_required': True,
        'source_command_success_does_not_by_itself_prove_snapshot_load_fidelity': True,
        'original_receipt_source_output_and_seed_files_unchanged': True,
        'no_compiler_guard_snapshot_deserialization_or_dynamic_DLL_load': True,
        'no_lease_hold_or_original_artifact_mutation': True,
        'no_load_authorization_no_project_audit_or_priority_upgrade': True,
    }
    write_new(output / 'actual-readonly-evidence-summary.json', record)
    # No stdout self-relaunch; root must wait for the actual producer exit.
    return 0

if __name__ == '__main__': sys.exit(main())
