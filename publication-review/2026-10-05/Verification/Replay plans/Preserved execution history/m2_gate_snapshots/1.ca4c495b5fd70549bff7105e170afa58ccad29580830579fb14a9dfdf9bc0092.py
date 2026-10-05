"""Prepare exact prior-own M2 reuse; linking needs a later SHA-bound root approval.

Preparation creates metadata only. The original DMS119 receipt and M2 StarCore
pilot remain immutable. Only 97 previously cold-checked DMS outputs are proposed
as links; StarCore stays its existing independent M2 pilot output. No Lean runs.
Observed link counts are dated, never a historical count-one prerequisite.
"""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import ctypes, hashlib, json, os, re, shutil, subprocess, sys, time
from ctypes import wintypes
from lean_imports import read_imports, stripped

BASE = Path(__file__).resolve().parent
TARGET = BASE / 'builds/htpeo-erdos-m2'
ORIGINAL = BASE / 'builds/htpeo-dms-current'
POLICY = BASE / 'htpeo-m2-original97-hardlink-policy-20261005.json'
SEED_RECEIPT = BASE / 'htpeo-m2-original97-hardlink-seed-completed-20261005.json'
CLOSURE = BASE / 'proposals/htpeo-m2-original97/complete-official-source-artifact-closure.json'
AUDIT = BASE / 'm2-prior-own-source-conditional-reuse-audit-20261005.json'
AUDIT_SHA = 'd92602bf0fc52f0b324c9ce8063b7dbe56b27e489786223adb1cdb140085ded3'
PREPARATION = BASE / 'm2-granular-execution-preparation-20261005.json'
PREPARATION_SHA = 'c2eb16e66fd9f5bacf75ad470cd25846d412ca8780a8a7d24c119d4b366c6ee5'
PLAN = TARGET / 'build-plan.json'
PLAN_SHA = 'd75af96c5e21e79909e7a95646d0bf766609a46dd40bb0fc44e6308a6eb60ef6'
PILOT = BASE / 'htpeo-erdos-m2-m2-granular-fresh-build.json'
PILOT_SHA = 'c658e5eb47ebbff4f5e3c511d78f3db4eed6c357317bc4ef5d221f05719f91bd'
ORIGINAL_RECEIPT = BASE / 'htpeo-dms-current-fresh-build.json'
ORIGINAL_RECEIPT_SHA = 'feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238'
NEW_NAMES = ['Star6Bounded', 'Star6Corollaries', 'Star6Simple']
SELECTED = ['Star6.simple_schoenberger', 'Star6.simple_petersen_connected',
 'Star6.simple_star6_cubic_bridgeless_le14', 'Star6.simple_star6_subcubic_le7']
ARTIFACT_SUFFIXES = ['.olean', '.olean.private', '.olean.server', '.ilean']
MATHLIB = BASE / 'dependencies/4.33.1/mathlib'
RUNTIME = BASE / 'runtimes/lean-4.33.1-windows'

class FILETIME(ctypes.Structure):
    _fields_ = [('low', wintypes.DWORD), ('high', wintypes.DWORD)]
class FILE_INFO(ctypes.Structure):
    _fields_ = [('attributes', wintypes.DWORD), ('creation', FILETIME),
      ('access', FILETIME), ('write', FILETIME), ('volume_serial', wintypes.DWORD),
      ('size_high', wintypes.DWORD), ('size_low', wintypes.DWORD),
      ('link_count', wintypes.DWORD), ('index_high', wintypes.DWORD), ('index_low', wintypes.DWORD)]
kernel = ctypes.WinDLL('kernel32', use_last_error=True)
kernel.CreateFileW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
kernel.CreateFileW.restype = wintypes.HANDLE
kernel.GetFileInformationByHandle.argtypes = [wintypes.HANDLE, ctypes.POINTER(FILE_INFO)]
kernel.GetFileInformationByHandle.restype = wintypes.BOOL
kernel.CloseHandle.argtypes = [wintypes.HANDLE]
kernel.CloseHandle.restype = wintypes.BOOL
kernel.GetVolumePathNameW.argtypes = [wintypes.LPCWSTR, wintypes.LPWSTR, wintypes.DWORD]
kernel.GetVolumePathNameW.restype = wintypes.BOOL
kernel.GetVolumeInformationW.argtypes = [wintypes.LPCWSTR, wintypes.LPWSTR, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD), ctypes.POINTER(wintypes.DWORD), ctypes.POINTER(wintypes.DWORD), wintypes.LPWSTR, wintypes.DWORD]
kernel.GetVolumeInformationW.restype = wintypes.BOOL

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()
def load(path): return json.loads(Path(path).read_bytes())
def now(): return datetime.now(timezone.utc).isoformat()
def save_new(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x', encoding='utf8') as stream: json.dump(value, stream, indent=2); stream.write('\n')
    return digest(path)
def file_identity(path):
    handle = kernel.CreateFileW(str(Path(path).resolve()), 0x80, 7, None, 3, 0, None)
    if handle == ctypes.c_void_p(-1).value: raise ctypes.WinError(ctypes.get_last_error())
    info = FILE_INFO()
    try:
        if not kernel.GetFileInformationByHandle(handle, ctypes.byref(info)): raise ctypes.WinError(ctypes.get_last_error())
        return {'volume_serial': int(info.volume_serial), 'file_index_high': int(info.index_high),
          'file_index_low': int(info.index_low), 'link_count': int(info.link_count),
          'bytes': (int(info.size_high) << 32) | int(info.size_low), 'attributes': int(info.attributes)}
    finally: kernel.CloseHandle(handle)
def inode_key(row): return (row['volume_serial'], row['file_index_high'], row['file_index_low'])
def stable_identity(row): return {k: v for k, v in row.items() if k != 'link_count'}
def volume_identity(path):
    root = ctypes.create_unicode_buffer(32768)
    if not kernel.GetVolumePathNameW(str(Path(path).resolve()), root, len(root)): raise ctypes.WinError(ctypes.get_last_error())
    serial, maximum, flags = wintypes.DWORD(), wintypes.DWORD(), wintypes.DWORD()
    fs = ctypes.create_unicode_buffer(64)
    if not kernel.GetVolumeInformationW(root.value, None, 0, ctypes.byref(serial), ctypes.byref(maximum), ctypes.byref(flags), fs, len(fs)): raise ctypes.WinError(ctypes.get_last_error())
    assert fs.value == 'NTFS' and flags.value & 0x00400000
    return {'volume_root': root.value, 'volume_serial': int(serial.value), 'filesystem': fs.value,
      'filesystem_flags': int(flags.value), 'supports_hard_links': True}
def route_inactive(allow_own_reviewed_M2_runner=False):
    cmd = "Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|python)(\\.exe)?$' } | Select-Object ProcessId,Name,CommandLine | ConvertTo-Json -Compress"
    result = subprocess.run(['powershell', '-NoProfile', '-Command', cmd], capture_output=True, text=True, encoding='utf8', errors='replace', check=True)
    rows = json.loads(result.stdout or '[]'); rows = rows if isinstance(rows, list) else [rows]
    disallowed = []
    for row in rows:
        text = (row.get('CommandLine') or '').replace('\\', '/').lower()
        # During the reviewed runner's own pre/post identity checks, its own
        # Python dispatcher is expected. Every other M2 dispatcher remains
        # disallowed; the original DMS and completed v2 routes stay inactive.
        if allow_own_reviewed_M2_runner and row['ProcessId'] == os.getpid() and 'run_htpeo_m2_linked_granular_plan.py' in text:
            continue
        if (('/builds/htpeo-dms-current/' in text) or
            ('run_source_plan.py' in text and ' htpeo-dms-current ' in text) or
            'dispatch_dms_sole_guarded.py' in text or
            'run_dms_modeq_v2_linked_plan.py' in text or
            ('run_m2_granular_source_plan.py' in text and 'htpeo-erdos-m2' in text) or
            'run_htpeo_m2_linked_granular_plan.py' in text): disallowed.append(row)
    assert not disallowed, ('DMS original/v2 and M2 source routes must be inactive for linking', disallowed)
    return {'checked_utc': now(), 'DMS_original_v2_and_M2_compilers_inactive': True, 'process_snapshot': rows}
def preserve():
    pairs = {AUDIT: AUDIT_SHA, PREPARATION: PREPARATION_SHA, PLAN: PLAN_SHA,
      PILOT: PILOT_SHA, ORIGINAL_RECEIPT: ORIGINAL_RECEIPT_SHA}
    for path, sha in pairs.items(): assert digest(path) == sha, ('Immutable record changed', str(path))
    return [{'file': str(p), 'sha256': h} for p, h in pairs.items()]
def source_and_runtime_check(policy=None):
    preserve(); plan = load(PLAN); prep = load(PREPARATION)
    assert plan['version'] == '4.33.1' and plan['mathlib_pin'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    for entry in plan['modules']: assert digest(entry['file']) == entry['sha256'], entry['module']
    assert digest(RUNTIME/'bin/lean.exe') == prep['compiler_binary_sha256']
    runtime = load(BASE/'lean-4.33.1-installation.json')
    assert runtime['complete'] and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in runtime['compiler_check']['output']
    assert load(BASE/'mathlib-4.33.1-cache-retry.json')['status'] == 'PASS'
    dependencies = load(BASE/'dependencies-4.33.1-verified-git.json')
    for pin in dependencies:
        directory = MATHLIB if pin['name'] == 'mathlib' else MATHLIB/'.lake/packages'/pin['name']
        got = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=directory, capture_output=True, text=True, check=True).stdout.strip()
        assert got == pin['rev'], (pin['name'], got, pin['rev'])
    if policy:
        # Recheck both original and M2 scientific source bytes for the entire
        # 98-module custom closure at actual seed and runner qualification,
        # rather than relying only on the dated preparation comparison.
        current_modules = {entry['module']: entry for entry in plan['modules']}
        bindings = {}
        for reused in policy['modules']:
            for binding in reused['entire_unaffected_custom_dependency_closure']:
                previous = bindings.setdefault(binding['module'], binding)
                assert previous == binding
        assert len(bindings) == 98
        for name, binding in bindings.items():
            original_source = ORIGINAL/Path(name.replace('.', '/')+'.lean')
            assert digest(original_source) == digest(current_modules[name]['file']) == binding['source_sha256']
            for output in binding['own_artifacts']:
                assert digest(output['file']) == output['sha256'] and Path(output['file']).stat().st_size == output['bytes']
        for row in policy['bound_runtime_and_helper_files']: assert digest(row['file']) == row['sha256'], row['file']
        assert digest(CLOSURE) == policy['complete_official_closure_sha256']
        graph = load(CLOSURE); names = {x['module'] for x in graph}
        for row in graph:
            assert all(n in names for n in row['dependency_names'])
            assert digest(row['source']) == row['source_sha256'] and digest(row['official_olean']) == row['official_olean_sha256']
    return plan, prep
def official_closure(direct):
    roots = [(MATHLIB, MATHLIB/'.lake/build/lib/lean', 'mathlib')]
    roots += [(p, p/'.lake/build/lib/lean', p.name) for p in sorted((MATHLIB/'.lake/packages').iterdir()) if p.is_dir()]
    roots += [(RUNTIME/'src/lean', RUNTIME/'lib/lean', 'official_lean_core'),
      (RUNTIME/'src/lean/lake', RUNTIME/'lib/lean', 'official_lake')]
    graph = {}
    def visit(name):
        if name in graph: return
        rel = Path(name.replace('.', '/') + '.lean')
        choices = [(s/rel, o/rel.with_suffix('.olean'), identity) for s, o, identity in roots if (s/rel).is_file()]
        assert choices, ('Unresolved official import', name)
        source, olean, identity = choices[0]; assert olean.is_file(), (name, olean)
        raw = source.read_bytes(); clean = stripped(raw.decode('utf8'))
        explicit = [n for n in read_imports(source) if n != 'all']
        implicit = name != 'Init' and not re.search(r'^\s*prelude\b', clean, re.M)
        deps = list(dict.fromkeys(explicit + (['Init'] if implicit else [])))
        clauses = []; offset = 0
        for line, (original, parsed) in enumerate(zip(raw.splitlines(keepends=True), clean.splitlines(keepends=True)), 1):
            if re.match(r'^\s*(public\s+)?(meta\s+)?import\s', parsed):
                clauses.append({'line': line, 'start_byte': offset, 'end_byte_exclusive': offset+len(original),
                  'exact_clause': original.decode('utf8').rstrip('\r\n')})
            offset += len(original)
        graph[name] = {'module': name, 'identity_root': identity, 'source': str(source),
          'source_sha256': hashlib.sha256(raw).hexdigest(), 'source_bytes': len(raw),
          'official_olean': str(olean), 'official_olean_sha256': digest(olean),
          'official_olean_bytes': olean.stat().st_size, 'explicit_imports': explicit,
          'implicit_Init_included': bool(implicit), 'exact_import_clauses': clauses,
          'dependency_names': deps, 'resolution_candidate_count': len(choices)}
        for dep in deps: visit(dep)
    for name in direct + ['Init']: visit(name)
    assert 'Mathlib' not in graph and 'Mathlib.Tactic' not in graph
    return [graph[name] for name in sorted(graph)]
def prepare():
    assert not POLICY.exists() and not CLOSURE.exists()
    preserved = preserve(); plan, prep = source_and_runtime_check()
    prepared = next(p for p in prep['projects'] if p['id'] == 'htpeo-erdos-m2')
    audit_project = next(p for p in load(AUDIT)['projects'] if p['project'] == 'htpeo-erdos-m2')
    modules = {m['module']: m for m in plan['modules']}
    granular = set(prepared['granular_source_names'])
    names = sorted(s['module'] for s in audit_project['sources'] if s['conditional_prior_other_route_reuse_candidate'] and s['module'] != 'StarCore')
    assert len(names) == 97 and granular == set(names) | {'StarCore'} | set(NEW_NAMES)
    audit_rows = [a for a in prepared['audits'] if not a['deferred_whole_scope']]
    assert len(audit_rows) == 1 and audit_rows[0]['audit'] == 'FreshAuditStar6Simple.lean' and audit_rows[0]['selected_names'] == SELECTED
    for row in prepared['audits']: assert digest(TARGET/row['audit']) == row['source_sha256']
    pilot = load(PILOT); assert pilot['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT'
    pilot_rows = [r for r in pilot['builds'] if r['exit'] == 0 and not r.get('stop_reason')]
    assert len(pilot_rows) == 1 and pilot_rows[0]['module'] == 'StarCore'
    pilot_row = pilot_rows[0]
    pilot_artifacts = []
    for artifact in pilot_row['artifacts']:
        path = Path(artifact['file']); assert digest(path) == artifact['sha256'] and path.stat().st_size == artifact['bytes']
        pilot_artifacts.append(dict(artifact, dated_NTFS_identity=file_identity(path)))
    original = load(ORIGINAL_RECEIPT)
    passed = {r['module']: r for r in original['builds'] if r.get('exit') == 0 and not r.get('stop_reason') and not r.get('is_endpoint_audit')}
    source_volume = volume_identity(ORIGINAL); target_volume = volume_identity(TARGET)
    assert source_volume == target_volume and source_volume['volume_root'].lower() == 'c:\\'
    output_links, reuse = [], []
    for name in names:
        candidate = next(s for s in audit_project['sources'] if s['module'] == name)
        witnesses = [w for w in candidate['witnesses'] if w['prior_project'] == 'htpeo-dms-current' and w['conditional_reuse_candidate']]
        assert len(witnesses) == 1
        witness = witnesses[0]; row = passed[name]; entry = modules[name]
        src = ORIGINAL/Path(name.replace('.', '/')+'.lean'); dst = Path(entry['file'])
        assert digest(src) == digest(dst) == entry['sha256'] == candidate['source_sha256'] == row['source_sha256']
        bindings = witness['full_custom_closure_bindings']
        for binding in bindings:
            dep = binding['module']; assert dep in set(names)|{'StarCore'}
            assert digest(ORIGINAL/Path(dep.replace('.', '/')+'.lean')) == digest(modules[dep]['file']) == binding['source_sha256']
            for artifact in binding['own_artifacts']: assert digest(artifact['file']) == artifact['sha256']
        actual = [src.with_suffix(s) for s in ARTIFACT_SUFFIXES if src.with_suffix(s).is_file()]
        declared = {Path(a['file']).resolve(): a for a in row['artifacts']}; assert set(p.resolve() for p in actual) == set(declared)
        records = []
        for source in actual:
            old = declared[source.resolve()]; suffix = source.name[len(src.stem):]; target = dst.with_suffix(suffix)
            assert not target.exists() and digest(source) == old['sha256'] and source.stat().st_size == old['bytes']
            identity = file_identity(source)
            record = {'module': name, 'original_owned_output': str(source), 'M2_target': str(target),
              'sha256': old['sha256'], 'bytes': old['bytes'], 'artifact_kind': suffix,
              'original_NTFS_identity_at_policy': identity,
              'dated_link_count_is_not_a_future_exact_prerequisite': True,
              'classification': 'PREVIOUS_OWN_DMS_ORIGINAL_ROUTE_COLD_OUTPUT_NOT_NEW_M2_COMPILATION'}
            records.append(record); output_links.append(record)
        reuse.append({'module': name, 'source_sha256': entry['sha256'], 'original_PASS_row': row,
          'original_PASS_row_json_sha256': hashlib.sha256(json.dumps(row, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
          'entire_unaffected_custom_dependency_closure': bindings, 'output_links': records,
          'previous_own_DMS_cold_PASS': True, 'new_M2_compilation': False})
    assert len(output_links) == 97
    actual_target_outputs = {p.resolve() for p in TARGET.rglob('*') if p.is_file() and any(p.name.endswith(s) for s in ARTIFACT_SUFFIXES)}
    assert actual_target_outputs == {Path(a['file']).resolve() for a in pilot_artifacts}
    for name in NEW_NAMES: assert not any(Path(modules[name]['file']).with_suffix(s).exists() for s in ARTIFACT_SUFFIXES)
    direct = sorted({n for name in granular for n in read_imports(modules[name]['file']) if n != 'all' and n not in modules})
    closure = official_closure(direct); closure_sha = save_new(CLOSURE, closure)
    bound = [BASE/'lean-4.33.1-installation.json', BASE/'dependencies-4.33.1-verified-git.json',
      BASE/'mathlib-4.33.1-cache-retry.json', MATHLIB/'lake-manifest.json', RUNTIME/'bin/lean.exe',
      BASE/'matt_resource_guard.py', BASE/'audit_axioms.py', BASE/'lean_imports.py', BASE/'resource_metrics.py']
    policy = {'status': 'PREPARED_EXACT97_CONDITIONAL_REUSE_POLICY_NO_LINK_NO_LEAN', 'prepared_utc': now(),
      'project': 'htpeo-erdos-m2', 'source_plan': str(PLAN), 'source_plan_sha256': PLAN_SHA,
      'original119_receipt': str(ORIGINAL_RECEIPT), 'original119_receipt_sha256': ORIGINAL_RECEIPT_SHA,
      'M2_StarCore_pilot': str(PILOT), 'M2_StarCore_pilot_sha256': PILOT_SHA,
      'M2_StarCore_pilot_actual_row': pilot_row, 'M2_StarCore_pilot_artifacts': pilot_artifacts,
      'immutable_records': preserved, 'original_and_target_NTFS_volume': source_volume,
      'modules': reuse, 'output_links': output_links, 'eligible97_module_names': names,
      'required3_new_cold_module_names': NEW_NAMES, 'granular_source_names': sorted(granular),
      'audit_records': audit_rows, 'selected4_endpoint_names': SELECTED,
      'deferred21_whole_source_names': sorted(s['module'] for s in prepared['sources'] if s['deferred_whole_scope']),
      'deferred_whole_audits': [a for a in prepared['audits'] if a['deferred_whole_scope']],
      'logical_proposed_linked_output_bytes': sum(r['bytes'] for r in output_links),
      'physical_payload_duplication_bytes': 0, 'module_count': 97, 'artifact_count': 97,
      'complete_official_closure': str(CLOSURE), 'complete_official_closure_sha256': closure_sha,
      'official_direct_imports': direct, 'official_closure_count': len(closure),
      'official_closure_identity_counts': dict(Counter(r['identity_root'] for r in closure)),
      'official_closure_closed_and_reachable': True, 'implicit_Init_included': True,
      'bound_runtime_and_helper_files': [{'file': str(p), 'sha256': digest(p)} for p in bound],
      'original_route_inactive_dated_observation': route_inactive(),
      'source_scope_counts': {'prior_own_DMS_cold_sources_conditionally_reused': 97,
        'independent_existing_M2_StarCore_pilot': 1, 'required_new_cold_M2_sources': 3,
        'granular_sources_total': 101, 'whole_authored_sources_no_attempt': 21,
        'required_scoped_axiom_prints': 4, 'deferred_whole_audit_prints': 33},
      'trust_policy': 'Preserve StarCert native_decide syntax as authored; classify all four actual printed axioms after new audit. Static no-admission analysis is not actual endpoint proof evidence.',
      'LEAN_PATH_policy': 'Only M2 own build destination, existing frozen additional libraries and verified exact official libraries. DMS original and v2 custom output directories forbidden. No additional custom library is used in this granular closure.',
      'seed_disk_floor_bytes': 1_000_000_000,
      'link_safety_policy': 'No overwrite, same C: NTFS volume, stable file ID/volume/source+output SHA. Policy link counts are dated; reobserve before linking, then assert exactly one increment and same file ID. Original DMS route inactive; DMS v2 qualified and inactive before links. No compiler writes or artifact renames for97 links or retained StarCore.',
      'required_separate_seed_approval_status': 'ROOT_APPROVED_HTPEO_M2_EXACT97_LINK_SEED_ONLY_AFTER_DMS_V2_QUALIFICATION_NO_LEAN',
      'execution_qualification': 'Preparation only. No link, alias, copied artifact, Lean compiler or new theorem verdict. Later granular completion remains distinct from full122-source project and every whole-scope result.'}
    sha = save_new(POLICY, policy)
    print(json.dumps({'policy': str(POLICY), 'policy_sha256': sha, 'proposed97links': 97,
      'existing_independent_M2_pilot': 1, 'required_new_sources': 3, 'official_closure': len(closure),
      'official_closure_sha256': closure_sha, 'links_created': 0, 'Lean_invocations': 0}), flush=True)
def seed(approval_path, approval_sha):
    approval_path = Path(approval_path).resolve(); assert approval_path.is_relative_to(BASE.resolve()) and digest(approval_path) == approval_sha
    approved = load(approval_path); policy = load(POLICY)
    assert approved['status'] == policy['required_separate_seed_approval_status']
    assert approved['reviewed_policy_sha256'] == digest(POLICY) and approved['reviewed_seed_helper_sha256'] == digest(__file__)
    assert approved['approved97_module_names'] == policy['eligible97_module_names']
    assert approved['DMS_v2_qualification_complete_and_link_count_lock_released'] is True
    qualification = Path(approved['DMS_v2_qualification_receipt']).resolve()
    assert qualification.is_relative_to(BASE.resolve()) and digest(qualification) == approved['DMS_v2_qualification_receipt_sha256']
    assert not SEED_RECEIPT.exists()
    source_and_runtime_check(policy); inactive = route_inactive()
    assert volume_identity(ORIGINAL) == volume_identity(TARGET) == policy['original_and_target_NTFS_volume']
    result = {'status': 'EXACT97_LINK_SEED_RUNNING_NO_LEAN', 'started_utc': now(),
      'approval_receipt': str(approval_path), 'approval_receipt_sha256': approval_sha,
      'policy_sha256': digest(POLICY), 'seed_helper_sha256': digest(__file__),
      'DMS_v2_qualification_receipt': str(qualification), 'DMS_v2_qualification_receipt_sha256': digest(qualification),
      'source_plan_sha256': PLAN_SHA, 'original119_receipt_sha256': ORIGINAL_RECEIPT_SHA,
      'M2_StarCore_pilot_sha256': PILOT_SHA, 'eligible97_module_names': policy['eligible97_module_names'],
      'output_links': [], 'new_Lean_compilations': 0, 'payload_bytes_copied': 0,
      'source_routes_inactive_before': inactive, 'minimum_disk_free_bytes': shutil.disk_usage(BASE).free}
    progress = BASE/'htpeo-m2-original97-hardlink-seed-progress-20261005.json'; assert not progress.exists()
    def checkpoint():
        temp = progress.with_suffix('.json.tmp'); temp.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
        os.replace(temp, progress)
    checkpoint()
    for item in policy['output_links']:
        src, dst = Path(item['original_owned_output']).resolve(), Path(item['M2_target']).resolve()
        assert src.is_relative_to(ORIGINAL.resolve()) and dst.is_relative_to(TARGET.resolve()) and not dst.exists()
        before = file_identity(src)
        assert stable_identity(before) == stable_identity(item['original_NTFS_identity_at_policy']) and digest(src) == item['sha256']
        free = shutil.disk_usage(BASE).free; result['minimum_disk_free_bytes'] = min(result['minimum_disk_free_bytes'], free)
        assert free >= policy['seed_disk_floor_bytes']
        os.link(src, dst)
        after, linked = file_identity(src), file_identity(dst)
        assert inode_key(before) == inode_key(after) == inode_key(linked)
        assert stable_identity(before) == stable_identity(after) == stable_identity(linked)
        assert after['link_count'] == before['link_count']+1 == linked['link_count']
        assert digest(src) == digest(dst) == item['sha256']
        result['output_links'].append(dict(item, original_NTFS_identity_before_link=before,
          original_NTFS_identity_after_link=after, M2_target_NTFS_identity_after_link=linked,
          original_sha256_after_link=digest(src), M2_target_sha256=digest(dst)))
        checkpoint()
    assert len(result['output_links']) == 97
    preserve(); result['source_routes_inactive_after'] = route_inactive()
    result.update(status='EXACT97_PREVIOUS_OWN_DMS_COLD_OUTPUT_LINK_SEED_COMPLETE_NO_NEW_COMPILATION', finished_utc=now())
    sha = save_new(SEED_RECEIPT, result); checkpoint()
    print(json.dumps({'seed_receipt': str(SEED_RECEIPT), 'seed_receipt_sha256': sha, 'new_Lean_compilations': 0, 'links': 97}), flush=True)
def verify_seed(policy_sha, seed_sha):
    assert digest(POLICY) == policy_sha and digest(SEED_RECEIPT) == seed_sha
    policy, result = load(POLICY), load(SEED_RECEIPT)
    assert result['status'] == 'EXACT97_PREVIOUS_OWN_DMS_COLD_OUTPUT_LINK_SEED_COMPLETE_NO_NEW_COMPILATION'
    assert result['policy_sha256'] == policy_sha and result['seed_helper_sha256'] == digest(__file__)
    assert result['eligible97_module_names'] == policy['eligible97_module_names'] and len(result['output_links']) == 97
    assert result['new_Lean_compilations'] == result['payload_bytes_copied'] == 0
    source_and_runtime_check(policy)
    for expected, actual in zip(policy['output_links'], result['output_links']):
        assert all(actual[k] == v for k, v in expected.items())
        src, dst = file_identity(expected['original_owned_output']), file_identity(expected['M2_target'])
        assert inode_key(src) == inode_key(dst) == inode_key(expected['original_NTFS_identity_at_policy'])
        assert stable_identity(src) == stable_identity(dst) == stable_identity(expected['original_NTFS_identity_at_policy'])
        assert src['link_count'] == dst['link_count'] and src['link_count'] >= actual['original_NTFS_identity_after_link']['link_count']
        assert digest(expected['original_owned_output']) == digest(expected['M2_target']) == expected['sha256']
    for artifact in policy['M2_StarCore_pilot_artifacts']:
        assert digest(artifact['file']) == artifact['sha256'] and stable_identity(file_identity(artifact['file'])) == stable_identity(artifact['dated_NTFS_identity'])
    inactive = route_inactive(allow_own_reviewed_M2_runner=True)
    return {'status': 'EXACT97_PRIOR_OWN_LINK_IDENTITIES_AND_SEPARATE_M2_PILOT_VERIFIED',
      'policy_sha256': policy_sha, 'seed_receipt_sha256': seed_sha,
      'reused_previous_own_DMS_cold_source_count': 97, 'independent_existing_M2_pilot_sources': 1,
      'new_M2_compilations_in_seed': 0, 'modules': policy['modules'],
      'source_route_inactivity_check': inactive,
      'required3_new_cold_module_names': policy['required3_new_cold_module_names'],
      'forbidden_custom_LEAN_PATH_roots': [str(ORIGINAL.resolve()), str((BASE/'builds/htpeo-dms-current-import-pruned-modeq-v2').resolve())]}
if __name__ == '__main__':
    if sys.argv[1:] == ['--prepare-policy']: prepare()
    elif len(sys.argv) == 4 and sys.argv[1] == '--seed-root-approved': seed(sys.argv[2], sys.argv[3])
    else: raise SystemExit('Use --prepare-policy or separately SHA-approved --seed-root-approved; no Lean is invoked.')
