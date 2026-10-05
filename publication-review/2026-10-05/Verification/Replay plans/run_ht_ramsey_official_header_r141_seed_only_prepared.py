"""PREPARED ONLY: one separately approved official R141 header-seed source invocation.

Ordinary pinned CLI subprocesses only. Never writes a canonical project receipt,
authored source, original output, helper, lease or hold. No execv or detached run.
This script cannot load a snapshot, audit endpoints, or continue another source.
"""
from pathlib import Path
from datetime import datetime, timezone
import ctypes, hashlib, importlib.util, json, msvcrt, os, re, shutil, sys, threading, time

BASE = Path(__file__).resolve().parent
STAGE = BASE / 'builds/htpeo-ramsey-current'
PLAN = STAGE / 'build-plan.json'
PLAN_SHA = '94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
CANONICAL = BASE / 'htpeo-ramsey-current-fresh-build.json'
MANIFEST = BASE / 'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
MANIFEST_SHA = '2c5963c0b5c5094b77206b80d9e02866a504d56991459a2f0ec3bacef147da15'
LEAN = BASE / 'runtimes/lean-4.33.1-windows/bin/lean.exe'
LEAN_SHA = 'af49bacfabaa1fea71332ca0feae0fa1a60912219d5902291adc79f905bffb8d'
SOURCE = STAGE / 'RamseyCert/Chunk/R141.lean'
SOURCE_SHA = 'd38f94725cbbe0294637f92e6b747ae1da6274de67f5af29b29317f901e1321e'
MODULE = 'RamseyCert.Chunk.R141'
READER = BASE / 'run_ht_ramsey_kernel_j2_continuation_prepared.py'
READER_SHA = 'e551e318748425f8672e73e670aaddda6533af58facefc0ebbef229bf42c6a23'
HELPERS = {
    'matt_resource_guard.py': 'ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71',
    'native_resource_guard.py': '0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4',
    'resource_metrics.py': '1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed',
    'lean_imports.py': '4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa',
    'receipt_io.py': '2e189122fe360f1925dda2e0409c321b775fe7eb6edf17c3f13ef067d1776362',
}
DEPENDENCIES = BASE / 'dependencies/4.33.1/mathlib'
OUTPUT_SUFFIXES = ['.olean', '.olean.server', '.olean.private', '.ilean', '.ir.sig', '.ir']
ROLE_SUFFIXES = {'olean': '.olean', 'oleanServer': '.olean.server',
                'oleanPrivate': '.olean.private', 'irSig': '.ir.sig', 'ir': '.ir'}
NAMES = ['RamseyCert.nbOKR_141', 'RamseyCert.mkOKR_141', 'RamseyCert.tR_141']
PHASES = {'--root-approved-r141-header-seed': ('seed', 'ROOT_APPROVED_SOLO_R141_OFFICIAL_HEADER_SAVE_SOURCE_ONLY')}

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''): h.update(block)
    return h.hexdigest()

def stamp(): return datetime.now(timezone.utc).isoformat()
def csha(value): return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def bound_file(value):
    path = Path(value['file']).resolve()
    assert path.is_relative_to(BASE) and path.is_file() and sha(path) == value['sha256']
    return path

def save_atomic(path, value):
    temporary = path.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n', encoding='utf8', newline='\n')
    for attempt in range(60):
        try: os.replace(temporary, path); return
        except PermissionError:
            if attempt == 59: raise
            time.sleep(.1)

def inventory(path):
    path = Path(path).resolve(); stat = path.stat()
    return {'file': str(path), 'sha256': sha(path), 'bytes': stat.st_size,
            'mtime_ns': stat.st_mtime_ns, 'native_stat_file_id': stat.st_ino}

def check_inventory(records):
    for record in records:
        actual = inventory(record['file'])
        for key in ['sha256', 'bytes', 'mtime_ns', 'native_stat_file_id']:
            assert actual[key] == record[key], (record['file'], key)

def import_checked(path, digest, name):
    assert sha(path) == digest
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

def source_outputs(source):
    return [source.with_suffix(s) for s in OUTPUT_SUFFIXES if source.with_suffix(s).exists()]

def output_inventory(library):
    records = []
    for path in sorted(library.rglob('*')):
        if not path.is_file(): continue
        assert path.name.startswith('R141.'), 'Unexpected file in isolated source output library'
        assert any(str(path).endswith(s) for s in OUTPUT_SUFFIXES), 'Unreviewed output role'
        row = inventory(path); row['relative_file'] = str(path.relative_to(library)); records.append(row)
    return records

def exact_hold_bindings(approval):
    # Preserve every observed hold-* file, including dated release markers.
    # This byte-binding is not an assertion that each marker is an active hold.
    records = approval['preserved_hold_and_release_marker_bindings']
    required = {Path(r['file']).resolve(): r for r in records}
    assert required, 'Explicit observed hold/release-marker bindings are required'
    actual = {p.resolve() for p in BASE.glob('hold-*') if p.is_file()}
    assert actual == set(required), 'Observed hold/release-marker file set changed since root approval'
    for path, record in required.items():
        assert path.is_relative_to(BASE) and sha(path) == record['sha256']

def process_gate(common, approval):
    registry = common.processes()
    assert all(int(pid) not in registry for pid in approval['exited_other_source_dispatcher_pids'])
    details = common.detailed_process_registry()
    violations = []
    leans = [pid for pid, row in registry.items() if row.get('exe', '').lower() == 'lean.exe']
    if leans: violations.append('A_LEAN_PROCESS_IS_ALREADY_ACTIVE')
    for pid, row in registry.items():
        if row.get('exe', '').lower() in {'lake.exe', 'leanc.exe', 'clang.exe', 'clang-cl.exe', 'gcc.exe', 'cc1.exe', 'leantar.exe'}:
            violations.append('ANOTHER_COMPILER_OR_CACHE_EXTRACTOR_IS_ACTIVE:' + str(pid))
    for pid, row in details.items():
        if pid == os.getpid() or row['name'].lower() != 'python.exe': continue
        command = row['command'] or ''
        if re.search(r'\brun_(?:ht_ramsey|htpeo_ramsey|a000|dms|original_e65|source_plan)', command, re.I):
            violations.append('ANOTHER_TASK_SOURCE_DISPATCHER_IS_ACTIVE:' + str(pid))
    observation = {'checked_utc': stamp(), 'global_Lean_pids': leans, 'violations': violations,
                   'solo_pilot_no_companion': True, 'maximum_total_global_Lean_importers': 2,
                   'no_foreign_process_termination': True}
    assert not violations, observation
    exact_hold_bindings(approval)
    return observation

def make_env():
    paths = [str(STAGE), str(DEPENDENCIES / '.lake/build/lib/lean')]
    paths += [str(p / '.lake/build/lib/lean') for p in (DEPENDENCIES / '.lake/packages').iterdir() if p.is_dir()]
    env = dict(os.environ); env['LEAN_PATH'] = ';'.join(paths)
    env['PATH'] = str(LEAN.parent) + ';' + env['PATH']; env['LEAN_NUM_THREADS'] = '2'
    return env, paths

def native_library_candidates(paths):
    # Conservative executable/DLL inventory supplements sampled loaded-image metadata.
    # It is not a claim that every candidate is actually loaded.
    roots = [LEAN.parent.parent] + [Path(p) for p in paths[1:]]
    files = set()
    for root in roots:
        if root.exists():
            files.update(p.resolve() for p in root.rglob('*') if p.is_file() and p.suffix.lower() in {'.dll', '.exe'})
    return [inventory(p) for p in sorted(files)]

def loaded_image_observer(done, common, image_module, results):
    seen = {}; successful = 0; errors = []
    while not done.is_set():
        registry = common.processes(); owned = common.own_tree(os.getpid(), registry)
        leans = {pid for pid, row in registry.items() if row.get('exe', '').lower() == 'lean.exe'}
        foreign = leans - set(owned)
        if foreign: results.setdefault('foreign_Lean_observations', []).append({'checked_utc': stamp(), 'pids': sorted(foreign)})
        for pid in leans & set(owned):
            try:
                rows = image_module.loaded_images(pid); successful += 1
                for row in rows: seen[str(Path(row['path']).resolve())] = row
            except Exception as error:
                errors.append({'checked_utc': stamp(), 'pid': pid, 'error': str(error)})
        done.wait(.1)
    results.update(successful_toolhelp_snapshots=successful, observed_loaded_image_paths=sorted(seen),
                   toolhelp_errors=errors, observation_scope='Sampled own Lean images only; not a continuous complete loader trace')
    records = []; hash_errors = []
    for path in sorted(seen):
        try: records.append(inventory(path))
        except Exception as error: hash_errors.append({'file': path, 'error': str(error)})
    results.update(observed_loaded_images=records, postexit_image_hash_errors=hash_errors,
                   all_successfully_observed_image_files_hashed=not hash_errors)

def parse_actual_regions(snapshot_path, own_sources):
    deps = Path(str(snapshot_path) + '.deps')
    parsed = json.loads(deps.read_bytes()); assert isinstance(parsed, list) and parsed
    records = []; seen = set()
    allowed_own = {str(Path(r['file']).resolve().with_suffix(s)): r['module'] for r in own_sources for s in OUTPUT_SUFFIXES}
    for index, item in enumerate(parsed):
        assert isinstance(item, dict) and set(item) <= set(ROLE_SUFFIXES) and item.get('olean')
        assert not item.get('oleanPrivate') or item.get('oleanServer'), 'Orphan private .olean role'
        assert not item.get('ir') or item.get('irSig'), 'Orphan .ir role'
        for role in ROLE_SUFFIXES:
            if role not in item: continue
            path = Path(item[role]); assert path.is_absolute(), 'Relative region path requires separate fidelity review'
            path = path.resolve(); assert path.is_file() and str(path).endswith(ROLE_SUFFIXES[role])
            assert path not in seen; seen.add(path)
            if str(path) in allowed_own: ownership = 'ORIGINAL_IMMUTABLE_COMMON35_OWN_PROVIDER'
            elif path.is_relative_to(LEAN.parent.parent): ownership = 'EXACT_PINNED_LEAN_RUNTIME_PROVIDER'
            elif path.is_relative_to(DEPENDENCIES): ownership = 'EXACT_PINNED_MATHLIB_OR_PACKAGE_PROVIDER'
            else: raise AssertionError('Unexpected serialized dependency region owner: ' + str(path))
            record = inventory(path); record.update(deps_item_index=index, role=role, ownership=ownership)
            if str(path) in allowed_own: record['own_module'] = allowed_own[str(path)]
            records.append(record)
    return parsed, records

def runtime_and_sources(approval, common):
    assert sha(PLAN) == PLAN_SHA and sha(MANIFEST) == MANIFEST_SHA and sha(LEAN) == LEAN_SHA
    assert approval['reviewed_original2103_plan_sha256'] == PLAN_SHA
    assert approval['reviewed_kernel_source_manifest_sha256'] == MANIFEST_SHA
    assert approval['exact_source_sha256'] == SOURCE_SHA == sha(SOURCE)
    assert approval['reviewed_runtime_executable_sha256'] == LEAN_SHA
    for filename, digest in HELPERS.items(): assert sha(BASE / filename) == digest
    assert sha(READER) == READER_SHA
    raw = common.read_bytes_shared(CANONICAL)
    assert hashlib.sha256(raw).hexdigest() == approval['actual_quiescent_HT_receipt_sha256']
    prior = json.loads(raw)
    assert prior['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT' and prior.get('finished_utc')
    assert not prior.get('current_module') and not prior.get('current_modules') and not prior.get('failed_invocations')
    plan = json.loads(PLAN.read_bytes()); manifest = json.loads(MANIFEST.read_bytes())
    assert plan['version'] == '4.33.1' and plan['mathlib_pin'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    assert not plan.get('lean_options') and not plan.get('additional_dependency_libs')
    assert prior['modules'] == plan['modules']
    passed = {r['module']: r for r in prior['builds'] if r['exit'] == 0 and not r.get('stop_reason')}
    assert len(passed) == len(prior['builds']) and not any(r['is_endpoint_audit'] for r in prior['builds'])
    entries, chunks = common.sources_ready(plan, passed, manifest)
    assert MODULE in chunks and MODULE not in passed and not source_outputs(SOURCE)
    kernel = next(r for r in manifest['kernel_sources'] if r['module'] == MODULE)
    assert kernel['source_sha256'] == SOURCE_SHA and len(kernel['entire_custom_prerequisite_closure']) == 35
    own_sources = [entries[n] for n in kernel['entire_custom_prerequisite_closure']]
    assert all(n in passed for n in kernel['entire_custom_prerequisite_closure'])
    for name, row in passed.items():
        if name not in chunks: continue
        relative = Path(entries[name]['file']).relative_to(STAGE)
        assert row['command'] == [str(LEAN), row['command'][1], '-DmaxHeartbeats=0', '-DmaxRecDepth=100000',
                                  '-o', str(relative.with_suffix('.olean')), str(relative)]
        assert row['command'][1] in {'-j1', '-j2'}
    expected_metadata = {'reviewed_official_cache_receipt': BASE/'mathlib-4.33.1-cache-retry.json',
      'reviewed_official_lake_manifest': DEPENDENCIES/'lake-manifest.json',
      'reviewed_exact_nine_dependency_git_record': BASE/'dependencies-4.33.1-verified-git.json'}
    for field,expected_path in expected_metadata.items():
        assert bound_file(approval[field]) == expected_path.resolve()
    cache = json.loads(bound_file(approval['reviewed_official_cache_receipt']).read_bytes())
    assert cache['status'] == 'PASS'
    pins = json.loads(bound_file(approval['reviewed_exact_nine_dependency_git_record']).read_bytes())
    assert len(pins) == 9
    for pin in pins:
        directory = DEPENDENCIES if pin['name'] == 'mathlib' else DEPENDENCIES / '.lake/packages' / pin['name']
        result = common.subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=directory, capture_output=True, text=True, check=True)
        origin = common.subprocess.run(['git', 'remote', 'get-url', 'origin'], cwd=directory, capture_output=True, text=True, check=True)
        assert result.stdout.strip() == pin['rev'] and origin.stdout.strip() == pin['url']
    return raw, plan, manifest, entries, passed, own_sources

def prepare_phase(approval_path, approval_sha, phase):
    assert approval_path.is_relative_to(BASE) and sha(approval_path) == approval_sha
    approval = json.loads(approval_path.read_bytes())
    assert approval['status'] == dict((p, s) for p, s in PHASES.values())[phase]
    assert approval['reviewed_controller_sha256'] == sha(__file__)
    assert approval['maximum_total_global_Lean_importers'] == 2 and approval['maximum_own_parallel_Lean_jobs'] == 1
    assert approval['no_other_source_compiler_or_dispatcher_admitted'] is True
    assert approval['source_options_proofs_original_outputs_and_canonical_receipts_unchanged'] is True
    assert approval['phase'] == phase and approval['exact_source_module'] == MODULE
    assert re.fullmatch(r'[a-z0-9][a-z0-9-]{0,63}', approval['pilot_id'])
    exit_record = bound_file(approval['actual_other_dispatcher_exit_record'])
    assert approval['actual_other_dispatcher_exit_confirmed_not_inferred_from_WAITING_label'] is True
    assert approval['direct_guarded_subprocess_only_no_execv_or_detached_stdout'] is True
    assert phase == 'seed'
    assert approval['endpoint_audit_invocations_this_phase'] == 0
    assert approval['new_original_source_invocations_this_phase'] == 1
    assert approval['no_snapshot_load_or_cross_file_source_or_audit_authorized'] is True
    assert approval['no_remaining_kernel_continuation_authorized'] is True
    common = import_checked(READER, READER_SHA, 'ht_header_reviewed_common')
    observer_path = BASE / 'luke_native_image_observer.py'
    assert approval['reviewed_loaded_image_observer_sha256'] == 'd25a05c7b3e15d349c94416f675af79d5e5ca2db9dd050f1ff9387eb4ea613d6'
    image_module = import_checked(observer_path, approval['reviewed_loaded_image_observer_sha256'], 'ht_header_readonly_images')
    root = BASE / 'isolated-header-pilots' / approval['pilot_id']
    receipt = root / ('actual-' + phase + '.json')
    assert not receipt.exists() and not receipt.with_suffix('.json.tmp').exists(), 'A phase may not overwrite an earlier receipt or failed attempt'
    return approval, common, image_module, root, receipt

def execute_one(common, observer, approval, command, env, prefix, receipt, report):
    assert not Path(str(prefix) + '.stdout.txt').exists() and not Path(str(prefix) + '.stderr.txt').exists()
    report['actual_pre_dispatch_process_gate'] = process_gate(common, approval)
    done = threading.Event(); images = {}
    thread = threading.Thread(target=loaded_image_observer, args=(done, common, observer, images), daemon=False)
    report.update(status='RUNNING_OWN_DIRECT_GUARDED_CLI', command=command, literal_LEAN_NUM_THREADS='2',
                  literal_LEAN_PATH=env['LEAN_PATH'], cwd=str(STAGE), exact_source_sha256=sha(SOURCE),
                  selected_axiom_prints='NOT_ATTEMPTED_IN_SOURCE_PHASE', started_utc=stamp())
    save_atomic(receipt, report); thread.start()
    try: guard = common.guarded_tree(command, STAGE, env, prefix, timeout=3600)
    finally: done.set(); thread.join()
    report.update(own_job_resource_receipt=guard, loaded_image_observation=images,
                  actual_owned_child_exit=guard.get('exit'), actual_owned_child_finished_utc=guard.get('finished_utc'),
                  attempted=guard['attempted'], actual_command_state=guard['state'], finished_utc=stamp(),
                  outer_controller_tool_wait_and_exit='MUST_BE_RECORDED_IN_SEPARATE_ACTUAL_ROOT_TOOL_RESULT_NOT_INFERRED_FROM_THIS_LABEL')
    assert sha(SOURCE) == SOURCE_SHA
    return guard





def allocated_bytes(path):
    kernel=ctypes.WinDLL('kernel32',use_last_error=True)
    kernel.GetCompressedFileSizeW.argtypes=[ctypes.c_wchar_p,ctypes.POINTER(ctypes.c_uint32)]
    kernel.GetCompressedFileSizeW.restype=ctypes.c_uint32
    hi=ctypes.c_uint32();ctypes.set_last_error(0)
    low=kernel.GetCompressedFileSizeW(str(Path(path).resolve()),ctypes.byref(hi))
    if low==0xffffffff and ctypes.get_last_error():raise ctypes.WinError(ctypes.get_last_error())
    return (int(hi.value)<<32)|int(low)

def main():
    assert len(sys.argv)==4 and sys.argv[1]=='--root-approved-r141-header-seed'
    approval_path=Path(sys.argv[2]).resolve();approval_sha=sys.argv[3]
    approval,common,observer,root,receipt=prepare_phase(approval_path,approval_sha,'seed')
    lockfile=STAGE/'.fresh-replay.lock';assert lockfile.is_file() and lockfile.stat().st_size==1
    lock=lockfile.open('r+b');lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1)
    report=None
    try:
        assert not CANONICAL.with_suffix('.json.tmp').exists()
        original_raw,plan,manifest,entries,passed,own_sources=runtime_and_sources(approval,common)
        process_gate(common,approval)
        env,paths=make_env()
        assert paths==approval['exact_original_LEAN_PATH_roots_in_order']
        assert len(passed)==approval['actual_completed_HT_source_row_count']
        assert not root.exists(),'The seed workspace must be completely fresh'
        libraries=native_library_candidates(paths)
        root.mkdir(parents=True)
        library=root/'A';library.mkdir()
        target=library/'RamseyCert/Chunk/R141.olean';target.parent.mkdir(parents=True)
        snap=root/'header/R141.header';snap.parent.mkdir()
        assert not snap.exists() and not Path(str(snap)+'.deps').exists()
        command=[str(LEAN),'-j2','-DmaxHeartbeats=0','-DmaxRecDepth=100000',
                 '--incr-header-save='+str(snap),'-o',str(target),str(SOURCE.relative_to(STAGE))]
        report={'phase':'seed','status':'PREPARATION','controller_source_sha256':sha(__file__),
          'root_approval':str(approval_path),'root_approval_sha256':approval_sha,
          'original_plan_sha256':PLAN_SHA,'original_source_module':MODULE,
          'original_canonical_receipt_sha256':hashlib.sha256(original_raw).hexdigest(),
          'canonical_prior_rows_preserved_not_relabelled':True,'no_original_output_writes':True,
          'no_custom_frontend_or_persistent_process':True,'no_execv_or_detached_stdout':True,
          'source_flags':['-j2','-DmaxHeartbeats=0','-DmaxRecDepth=100000'],
          'plan_additional_lean_options':{},'source_body_maxRecDepth_option':1000000,
          'inherited_LEAN_IMPORT_WORKERS':env.get('LEAN_IMPORT_WORKERS'),
          'new_source_invocations_this_phase':0,'new_audit_invocations_this_phase':0,
          'remaining_original_sources_not_authorized':True,'snapshot_load_not_authorized':True,
          'cross_file_R142_not_authorized':True,'conservative_native_library_inventory':libraries,
          'dependency_root_order':paths,'full_region_source_closure_independent_qualification':'NOT_PERFORMED_BY_THIS_SEED_CONTROLLER'}
        guard=execute_one(common,observer,approval,command,env,root/'logs-seed',receipt,report)
        if guard['attempted']:report['new_source_invocations_this_phase']=1
        report['isolated_output_artifacts']=output_inventory(library)
        assert not source_outputs(SOURCE),'Original output location must remain untouched'
        if guard['state']!='PASS' or guard.get('exit')!=0:
            report['status']='NOT_INVOKED_OR_ENVIRONMENT_OR_SOURCE_FAILURE_SEPARATE_FROM_SCIENTIFIC_PRIORITY'
            report['retained_partial_seed_files']=[inventory(p) for p in [snap,Path(str(snap)+'.deps')] if p.exists()]
        else:
            assert target.is_file() and report['isolated_output_artifacts']
            report.update(header_snapshot=inventory(snap),header_snapshot_deps=inventory(Path(str(snap)+'.deps')))
            parsed,regions=parse_actual_regions(snap,own_sources)
            report.update(header_snapshot=inventory(snap),header_snapshot_deps=inventory(Path(str(snap)+'.deps')),
              actual_deps_JSON=parsed,snapshot_dependency_regions=regions,
              actual_region_inventory_canonical_sha256=csha(regions),
              source_closure_qualification='NOT_YET_INDEPENDENTLY_REVIEWED_REQUIRES_NEW_ROOT_LOAD_APPROVAL',
              snapshot_storage={'snapshot_logical_bytes':snap.stat().st_size,'snapshot_allocated_bytes':allocated_bytes(snap),
                'deps_logical_bytes':Path(str(snap)+'.deps').stat().st_size,
                'deps_allocated_bytes':allocated_bytes(Path(str(snap)+'.deps')),
                'snapshot_size_or_speedup_not_promised_before_actual_seed':True},
              status='PASS_SOURCE_ONLY_HEADER_SEED_REQUIRES_SEPARATE_LOAD_APPROVAL')
        images=report['loaded_image_observation']
        report['image_observer_fidelity_requires_root_review_before_any_load']=True
        report['image_observer_errors_or_missing_positive_sample']=bool(images.get('toolhelp_errors') or
            images.get('postexit_image_hash_errors') or not images.get('successful_toolhelp_snapshots'))
        if images.get('foreign_Lean_observations'):
            report['status']='SOURCE_RESULT_PRESERVED_BUT_FOREIGN_LEASE_CONFLICT_REQUIRES_ROOT_REVIEW'
        assert common.read_bytes_shared(CANONICAL)==original_raw and sha(PLAN)==PLAN_SHA
        common.sources_ready(plan,passed,manifest)
        assert sha(SOURCE)==SOURCE_SHA and not source_outputs(SOURCE)
        exact_hold_bindings(approval);check_inventory(libraries)
        report.update(finished_utc=stamp(),canonical_receipt_byte_identical_after=True,
          source_and_all_prior_owned_artifacts_rehashed_after=True,original_source_outputs_still_absent=True,
          actual_selected_axiom_qualification='NOT_PERFORMED_NO_MAIN24_COMPLETION_CLAIM',
          outer_actual_tool_exit_receipt_required=True,
          stopped_after_exact_one_source_no_load_cross_file_audit_or_continuation=True)
        save_atomic(receipt,report)
        return 0 if report['status']=='PASS_SOURCE_ONLY_HEADER_SEED_REQUIRES_SEPARATE_LOAD_APPROVAL' else 2
    except Exception as error:
        if report is not None:
            report.update(status='OWN_OPERATIONAL_OR_FIDELITY_CHECKPOINT_REQUIRES_ROOT_REVIEW',
              error=repr(error),finished_utc=stamp(),no_scientific_failure_inference=True)
            save_atomic(receipt,report)
        raise
    finally:
        lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_UNLCK,1);lock.close()

if __name__=='__main__':
    # No stdout self-relaunch or execv. The direct calling tool must wait for the
    # actual outer exit; a saved WAITING or finished label is never its substitute.
    sys.exit(main())
