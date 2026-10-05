"""Exactly two authorized checks, then an unconditional resource-review boundary.

This source-identical operational route does not alter the entrants' Lake policy.
It does not dispatch any of the remaining sources or stop the original replay.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, shutil, subprocess, time
from receipt_io import read_bytes_shared
from audit_axioms import parse
from luke_native_source_guard import guarded, counters, GIB

BASE = Path(__file__).resolve().parent
DEST = BASE/'builds/luke-k4-ramsey-current-native'
REPORT = BASE/'luke-k4-ramsey-current-native-fresh-build.json'
COUNT = 'K4Ramsey.Constructions.Final3840.Certificate'


def stamp(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def atomic(path, raw):
    temp = path.with_suffix(path.suffix+'.tmp')
    with temp.open('wb') as f: f.write(raw); f.flush(); os.fsync(f.fileno())
    for attempt in range(60):
        try: os.replace(temp, path); return
        except PermissionError:
            if attempt == 59: raise
            time.sleep(.1)


def save(record): atomic(REPORT, json.dumps(record, ensure_ascii=False, indent=2).encode('utf8'))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--authorization', required=True)
    parser.add_argument('--dms-boundary-hold-confirmed', action='store_true')
    args = parser.parse_args()
    assert args.authorization == 'ROOT_NATIVE_COUNT_AND_RAW_AUDIT_ONLY_AUTHORIZED'
    assert args.dms_boundary_hold_confirmed, 'Root requires the actual DMS completed-module boundary hold'
    assert not REPORT.exists(), 'Preserve each attempted source route; reviewed resume requires a separate runner'
    frozen = json.loads((DEST/'build-plan.json').read_bytes())
    schema = json.loads((BASE/'luke_native_qualified_replay_plan.json').read_bytes())
    for key in ['id', 'commit', 'version', 'mathlib_pin']: assert frozen[key] == schema[key]
    assert frozen['id'] == 'luke-k4-ramsey-current' and len(frozen['modules']) == 51
    modules = {m['module']: m for m in frozen['modules']}
    for m in modules.values():
        assert sha(m['file']) == m['sha256'] == sha(m['frozen_source']), 'Frozen source identity changed'
    links_path = BASE/'luke-native-isolated-links.json'; links_raw = links_path.read_bytes(); links = json.loads(links_raw)
    assert links['status'] == 'ACTUAL_LINKS_AND_PE_PASS_INITIALIZATION_UNTESTED'
    assert len(links['dlls']) == 2 and all(links['two_DLL_DAG_import_checks'].values())
    assert links['actual_Count_initializer_is_exported_executable']
    assert all(c['actual_data_slot_is_nonexecuting_writable'] for c in links['actual_Count_closed_cache_PE_data_slots'])
    native_preparation = json.loads((BASE/'luke-native-isolated-preparation.json').read_bytes())
    assert native_preparation['compiler_pin'] == '5045d0056413266e57c625dcd7c365b10e377c52'
    assert hashlib.sha256((BASE/'luke-native-isolated-preparation.json').read_bytes()).hexdigest() == links['preparation_receipt_sha256']
    for tool, expected_hash in native_preparation['tool_hashes'].items():
        assert sha(tool) == expected_hash, 'Pinned tool binary changed after native object preparation'
    for d in links['dlls']:
        assert sha(d['file']) == d['sha256'] and sha(d['import_library']['file']) == d['import_library']['sha256']
        assert not d['missing_actual_COFF_exports'] and d['source_owned_exports_have_no_forwarders']
    prior_path = BASE/'luke-k4-ramsey-current-direct-fresh-build.json'
    prior_raw = read_bytes_shared(prior_path); prior = json.loads(prior_raw)
    for key in ['id', 'commit', 'version', 'mathlib_pin']: assert prior[key] == frozen[key]
    passed = {n for n, s in prior['module_states'].items() if s == 'PASS'}
    assert len(passed) == 33 and COUNT not in passed, 'Review any new original-route completion before duplicating it'
    snapshot = BASE/'native_source_attempts'/('direct33-before-native-pilot-'+stamp()[:19].replace(':','').replace('-','')+'.json')
    snapshot.parent.mkdir(exist_ok=True); assert not snapshot.exists(); atomic(snapshot, prior_raw)
    output = DEST/'.lake/build/lib/lean'; output.mkdir(parents=True, exist_ok=True)
    assert not list(output.rglob('*')), 'The isolated native source output directory must start cold'
    previous_output = Path(prior['source_dir'])/'.lake/build/lib/lean'
    reused = []; builds = []
    for row in prior['builds']:
        name = row.get('module')
        if name not in passed or row.get('exit') != 0: continue
        assert row['source_sha256'] == modules[name]['sha256']
        source_stem = previous_output.joinpath(*name.split('.'))
        artifacts = []
        for source in source_stem.parent.glob(source_stem.name+'.*'):
            if not source.is_file(): continue
            target = output/source.relative_to(previous_output); target.parent.mkdir(parents=True, exist_ok=True)
            assert not target.exists(); raw = source.read_bytes(); digest = hashlib.sha256(raw).hexdigest(); atomic(target, raw)
            assert sha(source) == digest == sha(target)
            artifacts.append({'prior_file': str(source), 'file': str(target), 'bytes': len(raw), 'sha256': digest})
        assert any(a['file'].endswith('.olean') for a in artifacts), 'A prior success requires its actual own .olean'
        builds.append({**row, 'state': 'PASS', 'reused_own_direct_output': True,
            'prior_receipt_snapshot_file': str(snapshot), 'prior_receipt_snapshot_sha256': hashlib.sha256(prior_raw).hexdigest(),
            'own_prior_output_artifacts': artifacts})
        reused.extend(artifacts)
    assert len(builds) == 33
    dependency_preflight = []
    for expected in prior['dependency_preflight']:
        path = Path(frozen['dependency_identity_root'])/'.lake/packages'/expected['name']
        head = subprocess.run(['git', '-C', str(path), 'rev-parse', 'HEAD'], capture_output=True, text=True, encoding='utf8')
        origin = subprocess.run(['git', '-C', str(path), 'remote', 'get-url', 'origin'], capture_output=True, text=True, encoding='utf8')
        assert head.returncode == origin.returncode == 0
        assert head.stdout.strip() == expected['expected_head'] and origin.stdout.strip() == expected['expected_origin']
        dependency_preflight.append({**expected, 'actual_head': head.stdout.strip(), 'actual_origin': origin.stdout.strip(), 'match': True})
    record = {**frozen, 'status': 'RUNNING_NATIVE_COUNT_PILOT', 'started_utc': stamp(),
        'route': schema['route'], 'builds': builds, 'module_states': {n: 'PASS' for n in passed},
        'runner_sha256': sha(__file__), 'guard_sha256': sha(BASE/'luke_native_source_guard.py'),
        'axiom_classifier_sha256': sha(BASE/'audit_axioms.py'), 'native_link_receipt_sha256': hashlib.sha256(links_raw).hexdigest(),
        'source_stage_build_plan_sha256': sha(DEST/'build-plan.json'),
        'dependency_preflight': dependency_preflight, 'pinned_tool_binary_hashes': native_preparation['tool_hashes'],
        'reused_own_direct_source_module_count': 33, 'reused_own_direct_artifact_inventory': reused,
        'prior_direct_attempt_preserved': str(prior_path), 'dms_completed_boundary_hold_confirmed': True,
        'pilot_scope': 'One unchanged Count Certificate source, followed by one organizer print-only raw count audit; pause for root review.',
        'authored_lake_policy': frozen.get('authored_lake_policy'),
        'resource_environment': {'LEAN_NUM_THREADS': '1', 'explicit_Lean_CLI_jobs': 1},
        'native_selection_notice': schema['native_dispatch_evidence'],
        'source_fidelity_notice': schema['source_fidelity'], 'no_original_process_stop_by_this_runner': True}
    save(record)
    runtime = BASE/'runtimes/lean-4.34.1-windows'; lean = runtime/'bin/lean.exe'
    env = dict(os.environ); assert not env.get('LEAN_CC') and not env.get('LEAN_SYSROOT')
    env['PATH'] = str(runtime/'bin')+';'+str(Path(links['dlls'][0]['file']).parent)+';'+env['PATH']
    env['LEAN_PATH'] = ';'.join([str(output), *frozen['dependency_library_paths']]); env['LEAN_NUM_THREADS'] = '1'
    version = subprocess.run([str(lean), '--version'], capture_output=True, text=True, encoding='utf8', env=env)
    assert version.returncode == 0 and ('version '+frozen['version']+',') in version.stdout
    assert version.stdout.strip() == prior['compiler_version_output']
    record['compiler_version_output'] = version.stdout.strip()
    count = modules[COUNT]; target = output.joinpath(*COUNT.split('.')); target.parent.mkdir(parents=True, exist_ok=True)
    command = [str(lean), '-j1', '--load-dynlib='+links['dlls'][0]['file'],
               '--plugin='+links['dlls'][1]['file']+'=initialize_K4Ramsey_Constructions_Final3840_Count',
               '-o', str(target)+'.olean', '-i', str(target)+'.ilean', str(Path(count['file']).relative_to(DEST))]
    record['current_module'] = COUNT; save(record); print('INVOKE_NATIVE_COUNT_PILOT '+COUNT, flush=True)
    row = guarded(command, DEST, env, DEST/'logs/native_count_pilot', native_images=links['dlls'], whole_mathlib=True)
    row.update(module=COUNT, source_sha256=count['sha256'], is_endpoint_audit=False)
    record['builds'].append(row); record['module_states'][COUNT] = row['state']
    if row['state'] != 'PASS':
        record['status'] = row['state']; record['finished_utc'] = stamp(); record.pop('current_module', None); save(record)
        print('NATIVE_COUNT_PILOT_STOP '+row['state'], flush=True); return
    assert sha(count['file']) == count['sha256'] == sha(count['frozen_source'])
    assert Path(str(target)+'.olean').exists()
    record['module_states'][COUNT] = 'PASS'; record['status'] = 'COUNT_SOURCE_PASS_RAW_AUDIT_PENDING'; save(record)
    audit_path = DEST/'Organizer/RawCount.lean'; audit_source_sha = sha(audit_path)
    command = [str(lean), '-j1', str(audit_path.relative_to(DEST))]
    record['current_module'] = 'Organizer.RawCount'; save(record); print('INVOKE_RAW_COUNT_AXIOMS', flush=True)
    audit = guarded(command, DEST, env, DEST/'logs/raw_count_axioms', whole_mathlib=True)
    audit.update(module='Organizer.RawCount', source_sha256=audit_source_sha, is_endpoint_audit=True,
                 organizer_only=True, not_an_entrant_source_module=True)
    record['builds'].append(audit); outputs = parse(audit.get('stdout', ''))
    required = {'K4Ramsey.Final3840.exact_count', 'K4Ramsey.Final3840.exact_density'}
    observed = {o['endpoint']: o for o in outputs}
    clean_axioms = required <= set(observed) and all(observed[n]['classification'] not in {'SORRY_ADMISSION','UNRECOGNIZED_AXIOMS'} for n in required)
    record['raw_count_endpoint_outputs'] = outputs
    record['raw_count_requested_endpoints'] = sorted(required)
    record['native_dispatch_observations_clean'] = row.get('all_expected_native_images_observed', False) and not row.get('image_observation_errors')
    record['actual_native_Count_certificate_and_raw_axiom_audit_PASS'] = audit['state'] == 'PASS' and clean_axioms and record['native_dispatch_observations_clean']
    record['status'] = ('COUNT_CERTIFICATE_PASS_SCOPE_INCOMPLETE' if record['actual_native_Count_certificate_and_raw_axiom_audit_PASS']
                        else 'COUNT_SOURCE_PASS_RAW_OR_NATIVE_EVIDENCE_UNQUALIFIED')
    record['pilot_finished_utc'] = stamp(); record.pop('current_module', None)
    record['review_boundary'] = 'STOPPED_AFTER_TWO_CHECKS; original direct process remains untouched; root review required before remaining source dispatch.'
    record['fresh_custom_artifact_inventory'] = {str(p.relative_to(output)): {'bytes': p.stat().st_size, 'sha256': sha(p)}
                                                for p in output.rglob('*') if p.is_file()}
    save(record)
    print(json.dumps({'status': record['status'], 'source_module_actual_successes': 34,
                     'raw_count_endpoints': outputs, 'review_boundary': record['review_boundary']}, indent=2), flush=True)


if __name__ == '__main__': main()
