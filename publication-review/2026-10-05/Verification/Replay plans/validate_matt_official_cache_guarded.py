"""Prepared one-invocation whole-Mathlib pilot; requires explicit proof-slot handoff."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys
from receipt_io import read_json_shared
from matt_resource_guard import guarded_tree
from native_resource_guard import stamp

BASE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--handoff-token', required=True)
parser.add_argument('--self-test', action='store_true')
args = parser.parse_args()
assert args.handoff_token == 'ROOT_APPROVED_MATT_FULL_IMPORT_PILOT'

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def atomic(path, data):
    tmp = path.with_suffix('.json.tmp')
    tmp.write_text(json.dumps(data, indent=2), encoding='utf-8')
    os.replace(tmp, path)

if args.self_test:
    target = BASE / 'matt-resource-guard-self-test.json'
    assert not target.exists(), 'Do not overwrite resource guard self-test receipt'
    result = guarded_tree([sys.executable, '-X', 'utf8', '-c', 'print("OWN_JOB_SELF_TEST_PASS")'], BASE,
                           dict(os.environ), BASE / 'matt-resource-guard-self-test', timeout=30)
    result['scope'] = 'Bounded operational Python child test only; no mathematical compiler.'
    atomic(target, result)
    print('RESOURCE_GUARD_SELF_TEST', result['state'])
    raise SystemExit(0)

version = '4.30.0-rc2'
root = BASE / 'dependencies' / version / 'mathlib'
runtime = BASE / 'runtimes' / ('lean-'+version+'-windows')
report = BASE / ('mathlib-'+version+'-cache-retry.json')
record = read_json_shared(report)
assert record['status'] == 'CACHE_EXTRACTED_AWAITING_SINGLE_IMPORT_VALIDATION'
planfile = BASE / ('official-cache-plan-'+version+'.json')
assert sha(planfile) == record['official_plan_sha256']
rows = json.loads(planfile.read_text())
assert len(rows) == record['official_module_count'] == 8308
assert sum(b['module_count'] for b in record['batches']) == len(rows)
assert all(b['leantar_exit'] == 0 and b['compression_exit_codes'] == [0] for b in record['batches'])
for row in rows:
    trace = Path(row['trace']); trace = trace if trace.is_absolute() else root / trace
    assert trace.resolve().is_relative_to(root.resolve())
    assert trace.exists() and trace.with_suffix('.olean').exists(), str(trace)
installation = read_json_shared(BASE / ('lean-'+version+'-installation.json'))
assert installation['complete'] and installation['compiler_check']['exit'] == 0
assert installation['expected_digest'] == 'sha256:'+installation['sha256']
identities = []
for dependency in read_json_shared(BASE / ('dependencies-'+version+'-source-manifest.json')):
    destination = Path(dependency['destination'])
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=destination, capture_output=True,
                          text=True, check=True).stdout.strip()
    assert head == dependency['commit'], str(destination)
    identities.append({'destination': str(destination), 'expected_commit': dependency['commit'], 'actual_commit': head})
compiler = subprocess.run([str(runtime / 'bin' / 'lean.exe'), '--version'], capture_output=True,
                          text=True, check=True).stdout.strip()
assert 'version '+version+',' in compiler and '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc' in compiler
self_test = read_json_shared(BASE / 'matt-resource-guard-self-test.json')
assert self_test['state'] == 'PASS' and self_test['own_job_assignment_before_resume'] == 'PASS'
commit_preflight = read_json_shared(BASE / 'matt-resource-commit-preflight.json')
assert commit_preflight['status'] == 'COMMIT_COUNTER_PREFLIGHT_PASS'
assert commit_preflight['counter_helper_sha256'] == sha(BASE / 'resource_metrics.py')
target = BASE / 'matt-full-mathlib-import-pilot.json'
assert not target.exists(), 'Do not overwrite an earlier full-import pilot receipt'
validation = BASE / 'ValidateOfficialMathlib4300rc2Guarded.lean'
validation.write_text('import Mathlib\nexample : (2 : ℝ) + 2 = 4 := by norm_num\n#print axioms Nat.add_comm\n', encoding='utf-8')
env = dict(os.environ); env['PATH'] = str(runtime / 'bin')+';'+env['PATH']; env['LEAN_NUM_THREADS'] = '1'
command = [str(runtime / 'bin' / 'lake.exe'), '--no-cache', 'env', 'lean', '-j1', str(validation)]
result = guarded_tree(command, root, env, BASE / 'matt-full-mathlib-import-pilot', timeout=900)
result.update(scope='Whole exact-pinned official Mathlib import, norm_num example and Nat.add_comm axiom print; no entrant proof.',
              version=version, official_plan_sha256=sha(planfile), dependency_identities=identities,
              compiler_version=compiler, validation_source_sha256=sha(validation),
              validation_guard_sha256=sha(BASE / 'matt_resource_guard.py'),
              commit_counter_preflight_receipt_sha256=sha(BASE / 'matt-resource-commit-preflight.json'))
atomic(target, result)
if result['attempted']:
    frozen = BASE / ('mathlib-'+version+'-cache-extracted-before-validation.json')
    assert not frozen.exists()
    frozen.write_bytes(report.read_bytes())
    record['extraction_receipt_archive'] = {'file': str(frozen), 'sha256': sha(frozen)}
    record['full_mathlib_import_validation'] = result
    record['validation_dependency_identity_preflight'] = identities
    record['validation_compiler_version'] = compiler
    record['minimum_free_bytes'] = min(record['minimum_free_bytes'], result['minimum_disk_free_bytes'])
    record['status'] = 'PASS' if result['state'] == 'PASS' else result['state'] if result['state'].startswith('ENVIRONMENT_') else 'FULL_MATHLIB_IMPORT_VALIDATION_FAILED'
    record['finished_utc'] = stamp(); record['remaining_free_bytes'] = shutil.disk_usage(BASE).free
    atomic(report, record)
print('MATT_FULL_MATHLIB_PILOT', result['state'], 'CACHE_STATUS', record['status'])
