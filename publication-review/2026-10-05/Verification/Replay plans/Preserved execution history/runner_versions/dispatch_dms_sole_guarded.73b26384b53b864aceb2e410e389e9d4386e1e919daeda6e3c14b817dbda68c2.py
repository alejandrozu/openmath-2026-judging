"""Exact DMS resource-only resume after the reviewed clean source boundary."""
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys, time
from receipt_io import read_bytes_shared
from resource_metrics import snapshot
from native_resource_guard import processes, stamp, save_once

BASE = Path(__file__).resolve().parent
PROJECT = 'htpeo-dms-current'
assert sys.argv[1:] == ['--execute']
plan_path = BASE / 'builds' / PROJECT / 'build-plan.json'
plan_raw = plan_path.read_bytes(); plan = json.loads(plan_raw)
report_path = BASE / (PROJECT + '-fresh-build.json')
raw = read_bytes_shared(report_path); prior = json.loads(raw)
assert prior['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT'
retained_count = sum(r['exit'] == 0 and not r['is_endpoint_audit'] for r in prior['builds'])
assert 118 <= retained_count <= len(plan['modules'])
original_pending_row = next(r for r in prior['builds'] if r['module'] == 'GPn2T')
assert original_pending_row['exit'] == 0 and original_pending_row['stop_reason'] is None
for source in plan['modules']:
    assert hashlib.sha256(Path(source['file']).read_bytes()).hexdigest() == source['sha256']
for row in prior['builds']:
    if row['exit'] == 0:
        for artifact in row['artifacts']:
            assert hashlib.sha256(Path(artifact['file']).read_bytes()).hexdigest() == artifact['sha256']
assert not (BASE / 'hold-third-worker-dispatch').exists()
receipt = BASE / ('dms-sole-guarded-dispatch-' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()) + '.json')
evidence = {'status':'WAITING_STRICT_SOLE_WHOLE_LIBRARY_DISPATCH', 'started_utc':stamp(),
    'source_plan_sha256':hashlib.sha256(plan_raw).hexdigest(),
    'checkpoint_receipt_sha256':hashlib.sha256(raw).hexdigest(),
    'retained_source_passes':retained_count, 'retained_source_and_artifact_hashes':'PASS',
    'runner_sha256':hashlib.sha256((BASE/'run_source_plan.py').read_bytes()).hexdigest(),
    'guard_sha256':hashlib.sha256((BASE/'full_mathlib_resource_guard.py').read_bytes()).hexdigest(),
    'qualification':'Root approved sole whole-library resume after actual Luke and main granular exits; this waits for unchanged strict resource gates.'}
save_once(receipt,evidence)
while True:
    assert not [p for p,r in processes().items() if r['exe'].lower() == 'lean.exe'], 'Sole source lease requires no other Lean compiler'
    metrics = {'disk_free_bytes':shutil.disk_usage(BASE).free, **snapshot()}
    if metrics['disk_free_bytes'] >= 4_000_000_000 and metrics['free_physical_bytes'] >= 6*2**30 and metrics['available_commit_bytes'] >= 11*2**30:
        break
    if (BASE/'hold-third-worker-dispatch').exists():
        save_once(receipt.with_name(receipt.stem+'.held.json'),{'status':'NO_ATTEMPT_COORDINATOR_HOLD','metrics':metrics})
        raise SystemExit(0)
    time.sleep(2)
lease_path = BASE/'full-mathlib-source-lease.json'
if lease_path.exists():
    save_once(receipt.with_name(receipt.stem+'.prior-lease.json'), json.loads(lease_path.read_bytes()))
lease = {'created_utc':stamp(),'holder_project':PROJECT,'source_plan_sha256':evidence['source_plan_sha256'],
    'other_umbrella_compilers_confirmed_held_or_finished':True,
    'root_authorization':'Reviewed118-source boundary, after actual Luke and main granular exits; sole future10GiB/11GiB whole-library route.',
    'scheduling':'SOLE_DMS_SOURCE_IMPORTER_OTHER_SOURCE_QUEUES_HELD', 'dispatch_metrics':metrics,
    'checkpoint_receipt_sha256':evidence['checkpoint_receipt_sha256']}
temp = lease_path.with_suffix('.json.tmp');temp.write_text(json.dumps(lease,indent=2),encoding='utf8');os.replace(temp,lease_path)
cmd=[sys.executable,'-X','utf8',str(BASE/'run_source_plan.py'),PROJECT,'1','--guarded-third-slot','--full-mathlib-source-mode']
save_once(receipt.with_name(receipt.stem+'.dispatch.json'),{'status':'DISPATCH_GATES_PASSED','command':cmd,'metrics':metrics,'lease':lease,'finished_utc':stamp()})
print('DMS_SOLE_DISPATCH',json.dumps(metrics),flush=True)
code=subprocess.call(cmd,cwd=BASE.parents[2])
save_once(receipt.with_name(receipt.stem+'.completed.json'),{'wrapper_exit':code,'source_receipt_sha256':hashlib.sha256(read_bytes_shared(report_path)).hexdigest(),'finished_utc':stamp()})
raise SystemExit(code)
