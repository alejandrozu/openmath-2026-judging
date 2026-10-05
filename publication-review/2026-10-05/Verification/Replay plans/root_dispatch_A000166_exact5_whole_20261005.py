"""Root actual sole replay handoff. Existing scientific runner and guards unchanged."""
from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, sys, msvcrt, time

V = Path(__file__).resolve().parent
sys.path.insert(0, str(V))
from resource_metrics import snapshot
from native_resource_guard import processes
from full_mathlib_scope import classify

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''): h.update(b)
    return h.hexdigest()

def binding(p):
    p = Path(p)
    return {'file': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}

def put_new(p, obj):
    assert not p.exists(), str(p)
    p.write_text(json.dumps(obj, indent=2), encoding='utf8')
    return binding(p)

def census():
    script = r"Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake|leanc|clang|gcc)\.exe$' -or ($_.Name -match '^python.*\.exe$' -and $_.CommandLine -match 'run_source_plan|run_a000_source|run_ht_ramsey|run_htpeo|run_original_e65') } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Depth 3"
    q = subprocess.run(['pwsh', '-NoProfile', '-Command', script], capture_output=True, text=True, check=True)
    rows = json.loads(q.stdout) if q.stdout.strip() else []
    if isinstance(rows, dict): rows = [rows]
    registry = processes()
    math = [{'pid': pid, **row} for pid, row in registry.items() if row['exe'].lower() in {'lean.exe', 'lake.exe', 'leanc.exe', 'clang.exe', 'gcc.exe'}]
    assert not rows and not math, 'Another mathematical compiler or source dispatcher is active'
    assert 55864 not in registry and 56304 not in registry, 'Old A000/HT parent still active'
    return {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'CIM_mathematical_compilers_and_dispatchers': rows, 'Toolhelp_mathematical_compilers': math, 'old_A00055864_and_HT56304_absent': True}

frozen = {
    'run_source_plan.py': '70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534',
    'full_mathlib_resource_guard.py': 'a4c76752e1e0afaf4ddff9368e4a5aa832bc56dcc7553182c5302e2c1c4e5c18',
    'matt_resource_guard.py': 'ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71',
    'native_resource_guard.py': '0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4',
    'resource_metrics.py': '1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed',
    'receipt_io.py': '2e189122fe360f1925dda2e0409c321b775fe7eb6edf17c3f13ef067d1776362',
    'lean_imports.py': '4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa',
    'full_mathlib_scope.py': '1698d525e0bac93cd241c499dc0a132e5c9477cabd7ca7899e4574645714a3ab',
    'audit_axioms.py': '1ee59639204140430c088023539a648f9007cc26c1856cf8cd2e3c2e59d7143f',
    'builds/sakana-a000224/build-plan.json': '0f6338f72ff570e79847995bac7cf6f6c56c8a1c2cc8dedf55181bc764180fe7',
    'a000224-whole-module-audit-boundary-evidence.json': '170886e5721254e24443bb6ec14f660409f14ceac938bf4d3c5c12d732cda6d0',
    'operational_history/a000166/ba420144481cf50c.json': 'ba420144481cf50ca830a1e44db44e90de417464fa672491c1f41925036b370f',
    'sakana-a000224-fresh-build.json': 'ba420144481cf50ca830a1e44db44e90de417464fa672491c1f41925036b370f',
    'A000-actual166-granular-completion-readonly-qualification-20261005T082522001255Z.json': '17e62b5196cbfaeeb34a704f270774134e6ceafef0ded9f26a467a845b1f36b2',
    'root-A000166-standard-allocation-verifier-correction-readonly-code-review-20261005.json': '7af97ea3fb3ff9c2a7cb432c6f5a9c392e09f7136b2ef1df90ec2a116dc333cf',
    'ht-ramsey-actual177-mode1-j2-natural-checkpoint-immutable-20261005.json': '5b827c653d1a07d5de5e8486a6451b33782a5a0b8788625d8fe10ac4b852ed6e',
    'htpeo-ramsey-current-fresh-build.json': '5b827c653d1a07d5de5e8486a6451b33782a5a0b8788625d8fe10ac4b852ed6e',
    'ht-ramsey-actual177-mode1-j2-readonly-partial-qualification-20261005.json': '5b7275e8ed5a68ac797a09ec18f8220fcabf67938749cf30d6aeef300e7434c0',
    'runtimes/lean-4.34.1-windows/bin/lean.exe': 'fcc4a10077d5fdd575592cea5f2981c91cbd77c490c80bc74407908e57e8b87b',
    'hold-third-worker-dispatch': 'cd23c0faaa1e08928bb4ad85720fb908569388cc85c403c86eced365efaac34b',
    'hold-original-e65-dispatch': '65f77bc65507c2065060f2f78ad2b7c116a35b454faba743b472a4e84bba5b5f',
    'full-mathlib-source-lease.json': 'b88a49773d0613d41bc8082be4e84ccbf68a7e07d216e0e58e020e26a731d763',
}
for name, expected in frozen.items(): assert sha(V/name) == expected, name
assert not (V/'sakana-a000224-fresh-build.json.tmp').exists()
assert not (V/'htpeo-ramsey-current-fresh-build.json.tmp').exists()
plan = json.loads((V/'builds/sakana-a000224/build-plan.json').read_bytes())
prior = json.loads((V/'sakana-a000224-fresh-build.json').read_bytes())
assert prior['status'] == 'SCHEDULED_RESOURCE_CHECKPOINT' and prior['finished_utc']
assert prior['modules'] == plan['modules'] and len(plan['modules']) == 171
whole = set(classify(plan)['authored_transitive_whole_Mathlib_closure'])
evidence = json.loads((V/'a000224-whole-module-audit-boundary-evidence.json').read_bytes())
assert whole == {x['module'] for x in evidence['five_authored_whole_modules']} and len(whole) == 5
good = {x['module']: x for x in prior['builds'] if x['exit'] == 0 and not x.get('stop_reason') and not x.get('is_endpoint_audit')}
assert set(good) == {x['module'] for x in plan['modules']} - whole and len(good) == 166
source_checks = []
artifact_checks = []
for m in plan['modules']:
    file = Path(m['file']); assert sha(file) == m['sha256'], m['module']
    source_checks.append({'module': m['module'], **binding(file)})
    if m['module'] in good:
        row = good[m['module']]
        if 'source_sha256' in row: assert row['source_sha256'] == m['sha256']
        assert row['artifacts'] and '-o' in row['command']
        assert str(file.relative_to(V/'builds/sakana-a000224')) in row['command']
        for a in row['artifacts']:
            p = Path(a['file']); assert sha(p) == a['sha256'] and p.stat().st_size == a['bytes']
            artifact_checks.append({'module': m['module'], **binding(p)})
    else:
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean'):
            assert not file.with_suffix(suffix).exists(), 'Whole output not cold: '+m['module']
assert plan['audit_modules'] == ['FreshAudit1.lean'] and not plan.get('non_acceptance_audit_modules')
audit = V/'builds/sakana-a000224/FreshAudit1.lean'
assert sha(audit) == 'c5e4477039688d0579f10457dae3ba29595d0f7cc05057f9fb63600e8b7d5547'
assert not any(audit.with_suffix(s).exists() for s in ('.olean','.olean.private','.olean.server','.ilean'))
dep = V/'dependencies/4.34.1/mathlib'
pins = json.loads((V/'dependencies-4.34.1-verified-git.json').read_bytes()); assert len(pins) == 9
git_checks = []
for x in pins:
    path = dep if x['name'] == 'mathlib' else dep/'.lake/packages'/x['name']
    head = subprocess.run(['git','rev-parse','HEAD'], cwd=path, capture_output=True, text=True, check=True).stdout.strip()
    origin = subprocess.run(['git','remote','get-url','origin'], cwd=path, capture_output=True, text=True, check=True).stdout.strip()
    assert head == x['rev'] and origin.removesuffix('.git') == x['url'].removesuffix('.git'), x['name']
    git_checks.append({'name': x['name'], 'file': str(path), 'actual_HEAD': head, 'actual_origin': origin})
assert plan['version'] == '4.34.1' and plan['mathlib_pin'] == pins[0]['rev'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
cache = V/'mathlib-4.34.1-cache-retry.json'; assert json.loads(cache.read_bytes())['status'] == 'PASS'
assert (dep/'.lake/build/lib/lean/Mathlib.olean').exists()
manifest = json.loads((dep/'lake-manifest.json').read_bytes())
assert {x['name']: x['rev'] for x in manifest['packages']} == {x['name']: x['rev'] for x in pins if x['name'] != 'mathlib'}
compiler = subprocess.run([str(V/'runtimes/lean-4.34.1-windows/bin/lean.exe'),'--version'], capture_output=True, text=True, check=True).stdout.strip()
assert 'version 4.34.1,' in compiler and '5045d0056413266e57c625dcd7c365b10e377c52' in compiler
for lockpath in (V/'.exclusive-full-mathlib-source.lock', V/'builds/sakana-a000224/.fresh-replay.lock'):
    with lockpath.open('r+b') as f:
        f.seek(0); msvcrt.locking(f.fileno(), msvcrt.LK_NBLCK, 1)
        f.seek(0); msvcrt.locking(f.fileno(), msvcrt.LK_UNLCK, 1)
observed = census()
resources = snapshot(); resources['disk_free_bytes'] = shutil.disk_usage(V).free
waiting = False
while resources['available_commit_bytes'] < 11*2**30 or resources['free_physical_bytes'] < 6*2**30 or resources['disk_free_bytes'] < 4_000_000_000:
    if not waiting:
        print('ROOT_PREFLIGHT_WAIT_UNCHANGED_STRICT_11GIB_6GIB_4GB_GATES',json.dumps(resources),flush=True)
        waiting = True
    assert sha(V/'hold-third-worker-dispatch') == frozen['hold-third-worker-dispatch']
    assert sha(V/'hold-original-e65-dispatch') == frozen['hold-original-e65-dispatch']
    time.sleep(2)
    resources = snapshot(); resources['disk_free_bytes'] = shutil.disk_usage(V).free
observed = census()
assert sha(V/'sakana-a000224-fresh-build.json') == frozen['sakana-a000224-fresh-build.json']
assert sha(V/'htpeo-ramsey-current-fresh-build.json') == frozen['htpeo-ramsey-current-fresh-build.json']
boundary = V/'root-A000166-HT177-actual-both-exits-zero-other-compilers-sole-preflight-20261005.json'
boundary_binding = put_new(boundary, {'status':'ACTUAL_BOTH_SOURCE_CONTROLLERS_NATURAL_EXIT0_ZERO_OTHER_MATH_COMPILERS','checked_utc':observed['checked_utc'],'root_actual_exec_results':{'A000_session53326':{'exit':0,'parent_pid':55864,'sources':166,'raw_sha256':frozen['sakana-a000224-fresh-build.json']},'HT_session80490':{'exit':0,'parent_pid':56304,'sources':177,'raw_sha256':frozen['htpeo-ramsey-current-fresh-build.json']}},'fresh_process_census':observed,'fresh_initial_whole_resource_gates':resources,'no_compiler_terminated_or_user_application_changed':True})
approval = V/'root-A000-actual166-exact5-whole-selected3-sole-dispatch-approval-20261005.json'
command = [sys.executable,'-X','utf8',str(V/'run_source_plan.py'),'sakana-a000224','1','--guarded-third-slot','--full-mathlib-source-mode','--a000-whole-scope-only']
approved = put_new(approval, {'status':'ROOT_APPROVED_A000_ACTUAL166_EXACT_FIVE_WHOLE_ORIGINAL_SELECTED3_SOLE_REPLAY','checked_utc':observed['checked_utc'],'producer':binding(Path(__file__)),'project':'sakana-a000224','source_plan_sha256':frozen['builds/sakana-a000224/build-plan.json'],'granular_completed_receipt_sha256':frozen['sakana-a000224-fresh-build.json'],'actual166_qualification_sha256':frozen['A000-actual166-granular-completion-readonly-qualification-20261005T082522001255Z.json'],'both_actual_exits_zero_Lean':boundary_binding,'reviewed_runner_sha256':frozen['run_source_plan.py'],'frozen_bindings':frozen,'all171_actual_source_checks':source_checks,'all166_current_owned_output_checks':artifact_checks,'five_whole_modules':sorted(whole),'original_audit':binding(audit),'actual_runtime_check':compiler,'actual_nine_dependency_HEAD_origins':git_checks,'cache_and_dependency_metadata':{name:binding(V/name) for name in ('lean-4.34.1-installation.json','dependencies-4.34.1-verified-git.json','mathlib-4.34.1-cache-retry.json','dependencies/4.34.1/mathlib/lake-manifest.json')},'cache_qualification':'Existing dated official PASS checked with current exact nine HEAD/origin and manifest; no new bulk provider rehash.','resource_policy':{'maximum_mathematical_compilers':1,'own_process_and_job_private_cap_bytes':10*2**30,'dispatch_available_commit_bytes':11*2**30,'dispatch_physical_bytes':6*2**30,'dispatch_disk_bytes':4_000_000_000,'continuous_commit_bytes':2**30,'continuous_physical_bytes':3*2**30,'continuous_disk_bytes':1_000_000_000},'fresh_gates':resources,'command':command,'source_or_storage_callback_changes':False,'prior166_guard_diversity_preserved':True,'scientific_scope':'Three distinct ordered odd primes2<p<q<r; actual square residue count, a(0)=1. No unrestricted A000224, priority, score or release upgrade inferred.','all_other_dispatchers_held_or_finished':'Both actual source controllers finished; E65 specific hold remains65f77; no other replay authorized until this sole controller actually exits.'})
history = V/'operational_history/a000-five-whole-sole-dispatch'; history.mkdir(parents=True, exist_ok=True)
for name in ('full-mathlib-source-lease.json','hold-third-worker-dispatch'):
    p = V/name; out=history/(sha(p)+('.json' if name.endswith('.json') else '.txt'))
    if out.exists(): assert out.read_bytes() == p.read_bytes()
    else: out.write_bytes(p.read_bytes())
lease = {'status':'ROOT_APPROVED_ACTUAL_A000_FIVE_WHOLE_ORIGINAL_SELECTED3_SOLE_SOURCE_LEASE','checked_utc':observed['checked_utc'],'holder_project':'sakana-a000224','source_plan_sha256':frozen['builds/sakana-a000224/build-plan.json'],'a000_whole_scope_only_authorized':True,'other_umbrella_compilers_confirmed_held_or_finished':True,'zero_other_Lean_compilers_confirmed':True,'actual166_finished_receipt_sha256':frozen['sakana-a000224-fresh-build.json'],'actual166_qualification_sha256':frozen['A000-actual166-granular-completion-readonly-qualification-20261005T082522001255Z.json'],'actual_HT177_finished_receipt_sha256':frozen['htpeo-ramsey-current-fresh-build.json'],'root_exact_scope_approval':approved,'both_exits_zero_Lean_preflight':boundary_binding,'maximum_mathematical_compilers':1,'own_process_and_job_private_cap_bytes':10*2**30,'dispatch_available_commit_bytes':11*2**30,'dispatch_physical_bytes':6*2**30,'dispatch_disk_bytes':4_000_000_000,'continuous_commit_bytes':2**30,'continuous_physical_bytes':3*2**30,'continuous_disk_bytes':1_000_000_000,'shell_threads':'-j1','LEAN_NUM_THREADS':'1','source_and_imports_unchanged':True,'storage_callback_disabled':True}
census()
assert sha(V/'full-mathlib-source-lease.json') == frozen['full-mathlib-source-lease.json']
assert sha(V/'hold-third-worker-dispatch') == frozen['hold-third-worker-dispatch']
assert sha(V/'hold-original-e65-dispatch') == frozen['hold-original-e65-dispatch']
(V/'full-mathlib-source-lease.json').write_text(json.dumps(lease,indent=2),encoding='utf8')
lease_binding = binding(V/'full-mathlib-source-lease.json')
(V/'hold-third-worker-dispatch').unlink()
put_new(V/'root-A000-exact5-whole-sole-lease-own-hold-handoff-actual-20261005.json',{'status':'ACTUAL_NEW_SOLE_LEASE_AND_BYTE_BOUND_OWN_GLOBAL_HOLD_PRESERVED_REMOVED','checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'approval':approved,'lease':lease_binding,'prior_lease_sha256':frozen['full-mathlib-source-lease.json'],'own_global_hold_sha256':frozen['hold-third-worker-dispatch'],'preserved_history':str(history),'E65_specific_hold_unchanged_sha256':frozen['hold-original-e65-dispatch'],'only_authorized_next_dispatch':command})
print('ROOT_A000_SOLE_ACTUAL_DISPATCH',json.dumps({'approval':approved,'lease':lease_binding,'command':command}),flush=True)
os.execv(sys.executable, command)
