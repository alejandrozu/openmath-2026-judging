"""Root-authorized operational checkpoint of two identity-verified owned PIDs.

No user application, other worker, source file or completed proof artifact changes.
"""
from pathlib import Path
import ctypes, datetime, hashlib, json, os, subprocess, time
from ctypes import wintypes as W
from native_resource_guard import K, processes, own_tree, memory
from luke_native_source_guard import counters
from receipt_io import read_bytes_shared

BASE = Path(__file__).resolve().parent
REPORT = BASE/'luke-k4-ramsey-current-direct-fresh-build.json'
COUNT_PID = 3184
RUNNER_PID = 49540
COUNT_MODULE = 'K4Ramsey.Constructions.Final3840.Certificate'

K.TerminateProcess.argtypes = [W.HANDLE, W.UINT]; K.TerminateProcess.restype = W.BOOL
K.WaitForSingleObject.argtypes = [W.HANDLE, W.DWORD]; K.WaitForSingleObject.restype = W.DWORD
K.GetExitCodeProcess.argtypes = [W.HANDLE, ctypes.POINTER(W.DWORD)]; K.GetExitCodeProcess.restype = W.BOOL
K.QueryFullProcessImageNameW.argtypes = [W.HANDLE, W.DWORD, W.LPWSTR, ctypes.POINTER(W.DWORD)]
K.QueryFullProcessImageNameW.restype = W.BOOL
K.GetProcessTimes.argtypes = [W.HANDLE, ctypes.POINTER(W.FILETIME), ctypes.POINTER(W.FILETIME), ctypes.POINTER(W.FILETIME), ctypes.POINTER(W.FILETIME)]
K.GetProcessTimes.restype = W.BOOL


def stamp(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def atomic(p, raw):
    t = p.with_suffix(p.suffix+'.tmp')
    with t.open('wb') as f: f.write(raw); f.flush(); os.fsync(f.fileno())
    for attempt in range(60):
        try: os.replace(t, p); return
        except PermissionError:
            if attempt == 59: raise
            time.sleep(.1)


def process_info(handle):
    path = ctypes.create_unicode_buffer(32768); length = W.DWORD(len(path))
    assert K.QueryFullProcessImageNameW(handle, 0, path, ctypes.byref(length))
    creation = W.FILETIME(); end = W.FILETIME(); kernel = W.FILETIME(); user = W.FILETIME()
    assert K.GetProcessTimes(handle, ctypes.byref(creation), ctypes.byref(end), ctypes.byref(kernel), ctypes.byref(user))
    ticks = lambda f: int(f.dwLowDateTime)+(int(f.dwHighDateTime)<<32)
    started = datetime.datetime(1601,1,1,tzinfo=datetime.timezone.utc)+datetime.timedelta(microseconds=ticks(creation)//10)
    exit_code = W.DWORD(); assert K.GetExitCodeProcess(handle, ctypes.byref(exit_code))
    return {'executable': path.value, 'started_utc': started.isoformat(),
            'creation_FILETIME': ticks(creation), 'cpu_seconds': (ticks(kernel)+ticks(user))/10_000_000,
            'exit_code': int(exit_code.value)}


def main():
    import argparse
    p = argparse.ArgumentParser(); p.add_argument('--authorization', required=True); args = p.parse_args()
    assert args.authorization == 'ROOT_REVISED_OWN_DIRECT_RESOURCE_CHECKPOINT_AUTHORIZED'
    initial_raw = read_bytes_shared(REPORT); d = json.loads(initial_raw)
    assert d['status'] == 'RUNNING' and d['current_module'] == COUNT_MODULE
    assert len([n for n,s in d['module_states'].items() if s=='PASS']) == 33
    m = next(m for m in d['modules'] if m['module'] == COUNT_MODULE)
    assert sha(m['file']) == m['sha256'] == sha(m['frozen_source'])
    source_dir = Path(d['source_dir']); out = source_dir/'.lake/build/lib/lean'
    lean = BASE/'runtimes/lean-4.34.1-windows/bin/lean.exe'
    target = out.joinpath(*COUNT_MODULE.split('.'))
    expected_command = [str(lean), '-j1', '-o', str(target)+'.olean', '-i', str(target)+'.ilean', str(Path(m['file']).relative_to(source_dir))]
    query = ("$rows=@(); foreach($id in @(3184,49540)){ $p=Get-CimInstance Win32_Process -Filter ('ProcessId='+$id); "
             "$rows += [PSCustomObject]@{PID=$p.ProcessId;ParentPID=$p.ParentProcessId;Executable=$p.ExecutablePath;Command=$p.CommandLine;" 
             "StartedUTC=$p.CreationDate.ToUniversalTime().ToString('o')}}; ConvertTo-Json -InputObject $rows -Depth 3")
    result = subprocess.run(['powershell', '-NoProfile', '-Command', query], capture_output=True, text=True, encoding='utf8')
    assert result.returncode == 0; rows = {int(r['PID']):r for r in json.loads(result.stdout)}
    assert rows[COUNT_PID]['ParentPID'] == RUNNER_PID
    assert rows[COUNT_PID]['Command'] == subprocess.list2cmdline(expected_command)
    assert rows[RUNNER_PID]['Command'].endswith('-X utf8 work/publication/verification/run_luke_direct_plan.py')
    registry = processes(); assert own_tree(RUNNER_PID, registry) == {RUNNER_PID, COUNT_PID}
    handles = {}
    before = {'started_utc':stamp(), 'status':'IDENTITY_VERIFIED_BEFORE_OWN_OPERATIONAL_CHECKPOINT',
              'runner_sha256':sha(__file__), 'source_sha256':m['sha256'], 'expected_command':expected_command,
              'CIM_identity_rows':list(rows.values()), 'initial_counters':counters(),
              'old_Count_memory':memory(COUNT_PID), 'own_tree_exact_PIDs':[RUNNER_PID, COUNT_PID]}
    try:
        for pid in [RUNNER_PID, COUNT_PID]:
            handle = K.OpenProcess(0x0001 | 0x1000 | 0x00100000, False, pid)
            assert handle, 'Cannot bind verified owned process handle'
            handles[pid] = handle
            info = process_info(handle)
            assert info['exit_code'] == 259
            assert Path(info['executable']) == Path(rows[pid]['Executable'])
            expected_start = '2026-10-04T21:49:30.299275+00:00' if pid==RUNNER_PID else '2026-10-04T22:48:02.973787+00:00'
            assert info['started_utc'] == expected_start, 'PID creation identity changed'
            before.setdefault('bound_process_handle_identity',{})[str(pid)] = info
        snapshot_dir = BASE/'native_source_attempts'; snapshot_dir.mkdir(exist_ok=True)
        suffix = stamp()[:19].replace(':','').replace('-','')
        snapshot = snapshot_dir/('direct33-before-coordinated-checkpoint-'+suffix+'.json')
        assert not snapshot.exists(); atomic(snapshot, initial_raw)
        inventory = {str(f.relative_to(out)):{'bytes':f.stat().st_size,'sha256':sha(f)} for f in out.rglob('*') if f.is_file()}
        for name,s in d['module_states'].items():
            if s=='PASS': assert str(Path(*name.split('.')))+'.olean' in inventory
        before.update(prior_receipt_snapshot_file=str(snapshot),prior_receipt_snapshot_sha256=hashlib.sha256(initial_raw).hexdigest(),
                      prior_completed_module_count=33,partial_artifact_inventory=inventory,
                      source_statement='Active Count has not completed. Completed33 own cold module outputs are preserved.',
                      piped_output_limitation='The active Count stdout/stderr pipes have not returned to the Python parent; these unfinished streams cannot be recovered by this checkpoint. Actual completed33 diagnostic strings are retained in the immutable prior receipt. No full Count log is invented.')
        # Recheck the live receipt and both bound handles immediately before stopping.
        latest = json.loads(read_bytes_shared(REPORT))
        assert latest['current_module'] == COUNT_MODULE and len(latest['builds']) == len(d['builds'])
        assert all(process_info(h)['exit_code']==259 for h in handles.values())
        assert own_tree(RUNNER_PID, processes()) == {RUNNER_PID, COUNT_PID}
        pre = snapshot_dir/('checkpoint-identity-before-stop-'+suffix+'.json')
        assert not pre.exists(); atomic(pre,json.dumps(before,indent=2).encode('utf8'))
        stops = []
        # Stop the verified parent first so it cannot dispatch another module.
        for pid in [RUNNER_PID, COUNT_PID]:
            ok = bool(K.TerminateProcess(handles[pid], 88 if pid==RUNNER_PID else 87))
            wait = int(K.WaitForSingleObject(handles[pid], 15000))
            exit_code=W.DWORD();assert K.GetExitCodeProcess(handles[pid],ctypes.byref(exit_code))
            stops.append({'pid':pid,'terminate_success':ok,'wait_result':wait,'actual_exit_code':int(exit_code.value),
                          'prior_bound_process_identity':before['bound_process_handle_identity'][str(pid)],
                          'post_exit_image_query_not_required':True})
            assert ok and wait==0 and exit_code.value==(88 if pid==RUNNER_PID else 87), 'Own checkpoint stop did not finish as requested'
        result = {**before, 'status':'SCHEDULED_RESOURCE_CHECKPOINT_COUNT_UNFINISHED',
                  'finished_utc':stamp(),'actual_stop_results':stops,'final_counters':counters(),
                  'source_result_notice':'This coordinated operational stop is neither a Lean proof failure nor a Count proof PASS. The source-identical native retry is separately pending.',
                  'partial_artifact_inventory_after':{str(f.relative_to(out)):{'bytes':f.stat().st_size,'sha256':sha(f)} for f in out.rglob('*') if f.is_file()}}
        assert result['partial_artifact_inventory_after']==inventory
        checkpoint = BASE/'luke-direct-coordinated-resource-checkpoint.json'; assert not checkpoint.exists()
        atomic(checkpoint,json.dumps(result,indent=2).encode('utf8'))
        d.update(status='SCHEDULED_RESOURCE_CHECKPOINT_COUNT_UNFINISHED',finished_utc=result['finished_utc'],
                 unfinished_active_module=COUNT_MODULE,coordinated_resource_checkpoint_file=str(checkpoint),
                 coordinated_resource_checkpoint_sha256=sha(checkpoint),fresh_custom_artifact_inventory=inventory,
                 module_states={**d['module_states'],COUNT_MODULE:'UNFINISHED_SCHEDULED_RESOURCE_CHECKPOINT'})
        d.pop('current_module',None); atomic(REPORT,json.dumps(d,indent=2).encode('utf8'))
        print(json.dumps({'checkpoint':str(checkpoint),'sha256':sha(checkpoint),'status':result['status'],
                          'actual_stops':stops,'final_counters':result['final_counters']},indent=2),flush=True)
    finally:
        for handle in handles.values(): K.CloseHandle(handle)


if __name__=='__main__':main()
