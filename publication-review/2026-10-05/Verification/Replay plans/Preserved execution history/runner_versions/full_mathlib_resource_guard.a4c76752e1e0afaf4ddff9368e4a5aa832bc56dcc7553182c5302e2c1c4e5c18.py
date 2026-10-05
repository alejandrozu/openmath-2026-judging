# Approved derived guard: original matt_resource_guard.py SHA256 ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71
"""Bounded own-job guard using the verified native resource counter helpers.

The child is suspended until job assignment, so Lake descendants cannot escape
the aggregate private-memory cap. Importing this module starts no process.
"""
from pathlib import Path
import ctypes, hashlib, os, shutil, subprocess, time
from native_resource_guard import K, W, EXTENDEDLIMIT, GIB, physical, memory, processes, own_tree, stamp
from resource_metrics import snapshot as system_snapshot

BASE = Path(__file__).resolve().parent
COUNTER_HELPER_SHA256 = hashlib.sha256((BASE / 'native_resource_guard.py').read_bytes()).hexdigest()
COMMIT_COUNTER_HELPER_SHA256 = hashlib.sha256((BASE / 'resource_metrics.py').read_bytes()).hexdigest()

class THREADENTRY32(ctypes.Structure):
    _fields_ = [('dwSize', W.DWORD), ('cntUsage', W.DWORD), ('th32ThreadID', W.DWORD),
                ('th32OwnerProcessID', W.DWORD), ('tpBasePri', W.LONG),
                ('tpDeltaPri', W.LONG), ('dwFlags', W.DWORD)]

K.Thread32First.argtypes = [W.HANDLE, ctypes.POINTER(THREADENTRY32)]
K.Thread32First.restype = W.BOOL
K.Thread32Next.argtypes = K.Thread32First.argtypes
K.Thread32Next.restype = W.BOOL
K.OpenThread.argtypes = [W.DWORD, W.BOOL, W.DWORD]
K.OpenThread.restype = W.HANDLE
K.ResumeThread.argtypes = [W.HANDLE]
K.ResumeThread.restype = W.DWORD

def resume_suspended_root(pid):
    snapshot = K.CreateToolhelp32Snapshot(4, 0)
    if snapshot == ctypes.c_void_p(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        entry = THREADENTRY32(); entry.dwSize = ctypes.sizeof(entry)
        ok = K.Thread32First(snapshot, ctypes.byref(entry))
        tids = []
        while ok:
            if entry.th32OwnerProcessID == pid:
                tids.append(entry.th32ThreadID)
            ok = K.Thread32Next(snapshot, ctypes.byref(entry))
        assert len(tids) == 1, 'Expected one suspended initial child thread'
        thread = K.OpenThread(2, False, tids[0])
        if not thread:
            raise ctypes.WinError(ctypes.get_last_error())
        try:
            previous = K.ResumeThread(thread)
            assert previous == 1, 'Unexpected initial suspension count'
        finally:
            K.CloseHandle(thread)
    finally:
        K.CloseHandle(snapshot)

def guarded_tree(command, cwd, env, log_prefix, timeout=900):
    prefix = Path(log_prefix); prefix.parent.mkdir(parents=True, exist_ok=True)
    stdout = Path(str(prefix) + '.stdout.txt'); stderr = Path(str(prefix) + '.stderr.txt')
    initial_system = system_snapshot()
    row = {'command': command, 'cwd': str(cwd), 'started_utc': stamp(), 'attempted': False,
           'counter_helper_sha256': COUNTER_HELPER_SHA256,
           'commit_counter_helper_sha256': COMMIT_COUNTER_HELPER_SHA256,
           'resource_policy': {'initial_disk_bytes': 4_000_000_000, 'initial_physical_bytes': 6*GIB,
             'initial_available_commit_bytes': 11*GIB,
             'continuous_disk_bytes': 1_000_000_000, 'continuous_physical_bytes': 3*GIB,
             'continuous_available_commit_bytes': 1*GIB,
             'own_job_private_bytes': 10*GIB, 'own_process_private_bytes': 10*GIB,
             'poll_seconds': .25, 'timeout_seconds': timeout},
           'minimum_disk_free_bytes': shutil.disk_usage(BASE).free,
           'initial_system_memory_snapshot': initial_system,
           'minimum_physical_available_bytes': initial_system['free_physical_bytes'],
           'minimum_available_commit_bytes': initial_system['available_commit_bytes']}
    if (row['minimum_disk_free_bytes'] < 4_000_000_000 or
        row['minimum_physical_available_bytes'] < 6*GIB or
        row['minimum_available_commit_bytes'] < 11*GIB):
        row['state'] = 'NOT_INVOKED_RESOURCE_DISPATCH_GATE'
        return row
    job = K.CreateJobObjectW(None, None)
    if not job:
        raise ctypes.WinError(ctypes.get_last_error())
    limits = EXTENDEDLIMIT()
    limits.BasicLimitInformation.LimitFlags = 0x2000 | 0x0100 | 0x0200
    limits.ProcessMemoryLimit = 10*GIB; limits.JobMemoryLimit = 10*GIB
    if not K.SetInformationJobObject(job, 9, ctypes.byref(limits), ctypes.sizeof(limits)):
        K.CloseHandle(job)
        raise ctypes.WinError(ctypes.get_last_error())
    start = time.monotonic(); seen = {}; peak_private = 0; peak_rss = 0; samples = 0; proc = None
    try:
        with stdout.open('wb') as out, stderr.open('wb') as err:
            proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=out, stderr=err,
                                    creationflags=0x08000000 | 0x00000004)
            row.update(attempted=True, root_pid=proc.pid)
            if not K.AssignProcessToJobObject(job, W.HANDLE(int(proc._handle))):
                proc.kill(); proc.wait()
                raise ctypes.WinError(ctypes.get_last_error())
            row['own_job_assignment_before_resume'] = 'PASS'
            resume_suspended_root(proc.pid)
            stop = None
            while True:
                registry = processes(); observed = []
                for pid in own_tree(proc.pid, registry):
                    metrics = memory(pid)
                    if metrics:
                        observed.append(metrics)
                        entry = seen.setdefault(str(pid), {'exe': registry.get(pid, {}).get('exe', ''),
                            'peak_private_bytes': 0, 'peak_rss_bytes': 0})
                        entry['peak_private_bytes'] = max(entry['peak_private_bytes'], metrics['private_bytes'])
                        entry['peak_rss_bytes'] = max(entry['peak_rss_bytes'], metrics['peak_rss_bytes'])
                total_private = sum(m['private_bytes'] for m in observed)
                peak_private = max(peak_private, total_private)
                peak_rss = max(peak_rss, sum(m['rss_bytes'] for m in observed)); samples += 1
                disk = shutil.disk_usage(BASE).free; system = system_snapshot()
                available = system['free_physical_bytes']; commit = system['available_commit_bytes']
                row['minimum_disk_free_bytes'] = min(row['minimum_disk_free_bytes'], disk)
                row['minimum_physical_available_bytes'] = min(row['minimum_physical_available_bytes'], available)
                row['minimum_available_commit_bytes'] = min(row['minimum_available_commit_bytes'], commit)
                if disk < 1_000_000_000: stop = 'ENVIRONMENT_BLOCKED_DISK_RESERVE'
                elif available < 3*GIB: stop = 'ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE'
                elif commit < 1*GIB: stop = 'ENVIRONMENT_BLOCKED_COMMIT_RESERVE'
                elif total_private > 10*GIB: stop = 'ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT'
                elif time.monotonic() - start > timeout: stop = 'OPERATIONAL_TIMEOUT'
                if stop:
                    K.TerminateJobObject(job, 77); proc.wait(timeout=15); break
                if proc.poll() is not None: break
                time.sleep(.25)
            proc.wait(timeout=15); row['exit'] = proc.returncode
            final_limits = EXTENDEDLIMIT()
            if not K.QueryInformationJobObject(job, 9, ctypes.byref(final_limits), ctypes.sizeof(final_limits), None):
                raise ctypes.WinError(ctypes.get_last_error())
            row['job_peak_process_private_bytes'] = int(final_limits.PeakProcessMemoryUsed)
            row['job_peak_aggregate_private_bytes'] = int(final_limits.PeakJobMemoryUsed)
            text = stdout.read_text(encoding='utf-8', errors='replace') + stderr.read_text(encoding='utf-8', errors='replace')
            if not stop and proc.returncode != 0 and any(s in text.lower() for s in ['out of memory', 'failed to allocate', 'bad_alloc']):
                stop = 'ENVIRONMENT_BLOCKED_OWN_ALLOCATION_FAILURE'
            row['state'] = stop or ('PASS' if proc.returncode == 0 else 'COMMAND_FAILED')
    except Exception as error:
        K.TerminateJobObject(job, 78)
        if proc is not None:
            proc.wait(timeout=15)
        row.update(state='OPERATIONAL_ERROR', error=str(error))
    finally:
        K.CloseHandle(job)
    row.update(finished_utc=stamp(), seconds=round(time.monotonic()-start, 3),
        polled_peak_tree_private_bytes=peak_private, polled_peak_tree_rss_bytes=peak_rss,
        counter_samples=samples, observed_own_processes=seen,
        stdout_file=str(stdout), stderr_file=str(stderr),
        stdout_sha256=hashlib.sha256(stdout.read_bytes()).hexdigest(),
        stderr_sha256=hashlib.sha256(stderr.read_bytes()).hexdigest(),
        stdout_excerpt=stdout.read_text(encoding='utf-8', errors='replace')[:32768],
        stderr_excerpt=stderr.read_text(encoding='utf-8', errors='replace')[:32768])
    assert COUNTER_HELPER_SHA256 == hashlib.sha256((BASE / 'native_resource_guard.py').read_bytes()).hexdigest()
    assert COMMIT_COUNTER_HELPER_SHA256 == hashlib.sha256((BASE / 'resource_metrics.py').read_bytes()).hexdigest()
    return row
