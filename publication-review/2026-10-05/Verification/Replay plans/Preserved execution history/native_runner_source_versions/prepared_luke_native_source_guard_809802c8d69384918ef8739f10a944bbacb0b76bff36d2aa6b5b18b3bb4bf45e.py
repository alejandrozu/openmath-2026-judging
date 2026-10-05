"""Guard an explicitly authorized owned Lean invocation; never dispatch on import."""
from pathlib import Path
import ctypes, hashlib, os, shutil, subprocess, time
from native_resource_guard import K, W, EXTENDEDLIMIT, MEMORYSTATUSEX, GIB, processes, own_tree, memory, stamp
from luke_native_image_observer import loaded_images, exact_cache_slots, image_file_hash

BASE = Path(__file__).resolve().parent
N = ctypes.WinDLL('ntdll')
N.NtResumeProcess.argtypes = [W.HANDLE]
N.NtResumeProcess.restype = ctypes.c_long


def counters():
    info = MEMORYSTATUSEX(); info.dwLength = ctypes.sizeof(info)
    if not K.GlobalMemoryStatusEx(ctypes.byref(info)):
        raise ctypes.WinError(ctypes.get_last_error())
    return {'disk_free_bytes': shutil.disk_usage(BASE).free,
            'physical_available_bytes': int(info.ullAvailPhys),
            'available_commit_bytes': int(info.ullAvailPageFile),
            'commit_limit_bytes': int(info.ullTotalPageFile)}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def guarded(command, cwd, env, prefix, native_images=None, timeout=14400, whole_mathlib=True):
    """Own job only. Optional image observation uses ToolHelp and three data slots.

    `native_images` is a finished actual PE audit, never an untested DLL guess.
    No adapter DLL is loaded in this Python observer.
    """
    prefix = Path(prefix); prefix.parent.mkdir(parents=True, exist_ok=True)
    stdout = Path(str(prefix) + '.stdout.txt'); stderr = Path(str(prefix) + '.stderr.txt')
    assert not stdout.exists() and not stderr.exists(), 'Invocation logs must be cold'
    cap=(10 if whole_mathlib else 6)*GIB
    initial_commit=(11 if whole_mathlib else 5)*GIB
    initial = counters()
    row = {'command': command, 'cwd': str(cwd), 'started_utc': stamp(), 'attempted': False,
           'dispatch_counters': initial, 'minimum_counters': dict(initial),
           'guard_sha256': sha(__file__), 'counter_helper_sha256': sha(BASE/'native_resource_guard.py'),
           'image_observer_sha256': sha(BASE/'luke_native_image_observer.py'),
           'resource_policy': {'initial_disk_bytes': 4_000_000_000,
             'initial_physical_bytes': 6*GIB, 'initial_available_commit_bytes': initial_commit,
             'continuous_disk_bytes': 1_000_000_000, 'continuous_physical_bytes': 3*GIB,
             'continuous_available_commit_bytes': GIB, 'own_job_private_cap_bytes': cap,
             'own_process_private_cap_bytes': cap, 'poll_seconds': .25,
             'timeout_seconds': timeout},
           'uses_native_adapter': bool(native_images), 'loaded_native_images': [],
           'cache_pointer_observations': [], 'image_observation_errors': []}
    if (initial['disk_free_bytes'] < 4_000_000_000 or initial['physical_available_bytes'] < 6*GIB
            or initial['available_commit_bytes'] < initial_commit):
        row['state'] = 'NOT_INVOKED_RESOURCE_DISPATCH_GATE'
        return row
    if native_images:
        assert len(native_images) == 2
        for image in native_images:
            assert sha(image['file']) == image['sha256']
    expected = {Path(i['file']).name.lower(): i for i in (native_images or [])}
    job = K.CreateJobObjectW(None, None)
    if not job: raise ctypes.WinError(ctypes.get_last_error())
    limits = EXTENDEDLIMIT(); limits.BasicLimitInformation.LimitFlags = 0x2000 | 0x0100 | 0x0200
    limits.ProcessMemoryLimit = limits.JobMemoryLimit = cap
    if not K.SetInformationJobObject(job, 9, ctypes.byref(limits), ctypes.sizeof(limits)):
        K.CloseHandle(job); raise ctypes.WinError(ctypes.get_last_error())
    start = time.monotonic(); peak = 0; seen = {}; samples = 0; process = None
    captured = {}; previous_pointer_state = None; stop = None
    try:
        with stdout.open('wb') as out, stderr.open('wb') as err:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdout=out, stderr=err,
                                       creationflags=0x08000000 | 0x00000004)
            row.update(attempted=True, root_pid=process.pid, created_suspended=True)
            if not K.AssignProcessToJobObject(job, W.HANDLE(int(process._handle))):
                process.kill(); process.wait(); raise OSError('Suspended own-root job assignment failed')
            row['assigned_to_own_job_before_resume'] = True
            status = int(N.NtResumeProcess(W.HANDLE(int(process._handle))))
            row['NtResumeProcess_status'] = status
            if status < 0: raise OSError('NtResumeProcess failed: ' + hex(status & 0xffffffff))
            row['resumed_after_own_job_assignment'] = True
            while True:
                current = counters()
                row['minimum_counters'] = {k: min(row['minimum_counters'][k], v) for k, v in current.items()}
                registry = processes(); measurements = []
                for pid in own_tree(process.pid, registry):
                    info = memory(pid)
                    if info:
                        measurements.append(info)
                        entry = seen.setdefault(str(pid), {'exe': registry.get(pid, {}).get('exe', ''),
                                    'peak_private_bytes': 0, 'peak_rss_bytes': 0})
                        entry['peak_private_bytes'] = max(entry['peak_private_bytes'], info['private_bytes'])
                        entry['peak_rss_bytes'] = max(entry['peak_rss_bytes'], info['peak_rss_bytes'])
                private = sum(m['private_bytes'] for m in measurements); peak = max(peak, private); samples += 1
                if native_images and process.poll() is None:
                    try:
                        images = loaded_images(process.pid)
                        for image in images:
                            key = Path(image['path']).name.lower()
                            if key not in expected: continue
                            wanted = expected[key]
                            assert Path(image['path']).resolve() == Path(wanted['file']).resolve(), 'Unexpected same-name native image'
                            if key not in captured:
                                actual_hash = image_file_hash(image)
                                assert actual_hash == wanted['sha256'], 'Loaded image file differs from actual PE audit'
                                captured[key] = image
                                row['loaded_native_images'].append({**image, 'sha256': actual_hash,
                                     'observed_utc': stamp(), 'seconds_after_resume': round(time.monotonic()-start, 4)})
                            if key == 'luke_mathlib_count_native.dll':
                                slots = exact_cache_slots(process.pid, image, wanted['exports'])
                                state = tuple(s['pointer_value'] for s in slots)
                                if state != previous_pointer_state:
                                    row['cache_pointer_observations'].append({'observed_utc': stamp(),
                                        'seconds_after_resume': round(time.monotonic()-start, 4), 'slots': slots,
                                        'all_three_slots_non_null': all(not s['is_null'] for s in slots),
                                        'source_initializer_incomplete_inference': any(s['is_null'] for s in slots)})
                                    previous_pointer_state = state
                    except (OSError, AssertionError) as error:
                        message = str(error)
                        if message not in row['image_observation_errors']:
                            row['image_observation_errors'].append(message)
                if current['disk_free_bytes'] < 1_000_000_000: stop = 'ENVIRONMENT_BLOCKED_DISK_RESERVE'
                elif current['physical_available_bytes'] < 3*GIB: stop = 'ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE'
                elif current['available_commit_bytes'] < GIB: stop = 'ENVIRONMENT_BLOCKED_AVAILABLE_COMMIT_RESERVE'
                elif private > cap: stop = 'ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT'
                elif time.monotonic()-start > timeout: stop = 'OPERATIONAL_TIMEOUT'
                if stop:
                    K.TerminateJobObject(job, 77); process.wait(timeout=15); break
                if process.poll() is not None: break
                time.sleep(.25)
            process.wait(timeout=15); row['exit'] = process.returncode
            measured = EXTENDEDLIMIT()
            if not K.QueryInformationJobObject(job, 9, ctypes.byref(measured), ctypes.sizeof(measured), None):
                raise ctypes.WinError(ctypes.get_last_error())
            row['job_peak_process_private_bytes'] = int(measured.PeakProcessMemoryUsed)
            row['job_peak_aggregate_private_bytes'] = int(measured.PeakJobMemoryUsed)
            diagnostics=stdout.read_text(encoding='utf8',errors='replace')+stderr.read_text(encoding='utf8',errors='replace')
            if not stop and process.returncode!=0 and any(t in diagnostics.lower() for t in ['failed to allocate','out of memory','bad_alloc']):
                stop='ENVIRONMENT_BLOCKED_OWN_ALLOCATION_FAILURE'
            row['state'] = stop or ('PASS' if process.returncode == 0 else 'SOURCE_OR_RUNTIME_FAILED')
    except Exception as error:
        K.TerminateJobObject(job, 78)
        if process is not None: process.wait(timeout=15)
        row.update(state='OPERATIONAL_ERROR', error=str(error))
    finally:
        K.CloseHandle(job)
    row.update(finished_utc=stamp(), seconds=round(time.monotonic()-start, 3),
               polled_peak_tree_private_bytes=peak, observed_own_processes=seen, counter_samples=samples,
               stdout_file=str(stdout), stderr_file=str(stderr), stdout_sha256=sha(stdout), stderr_sha256=sha(stderr),
               stdout=stdout.read_text(encoding='utf8', errors='replace'),
               stderr=stderr.read_text(encoding='utf8', errors='replace'))
    if native_images:
        row['all_expected_native_images_observed'] = set(captured) == set(expected)
        row['pre_import_observation'] = ('INFERRED_FROM_UNFINISHED_SYNCHRONOUS_PLUGIN_INITIALIZER'
            if any(o['source_initializer_incomplete_inference'] for o in row['cache_pointer_observations'])
            else 'NOT_OBSERVED_NO_PRE_IMPORT_TIMING_CLAIM')
        row['initialization_completion_evidence'] = ('ALL_THREE_EXACT_DATA_SLOTS_OBSERVED_NON_NULL'
            if any(o['all_three_slots_non_null'] for o in row['cache_pointer_observations']) else 'NOT_OBSERVED')
        row['native_selection_evidence_notice'] = ('Selection is a deterministic inference from actual PE exports/imports, '
            'loaded image identities, exact pinned default-package mangling/native preference, and successful unchanged source execution. '
            'These observations are not a function-call trace and do not dereference Lean heap objects.')
    return row
