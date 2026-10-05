"""Read-only Windows physical and owned-process private-memory counters."""
import ctypes
class MemoryStatus(ctypes.Structure):
    _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong),('total_physical',ctypes.c_ulonglong),
     ('free_physical',ctypes.c_ulonglong),('total_commit_limit',ctypes.c_ulonglong),
     ('available_commit',ctypes.c_ulonglong),('total_virtual',ctypes.c_ulonglong),
     ('available_virtual',ctypes.c_ulonglong),('available_extended_virtual',ctypes.c_ulonglong)]
class ProcessMemory(ctypes.Structure):
    _fields_=[('cb',ctypes.c_ulong),('page_faults',ctypes.c_ulong),
     ('peak_working_set',ctypes.c_size_t),('working_set',ctypes.c_size_t),
     ('peak_paged_quota',ctypes.c_size_t),('paged_quota',ctypes.c_size_t),
     ('peak_nonpaged_quota',ctypes.c_size_t),('nonpaged_quota',ctypes.c_size_t),
     ('pagefile_usage',ctypes.c_size_t),('peak_pagefile_usage',ctypes.c_size_t),('private_bytes',ctypes.c_size_t)]
k=ctypes.WinDLL('kernel32',use_last_error=True)
k.GlobalMemoryStatusEx.argtypes=[ctypes.POINTER(MemoryStatus)];k.GlobalMemoryStatusEx.restype=ctypes.c_int
p=ctypes.WinDLL('psapi',use_last_error=True)
p.GetProcessMemoryInfo.argtypes=[ctypes.c_void_p,ctypes.POINTER(ProcessMemory),ctypes.c_ulong]
p.GetProcessMemoryInfo.restype=ctypes.c_int
def snapshot(handle=None):
    memory=MemoryStatus();memory.length=ctypes.sizeof(memory)
    if not k.GlobalMemoryStatusEx(ctypes.byref(memory)):raise OSError(ctypes.get_last_error(),'GlobalMemoryStatusEx')
    result={'free_physical_bytes':memory.free_physical,'total_physical_bytes':memory.total_physical,
     'available_commit_bytes':memory.available_commit,'total_commit_limit_bytes':memory.total_commit_limit}
    if handle is not None:
        counters=ProcessMemory();counters.cb=ctypes.sizeof(counters)
        if not p.GetProcessMemoryInfo(ctypes.c_void_p(int(handle)),ctypes.byref(counters),counters.cb):
            raise OSError(ctypes.get_last_error(),'GetProcessMemoryInfo for owned process')
        result.update({'private_bytes':counters.private_bytes,'working_set_bytes':counters.working_set})
    return result
