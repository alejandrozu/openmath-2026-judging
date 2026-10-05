"""Pinned Win32 resource counter and own-job helpers; importing this module invokes no compiler."""
from pathlib import Path
import argparse,ctypes,datetime,hashlib,json,os,shutil,subprocess,time
from ctypes import wintypes as W

BASE=Path(__file__).resolve().parent
RUNTIME=BASE/'runtimes/lean-4.34.1-windows'
GIB=2**30
K=ctypes.WinDLL('kernel32',use_last_error=True)
P=ctypes.WinDLL('psapi',use_last_error=True)

class MEMORYSTATUSEX(ctypes.Structure):
    _fields_=[('dwLength',W.DWORD),('dwMemoryLoad',W.DWORD),*[(n,ctypes.c_ulonglong) for n in
      ['ullTotalPhys','ullAvailPhys','ullTotalPageFile','ullAvailPageFile','ullTotalVirtual','ullAvailVirtual','ullAvailExtendedVirtual']]]
class PMCEX(ctypes.Structure):
    _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD),*[(n,ctypes.c_size_t) for n in
      ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage','PrivateUsage']]]
class PROCESSENTRY32W(ctypes.Structure):
    _fields_=[('dwSize',W.DWORD),('cntUsage',W.DWORD),('th32ProcessID',W.DWORD),
      ('th32DefaultHeapID',ctypes.c_size_t),('th32ModuleID',W.DWORD),('cntThreads',W.DWORD),
      ('th32ParentProcessID',W.DWORD),('pcPriClassBase',W.LONG),('dwFlags',W.DWORD),('szExeFile',W.WCHAR*260)]
class BASICLIMIT(ctypes.Structure):
    _fields_=[('PerProcessUserTimeLimit',ctypes.c_longlong),('PerJobUserTimeLimit',ctypes.c_longlong),
      ('LimitFlags',W.DWORD),('MinimumWorkingSetSize',ctypes.c_size_t),('MaximumWorkingSetSize',ctypes.c_size_t),
      ('ActiveProcessLimit',W.DWORD),('Affinity',ctypes.c_size_t),('PriorityClass',W.DWORD),('SchedulingClass',W.DWORD)]
class IOCOUNTERS(ctypes.Structure):
    _fields_=[(n,ctypes.c_ulonglong) for n in ['ReadOperationCount','WriteOperationCount','OtherOperationCount','ReadTransferCount','WriteTransferCount','OtherTransferCount']]
class EXTENDEDLIMIT(ctypes.Structure):
    _fields_=[('BasicLimitInformation',BASICLIMIT),('IoInfo',IOCOUNTERS),('ProcessMemoryLimit',ctypes.c_size_t),
      ('JobMemoryLimit',ctypes.c_size_t),('PeakProcessMemoryUsed',ctypes.c_size_t),('PeakJobMemoryUsed',ctypes.c_size_t)]

K.GlobalMemoryStatusEx.argtypes=[ctypes.POINTER(MEMORYSTATUSEX)];K.GlobalMemoryStatusEx.restype=W.BOOL
K.OpenProcess.argtypes=[W.DWORD,W.BOOL,W.DWORD];K.OpenProcess.restype=W.HANDLE
K.CloseHandle.argtypes=[W.HANDLE];K.CloseHandle.restype=W.BOOL
P.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMCEX),W.DWORD];P.GetProcessMemoryInfo.restype=W.BOOL
K.CreateToolhelp32Snapshot.argtypes=[W.DWORD,W.DWORD];K.CreateToolhelp32Snapshot.restype=W.HANDLE
K.Process32FirstW.argtypes=[W.HANDLE,ctypes.POINTER(PROCESSENTRY32W)];K.Process32FirstW.restype=W.BOOL
K.Process32NextW.argtypes=K.Process32FirstW.argtypes;K.Process32NextW.restype=W.BOOL
K.CreateJobObjectW.argtypes=[ctypes.c_void_p,W.LPCWSTR];K.CreateJobObjectW.restype=W.HANDLE
K.SetInformationJobObject.argtypes=[W.HANDLE,ctypes.c_int,ctypes.c_void_p,W.DWORD];K.SetInformationJobObject.restype=W.BOOL
K.QueryInformationJobObject.argtypes=[W.HANDLE,ctypes.c_int,ctypes.c_void_p,W.DWORD,ctypes.c_void_p];K.QueryInformationJobObject.restype=W.BOOL
K.AssignProcessToJobObject.argtypes=[W.HANDLE,W.HANDLE];K.AssignProcessToJobObject.restype=W.BOOL
K.TerminateJobObject.argtypes=[W.HANDLE,W.UINT];K.TerminateJobObject.restype=W.BOOL
K.GetCompressedFileSizeW.argtypes=[W.LPCWSTR,ctypes.POINTER(W.DWORD)];K.GetCompressedFileSizeW.restype=W.DWORD

def physical():
    s=MEMORYSTATUSEX();s.dwLength=ctypes.sizeof(s)
    if not K.GlobalMemoryStatusEx(ctypes.byref(s)):raise ctypes.WinError(ctypes.get_last_error())
    return {'available_bytes':int(s.ullAvailPhys),'total_bytes':int(s.ullTotalPhys)}
def memory(pid):
    h=K.OpenProcess(0x0400|0x0010,False,pid)
    if not h:return None
    try:
        s=PMCEX();s.cb=ctypes.sizeof(s)
        if not P.GetProcessMemoryInfo(h,ctypes.byref(s),s.cb):return None
        return {'pid':pid,'private_bytes':int(s.PrivateUsage),'rss_bytes':int(s.WorkingSetSize),'peak_rss_bytes':int(s.PeakWorkingSetSize)}
    finally:K.CloseHandle(h)
def processes():
    h=K.CreateToolhelp32Snapshot(2,0)
    if h==ctypes.c_void_p(-1).value:raise ctypes.WinError(ctypes.get_last_error())
    try:
        e=PROCESSENTRY32W();e.dwSize=ctypes.sizeof(e);rows={}
        ok=K.Process32FirstW(h,ctypes.byref(e))
        while ok:
            rows[int(e.th32ProcessID)]={'parent':int(e.th32ParentProcessID),'exe':e.szExeFile}
            ok=K.Process32NextW(h,ctypes.byref(e))
        return rows
    finally:K.CloseHandle(h)
def own_tree(root,registry):
    result={root}
    while True:
        extra={pid for pid,r in registry.items() if r['parent'] in result}-result
        if not extra:return result
        result.update(extra)
def allocated(p):
    high=W.DWORD();ctypes.set_last_error(0)
    low=K.GetCompressedFileSizeW('\\\\?\\'+str(p.resolve()),ctypes.byref(high))
    if low==0xffffffff and ctypes.get_last_error():raise ctypes.WinError(ctypes.get_last_error())
    return int(low)+(int(high.value)<<32)
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save_once(path,data):
    assert not path.exists(),'Immutable pilot receipt must not be overwritten'
    tmp=path.with_suffix('.json.tmp')
    with tmp.open('w',encoding='utf8') as f:json.dump(data,f,indent=2);f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)

