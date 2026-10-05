"""Read atomic receipts without blocking a Windows writer's file replacement."""
from pathlib import Path
import json, os, time

def read_bytes_shared(path):
    path = Path(path)
    if os.name != 'nt':
        return path.read_bytes()
    import ctypes, msvcrt
    from ctypes import wintypes
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    create = kernel.CreateFileW
    create.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD,
                      wintypes.LPVOID, wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
    create.restype = wintypes.HANDLE
    close = kernel.CloseHandle
    close.argtypes = [wintypes.HANDLE]
    close.restype = wintypes.BOOL
    # GENERIC_READ; share read/write/delete; OPEN_EXISTING; normal attributes.
    handle = create(str(path.resolve()), 0x80000000, 0x7, None, 3, 0x80, None)
    if handle == ctypes.c_void_p(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        descriptor = msvcrt.open_osfhandle(int(handle), os.O_RDONLY | os.O_BINARY)
    except BaseException:
        close(handle)
        raise
    with os.fdopen(descriptor, 'rb') as stream:
        return stream.read()

def read_json_shared(path):
    # Atomic writers expose a complete old or new snapshot. A bounded retry also
    # accommodates the few historical non-atomic receipts during transition.
    for attempt in range(4):
        try:
            return json.loads(read_bytes_shared(path).decode('utf-8-sig'))
        except json.JSONDecodeError:
            if attempt == 3:
                raise
            time.sleep(0.05)
