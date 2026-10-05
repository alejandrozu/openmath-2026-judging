"""Read-only image and exact cache-slot snapshots of an owned Lean process.

Importing this helper starts no process and loads no proof/native adapter DLL.
It does not read or interpret Lean heap objects, and invokes no entrant function.
"""
from pathlib import Path
import ctypes, hashlib, time
from ctypes import wintypes as W
from native_resource_guard import K


class MODULEENTRY32W(ctypes.Structure):
    _fields_ = [('dwSize', W.DWORD), ('th32ModuleID', W.DWORD),
                ('th32ProcessID', W.DWORD), ('GlblcntUsage', W.DWORD),
                ('ProccntUsage', W.DWORD), ('modBaseAddr', ctypes.c_void_p),
                ('modBaseSize', W.DWORD), ('hModule', W.HMODULE),
                ('szModule', W.WCHAR * 256), ('szExePath', W.WCHAR * 260)]


K.Module32FirstW.argtypes = [W.HANDLE, ctypes.POINTER(MODULEENTRY32W)]
K.Module32FirstW.restype = W.BOOL
K.Module32NextW.argtypes = K.Module32FirstW.argtypes
K.Module32NextW.restype = W.BOOL
K.ReadProcessMemory.argtypes = [W.HANDLE, ctypes.c_void_p, ctypes.c_void_p,
                              ctypes.c_size_t, ctypes.POINTER(ctypes.c_size_t)]
K.ReadProcessMemory.restype = W.BOOL


def loaded_images(pid):
    """Use ToolHelp metadata only; transient ERROR_BAD_LENGTH is retried."""
    handle = None
    for _ in range(8):
        ctypes.set_last_error(0)
        handle = K.CreateToolhelp32Snapshot(8 | 16, pid)
        if handle != ctypes.c_void_p(-1).value:
            break
        if ctypes.get_last_error() != 24:
            raise ctypes.WinError(ctypes.get_last_error())
        time.sleep(.01)
    if handle == ctypes.c_void_p(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        entry = MODULEENTRY32W(); entry.dwSize = ctypes.sizeof(entry)
        rows = []
        ok = K.Module32FirstW(handle, ctypes.byref(entry))
        while ok:
            rows.append({'path': entry.szExePath, 'module': entry.szModule,
                         'base_address': int(entry.modBaseAddr or 0),
                         'mapped_image_bytes': int(entry.modBaseSize)})
            ok = K.Module32NextW(handle, ctypes.byref(entry))
        return rows
    finally:
        K.CloseHandle(handle)


def exact_cache_slots(pid, image, exports):
    """Read three exported pointer slots, never follow or modify the pointers."""
    handle = K.OpenProcess(0x0400 | 0x0010, False, pid)
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())
    rows = []
    try:
        for name in ['bCache', 'dCache', 'pathsCache']:
            symbol = 'l_K4Ramsey_Final3840_Count_' + name
            info = exports[symbol]
            assert not info['executable'] and info['writable']
            address = image['base_address'] + int(info['rva'])
            buffer = ctypes.create_string_buffer(8); count = ctypes.c_size_t()
            ok = K.ReadProcessMemory(handle, ctypes.c_void_p(address), buffer,
                                     8, ctypes.byref(count))
            if not ok or count.value != 8:
                raise ctypes.WinError(ctypes.get_last_error())
            pointer = int.from_bytes(buffer.raw, 'little')
            rows.append({'cache': name, 'symbol': symbol, 'slot_address': address,
                         'pointer_value': pointer, 'is_null': pointer == 0,
                         'read_bytes': int(count.value),
                         'representation': 'Exact exported 64-bit lean_object* data slot; pointer is not dereferenced.'})
        return rows
    finally:
        K.CloseHandle(handle)


def image_file_hash(image):
    p = Path(image['path'])
    return hashlib.sha256(p.read_bytes()).hexdigest()
