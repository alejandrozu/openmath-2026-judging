"""Native filesystem metadata only for file storage; no compression or file copy."""
from pathlib import Path
from collections import defaultdict
from datetime import datetime,timezone
from ctypes import wintypes
import ctypes,hashlib,json,os,re,shutil,subprocess
from receipt_io import read_bytes_shared

BASE=Path(__file__).resolve().parent;BUILDS=(BASE/'builds').resolve()
def sha_bytes(raw):return hashlib.sha256(raw).hexdigest()
K=ctypes.WinDLL('kernel32',use_last_error=True)
class FT(ctypes.Structure):_fields_=[('low',wintypes.DWORD),('high',wintypes.DWORD)]
class FI(ctypes.Structure):
    _fields_=[('attributes',wintypes.DWORD),('creation',FT),('access',FT),('write',FT),('volume_serial',wintypes.DWORD),('size_high',wintypes.DWORD),('size_low',wintypes.DWORD),('link_count',wintypes.DWORD),('index_high',wintypes.DWORD),('index_low',wintypes.DWORD)]
class SI(ctypes.Structure):
    _fields_=[('allocation_size',ctypes.c_longlong),('end_of_file',ctypes.c_longlong),('number_of_links',wintypes.DWORD),('delete_pending',ctypes.c_ubyte),('directory',ctypes.c_ubyte)]
class CI(ctypes.Structure):
    _fields_=[('compressed_file_size',ctypes.c_longlong),('compression_format',wintypes.WORD),('compression_unit_shift',ctypes.c_ubyte),('chunk_shift',ctypes.c_ubyte),('cluster_shift',ctypes.c_ubyte),('reserved',ctypes.c_ubyte*3)]
K.CreateFileW.argtypes=[wintypes.LPCWSTR,wintypes.DWORD,wintypes.DWORD,ctypes.c_void_p,wintypes.DWORD,wintypes.DWORD,wintypes.HANDLE];K.CreateFileW.restype=wintypes.HANDLE
K.CloseHandle.argtypes=[wintypes.HANDLE];K.CloseHandle.restype=wintypes.BOOL
K.GetFileInformationByHandle.argtypes=[wintypes.HANDLE,ctypes.POINTER(FI)];K.GetFileInformationByHandle.restype=wintypes.BOOL
K.GetFileInformationByHandleEx.argtypes=[wintypes.HANDLE,ctypes.c_int,ctypes.c_void_p,wintypes.DWORD];K.GetFileInformationByHandleEx.restype=wintypes.BOOL
K.GetCompressedFileSizeW.argtypes=[wintypes.LPCWSTR,ctypes.POINTER(wintypes.DWORD)];K.GetCompressedFileSizeW.restype=wintypes.DWORD
K.GetVolumePathNameW.argtypes=[wintypes.LPCWSTR,wintypes.LPWSTR,wintypes.DWORD];K.GetVolumePathNameW.restype=wintypes.BOOL
K.GetVolumeInformationW.argtypes=[wintypes.LPCWSTR,wintypes.LPWSTR,wintypes.DWORD,ctypes.POINTER(wintypes.DWORD),ctypes.POINTER(wintypes.DWORD),ctypes.POINTER(wintypes.DWORD),wintypes.LPWSTR,wintypes.DWORD];K.GetVolumeInformationW.restype=wintypes.BOOL
def native_metadata(path):
    p=Path(path).resolve();h=K.CreateFileW(str(p),0x80,7,None,3,0,None)
    if h==ctypes.c_void_p(-1).value:raise ctypes.WinError(ctypes.get_last_error())
    info=FI();standard=SI();compression=CI()
    try:
        if not K.GetFileInformationByHandle(h,ctypes.byref(info)):raise ctypes.WinError(ctypes.get_last_error())
        standard_ok=bool(K.GetFileInformationByHandleEx(h,1,ctypes.byref(standard),ctypes.sizeof(standard)))
        compression_ok=bool(K.GetFileInformationByHandleEx(h,8,ctypes.byref(compression),ctypes.sizeof(compression)))
        hi=wintypes.DWORD();ctypes.set_last_error(0);lo=K.GetCompressedFileSizeW(str(p),ctypes.byref(hi))
        if lo==0xffffffff and ctypes.get_last_error():raise ctypes.WinError(ctypes.get_last_error())
        return {'file':str(p),'logical_bytes':(info.size_high<<32)|info.size_low,'stored_bytes_GetCompressedFileSizeW':(hi.value<<32)|lo,'standard_allocation_bytes':standard.allocation_size if standard_ok else None,'compression_info_stored_bytes':compression.compressed_file_size if compression_ok else None,'compression_format':compression.compression_format if compression_ok else None,'volume_serial':int(info.volume_serial),'file_index_high':int(info.index_high),'file_index_low':int(info.index_low),'link_count':int(info.link_count),'attributes':int(info.attributes),'FILE_ATTRIBUTE_COMPRESSED':bool(info.attributes&0x800),'FILE_ATTRIBUTE_REPARSE_POINT':bool(info.attributes&0x400),'FILE_ATTRIBUTE_ENCRYPTED':bool(info.attributes&0x4000),'last_write_FILETIME':(info.write.high<<32)|info.write.low}
    finally:K.CloseHandle(h)
def process_snapshot():
    cmd="Get-CimInstance Win32_Process -Filter \"Name = 'lean.exe' OR Name = 'python.exe'\" | Where-Object { $_.Name -eq 'lean.exe' -or ($_.CommandLine -like '*loo*verification*' -and $_.CommandLine -match '(run_|dispatch_)') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine | ConvertTo-Json -Compress"
    r=subprocess.run(['powershell','-NoProfile','-Command',cmd],capture_output=True,text=True,encoding='utf-8',errors='replace',check=True)
    d=json.loads(r.stdout or '[]');return d if isinstance(d,list) else [d]
before_processes=process_snapshot()
root=ctypes.create_unicode_buffer(32768);assert K.GetVolumePathNameW(str(BASE),root,len(root))
serial=wintypes.DWORD();maximum=wintypes.DWORD();flags=wintypes.DWORD();fs=ctypes.create_unicode_buffer(64)
assert K.GetVolumeInformationW(root.value,None,0,ctypes.byref(serial),ctypes.byref(maximum),ctypes.byref(flags),fs,len(fs))
volume={'root':root.value,'filesystem':fs.value,'serial':serial.value,'flags':flags.value,'supports_file_compression':bool(flags.value&0x10),'supports_hard_links':bool(flags.value&0x400000),'supports_reparse_points':bool(flags.value&0x80)}
assert volume['filesystem']=='NTFS'
refs={};receipt_records=[];excluded_live=[];anomalies=[]
for rp in sorted(BASE.glob('*-fresh-build.json')):
    raw=read_bytes_shared(rp);d=json.loads(raw);status=d.get('status','')
    if status in ('RUNNING','WAITING_THIRD_WORKER_DISPATCH_GATES') or d.get('current_module'):
        excluded_live.append({'receipt':str(rp),'receipt_sha256':sha_bytes(raw),'status':status,'current_module':d.get('current_module')});continue
    if not d.get('finished_utc'):continue
    project=d.get('id',rp.name.removesuffix('-fresh-build.json'))
    # A source receipt may have partial historical failures; only actual completed outputs enter.
    rows=[x for x in d.get('builds',[]) if x.get('exit')==0 and not x.get('stop_reason') and not x.get('disk_reserve_stopped')]
    owned=[]
    for row in rows:
        for a in row.get('artifacts',[]):
            p=Path(a['file']).resolve()
            if not p.is_relative_to(BUILDS) or p.suffix not in ['.olean','.private','.server','.ir','.ilean']:
                anomalies.append({'file':str(p),'reason':'Not an explicitly recorded own Lean output inside builds'});continue
            if not p.is_file():anomalies.append({'file':str(p),'reason':'Recorded output missing'});continue
            owned.append(str(p));refs.setdefault(str(p),{'expected_content_sha256':a['sha256'],'expected_logical_bytes':a['bytes'],'provenance':[]})['provenance'].append({'project':project,'receipt':str(rp),'receipt_sha256':sha_bytes(raw),'module':row['module'],'actual_compiler_exit':0})
    receipt_records.append({'file':str(rp),'sha256':sha_bytes(raw),'status':status,'owned_completed_output_paths':len(owned)})
    if read_bytes_shared(rp)!=raw:
        for path in owned:refs.pop(path,None)
        excluded_live.append({'receipt':str(rp),'reason':'Receipt changed while reading; all its proposed outputs excluded'})

# Completed custom Luke Lean outputs; derive only exact paths from its completed recorded inventory.
lp=BASE/'luke-k4-ramsey-current-native-fresh-build.json'
if lp.exists():
    raw=read_bytes_shared(lp);d=json.loads(raw)
    if d.get('finished_utc') and d.get('status')=='PASS_WITH_NATIVE_EVALUATION':
        lib=BUILDS/'luke-k4-ramsey-current-native/.lake/build/lib/lean'
        for rel,a in d['fresh_custom_artifact_inventory'].items():
            p=(lib/rel).resolve();assert p.is_relative_to(lib.resolve())
            if p.is_file():refs.setdefault(str(p),{'expected_content_sha256':a['sha256'],'expected_logical_bytes':a['bytes'],'provenance':[]})['provenance'].append({'project':'luke-k4-ramsey-current-native','receipt':str(lp),'receipt_sha256':sha_bytes(raw),'module':rel,'actual_compiler_exit':0})
        receipt_records.append({'file':str(lp),'sha256':sha_bytes(raw),'status':d['status'],'ownership_scope':'Completed custom Lean artifact inventory only; generated official dependency objects excluded'})

files=[];excluded_identity=[]
for p,ref in refs.items():
    info=native_metadata(p)
    if info['logical_bytes']!=ref['expected_logical_bytes']:
        anomalies.append({'file':p,'reason':'Logical size differs from completed owned receipt'});continue
    row={**info,**ref}
    reasons=[]
    if info['link_count']!=1:reasons.append('Shared NTFS inode; held DMS/M2/v2 linkcount contracts and all aliases require separate review')
    if info['FILE_ATTRIBUTE_REPARSE_POINT']:reasons.append('Existing reparse/WOF or other backing; no ordinary compression proposal without exact backing review')
    if info['FILE_ATTRIBUTE_ENCRYPTED']:reasons.append('Encrypted file')
    if reasons:row['excluded_reason']=reasons;excluded_identity.append(row)
    else:files.append(row)

# Metadata-only archival/planning inventory. Submitted sources, original ZIPs, runtime and dependencies are never targets.
metadata_paths=[]
for folder in ['m2_runner_source_archives','runner_source_archives','native_runner_source_versions']:
    directory=BASE/folder
    if directory.exists():metadata_paths.extend(p for p in directory.rglob('*') if p.is_file() and not p.is_symlink() and p.suffix in ['.py','.diff','.json'])
metadata_paths.extend(p for p in BUILDS.glob('*/build-plan.json') if p.is_file())
archive_metadata=[native_metadata(p) for p in sorted(set(metadata_paths))]

def summarize(rows):
    ids={};logical=stored=standard=0
    for r in rows:
        key=(r['volume_serial'],r['file_index_high'],r['file_index_low'])
        if key in ids:continue
        ids[key]=True;logical+=r['logical_bytes'];stored+=r['stored_bytes_GetCompressedFileSizeW'];standard+=r['standard_allocation_bytes'] or 0
    return {'path_count':len(rows),'unique_inodes':len(ids),'logical_bytes_unique':logical,'stored_bytes_unique_GetCompressedFileSizeW':stored,'standard_allocation_bytes_unique':standard}
groups=defaultdict(list)
for row in files:groups[row['provenance'][0]['project']].append(row)
ranked=sorted([{'project':n,**summarize(rs),'largest_files':[{'file':r['file'],'logical_bytes':r['logical_bytes'],'stored_bytes':r['stored_bytes_GetCompressedFileSizeW'],'compression_format':r['compression_format']} for r in sorted(rs,key=lambda a:a['stored_bytes_GetCompressedFileSizeW'],reverse=True)[:5]]} for n,rs in groups.items()],key=lambda r:r['stored_bytes_unique_GetCompressedFileSizeW'],reverse=True)
summary=summarize(files);before_free=shutil.disk_usage(BASE).free
after_processes=process_snapshot()
out={'status':'READ_ONLY_STORAGE_METADATA_AND_LOSSLESS_COMPRESSION_PROPOSAL_NO_ACTION','created_utc':datetime.now(timezone.utc).isoformat(),'volume':volume,'current_free_disk_bytes':before_free,'process_snapshot_before':before_processes,'process_snapshot_after':after_processes,'active_or_unstable_receipt_scopes_excluded':excluded_live,'receipt_ownership_bindings':receipt_records,'eligible_completed_single_link_non_reparse_own_outputs':summary,'top_project_candidates':ranked,'exact_proposed_owned_output_files':files,'shared_or_special_inodes_excluded':excluded_identity,'shared_or_special_excluded_storage':summarize(excluded_identity),'generated_runner_archives_and_frozen_plan_metadata_only':{'summary':summarize(archive_metadata),'files':archive_metadata,'proposal_role':'Optional separate tiny metadata tier; no authored Lean sources or submitted archives included'},'observed_metadata_anomalies':anomalies,'potential_savings_bounds':{'guaranteed_lower_bound_bytes':0,'absolute_upper_bound_bytes':summary['stored_bytes_unique_GetCompressedFileSizeW'],'upper_bound_qualification':'Cannot save more than current stored data bytes; this is an intentionally loose upper bound, not a prediction. Existing compressed sizes are measured; no uncompressed-size estimate is counted as additional gain.','additional_25_percent_stored_reduction_scenario_bytes':summary['stored_bytes_unique_GetCompressedFileSizeW']//4,'additional_50_percent_stored_reduction_scenario_bytes':summary['stored_bytes_unique_GetCompressedFileSizeW']//2,'scenarios_are_not_measured_outcomes_or_guarantees':True},'proposed_future_operation_contract':{'root_review_and_exact_target_list_required':True,'operation':'A serialized, reversible NTFS in-place compression pass on only root-selected completed own artifact files; an actual small lossless pilot must measure additional savings before broad dispatch. No operation is executed or presupposed by this packet.','quiescence':'Recheck project receipts, current compiler/dispatcher/loader ownership and target aliases immediately before dispatch. Do not run alongside any source compilation/native loader reading these files; active project scopes excluded wholesale.','identity':'Before and after each future file, verify source/receipt provenance, logical SHA256, volume serial, NTFS file index and hardlink count. Reject any unexpected alias/size/content change; all shared DMS/v2/M2 inodes excluded from this first tier.','path_safety':'Exact resolved paths inside verification/builds only; no recursive wildcard command, no scientific sources, original submission archives, dependencies, runtimes, user applications or caches.','resources':'Single compressor, continuous disk/resource reserve; bounded pilot and allocated-growth measurements. Stop without deleting/copying or overwriting other files.','reversal':'If needed, decompress the same exact selected file paths once sufficient disk reserve is available; preserve logical SHA, file identity and link count.','risks':['Additional savings may be small for already compressed certificate data.','Compression/decompression may temporarily require allocation and CPU; do not infer the4GB gate is protected by logical size alone.','Read latency could slow later imported artifacts; source-compilation and DLL-loading quiescence must be checked at dispatch.','Shared inodes and existing reparse/WOF backing can affect multiple aliases or existing compression policies; excluded pending a separate root-reviewed identity contract.','Decompression needs free capacity and should not be used merely to validate hashes.']},'methodology':'File content was not rehashed for storage measurement. Expected logical SHA values are preserved from actual cold-compiler receipts; native file size, allocation, compression format, volume/file ID and linkcount measured now. GetCompressedFileSizeW stored bytes and FileStandardInfo allocation are both recorded because their accounting can differ. All future content validation is required before mutation.','compress_delete_copy_install_or_compiler_execute_performed':False,'existing_source_output_plan_receipt_or_PDF_modified':False}
dest=BASE/'completed-own-artifact-storage-compression-proposal-20261005.json'
with dest.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'packet':str(dest),'sha256':sha_bytes(dest.read_bytes()),'free_disk_bytes':before_free,'eligible':summary,'top_projects':[{'project':r['project'],'logical':r['logical_bytes_unique'],'stored':r['stored_bytes_unique_GetCompressedFileSizeW']} for r in ranked[:8]],'shared_excluded':summarize(excluded_identity),'metadata_archives':summarize(archive_metadata),'metadata_anomalies':len(anomalies)}))
