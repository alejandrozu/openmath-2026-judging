"""Read-only exact A00076 own-output NTFS/storage assessment.

Only new metadata is written. No compression, copy, deletion, Lean, or source /
runtime / provider / existing output / receipt mutation is performed.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
from ctypes import wintypes as W
import ctypes, hashlib, json, mmap, os, shutil, subprocess, time

BASE = Path(__file__).resolve().parent
STAGE = (BASE/'builds/sakana-a000224').resolve()
RECEIPT_SHA = 'd8226e2920788365d04ccd7c4a1cab829c5c0c192b4fa155aa4e4e4b11e3a552'
PLAN_SHA = '0f6338f72ff570e79847995bac7cf6f6c56c8a1c2cc8dedf55181bc764180fe7'
META = BASE/'assess_completed_own_artifact_storage_readonly.py'

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def identity(p):
    p=Path(p).resolve()
    return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}

prefix,marker,_=META.read_text(encoding='utf8').partition('before_processes=process_snapshot()')
assert marker and 'def native_metadata(path):' in prefix
ns={'__file__':str(META),'__name__':'readonly_native_metadata_definitions_only'}
exec(compile(prefix,str(META),'exec'),ns)
native=ns['native_metadata'];K=ns['K']

def process_inventory():
    cmd="Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake|leantar|compact|python|clang|lld|7z|tar)\\.exe$' } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Compress"
    p=subprocess.run(['powershell','-NoProfile','-Command',cmd],capture_output=True,text=True,encoding='utf8',errors='replace',check=True)
    rows=json.loads(p.stdout or '[]');rows=[rows] if isinstance(rows,dict) else rows
    blocked=[]
    for r in rows:
        if r['ProcessId']==os.getpid():continue
        cli=(r.get('CommandLine') or '').lower()
        if any(t in cli for t in ('sakana-a000224','quadraticresidue224','a000224-original76','dispatch_main_source_queue')):
            blocked.append(r)
    assert not blocked,('A000 reader/writer/dispatcher is active; readonly assessment waits for its actual quiescent boundary',blocked)
    return rows

def wof_info(p):
    dll=ctypes.WinDLL('Wofutil.dll');fn=dll.WofIsExternalFile
    fn.argtypes=[W.LPCWSTR,ctypes.POINTER(W.BOOL),ctypes.POINTER(W.ULONG),ctypes.c_void_p,ctypes.POINTER(W.ULONG)]
    fn.restype=ctypes.c_long
    external=W.BOOL();provider=W.ULONG();buf=ctypes.create_string_buffer(64);length=W.ULONG(64)
    result=fn(str(p),ctypes.byref(external),ctypes.byref(provider),buf,ctypes.byref(length))
    assert result==0 and length.value<=64
    return {'HRESULT':result,'external':bool(external.value),'provider':provider.value,
        'info_length':length.value,'info_hex':buf.raw[:length.value].hex(),
        'algorithm':int.from_bytes(buf.raw[:4],'little') if external.value and provider.value==2 else None}

started=time.time()
process_before=process_inventory()
rp=BASE/'sakana-a000224-original76-storage-checkpoint-receipt-20261005.json'
cp=BASE/'sakana-a000224-fresh-build.json'
pp=STAGE/'build-plan.json'
bp=BASE/'a000224-natural76-storage-boundary-summary-20261005.json'
assert sha(rp)==sha(cp)==RECEIPT_SHA and sha(pp)==PLAN_SHA
d=json.loads(rp.read_bytes());plan=json.loads(pp.read_bytes());boundary=json.loads(bp.read_bytes())
assert boundary['actual_source_PASS']==76 and boundary['canonical_receipt_sha256']==RECEIPT_SHA
assert d['status']=='SCHEDULED_RESOURCE_CHECKPOINT' and d.get('current_module') is None
release=BASE/'root-own-A000-hold-release-Groth-continuation-20261005.json'
release_doc=json.loads(release.read_bytes())
assert release_doc['status']=='OWN_A000_BOUNDARY_HOLD_RELEASED_FOR_ROOT_GROTH_ONLY'
assert release_doc['A000_remains_quiescent_no_dispatcher_restarted'] is True
assert release_doc['A000_actual76_receipt_sha256']==RECEIPT_SHA
rows=[r for r in d['builds'] if r.get('exit')==0 and not r.get('stop_reason') and not r.get('is_endpoint_audit')]
assert len(rows)==len({r['module'] for r in rows})==76
source_map={r['module']:r for r in plan['modules']}
assert len(source_map)==171
bindings={'immutable_original76_receipt':identity(rp),'current_original_receipt':identity(cp),
    'frozen_source_plan':identity(pp),'completed_boundary':identity(bp),
    'native_metadata_definition_helper':identity(META),'root_dated_global_hold_release_A000_still_quiescent':identity(release),
    'current_runtime_installation_receipt':identity(BASE/'lean-4.34.1-installation.json'),
    'current_runtime_compiler':identity(BASE/'runtimes/lean-4.34.1-windows/bin/lean.exe'),
    'official_installed_cache_PASS_receipt':identity(BASE/'mathlib-4.34.1-cache-retry.json')}
assert json.loads((BASE/'lean-4.34.1-installation.json').read_bytes())['complete'] is True
cache=json.loads((BASE/'mathlib-4.34.1-cache-retry.json').read_bytes())
assert cache['status']=='PASS'
sources=[]
for m in plan['modules']:
    p=Path(m['file']).resolve();assert p.is_relative_to(STAGE) and p.suffix=='.lean'
    assert sha(p)==m['sha256']
    sources.append({'module':m['module'],'file':str(p),'sha256':m['sha256'],'bytes':p.stat().st_size})
outputs=[];seen=set()
for i,r in enumerate(rows):
    assert r['module'] in source_map
    assert not r.get('disk_reserve_stopped')
    for a in r['artifacts']:
        p=Path(a['file']).resolve();assert p.is_relative_to(STAGE) and not p.is_symlink()
        assert p.suffix in {'.olean','.ilean','.ir','.private','.server'}
        assert str(p) not in seen;seen.add(str(p))
        before=native(p);assert before['logical_bytes']==a['bytes']
        assert before['link_count']==1 and not before['FILE_ATTRIBUTE_ENCRYPTED']
        wof=wof_info(p)
        ordinary=sha(p)
        with p.open('rb') as f:
            with mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as mm:mapped=hashlib.sha256(mm).hexdigest()
        assert ordinary==mapped==a['sha256']
        after=native(p);assert before==after
        outputs.append({**before,'content_sha256':ordinary,'Windows_readonly_mmap_sha256':mapped,
            'ordinary_read_equals_readonly_mmap':True,'native_before_after_identity_unchanged':True,
            'WOF':wof,'source_module':r['module'],'source_sha256':source_map[r['module']]['sha256'],
            'actual_source_row_exit':r['exit'],'actual_source_row_seconds':r.get('seconds'),
            'artifact_provenance':r.get('artifact_hash_provenance'),
            'completed_own_receipt_sha256':RECEIPT_SHA,
            'future_storage_eligibility':'single-link ordinary compressed/non-reparse own output' if not wof['external'] and not before['FILE_ATTRIBUTE_REPARSE_POINT'] else 'requires exact existing WOF/reparse review; no new ordinary compression proposed'})
    if (i+1)%16==0:print(json.dumps({'readonly_completed_rows':i+1,'of':76,'outputs_hashed':len(outputs)}),flush=True)
process_after=process_inventory()
assert sha(rp)==sha(cp)==RECEIPT_SHA and sha(pp)==PLAN_SHA
assert sha(bp)==bindings['completed_boundary']['sha256']
for label,b in bindings.items():assert sha(b['file'])==b['sha256'],label
summary={'receipt_matched_source_pass_rows':76,'total_source_scope':171,'selected_audits_actually_complete':0,
    'distinct_output_paths':len(outputs),'distinct_native_inodes':len({(x['volume_serial'],x['file_index_high'],x['file_index_low']) for x in outputs}),
    'logical_bytes':sum(x['logical_bytes'] for x in outputs),
    'stored_bytes_GetCompressedFileSizeW':sum(x['stored_bytes_GetCompressedFileSizeW'] for x in outputs),
    'standard_allocation_bytes':sum(x['standard_allocation_bytes'] or 0 for x in outputs),
    'ordinary_NTFS_compressed_files':sum(x['FILE_ATTRIBUTE_COMPRESSED'] for x in outputs),
    'WOF_external_files':sum(x['WOF']['external'] for x in outputs),
    'artifact_type_counts':dict(Counter(Path(x['file']).suffix for x in outputs))}
out={'status':'READ_ONLY_A000_ORIGINAL76_QUIESCENT_OWN_OUTPUT_IDENTITIES_WOF_MMAP_STORAGE_ASSESSMENT_NO_ACTION',
    'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
    'elapsed_seconds':round(time.time()-started,3),'frozen_bindings':bindings,
    'immutable_source_identities':sources,'exact_owned_receipt_matched_outputs':outputs,
    'summary':summary,'largest_completed_own_output_candidates':sorted(outputs,key=lambda x:x['standard_allocation_bytes'] or 0,reverse=True)[:12],
    'processes_before':process_before,'processes_after':process_after,'actual_free_disk_bytes':shutil.disk_usage(BASE).free,
    'potential_additional_LZX_savings':{'guaranteed_bytes':0,'loose_upper_bound_bytes':summary['standard_allocation_bytes'],
        'qualification':'Current allocation is measured. No additional LZX reduction is measured; root BooleanTree storage-only pilot does not supply a proven ratio for these A000 certificates.'},
    'future_contract':'Only exact root-approved completed own single-link paths after renewed actual A000 dispatcher/loader quiescence; preserve logical SHA, inode, linkcount, mtime, sources/runtime/providers/receipts. A bounded actual pilot must recheck before/after WOF + ordinary/mmap equality and resource reserves. No recursive or directory-wide target.',
    'explicit_exclusions':['all submitted scientific/source archives','all authored .lean source files','all DMS outputs/aliases','all actual runtimes/official source/provider dependencies','all live or unrecorded outputs','all user/system/application files'],
    'existing_source_output_runtime_provider_receipt_PDF_mutations':0,'compiler_compression_deletion_copy_install_invocations':0,
    'full_source_theorem_endpoint_novelty_or_score_completion_inferred':False}
dest=BASE/'a000-original76-quiescent-owned-output-storage-proposal-20261005.json'
with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'packet':str(dest),'sha256':sha(dest),'summary':summary,'actions':0},indent=2))
