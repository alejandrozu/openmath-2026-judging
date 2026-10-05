"""Prepare a reviewed hard-link policy; execute only with a separate SHA-bound approval.

No Lean invocation is made. Each linked output is an original owned cold pass,
not a new diagnostic compilation. The source and target share an NTFS file ID.
The diagnostic runner must skip these 99 modules and never overwrite them.
"""
from pathlib import Path
from datetime import datetime, timezone
import ctypes,hashlib,json,os,shutil,subprocess,sys,time
from ctypes import wintypes
from verify_dms_modeq_v2_stage import verify_stage
BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-dms-current-import-pruned-modeq-v2'
ORIGINAL=BASE/'builds/htpeo-dms-current'
POLICY=BASE/'dms-modeq-v2-original99-hardlink-policy-20261005.json'
SEED_RECEIPT=BASE/'dms-modeq-v2-original99-hardlink-seed-completed-20261005.json'
ROOT_REVIEW=BASE/'dms-modeq-v2-root-cold-stage-review-20261005.json'
ROOT_REVIEW_SHA='29053bc40407850769b1efef39bae3f6fd3bb588a3a747c0bdded21141481151'
PRESERVED={
 BASE/'htpeo-dms-current-fresh-build.json':'feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238',
 BASE/'htpeo-dms-current-import-pruned-diagnostic-fresh-build.json':'fb939c9bcf589a1152d346aaae430cc602c4c0b29c9000023c299e92a35adc4b',
 BASE/'dms-original99-output-transfer-completed-20261005.json':'8d2ad36c44b26ef747585e78eb86a60baf1cdfaeebb0dee465b25713dc4570ca',
 BASE/'builds/htpeo-dms-current-import-pruned-diagnostic/build-plan.json':'749292bbe2ed1cf05901d278aee752e3404324037a501d0da7d19c8e1893c93e'}

class FILETIME(ctypes.Structure):
    _fields_=[('low',wintypes.DWORD),('high',wintypes.DWORD)]
class BY_HANDLE_FILE_INFORMATION(ctypes.Structure):
    _fields_=[('attributes',wintypes.DWORD),('creation',FILETIME),('access',FILETIME),('write',FILETIME),
      ('volume_serial',wintypes.DWORD),('size_high',wintypes.DWORD),('size_low',wintypes.DWORD),
      ('link_count',wintypes.DWORD),('index_high',wintypes.DWORD),('index_low',wintypes.DWORD)]
kernel=ctypes.WinDLL('kernel32',use_last_error=True)
kernel.CreateFileW.argtypes=[wintypes.LPCWSTR,wintypes.DWORD,wintypes.DWORD,ctypes.c_void_p,wintypes.DWORD,wintypes.DWORD,wintypes.HANDLE]
kernel.CreateFileW.restype=wintypes.HANDLE
kernel.GetFileInformationByHandle.argtypes=[wintypes.HANDLE,ctypes.POINTER(BY_HANDLE_FILE_INFORMATION)]
kernel.GetFileInformationByHandle.restype=wintypes.BOOL
kernel.CloseHandle.argtypes=[wintypes.HANDLE];kernel.CloseHandle.restype=wintypes.BOOL
kernel.GetVolumePathNameW.argtypes=[wintypes.LPCWSTR,wintypes.LPWSTR,wintypes.DWORD]
kernel.GetVolumePathNameW.restype=wintypes.BOOL
kernel.GetVolumeInformationW.argtypes=[wintypes.LPCWSTR,wintypes.LPWSTR,wintypes.DWORD,ctypes.POINTER(wintypes.DWORD),ctypes.POINTER(wintypes.DWORD),ctypes.POINTER(wintypes.DWORD),wintypes.LPWSTR,wintypes.DWORD]
kernel.GetVolumeInformationW.restype=wintypes.BOOL

def digest(path):
    d=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):d.update(block)
    return d.hexdigest()
def load(path):return json.loads(Path(path).read_bytes())
def now():return datetime.now(timezone.utc).isoformat()
def save_new(path,value):
    assert not path.exists(),str(path)
    with path.open('x',encoding='utf8') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    return digest(path)
def file_identity(path):
    handle=kernel.CreateFileW(str(Path(path).resolve()),0x80,7,None,3,0,None)
    if handle==ctypes.c_void_p(-1).value:raise ctypes.WinError(ctypes.get_last_error())
    info=BY_HANDLE_FILE_INFORMATION()
    try:
        if not kernel.GetFileInformationByHandle(handle,ctypes.byref(info)):raise ctypes.WinError(ctypes.get_last_error())
        return {'volume_serial':int(info.volume_serial),'file_index_high':int(info.index_high),
            'file_index_low':int(info.index_low),'link_count':int(info.link_count),
            'bytes':(int(info.size_high)<<32)|int(info.size_low),'attributes':int(info.attributes)}
    finally:kernel.CloseHandle(handle)
def inode_key(info):return (info['volume_serial'],info['file_index_high'],info['file_index_low'])
def volume_identity(path):
    root=ctypes.create_unicode_buffer(32768)
    if not kernel.GetVolumePathNameW(str(Path(path).resolve()),root,len(root)):raise ctypes.WinError(ctypes.get_last_error())
    serial=wintypes.DWORD();maximum=wintypes.DWORD();flags=wintypes.DWORD()
    filesystem=ctypes.create_unicode_buffer(64)
    if not kernel.GetVolumeInformationW(root.value,None,0,ctypes.byref(serial),ctypes.byref(maximum),ctypes.byref(flags),filesystem,len(filesystem)):raise ctypes.WinError(ctypes.get_last_error())
    assert filesystem.value=='NTFS' and flags.value&0x00400000
    return {'volume_root':root.value,'volume_serial':int(serial.value),'filesystem':filesystem.value,
        'filesystem_flags':int(flags.value),'supports_hard_links':True}
def preserved_check():
    for path,sha in PRESERVED.items():assert digest(path)==sha,('Preserved receipt/plan changed',str(path))
    return [{'file':str(path),'sha256':sha} for path,sha in PRESERVED.items()]
def original_route_inactive():
    command="Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|python)(\\.exe)?$' } | Select-Object ProcessId,Name,CommandLine | ConvertTo-Json -Compress"
    result=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True,text=True,encoding='utf8',errors='replace',check=True)
    rows=json.loads(result.stdout or '[]');rows=rows if isinstance(rows,list) else [rows]
    disallowed=[]
    for row in rows:
        cmd=(row.get('CommandLine') or '').replace('\\','/').lower()
        if ('/builds/htpeo-dms-current/' in cmd or
            ('run_source_plan.py' in cmd and ' htpeo-dms-current ' in cmd) or 'dispatch_dms_sole_guarded.py' in cmd):disallowed.append(row)
    assert not disallowed,('Original shared-output route must stay inactive',disallowed)
    return {'checked_utc':now(),'original_scientific_route_inactive':True,'process_snapshot':rows}

def prepare():
    assert digest(ROOT_REVIEW)==ROOT_REVIEW_SHA
    preserved=preserved_check();check=verify_stage(require_cold=True)
    proposal=load(BASE/'dms-modeq-v2-complete-stage-proposal-20261005.json')
    stage_plan=load(STAGE/'build-plan.json')
    eligibility=load(proposal['owned_output_eligibility_inventory']['file'])
    original_receipt=load(stage_plan['original119_immutable_receipt'])
    passed={r['module']:r for r in original_receipt['builds'] if r.get('exit')==0 and not r.get('is_endpoint_audit') and not r.get('stop_reason')}
    modules={r['module']:r for r in stage_plan['modules']}
    links=[];reuse=[]
    source_volume=volume_identity(ORIGINAL);target_volume=volume_identity(STAGE)
    assert source_volume==target_volume
    for name in check['eligible99_module_names']:
        row=passed[name];entry=modules[name]
        src=Path(entry['original_file']).resolve();dst=Path(entry['file']).resolve()
        assert src.is_relative_to(ORIGINAL.resolve()) and dst.is_relative_to(STAGE.resolve())
        actual=[src.with_suffix(s) for s in ['.olean','.olean.private','.olean.server','.ilean'] if src.with_suffix(s).is_file()]
        declared={Path(a['file']).resolve():a for a in row['artifacts']}
        assert set(actual)==set(declared)
        records=[]
        for artifact in actual:
            old=declared[artifact];target=dst.with_suffix(artifact.name[len(src.stem):])
            assert not target.exists() and digest(artifact)==old['sha256'] and artifact.stat().st_size==old['bytes']
            identity=file_identity(artifact)
            assert identity['volume_serial']==source_volume['volume_serial'] and identity['bytes']==old['bytes']
            record={'module':name,'original_owned_output':str(artifact),'diagnostic_target':str(target),
                'bytes':old['bytes'],'sha256':old['sha256'],'artifact_kind':artifact.name[len(src.stem):],
                'original_NTFS_identity_at_policy':identity,
                'classification':'HARD_LINK_OF_PREVIOUS_OWN_ORIGINAL_ROUTE_COLD_OUTPUT_NO_NEW_COMPILATION'}
            links.append(record);records.append(record)
        candidate=next(r for r in eligibility['modules'] if r['module']==name)
        reuse.append({'module':name,'original_and_actual_staged_source_sha256':entry['sha256'],
            'original_PASS_row_source_sha256':row['source_sha256'],'original_PASS_row_sha256':candidate['original_PASS_row_sha256'],
            'entire_unaffected_custom_dependency_closure':candidate['custom_dependency_closure'],
            'hard_linked_previous_own_cold_output_artifacts':records,'fresh_diagnostic_compilation':False})
    assert len(reuse)==len(links)==99 and len({r['diagnostic_target'] for r in links})==99
    policy={'status':'PREPARED_EXACT99_HARD_LINK_POLICY_NO_LINK_NO_LEAN_ROOT_REVIEW_REQUIRED','prepared_utc':now(),
        'original_family':'htpeo-dms-current','diagnostic_route':stage_plan['id'],
        'source_plan':str(STAGE/'build-plan.json'),'source_plan_sha256':digest(STAGE/'build-plan.json'),
        'root_cold_stage_review':str(ROOT_REVIEW),'root_cold_stage_review_sha256':ROOT_REVIEW_SHA,
        'read_only_stage_verifier_sha256':digest(BASE/'verify_dms_modeq_v2_stage.py'),
        'immutable_original119_receipt':stage_plan['original119_immutable_receipt'],
        'immutable_original119_receipt_sha256':stage_plan['original119_immutable_receipt_sha256'],
        'full_official2735_closure':stage_plan['exact_full_official_closure'],
        'full_official2735_closure_sha256':stage_plan['exact_full_official_closure_sha256'],
        'original_and_target_NTFS_volume':source_volume,'preserved_original_and_failed_v1_receipts':preserved,
        'module_count':99,'artifact_count':99,'logical_output_bytes':sum(r['bytes'] for r in links),
        'physical_payload_duplication_bytes':0,'eligible99_module_names':check['eligible99_module_names'],
        'modules':reuse,'output_links':links,'required129_new_cold_module_names':check['all129_required_cold_sources'],
        'affected125_modules_must_remain_cold':check['all125_affected_sources_must_remain_cold'],
        'scientific_coverage_labels':{'reused_previous_own_original_route_cold_sources':99,'required_new_cold_diagnostic_sources':129,'total_authored_scientific_bodies':228},
        'LEAN_PATH_policy':'Only v2 stage and verified official libraries; original custom directory forbidden.',
        'hard_link_safety_policy':'Original route inactive; runner skips99 and never writes or overwrites linked outputs. No attributes changed. Current source/target SHA and NTFS file IDs checked before/after.',
        'seed_disk_floor_bytes':1_000_000_000,
        'execution_requirements':'Separate SHA-bound ROOT_APPROVED_HARD_LINK_SEED_ONLY_NO_LEAN receipt with exact99 names, helper and policy hashes; no overwrite.',
        'qualification':'Preparation creates no link or compiler. These99 are previous own original-route cold outputs, never new diagnostic invocations;129 affected/unpassed remain cold.'}
    sha=save_new(POLICY,policy)
    print(json.dumps({'policy':str(POLICY),'policy_sha256':sha,'modules':99,'logical_bytes':policy['logical_output_bytes'],'links_created':0,'new_Lean_invocations':0}),flush=True)

def seed(approval_path,approval_sha):
    approval_path=Path(approval_path).resolve()
    assert approval_path.is_relative_to(BASE.resolve()) and digest(approval_path)==approval_sha
    approved=load(approval_path)
    assert approved['status']=='ROOT_APPROVED_HARD_LINK_SEED_ONLY_NO_LEAN'
    assert approved['reviewed_policy_sha256']==digest(POLICY) and approved['reviewed_seed_helper_sha256']==digest(__file__)
    policy=load(POLICY)
    assert not SEED_RECEIPT.exists() and not (BASE/(policy['diagnostic_route']+'-fresh-build.json')).exists()
    check=verify_stage(require_cold=True)
    assert check['eligible99_module_names']==policy['eligible99_module_names']==approved['approved99module_names']
    assert digest(policy['source_plan'])==policy['source_plan_sha256']
    assert volume_identity(ORIGINAL)==volume_identity(STAGE)==policy['original_and_target_NTFS_volume']
    preserved_check();inactive=original_route_inactive()
    assert shutil.disk_usage(BASE).free>=policy['seed_disk_floor_bytes']
    result={'status':'OWN_ORIGINAL99_HARD_LINK_SEED_RUNNING_NO_LEAN','started_utc':now(),
        'approval_receipt':str(approval_path),'approval_receipt_sha256':approval_sha,'policy_file':str(POLICY),'policy_sha256':digest(POLICY),
        'seed_helper_sha256':digest(__file__),'stage_source_plan_sha256':policy['source_plan_sha256'],
        'immutable_original119_receipt_sha256':digest(policy['immutable_original119_receipt']),
        'modules':policy['modules'],'scientific_coverage_labels':policy['scientific_coverage_labels'],
        'output_links':[],'new_Lean_compilation_invocations':0,'payload_bytes_copied':0,
        'original_custom_output_directory_allowed_on_LEAN_PATH':False,'original_route_inactive_before':inactive,
        'minimum_disk_free_bytes':shutil.disk_usage(BASE).free}
    progress=BASE/'dms-modeq-v2-original99-hardlink-seed-progress-20261005.json'
    assert not progress.exists()
    def checkpoint():
        temp=progress.with_suffix('.json.tmp');temp.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
        for attempt in range(60):
            try:os.replace(temp,progress);return
            except PermissionError:
                if attempt==59:raise
                time.sleep(.1)
    checkpoint()
    for item in policy['output_links']:
        source=Path(item['original_owned_output']).resolve();target=Path(item['diagnostic_target']).resolve()
        assert source.is_relative_to(ORIGINAL.resolve()) and target.is_relative_to(STAGE.resolve()) and not target.exists()
        before=file_identity(source)
        assert before==item['original_NTFS_identity_at_policy'] and digest(source)==item['sha256']
        free=shutil.disk_usage(BASE).free;result['minimum_disk_free_bytes']=min(result['minimum_disk_free_bytes'],free)
        assert free>=policy['seed_disk_floor_bytes']
        os.link(source,target)
        after=file_identity(source);linked=file_identity(target)
        assert inode_key(before)==inode_key(after)==inode_key(linked)
        assert after['link_count']==before['link_count']+1==linked['link_count']
        assert after['attributes']==before['attributes'] and after['bytes']==before['bytes']==item['bytes']
        assert digest(source)==digest(target)==item['sha256']
        result['output_links'].append(dict(item,original_NTFS_identity_before_link=before,
            original_NTFS_identity_after_link=after,target_NTFS_identity_after_link=linked,
            original_sha256_after_link=digest(source),target_sha256=digest(target)))
        checkpoint()
    assert len(result['output_links'])==99
    preserved_check();result['original_route_inactive_after']=original_route_inactive()
    result.update(status='EXACT99_PREVIOUS_OWN_COLD_OUTPUT_HARD_LINK_SEED_COMPLETE_NO_NEW_COMPILATION',finished_utc=now(),
        eligible99_module_names=policy['eligible99_module_names'],required129_new_cold_module_names=policy['required129_new_cold_module_names'])
    sha=save_new(SEED_RECEIPT,result);checkpoint()
    print(json.dumps({'seed_receipt':str(SEED_RECEIPT),'seed_receipt_sha256':sha,'linked_previous_own_cold_sources':99,'new_Lean_compilations':0,'payload_bytes_copied':0}),flush=True)

def verify_seed(policy_sha,seed_sha):
    assert digest(POLICY)==policy_sha and digest(SEED_RECEIPT)==seed_sha
    policy=load(POLICY);result=load(SEED_RECEIPT)
    assert result['status']=='EXACT99_PREVIOUS_OWN_COLD_OUTPUT_HARD_LINK_SEED_COMPLETE_NO_NEW_COMPILATION'
    assert result['policy_sha256']==policy_sha and result['stage_source_plan_sha256']==digest(STAGE/'build-plan.json')
    assert result['new_Lean_compilation_invocations']==result['payload_bytes_copied']==0
    assert result['eligible99_module_names']==policy['eligible99_module_names'] and len(result['output_links'])==99
    for expected,actual in zip(policy['output_links'],result['output_links']):
        assert all(actual[k]==v for k,v in expected.items())
        source=file_identity(expected['original_owned_output']);target=file_identity(expected['diagnostic_target'])
        assert inode_key(source)==inode_key(target)==inode_key(expected['original_NTFS_identity_at_policy'])
        assert source==target==actual['original_NTFS_identity_after_link']==actual['target_NTFS_identity_after_link']
        assert digest(expected['original_owned_output'])==digest(expected['diagnostic_target'])==expected['sha256']
    preserved_check();original_route_inactive()
    return {'status':'EXACT99_NTFS_HARD_LINK_IDENTITIES_VERIFIED_PREVIOUS_OWN_COLD_OUTPUTS_NOT_NEW_COMPILES',
        'policy_sha256':policy_sha,'seed_receipt_sha256':seed_sha,'reused_previous_own_cold_source_count':99,
        'new_diagnostic_compilations':0,'modules':result['modules'],
        'required129_new_cold_module_names':policy['required129_new_cold_module_names'],
        'LEAN_PATH_original_custom_directory_forbidden':str(ORIGINAL.resolve())}

if __name__=='__main__':
    if sys.argv[1:]==['--prepare-policy']:prepare()
    elif len(sys.argv)==4 and sys.argv[1]=='--seed-root-approved':seed(sys.argv[2],sys.argv[3])
    else:raise SystemExit('Use --prepare-policy or --seed-root-approved approval_path approval_sha256; preparation creates no links or Lean.')
