"""Prepare exact remaining75 owned A000 storage pass; execute no mutator."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,os,time

BASE=Path(__file__).resolve().parent
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
source=BASE/'a000_post_exit_lzx_interface_prepared.py';source_text=source.read_text(encoding='utf8');tree=ast.parse(source_text)
core=BASE/'a000_owned_storage_guard_prepared.py'
functions=['sha','stamp','write_new','wof_info','read_and_mmap','quiescence','gates','guarded_compact']
pieces={n.name:ast.get_source_segment(source_text,n) for n in tree.body if isinstance(n,ast.FunctionDef)}
header='''"""Prepared storage-only own-output guard core; no standalone operation."""
from pathlib import Path
from datetime import datetime,timezone
from ctypes import wintypes as W
import ctypes,hashlib,json,mmap,os,shutil,subprocess,time
from native_resource_guard import K,EXTENDEDLIMIT,memory,processes,own_tree
from matt_resource_guard import resume_suspended_root
from resource_metrics import snapshot
BASE=Path(__file__).resolve().parent
GIB=2**30
'''
core_text=header+'\n\n'.join(pieces[n] for n in functions)+'\n\nif __name__=="__main__":raise SystemExit("Prepared guard library only; no standalone operation.")\n'
ast.parse(core_text)
with core.open('x',encoding='utf8',newline='\n') as f:f.write(core_text)
from a000_owned_storage_guard_prepared import wof_info,read_and_mmap,quiescence
quiescence(0)
ip=BASE/'a000-original76-quiescent-owned-output-storage-proposal-20261005.json'
assert sha(ip)=='edf00e50525ecf5acdc227368403ddbbba1cdc952b8952402bc5b12692b2e5fc'
inv=json.loads(ip.read_bytes())
pilot=BASE/'20261005T054942002749Z-single-own-output-compress-actual.json'
assert sha(pilot)=='325bec959997fb2b2f4ec8defe8f7d6776e5d35aee508b553591b53fc72613cc'
pd=json.loads(pilot.read_bytes());assert pd['status']=='PASS_BYTE_IDENTICAL_READABLE_STRONG_LZX_PILOT'
assert pd['actual_allocation_bytes_saved']==8_998_912
native_path=BASE/'assess_completed_own_artifact_storage_readonly.py'
prefix,marker,_=native_path.read_text(encoding='utf8').partition('before_processes=process_snapshot()');assert marker
ns={'__file__':str(native_path),'__name__':'reviewed_native_metadata_definitions_only'}
exec(compile(prefix,str(native_path),'exec'),ns);native=ns['native_metadata']
targets=[];skipped=None;started=time.time()
for i,row in enumerate(inv['exact_owned_receipt_matched_outputs']):
    p=Path(row['file']).resolve();now=native(p);w=wof_info(p);read=read_and_mmap(p)
    for k in ['logical_bytes','volume_serial','file_index_high','file_index_low','link_count','last_write_FILETIME']:
        assert now[k]==row[k],k
    assert read['ordinary_read_sha256']==row['content_sha256'] and now['link_count']==1
    data={'file':str(p),'source_module':row['source_module'],'source_sha256':row['source_sha256'],
        'content_sha256':row['content_sha256'],'native_before':now,'WOF_before':w,'read_and_mmap_before':read}
    if row['source_module']=='OpHack.QuadraticResidue224.CertificateP127Part0033':
        assert now==pd['native_after'] and w==pd['WOF_after'] and w['external']
        skipped={'file':str(p),'source_module':row['source_module'],'content_sha256':row['content_sha256'],
            'native_current':now,'WOF_current':w,'read_and_mmap_current':read,'actual_pilot':str(pilot),'actual_pilot_sha256':sha(pilot),'never_targeted':True}
    else:
        assert now['FILE_ATTRIBUTE_COMPRESSED'] and not now['FILE_ATTRIBUTE_REPARSE_POINT'] and not now['FILE_ATTRIBUTE_ENCRYPTED'] and not w['external']
        assert now['standard_allocation_bytes']==row['standard_allocation_bytes']
        targets.append(data)
    if (i+1)%16==0:print(json.dumps({'read_only_hash_mmap_checks':i+1,'of':76}),flush=True)
assert len(targets)==75 and skipped
bindings={x['file']:x['sha256'] for x in inv['frozen_bindings'].values()}
bindings.update({s['file']:s['sha256'] for s in inv['immutable_source_identities']})
bindings[str(ip)]=sha(ip);bindings[str(pilot)]=sha(pilot)
for n in ['native_resource_guard.py','matt_resource_guard.py','resource_metrics.py']:
    p=BASE/n;bindings[str(p)]=sha(p)
for path,h in bindings.items():assert sha(path)==h,path
quiescence(0)
helper=BASE/'compress_a000_existing75_owned_outputs_prepared.py';ast.parse(helper.read_text(encoding='utf8'))
compact=Path(os.environ['SystemRoot'])/'System32/compact.exe'
commands=[[str(compact),'/C','/F','/Q','/EXE:LZX',r['file']] for r in targets]
policy={'dispatch_disk_bytes':4_000_000_000,'dispatch_physical_bytes':6*2**30,'dispatch_available_commit_bytes':5*2**30,
    'continuous_disk_bytes':1_000_000_000,'continuous_physical_bytes':3*2**30,'continuous_available_commit_bytes':2**30,
    'own_process_and_job_cap_bytes':256*2**20,'timeout_per_file_seconds':180,'one_compressor_no_parallel_files':True,
    'additional_per_file_initial_free_minus_logical_bytes_at_least':1_000_000_000}
out={'status':'PREPARED_ONLY_EXACT75_COMPLETED_OWN_A000_LZX_STORAGE_PASS_NO_EXECUTION',
    'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),'read_only_elapsed_seconds':round(time.time()-started,3),
    'helper':str(helper),'helper_sha256':sha(helper),'guard_core':str(core),'guard_core_sha256':sha(core),
    'guard_core_function_source_derivation':{'file':str(source),'sha256_at_preparation':sha(source),'exact_function_names':functions},
    'syntax_AST_all_helpers':'PASS','native_metadata_helper_sha256':sha(native_path),
    'protected_frozen_input_bindings':bindings,'original76_receipt_sha256':'d8226e2920788365d04ccd7c4a1cab829c5c0c192b4fa155aa4e4e4b11e3a552',
    'all171_scientific_source_identity_preserved':True,'exact75_remaining_completed_owned_targets':targets,
    'already_WOF_pilot_output_NOT_A_TARGET':skipped,'compact_executable_sha256':sha(compact),'resource_policy':policy,
    'exact_future_commands_not_executed':commands,
    'future_root_approval_fields':{'status':'ROOT_APPROVED_EXACT_EXISTING_A00075_COMPLETED_OWN_OUTPUTS_LZX',
        'helper_sha256':sha(helper),'guard_core_sha256':sha(core),'proposal_sha256':'ROOT_BINDS_THIS_COMPLETE_PROPOSAL_SHA',
        'target_count':75,'Part0033_already_WOF_target_excluded':True,'sources_receipts_runtime_providers_never_modified':True,'exact_reviewed_commands':commands},
    'target_storage_totals':{'logical_bytes':sum(r['native_before']['logical_bytes'] for r in targets),
        'stored_bytes_GetCompressedFileSizeW':sum(r['native_before']['stored_bytes_GetCompressedFileSizeW'] for r in targets),
        'standard_allocation_bytes':sum(r['native_before']['standard_allocation_bytes'] for r in targets)},
    'additional_savings_qualification':'Part0033 saved8,998,912 allocated bytes in an actual exact pilot. Further75 savings are not guaranteed or claimed; measure every file.',
    'future_reverse_recipe_not_executed':'Only separately reviewed exact successfully compressed paths: compact /U /EXE /Q EXACT_FILE, then compact /C /F /Q EXACT_FILE; ensure sufficient free allocation and preserve SHA/inode/linkcount/mtime/mmap. No automatic rollback.',
    'future_failure_contract':'Stop before next file on any guard/compact/content/identity/WOF failure; preserve started record and exact per-file raw logs/current state for root review. Never reclassify an existing source PASS or invent a Lean failure.',
    'scope_exclusions':['all171 authored Lean sources and audits','original/historical proof receipt bytes','actual runtimes and official source/providers','already-compressed Part0033 pilot inode','all DMS/shared/inactive donor aliases','all other/user/system/application files'],
    'source_compiler_compressor_copy_delete_existing_evidence_mutations':0}
dest=BASE/'proposals/a000-existing75-completed-owned-output-LZX-preparation-20261005.json'
with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'proposal':str(dest),'sha256':sha(dest),'helper_sha256':sha(helper),'guard_core_sha256':sha(core),'target_count':75,'storage_totals':out['target_storage_totals'],'executions':0},indent=2))
