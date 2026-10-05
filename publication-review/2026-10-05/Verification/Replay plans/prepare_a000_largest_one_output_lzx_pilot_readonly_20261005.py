"""Prepare an exact one-file A000 LZX pilot; never execute compression or Lean."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json,os,sys

BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
from pilot_completed_own_output_strong_lzx import sha,wof_info,read_and_mmap,metadata
OLD=BASE/'pilot_completed_own_output_strong_lzx.py'
OLD_SHA='63f23664c23f44922f86106c5016a9a16e3c37f3cf2341972a4a9eeb416776cd'
INVENTORY=BASE/'a000-original76-quiescent-owned-output-storage-proposal-20261005.json'
INVENTORY_SHA='edf00e50525ecf5acdc227368403ddbbba1cdc952b8952402bc5b12692b2e5fc'
assert sha(OLD)==OLD_SHA and sha(INVENTORY)==INVENTORY_SHA
inv=json.loads(INVENTORY.read_bytes())
row=inv['largest_completed_own_output_candidates'][0]
assert row['source_module']=='OpHack.QuadraticResidue224.CertificateP127Part0033'
target=Path(row['file']).resolve()
assert target==BASE/'builds/sakana-a000224/OpHack/QuadraticResidue224/CertificateP127Part0033.olean'
proposal_path=BASE/'completed-own-A000-P127Part0033-strong-LZX-single-pilot-preparation-20261005.json'
helper_path=BASE/'pilot_completed_a000_P127Part0033_strong_lzx.py'
diff_path=BASE/'proposals/a000-P127Part0033-single-LZX-pilot-full-helper-diff-20261005.diff'
old=OLD.read_text(encoding='utf8');new=old
replacements={
 "PROPOSAL=BASE/'completed-own-BooleanTree-strong-LZX-single-pilot-preparation-20261005.json'":"PROPOSAL=BASE/'completed-own-A000-P127Part0033-strong-LZX-single-pilot-preparation-20261005.json'",
 "TARGET=BASE/'builds/sakana-FOCUS-E3/BooleanTree.olean'":"TARGET=BASE/'builds/sakana-a000224/OpHack/QuadraticResidue224/CertificateP127Part0033.olean'",
 " or 'sakana-focus-e3' in cli:":" or 'sakana-a000224' in cli or 'quadraticresidue224' in cli:",
 "BASE/'builds/sakana-FOCUS-E3'":"BASE/'builds/sakana-a000224'",
 "'sources_compiler_alias_DMS_A000_seed_protected_or_other_output_targets':0":"'sources_runtime_providers_DMS_shared_or_other_output_targets':0",
 "import ctypes, hashlib, json, mmap, os, shutil, subprocess, sys, time":"import ctypes, hashlib, json, mmap, msvcrt, os, shutil, subprocess, sys, time",
 "    quiescence();gates()\n    # An exclusive named mutex":"    quiescence();gates()\n    # Hold the existing own replay byte lock without writing its bytes.\n    replay_lock=BASE/'builds/sakana-a000224/.fresh-replay.lock'\n    assert replay_lock.is_file() and replay_lock.stat().st_size==1\n    replay=replay_lock.open('r+b');replay.seek(0)\n    try:msvcrt.locking(replay.fileno(),msvcrt.LK_NBLCK,1)\n    except OSError:\n        replay.close();raise RuntimeError('A000 dispatcher still owns the source replay lock')\n    # An exclusive named mutex",
 "        K.ReleaseMutex(mutex);K.CloseHandle(mutex)":"        K.ReleaseMutex(mutex);K.CloseHandle(mutex)\n        replay.seek(0);msvcrt.locking(replay.fileno(),msvcrt.LK_UNLCK,1);replay.close()",
}
for before,after in replacements.items():
    assert new.count(before)==1,(before,new.count(before));new=new.replace(before,after,1)
ast.parse(new)
with helper_path.open('x',encoding='utf8',newline='\n') as f:f.write(new)
with diff_path.open('x',encoding='utf8',newline='\n') as f:
    f.writelines(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='preserved-reviewed-BooleanTree-single-file-helper',tofile='prepared-only-A000-P127Part0033-single-file-helper'))
oldproposal=json.loads((BASE/'completed-own-BooleanTree-strong-LZX-single-pilot-preparation-20261005.json').read_bytes())
native=metadata(oldproposal);now=native(target);backing=wof_info(target);read=read_and_mmap(target)
assert read['ordinary_read_sha256']==row['content_sha256'] and not backing['external']
for k in ['logical_bytes','volume_serial','file_index_high','file_index_low','link_count','last_write_FILETIME','standard_allocation_bytes']:
    assert now[k]==row[k],k
assert now['link_count']==1 and now['FILE_ATTRIBUTE_COMPRESSED'] and not now['FILE_ATTRIBUTE_REPARSE_POINT']
bindings={i['file']:i['sha256'] for i in inv['frozen_bindings'].values()}
bindings.update({s['file']:s['sha256'] for s in inv['immutable_source_identities']})
bindings[str(INVENTORY)]=INVENTORY_SHA
for n in ['native_resource_guard.py','matt_resource_guard.py','resource_metrics.py','assess_completed_own_artifact_storage_readonly.py']:
    p=BASE/n;bindings[str(p)]=sha(p)
boolean=BASE/'20261005T054436652013Z-single-own-output-compress-actual.json'
boolean_doc=json.loads(boolean.read_bytes())
assert boolean_doc['status']=='PASS_BYTE_IDENTICAL_READABLE_STRONG_LZX_PILOT'
assert boolean_doc['actual_allocation_bytes_saved']==6_414_336
bindings[str(boolean)]=sha(boolean)
cleanup=BASE/'operational_history/cache-only-housekeeping/20261005T053902965112Z-execute.json'
cleanup_doc=json.loads(cleanup.read_bytes())
assert cleanup_doc['status']=='TASK_BINARY_DOWNLOAD_CACHE_REMOVED_EXTRACTED_PROVIDERS_PRESERVED'
bindings[str(cleanup)]=sha(cleanup)
for path,h in bindings.items():assert sha(path)==h,path
compact=Path(os.environ['SystemRoot'])/'System32/compact.exe'
commands=[[str(compact),'/C','/F','/Q','/EXE:LZX',str(target)]]
restore=[[str(compact),'/U','/EXE','/Q',str(target)],[str(compact),'/C','/F','/Q',str(target)]]
out={
 'status':'PREPARED_ONLY_ONE_COMPLETED_A000_OWN_OUTPUT_STRONG_LZX_PILOT_NO_EXECUTION',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'helper':str(helper_path),'helper_sha256':sha(helper_path),'helper_AST':'PASS',
 'preserved_reviewed_parent_helper':str(OLD),'preserved_parent_helper_sha256':OLD_SHA,
 'full_helper_diff':str(diff_path),'full_helper_diff_sha256':sha(diff_path),
 'exact_target':str(target),'content_sha256_before':row['content_sha256'],
 'native_before':now,'WOF_before':backing,'read_and_mmap_before':read,
 'completed_own_receipt':str(BASE/'sakana-a000224-original76-storage-checkpoint-receipt-20261005.json'),
 'completed_own_receipt_sha256':inv['frozen_bindings']['immutable_original76_receipt']['sha256'],
 'source_module':row['source_module'],'source_sha256':row['source_sha256'],
 'actual_completed_module_artifact':{'file':str(target),'sha256':row['content_sha256'],'bytes':row['logical_bytes']},
 'native_metadata_helper_sha256':sha(BASE/'assess_completed_own_artifact_storage_readonly.py'),
 'frozen_input_bindings':bindings,'compact_executable':str(compact),'compact_executable_sha256':sha(compact),
 'exact_operation_not_executed':commands[0],'exact_inverse_ordinary_recompression_recipe_not_executed':restore,
 'resource_policy':oldproposal['resource_policy'],
 'future_compress_root_approval_fields':{'status':'ROOT_APPROVED_ONE_COMPLETED_OWN_OUTPUT_STRONG_LZX_PILOT','reviewed_helper_sha256':sha(helper_path),'reviewed_proposal_sha256':'ROOT_BINDS_COMPLETE_PROPOSAL_SHA','reviewed_exact_commands':commands},
 'future_restore_root_approval_fields':{'status':'ROOT_APPROVED_EXACT_STRONG_LZX_PILOT_ORDINARY_NTFS_RESTORATION','reviewed_helper_sha256':sha(helper_path),'reviewed_proposal_sha256':'ROOT_BINDS_COMPLETE_PROPOSAL_SHA','actual_pilot_receipt':'ACTUAL_A000_PASS_PILOT_FILE','actual_pilot_receipt_sha256':'ROOT_BINDS_ACTUAL_A000_PASS_SHA','reviewed_exact_commands':restore},
 'quiescence':'Actual current A000 receipt/checkpoint/source hashes must remain identical; reject own A000 Lean/dispatcher or any compressor/extractor. Nonblocking lock existing one-byte A000 replay file during operation; exact global storage mutex.',
 'inherited_pre_post_contract':oldproposal['pre_post_contract'],
 'prior_BooleanTree_evidence':{'file':str(boolean),'sha256':sha(boolean),'allocated_savings_measured':6_414_336,'same_gain_for_A000_not_implied':True},
 'cache_cleanup_provenance':{'file':str(cleanup),'sha256':sha(cleanup),'actual_all_task_download_cache_cleanup_complete':True},
 'scope_exclusions':['all171 scientific Lean sources','all runtimes/installed official dependencies/providers','all DMS and shared inodes','other75 A000 owned outputs and every unrecorded future output','all other outputs/submitted archives/user/system/application files'],
 'guaranteed_additional_savings_bytes':0,'actual_compact_Lean_delete_copy_existing_source_receipt_or_output_mutation':False}
with proposal_path.open('x',encoding='utf8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'proposal':str(proposal_path),'proposal_sha256':sha(proposal_path),'helper':str(helper_path),'helper_sha256':sha(helper_path),'diff_sha256':sha(diff_path),'executions':0},indent=2))
