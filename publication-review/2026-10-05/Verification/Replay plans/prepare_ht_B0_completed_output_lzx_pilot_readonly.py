"""Prepare an exact, reversible completed HT B0 output pilot; no storage/Lean execution."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json,os,shutil,sys

BASE=Path(__file__).resolve().parent
from pilot_completed_own_output_strong_lzx import sha,metadata,wof_info,read_and_mmap
from resource_metrics import snapshot
OLD=BASE/'pilot_completed_own_output_strong_lzx.py'
OLD_SHA='63f23664c23f44922f86106c5016a9a16e3c37f3cf2341972a4a9eeb416776cd'
PLAN=BASE/'builds/htpeo-ramsey-current/build-plan.json'
PLAN_SHA='94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
RECEIPT=BASE/'htpeo-ramsey-current-fresh-build.json'
RECEIPT_SHA='7f615bb0257aa9e56c2088c4fc494f4c66becc82291218d1c18fa2b078a2d39d'
TARGET=BASE/'builds/htpeo-ramsey-current/RamseyCert/Chunk/B0.olean'
MODULE='RamseyCert.Chunk.B0'
HELPER=BASE/'pilot_completed_ht_B0_strong_lzx.py'
PROPOSAL=BASE/'completed-own-HTRamsey-B0-strong-LZX-single-pilot-preparation-20261005.json'
DIFF=BASE/'proposals/ht-ramsey-B0-single-LZX-pilot-full-helper-diff-20261005.diff'
assert sha(OLD)==OLD_SHA and sha(PLAN)==PLAN_SHA and sha(RECEIPT)==RECEIPT_SHA
plan=json.loads(PLAN.read_bytes());doc=json.loads(RECEIPT.read_bytes())
assert doc['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
rows=[r for r in doc['builds'] if not r['is_endpoint_audit'] and r['exit']==0 and not r.get('stop_reason')]
assert len(rows)==36
row=next(r for r in rows if r['module']==MODULE)
artifact=next(a for a in row['artifacts'] if Path(a['file']).resolve()==TARGET)
assert sha(TARGET)==artifact['sha256']=='02f47c4a043a6931357bd3b224f44064697224a744eff3276090617a641d3825'
oldproposal=json.loads((BASE/'completed-own-BooleanTree-strong-LZX-single-pilot-preparation-20261005.json').read_bytes())
native=metadata(oldproposal);before=native(TARGET);backing=wof_info(TARGET);read=read_and_mmap(TARGET)
assert before['link_count']==1 and before['FILE_ATTRIBUTE_COMPRESSED']
assert not backing['external'] and not before['FILE_ATTRIBUTE_REPARSE_POINT'] and not before['FILE_ATTRIBUTE_ENCRYPTED']
bindings={str(PLAN):PLAN_SHA,str(RECEIPT):RECEIPT_SHA}
for entry in plan['modules']:
    assert sha(entry['file'])==entry['sha256'];bindings[entry['file']]=entry['sha256']
for r in rows:
    for a in r['artifacts']:
        assert sha(a['file'])==a['sha256']
        if Path(a['file']).resolve()!=TARGET:bindings[a['file']]=a['sha256']
for name in ['native_resource_guard.py','matt_resource_guard.py','resource_metrics.py','assess_completed_own_artifact_storage_readonly.py',
             'run_htpeo_ramsey_first_kernel_chunk_calibration.py','htpeo-ramsey-first-kernel-chunk-calibration-scope-20261005.json']:
    p=BASE/name;bindings[str(p)]=sha(p)
for name in plan['audit_modules']+['FreshAuditSupplement.lean']:
    p=PLAN.parent/name;bindings[str(p)]=sha(p)
old=OLD.read_text(encoding='utf8');new=old
replacements={
 "PROPOSAL=BASE/'completed-own-BooleanTree-strong-LZX-single-pilot-preparation-20261005.json'":"PROPOSAL=BASE/'completed-own-HTRamsey-B0-strong-LZX-single-pilot-preparation-20261005.json'",
 "TARGET=BASE/'builds/sakana-FOCUS-E3/BooleanTree.olean'":"TARGET=BASE/'builds/htpeo-ramsey-current/RamseyCert/Chunk/B0.olean'",
 " or 'sakana-focus-e3' in cli:":" or 'htpeo-ramsey-current' in cli or 'ramseycert' in cli:",
 "BASE/'builds/sakana-FOCUS-E3'":"BASE/'builds/htpeo-ramsey-current'",
 "'sources_compiler_alias_DMS_A000_seed_protected_or_other_output_targets':0":"'sources_runtime_providers_DMS_shared_or_other_output_targets':0",
 "import ctypes, hashlib, json, mmap, os, shutil, subprocess, sys, time":"import ctypes, hashlib, json, mmap, msvcrt, os, shutil, subprocess, sys, time",
 "    quiescence();gates()\n    # An exclusive named mutex":"    quiescence();gates()\n    # Hold the existing HT replay byte lock; no source dispatcher may overlap this pilot.\n    replay_lock=BASE/'builds/htpeo-ramsey-current/.fresh-replay.lock'\n    assert replay_lock.is_file() and replay_lock.stat().st_size==1\n    replay=replay_lock.open('r+b');replay.seek(0)\n    try:msvcrt.locking(replay.fileno(),msvcrt.LK_NBLCK,1)\n    except OSError:\n        replay.close();raise RuntimeError('HT dispatcher still owns its replay lock')\n    # An exclusive named mutex",
 "        K.ReleaseMutex(mutex);K.CloseHandle(mutex)":"        K.ReleaseMutex(mutex);K.CloseHandle(mutex)\n        replay.seek(0);msvcrt.locking(replay.fileno(),msvcrt.LK_UNLCK,1);replay.close()",
}
for a,b in replacements.items():
    assert new.count(a)==1,(a,new.count(a));new=new.replace(a,b,1)
ast.parse(new)
if HELPER.exists():assert HELPER.read_bytes()==new.encode('utf8')
else:
    with HELPER.open('x',encoding='utf8',newline='\n') as f:f.write(new)
diff_text=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=OLD.name,tofile=HELPER.name))
if DIFF.exists():assert DIFF.read_bytes()==diff_text.encode('utf8')
else:
    with DIFF.open('x',encoding='utf8',newline='\n') as f:f.write(diff_text)
compact=Path(os.environ['SystemRoot'])/'System32/compact.exe'
commands=[[str(compact),'/C','/F','/Q','/EXE:LZX',str(TARGET)]]
restore=[[str(compact),'/U','/EXE','/Q',str(TARGET)],[str(compact),'/C','/F','/Q',str(TARGET)]]
out={'status':'PREPARED_ONLY_ONE_COMPLETED_HT_B0_OWN_OUTPUT_STRONG_LZX_PILOT_NO_EXECUTION',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'helper':str(HELPER),'helper_sha256':sha(HELPER),'helper_AST':'PASS','preserved_reviewed_parent_helper':str(OLD),'preserved_parent_helper_sha256':OLD_SHA,
 'full_helper_diff':str(DIFF),'full_helper_diff_sha256':sha(DIFF),
 'exact_target':str(TARGET),'content_sha256_before':artifact['sha256'],'native_before':before,'WOF_before':backing,'read_and_mmap_before':read,
 'completed_own_receipt':str(RECEIPT),'completed_own_receipt_sha256':RECEIPT_SHA,'actual36_source_passes':36,
 'source_module':MODULE,'source_sha256':row['source_sha256'],'actual_completed_module_artifact':artifact,
 'actual_B0_seconds':row['seconds'],'actual_B0_own_job_guard':row['own_job_resource_receipt'],
 'native_metadata_helper_sha256':sha(BASE/'assess_completed_own_artifact_storage_readonly.py'),
 'frozen_input_bindings':bindings,'compact_executable':str(compact),'compact_executable_sha256':sha(compact),
 'exact_operation_not_executed':commands[0],'exact_inverse_ordinary_recompression_recipe_not_executed':restore,
 'resource_policy':oldproposal['resource_policy'],'pre_post_contract':oldproposal['pre_post_contract'],
 'future_compress_root_approval_fields':{'status':'ROOT_APPROVED_ONE_COMPLETED_OWN_OUTPUT_STRONG_LZX_PILOT','reviewed_helper_sha256':sha(HELPER),'reviewed_proposal_sha256':'ROOT_BINDS_COMPLETE_PROPOSAL_SHA','reviewed_exact_commands':commands},
 'future_restore_root_approval_fields':{'status':'ROOT_APPROVED_EXACT_STRONG_LZX_PILOT_ORDINARY_NTFS_RESTORATION','reviewed_helper_sha256':sha(HELPER),'reviewed_proposal_sha256':'ROOT_BINDS_COMPLETE_PROPOSAL_SHA','actual_pilot_receipt':'ACTUAL_HT_B0_PASS_PILOT_FILE','actual_pilot_receipt_sha256':'ROOT_BINDS_ACTUAL_PASS_SHA','reviewed_exact_commands':restore},
 'quiescence':'Reject HT/RamseyCert source/compiler/dispatcher, all compressors/extractors, and acquire the existing replay byte lock. One global own storage mutex.',
 'scope_exclusions':['all2103 scientific sources and both organizer audits','all runtimes/official dependencies/providers','all DMS protected aliases and all other shared inodes','other35 HT source outputs and unrecorded future outputs','entrant archives/user/system/application files'],
 'current_resources':{'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()},
 'guaranteed_additional_savings_bytes':0,'compiler_compression_deletion_alias_or_existing_source_receipt_mutations':0}
with PROPOSAL.open('x',encoding='utf8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'proposal':str(PROPOSAL),'proposal_sha256':sha(PROPOSAL),'helper':str(HELPER),'helper_sha256':sha(HELPER),'diff_sha256':sha(DIFF),'native_before':before,'execution':0},indent=2))
