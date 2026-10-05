"""Prepared exact75 existing-owned A000 storage pass; no operation without root.

All scientific sources and all proof receipts are read-only. The one already-tested
Part0033 WOF output is validated and never targeted. This is no proof compiler.
"""
from pathlib import Path
from datetime import datetime,timezone
from ctypes import wintypes as W
import argparse,ctypes,hashlib,json,msvcrt,os,sys
from a000_owned_storage_guard_prepared import K,sha,stamp,write_new,wof_info,read_and_mmap,quiescence,gates,guarded_compact

BASE=Path(__file__).resolve().parent
STAGE=(BASE/'builds/sakana-a000224').resolve()
PROPOSAL=BASE/'proposals/a000-existing75-completed-owned-output-LZX-preparation-20261005.json'

def metadata(proposal):
    path=BASE/'assess_completed_own_artifact_storage_readonly.py'
    assert sha(path)==proposal['native_metadata_helper_sha256']
    prefix,marker,_=path.read_text(encoding='utf8').partition('before_processes=process_snapshot()');assert marker
    ns={'__file__':str(path),'__name__':'reviewed_native_metadata_definitions_only'}
    exec(compile(prefix,str(path),'exec'),ns)
    return ns['native_metadata']

def same_identity(a,b):
    return all(a[k]==b[k] for k in ('volume_serial','file_index_high','file_index_low','link_count','last_write_FILETIME','logical_bytes'))

def check_frozen(proposal):
    for path,h in proposal['protected_frozen_input_bindings'].items():assert sha(path)==h,path

def check_target(native,target_row):
    p=Path(target_row['file']).resolve()
    assert p.is_relative_to(STAGE) and p.suffix=='.olean' and not p.is_symlink()
    now=native(p);w=wof_info(p);read=read_and_mmap(p)
    assert same_identity(now,target_row['native_before'])
    assert read['ordinary_read_sha256']==target_row['content_sha256']
    assert now['link_count']==1 and now['FILE_ATTRIBUTE_COMPRESSED'] and not now['FILE_ATTRIBUTE_ENCRYPTED'] and not now['FILE_ATTRIBUTE_REPARSE_POINT']
    assert not w['external']
    return p,now,w,read

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--root-approval-file',required=True);parser.add_argument('--root-approval-sha256',required=True)
    args=parser.parse_args();ap=Path(args.root_approval_file).resolve()
    assert ap.is_relative_to(BASE) and sha(ap)==args.root_approval_sha256
    a=json.loads(ap.read_bytes());self_sha=sha(__file__)
    assert a['status']=='ROOT_APPROVED_EXACT_EXISTING_A00075_COMPLETED_OWN_OUTPUTS_LZX'
    assert a['helper_sha256']==self_sha and a['proposal_sha256']==sha(PROPOSAL)
    p=json.loads(PROPOSAL.read_bytes())
    assert p['helper_sha256']==self_sha
    core=BASE/'a000_owned_storage_guard_prepared.py'
    assert sha(core)==p['guard_core_sha256']==a['guard_core_sha256']
    assert a['target_count']==75 and a['Part0033_already_WOF_target_excluded'] is True
    assert a['sources_receipts_runtime_providers_never_modified'] is True
    check_frozen(p);native=metadata(p)
    targets=p['exact75_remaining_completed_owned_targets']
    assert len(targets)==len({r['file'] for r in targets})==75
    skipped=p['already_WOF_pilot_output_NOT_A_TARGET']
    assert skipped['file'] not in {r['file'] for r in targets}
    skip_path=Path(skipped['file']).resolve();skip_now=native(skip_path);skip_wof=wof_info(skip_path);skip_read=read_and_mmap(skip_path)
    assert same_identity(skip_now,skipped['native_current']) and skip_wof==skipped['WOF_current']
    assert skip_read['ordinary_read_sha256']==skipped['content_sha256'] and skip_wof['external'] and skip_wof['provider']==2 and skip_wof['algorithm']==1
    compact=Path(os.environ['SystemRoot'])/'System32/compact.exe';assert sha(compact)==p['compact_executable_sha256']
    commands=[[str(compact),'/C','/F','/Q','/EXE:LZX',r['file']] for r in targets]
    assert commands==a['exact_reviewed_commands']
    quiescence(0)
    # Existing A000 source replay byte lock is held without writing its bytes.
    replay_path=STAGE/'.fresh-replay.lock';assert replay_path.is_file() and replay_path.stat().st_size==1
    replay=replay_path.open('r+b');replay.seek(0)
    try:msvcrt.locking(replay.fileno(),msvcrt.LK_NBLCK,1)
    except OSError:
        replay.close();raise RuntimeError('A000 source dispatcher still owns the replay lock')
    K.CreateMutexW.argtypes=[ctypes.c_void_p,W.BOOL,W.LPCWSTR];K.CreateMutexW.restype=W.HANDLE
    mutex=None
    try:
        mutex=K.CreateMutexW(None,True,'Local\\OpenMathSingleCompletedOutputStoragePilot')
        assert mutex and ctypes.get_last_error()!=183,'Another own-output compressor is active'
        # Rehash/check all exact target identities before the first mutation.
        for target in targets:check_target(native,target)
        check_frozen(p);quiescence(0)
        serial=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        history=BASE/'operational_history/a000-existing75-storage';history.mkdir(exist_ok=True)
        log=history/(serial+'-per-file-actual.jsonl')
        assert not log.exists()
        record={'status':'STARTED_EXACT75_A000_COMPLETED_OWN_OUTPUT_STORAGE_PASS','started_utc':stamp(),
            'helper_sha256':self_sha,'guard_core_sha256':sha(core),'proposal_sha256':sha(PROPOSAL),
            'root_approval_file':str(ap),'root_approval_sha256':args.root_approval_sha256,
            'target_count':75,'already_WOF_skipped':skipped,'protected_frozen_input_bindings':p['protected_frozen_input_bindings'],
            'actual_per_file_log':str(log),'actual_commands':commands,'resource_policy':p['resource_policy'],
            'scientific_source_or_historical_proof_receipt_targets':0}
        write_new(history/(serial+'-started.json'),record)
        rows=[];stop=None
        with log.open('x',encoding='utf8',newline='\n') as stream:
            for index,(target,command) in enumerate(zip(targets,commands)):
                path,before,wb,read_before=check_target(native,target)
                gates(path);quiescence(0);check_frozen(p)
                result=guarded_compact(command,serial+'-A000-existing75-'+str(index),path,0)
                after=native(path);wa=wof_info(path);read_after=read_and_mmap(path)
                same=same_identity(before,after) and read_after['ordinary_read_sha256']==target['content_sha256']
                good=result.get('exit')==0 and not result.get('stop_reason') and same and wa['external'] and wa['provider']==2 and wa['algorithm']==1
                row={'index':index,'module':target['source_module'],'file':str(path),
                    'status':'PASS_BYTE_IDENTICAL_A000_COMPLETED_OWN_OUTPUT_LZX' if good else 'STORAGE_REVIEW_REQUIRED_NO_PROOF_FAILURE_INFERENCE',
                    'native_before':before,'WOF_before':wb,'read_and_mmap_before':read_before,
                    'actual_command_row':result,'native_after':after,'WOF_after':wa,'read_and_mmap_after':read_after,
                    'content_inode_linkcount_size_mtime_preserved':same,
                    'actual_allocation_bytes_saved':before['standard_allocation_bytes']-after['standard_allocation_bytes']}
                stream.write(json.dumps(row)+'\n');stream.flush();rows.append(row)
                check_frozen(p)
                if not good:stop='CURRENT_FILE_OPERATIONAL_REVIEW_REQUIRED';break
        successful=len(rows)==75 and all(r['status'].startswith('PASS_') for r in rows)
        record.update(status='PASS_EXACT75_A000_OWN_OUTPUTS_BYTE_IDENTICAL_LZX_NO_PROOF_CHANGE' if successful else 'A000_STORAGE_PASS_CHECKPOINT_REVIEW_REQUIRED',
            finished_utc=stamp(),completed_storage_files=len(rows),actual_allocation_bytes_saved=sum(r['actual_allocation_bytes_saved'] for r in rows),
            stop_reason=stop,actual_per_file_log_sha256=sha(log),all_protected_source_receipt_runtime_provider_bytes_preserved=True)
        write_new(history/(serial+'-actual.json'),record)
        print(json.dumps({'status':record['status'],'record':str(history/(serial+'-actual.json')),'sha256':sha(history/(serial+'-actual.json')),'storage_files':len(rows),'actual_allocation_bytes_saved':record['actual_allocation_bytes_saved']}))
    finally:
        if mutex:
            K.ReleaseMutex.argtypes=[W.HANDLE];K.ReleaseMutex.restype=W.BOOL
            K.ReleaseMutex(mutex);K.CloseHandle(mutex)
        replay.seek(0);msvcrt.locking(replay.fileno(),msvcrt.LK_UNLCK,1);replay.close()

if __name__=='__main__':main()
