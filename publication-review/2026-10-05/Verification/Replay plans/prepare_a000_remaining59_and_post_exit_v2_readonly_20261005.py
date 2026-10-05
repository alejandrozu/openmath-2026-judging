"""Prepare reviewed-current-state storage classifications/copies, apply no mutator."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json,os
from a000_owned_storage_guard_prepared import wof_info,read_and_mmap,quiescence

V=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def write(p,d):
 with Path(p).open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')
def clone(oldpath,newpath,replacements,diffpath):
 old=oldpath.read_text(encoding='utf8');new=old
 for before,after in replacements:
  assert before in new,(oldpath,before);new=new.replace(before,after)
 ast.parse(new)
 with newpath.open('x',encoding='utf8',newline='\n') as f:f.write(new)
 with diffpath.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=oldpath.name+'-'+sha(oldpath),tofile=newpath.name))
 return new
oldp=V/'proposals/a000-existing75-completed-owned-output-LZX-preparation-20261005.json'
assert sha(oldp)=='be1752cdbab5df645ec6520aa11c84782b758ee44849c63396e6b6c404d97484'
p=json.loads(oldp.read_bytes())
actual=V/'operational_history/a000-existing75-storage/20261005T055502130295Z-actual.json'
logs=V/'operational_history/a000-existing75-storage/20261005T055502130295Z-per-file-actual.jsonl'
assert sha(logs)=='b56c578c3575a07b865ed8f12227c1e08e1a0be5f6241831a5dda84e08fc337f'
a=json.loads(actual.read_bytes());rows=[json.loads(s) for s in logs.read_text().splitlines()]
assert len(rows)==16 and a['completed_storage_files']==16 and a['actual_per_file_log_sha256']==sha(logs)
assert sha(actual).startswith('327a8095')
meta=V/'assess_completed_own_artifact_storage_readonly.py'
prefix,marker,_=meta.read_text(encoding='utf8').partition('before_processes=process_snapshot()');assert marker
ns={'__file__':str(meta),'__name__':'reviewed_native_metadata_definitions_only'};exec(compile(prefix,str(meta),'exec'),ns);native=ns['native_metadata']
quiescence(0)
handled=[];classes=[]
for r in rows:
 now=native(r['file']);w=wof_info(r['file']);read=read_and_mmap(r['file'])
 assert now==r['native_after'] and w==r['WOF_after'] and read==r['read_and_mmap_after']
 assert r['content_inode_linkcount_size_mtime_preserved'] and r['actual_command_row']['exit']==0 and not r['actual_command_row']['stop_reason']
 assert now['standard_allocation_bytes']<=r['native_before']['standard_allocation_bytes']
 for ch in ['stdout','stderr']:
  assert sha(r['actual_command_row'][ch+'_file'])==r['actual_command_row'][ch+'_sha256']
 category='PASS_BYTE_IDENTICAL_WOF_LZX_NONINCREASING_ALLOCATION' if w['external'] and w['provider']==2 and w['algorithm']==1 else 'PASS_BYTE_IDENTICAL_ORDINARY_NON_WOF_NONINCREASING_ALLOCATION'
 assert category.startswith('PASS_')
 classes.append({'module':r['module'],'historical_status_unchanged':r['status'],'additive_storage_only_classification':category,'allocation_saved_bytes':r['actual_allocation_bytes_saved'],'WOF_LZX_installed':w['external'],'proof_status_changed':False})
 handled.append({'file':r['file'],'source_module':r['module'],'content_sha256':read['ordinary_read_sha256'],'native_current':now,'WOF_current':w,'read_and_mmap_current':read,'additive_storage_classification':category,'never_targeted_by_remaining59':True})
pilot=p['already_WOF_pilot_output_NOT_A_TARGET'];handled.append(pilot)
last=classes[-1];assert last['allocation_saved_bytes']==0 and not last['WOF_LZX_installed']
classification={'status':'ADDITIVE_ACTUAL_STORAGE_ONLY_CLASSIFICATION_NO_PROOF_STATUS_CHANGE','created_utc':datetime.now(timezone.utc).isoformat(),
 'original_actual_receipt':str(actual),'original_actual_receipt_sha256':sha(actual),'original_JSONL':str(logs),'original_JSONL_sha256':sha(logs),
 'actual_classifications':classes,'counts':{'WOF_LZX':15,'ordinary_non_WOF_no_savings':1},
 'small_file_conclusion':'CertificateP31.olean retains all1568 logical bytes, SHA/mmap/inode/linkcount1/mtime, compactexit0 and4096 allocated bytes; ordinary compressionformat2 became0 with noWOF installed. This successful unchanged/nonincreasing storage result has zero measured savings and no proof-status implication.',
 'historical_record_helper_or_proof_receipt_modified':False}
cp=V/'proposals/a000-existing75-actual16-additive-storage-classification-20261005.json';write(cp,classification)
remaining=[r for r in p['exact75_remaining_completed_owned_targets'] if r['file'] not in {x['file'] for x in handled}]
assert len(remaining)==59 and len(handled)==17
for r in remaining:
 assert native(r['file'])==r['native_before'] and wof_info(r['file'])==r['WOF_before'] and read_and_mmap(r['file'])==r['read_and_mmap_before']
oldh=V/'compress_a000_existing75_owned_outputs_prepared.py';assert sha(oldh)=='8570d49698c6d2595559297a47d21e9f6bb9b509ad6d88ea67b7a44c98f24704'
newh=V/'compress_a000_remaining59_owned_outputs_v2_prepared.py';diff=V/'proposals/a000-remaining59-storage-v2-full-helper-diff-20261005.diff'
skip_old="""    skipped=p['already_WOF_pilot_output_NOT_A_TARGET']
    assert skipped['file'] not in {r['file'] for r in targets}
    skip_path=Path(skipped['file']).resolve();skip_now=native(skip_path);skip_wof=wof_info(skip_path);skip_read=read_and_mmap(skip_path)
    assert same_identity(skip_now,skipped['native_current']) and skip_wof==skipped['WOF_current']
    assert skip_read['ordinary_read_sha256']==skipped['content_sha256'] and skip_wof['external'] and skip_wof['provider']==2 and skip_wof['algorithm']==1
"""
skip_new="""    skipped=p['already_handled17_outputs_NOT_TARGETS']
    assert len(skipped)==17
    for done in skipped:
        assert done['file'] not in {r['file'] for r in targets}
        skip_path=Path(done['file']).resolve();skip_now=native(skip_path);skip_wof=wof_info(skip_path);skip_read=read_and_mmap(skip_path)
        assert same_identity(skip_now,done['native_current']) and skip_wof==done['WOF_current']
        assert skip_read['ordinary_read_sha256']==done['content_sha256']
"""
old_good="good=result.get('exit')==0 and not result.get('stop_reason') and same and wa['external'] and wa['provider']==2 and wa['algorithm']==1"
new_good="""backing_lzx=wa['external'] and wa['provider']==2 and wa['algorithm']==1
                backing_ordinary=not wa['external'] and not after['FILE_ATTRIBUTE_REPARSE_POINT'] and not after['FILE_ATTRIBUTE_ENCRYPTED']
                allocation_nonincreasing=after['standard_allocation_bytes']<=before['standard_allocation_bytes']
                good=result.get('exit')==0 and not result.get('stop_reason') and same and allocation_nonincreasing and (backing_lzx or backing_ordinary)
                actual_storage_class='PASS_BYTE_IDENTICAL_WOF_LZX_NONINCREASING_ALLOCATION' if good and backing_lzx else ('PASS_BYTE_IDENTICAL_ORDINARY_NON_WOF_NONINCREASING_ALLOCATION' if good else 'STORAGE_REVIEW_REQUIRED_NO_PROOF_FAILURE_INFERENCE')"""
clone(oldh,newh,[
 ('a000-existing75-completed-owned-output-LZX-preparation-20261005.json','a000-remaining59-completed-owned-output-storage-v2-preparation-20261005.json'),
 ('ROOT_APPROVED_EXACT_EXISTING_A00075_COMPLETED_OWN_OUTPUTS_LZX','ROOT_APPROVED_EXACT_REMAINING_A00059_COMPLETED_OWN_OUTPUTS_STORAGE_V2'),
 ("a['Part0033_already_WOF_target_excluded'] is True","a['all17_previously_handled_outputs_excluded'] is True"),
 ("p['exact75_remaining_completed_owned_targets']","p['exact59_remaining_completed_owned_targets']"),
 (skip_old,skip_new),(old_good,new_good),
 ("'status':'PASS_BYTE_IDENTICAL_A000_COMPLETED_OWN_OUTPUT_LZX' if good else 'STORAGE_REVIEW_REQUIRED_NO_PROOF_FAILURE_INFERENCE'","'status':actual_storage_class,'WOF_LZX_installed':bool(backing_lzx),'allocation_nonincreasing':allocation_nonincreasing"),
 ('EXACT75','EXACT59'),('EXACT75','EXACT59') if False else ('==75','==59'),
 ('target_count\':75','target_count\':59'),('a000-existing75-storage','a000-remaining59-storage-v2'),
 ('A000-existing75-','A000-remaining59-v2-'),('PASS_EXACT59_A000_OWN_OUTPUTS_BYTE_IDENTICAL_LZX_NO_PROOF_CHANGE','PASS_EXACT59_A000_OWN_OUTPUTS_BYTE_IDENTICAL_STORAGE_CLASSES_NO_PROOF_CHANGE')],diff)
newp=dict(p)
for key in ['exact75_remaining_completed_owned_targets','already_WOF_pilot_output_NOT_A_TARGET','future_root_approval_fields']:newp.pop(key)
newp.update(status='PREPARED_ONLY_EXACT59_REMAINING_OWN_A000_STORAGE_V2_NO_EXECUTION',created_utc=datetime.now(timezone.utc).isoformat(),
 helper=str(newh),helper_sha256=sha(newh),exact59_remaining_completed_owned_targets=remaining,already_handled17_outputs_NOT_TARGETS=handled,
 full_helper_diff=str(diff),full_helper_diff_sha256=sha(diff),preserved_previous75_proposal_sha256=sha(oldp),preserved_previous75_helper_sha256=sha(oldh),
 actual16_additive_classification=str(cp),actual16_additive_classification_sha256=sha(cp),
 actual_success_contract='compactexit0, noresource stop, exactSHA/mmap/IDs/linkcount1/mtime and nonincreasing allocation; distinguish WOFprovider2algorithm1 from ordinary nonWOF without asserting WOF or savings when absent.')
newp['protected_frozen_input_bindings']=dict(p['protected_frozen_input_bindings']);newp['protected_frozen_input_bindings'].update({str(actual):sha(actual),str(logs):sha(logs),str(cp):sha(cp)})
compact=Path(os.environ['SystemRoot'])/'System32/compact.exe'
commands=[[str(compact),'/C','/F','/Q','/EXE:LZX',r['file']] for r in remaining]
newp['exact_future_commands_not_executed']=commands
newp['future_root_approval_fields']={'status':'ROOT_APPROVED_EXACT_REMAINING_A00059_COMPLETED_OWN_OUTPUTS_STORAGE_V2','helper_sha256':sha(newh),'guard_core_sha256':p['guard_core_sha256'],'proposal_sha256':'ROOT_BINDS_COMPLETE_NEW59_PROPOSAL_SHA','target_count':59,'all17_previously_handled_outputs_excluded':True,'sources_receipts_runtime_providers_never_modified':True,'exact_reviewed_commands':commands}
newp['target_storage_totals']={'logical_bytes':sum(r['native_before']['logical_bytes'] for r in remaining),'standard_allocation_bytes':sum(r['native_before']['standard_allocation_bytes'] for r in remaining)}
np=V/'proposals/a000-remaining59-completed-owned-output-storage-v2-preparation-20261005.json';write(np,newp)

# The future interface gets the same explicit result classification; old copies stay intact.
oi=V/'a000_post_exit_lzx_interface_prepared.py';ni=V/'a000_post_exit_lzx_interface_v2_prepared.py'
idiff=V/'proposals/a000-post-exit-interface-v2-full-diff-20261005.diff'
old_success="successful=result.get('exit')==0 and not result.get('stop_reason') and same and wa['external'] and wa['provider']==2 and wa['algorithm']==1"
new_success="""backing_lzx=wa['external'] and wa['provider']==2 and wa['algorithm']==1
        backing_ordinary=not wa['external'] and not after['FILE_ATTRIBUTE_REPARSE_POINT'] and not after['FILE_ATTRIBUTE_ENCRYPTED']
        allocation_nonincreasing=after['standard_allocation_bytes']<=before['standard_allocation_bytes']
        successful=result.get('exit')==0 and not result.get('stop_reason') and same and allocation_nonincreasing and (backing_lzx or backing_ordinary)
        actual_storage_class='PASS_BYTE_IDENTICAL_A000_POST_EXIT_WOF_LZX' if successful and backing_lzx else ('PASS_BYTE_IDENTICAL_A000_POST_EXIT_ORDINARY_NON_WOF_NONINCREASING_ALLOCATION' if successful else 'STORAGE_OPERATION_REVIEW_REQUIRED_PRESERVE_SOURCE_PASS')"""
clone(oi,ni,[('a000-post-exit-owned-artifact-lzx-interface-preparation-20261005.json','a000-post-exit-owned-artifact-storage-interface-v2-preparation-20261005.json'),(old_success,new_success),("status='PASS_BYTE_IDENTICAL_A000_POST_EXIT_OWN_OUTPUT_LZX' if successful else 'STORAGE_OPERATION_REVIEW_REQUIRED_PRESERVE_SOURCE_PASS'","status=actual_storage_class,WOF_LZX_installed=bool(backing_lzx),allocation_nonincreasing=allocation_nonincreasing")],idiff)
orr=V/'run_a000_source_plan_with_post_exit_lzx_prepared.py';nr=V/'run_a000_source_plan_with_post_exit_storage_v2_prepared.py';rdiff=V/'proposals/a000-post-exit-runner-v2-full-diff-20261005.diff'
clone(orr,nr,[('a000-post-exit-owned-artifact-lzx-interface-preparation-20261005.json','a000-post-exit-owned-artifact-storage-interface-v2-preparation-20261005.json'),('a000_post_exit_lzx_interface_prepared','a000_post_exit_lzx_interface_v2_prepared')],rdiff)
ospec=V/'proposals/a000-post-exit-owned-artifact-lzx-interface-preparation-20261005.json';s=json.loads(ospec.read_bytes())
assert sha(ospec)=='c4ed8eb74f6e1cffcf3f00f572ee20fcd13b03318a5277955663406d398e5f6b'
s.update(status='PREPARED_ONLY_SEPARATE_A000_POST_EXIT_STORAGE_V2_INTERFACE_AND_RUNNER_NO_EXECUTION',created_utc=datetime.now(timezone.utc).isoformat(),
 interface=str(ni),interface_sha256=sha(ni),prepared_runner=str(nr),prepared_runner_sha256=sha(nr),
 full_interface_v2_diff=str(idiff),full_interface_v2_diff_sha256=sha(idiff),full_runner_v2_diff=str(rdiff),full_runner_v2_diff_sha256=sha(rdiff),
 preserved_old_interface_sha256=sha(oi),preserved_old_runner_sha256=sha(orr),preserved_old_spec_sha256=sha(ospec),
 additive_actual16_storage_classification=str(cp),additive_actual16_storage_classification_sha256=sha(cp),
 actual_storage_success_classes=['PASS_BYTE_IDENTICAL_A000_POST_EXIT_WOF_LZX','PASS_BYTE_IDENTICAL_A000_POST_EXIT_ORDINARY_NON_WOF_NONINCREASING_ALLOCATION'],
 mutable_future_canonical_source_receipt_NOT_frozen_across_iterations=True,
 immutable_original76_copy_is_frozen=True,
 dynamic_receipt_contract='For each new completed source separately, bind its then-current canonical receipt SHA; read it unchanged during only that synchronous storage callback. Do not include the live canonical receipt in permanent protected_frozen_input_bindings. Only the immutable76copy remains permanently bound.')
assert not any(Path(path).name=='sakana-a000224-fresh-build.json' for path in s['protected_frozen_input_bindings'])
s['future_root_approval_fields'].update(interface_sha256=sha(ni),runner_sha256=sha(nr),specification_sha256='ROOT_BINDS_NEW_V2_COMPLETE_SPEC_SHA')
s['future_granular_command_NOT_AUTHORIZATION'][3]=str(nr)
sp=V/'proposals/a000-post-exit-owned-artifact-storage-interface-v2-preparation-20261005.json';write(sp,s)
for path,h in newp['protected_frozen_input_bindings'].items():assert sha(path)==h,path
print(json.dumps({'classification':{'file':str(cp),'sha256':sha(cp)},'remaining59':{'proposal':str(np),'sha256':sha(np),'helper_sha256':sha(newh),'diff_sha256':sha(diff)},'postexit_v2':{'spec':str(sp),'sha256':sha(sp),'interface_sha256':sha(ni),'runner_sha256':sha(nr),'interface_diff_sha256':sha(idiff),'runner_diff_sha256':sha(rdiff)},'source_or_compact_invocations':0},indent=2))
