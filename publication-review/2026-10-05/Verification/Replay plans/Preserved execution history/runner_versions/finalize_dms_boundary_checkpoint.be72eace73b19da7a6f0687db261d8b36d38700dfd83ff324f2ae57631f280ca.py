"""Explicit operational recovery after the original pending row is flushed.

Preserves both canonical raw receipts and the exact old row.  Only an externally
observed successful, source/hash-matched GPn2T can be retained.  No Lean executes.
"""
from pathlib import Path
import hashlib,json,os,sys,time
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent
def sha(raw):return hashlib.sha256(raw).hexdigest()
assert len(sys.argv)==2,'Provide the reviewed completed boundary receipt'
file=Path(sys.argv[1]).resolve();assert file.is_relative_to(BASE.resolve())
boundary=json.loads(file.read_bytes());assert boundary['status']=='PENDING_ORIGINAL_ROW_FLUSHED_OS_REFUSED_NEXT_CHILD'
hold_file=Path(boundary['hold_receipt']);hold_raw=hold_file.read_bytes();hold=json.loads(hold_raw)
assert sha(hold_raw)==boundary['hold_sha256'] and hold['actual_child_exit']==0
main=BASE/'htpeo-dms-current-fresh-build.json';raw=read_bytes_shared(main);doc=json.loads(raw)
assert sha(raw)==boundary['after_receipt_sha256'] and doc['status']=='RUNNING'
assert len(doc['builds'])==118
prior=json.loads(Path(boundary['original_receipt']).read_bytes())
assert doc['builds'][:117]==prior['builds']
row=doc['builds'][-1];assert row==boundary['flushed_row'] and row['module']=='GPn2T' and row['exit']==0
assert row.get('stop_reason') is None,'This review authorizes only the actual exit0 row without a stop reason'
assert row['source_sha256']==hold['source']['sha256']==sha(Path(hold['source']['file']).read_bytes())
for artifact in row['artifacts']:
    assert sha(Path(artifact['file']).read_bytes())==artifact['sha256']
out=BASE/('dms-boundary-checkpoint-normalization-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'.json')
preserved=out.with_suffix('.original-running-receipt.json');assert not preserved.exists();preserved.write_bytes(raw)
original_row=json.loads(json.dumps(row))
row['external_scheduled_hold_qualification']={'original_row':original_row,'hold_receipt':str(hold_file),
 'hold_sha256':sha(hold_raw),'externally_observed_actual_child_exit':0,
 'actual_child_exit_observed_utc':hold['actual_child_exit_observed_utc'],
 'held_wall_seconds':boundary['held_wall_seconds'],
 'qualification':'The caller wall time includes a coordinator-authorized main-thread hold after actual source exit0; it is not source CPU or source execution wall time.'}
doc['status']='SCHEDULED_RESOURCE_CHECKPOINT'
doc['checkpoint_reason']='ORIGINAL_BUFFERED_SOURCE_ROW_FLUSHED_OS_PROCESS_LIMIT_REFUSED_NEXT_CHILD_BEFORE_EXECUTION'
doc['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
doc['source_boundary_handoff']={'boundary_receipt':str(file),'sha256':sha(file.read_bytes()),
 'preserved_original_running_receipt':str(preserved),'sha256_original_running_receipt':sha(raw),
 'normalization_receipt':str(out),'unattempted_next_module':doc.get('current_module'),
 'qualification':'Dispatcher operational refusal is a scheduled resource handoff. No next source compiler executed; no mathematical failure is inferred.'}
new=json.dumps(doc,indent=2).encode('utf8');tmp=main.with_suffix('.json.tmp')
tmp.write_bytes(new);os.replace(tmp,main)
evidence={'status':'OPERATIONAL_CHECKPOINT_RECOVERED_NO_LEAN_INVOCATION','original_running_receipt':str(preserved),
 'original_running_receipt_sha256':sha(raw),'new_checkpoint_receipt':str(main),'new_checkpoint_sha256':sha(new),
 'original_pending_row':original_row,'boundary_receipt':str(file),'boundary_receipt_sha256':sha(file.read_bytes()),
 'source_exit_basis':'Externally observed actual child exit0, exact source SHA and every fresh output hash verified.',
 'retained_actual_source_successes':118,'helper_sha256':sha(Path(__file__).read_bytes())}
assert not out.exists();out.write_text(json.dumps(evidence,indent=2),encoding='utf8')
print(json.dumps({'status':evidence['status'],'receipt':str(out),'retained':118}),flush=True)
