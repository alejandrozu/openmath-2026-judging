"""Immutable postprocess for the apostrophe-safe DMS endpoint parser.

No proof invocation or original receipt mutation. Refuses running/incomplete
source attempts; preserves exact original receipt bytes and their SHA-256.
"""
from pathlib import Path
import hashlib,json,re,time
from audit_axioms import parse
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent
receipt=BASE/'htpeo-dms-current-fresh-build.json'
raw=read_bytes_shared(receipt);run=json.loads(raw)
assert run.get('finished_utc') and run['status'].startswith('PASS'),'Await actual completed DMS replay'
planfile=BASE/'builds/htpeo-dms-current/build-plan.json'
plan=json.loads(planfile.read_text(encoding='utf8'))
expected=sorted(set(plan['endpoints']));assert len(expected)==123
audit_names=set(plan['audit_modules'])
audits=[row for row in run['builds'] if row.get('is_endpoint_audit') and row['module'] in audit_names]
assert len(audits)==len(audit_names) and all(row['exit']==0 for row in audits),'Selected audit commands incomplete'
assert not run.get('failed_invocations'),'Original source failures cannot be overridden'
parsed=[]
for row in audits:parsed+=parse(row['stdout'])
by_name={row['endpoint']:row for row in parsed}
missing=sorted(set(expected)-set(by_name))
duplicates=sorted({name for name in by_name if sum(row['endpoint']==name for row in parsed)>1})
selected=[by_name[name] for name in expected if name in by_name]
sorry=[row['endpoint'] for row in selected if row['classification']=='SORRY_ADMISSION']
unknown=[row['endpoint'] for row in selected if row['unrecognized_axioms']]
native=[row['endpoint'] for row in selected if row['native_axioms']]
effective='INCOMPLETE_SELECTED_PRINT_COVERAGE' if missing or duplicates else ('SELECTED_ENDPOINT_USES_SORRY' if sorry else ('SELECTED_ENDPOINT_USES_UNRECOGNIZED_AXIOMS' if unknown else ('PASS_WITH_NATIVE_EVALUATION' if native else 'PASS')))
stamp=time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())
original=BASE/('htpeo-dms-current-original-final-receipt-'+stamp+'.json')
assert not original.exists();original.write_bytes(raw)
record={
 'project':'htpeo-dms-current','method':'REPARSE_ACTUAL_SUCCESSFUL_AUDIT_STDOUT_WITH_APOSTROPHE_SAFE_PARSER_NO_PROOF_RERUN',
 'checked_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
 'original_receipt':str(receipt),'original_receipt_sha256':hashlib.sha256(raw).hexdigest(),
 'immutable_original_receipt_copy':str(original),'original_status':run['status'],
 'source_plan':str(planfile),'source_plan_sha256':hashlib.sha256(planfile.read_bytes()).hexdigest(),
 'parser_file':str(BASE/'audit_axioms.py'),'parser_sha256':hashlib.sha256((BASE/'audit_axioms.py').read_bytes()).hexdigest(),
 'effective_status':effective,'expected_endpoint_count':len(expected),'expected_endpoints':expected,
 'parsed_selected_endpoint_count':len(selected),'missing_expected_endpoints':missing,'duplicated_output_endpoints':duplicates,
 'unexpected_printed_endpoints':sorted(set(by_name)-set(expected)),
 'sorry_endpoints':sorry,'unrecognized_axiom_endpoints':unknown,'native_evaluation_endpoints':native,
 'selected_endpoint_axioms':selected,
 'raw_audit_commands':[{'module':row['module'],'command':row['command'],'exit':row['exit'],'source_sha256':row.get('source_sha256'),'stdout':row['stdout'],'stderr':row['stderr']} for row in audits],
 'qualification':'Native-evaluation source provenance, if any, remains a separate fresh-source audit; no compiled or proof sources were changed.'
}
out=BASE/('htpeo-dms-current-corrected-axiom-reparse-'+stamp+'.json')
assert not out.exists();out.write_text(json.dumps(record,indent=2),encoding='utf8')
print(effective,len(selected),'/',len(expected),str(out),flush=True)
