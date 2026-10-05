"""Compact, atomic derived status register; no entrant/source mutation."""
from pathlib import Path
import json,time,os,re,hashlib
from receipt_io import read_json_shared,read_bytes_shared
BASE=Path(__file__).resolve().parent
rows=[];families={}
for file in sorted((BASE/'builds').glob('*/build-plan.json')):
 plan=json.loads(file.read_text(encoding='utf8'));pid=plan['id'];route_id=file.parent.name;receipt=BASE/(route_id+'-fresh-build.json')
 result=read_json_shared(receipt) if receipt.exists() else None
 endpoints=plan.get('endpoints',[])
 if not endpoints and pid=='luke-k4-ramsey-current':
  endpoints=sorted(set(n for m in plan['modules'] if m['module'].startswith('Audits.') for n in re.findall(r'#print\s+axioms\s+(\S+)',Path(m['file']).read_text(encoding='utf8'))))
 row={'id':pid,'route_id':route_id,'entrant':plan.get('entrant'),'version':plan.get('version'),'mathlib_pin':plan.get('mathlib_pin'),
  'source_modules':len(plan['modules']),'selected_endpoints':endpoints,'custom_source_manifest':str(file),
  'status':result['status'] if result else 'PLANNED_NOT_RUN','fresh_receipt':str(receipt) if result else None,
  'completed_invocations':len(result.get('builds',[])) if result else 0,'current_module':result.get('current_module') if result else None,
  'current_modules':result.get('current_modules',[]) if result else [],
  'failed_invocations':result.get('failed_invocations',[]) if result else [],
  'resource_settings':result.get('resource_settings') if result else None,
  'resource_checkpoint_reason':result.get('checkpoint_reason') if result else None,
  'prior_attempt_receipts':result.get('prior_attempt_receipts',[]) if result else [],
  'retained_successful_custom_modules':result.get('retained_successful_custom_modules') if result else None,
  'provenance_qualification':plan.get('dependency_replay_qualification'),'operational_route_qualification':plan.get('operational_difference')}
 if pid=='htpeo-dms-current' and result and result['status']=='RUNNING':
  hold=BASE/'dms-dispatcher-hold-20261005T005041Z.json'
  resume=hold.with_name(hold.stem+'.resumed.json')
  if hold.exists() and not resume.exists() and not list(BASE.glob('dms-boundary-checkpoint-normalization-*.json')):
   evidence=read_json_shared(hold)
   if evidence['status']=='DISPATCHER_HELD_NO_ACTIVE_DMS_SOURCE_CHILD':
    row['external_operational_hold']={'receipt':str(hold),'sha256':hashlib.sha256(read_bytes_shared(hold)).hexdigest(),
     'classification':'GENUINE_COMPLETED_SOURCE_BOUNDARY_DISPATCHER_HOLD',
     'qualification':'Canonical live receipt remains unchanged; the completed child row is still buffered for finalization when the original dispatcher resumes.',
     'pending_completed_source':evidence.get('source'),'actual_child_exit':evidence.get('actual_child_exit')}
    row['canonical_receipt_status']=row['status'];row['status']='SOURCE_BOUNDARY_DISPATCHER_HELD'
 if pid=='htpeo-dms-current' and result and result['status'].startswith('PASS'):
  reparses=sorted(BASE.glob('htpeo-dms-current-corrected-axiom-reparse-*.json'))
  if reparses:
   corrected=read_json_shared(reparses[-1])
   if corrected['original_receipt_sha256']==hashlib.sha256(read_bytes_shared(receipt)).hexdigest():
    row['original_receipt_status']=row['status'];row['status']=corrected['effective_status']
    row['corrected_axiom_reparse_receipt']=str(reparses[-1])
    row['corrected_expected_endpoint_count']=corrected['expected_endpoint_count']
    row['corrected_printed_endpoint_count']=corrected['parsed_selected_endpoint_count']
   else:row['corrected_axiom_reparse_warning']='Original receipt changed; no effective-status override applied'
 families.setdefault(pid,[]).append(row)
for pid,routes in families.items():
 # Operational routes replay the same 51 frozen Luke files, not additional mathematical projects.
 chosen=max(routes,key=lambda r:(bool(r['fresh_receipt']),r['status'].startswith('PASS'),r['route_id'].endswith('-direct')))
 if len(routes)>1:
  chosen=dict(chosen);chosen['routes']=[{'route_id':r['route_id'],'status':r['status'],'fresh_receipt':r['fresh_receipt'],'custom_source_manifest':r['custom_source_manifest'],'operational_route_qualification':r['operational_route_qualification']} for r in routes]
 rows.append(chosen)
chandra=BASE/'chandragupt-pinned-build.json'
if chandra.exists():
 d=read_json_shared(chandra);rows.append({'id':'chandragupt','entrant':'Chandragupt','version':'4.34.1','mathlib_pin':None,
  'status':d.get('status'),'source_modules':len(d['source_sha256']),'selected_endpoints':d['endpoints'],'fresh_receipt':str(chandra),'completed_invocations':len(d['builds'])})
rows.append({'id':'rohith-k61','entrant':'E57 Rohith Poola','status':'NO_LEAN_SOURCE_AVAILABLE',
 'ordinary_exact_certificate_receipt':str(BASE.parents[1]/'judging_audit/independent_kobon_n61.json'),
 'reason':'Frozen formal-proofs file index is empty. Integer homogeneous-intersection geometry recount is a separate verification method.'})
rows.append({'id':'qichao-cerny-scoped-cores','entrant':'E17 Qichao Wang','status':'NO_LEAN_SOURCE_AVAILABLE',
 'reason':'The frozen packet preserves manifests and descriptions, but not the requested27MB source ZIP. Claimed compiler/axiom receipts are historical author evidence, not a fresh replay.'})
register={'updated_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'scope':'All selected novelty-bearing and novelty-adjacent Lean project plans; superseded duplicates explicitly excluded; pending is never pass.',
 'projects':rows,'dependency_caches':[],'resource_receipts':[]}
for name in ('sakana-a000224-third-worker-pilot.json','a000224-third-slot-resource-amendment.json','a000224-matt-fullimport-lease-handoff.json','matt-download-resource-gate-amendment.json','matt-leantar-capabilities.json',
             'future-whole-mathlib-source-scopes.json','full-mathlib-guard-preparation.json','windows-olean-commit-source-review.json',
             'dms-dispatcher-hold-20261005T004939Z.json','dms-dispatcher-hold-20261005T004939Z.aborted.json',
             'dms-dispatcher-hold-20261005T004939Z.source-row-evidence.json','dms-dispatcher-hold-20261005T005041Z.json',
             'dms-dispatcher-hold-20261005T005041Z.resumed.json','dms-held-GPn2T-additional-timing-query-unavailable.json',
             'e169-independent-resource-dag-preparation.json','a000224-literal-whole-import-scope.json',
             'a000224-whole-module-audit-boundary-evidence.json','dms-pending-row-boundary-selftest.json',
             'dms-pending-row-boundary-selftest-v2.json','dms-pending-row-boundary-selftest-v3.json',
             'dms-pending-row-boundary-selftest-v4.json','kobon-e169-serialized-boundary.json',
             'kobon-e169-serialized-boundary.completed.json','a000224-five-whole-module-guard-preparation.json',
             'held-novelty-candidate-source-inventory.json','root-resource-scope-approvals-20261005.json',
             'held-novelty-guarded-adapter-preparation.json','ht-ramsey-mixed-source-boundary-evidence.json',
             'dms-boundary-win32-primary-source-review.json'):
 file=BASE/name
 if file.exists():
  register['resource_receipts'].append({'file':str(file),'sha256':hashlib.sha256(file.read_bytes()).hexdigest()})
for file in sorted(BASE.glob('*-first-granular-pilot.json')):
 register['resource_receipts'].append({'file':str(file),'sha256':hashlib.sha256(file.read_bytes()).hexdigest()})
for pattern in ('dms-pending-row-handoff-*.json','dms-boundary-checkpoint-normalization-*.json'):
 for file in sorted(BASE.glob(pattern)):
  register['resource_receipts'].append({'file':str(file),'sha256':hashlib.sha256(file.read_bytes()).hexdigest()})
for file in sorted((BASE/'native_object_pilots').glob('*/receipt.json')):
 register['resource_receipts'].append({'file':str(file),'sha256':hashlib.sha256(file.read_bytes()).hexdigest()})
for file in sorted(BASE.glob('mathlib-*-cache-*.json')):
 try:d=read_json_shared(file)
 except (json.JSONDecodeError,UnicodeDecodeError):continue
 register['dependency_caches'].append({'file':str(file),'version':d.get('version'),'status':d.get('status'),'method':d.get('method'),
  'completed_batches':len(d.get('batches',[])),'official_module_count':d.get('official_module_count')})
out=BASE/'comprehensive-lean-replay-register.json';temp=out.with_suffix('.json.tmp');temp.write_text(json.dumps(register,indent=2),encoding='utf8');os.replace(temp,out)
print(len(rows),'project statuses saved',flush=True)
