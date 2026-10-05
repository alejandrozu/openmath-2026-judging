"""Compact, atomic derived status register; no entrant/source mutation."""


from pathlib import Path


import json,time,os,re,hashlib


from receipt_io import read_json_shared,read_bytes_shared


BASE=Path(__file__).resolve().parent


# Qualified scientific scopes are additive evidence, never raw-receipt overrides.
import sys
sys.path.insert(0,str(BASE.parent))
SUMMARY_SOURCE_SHA256=hashlib.sha256((BASE.parent/'verification_summary.py').read_bytes()).hexdigest()
assert SUMMARY_SOURCE_SHA256=='1112c4eac5ef1dffceb692ee3f67bc14093a5fd321f1838ed9daae3845d406f3'
from verification_summary import qualified_dms_composite_route

def qualified_record(filename,expected_sha):
 path=BASE/filename
 if not path.exists():return None,None
 raw=read_bytes_shared(path);assert hashlib.sha256(raw).hexdigest()==expected_sha
 return json.loads(raw),{'qualification_record':str(path),'qualification_record_sha256':expected_sha}

def standard_selected_scope(records,count):
 assert len(records)==count and len({r['endpoint'] for r in records})==count
 assert all(r['classification']=='STANDARD_KERNEL_AXIOMS' and not r.get('native_axioms') and not r.get('unrecognized_axioms') for r in records)

def actual_qualified_scientific_scopes():
 scopes={}
 dms=qualified_dms_composite_route()
 if dms:
  scopes['htpeo-dms-current']={**dms,'scope_relation':'Separate qualified228-body/123-selected composite; every original and intermediate raw receipt remains unchanged.'}
 q,meta=qualified_record('groth-exact2-source5-completed-qualification-20261005.json','9bc15bcba169f703e53b019ad2adaa7fca3645aaee07aa41a7df9e835ba009e1')
 if q:
  assert q['status']=='PASS_EXACT_UNCHANGED_GROTH2_SOURCE5_SELECTED_OUTPUT_STANDARD_SCOPE'
  assert (q['authored_source_passes'],q['selected_unique_prints'])==(2,5)
  standard_selected_scope(q['actual_selected_axiom_classifications'],5)
  raw=BASE/'sakana-FOCUS-GROTH-fresh-build.json'
  assert hashlib.sha256(read_bytes_shared(raw)).hexdigest()==q['completed_receipt_sha256']
  scopes['sakana-FOCUS-GROTH']={**meta,'family':'FOCUS-GROTH','status':q['status'],'qualified':True,
   'scientific_body_scope_complete':True,'selected_endpoint_scope_complete':True,
   'scientific_body_count':2,'selected_endpoint_count':5,'selected_classification_counts':{'STANDARD_KERNEL_AXIOMS':5},
   'completed_raw_receipt_sha256':q['completed_receipt_sha256'],'scope_relation':'Exact unchanged two-source/five-selected restricted-upper-bound scope.',
   'mathematical_scope':q['scientific_scope'],'novelty_or_scoring_or_publication_upgrade_implied':False}
 q,meta=qualified_record('e169-tactic-specific-v2-completed-qualification.json','57c466bc581ab50ab62c9fefeadc0a0a6637aee19c5151c652f387dfea56709d')
 if q:
  assert q['status']=='PASS_BODY_IDENTICAL_IMPORT_ONLY_ROUTE_SELECTED_ENDPOINT_STANDARD_AXIOMS'
  assert (q['authored_source_modules_passed'],q['selected_endpoint_prints'])==(22,1)
  assert len(q['scientific_body_identity_checks'])==22 and all(r['scientific_body_options_comments_identical'] for r in q['scientific_body_identity_checks'])
  standard_selected_scope(q['actual_selected_axiom_review'],1)
  assert hashlib.sha256(read_bytes_shared(Path(q['receipt']))).hexdigest()==q['receipt_sha256']
  scopes['sakana-erdos169-fourap']={**meta,'family':'erdos169-fourap','status':q['status'],'qualified':True,
   'scientific_body_scope_complete':True,'selected_endpoint_scope_complete':True,
   'scientific_body_count':22,'selected_endpoint_count':1,'selected_classification_counts':{'STANDARD_KERNEL_AXIOMS':1},
   'completed_alternative_receipt_sha256':q['receipt_sha256'],'scope_relation':q['qualification'],
   'original_raw_receipt_replaced':False,'novelty_or_scoring_or_publication_upgrade_implied':False}
 q,meta=qualified_record('focus-matrix-three-seed-completed-artifact-roots-qualified-20261005.json','4337a4f479fb2e6ef9436a7e7533797070de4b525a5642f8cde1b545803d4703')
 if q:
  assert q['status']=='PASS_EXACT_THREE_SEED_213_SOURCE_18_STANDARD_SELECTED_ENDPOINT_SCOPE'
  assert (q['authored_sources_passed'],q['requested_selected_prints_passed'],q['selected_native_admitted_unknown_axioms'])==(213,18,0)
  assert len(q['projects'])==3 and sum(r['source_count'] for r in q['projects'])==213
  for seed in q['projects']:
   assert hashlib.sha256(read_bytes_shared(Path(seed['receipt']))).hexdigest()==seed['receipt_sha256']
   selected=[r for a in seed['actual_selected_audits'] for r in a['six_actual_selected_prints']]
   standard_selected_scope(selected,6)
   scopes[seed['project_id']]={**meta,'family':'FOCUS-MATRIX','status':q['status'],'qualified':True,
    'scientific_body_scope_complete':True,'selected_endpoint_scope_complete':True,
    'scientific_body_count':71,'selected_endpoint_count':6,'selected_classification_counts':{'STANDARD_KERNEL_AXIOMS':6},
    'three_seed_family_source_count':213,'three_seed_family_selected_print_count':18,
    'seed':seed['seed'],'completed_raw_receipt_sha256':seed['receipt_sha256'],
    'scope_relation':'Exact unchanged selected six endpoints for this seed; total three-seed family213/18.',
    'mathematical_scope':q['scoped_conclusion'],'novelty_or_scoring_or_publication_upgrade_implied':False}
 q,meta=qualified_record('root-HTM2-granular101-three-new-four-standard-qualified-20261005.json','ede28ac93ddfcae456936231e86b4f3c1db3a0d333e1b363b78e16061f9aa90e')
 if q:
  assert q['status']=='ROOT_QUALIFIED_HTM2_EXACT_GRANULAR101_SOURCES_97_PRIOR_DMS_ONE_PRIOR_OWN_THREE_NEW_AND_FOUR_STANDARD_SELECTED'
  assert (q['body_count_covered'],q['prior_owned_DMS97'],q['prior_owned_M2_StarCore1'],q['new_cold_source_passes'],q['actual_selected_prints'])==(101,97,1,3,4)
  assert q['full122_project_qualified'] is False and q['whole21_and_selected33_deferred'] is True
  standard_selected_scope(q['actual_selected_classifications'],4)
  assert hashlib.sha256(read_bytes_shared(Path(q['receipt_file']))).hexdigest()==q['receipt_sha256']
  linked=read_json_shared(Path(q['receipt_file']))
  assert linked['source_plan_sha256']==q['source_plan_sha256']
  assert q['all_four_raw_CLI_guard_log_source_output_hashes_checked'] is True and q['all122_source_hashes_checked'] is True
  scopes['htpeo-erdos-m2']={**meta,'family':'HTPeo-M2','status':q['status'],'qualified':True,
   'scientific_body_scope_complete':False,'selected_endpoint_scope_complete':False,
   'qualified_granular_subscope_complete':True,'qualified_selected_endpoint_subscope_complete':True,
   'scientific_body_count':101,'full_project_scientific_body_count':122,
   'prior_owned_DMS_source_passes':97,'prior_owned_M2_StarCore_source_passes':1,'new_cold_source_passes':3,
   'selected_endpoint_count':4,'full_project_selected_endpoint_count':37,
   'selected_classification_counts':{'STANDARD_KERNEL_AXIOMS':4},
   'whole_source_modules_deferred':21,'other_selected_endpoint_prints_deferred':33,
   'actual_linked_granular_receipt':q['receipt_file'],'actual_linked_granular_receipt_sha256':q['receipt_sha256'],
   'source_plan_sha256':q['source_plan_sha256'],'seed_receipt_sha256':q['seed_receipt_sha256'],
   'scope_relation':'Only exact granular101/122 bodies and four selected outputs are qualified:97 earlier DMS-owned passes,one earlier M2-owned StarCore pass,three new checks. Whole21 and33 other selected outputs remain unattempted. The default full-route status is unchanged.',
   'full_project_qualified':False,'original_raw_receipt_replaced':False,'novelty_or_scoring_or_publication_upgrade_implied':False}
 return scopes

qualified_scopes=actual_qualified_scientific_scopes()

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


 if pid in qualified_scopes:
  chosen=dict(chosen);chosen['qualified_scientific_scope']=qualified_scopes[pid]
  chosen['effective_scientific_scope_status']='QUALIFIED_SELECTED_SCIENTIFIC_SCOPE' if qualified_scopes[pid]['scientific_body_scope_complete'] else 'PARTIALLY_QUALIFIED_GRANULAR_SCIENTIFIC_SCOPE'
  chosen['raw_execution_status_preserved']=chosen['status']
  chosen['qualified_selected_endpoint_coverage']={'status':'PASS_FROM_ACTUAL_COMPLETED_QUALIFICATION' if qualified_scopes[pid]['selected_endpoint_scope_complete'] else 'PASS_FROM_COMPLETED_GRANULAR_SUBSCOPE_QUALIFICATION_FULL_SCOPE_PENDING',
   'requested_and_actual_count':qualified_scopes[pid]['selected_endpoint_count'],
   'classification_counts':qualified_scopes[pid]['selected_classification_counts'],
   'qualification_record_sha256':qualified_scopes[pid]['qualification_record_sha256']}
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


register['qualified_scientific_scope_metadata']={'summary_helper_source_sha256':SUMMARY_SOURCE_SHA256,
 'policy':'Separate actual qualification metadata; raw statuses/failures/resource checkpoints and intermediate routes remain unchanged. No novelty or general-conjecture promotion.',
 'projects':qualified_scopes}

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


for pattern in ('dms-pending-row-handoff-*.json','dms-boundary-checkpoint-normalization-*.json',

                'dms-sole-guarded-dispatch-*.json','dms-sole-first-dispatch-*.json','main-whole-lease-boundary-*.json',
                'dms-119-waiting-boundary-*.json','dms-sole-post-first-pass-no-attempt-*.json',
                'm2-novel-formalization-source-scope-inventory-*.json', 'dms-full228-*.json',
                'dms-gpn2-import-only-*.json', 'main-complete-family-resource-snapshot-*.json',
                'main-queue-hold-for-e169-v2-*.json', 'dms-original119-*.json', 'dms-original99-*.json',
                'dms-modeq-v2-*.json', 'dms-modeq-import-revision-*.json', 'dms-v3-*.json'):
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


