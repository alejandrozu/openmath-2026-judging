"""Prepare exact remaining HT granular source scope and measured storage/time scenarios."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json,math,shutil,statistics,sys
from lean_imports import read_imports
from full_mathlib_scope import classify
from resource_metrics import snapshot
from pilot_completed_own_output_strong_lzx import metadata,wof_info

BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-ramsey-current'
PLAN=STAGE/'build-plan.json'
PLAN_SHA='94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
OLD=BASE/'run_htpeo_ramsey_supplemented_plan.py'
OLD_SHA='b0293550ae7afaf65c1a0bd03c543d39213de48b4523aa4568547c1a1f78518a'
RECEIPT=BASE/'htpeo-ramsey-current-fresh-build.json'
RECEIPT_SHA='7f615bb0257aa9e56c2088c4fc494f4c66becc82291218d1c18fa2b078a2d39d'
SCOPE=BASE/'htpeo-ramsey-exact2056-granular-continuation-scope-20261005.json'
ADAPTER=BASE/'run_htpeo_ramsey2056_granular_continuation.py'
DIFF=BASE/'htpeo-ramsey2056-granular-continuation-minimal-operational.diff'
PACKET=BASE/'htpeo-ramsey2056-granular-continuation-preparation-20261005.json'
PROJECTION=BASE/'htpeo-ramsey2056-measured-output-storage-time-projection-20261005.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_new(p,d):
    with Path(p).open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')
assert sha(PLAN)==PLAN_SHA and sha(OLD)==OLD_SHA and sha(RECEIPT)==RECEIPT_SHA
plan=json.loads(PLAN.read_bytes());receipt=json.loads(RECEIPT.read_bytes())
assert receipt['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
entries={m['module']:m for m in plan['modules']};assert len(entries)==2103
whole=set(classify(plan)['authored_transitive_whole_Mathlib_closure']);assert len(whole)==11
granular=set(entries)-whole;assert len(granular)==2092
passed={r['module']:r for r in receipt['builds'] if not r['is_endpoint_audit'] and r['exit']==0 and not r.get('stop_reason')}
assert len(passed)==36 and set(passed)<=granular
remaining=granular-set(passed);assert len(remaining)==2056
all_records=[];custom_imports={}
for name,entry in entries.items():
    assert sha(entry['file'])==entry['sha256']
    roots=[r for r in read_imports(entry['file']) if r!='all'];custom_imports[name]=[r for r in roots if r in entries]
    all_records.append({'module':name,'file':entry['file'],'sha256':entry['sha256'],'source_bytes':Path(entry['file']).stat().st_size,'direct_imports':roots})
for name in granular:assert not set(custom_imports[name])&whole,(name,custom_imports[name])
seen=set();order=[]
def visit(n):
    if n in seen:return
    for dep in custom_imports[n]:visit(dep)
    seen.add(n);order.append(n)
for n in entries:visit(n)
ordered=[n for n in order if n in granular]
remaining_order=[n for n in ordered if n in remaining]
assert len(ordered)==2092 and len(remaining_order)==2056
for n,row in passed.items():
    assert row['source_sha256']==entries[n]['sha256']
    for a in row['artifacts']:assert sha(a['file'])==a['sha256']
source_snapshot=BASE/'htpeo-ramsey-original36-calibration-immutable-receipt-20261005.json'
if source_snapshot.exists():assert sha(source_snapshot)==RECEIPT_SHA
else:source_snapshot.write_bytes(RECEIPT.read_bytes())
scope={'status':'PREPARED_ONLY_EXACT_REMAINING2056_GRANULAR_SOURCES_NO_DISPATCH',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),'original_source_plan_sha256':PLAN_SHA,
 'actual36_checkpoint_receipt_sha256':RECEIPT_SHA,'actual36_immutable_receipt':str(source_snapshot),
 'all2103_source_identities':all_records,'granular2092_topological_order':ordered,
 'remaining2056_topological_order':remaining_order,'prior36_own_cold_pass_module_names':sorted(passed),
 'prior36_own_actual_rows':list(passed.values()),'deferred11_whole_source_names':sorted(whole),
 'both_original_and_supplemental_audits_unattempted_by_this_scope':True,
 'all_scientific_sources_source_plan_options_and_original_audit_bytes_unchanged':True,
 'resource_policy':'Unchanged6GiB owned process/job cap; dispatch5GiBcommit/6GiBphysical/4GBdisk; continuous1GiBcommit/3GiBphysical/1GBdisk;-j1;max2actualsource importers.',
 'no_compaction_deletion_output_alias_or_Lean_execution_performed':True}
write_new(SCOPE,scope);scope_sha=sha(SCOPE)
old=OLD.read_text(encoding='utf8');new=old
needle="plan=json.loads((dest/'build-plan.json').read_text())\n";assert new.count(needle)==1
block="""
assert '--exact2056-granular-continuation' in sys.argv[3:]
assert project=='htpeo-ramsey-current' and worker_threads==1 and third_worker_continuation and defer_whole_import_mode
assert not third_worker_pilot and not full_mathlib_source_mode and not independent_resource_mode
ht_scope_flag='--granular-continuation-scope-sha256';assert sys.argv.count(ht_scope_flag)==1
ht_scope_sha=sys.argv[sys.argv.index(ht_scope_flag)+1];assert ht_scope_sha==SCOPE_SHA_PLACEHOLDER
ht_scope_file=BASE/'htpeo-ramsey-exact2056-granular-continuation-scope-20261005.json'
assert hashlib.sha256(ht_scope_file.read_bytes()).hexdigest()==ht_scope_sha
ht_scope=json.loads(ht_scope_file.read_bytes())
assert hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()==ht_scope['original_source_plan_sha256']
assert hashlib.sha256(Path(ht_scope['actual36_immutable_receipt']).read_bytes()).hexdigest()==ht_scope['actual36_checkpoint_receipt_sha256']
ht_actual_modules={r['module']:r for r in plan['modules']}
for record in ht_scope['all2103_source_identities']:
 assert ht_actual_modules[record['module']]['sha256']==record['sha256']==hashlib.sha256(Path(record['file']).read_bytes()).hexdigest()
 assert [n for n in read_imports(record['file']) if n!='all']==record['direct_imports']
plan['exact2056_granular_continuation_policy']={'scope_file':str(ht_scope_file),'scope_sha256':ht_scope_sha,
 'prior36_own_cold_pass_checkpoint_sha256':ht_scope['actual36_checkpoint_receipt_sha256'],
 'remaining2056_scientific_sources':ht_scope['remaining2056_topological_order'],
 'all11whole_sources_and_both_organizer_audits_deferred':True,'source_plan_or_body_changes':False,
 'no_automatic_compression_or_storage_mutation':True}
""".replace('SCOPE_SHA_PLACEHOLDER',repr(scope_sha))
new=new.replace(needle,needle+block,1)
needle="for n in ordered+plan['audit_modules']+plan.get('non_acceptance_audit_modules',[]):\n";assert new.count(needle)==1
new=new.replace(needle,"""assert set(ht_scope['deferred11_whole_source_names'])<=deferred_whole_names
dispatch_order=[n for n in ordered if n not in deferred_whole_names]
assert dispatch_order==ht_scope['granular2092_topological_order'] and len(dispatch_order)==2092
for n in ht_scope['prior36_own_cold_pass_module_names']:
 assert n in retained and retained[n]['exit']==0 and not retained[n].get('stop_reason')
 assert retained[n]['source_sha256']==ht_actual_modules[n]['sha256']
for n in dispatch_order:
""",1)
needle=" if plan['failed_invocations']:plan['status']='BUILD_FAILED_OR_TIMED_OUT'\n";assert new.count(needle)==1
new=new.replace(needle,needle+""" else:
  ht_actual_passes={r['module'] for r in plan['builds'] if r['exit']==0 and not r['is_endpoint_audit'] and not r.get('stop_reason')}
  assert set(ht_scope['granular2092_topological_order'])<=ht_actual_passes
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT'
  plan['checkpoint_reason']='EXACT2092_GRANULAR_SOURCE_CLOSURE_COMPLETE_ELEVEN_WHOLE_SOURCES_AND_BOTH_AUDITS_NEED_SEPARATE_EXCLUSIVE_LEASE'
""",1)
# The original final block contains elif branches; retain their original order by
# placing our end-scope checkpoint immediately before the existing terminal else.
new=new.replace(" else:\n  ht_actual_passes=", " elif '--exact2056-granular-continuation' in sys.argv[3:]:\n  ht_actual_passes=",1)
ast.parse(new)
with ADAPTER.open('x',encoding='utf8',newline='\n') as f:f.write(new)
with DIFF.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=OLD.name,tofile=ADAPTER.name))
native=metadata(json.loads((BASE/'completed-own-BooleanTree-strong-LZX-single-pilot-preparation-20261005.json').read_bytes()))
artifact_inventory=[]
for row in passed.values():
    for a in row['artifacts']:artifact_inventory.append(dict(a,native=native(Path(a['file'])),WOF=wof_info(Path(a['file']))))
b0=passed['RamseyCert.Chunk.B0'];b0a=next(a for a in artifact_inventory if a['file'].endswith('B0.olean'))
chunks=[n for n in entries if '.Chunk.' in n];remaining_chunks=[n for n in remaining_order if '.Chunk.' in n]
assert len(chunks)==2048 and len(remaining_chunks)==2047
chunk_sources=[Path(entries[n]['file']).stat().st_size for n in remaining_chunks]
nonchunks=[n for n in remaining_order if '.Chunk.' not in n];assert len(nonchunks)==9
resources={'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()}
projection={'status':'READ_ONLY_SINGLE_KERNEL_CHUNK_MEASURED_SCENARIOS_NOT_UPPER_BOUNDS',
 'created_utc':datetime.now(timezone.utc).isoformat(),'scope_sha256':scope_sha,'actual36_receipt_sha256':RECEIPT_SHA,
 'all36_current_output_native_identity':artifact_inventory,
 'current36_output_logical_bytes':sum(a['bytes'] for a in artifact_inventory),
 'current36_output_allocated_bytes':sum(a['native']['standard_allocation_bytes'] for a in artifact_inventory),
 'first_kernel_chunk_actual':b0,'first_kernel_output_current_native':b0a,
 'remaining_source_count':2056,'remaining_kernel_chunk_count':2047,'remaining_other_granular_modules':nonchunks,
 'remaining_kernel_source_size_distribution_bytes':{'min':min(chunk_sources),'max':max(chunk_sources),'median':statistics.median(chunk_sources),'total':sum(chunk_sources)},
 'scenario_if_each_remaining_chunk_equals_B0':{'kernel_seconds':2047*b0['seconds'],'kernel_hours':2047*b0['seconds']/3600,
    'kernel_output_logical_bytes':2047*b0a['bytes'],'kernel_output_allocated_bytes':2047*b0a['native']['standard_allocation_bytes'],
    'estimated_disk_free_after_kernel_only':resources['disk_free_bytes']-2047*b0a['native']['standard_allocation_bytes']},
 'scenario_if_every_chunk_is_twice_B0_allocated':{'kernel_output_allocated_bytes':2047*2*b0a['native']['standard_allocation_bytes'],
    'estimated_disk_free_after_kernel_only':resources['disk_free_bytes']-2047*2*b0a['native']['standard_allocation_bytes']},
 'unbounded_variation':['Only one kernel chunk measured; chunk cost/output may differ','Nine glue/check granular modules and final receipt/log growth are additional','Other active owned proof work and system allocations share disk and commit'],
 'unchanged_initial_disk_dispatch_bytes':4_000_000_000,'unchanged_continuous_disk_floor_bytes':1_000_000_000,
 'future_storage_decision':'No2056dispatch should assume these estimates are bounds. Await exactB0 completed-output LZX pilot/review; if needed, prepare separately reviewed post-exit own-output compression policy before actual continuation.',
 'current_resources':resources,'guaranteed_savings_bytes':0,'compiler_compressor_deletion_alias_or_source_mutation':0}
write_new(PROJECTION,projection)
packet={'status':'PREPARED_ONLY_ROOT_REVIEW_REQUIRED_NO2056_COMPILER_OR_STORAGE_EXECUTION',
 'scope':str(SCOPE),'scope_sha256':scope_sha,'adapter':str(ADAPTER),'adapter_sha256':sha(ADAPTER),
 'minimal_operational_diff':str(DIFF),'minimal_operational_diff_sha256':sha(DIFF),
 'projection':str(PROJECTION),'projection_sha256':sha(PROJECTION),
 'original2103_plan_sha256':PLAN_SHA,'preserved36_actual_receipt_sha256':RECEIPT_SHA,
 'command':[str(Path(sys.executable)),'-X','utf8',str(ADAPTER),'htpeo-ramsey-current','1','--guarded-third-slot','--defer-whole-imports','--with-reviewed-supplemental-audit','--exact2056-granular-continuation','--granular-continuation-scope-sha256',scope_sha],
 'exact_remaining2056_sources':remaining_order,'deferred11_whole_sources':sorted(whole),'audit_invocations':0,
 'scientific_body_plan_options_or_audit_changes':0,'compiler_or_storage_execution':0,
 'future_prerequisite':'Root review of exact adapter/scope/projected storage and actual B0 compression pilot; dated lease with <=2actual compilers/no whole importer.'}
write_new(PACKET,packet)
print(json.dumps({'scope_sha256':scope_sha,'adapter_sha256':sha(ADAPTER),'diff_sha256':sha(DIFF),'projection_sha256':sha(PROJECTION),'preparation_sha256':sha(PACKET),'scenario':projection['scenario_if_each_remaining_chunk_equals_B0'],'other9':nonchunks},indent=2))
