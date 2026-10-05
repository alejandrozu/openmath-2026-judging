"""Prepare-only bounded first original HT kernel chunk and its exact prerequisites."""
from pathlib import Path
import hashlib,json,ast,difflib
from lean_imports import read_imports
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-ramsey-current'
PLAN=STAGE/'build-plan.json'
PLAN_SHA='94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
ORIGINAL_ADAPTER=BASE/'run_htpeo_ramsey_supplemented_plan.py'
ORIGINAL_ADAPTER_SHA='b0293550ae7afaf65c1a0bd03c543d39213de48b4523aa4568547c1a1f78518a'
FIRST='RamseyCert.Chunk.B0'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha(PLAN)==PLAN_SHA and sha(ORIGINAL_ADAPTER)==ORIGINAL_ADAPTER_SHA
plan=json.loads(PLAN.read_bytes());entries={r['module']:r for r in plan['modules']};assert len(entries)==2103
seen=set();visiting=set();ordered=[];imports={}
def visit(name):
    if name in seen:return
    assert name not in visiting,'Custom import cycle'
    visiting.add(name);imports[name]=[n for n in read_imports(entries[name]['file']) if n!='all']
    for dep in imports[name]:
        if dep in entries:visit(dep)
    visiting.remove(name);seen.add(name);ordered.append(name)
visit(FIRST)
assert FIRST==ordered[-1] and len([n for n in ordered if '.Chunk.' in n])==1
assert not {'Mathlib','Mathlib.Tactic'}&{n for roots in imports.values() for n in roots}
assert 'RamseyCert.Defs' in seen
receipt_path=BASE/'htpeo-ramsey-current-fresh-build.json';raw=read_bytes_shared(receipt_path);prior=json.loads(raw)
passed=[r for r in prior['builds'] if r['exit']==0 and not r['is_endpoint_audit'] and not r.get('stop_reason')]
assert len(passed)==1 and passed[0]['module']=='RamseyCert.Defs' and prior['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
assert passed[0]['source_sha256']==entries['RamseyCert.Defs']['sha256']
for artifact in passed[0]['artifacts']:assert sha(artifact['file'])==artifact['sha256']
all_sources=[]
for name,entry in entries.items():
    assert sha(entry['file'])==entry['sha256']
    all_sources.append({'module':name,'sha256':entry['sha256']})
manifest_path=BASE/'htpeo-ramsey-first-kernel-chunk-calibration-scope-20261005.json';assert not manifest_path.exists()
manifest={'status':'PREPARED_ONLY_NO_LEAN_EXACT_PREREQUISITES_PLUS_ONE_ORIGINAL_KERNEL_CHUNK',
    'original_source_plan_sha256':PLAN_SHA,'original_full2103_source_hashes_verified':all_sources,
    'original_adapter_sha256':ORIGINAL_ADAPTER_SHA,'first_original_kernel_chunk':FIRST,
    'exact_custom_prerequisite_order':ordered[:-1],'exact_bounded_dispatch_order':ordered,
    'prior_own_Definitions_PASS_receipt_sha256':hashlib.sha256(raw).hexdigest(),'prior_Definitions_PASS_row':passed[0],
    'source_records':[dict(entries[n],direct_imports=imports[n],bytes=Path(entries[n]['file']).stat().st_size) for n in ordered],
    'external_direct_roots':sorted({r for roots in imports.values() for r in roots if r not in entries}),
    'no_other_chunks_or_whole_or_audits':'All non-scope2103 custom sources and both original/supplemental audits are not invoked by calibration adapter.',
    'source_body_changes':0,'compiler_invocations_performed':0,'output_aliases':0,
    'original_source_plan_and_all2103_scientific_bytes_unchanged':True,
    'resource_policy':'Existing6GiB own/5GiB commit/6GiB physical/4GB disk dispatch andcontinuous1GiB commit/3GiBphysical/1GBdisk;-j1;max2actualsource compilers.'}
manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
manifest_sha=sha(manifest_path)
text=ORIGINAL_ADAPTER.read_text(encoding='utf8')
needle="project=sys.argv[1]\n"
assert text.count(needle)==1
text=text.replace(needle,needle+"first_kernel_chunk_calibration='--first-kernel-chunk-calibration' in sys.argv[3:]\n")
needle="plan=json.loads((dest/'build-plan.json').read_text())\n"
assert text.count(needle)==1
block="""
if first_kernel_chunk_calibration:
 assert project=='htpeo-ramsey-current' and worker_threads==1 and third_worker_continuation and defer_whole_import_mode
 assert not third_worker_pilot and not full_mathlib_source_mode and not independent_resource_mode
 scope_flag='--calibration-scope-sha256';assert sys.argv.count(scope_flag)==1
 scope_sha=sys.argv[sys.argv.index(scope_flag)+1];assert scope_sha==MANIFEST_SHA_PLACEHOLDER
 scope_file=BASE/'htpeo-ramsey-first-kernel-chunk-calibration-scope-20261005.json'
 assert hashlib.sha256(scope_file.read_bytes()).hexdigest()==scope_sha
 calibration_scope=json.loads(scope_file.read_bytes())
 assert hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()==calibration_scope['original_source_plan_sha256']
 assert calibration_scope['first_original_kernel_chunk']=='RamseyCert.Chunk.B0'
 actual_modules={r['module']:r for r in plan['modules']}
 for record in calibration_scope['source_records']:
  assert actual_modules[record['module']]['sha256']==record['sha256']==hashlib.sha256(Path(record['file']).read_bytes()).hexdigest()
  assert [n for n in read_imports(record['file']) if n!='all']==record['direct_imports']
 plan['bounded_first_kernel_chunk_calibration']={'scope_file':str(scope_file),'scope_sha256':scope_sha,
  'first_original_kernel_chunk':'RamseyCert.Chunk.B0','bounded_dispatch_order':calibration_scope['exact_bounded_dispatch_order'],
  'source_body_or_plan_edits':False,'all_other_sources_and_both_audits_unattempted':True}
""".replace('MANIFEST_SHA_PLACEHOLDER',repr(manifest_sha))
text=text.replace(needle,needle+block)
needle="for n in ordered+plan['audit_modules']+plan.get('non_acceptance_audit_modules',[]):\n"
assert text.count(needle)==1
block="""dispatch_order=ordered+plan['audit_modules']+plan.get('non_acceptance_audit_modules',[])
if first_kernel_chunk_calibration:
 scope_names=set(calibration_scope['exact_bounded_dispatch_order'])
 assert len(scope_names)==len(calibration_scope['exact_bounded_dispatch_order'])
 dispatch_order=[n for n in ordered if n in scope_names]
 assert dispatch_order==calibration_scope['exact_bounded_dispatch_order']
 assert not scope_names&deferred_whole_names and not any(n.endswith('.lean') for n in dispatch_order)
 assert 'RamseyCert.Defs' in retained and retained['RamseyCert.Defs']['exit']==0
 assert retained['RamseyCert.Defs']['source_sha256']==calibration_scope['prior_Definitions_PASS_row']['source_sha256']
for n in dispatch_order:
"""
text=text.replace(needle,block)
needle=" if plan['failed_invocations']:plan['status']='BUILD_FAILED_OR_TIMED_OUT'\n"
assert text.count(needle)==1
block=""" elif first_kernel_chunk_calibration:
  actual_success={r['module'] for r in plan['builds'] if r['exit']==0 and not r['is_endpoint_audit'] and not r.get('stop_reason')}
  assert set(calibration_scope['exact_bounded_dispatch_order'])<=actual_success
  plan['status']='SCHEDULED_RESOURCE_CHECKPOINT'
  plan['checkpoint_reason']='BOUNDED_PREREQUISITES_AND_FIRST_ORIGINAL_KERNEL_CHUNK_COMPLETED_NO_OTHER_SOURCE_OR_AUDIT_DISPATCH'
"""
text=text.replace(needle,needle+block)
target=BASE/'run_htpeo_ramsey_first_kernel_chunk_calibration.py';assert not target.exists();ast.parse(text)
target.write_text(text,encoding='utf8',newline='\n')
diff=BASE/'htpeo-ramsey-first-kernel-chunk-calibration-minimal-operational.diff';assert not diff.exists()
diff.write_text(''.join(difflib.unified_diff(ORIGINAL_ADAPTER.read_text(encoding='utf8').splitlines(keepends=True),text.splitlines(keepends=True),fromfile=ORIGINAL_ADAPTER.name,tofile=target.name)),encoding='utf8')
packet=BASE/'htpeo-ramsey-first-kernel-chunk-calibration-preparation-20261005.json';assert not packet.exists()
packet.write_text(json.dumps({'status':'PREPARED_ONLY_FULL_ROOT_REVIEW_REQUIRED_NO_LEAN','scope':str(manifest_path),'scope_sha256':manifest_sha,
    'adapter':str(target),'adapter_sha256':sha(target),'minimal_operational_diff':str(diff),'minimal_operational_diff_sha256':sha(diff),
    'unchanged2103_plan_sha256':PLAN_SHA,'exact_prerequisite_order':ordered[:-1],'first_kernel_chunk':FIRST,
    'command':[str(Path(__import__('sys').executable)),'-X','utf8',str(target),'htpeo-ramsey-current','1','--guarded-third-slot','--defer-whole-imports','--first-kernel-chunk-calibration','--calibration-scope-sha256',manifest_sha],
    'no_other_source_or_audit_execution':True,'compiler_invocations':0,'source_changes':0},indent=2)+'\n',encoding='utf8')
print(json.dumps({'scope':str(manifest_path),'scope_sha256':manifest_sha,'adapter_sha256':sha(target),'diff_sha256':sha(diff),
    'preparation_sha256':sha(packet),'ordered_scope':ordered},indent=2))
