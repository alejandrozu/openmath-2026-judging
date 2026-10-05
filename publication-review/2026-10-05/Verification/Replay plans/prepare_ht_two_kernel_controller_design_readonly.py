"""Read-only design/source manifest for future two-job original kernel replay; no execution."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json
from lean_imports import read_imports,stripped
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent
PLAN=BASE/'builds/htpeo-ramsey-current/build-plan.json'
CONTROLLER=BASE/'run_ht_ramsey_two_kernel_controller_prepared.py'
MANIFEST=BASE/'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
DESIGN=BASE/'ht-ramsey-two-kernel-controller-design-preparation-20261005.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,d):
    with Path(p).open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')
assert sha(PLAN)=='94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3'
plan=json.loads(PLAN.read_bytes());entries={m['module']:m for m in plan['modules']}
assert len(entries)==2103
imports={n:[d for d in read_imports(e['file']) if d!='all'] for n,e in entries.items()}
for e in entries.values():assert sha(e['file'])==e['sha256']
chunks={n for n in entries if '.Chunk.' in n};assert len(chunks)==2048
memo={}
def closure(n):
    if n not in memo:
        found=set()
        for dep in imports[n]:
            if dep in entries:found.add(dep);found.update(closure(dep))
        memo[n]=found
    return memo[n]
records=[]
for name in sorted(chunks):
    deps=closure(name);assert not deps&chunks
    assert not {'Mathlib','Mathlib.Tactic'}&{d for n in deps|{name} for d in imports[n]}
    text=stripped(Path(entries[name]['file']).read_text(encoding='utf8'))
    assert 'native_decide' not in text and not __import__('re').search(r'\bsorry\b|^\s*axiom\s',text,__import__('re').M)
    records.append({'module':name,'source_file':entries[name]['file'],'source_sha256':entries[name]['sha256'],
      'direct_imports':imports[name],'entire_custom_prerequisite_closure':sorted(deps),
      'literal_kernel_decide_sites':text.count('decide +kernel')})
shared=set().union(*(set(r['entire_custom_prerequisite_closure']) for r in records));assert len(shared)==35
save(MANIFEST,{'status':'PREPARED_ONLY_COMPLETE_SOURCE_GRAPH_NO_PARALLEL_PROOF_EXECUTION',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'original2103_source_plan_sha256':sha(PLAN),'independent2048_kernel_chunk_names':sorted(chunks),'kernel_sources':records,
 'immutable_shared35_custom_prerequisite_source_records':[entries[n] for n in sorted(shared)],
 'no_chunk_to_chunk_import_edges':True,'no_kernel_scope_whole_or_tactic_umbrella_exposure':True,
 'scientific_sources_semantic_flags_or_active_c810_runner_changes':0})
ast.parse(CONTROLLER.read_text(encoding='utf8'))
full=BASE/'ht-ramsey-two-kernel-controller-full-prepared-implementation.diff'
with full.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff([],CONTROLLER.read_text(encoding='utf8').splitlines(True),fromfile='/dev/null',tofile=CONTROLLER.name))
live=BASE/'htpeo-ramsey-current-fresh-build.json';raw=read_bytes_shared(live);receipt=json.loads(raw)
save(DESIGN,{'status':'PREPARED_SOURCE_ONLY_NO_EMPIRICAL_PARALLEL_QUALIFICATION_NO_EXECUTION',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'controller':str(CONTROLLER),'controller_sha256':sha(CONTROLLER),'controller_AST':'PASS_ONLY',
 'full_prepared_implementation':str(full),'full_prepared_implementation_sha256':sha(full),
 'source_manifest':str(MANIFEST),'source_manifest_sha256':sha(MANIFEST),'original_plan_sha256':sha(PLAN),
 'active_unchanged_serial_controller':str(BASE/'run_htpeo_ramsey2056_granular_continuation.py'),
 'active_serial_controller_sha256':sha(BASE/'run_htpeo_ramsey2056_granular_continuation.py'),
 'dated_live_original_receipt_snapshot_sha256':hashlib.sha256(raw).hexdigest(),'dated_live_status':receipt['status'],
 'dated_actual_source_passes':sum(r['exit']==0 and not r.get('stop_reason') and not r['is_endpoint_audit'] for r in receipt['builds']),
 'future_authorization_requires_NEW_actual_quiescent_boundary_receipt_SHA_not_live_snapshot':True,
 'operational_design':['Oneparent HTreplaylock; all prior rows preserved in immutable boundary receipt','Oneparent only canonicalatomicwrites; workers only distinct chunkoutput and distinct redirectedguardlogs','Two threaded calls to unchanged local-state guarded_tree with separate suspended ownjobs; eachj1/6GiBown/5GiBcommit/6GiBphysical/4GBdisk and continuous1GiBcommit/3GiBphysical/1GBdisk','No other global Lean source worker atstartup; parent halts dispatch upon foreigncompiler appearance; no foreignprocess stop','All2048chunks independent ofeachother; complete shared35 source/output identity must be ownactualPASS before dispatch','Required firstmeasurement is exactly2NEWchunk pilot; no automaticcontinuation','NoSymDefs/eightSymChk,11whole,originalaudit or24supplementalprints are invoked','Noaliases/sourceedits/nativeC/librarybuild/compression/deletion; unrecordedpartialoutputs require separate recovery','Onresource/hold event stopnewdispatch, let any other active ownchunk finish under its guard, preserve every outcome/partialbyte','Resource no-attempt backpressure; no repeated whole-libraryimports/no capfloor changes'],
 'shared_guard_source_sha256':sha(BASE/'matt_resource_guard.py'),
 'guard_local_state_static_review':'Jobhandle/process/stdout/stderr/counters are local percall; global DLL API signatures remain immutable afterimport. This is read-only feasibility, not an empirical thread/parallelproof result.',
 'future_root_pilot_approval_fields':{'status':'ROOT_APPROVED_HT_RAMSEY_TWO_INDEPENDENT_NEW_KERNEL_PILOT_ONLY','reviewed_controller_sha256':sha(CONTROLLER),'reviewed_kernel_source_manifest_sha256':sha(MANIFEST),'reviewed_original2103_plan_sha256':sha(PLAN),
   'actual_quiescent_boundary_receipt_sha256':'ROOT_BINDS_LATER_ACTUAL_FINISHED_SERIAL_BOUNDARY','all_other_source_compiler_leases_returned_and_no_whole_importer':True,'maximum_total_global_Lean_importers':2,'maximum_own_parallel_kernel_jobs':2,
   'exact_current_remaining_kernel_names':'ROOT_BINDS_LATER_ACTUAL_QUESCENT_REMAINING_ORDER','reviewed_official_lake_manifest_sha256':sha(BASE/'dependencies/4.33.1/mathlib/lake-manifest.json'),'reviewed_exact_nine_dependency_git_record_sha256':sha(BASE/'dependencies-4.33.1-verified-git.json')},
 'proof_compilers_storage_mutations_aliases_actual':0})
print(json.dumps({'design':str(DESIGN),'design_sha256':sha(DESIGN),'controller_sha256':sha(CONTROLLER),
 'full_implementation_sha256':sha(full),'source_manifest_sha256':sha(MANIFEST),'current_snapshot_passes':sum(r['exit']==0 and not r.get('stop_reason') for r in receipt['builds']),'actual_compilers_or_source_mutations':0},indent=2))
