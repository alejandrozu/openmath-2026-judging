"""Prepare an adapter and full review diff only. No compiler invocation."""
from pathlib import Path
import ast, datetime, difflib, hashlib, json, os

BASE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
baseline_file=BASE/'m2_runner_source_archives/run_source_plan.baseline.70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534.py'
assert sha(baseline_file)=='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'
baseline=baseline_file.read_text(encoding='utf8')
preparation_file=BASE/'original-E65-source-replay-preparation-20261005.json'
assert sha(preparation_file)=='96f74d38af628c8763632c3a0869d7fa2404796ecf66de70fd13d6b0652e1e06'
prepared=json.loads(preparation_file.read_text(encoding='utf8'))
header='''"""Prepared exact recovered E65 source replay, separate from original-container execution.
No process starts unless this concrete adapter and a resource lease are root reviewed.
Initially only189 recovered FC granular sources; all whole descendants/audits deferred.
The separately verified Std-only source/audit is a candidate witness, never copied or
automatically counted as a new PASS here. Future whole mode requires189 own hashed
passes and an exact-plan sole lease, with10/11 GiB guard. Source bodies stay unchanged.
"""
from pathlib import Path
import json,re,subprocess,os,sys,time,hashlib,shutil,msvcrt
from lean_imports import read_imports,stripped as stripped_lean
from audit_axioms import parse as parse_axioms
from resource_metrics import snapshot as memory_snapshot
from receipt_io import read_bytes_shared,read_json_shared
BASE=Path(__file__).resolve().parent
RUNNER_SOURCE_SHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
AXIOM_PARSER_SOURCE_SHA256=hashlib.sha256((BASE/'audit_axioms.py').read_bytes()).hexdigest()
PROJECT='sundai-erdos3-original-image-source'
PREPARATION_SHA256='96f74d38af628c8763632c3a0869d7fa2404796ecf66de70fd13d6b0652e1e06'
PLAN_SHA256='0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15'
project=sys.argv[1]
worker_threads=int(sys.argv[2])
flags=sys.argv[3:]
assert project==PROJECT and worker_threads==1,'Exact original-source project and -j1 only'
assert '--original-e65-source-replay-authorized' in flags and '--resource-lease-confirmed' in flags,'Concrete root scope review and resource handoff required'
assert '--reviewed-runner-sha256='+RUNNER_SOURCE_SHA256 in flags,'Exact executed adapter SHA must match root-reviewed command'
third_worker_pilot='--pilot-third-slot' in flags
third_worker_continuation='--guarded-third-slot' in flags
assert third_worker_pilot != third_worker_continuation,'Choose one-source pilot or guarded continuation'
third_worker_guarded=third_worker_tree_guarded=True
full_mathlib_source_mode='--full-mathlib-source-mode' in flags
assert full_mathlib_source_mode != ('--defer-whole-imports' in flags),'Choose granular withholding or future exact whole-only lease'
a000_whole_scope_only=False
independent_resource_mode=False
defer_whole_import_mode=True
legacy_a000_single_pilot=False
def sha_file(file):return hashlib.sha256(Path(file).read_bytes()).hexdigest()
prep_file=BASE/'original-E65-source-replay-preparation-20261005.json'
assert sha_file(prep_file)==PREPARATION_SHA256,'Reviewed preparation changed'
prepared=json.loads(prep_file.read_text(encoding='utf8'))
assert sha_file(BASE/'original-E65-FC193-replay-inventory-20261005.json')==prepared['inventory_sha256']
for filename,digest_value in prepared['helper_hashes'].items():
 assert sha_file(BASE/filename)==digest_value,'Reviewed helper changed: '+filename
dest=BASE/'builds'/PROJECT
assert sha_file(dest/'build-plan.json')==PLAN_SHA256,'Frozen original-source plan changed'
plan=json.loads((dest/'build-plan.json').read_text(encoding='utf8'))
assert len(plan['modules'])==200 and len(plan['audit_modules'])==7 and len(set(plan['endpoints']))==56
assert not plan.get('additional_dependency_libs'),'No compatible FC library may be admitted'
for row in plan['modules']:
 assert sha_file(row['file'])==row['sha256'],'Frozen staged source changed: '+row['module']
for row in prepared['audits']:
 assert sha_file(row['file'])==row['source_sha256'],'Frozen selected audit changed'
compiler=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
assert sha_file(compiler)==prepared['compiler_binary_sha256'],'Compiler binary changed'
for row in prepared['exact_original_nine_packages']:
 actual=subprocess.run(['git','rev-parse','HEAD'],cwd=row['prepared_source_path'],capture_output=True,text=True,check=True).stdout.strip()
 assert actual==row['original_manifest_rev'],'Original package pin mismatch: '+row['name']
cache_raw=read_bytes_shared(BASE/'mathlib-4.33.1-cache-retry.json')
assert hashlib.sha256(cache_raw).hexdigest()==prepared['official_cache_PASS_receipt_sha256']
assert json.loads(cache_raw)['status']=='PASS','Exact official cache validation required'
from full_mathlib_scope import classify as classify_full_mathlib
full_scope=classify_full_mathlib(plan)
assert full_scope==prepared['exact_frozen_import_scope'],'Frozen import scope changed'
granular_names=set(prepared['initial_granular_source_names']);assert len(granular_names)==189
whole_names=set(prepared['whole_FC_source_names']+prepared['whole_entrant_source_names']);assert len(whole_names)==10
candidate=prepared['Std_existing_qualified_reuse_candidate_only']
assert sha_file(candidate['qualified_record_file'])==candidate['qualified_record_sha256']
deferred_whole_names={candidate['module'],candidate['audit']}
if not full_mathlib_source_mode:
 deferred_whole_names.update(whole_names)
 deferred_whole_names.update(row['audit'] for row in prepared['audits'] if row['deferred_whole_scope'])
deferred_whole_scope={**full_scope,'Std_witness_candidate_pending':candidate,
 'qualification':'Only exact recovered source bodies; withheld whole descendants and separately qualified Std candidate are never silently counted as this route PASS.'}
if full_mathlib_source_mode:
 current_file=BASE/(PROJECT+'-fresh-build.json');current_raw=read_bytes_shared(current_file);current=json.loads(current_raw)
 assert current['source_plan_sha256']==PLAN_SHA256
 assert current.get('finished_utc') and current['status']=='SCHEDULED_RESOURCE_CHECKPOINT','Actual completed granular checkpoint required'
 frozen={m['module']:m for m in plan['modules']}
 successes={r['module']:r for r in current['builds'] if r.get('exit')==0 and not r.get('stop_reason') and not r.get('is_endpoint_audit')}
 assert granular_names<=set(successes),'All189 own granular successes required before any whole invocation'
 for name in granular_names:
  row=successes[name];assert row['source_sha256']==frozen[name]['sha256'] and '-o' in row['command']
  assert row.get('effective_lean_options')==frozen[name]['lean_options'],'Recorded FC semantic options required'
  file=Path(frozen[name]['file']);expected_paths=[p for p in [file.with_suffix('.olean'),file.with_suffix('.olean.private'),file.with_suffix('.olean.server'),file.with_suffix('.ilean'),file.with_suffix('.ir')] if p.exists()]
  actual=[{'file':str(p),'sha256':sha_file(p),'bytes':p.stat().st_size} for p in expected_paths]
  assert row.get('artifacts')==actual and file.with_suffix('.olean').exists(),'Own granular artifacts changed or missing'
 lease_raw=read_bytes_shared(BASE/'original-e65-source-replay-sole-lease.json');lease=json.loads(lease_raw)
 assert lease['holder_project']==PROJECT and lease['source_plan_sha256']==PLAN_SHA256
 assert lease['granular_completed_receipt_sha256']==hashlib.sha256(current_raw).hexdigest()
 assert lease['whole_library_solo_authorized'] is True and lease['other_source_compilers_confirmed_held_or_finished'] is True
 assert set(lease['allowed_source_names'])==whole_names
 assert set(lease['allowed_audit_names'])=={r['audit'] for r in prepared['audits'] if r['deferred_whole_scope']}
 assert lease['reviewed_runner_sha256']==RUNNER_SOURCE_SHA256
 full_lock=(BASE/'.exclusive-full-mathlib-source.lock').open('a+b')
 if full_lock.seek(0,2)==0:full_lock.write(b'0');full_lock.flush()
 full_lock.seek(0);msvcrt.locking(full_lock.fileno(),msvcrt.LK_NBLCK,1)
third_disk_dispatch_bytes=4_000_000_000
third_commit_dispatch_bytes=(11 if full_mathlib_source_mode else 5)*2**30
third_private_limit_bytes=(10 if full_mathlib_source_mode else 6)*2**30
resource_guard_name='full_mathlib_resource_guard.py' if full_mathlib_source_mode else 'matt_resource_guard.py'
assert shutil.disk_usage(BASE).free>=third_disk_dispatch_bytes,'Initial4GB disk dispatch gate'
initial_metrics=memory_snapshot()
assert initial_metrics['free_physical_bytes']>=6*2**30 and initial_metrics['available_commit_bytes']>=third_commit_dispatch_bytes,'Initial physical/commit gates'
if full_mathlib_source_mode:from full_mathlib_resource_guard import guarded_tree
else:from matt_resource_guard import guarded_tree
assert dest.resolve().is_relative_to((BASE/'builds').resolve())
'''
tail=baseline[baseline.index('# Persistent one-byte file;'):]
tail=tail.replace("prior=json.loads(report.read_text(encoding='utf8'))","prior=read_json_shared(report)")
tail=tail.replace("archived.write_bytes(report.read_bytes())","archived.write_bytes(read_bytes_shared(report))")
tail=tail.replace("assert json.loads((BASE/('mathlib-'+plan['version']+'-cache-retry.json')).read_text())['status']=='PASS'","assert read_json_shared(BASE/('mathlib-'+plan['version']+'-cache-retry.json'))['status']=='PASS'")
tail=tail.replace("plan['failed_invocations']=[]", "plan['execution_route']='EXACT_RECOVERED_E65_SOURCE_WINDOWS_OPERATIONAL_REPLAY_NOT_ORIGINAL_CONTAINER_EXECUTION'\nplan['source_plan_sha256']=PLAN_SHA256\nplan['preparation_sha256']=PREPARATION_SHA256\nplan['baseline_runner_sha256']='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'\nplan['original_container_executed']=False\nplan['Std_external_witness_candidate_accepted']=False\nplan['failed_invocations']=[]",1)
tail=tail.replace("ROOT_AUTHORIZED_GRANULAR_REMAINDER_ONLY_WHOLE_MODULES_AND_AUDITS_NEED_SEPARATE_LITERAL_IMPORTER_LEASE", "EXACT_RECOVERED_ORIGINAL_SOURCE_ROUTE_WITH_PENDING_WHOLE_LEASE_AND_EXTERNAL_STD_WITNESS_NOT_CONTAINER_EXECUTION")
tail=tail.replace("file.with_suffix('.ilean')]", "file.with_suffix('.ilean'),file.with_suffix('.ir')]")
tail=tail.replace("str(archived),'status':prior['status']", "str(archived),'status':prior['status']")
tail=tail.replace("(BASE/'hold-third-worker-dispatch')", "(BASE/'hold-original-e65-dispatch')")
tail=tail.replace("'classification':'SEPARATE_SOLE_LITERAL_IMPORTER_LEASE_REQUIRED'", "'classification':'EXTERNAL_STD_WITNESS_REVIEW_PENDING' if n in {candidate['module'],candidate['audit']} else 'SEPARATE_SOLE_LITERAL_IMPORTER_LEASE_REQUIRED'")
old="for key,value in plan.get('lean_options',{}).items():args.append('-D'+key+'='+str(value).lower())"
new="effective_options=plan.get('lean_options',{}) if audit else m['lean_options']\n for key,value in effective_options.items():args.append('-D'+key+'='+str(value).lower())"
assert old in tail;tail=tail.replace(old,new)
tail=tail.replace("row['source_sha256']=digest(file)", "row['source_sha256']=digest(file)\n row['effective_lean_options']=effective_options\n row['semantic_option_qualification']='Explicit recovered FC strong options; entrant/audit options separately recorded, historical author invocation not inferred'")
tail=tail.replace("'GRANULAR_REMAINDER_FINISHED_WHOLE_IMPORT_LEASE_STILL_REQUIRED'", "'EXACT_RECOVERED_SCOPE_PARTIAL_WITH_WHOLE_LEASE_OR_EXTERNAL_STD_WITNESS_STILL_PENDING'")
text=header+tail
ast.parse(text)
target=BASE/'run_original_e65_source_plan.py'
tmp=target.with_suffix('.py.tmp');tmp.write_text(text,encoding='utf8',newline='\n');os.replace(tmp,target)
archive=BASE/'m2_runner_source_archives'/('run_original_e65_source_plan.prepared.'+sha(target)+'.py')
assert not archive.exists();archive.write_bytes(target.read_bytes())
diff=''.join(difflib.unified_diff(baseline.splitlines(True),text.splitlines(True),fromfile=baseline_file.name,tofile=target.name))
diff_file=BASE/'original-E65-source-adapter-full-baseline70ff.diff';diff_file.write_text(diff,encoding='utf8',newline='\n')
record={'status':'CONCRETE_ADAPTER_PREPARED_FOR_ROOT_REVIEW_NO_DISPATCH',
    'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'baseline_runner_sha256':sha(baseline_file),'adapter_file':str(target),'adapter_sha256':sha(target),
    'immutable_prepared_adapter_file':str(archive),'full_diff_file':str(diff_file),'full_diff_sha256':sha(diff_file),
    'preparation_sha256':sha(preparation_file),'source_plan_sha256':prepared['source_plan_sha256'],
    'initial_source_count':189,'initial_selected_audits':0,'deferred_whole_sources':10,
    'deferred_whole_audits':6,'deferred_whole_selected_names':42,
    'separate_Std_candidate_source':1,'separate_Std_candidate_audit':1,'separate_Std_candidate_selected_names':14,
    'whole_mode_prerequisite':'Actual189 own source/semantic-option/artifact hashes plus exact-plan root sole lease;10GiB own/11GiB commit guard.',
    'guard_dispatch_and_continuous_policies_unchanged':True,'shell_threads':1,
    'compatible_FC_source_library_admitted':False,'source_body_or_tactic_changes':False,
    'output_copies_links_or_aliases':False,'Lean_or_compiler_invoked':False,
    'parse_only_Python_syntax_check':'ast.parse PASS, not adapter execution',
    'preparation_scope_qualification':'A full200source/56selected plan is preserved, but no full-project PASS is possible while its Std witness is merely pending or any whole/audit invocation is deferred.'}
review=BASE/'original-E65-source-adapter-review-packet-20261005.json'
review.write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({**record,'review_packet_file':str(review),'review_packet_sha256':sha(review)},indent=2))
