"""Prepared-only exact original E65 whole16/six-audit scheduling packet.

No active lease or hold flag is created, no receipt or proof source is modified,
and no Lean/guard/compiler process is invoked. The current granular snapshot is
historical only; the final183 boundary and actual HT inactivity must be bound later.
"""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re,subprocess
from lean_imports import read_imports,stripped
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent
PROJECT='sundai-erdos3-original-image-source'
STAGE=BASE/'builds'/PROJECT
PLAN=STAGE/'build-plan.json'
RUNNER=BASE/'run_original_e65_tactic_aware_source_plan.py'
WHOLE=BASE/'original-E65-whole16-prerequisites-sole-lease-review-20261005.json'
PREP=BASE/'original-E65-source-replay-preparation-20261005.json'
SCOPE=BASE/'original-E65-tactic-aware-resource-scope-20261005.json'
STD_ACCEPT=BASE/'original-E65-root-exact-Std1-14-external-evidence-acceptance-20261005.json'
REPORT=BASE/(PROJECT+'-fresh-build.json')
OUT=BASE/'original-E65-exact16-sixAudit42-sole-continuation-concrete-preparation-20261005.json'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def save(p,d):
    with p.open('x',encoding='utf8',newline='\n') as f:json.dump(d,f,indent=2);f.write('\n')
assert sha(RUNNER)=='a2e5931c838e8b348de9fae4945b9f16ceb0883eaed51ca55f93e797deaa9e6d'
assert sha(PLAN)=='0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15'
assert sha(WHOLE)=='27a5c37d5134f6db703917520790202ee38ec5a17fd253dafe641d7d7ee0726f'
assert sha(PREP)=='96f74d38af628c8763632c3a0869d7fa2404796ecf66de70fd13d6b0652e1e06'
assert sha(SCOPE)=='47ed60dae2f8c65df991072ece7152e80f5594f79f54fd51d5e88d5e31b738ab'
source=RUNNER.read_text(encoding='utf8');ast.parse(source)
for token in ['--full-mathlib-source-mode','--guarded-third-slot','--reviewed-runner-sha256=',
              'original-e65-source-replay-sole-lease.json','--original-e65-source-replay-authorized',
              'hold-original-e65-dispatch','11 if full_mathlib_source_mode else 5',
              '10 if full_mathlib_source_mode else 6','from full_mathlib_resource_guard import guarded_tree']:
    assert token in source,token
plan=json.loads(PLAN.read_bytes());prep=json.loads(PREP.read_bytes());scope=json.loads(SCOPE.read_bytes());whole=json.loads(WHOLE.read_bytes())
entries={r['module']:r for r in plan['modules']};assert len(entries)==200
safe=set(scope['truly_no_Mathlib_or_Tactic_custom_closed_subset']);held=set(scope['future_whole_resource_sources'])
candidate=prep['Std_existing_qualified_reuse_candidate_only'];assert len(safe)==183 and len(held)==16
assert safe|held|{candidate['module']}==set(entries)
assert held==set(whole['whole_topological_order'])
for r in entries.values():assert sha(r['file'])==r['sha256']
imports={n:[d for d in read_imports(r['file']) if d!='all'] for n,r in entries.items()}
memo={};ordered=[];seen=set();visiting=set()
def closure(n):
    if n in memo:return memo[n]
    result={n}
    for d in imports[n]:
        if d in entries:result.update(closure(d))
    memo[n]=result;return result
def topo(n):
    if n in seen:return
    assert n not in visiting,'Custom import cycle'
    visiting.add(n)
    for d in imports[n]:
        if d in entries:topo(d)
    visiting.remove(n);seen.add(n);ordered.append(n)
for n in entries:topo(n)
assert [n for n in ordered if n in held]==whole['whole_topological_order']
assert set().union(*(closure(n) for n in held))==safe|held
audit_rows=[]
for r in prep['audits']:
    assert sha(r['file'])==r['source_sha256']
    if not r['deferred_whole_scope']:continue
    file=Path(r['file']);roots=[d for d in read_imports(file) if d!='all']
    deps=set().union(*(closure(d) for d in roots if d in entries))
    assert deps<=safe|held and candidate['module'] not in deps
    requested=re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(file.read_text(encoding='utf8')),re.M)
    original=next(x for x in whole['audit_rows'] if x['audit']==r['audit'])
    assert requested==original['selected_names'] and set(original['required_granular_sources'])==deps&safe
    assert set(original['required_whole_sources'])==deps&held
    audit_rows.append({'audit':r['audit'],'file':r['file'],'sha256':r['source_sha256'],
        'required_prior183':sorted(deps&safe),'required_whole16':sorted(deps&held),
        'requested_print_names':requested,'effective_lean_options':plan['lean_options']})
assert len(audit_rows)==6 and sum(len(r['requested_print_names']) for r in audit_rows)==42
assert len({n for r in audit_rows for n in r['requested_print_names']})==42
std=json.loads(STD_ACCEPT.read_bytes());assert std['status']=='ROOT_ACCEPTED_EXACT_STD_SOURCE_AND14_PRINT_EXTERNAL_EVIDENCE_COMPOSITION_ONLY'
assert std['original_source_plan_sha256']==sha(PLAN) and std['actual_source_modules_covered']==1 and std['actual_selected_prints_covered']==14
assert sha(std['immutable_external_witness_receipt'])==std['immutable_external_witness_receipt_sha256']
lean=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe';assert sha(lean)==prep['compiler_binary_sha256']
pinchecks=[]
for pin in prep['exact_original_nine_packages']:
    path=Path(pin['prepared_source_path'])
    head=subprocess.run(['git','rev-parse','HEAD'],cwd=path,capture_output=True,text=True,check=True).stdout.strip()
    origin=subprocess.run(['git','remote','get-url','origin'],cwd=path,capture_output=True,text=True,check=True).stdout.strip()
    assert head==pin['original_manifest_rev'] and origin==pin['original_manifest_url']
    pinchecks.append({'name':pin['name'],'actual_HEAD':head,'actual_origin':origin})
cache=BASE/'mathlib-4.33.1-cache-retry.json';assert sha(cache)==prep['official_cache_PASS_receipt_sha256']
assert json.loads(cache.read_bytes())['status']=='PASS'
raw=read_bytes_shared(REPORT);current=json.loads(raw)
assert current['source_plan_sha256']==sha(PLAN)
current_passes=[r for r in current['builds'] if r.get('exit')==0 and not r.get('stop_reason') and not r['is_endpoint_audit']]
assert all(r['module'] in safe for r in current_passes)
for n in held:
    file=Path(entries[n]['file'])
    assert not any(file.with_suffix(s).exists() for s in ['.olean','.olean.private','.olean.server','.ilean','.ir'])
future_args=[str(RUNNER),PROJECT,'1','--guarded-third-slot','--full-mathlib-source-mode',
    '--original-e65-source-replay-authorized','--resource-lease-confirmed','--reviewed-runner-sha256='+sha(RUNNER)]
future_lease=dict(whole['sole_lease_template_not_active']);future_lease['granular_completed_receipt_sha256']='ROOT_BINDS_LATER_ACTUAL_FINISHED183_CHECKPOINT_SHA'
record={'status':'PREPARED_CONCRETE_ORIGINAL_E65_SOLE_WHOLE16_SIX_AUDITS42_NO_EXECUTION_OR_ACTIVE_LEASE',
    'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
    'project':PROJECT,'runner_file':str(RUNNER),'runner_sha256':sha(RUNNER),'runner_AST':'PASS_ONLY',
    'original_plan_file':str(PLAN),'original_plan_sha256':sha(PLAN),'historical_whole_prerequisite_packet_sha256':sha(WHOLE),
    'exact200_scientific_source_SHA_rechecked':True,'source_body_options_tactics_source_or_adapter_changes':0,
    'exact16_source_order':whole['whole_topological_order'],'whole16_source_rows':whole['whole_source_rows'],
    'six_audit_rows':audit_rows,'new_scope_source_count':16,'new_scope_audit_count':6,'new_scope_unique_requested_prints':42,
    'required_custom_union_count':199,'all183_required_prior_own_cold_passes':True,
    'future_python_command_args':future_args,'whole_guard_file':str(BASE/'full_mathlib_resource_guard.py'),
    'whole_guard_sha256':sha(BASE/'full_mathlib_resource_guard.py'),'resource_policy':whole['required_before_whole'],
    'counter_helper_sha256':sha(BASE/'native_resource_guard.py'),'commit_counter_helper_sha256':sha(BASE/'resource_metrics.py'),
    'exact_compiler_binary_sha256':sha(lean),'nine_current_HEAD_origin_checks':pinchecks,
    'exact_official_cache_PASS_receipt_sha256':sha(cache),'complete_custom_closure_verified':True,
    'new_complete_official_umbrella_artifact_rehash_performed':False,
    'official_closure_qualification':'Exact pins, unchanged official full-cache validation and complete custom sources are bound. No new full Mathlib umbrella artifact hash scan is claimed by this preparation.',
    'historical_live_granular_snapshot_SHA_not_an_execution_lease':hashlib.sha256(raw).hexdigest(),
    'historical_live_granular_status':current['status'],'historical_live_own_source_passes':len(current_passes),
    'current_whole16_own_outputs_absent':True,
    'later_required_before_any_dispatch':['Actually finished183 own source checkpoint with row/source/CLI/options/artifact hashes verified',
        'Actually exited HT/E65 granular compilers and owned dispatchers at safe boundaries',
        'Fresh all-Lean-absent PID and resource snapshot satisfying11GiB commit/6GiB physical/4GB disk',
        'Root dated exact-plan SOLO approval and active lease bound to actual finished183 receiptSHA',
        'Task-owned HT hold remains throughout whole source/audit lease; no other source compiler'],
    'future_sole_lease_template_INACTIVE':future_lease,'active_sole_lease_file_written':False,
    'Std_external_acceptance_record':str(STD_ACCEPT),'Std_external_acceptance_sha256':sha(STD_ACCEPT),
    'Std_actual_separate_source1_prints14_evidence_preserved_not_compiled_or_aliased_here':True,
    'eventual_evidence_composition_only_if_all_scopes_actually_pass':'199 original recovered own-source checks and42 prints plus independently accepted exact Std source1/14 prints; no physical Std artifact reuse and no new200-source cold replay claim.',
    'existing_runner_will_intentionally_remain_partial_for_withheld_Std':'Its candidate source/audit remain deferred and Std_external_witness_candidate_accepted remains false. A later external composite qualifier must preserve that raw receipt rather than relabel it.',
    'original_container_executed':False,'full_FC_Git_revision_reconstructed':False,
    'scientific_claim_from_source_replay_only':'These AP auxiliary bridges do not prove either unresolved side of Erdos3 merely by compiling.',
    'compiler_flags_process_holds_aliases_or_source_mutations_invoked':0}
save(OUT,record)
print(json.dumps({'packet':str(OUT),'packet_sha256':sha(OUT),'source_count':16,'audits':6,'selected_prints':42,
    'historical_current_prior_passes':len(current_passes),'no_Lean_or_active_lease':True},indent=2))
