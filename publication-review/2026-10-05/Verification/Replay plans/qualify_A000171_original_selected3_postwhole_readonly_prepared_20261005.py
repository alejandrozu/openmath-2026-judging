"""UNEXECUTED prepared additive A000171/original-selected3 qualification.

Explicit root-bound finished records are mandatory. Writes only an immutable
raw receipt copy and a new qualification; no compiler, guard, storage or scheduler.
"""
import argparse
import collections
import configparser
import datetime as dt
import hashlib
import json
import pathlib
import re
import sys

V = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(V))
from receipt_io import read_bytes_shared
from full_mathlib_scope import classify
from lean_imports import read_imports
from audit_axioms import parse as parse_axioms

G = 2**30
BOUND = {
    'qualify_A000166_granular_completion_standard_allocation_readonly_prepared_20261005.py': '7b4c390e257fe8e2d7e57ec503884e2a4f2870340d611f4b10ec671421349ef3',
    'run_source_plan.py': '70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534',
    'builds/sakana-a000224/build-plan.json': '0f6338f72ff570e79847995bac7cf6f6c56c8a1c2cc8dedf55181bc764180fe7',
    'a000224-whole-module-audit-boundary-evidence.json': '170886e5721254e24443bb6ec14f660409f14ceac938bf4d3c5c12d732cda6d0',
    'builds/sakana-a000224/FreshAudit1.lean': 'c5e4477039688d0579f10457dae3ba29595d0f7cc05057f9fb63600e8b7d5547',
    'full_mathlib_resource_guard.py': 'a4c76752e1e0afaf4ddff9368e4a5aa832bc56dcc7553182c5302e2c1c4e5c18',
    'native_resource_guard.py': '0543549476ccdffdc00eab05e3139f423cf0b1471e985e196e69df011a77bed4',
    'resource_metrics.py': '1d7cb5131a34499f3000b34f46d271ef5cb43fdde37e7bb2c16dac6d01c8d8ed',
    'audit_axioms.py': '1ee59639204140430c088023539a648f9007cc26c1856cf8cd2e3c2e59d7143f',
    'full_mathlib_scope.py': '1698d525e0bac93cd241c499dc0a132e5c9477cabd7ca7899e4574645714a3ab',
    'lean_imports.py': '4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa',
    'receipt_io.py': '2e189122fe360f1925dda2e0409c321b775fe7eb6edf17c3f13ef067d1776362',
}
ENDPOINTS = ['OeisA224.not_divisible_three_primes', 'OeisA224.not_modEq_three_primes', 'OeisA224.conjecture_three_primes']
POLICY = {'initial_disk_bytes': 4_000_000_000, 'initial_physical_bytes': 6*G,
    'initial_available_commit_bytes': 11*G, 'continuous_disk_bytes': 1_000_000_000,
    'continuous_physical_bytes': 3*G, 'continuous_available_commit_bytes': G,
    'own_job_private_bytes': 10*G, 'own_process_private_bytes': 10*G,
    'poll_seconds': .25, 'timeout_seconds': 3600}

def sha(data): return hashlib.sha256(data).hexdigest()
def file_sha(path):
    h = hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''): h.update(b)
    return h.hexdigest()
def at(s): return dt.datetime.fromisoformat(s.replace('Z', '+00:00'))
def ensure(test, message):
    if not test: raise AssertionError(message)
def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists(): ensure(path.read_bytes() == data, 'Immutable output differs: '+str(path))
    else:
        with path.open('xb') as f: f.write(data)
def binding(path):
    p = pathlib.Path(path)
    return {'file': str(p), 'sha256': file_sha(p), 'bytes': p.stat().st_size}
def record_bound(path, expected, label):
    p = pathlib.Path(path).resolve()
    ensure(p.is_relative_to(V), label+' must be inside this verification workspace')
    ensure(re.fullmatch('[0-9a-f]{64}', expected), label+' malformed SHA')
    raw = read_bytes_shared(p)
    ensure(sha(raw) == expected, label+' explicit SHA mismatch')
    return p, raw, json.loads(raw)
def logs(guard, row, label):
    checked = []
    for stream in ('stdout','stderr'):
        path = pathlib.Path(guard[stream+'_file']).resolve()
        ensure(path.is_relative_to(V), label+' raw log containment')
        raw = path.read_bytes()
        ensure(sha(raw) == guard[stream+'_sha256'], label+' '+stream+' hash')
        ensure(raw.decode('utf8',errors='replace') == row[stream], label+' '+stream+' row bytes')
        checked.append({'stream':stream, 'file':str(path), 'bytes':len(raw), 'sha256':sha(raw)})
    return checked
def git_identity_readonly(root):
    """Read installed exact Git metadata; no Git/shell invocation or worktree edit."""
    root=pathlib.Path(root).resolve(); gitdir=root/'.git'
    ensure(gitdir.is_dir(),'Pinned dependency .git directory absent')
    head=(gitdir/'HEAD').read_text(encoding='utf8').strip()
    if head.startswith('ref: '):
        ref=head[5:]; rp=gitdir/ref
        if rp.is_file(): head=rp.read_text(encoding='utf8').strip()
        else:
            found=[line.split(' ',1)[0] for line in (gitdir/'packed-refs').read_text(encoding='utf8').splitlines() if line.endswith(' '+ref)]
            ensure(len(found)==1,'Pinned dependency unresolved HEAD'); head=found[0]
    ensure(re.fullmatch('[0-9a-f]{40}',head),'Pinned dependency malformed HEAD')
    config=configparser.ConfigParser(interpolation=None,strict=False)
    config.read(gitdir/'config',encoding='utf8')
    return head,config['remote "origin"']['url']

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--completed171-receipt-file', required=True)
parser.add_argument('--completed171-receipt-sha256', required=True)
for name in ('qualified166','whole-lease','root-whole-approval','both-exits-zeroLean-record','whole-controller-exit-record'):
    parser.add_argument('--'+name+'-file', required=True)
    parser.add_argument('--'+name+'-sha256', required=True)
args = parser.parse_args()
started = dt.datetime.now(dt.timezone.utc)
raw_path, raw, r = record_bound(args.completed171_receipt_file,args.completed171_receipt_sha256,'Future finished171 raw receipt')
qfile, qraw, q = record_bound(args.qualified166_file,args.qualified166_sha256,'Actual reviewed166 qualification')
leasefile, lease_raw, lease = record_bound(args.whole_lease_file,args.whole_lease_sha256,'Actual sole whole lease')
approvalfile, approval_raw, approval = record_bound(args.root_whole_approval_file,args.root_whole_approval_sha256,'Actual root whole dispatch approval')
zerofile, zero_raw, zero = record_bound(args.both_exits_zeroLean_record_file,args.both_exits_zeroLean_record_sha256,'Actual both controllers natural exits/zeroLean record')
exitfile, exit_raw, observed_exit = record_bound(args.whole_controller_exit_record_file,args.whole_controller_exit_record_sha256,'Actual whole controller process-handle exit record, never launcher exit')
bound_records, loaded = {}, {}
for name,wanted in BOUND.items():
    data = read_bytes_shared(V/name); ensure(sha(data)==wanted,'Bound code/record changed: '+name)
    bound_records[name] = {'sha256':wanted,'bytes':len(data)}
    if name.endswith('.json'): loaded[name] = json.loads(data)

ensure(q['status']=='QUALIFIED_ACTUAL_A000166_GRANULAR_SOURCE_COMPLETION_FIVE_WHOLE_AND_SELECTED3_UNRUN','Wrong actual166 scientific scope')
ensure(q['producer']['sha256']==BOUND['qualify_A000166_granular_completion_standard_allocation_readonly_prepared_20261005.py'],'Actual166 reviewed producer')
ensure(q['counts']['successful_original_source_modules']==166 and q['counts']['planned_original_source_modules']==171,'Actual166 counts')
ensure(q['counts']['selected_endpoint_audit_invocations']==0 and q['prior114_preservation']['all114_rows_identical'] is True,'Actual166 ancestry/audit hold')
priorfile, prior_raw, prior = record_bound(q['immutable166_receipt']['file'],q['immutable166_receipt']['sha256'],'Actual immutable166 ancestry')
ensure(prior['status']=='SCHEDULED_RESOURCE_CHECKPOINT' and len(prior['builds'])==166,'Actual166 natural checkpoint')
p = loaded['builds/sakana-a000224/build-plan.json']
stage = pathlib.Path(p['source_dir']).resolve()
ensure(stage==V/'builds/sakana-a000224','Exact staged source directory')
for key in ('id','entrant','version','mathlib_pin','source_dir','modules','endpoints','roots','audit_modules','lean_options'):
    ensure(r[key]==prior[key]==p[key],'Receipt/plan identity mismatch: '+key)
ensure(p['version']=='4.34.1' and p['mathlib_pin']=='d13f23b723b8a846827a245b89c10fc7d3f11612' and p['lean_options']=={},'Exact frozen pins/options')
ensure(r['status']=='PASS' and r.get('finished_utc') and 'current_module' not in r,'Final actual source/audit pass required')
ensure(not r.get('failed_invocations') and not r.get('selected_incomplete_print_audits'),'Actual source/audit failures/incomplete prints present')
ensure(not any(r.get(k) for k in ('selected_endpoint_uses_sorry','selected_unrecognized_axioms','selected_native_evaluation')),'Actual selected trust hold flags present')
ensure(not raw_path.with_suffix('.json.tmp').exists(),'Canonical pending temporary receipt requires separate review')

ensure(approval['status']=='ROOT_APPROVED_A000_ACTUAL166_EXACT_FIVE_WHOLE_ORIGINAL_SELECTED3_SOLE_REPLAY','Wrong root-approved scope')
ensure(approval['reviewed_runner_sha256']==BOUND['run_source_plan.py'] and approval['source_plan_sha256']==BOUND['builds/sakana-a000224/build-plan.json'],'Root exact runner/plan')
ensure(approval['actual166_qualification_sha256']==args.qualified166_sha256,'Root actual166 qualification binding')
ensure(approval['granular_completed_receipt_sha256']==sha(prior_raw),'Root actual166 raw binding')
ensure(approval['both_actual_exits_zero_Lean']['sha256']==args.both_exits_zeroLean_record_sha256 and pathlib.Path(approval['both_actual_exits_zero_Lean']['file']).resolve()==zerofile,'Root actual zeroLean binding')
root_policy={'maximum_mathematical_compilers':1,'own_process_and_job_private_cap_bytes':10*G,
    'dispatch_available_commit_bytes':11*G,'dispatch_physical_bytes':6*G,'dispatch_disk_bytes':4_000_000_000,
    'continuous_commit_bytes':G,'continuous_physical_bytes':3*G,'continuous_disk_bytes':1_000_000_000}
ensure(approval['resource_policy']==root_policy,'Root exact sole scheduling/resource scope')
ensure(approval['original_audit']['sha256']==BOUND['builds/sakana-a000224/FreshAudit1.lean'] and pathlib.Path(approval['original_audit']['file']).resolve()==stage/'FreshAudit1.lean','Root exact original three-request audit')
ensure(approval['source_or_storage_callback_changes'] is False and approval['prior166_guard_diversity_preserved'] is True,'Root original source/storage/history scope')
ensure(zero['status']=='ACTUAL_BOTH_SOURCE_CONTROLLERS_NATURAL_EXIT0_ZERO_OTHER_MATH_COMPILERS','Wrong natural-exit evidence scope')
zero_a=zero['root_actual_exec_results']['A000_session53326']; zero_h=zero['root_actual_exec_results']['HT_session80490']
ensure(zero_a['exit']==zero_h['exit']==0,'Both actual controllers must exit0 naturally')
ensure(zero_a['parent_pid']==55864 and zero_h['parent_pid']==56304,'Both actual parent identities')
census=zero['fresh_process_census']
ensure(census['CIM_mathematical_compilers_and_dispatchers']==[] and census['Toolhelp_mathematical_compilers']==[] and census['old_A00055864_and_HT56304_absent'] is True,'Actual zeroLean census required')
ensure(zero_a['raw_sha256']==sha(prior_raw) and zero_a['sources']==166,'ZeroLean actual166 receipt binding')
ensure(zero_h['raw_sha256']=='5b827c653d1a07d5de5e8486a6451b33782a5a0b8788625d8fe10ac4b852ed6e' and zero_h['sources']==177,'ZeroLean actual177 receipt binding')
ensure(zero['no_compiler_terminated_or_user_application_changed'] is True,'Actual natural boundary census scope')
ensure(at(zero['checked_utc'])>=at(prior['finished_utc']) and at(zero['checked_utc'])>=at('2026-10-05T08:17:14.160919+00:00'),'ZeroLean census before completed source boundaries')
ensure(at(approval['checked_utc'])>=at(zero['checked_utc']),'Root dispatch predates natural-exit census')
ensure(observed_exit['status']=='ACTUAL_A000_WHOLE_CONTROLLER_EXIT_OBSERVED_BY_BOUND_PROCESS_HANDLE','Actual whole process-handle observation required')
ensure(observed_exit['actual_whole_controller_pid']==55364 and observed_exit['CIM_previously_observed_creation_utc']=='2026-10-05T08:30:14.203519Z','Actual final source-controller PID/start identity')
ensure(observed_exit['actual_process_exit_code']==0,'Actual source-controller handle exit must be zero, never launcher exit')
ensure(observed_exit['observed_source_receipt_sha256']==args.completed171_receipt_sha256 and observed_exit['observed_source_receipt_status']=='PASS','Observed actual controller receipt identity/state')
ensure(observed_exit['observed_source_receipt_finished_utc']==r['finished_utc'] and observed_exit['observed_original_source_successes']==171 and observed_exit['observed_selected_audit_invocations']==1,'Observed actual completed source/audit boundary')
ensure(observed_exit['no_compiler_or_source_or_hold_mutation_by_observer'] is True and observed_exit['old_preflight_session33303_exit0_not_whole_controller_exit'] is True,'Observer exact read-only and launcher distinction')
ensure(at(observed_exit['observer_attached_utc'])>=at(observed_exit['CIM_previously_observed_creation_utc']) and at(observed_exit['exit_observed_utc'])>=at(observed_exit['observer_attached_utc']),'Actual handle observation chronology')
ensure(at(observed_exit['exit_observed_utc'])>=at(r['finished_utc']),'Observed actual process exit before final receipt')
metadata_checks=[]
for name,a in approval['cache_and_dependency_metadata'].items():
    metadata_path,metadata_raw,metadata_obj=record_bound(a['file'],a['sha256'],'Root pinned dependency/runtime/cache metadata '+name)
    ensure(len(metadata_raw)==a['bytes'],'Pinned dependency/runtime/cache metadata size')
    metadata_checks.append(binding(metadata_path))
    if name=='dependencies/4.34.1/mathlib/lake-manifest.json': manifest=metadata_obj
expected_dependencies={'mathlib':{'rev':p['mathlib_pin'],'url':'https://github.com/leanprover-community/mathlib4.git'},**{m['name']:{'rev':m['rev'],'url':m['url']} for m in manifest['packages']}}
ensure(len(expected_dependencies)==9 and len(approval['actual_nine_dependency_HEAD_origins'])==9,'Exact nine pinned dependencies')
dependency_checks=[]
for d in approval['actual_nine_dependency_HEAD_origins']:
    wanted=expected_dependencies[d['name']]
    ensure(d['actual_HEAD']==wanted['rev'] and d['actual_origin']==wanted['url'],'Root exact dependency HEAD/origin provenance')
    actual_head,actual_origin=git_identity_readonly(d['file'])
    ensure(actual_head==d['actual_HEAD'] and actual_origin==d['actual_origin'],'Current pure-read pinned dependency metadata identity')
    dependency_checks.append({'name':d['name'],'file':d['file'],'current_HEAD':actual_head,'current_origin':actual_origin,'method':'Pure installed .git metadata read; no shell/Git command or bulk compiled-dependency rehash'})

scope = classify(p)
whole = set(scope['authored_transitive_whole_Mathlib_closure'])
evidence = loaded['a000224-whole-module-audit-boundary-evidence.json']
expected_whole = {x['module']:x['source_sha256'] for x in evidence['five_authored_whole_modules']}
ensure(set(expected_whole)==whole and len(whole)==5,'Exact frozen five-boundary identity')
ensure(set(approval['five_whole_modules'])==whole and len(approval['five_whole_modules'])==5,'Root exact five-source authorization')
ensure(lease['status']=='ROOT_APPROVED_ACTUAL_A000_FIVE_WHOLE_ORIGINAL_SELECTED3_SOLE_SOURCE_LEASE','Actual root sole lease scope')
ensure(lease['holder_project']=='sakana-a000224' and lease['source_plan_sha256']==BOUND['builds/sakana-a000224/build-plan.json'],'Actual lease holder/plan')
ensure(lease['a000_whole_scope_only_authorized'] is True and lease['other_umbrella_compilers_confirmed_held_or_finished'] is True,'Actual full-mode exception/hand-off')
ensure(lease['zero_other_Lean_compilers_confirmed'] is True and lease['maximum_mathematical_compilers']==1,'Actual exclusive compiler lease')
ensure(lease['actual166_qualification_sha256']==args.qualified166_sha256 and lease['actual166_finished_receipt_sha256']==sha(prior_raw),'Lease actual166 ancestry')
ensure(lease['root_exact_scope_approval']['sha256']==args.root_whole_approval_sha256 and pathlib.Path(lease['root_exact_scope_approval']['file']).resolve()==approvalfile,'Lease actual root scope binding')
ensure(lease['both_exits_zero_Lean_preflight']['sha256']==args.both_exits_zeroLean_record_sha256 and pathlib.Path(lease['both_exits_zero_Lean_preflight']['file']).resolve()==zerofile,'Lease actual controller-exit evidence')
ensure(all(lease[k]==wanted for k,wanted in root_policy.items()),'Lease exact full policy')
ensure(lease['shell_threads']=='-j1' and lease['LEAN_NUM_THREADS']=='1' and lease['source_and_imports_unchanged'] is True and lease['storage_callback_disabled'] is True,'Lease original source/j1/no-storage policy')
recorded_mode = r['resource_settings']['full_mathlib_source_mode']
ensure(recorded_mode['coordinated_lease']==lease and recorded_mode['lease_sha256']==args.whole_lease_sha256,'Executed full-mode lease bytes')
ensure(recorded_mode['a000_exception']['granular_actual_source_successes_required']==166 and set(recorded_mode['a000_exception']['whole_modules'])==whole,'Executed five-only exception')
ensure(r['resource_settings']['runner_source_sha256']==BOUND['run_source_plan.py'],'Actual executed base70ff runner')
ensure(r['resource_settings']['LEAN_NUM_THREADS']==1 and r['resource_settings']['lean_shell_worker_flag']=='-j1','Executed j1/env1 resource settings')
ensure(r['resource_settings']['axiom_parser_source_sha256']==BOUND['audit_axioms.py'],'Executed axiom classifier identity')
modeguard = r['resource_settings']['guarded_third_worker_continuation']
ensure(modeguard['resource_guard_sha256']==BOUND['full_mathlib_resource_guard.py'],'Executed10/11 own guard identity')
ensure(modeguard['owned_job_private_memory_ceiling_bytes']==10*G and modeguard['initial_available_commit_bytes']==11*G,'Executed full-mode allocation/commit policy')

current = {b['module']:b for b in r['builds'] if not b['is_endpoint_audit']}
old = {b['module']:b for b in prior['builds']}
ensure(len(r['builds'])==172 and len(current)==171 and len(old)==166,'Exactly171 source rows plus one original audit required')
ensure(set(old)<=set(current) and all(old[n]==current[n] for n in old),'Preserved166 full rows must match BY MODULE exactly')
new_names = set(current)-set(old)
ensure(new_names==whole and not set(old)&whole,'Exactly five new whole sources only')
entries = {m['module']:m for m in p['modules']}
ensure(set(current)==set(entries),'All171 planned sources must have their actual own pass rows')
source_checks, artifacts = [], []
for n,m in entries.items():
    path=pathlib.Path(m['file']).resolve(); ensure(path.is_relative_to(stage),'Source containment')
    ensure(file_sha(path)==m['sha256'],'Original scientific bytes changed: '+n)
    source_checks.append({'module':n,**binding(path)})
    b=current[n]; ensure(b['exit']==0 and not b.get('stop_reason'),'Non-pass source row: '+n)
    ensure(b.get('source_sha256',m['sha256'])==m['sha256'],'Recorded source SHA: '+n)
    siblings={path.with_suffix(s).resolve() for s in ('.olean','.olean.private','.olean.server','.ilean') if path.with_suffix(s).exists()}
    ensure(siblings=={pathlib.Path(a['file']).resolve() for a in b['artifacts']},'Actual current owned siblings differ: '+n)
    ensure(path.with_suffix('.olean').is_file(),'No own successful olean: '+n)
    for a in b['artifacts']:
        output=pathlib.Path(a['file']).resolve(); ensure(output.is_relative_to(stage),'Artifact containment')
        ensure(output.is_file() and output.stat().st_size==a['bytes'] and file_sha(output)==a['sha256'],'Own output hash/size: '+n)
        artifacts.append({'module':n,**binding(output)})
    if path.with_suffix('.ir').exists():
        artifacts.append({'module':n,'role':'additional_own_IR_sibling_not_used_as_prior_receipt_proof',**binding(path.with_suffix('.ir'))})
for n,wanted in expected_whole.items(): ensure(entries[n]['sha256']==wanted,'Frozen five source hash')

lean = V/'runtimes/lean-4.34.1-windows/bin/lean.exe'
ensure(file_sha(lean)==approval['frozen_bindings']['runtimes/lean-4.34.1-windows/bin/lean.exe'],'Explicit root-bound pinned compiler binary')
ensure('version 4.34.1,' in r['compiler_version'],'Actual compiler version')
ensure(r['compiler_version']==approval['actual_runtime_check'],'Actual complete pinned runtime version/commit identity')
ensure(approval['frozen_bindings']['full_mathlib_resource_guard.py']==BOUND['full_mathlib_resource_guard.py'],'Root exact full guard')
newrows=sorted((current[n] for n in whole),key=lambda b:at(b['started_utc']))
auditrows=[b for b in r['builds'] if b['is_endpoint_audit']]
ensure(len(auditrows)==1 and auditrows[0]['module']=='FreshAudit1.lean','Exact original selected3 audit only')
audit=auditrows[0]
available=set(old); completed_end=at(prior['finished_utc']); checks=[]
for b in newrows+[audit]:
    is_audit=b['is_endpoint_audit']; name=b['module']
    path=stage/'FreshAudit1.lean' if is_audit else pathlib.Path(entries[name]['file'])
    relative=path.relative_to(stage)
    expected_command=[str(lean),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(relative.with_suffix('.olean')),str(relative)]
    ensure(b['command']==expected_command,'New actual semantic CLI: '+name)
    ensure(b['source_sha256']==file_sha(path),'New actual source/audit byte identity: '+name)
    guard=b['own_job_resource_receipt']
    ensure(guard['command']==expected_command and pathlib.Path(guard['cwd']).resolve()==stage,'Guard exact invocation')
    ensure(guard['resource_policy']==POLICY and guard['attempted'] is True,'Exact10/11 invocation resource policy')
    ensure(guard['own_job_assignment_before_resume']=='PASS' and guard['state']=='PASS' and guard['exit']==b['exit']==0,'Actual own-job/child pass')
    ensure(guard['counter_helper_sha256']==BOUND['native_resource_guard.py'] and guard['commit_counter_helper_sha256']==BOUND['resource_metrics.py'],'Exact counter helpers')
    ensure(guard['started_utc']==b['started_utc'] and guard['finished_utc']==b['finished_utc'] and guard['seconds']==b['seconds'],'Exact actual invocation chronology')
    ensure(b['stop_reason'] is None and b['minimum_free_bytes']==guard['minimum_disk_free_bytes'],'Exact stop/reserve row')
    ensure(at(b['started_utc'])>=at(approval['checked_utc']) and at(b['started_utc'])>=completed_end,'Sole serial dispatch order')
    ensure(at(b['finished_utc'])>=at(b['started_utc']),'Invocation time ordering')
    initial=guard['initial_system_memory_snapshot']
    ensure(initial['available_commit_bytes']>=11*G and initial['free_physical_bytes']>=6*G,'Full source initial memory gates')
    ensure(guard['minimum_disk_free_bytes']>=1_000_000_000 and guard['minimum_physical_available_bytes']>=3*G and guard['minimum_available_commit_bytes']>=G,'Actual continuous floors')
    ensure(guard['job_peak_aggregate_private_bytes']<=10*G and guard['job_peak_process_private_bytes']<=10*G,'Actual own caps')
    deps=set(read_imports(path))&set(entries)
    ensure(deps<=available,'Prerequisite not complete before invocation: '+name)
    checkedlogs=logs(guard,b,name)
    if not is_audit: available.add(name)
    completed_end=at(b['finished_utc'])
    checks.append({'module':name,'is_original_selected3_audit':is_audit,'source_sha256':b['source_sha256'],
        'command':expected_command,'LEAN_NUM_THREADS':'1 bound by executed70ff code and resource settings',
        'guard':guard,'raw_log_checks':checkedlogs,'custom_prerequisites_already_completed':sorted(deps)})
ensure(len(newrows)==5 and len(available)==171,'Exact five-phase source assembly')
ensure(completed_end.replace(microsecond=0)<=at(r['finished_utc']),'Final receipt predates actual audit exit')

audit_source=(stage/'FreshAudit1.lean').read_text(encoding='utf8')
requests=re.findall(r'^\s*#print\s+axioms\s+(\S+)',audit_source,re.M)
ensure(requests==ENDPOINTS and len(set(requests))==3,'Exact original selected3 requests')
parsed=parse_axioms(audit['stdout'])
ensure(len(parsed)==3 and collections.Counter(x['endpoint'] for x in parsed)==collections.Counter(ENDPOINTS),'Exactly three unique actual rawprints')
ensure(all(x['classification'] in {'AXIOM_FREE','STANDARD_KERNEL_AXIOMS'} and not x['native_axioms'] and not x['unrecognized_axioms'] and 'sorryAx' not in x['axioms'] for x in parsed),'Selected admission/native/unknown trust found')
ensure(collections.Counter((x['endpoint'],tuple(x['axioms'])) for x in r['selected_audit_axiom_review'])==collections.Counter((x['endpoint'],tuple(x['axioms'])) for x in parsed),'Stored audit review differs from actual raw reparse')
coverage=audit['selected_endpoint_print_coverage']
ensure(coverage['status']=='PASS' and coverage['requested_endpoints']==ENDPOINTS and not coverage['missing_endpoints'] and set(coverage['parsed_endpoints'])==set(ENDPOINTS),'Actual requested print coverage')
for a in audit['artifacts']:
    output=pathlib.Path(a['file']).resolve();ensure(output.is_relative_to(stage) and output.is_file(),'Original audit artifact containment')
    ensure(file_sha(output)==a['sha256'] and output.stat().st_size==a['bytes'],'Original audit output identity')
ensure((stage/'FreshAudit1.olean').is_file(),'Actual original audit own olean absent')
audit_siblings={(stage/'FreshAudit1.lean').with_suffix(s).resolve() for s in ('.olean','.olean.private','.olean.server','.ilean') if (stage/'FreshAudit1.lean').with_suffix(s).exists()}
ensure(audit_siblings=={pathlib.Path(a['file']).resolve() for a in audit['artifacts']},'Original selected audit owned output siblings')

target=pathlib.Path(entries['OpHack.QuadraticResidue224.Target224']['file'])
targettext=target.read_text(encoding='utf8')
adefinition=targettext[targettext.index('def a (n : ℕ) : ℕ :='):targettext.index('\nopen OpHack.QuadraticResidue224')].strip()
ensure(adefinition=='def a (n : ℕ) : ℕ :=\n  if n = 0 then 1\n  else Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))','Literal a-definition scope changed')
statements=[]
for endpoint in ENDPOINTS:
    name=endpoint.rsplit('.',1)[1]; start=targettext.index('theorem '+name+' '); end=targettext.index(':= by',start)
    statement=targettext[start:end].rstrip()
    ensure('(hp : p.Prime) (hq : q.Prime) (hr : r.Prime)' in statement and '(hp2 : 2 < p) (hpq : p < q) (hqr : q < r)' in statement,'Selected ordered odd-prime hypotheses')
    statements.append({'endpoint':endpoint,'exact_statement_before_proof':statement,'statement_utf8_sha256':sha(statement.encode('utf8'))})
ensure(file_sha(target)==expected_whole['OpHack.QuadraticResidue224.Target224'],'Actual frozen target declaration source')
ensure(sha(read_bytes_shared(raw_path))==args.completed171_receipt_sha256,'Finished raw receipt changed during review')
for name,wanted in BOUND.items():ensure(sha(read_bytes_shared(V/name))==wanted,'Bound record/code changed during review')
for m in p['modules']:ensure(file_sha(m['file'])==m['sha256'],'Scientific source changed during review')
for path,wanted in [(qfile,args.qualified166_sha256),(leasefile,args.whole_lease_sha256),(approvalfile,args.root_whole_approval_sha256),(zerofile,args.both_exits_zeroLean_record_sha256),(exitfile,args.whole_controller_exit_record_sha256)]:ensure(file_sha(path)==wanted,'Explicit input record changed during review')

snapshot=V/'operational_history/a000171'/(args.completed171_receipt_sha256[:16]+'.json')
write_new(snapshot,raw)
finished=dt.datetime.now(dt.timezone.utc)
record={'status':'QUALIFIED_ACTUAL_A000171_ORIGINAL_SOURCES_AND_ORIGINAL_SELECTED3_STANDARD_RESTRICTED_THREE_ODD_PRIMES',
    'started_utc':started.isoformat(),'finished_utc':finished.isoformat(),'reviewer':'/root/lean_rebuild',
    'producer':binding(__file__),'immutable171_plus_original_audit_receipt':binding(snapshot),
    'actual166_qualification':binding(qfile),'actual166_immutable_ancestry':binding(priorfile),
    'actual_root_whole_dispatch_approval':binding(approvalfile),'actual_solo_lease':binding(leasefile),'actual_both_controller_exit_zeroLean_record':binding(zerofile),
    'actual_final_whole_controller_process_handle_exit_record':binding(exitfile),'actual_controller_exit_is_not_launcher_exit':True,
    'frozen_record_and_operational_source_bindings':bound_records,
    'current_runtime_dependency_cache_metadata_checks':metadata_checks,'current_nine_pinned_HEAD_origin_pure_metadata_checks':dependency_checks,
    'counts':{'planned_original_source_modules':171,'actual_original_source_modules_PASS':171,'prior_actual_granular_rows_retained_BY_MODULE':166,'new_whole_source_successes':5,'new_original_selected_audit_invocations':1,'unique_actual_selected_prints':3},
    'preserved166_full_rows_BY_MODULE_exact':True,'prior_diverse76_plus_guarded90_policies_not_reclassified_as10_11':True,
    'all171_current_source_checks':source_checks,'all171_current_own_artifact_checks':artifacts,
    'new5_and_original_audit_actual_command_guard_log_chronology_checks':checks,
    'new_phase_only_full_policy':POLICY,'selected3_actual_raw_output_classifications':parsed,
    'selected3_raw_stdout_sha256':audit['own_job_resource_receipt']['stdout_sha256'],
    'selected3_classification_counts':dict(collections.Counter(x['classification'] for x in parsed)),
    'exact_statement_source':binding(target),'exact_a_definition':adefinition,'exact_restricted_statements':statements,
    'scientific_scope':'For three ordered distinct odd primes2<p<q<r, using the literal quadratic-residue-cardinality definitiona, the source proves nondivisibility, noncongruence, and the restricted equivalence at n=p*q*r. This does not prove the full A000224 conjecture for alln, repeated prime factors, even cases or other factor counts.',
    'no_score_novelty_priority_publication_release_upgrade':True,
    'limitations':['Guard10/11 applies only to these five whole sources and original audit.166 prior rows and their separate storage/guard diversity remain exactly as previously qualified.',
        'Three raw selected outputs are examined; source-wide absence of every possible imported admission is not inferred from source exit0. No native/unknown/sorry may reach these three selected outputs.',
        'Root SHA-bound dated actual natural exits/zeroLean evidence and sole lease are required. This qualifier performs no new process census or compiler invocation.',
        'No bulk official-provider artifact rehash or new storage/mmap measurement. Future exact runtime SHA is supplied by root actual approval and matched against actual command binary.',
        'Potential other pending families and HT source/audit incompleteness remain separate. This scope does not establish competitionplacement, mathematical priority or a release decision.'],
    'actions':{'compiler_or_native_guard_invoked':False,'source_canonical_hold_lease_or_storage_modified':False,'output_alias_or_copy_operation':False,'only_new_outputs':['immutable byte-identical future171 raw JSON','additive qualification JSON']}}
out=V/('A000-actual171-original-selected3-postwhole-readonly-qualification-'+finished.strftime('%Y%m%dT%H%M%S%fZ')+'.json')
data=(json.dumps(record,ensure_ascii=False,indent=2)+'\n').encode('utf8');write_new(out,data)
print(json.dumps({'status':record['status'],'qualification':binding(out),'immutable':binding(snapshot),'counts':record['counts'],'classification_counts':record['selected3_classification_counts']},ensure_ascii=False),flush=True)
