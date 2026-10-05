"""Read-only final qualification, only after a separate SHA-bound root review.

All228 scientific bodies/options/audits remain unchanged.99 original-owned passes
are imported from proven V1 copies read-only,122 unaffected V3-new passes are
linked into V4, and seven affected sources must have actual new V4 rows. No novelty, scoring, publication or release is authorized here.
"""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,re,sys
from receipt_io import read_bytes_shared
from lean_imports import stripped
from audit_axioms import parse as parse_axioms
from verify_dms_v4_vector_stage import verify_stage
from dms_v4_vector122_seed import verify_seed
from dms_v3_copy99_hardlink_seed import preserved_check
BASE=Path(__file__).resolve().parent
PROJECT='htpeo-dms-current-import-pruned-v4-vector'
STAGE=BASE/'builds'/PROJECT
PLAN_SHA='30f7b071fbcd9ddb37e48a059126daf8e37dd65dae9b2733614af926589a7308'
RUNNER_SHA='96e616f35df492576c8b26909bc76782f476370e08c607883daff706e04456dc'
POLICY_SHA='0af7feab4fc55f1b7ecade9b60491c2507ac3687d2899f0f74116afd40a93a8f'
# Actual future seed SHA must be explicitly reviewed in the root final approval.
ORIGINAL119_SHA='feb37da0178c7ad7f259096eba604ab43ae253bcaaac5212d66a2748ffc84238'
VERIFIER_SHA='d876f0d7850b4618ff4855aad2306216f6921987936daea24a820fef798b6242'
SEED_HELPER_SHA='219fa8cd4bbd3d90ca80f3ad4e0ac662b6a7083afc819d88d1cbd5ba93d73df4'

def digest(path):
    d=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):d.update(block)
    return d.hexdigest()
def load(path):return json.loads(Path(path).read_bytes())
def now():return datetime.now(timezone.utc).isoformat()

def exact_invocation_identity(row,file,expected_command):
    """Bind actual source, semantic CLI, own guard, and byte-identical raw logs."""
    assert row['source_sha256']==digest(file)
    assert row['command']==expected_command
    guard=row['own_job_resource_receipt']
    assert guard['attempted'] is True and guard['own_job_assignment_before_resume']=='PASS'
    assert guard['command']==expected_command and Path(guard['cwd']).resolve()==STAGE.resolve()
    assert guard['exit']==row['exit'] and guard['seconds']==row['seconds']
    assert guard['started_utc']==row['started_utc'] and guard['finished_utc']==row['finished_utc']
    if row['exit']==0 and row.get('stop_reason') is None:
        assert guard['state']=='PASS'
    logs=[]
    for channel in ['stdout','stderr']:
        path=Path(guard[channel+'_file']).resolve()
        assert path.is_relative_to((BASE/'guarded-source-logs').resolve())
        assert path.name.startswith(PROJECT+'-')
        raw=path.read_bytes();actual=hashlib.sha256(raw).hexdigest()
        assert actual==guard[channel+'_sha256']
        assert raw==row[channel].encode('utf8'),'Current raw guard log bytes must equal the recorded row text bytes'
        logs.append({'channel':channel,'file':str(path),'sha256':actual,'bytes':len(raw),'raw_bytes_equal_row':True})
    return {'source_sha256':digest(file),'actual_command':expected_command,'own_guard_state':guard['state'],
        'own_guard_exit':guard['exit'],'guard_assignment_before_resume':'PASS','current_raw_logs':logs}

def qualify(approval_path,approval_sha):
    approval_path=Path(approval_path).resolve()
    assert approval_path.is_relative_to(BASE.resolve()) and digest(approval_path)==approval_sha
    approved=load(approval_path)
    assert approved['status']=='ROOT_APPROVED_DMS_V4_FINAL_QUALIFICATION_READ_ONLY'
    SEED_SHA=approved['reviewed_seed_receipt_sha256'];assert re.fullmatch('[0-9a-f]{64}',SEED_SHA)
    assert approved['reviewed_qualification_helper_sha256']==digest(__file__)
    assert approved['reviewed_runner_sha256']==RUNNER_SHA
    assert approved['reviewed_policy_sha256']==POLICY_SHA and approved['reviewed_seed_receipt_sha256']==SEED_SHA
    assert digest(BASE/'run_dms_v4_vector_plan.py')==RUNNER_SHA
    assert digest(BASE/'verify_dms_v4_vector_stage.py')==VERIFIER_SHA
    assert digest(BASE/'dms_v4_vector122_seed.py')==SEED_HELPER_SHA
    plan_path=STAGE/'build-plan.json';assert digest(plan_path)==PLAN_SHA
    plan=load(plan_path);assert plan['version']=='4.33.1' and plan.get('lean_options',{})=={}
    receipt_path=BASE/(PROJECT+'-fresh-build.json');raw=read_bytes_shared(receipt_path)
    receipt_sha=hashlib.sha256(raw).hexdigest()
    assert receipt_sha==approved['reviewed_actual_source_receipt_sha256']
    receipt=json.loads(raw)
    assert receipt.get('current_module') is None and receipt.get('waiting_for_module') is None
    assert receipt['resource_settings']['runner_source_sha256']==RUNNER_SHA
    assert receipt['modules']==plan['modules'] and receipt.get('finished_utc'), 'Actual final scoped receipt required'
    assert '4.33.1' in receipt['compiler_version'] and '819816b' in receipt['compiler_version']
    original_and_v1=preserved_check()
    assert digest(plan['original119_immutable_receipt'])==ORIGINAL119_SHA
    stage_identity=verify_stage(require_cold=False,linked122_allowed=True)
    seed_identity=verify_seed(POLICY_SHA,SEED_SHA)
    required=set(seed_identity['required7_new_cold_module_names'])
    reused=set(seed_identity['prior221_names'])
    assert len(required)==7 and len(reused)==221 and required.isdisjoint(reused)
    entries={r['module']:r for r in plan['modules']}
    assert set(entries)==required|reused and len(entries)==228
    source_rows=[r for r in receipt['builds'] if not r['is_endpoint_audit']]
    rows_by_name={r['module']:r for r in source_rows}
    assert len(rows_by_name)==len(source_rows) and not set(rows_by_name)&reused
    actual_pass=[];actual_failure=[];artifact_records=[];actual_source_invocation_identities=[]
    lean=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
    for name,row in rows_by_name.items():
        assert name in required
        entry=entries[name];file=Path(entry['file']);relative=file.relative_to(STAGE)
        assert digest(file)==entry['sha256']==row['source_sha256']
        expected_command=[str(lean),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000',
            '-o',str(relative.with_suffix('.olean')),str(relative)]
        assert row['command']==expected_command,('Authored semantic CLI differs',name)
        actual_source_invocation_identities.append({'module':name,**exact_invocation_identity(row,file,expected_command)})
        if row['exit']!=0 or row.get('stop_reason'):
            actual_failure.append({'module':name,'exit':row['exit'],'stop_reason':row.get('stop_reason')});continue
        paths=[file.with_suffix(s) for s in ['.olean','.olean.private','.olean.server','.ilean'] if file.with_suffix(s).exists()]
        declared={Path(r['file']).resolve():r for r in row['artifacts']}
        assert set(p.resolve() for p in paths)==set(declared) and file.with_suffix('.olean').exists()
        for path,item in declared.items():
            assert path.is_relative_to(STAGE.resolve()) and digest(path)==item['sha256'] and path.stat().st_size==item['bytes']
            artifact_records.append({'module':name,**item,'current_hash_and_bytes_match':True})
        actual_pass.append(name)
    audit_identity=[];requested=[];parsed=[];raw_print_receipts=[]
    for audit in plan['audit_modules']:
        audit_file=STAGE/audit
        requests=re.findall(r'^\s*#print\s+axioms\s+(\S+)',stripped(audit_file.read_text(encoding='utf8')),re.M)
        requested+=requests
        audit_rows=[r for r in receipt['builds'] if r['is_endpoint_audit'] and r['module']==audit]
        assert len(audit_rows)<=1
        item={'audit':audit,'source_sha256':digest(audit_file),'requested_endpoints':requests,'attempted':bool(audit_rows)}
        if audit_rows:
            row=audit_rows[0]
            relative=audit_file.relative_to(STAGE)
            expected_command=[str(lean),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000',
                '-o',str(relative.with_suffix('.olean')),str(relative)]
            item['actual_audit_source_command_guard_and_raw_log_identity']=exact_invocation_identity(row,audit_file,expected_command)
            item.update(exit=row['exit'],stop_reason=row.get('stop_reason'),stdout_sha256=hashlib.sha256(row['stdout'].encode()).hexdigest(),stderr_sha256=hashlib.sha256(row['stderr'].encode()).hexdigest())
            actual=parse_axioms(row['stdout']);parsed+=actual
            raw_print_receipts.append({'audit':audit,'actual_stdout':row['stdout'],'actual_stderr':row['stderr'],
                'actual_command':row['command'],'actual_exit':row['exit'],'actual_row':row})
            item['printed_endpoints']=[r['endpoint'] for r in actual]
        audit_identity.append(item)
    assert len(requested)==len(set(requested))==123
    count=Counter(r['endpoint'] for r in parsed)
    missing=sorted(set(requested)-set(count));unexpected=sorted(set(count)-set(requested))
    duplicate=sorted(name for name,n in count.items() if n!=1)
    admissions=[r for r in parsed if r['classification']=='SORRY_ADMISSION']
    unknown=[r for r in parsed if r['classification']=='UNRECOGNIZED_AXIOMS']
    native=[r for r in parsed if r['classification']=='NATIVE_EVALUATION_TRUST']
    source_complete=set(actual_pass)==required and not actual_failure
    audit_complete=not missing and not unexpected and not duplicate and len(parsed)==123 and all(
        a.get('exit')==0 and a.get('stop_reason') is None for a in audit_identity)
    qualified=source_complete and audit_complete and not admissions and not unknown
    if qualified:
        status=('QUALIFIED_BODY_IDENTICAL_ROUTE_WITH_PREVIOUS_OWN_COLD_OUTPUT_REUSE_NATIVE_EVALUATION_DISCLOSED'
                if native else 'QUALIFIED_BODY_IDENTICAL_ROUTE_WITH_PREVIOUS_OWN_COLD_OUTPUT_REUSE_STANDARD_ENDPOINTS')
    elif admissions or unknown:status='NOT_QUALIFIED_SELECTED_ADMISSION_OR_UNKNOWN_AXIOMS'
    else:status='NOT_QUALIFIED_MISSING_ACTUAL_SOURCE_OR_SELECTED_COVERAGE'
    result={'status':status,'qualified':qualified,'checked_utc':now(),
        'root_approval':str(approval_path),'root_approval_sha256':approval_sha,'qualification_helper_sha256':digest(__file__),
        'final_source_receipt':str(receipt_path),'final_source_receipt_sha256':receipt_sha,'recorded_runner_status':receipt['status'],
        'source_plan_sha256':PLAN_SHA,'runner_sha256':RUNNER_SHA,'policy_sha256':POLICY_SHA,'seed_sha256':SEED_SHA,
        'compiler_version_recorded_by_actual_runner':receipt['compiler_version'],
        'current_pinned_compiler_executable_sha256':digest(lean),
        'current_resource_guard_sha256':digest(BASE/'matt_resource_guard.py'),
        'original119_and_failed_v1_preservation':original_and_v1,'original119_immutable_receipt_sha256':ORIGINAL119_SHA,
        'original_scientific_and_scored_scope':'UNALTERED228_SCIENTIFIC_BODIES_OPTIONS_COMMENTS_AND123_ORIGINAL_ENDPOINTS;ORIGINAL_THREE_IMPORT_HEADER_SPANS_PLUS_DIRECT_INFLATIONA_VECNOTATION_IMPORT',
        'all228_body_identity_and2735_official_source_artifact_runtime_git_cache_identity':stage_identity,
        'post_run221_readonly99_and_linked122_identity_and_all_original_V1_V2_V3_protection':seed_identity,
        'existing_V1_copy99_readonly_inputs_and_original_V2_V1_V3_protected99_linkcount2_preservation':True,
        'prior_own_original_cold_source_outputs_reused_readonly99':99,'prior_V3_new_own_cold_source_passes_reused_linked122':122,'new_V4_cold_source_passes':len(actual_pass),
        'new_actual_source_module_names':sorted(actual_pass),'required_new7_module_names':sorted(required),
        'source_failures_or_resources':actual_failure,'missing_actual_new_source_modules':sorted(required-set(actual_pass)),
        'current7_V4_artifact_hashes':artifact_records,'actual7_V4_source_CLI_guard_raw_log_identities':actual_source_invocation_identities,'actual_selected_audit_identity':audit_identity,
        'requested_endpoint_count':123,'actual_unique_print_count':len(count),'missing_prints':missing,'unexpected_prints':unexpected,'duplicate_prints':duplicate,
        'axiom_parser_sha256':digest(BASE/'audit_axioms.py'),'selected123_actual_axiom_classifications':parsed,
        'selected_classification_counts':dict(Counter(r['classification'] for r in parsed)),
        'selected_admitted':admissions,'selected_unknown_axioms':unknown,'selected_native_trust':native,
        'native_trust_qualification':'Recognized native reduction axioms rely on the pinned evaluator/compiler/runtime; they are disclosed separately from standard kernel axioms.',
        'actual_raw_print_receipts':raw_print_receipts,'compiler_invocations_in_this_helper':0,
        'qualification_limits':'This independently rechecks proof replay and body/import/dependency provenance. It does not decide mathematical novelty, statement faithfulness, competition scores or publication.'}
    assert read_bytes_shared(receipt_path)==raw,'Final source receipt changed during read-only qualification'
    out=BASE/'dms-v4-vector-complete-route-final-qualification-20261005.json'
    assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'qualification':str(out),'qualification_sha256':digest(out),'status':status,
        'prior_owned_reused':221,'actual_new_cold_passes':len(actual_pass),'actual_unique_prints':len(count),
        'admitted':len(admissions),'unknown_axioms':len(unknown),'native_endpoints':len(native)},indent=2),flush=True)

if __name__=='__main__':
    if len(sys.argv)!=4 or sys.argv[1]!='--qualify-root-approved':
        raise SystemExit('Prepared only. Final execution requires --qualify-root-approved approval_path approval_sha after root review and actual source/audit completion.')
    qualify(sys.argv[2],sys.argv[3])
