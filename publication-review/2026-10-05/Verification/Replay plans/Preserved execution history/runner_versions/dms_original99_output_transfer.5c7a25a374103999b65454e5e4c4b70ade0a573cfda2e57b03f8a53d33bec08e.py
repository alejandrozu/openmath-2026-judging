"""Prepare or execute a separately reviewed transfer of our own fresh outputs.

The policy preparation copies nothing. Execution requires a SHA-bound explicit
root approval receipt; it never invokes Lean. Transferred outputs remain labeled
as previous original-route cold passes, never as new diagnostic compilations.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,shutil,sys,time
from verify_dms_full228_stage import verify_stage
BASE=Path(__file__).resolve().parent
STAGE=BASE/'builds/htpeo-dms-current-import-pruned-diagnostic'
ORIGINAL=BASE/'builds/htpeo-dms-current'
POLICY=BASE/'dms-original99-output-transfer-policy-20261005.json'
SEED_RECEIPT=BASE/'dms-original99-output-transfer-completed-20261005.json'
def digest(path):
    d=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):d.update(block)
    return d.hexdigest()
def load(path):return json.loads(Path(path).read_bytes())
def now():return datetime.now(timezone.utc).isoformat()
def save_new(path,value):
    assert not path.exists(),str(path)
    with path.open('x',encoding='utf8') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    return digest(path)

def prepare():
    root_review=BASE/'dms-full228-root-cold-stage-review-20261005.json'
    assert digest(root_review)=='1fba31215197f9bff1bc2ab30916cfd4dd07ce09d285f6872271d4ffe4eea746'
    check=verify_stage(require_cold=True)
    proposal=load(BASE/'dms-full228-complete-official-closure-and-reuse-proposal-20261005.json')
    stage_plan=load(STAGE/'build-plan.json')
    eligibility=load(proposal['owned_output_eligibility_inventory']['file'])
    original_receipt=load(stage_plan['original119_immutable_receipt'])
    passed={row['module']:row for row in original_receipt['builds'] if row.get('exit')==0 and not row.get('is_endpoint_audit')}
    modules={row['module']:row for row in stage_plan['modules']}
    transfers=[];reuse=[]
    for name in check['eligible99_module_names']:
        row=passed[name];entry=modules[name]
        src=Path(entry['original_file']).resolve();dst=Path(entry['file']).resolve()
        assert src.is_relative_to(ORIGINAL.resolve()) and dst.is_relative_to(STAGE.resolve())
        actual=[]
        for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
            path=src.with_suffix(suffix)
            if path.is_file():actual.append(path)
        declared={Path(a['file']).resolve():a for a in row['artifacts']}
        assert set(actual)==set(declared),'All sibling outputs must be covered by the original119 receipt'
        artifact_records=[]
        for artifact in actual:
            old=declared[artifact];target=dst.with_suffix(artifact.name[len(src.stem):])
            assert artifact.is_relative_to(ORIGINAL.resolve()) and target.is_relative_to(STAGE.resolve())
            assert not target.exists() and digest(artifact)==old['sha256'] and artifact.stat().st_size==old['bytes']
            record={'module':name,'original_owned_output':str(artifact),
                'diagnostic_target':str(target),'bytes':old['bytes'],'sha256':old['sha256'],
                'artifact_kind':artifact.name[len(src.stem):],
                'classification':'TRANSFER_OF_PREVIOUS_OWN_ORIGINAL_ROUTE_COLD_OUTPUT_NO_NEW_COMPILATION'}
            transfers.append(record);artifact_records.append(record)
        candidate=next(r for r in eligibility['modules'] if r['module']==name)
        reuse.append({'module':name,'original_and_actual_staged_source_sha256':entry['sha256'],
            'original_PASS_row_source_sha256':row['source_sha256'],
            'original_PASS_row_sha256':candidate['original_PASS_row_sha256'],
            'entire_unaffected_custom_dependency_closure':candidate['custom_dependency_closure'],
            'transferred_previous_own_cold_output_artifacts':artifact_records,
            'fresh_diagnostic_compilation':False})
    assert len(reuse)==99 and len({r['diagnostic_target'] for r in transfers})==len(transfers)
    policy={'status':'PREPARED_EXACT99_TRANSFER_POLICY_NO_COPY_NO_LEAN_ROOT_EXECUTION_REVIEW_REQUIRED',
        'prepared_utc':now(),'original_family':'htpeo-dms-current','diagnostic_route':stage_plan['id'],
        'source_plan':str(STAGE/'build-plan.json'),'source_plan_sha256':digest(STAGE/'build-plan.json'),
        'root_cold_stage_review':str(root_review),'root_cold_stage_review_sha256':digest(root_review),
        'read_only_stage_verifier_sha256':digest(BASE/'verify_dms_full228_stage.py'),
        'immutable_original119_receipt':stage_plan['original119_immutable_receipt'],
        'immutable_original119_receipt_sha256':stage_plan['original119_immutable_receipt_sha256'],
        'full_official2735_closure':stage_plan['exact_full_official_closure'],
        'full_official2735_closure_sha256':stage_plan['exact_full_official_closure_sha256'],
        'module_count':99,'artifact_count':len(transfers),'total_output_bytes':sum(r['bytes'] for r in transfers),
        'eligible99_module_names':check['eligible99_module_names'],'modules':reuse,'output_transfers':transfers,
        'required129_new_cold_module_names':check['all129_required_cold_sources'],
        'affected125_modules_must_remain_cold':check['all125_affected_sources_must_remain_cold'],
        'scientific_coverage_labels':{'reused_previous_own_original_route_cold_sources':99,
            'required_new_cold_diagnostic_sources':129,'total_authored_scientific_bodies':228},
        'LEAN_PATH_policy':'Only new diagnostic stage plus verified official dependency libraries; original custom-output directory is forbidden.',
        'transfer_disk_floor_bytes':1_000_000_000,
        'execution_requirements':'SHA-bound ROOT_APPROVED_OUTPUT_TRANSFER_ONLY_NO_LEAN receipt; exact policy/helper/source/stage/runtime/dependency revalidation; no overwrite.',
        'qualification':'This policy performs no copy and does not authorize Lean. All125affected+4unpassed remain cold;99 transfers never appear as new compilation invocations.'}
    policy_sha=save_new(POLICY,policy)
    print(json.dumps({'policy':str(POLICY),'policy_sha256':policy_sha,'modules':99,
        'artifacts':len(transfers),'output_bytes':policy['total_output_bytes'],'copies_performed':0}),flush=True)

def transfer(approval_path,approval_sha):
    approval_path=Path(approval_path).resolve()
    assert approval_path.is_relative_to(BASE.resolve()) and digest(approval_path)==approval_sha
    approved=load(approval_path)
    assert approved['status']=='ROOT_APPROVED_OUTPUT_TRANSFER_ONLY_NO_LEAN'
    assert approved['reviewed_policy_sha256']==digest(POLICY)
    assert approved['reviewed_seed_helper_sha256']==digest(__file__)
    policy=load(POLICY)
    assert not SEED_RECEIPT.exists() and not (BASE/(policy['diagnostic_route']+'-fresh-build.json')).exists()
    check=verify_stage(require_cold=True)
    assert check['eligible99_module_names']==policy['eligible99_module_names']
    assert digest(policy['source_plan'])==policy['source_plan_sha256']
    assert approved['approved99module_names']==policy['eligible99_module_names']
    assert shutil.disk_usage(BASE).free>=policy['transfer_disk_floor_bytes']+policy['total_output_bytes']
    initial_canonical_sha=digest(BASE/'htpeo-dms-current-fresh-build.json')
    result={'status':'OWN_ORIGINAL99_OUTPUT_TRANSFER_RUNNING_NO_LEAN','started_utc':now(),
        'approval_receipt':str(approval_path),'approval_receipt_sha256':approval_sha,
        'policy_file':str(POLICY),'policy_sha256':digest(POLICY),'seed_helper_sha256':digest(__file__),
        'immutable_original119_receipt_sha256':digest(policy['immutable_original119_receipt']),
        'stage_source_plan_sha256':policy['source_plan_sha256'],'modules':policy['modules'],
        'scientific_coverage_labels':policy['scientific_coverage_labels'],
        'output_transfers':[],'minimum_disk_free_bytes':shutil.disk_usage(BASE).free,
        'new_Lean_compilation_invocations':0,'original_custom_output_directory_allowed_on_LEAN_PATH':False}
    progress=BASE/'dms-original99-output-transfer-progress-20261005.json'
    assert not progress.exists()
    def save_progress():
        temp=progress.with_suffix('.json.tmp')
        temp.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8');os.replace(temp,progress)
    save_progress()
    for item in policy['output_transfers']:
        source=Path(item['original_owned_output']).resolve();target=Path(item['diagnostic_target']).resolve()
        assert source.is_relative_to(ORIGINAL.resolve()) and target.is_relative_to(STAGE.resolve())
        assert digest(source)==item['sha256'] and source.stat().st_size==item['bytes'] and not target.exists()
        temporary=target.with_name(target.name+'.owned-transfer-incomplete')
        assert not temporary.exists()
        with source.open('rb') as src,temporary.open('xb') as dst:
            for block in iter(lambda:src.read(1024*1024),b''):
                free=shutil.disk_usage(BASE).free
                result['minimum_disk_free_bytes']=min(result['minimum_disk_free_bytes'],free)
                assert free>=policy['transfer_disk_floor_bytes'], 'Own transfer halted at disk reserve; bytes preserved'
                dst.write(block)
        assert digest(temporary)==item['sha256']
        temporary.rename(target)
        result['output_transfers'].append(dict(item,target_sha256=digest(target),
            original_owned_output_still_identical=digest(source)==item['sha256']))
        save_progress()
    assert len(result['output_transfers'])==policy['artifact_count']
    assert digest(BASE/'htpeo-dms-current-fresh-build.json')==initial_canonical_sha
    for item in policy['output_transfers']:assert digest(item['original_owned_output'])==item['sha256']
    result['status']='EXACT99_PREVIOUS_OWN_COLD_OUTPUT_TRANSFER_COMPLETE_NO_NEW_DIAGNOSTIC_COMPILATION'
    result['finished_utc']=now();result['original_canonical_receipt_unchanged_sha256']=initial_canonical_sha
    result['eligible99_module_names']=policy['eligible99_module_names']
    result['required129_new_cold_module_names']=policy['required129_new_cold_module_names']
    seed_sha=save_new(SEED_RECEIPT,result);save_progress()
    print(json.dumps({'seed_receipt':str(SEED_RECEIPT),'seed_receipt_sha256':seed_sha,
        'transferred_previous_own_cold_sources':99,'new_Lean_compilations':0,'required_new_diagnostic_sources':129}),flush=True)

def verify_seed(policy_sha,seed_sha):
    assert digest(POLICY)==policy_sha and digest(SEED_RECEIPT)==seed_sha
    policy=load(POLICY);seed=load(SEED_RECEIPT)
    assert seed['status']=='EXACT99_PREVIOUS_OWN_COLD_OUTPUT_TRANSFER_COMPLETE_NO_NEW_DIAGNOSTIC_COMPILATION'
    assert seed['policy_sha256']==policy_sha and seed['stage_source_plan_sha256']==digest(STAGE/'build-plan.json')
    assert seed['new_Lean_compilation_invocations']==0 and seed['eligible99_module_names']==policy['eligible99_module_names']
    assert seed['scientific_coverage_labels']==policy['scientific_coverage_labels']
    assert len(seed['output_transfers'])==len(policy['output_transfers'])==policy['artifact_count']
    for expected,actual in zip(policy['output_transfers'],seed['output_transfers']):
        assert all(actual[key]==value for key,value in expected.items())
        assert actual['target_sha256']==expected['sha256']==digest(expected['diagnostic_target'])
        assert digest(expected['original_owned_output'])==expected['sha256']
    assert seed['original_custom_output_directory_allowed_on_LEAN_PATH'] is False
    return {'status':'EXACT99_TRANSFER_IDENTITY_VERIFIED_PREVIOUS_OWN_COLD_OUTPUTS_NOT_NEW_COMPILES',
        'policy_sha256':policy_sha,'seed_receipt_sha256':seed_sha,
        'reused_previous_own_cold_source_count':99,'new_diagnostic_compilations':0,
        'modules':seed['modules'],'required129_new_cold_module_names':policy['required129_new_cold_module_names'],
        'LEAN_PATH_original_custom_directory_forbidden':str(ORIGINAL.resolve())}

if __name__=='__main__':
    if sys.argv[1:]==['--prepare-policy']:prepare()
    elif len(sys.argv)==4 and sys.argv[1]=='--transfer-root-approved':transfer(sys.argv[2],sys.argv[3])
    else:raise SystemExit('Use --prepare-policy or --transfer-root-approved approval_receipt approval_sha256; preparation alone authorizes no copy or Lean.')
