"""Prepared separate exact157 source-output reuse; no actions merely by import.
Every operational mode requires a later exact SHA-bound root approval.
The reviewed pp.unicode.fun difference is preserved, never called identical CLI.
"""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,os,re,subprocess,sys
from receipt_io import read_bytes_shared
from lean_imports import read_imports
BASE=Path(__file__).resolve().parent
POLICY=BASE/'compatible-FC-exact157-prior-own-output-policy-20261005.json'
PROVIDERS=BASE/'proposals/compatible-FC-exact157/official-source-artifact-closure.json'
DONOR=BASE/'builds/sundai-erdos3-original-image-source'
TARGET=BASE/'builds/official-fc-util433'
DONOR_REPORT=BASE/'sundai-erdos3-original-image-source-fresh-build.json'
DONOR_QUAL=BASE/'original-E65-noTactic183-completed-own-source-qualification-20261005.json'
SEED=BASE/'compatible-FC-exact157-hardlink-seed-completed-20261005.json'
TARGET_REPORT=BASE/'official-fc-util433-exact157-linked-granular-fresh-build.json'
TARGET_QUAL=BASE/'compatible-FC-exact157-plus66-granular-completed-qualification-20261005.json'
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir']
FORBIDDEN_OUTPUT_SUFFIXES=SUFFIXES+['.c','.c.o','.o','.dll']
ROOT_PP_SHA='7550b5203048ea7cc29539bef5b039d7c43bd6ec66d3d3a96d2b8664e8806cb4'
NTFS_HELPER_SHA='cf35eb78ccf5e36e7775eb0d4d676de2cf6cf57d5ee5b8cbb8878827a0f5ae4e'
def digest(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def load(p):return json.loads(Path(p).read_bytes())
def now():return datetime.now(timezone.utc).isoformat()
def save_new(p,x):
    with p.open('x',encoding='utf8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
    return digest(p)
def ntfs_helpers():
    assert digest(BASE/'htpeo_m2_original97_hardlink_seed.py')==NTFS_HELPER_SHA
    # Read-only Win32 identities from the preserved helper; no HT seed mode runs.
    from htpeo_m2_original97_hardlink_seed import file_identity,inode_key,volume_identity
    return file_identity,inode_key,volume_identity
def approval(file,sha,status):
    p=Path(file).resolve();assert p.is_relative_to(BASE.resolve()) and digest(p)==sha
    a=load(p);assert a['status']==status and a['seed_and_qualification_helper_sha256']==digest(__file__)
    assert digest(POLICY)==a['policy_sha256']
    return p,a
def inactive(allow_own_target_runner=False):
    cmd="Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|python)(\\.exe)?$' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,CreationDate | ConvertTo-Json -Compress"
    r=subprocess.run(['powershell','-NoProfile','-Command',cmd],capture_output=True,text=True,encoding='utf8',errors='replace',check=True)
    rows=json.loads(r.stdout or '[]');rows=rows if isinstance(rows,list) else [rows]
    forbidden=[]
    for row in rows:
        text=(row.get('CommandLine') or '').replace('\\','/').lower()
        if allow_own_target_runner and row['ProcessId']==os.getpid() and 'run_compatible_fc157_linked_granular_plan.py' in text:continue
        donor_driver=('run_original_e65' in text or 'dispatch_original_e65' in text) and 'sundai-erdos3-original-image-source' in text
        target_driver=any(n in text for n in ['run_m2_granular_source_plan.py','run_m2_tactic_aware_granular_source_plan.py','run_compatible_fc157_linked_granular_plan.py']) and 'official-fc-util433' in text
        if donor_driver or target_driver or '/builds/sundai-erdos3-original-image-source/' in text or '/builds/official-fc-util433/' in text:forbidden.append(row)
    assert not forbidden,('Donor/target route must be quiescent except exact executing target runner',forbidden)
    return {'checked_utc':now(),'donor_and_other_target_dispatchers_quiescent':True,'process_snapshot':rows}
def source_runtime_provider_check(policy_sha):
    assert digest(POLICY)==policy_sha;p=load(POLICY)
    assert digest(BASE/'pp-unicode-fun-root-narrow-future-option-difference-review-20261005.json')==ROOT_PP_SHA==p['root_pp_option_review_sha256']
    for r in p['bound_files']:assert digest(r['file'])==r['sha256'],r['file']
    for r in p['all183_donor_source_identities']:
        assert digest(r['file'])==r['sha256']
    for r in p['all233_target_source_identities']:
        assert digest(r['file'])==r['sha256']
    for r in p['exact_original_nine_packages']:
        got=subprocess.run(['git','rev-parse','HEAD'],cwd=r['prepared_source_path'],capture_output=True,text=True,check=True).stdout.strip()
        assert got==r['original_manifest_rev']
    assert digest(PROVIDERS)==p['full183_official_provider_manifest_sha256']
    providers=load(PROVIDERS);names={r['module'] for r in providers}
    for r in providers:
        assert digest(r['source_file'])==r['source_sha256']
        assert all(d in names for d in r['effective_import_dependencies'])
        for a in r['official_artifacts']:
            assert digest(a['file'])==a['sha256'] and Path(a['file']).stat().st_size==a['bytes']
    assert 'Mathlib' not in names and 'Mathlib.Tactic' not in names
    return p
def exact_row(row,entry,stage,options):
    f=Path(entry['file']);relative=f.relative_to(stage)
    cmd=[str(BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000']
    cmd+=['-D'+k+'='+str(v).lower() for k,v in options.items()]
    cmd+=['-o',str(relative.with_suffix('.olean')),str(relative)]
    assert row['source_sha256']==entry['sha256']==digest(f) and row['command']==cmd
    if 'effective_lean_options' in row:assert row['effective_lean_options']==options
    assert row['exit']==0 and row.get('stop_reason') is None and not row['is_endpoint_audit']
    g=row['own_job_resource_receipt']
    assert g['attempted'] is True and g['state']=='PASS' and g['exit']==0 and g['command']==cmd
    assert Path(g['cwd']).resolve()==stage.resolve() and g['own_job_assignment_before_resume']=='PASS'
    assert row['started_utc']==g['started_utc'] and row['finished_utc']==g['finished_utc'] and row['seconds']==g['seconds']
    for c in ['stdout','stderr']:
        log=Path(g[c+'_file']).resolve();assert log.is_relative_to((BASE/'guarded-source-logs').resolve())
        raw=log.read_bytes();assert hashlib.sha256(raw).hexdigest()==g[c+'_sha256'] and raw==row[c].encode('utf8')
    paths=[f.with_suffix(s) for s in SUFFIXES if f.with_suffix(s).exists()]
    declared={Path(a['file']).resolve():a for a in row['artifacts']}
    assert set(x.resolve() for x in paths)==set(declared) and f.with_suffix('.olean').exists()
    out=[]
    identity,_,_=ntfs_helpers()
    for file,a in declared.items():
        assert file.is_relative_to(stage.resolve()) and digest(file)==a['sha256'] and file.stat().st_size==a['bytes']
        out.append({**a,'dated_NTFS_identity':identity(file)})
    return {'module':entry['module'],'source_sha256':entry['sha256'],'actual_command':cmd,'actual_effective_options':options,'actual_raw_guard':g,'artifacts':out}
def qualify_donor(file,sha):
    ap,a=approval(file,sha,'ROOT_APPROVED_COMPATIBLE_FC157_DONOR183_READ_ONLY_QUALIFICATION')
    p=source_runtime_provider_check(a['policy_sha256']);quiet=inactive()
    raw=read_bytes_shared(DONOR_REPORT);assert hashlib.sha256(raw).hexdigest()==a['actual_completed_donor_receipt_sha256']
    r=json.loads(raw);assert r['finished_utc'] and r['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
    assert a['reviewed_donor_runner_sha256']=='a2e5931c838e8b348de9fae4945b9f16ceb0883eaed51ca55f93e797deaa9e6d'
    assert digest(BASE/'run_original_e65_tactic_aware_source_plan.py')==a['reviewed_donor_runner_sha256']
    assert r['resource_settings']['runner_source_sha256']==a['reviewed_donor_runner_sha256']
    assert r['source_plan_sha256']==p['donor_plan_sha256'] and not r.get('current_module') and not r.get('waiting_for_module')
    assert '819816b' in r['compiler_version'] and r['version']=='4.33.1'
    rows=[x for x in r['builds'] if not x['is_endpoint_audit']]
    assert len(rows)==len({x['module'] for x in rows})==183 and not any(x['is_endpoint_audit'] for x in r['builds'])
    by={x['module']:x for x in rows};assert set(by)==set(p['all183_donor_safe_names'])
    plan=load(DONOR/'build-plan.json');entries={x['module']:x for x in plan['modules']}
    actual=[exact_row(by[n],entries[n],DONOR,p['donor_explicit_options']) for n in p['all183_donor_safe_names']]
    for x in p['all233_target_source_identities']:
        f=Path(x['file']);assert not any(f.with_suffix(s).exists() for s in FORBIDDEN_OUTPUT_SUFFIXES),'Target is not cold'
    assert inactive()['donor_and_other_target_dispatchers_quiescent'] and read_bytes_shared(DONOR_REPORT)==raw
    snapshot=BASE/('original-E65-noTactic183-immutable-donor-receipt.'+hashlib.sha256(raw).hexdigest()+'.json')
    if snapshot.exists():assert snapshot.read_bytes()==raw
    else:snapshot.write_bytes(raw)
    result={'status':'QUALIFIED_EXACT183_PREVIOUS_OWN_COLD_SOURCE_OUTPUTS_FOR_REVIEWED157_FUTURE_SEED_ONLY',
      'checked_utc':now(),'helper_sha256':digest(__file__),'policy_sha256':digest(POLICY),'root_approval':str(ap),'root_approval_sha256':sha,
      'actual_donor_receipt_sha256':hashlib.sha256(raw).hexdigest(),'immutable_donor_receipt':str(snapshot),
      'actual_own_source_invocations':183,'selected_endpoint_audits':0,'no_full_Erdos3_or_container_or_novelty_claim':True,
      'all183_actual_source_guards_commands_logs_artifacts':actual,'donor_driver_quiescence':quiet,
      'provider_manifest_sha256':digest(PROVIDERS),'root_pp_option_review_sha256':ROOT_PP_SHA,
      'new_target_compiler_rows':0,'aliases_created':0,'printing_difference_disclosed':True}
    print(json.dumps({'qualification_sha256':save_new(DONOR_QUAL,result),'actual_source_invocations':183,'target_invocations':0}))
def donor_qualification(file,sha,policy_sha):
    f=Path(file).resolve();assert f==DONOR_QUAL.resolve() and digest(f)==sha
    q=load(f);assert q['status']=='QUALIFIED_EXACT183_PREVIOUS_OWN_COLD_SOURCE_OUTPUTS_FOR_REVIEWED157_FUTURE_SEED_ONLY'
    assert q['helper_sha256']==digest(__file__) and q['policy_sha256']==policy_sha and q['actual_own_source_invocations']==183
    assert digest(q['immutable_donor_receipt'])==q['actual_donor_receipt_sha256']==digest(DONOR_REPORT)
    return q
def seed(file,sha):
    ap,a=approval(file,sha,'ROOT_APPROVED_COMPATIBLE_FC_EXACT157_PREVIOUS_OWN_OUTPUT_HARDLINK_SEED_ONLY')
    p=source_runtime_provider_check(a['policy_sha256']);q=donor_qualification(a['donor_qualification_file'],a['donor_qualification_sha256'],a['policy_sha256'])
    quiet=inactive();assert a['donor_finished_and_driver_quiescent_confirmed'] is True
    assert not SEED.exists() and not TARGET_REPORT.exists()
    identity,inode,volume=ntfs_helpers();assert volume(DONOR)==volume(TARGET)
    by={r['module']:r for r in q['all183_actual_source_guards_commands_logs_artifacts']}
    for r in p['all233_target_source_identities']:
        f=Path(r['file']);assert not any(f.with_suffix(s).exists() for s in FORBIDDEN_OUTPUT_SUFFIXES),'Existing target output forbids seed'
    pending=[]
    for n in p['eligible157_module_names']:
        for original in by[n]['artifacts']:
            src=Path(original['file']).resolve();target=TARGET/src.relative_to(DONOR)
            assert digest(src)==original['sha256'] and identity(src)==original['dated_NTFS_identity']
            assert src.is_relative_to(DONOR.resolve()) and target.resolve().is_relative_to(TARGET.resolve()) and not target.exists()
            pending.append({'module':n,'donor':str(src),'target':str(target),'sha256':original['sha256'],'bytes':original['bytes'],'donor_before_NTFS':identity(src)})
    links=[]
    try:
        for row in pending:
            src=Path(row['donor']);target=Path(row['target']);assert not target.exists()
            os.link(src,target)
            before=row['donor_before_NTFS'];si=identity(src);ti=identity(target)
            assert inode(si)==inode(ti)==inode(before) and si['link_count']==ti['link_count']==before['link_count']+1
            assert digest(src)==digest(target)==row['sha256']
            links.append({**row,'donor_after_NTFS':si,'target_after_NTFS':ti})
    except BaseException as e:
        failure=BASE/('compatible-FC-exact157-partial-seed-preserved-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'.json')
        save_new(failure,{'status':'PARTIAL_OPERATIONAL_SEED_PRESERVED_NO_ROLLBACK_OR_PASS','error':repr(e),'completed_links':links,
          'all_planned_links_with_actual_target_existence':[dict(r,target_exists_after_failure=Path(r['target']).exists()) for r in pending],
          'policy_sha256':digest(POLICY)})
        raise
    result={'status':'EXACT157_PREVIOUS_OWN_HARDLINK_SEED_WITH_REVIEWED_PP_DIFFERENCE_COMPLETED',
      'seeded_utc':now(),'helper_sha256':digest(__file__),'policy_sha256':digest(POLICY),'root_approval':str(ap),'root_approval_sha256':sha,
      'donor_qualification_file':str(DONOR_QUAL),'donor_qualification_sha256':digest(DONOR_QUAL),
      'donor_actual183_receipt_sha256':q['actual_donor_receipt_sha256'],'root_pp_option_review_sha256':ROOT_PP_SHA,
      'previous_own_source_output_modules':157,'new_target_cold_source_invocations':0,'selected_target_audits':0,
      'reuse_record_label':'PRIOR_OWN_OUTPUT_REUSED_WITH_REVIEWED_PP_UNICODE_FUN_DIFFERENCE',
      'donor_explicit_options':p['donor_explicit_options'],'target_explicit_options':p['target_explicit_options'],
      'identical_CLI_options_claimed':False,'cold_target_binary_identity_claimed':False,
      'donor_driver_quiescence':quiet,'links':links,'required66_new_cold_module_names':p['required66_new_cold_module_names'],
      'printing_exception_ancestry_by_target_source':p['printing_exception_ancestry_by_target_source']}
    print(json.dumps({'seed_receipt_sha256':save_new(SEED,result),'previous_own_source_outputs':157,'target_invocations':0}))
def verify_seed(policy_sha,seed_sha,allow_own_target_runner=False):
    p=source_runtime_provider_check(policy_sha);assert digest(SEED)==seed_sha
    s=load(SEED);assert s['helper_sha256']==digest(__file__) and s['policy_sha256']==policy_sha
    assert s['status']=='EXACT157_PREVIOUS_OWN_HARDLINK_SEED_WITH_REVIEWED_PP_DIFFERENCE_COMPLETED'
    sap=Path(s['root_approval']);assert digest(sap)==s['root_approval_sha256']
    sa=load(sap);assert sa['status']=='ROOT_APPROVED_COMPATIBLE_FC_EXACT157_PREVIOUS_OWN_OUTPUT_HARDLINK_SEED_ONLY'
    assert sa['policy_sha256']==policy_sha and sa['seed_and_qualification_helper_sha256']==digest(__file__)
    assert s['previous_own_source_output_modules']==157 and s['new_target_cold_source_invocations']==0
    q=donor_qualification(s['donor_qualification_file'],s['donor_qualification_sha256'],policy_sha)
    identity,inode,_=ntfs_helpers();names=set()
    for r in s['links']:
        names.add(r['module']);src=Path(r['donor']);target=Path(r['target'])
        assert digest(src)==digest(target)==r['sha256'] and src.stat().st_size==target.stat().st_size==r['bytes']
        si=identity(src);ti=identity(target);assert si==r['donor_after_NTFS'] and ti==r['target_after_NTFS'] and inode(si)==inode(ti)
    assert names==set(p['eligible157_module_names'])
    inactive(allow_own_target_runner)
    return {'status':'VERIFIED_EXACT157_PRIOR_OWN_OUTPUT_SEED_WITH_PP_DIFFERENCE_ANCESTRY',
      'seed_receipt_sha256':seed_sha,'donor_qualification_sha256':digest(DONOR_QUAL),'eligible157_module_names':sorted(names),
      'printing_difference_ancestry_preserved':True,'new_source_invocations_counted':0}
def qualify_target(file,sha):
    ap,a=approval(file,sha,'ROOT_APPROVED_COMPATIBLE_FC157_PLUS66_GRANULAR_READ_ONLY_FINAL_QUALIFICATION')
    p=source_runtime_provider_check(a['policy_sha256']);seedcheck=verify_seed(a['policy_sha256'],a['seed_receipt_sha256'])
    raw=read_bytes_shared(TARGET_REPORT);assert hashlib.sha256(raw).hexdigest()==a['actual_target_receipt_sha256']
    r=json.loads(raw);assert r['finished_utc'] and not r.get('current_module') and not r.get('waiting_for_module')
    assert digest(BASE/'run_compatible_fc157_linked_granular_plan.py')==a['reviewed_target_runner_sha256']
    assert r['resource_settings']['runner_source_sha256']==a['reviewed_target_runner_sha256']
    assert r['source_plan_sha256']==p['target_plan_sha256'] and r['status']=='SCHEDULED_RESOURCE_CHECKPOINT'
    rows=[x for x in r['builds'] if not x['is_endpoint_audit']];assert len(rows)==len({x['module'] for x in rows})==66
    assert not any(x['is_endpoint_audit'] for x in r['builds']) and not set(x['module'] for x in rows)&set(p['eligible157_module_names'])
    by={x['module']:x for x in rows};assert set(by)==set(p['required66_new_cold_module_names'])
    plan=load(TARGET/'build-plan.json');entries={x['module']:x for x in plan['modules']}
    actual=[exact_row(by[n],entries[n],TARGET,p['target_explicit_options']) for n in p['required66_new_cold_module_names']]
    assert r['previous_own_output_reuse_policy_sha256']==digest(POLICY) and r['previous_own_output_seed_receipt_sha256']==a['seed_receipt_sha256']
    assert read_bytes_shared(TARGET_REPORT)==raw
    result={'status':'QUALIFIED_COMPATIBLE_FC223_GRANULAR_SCOPE_157_PRIOR_OWN_WITH_REVIEWED_PP_DIFFERENCE_PLUS66_ACTUAL_NEW_ZERO_AUDITS',
      'checked_utc':now(),'helper_sha256':digest(__file__),'policy_sha256':digest(POLICY),'root_approval':str(ap),'root_approval_sha256':sha,
      'actual_target_receipt_sha256':hashlib.sha256(raw).hexdigest(),'previous_own_output_seed_qualification':seedcheck,
      'previous_own_source_outputs_with_printing_difference':157,'actual_new_target_cold_source_invocations':66,
      'granular_source_scope_total':223,'selected_endpoint_audits':0,'withheld_whole_resource_modules':10,
      'actual66_source_command_guard_raw_artifact_records':actual,'root_pp_option_review_sha256':ROOT_PP_SHA,
      'donor_explicit_options':p['donor_explicit_options'],'target_explicit_options':p['target_explicit_options'],
      'printing_exception_ancestry_by_target_source':p['printing_exception_ancestry_by_target_source'],
      'full_project_PASS_or_selected_theorem_or_novelty_claim':False,'ancestry_must_survive_any_later_Sakana217_composition':True}
    print(json.dumps({'qualification_sha256':save_new(TARGET_QUAL,result),'scope':223,'previous':157,'actual_new':66,'audits':0}))
if __name__=='__main__':
    assert len(sys.argv)==4,'Prepared only; exact future mode approval_file approval_sha required'
    mode={'--qualify-donor-root-approved':qualify_donor,'--seed-root-approved':seed,'--qualify-target-root-approved':qualify_target}
    assert sys.argv[1] in mode;mode[sys.argv[1]](sys.argv[2],sys.argv[3])
