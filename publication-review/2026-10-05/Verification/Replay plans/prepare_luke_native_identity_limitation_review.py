"""Additive, read-only evidence review for the completed Count source invocation.

This script does not approve its own evidence, modify the attempted receipt,
invoke Lean, load a DLL, or infer the time of an un-timestamped observer error.
Root must issue a separate SHA-bound acceptance after independent review.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time
from receipt_io import read_bytes_shared

BASE=Path(__file__).resolve().parent
PILOT=BASE/'luke-k4-ramsey-current-native-fresh-build.json'
EXPECTED_PILOT='f96afa977949375778b0666754a20238403718d93919f08508ed9d3f4370229d'
OUT=BASE/'luke-native-identity-observer-limitation-review.json'
COUNT='K4Ramsey.Constructions.Final3840.Certificate'

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        while b:=f.read(1024*1024): h.update(b)
    return h.hexdigest()

def digest(value):
    return hashlib.sha256(json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8')).hexdigest()

def immutable_json(path,value):
    assert not path.exists(), 'Preserve every additive evidence version'
    tmp=path.with_suffix(path.suffix+'.tmp')
    with tmp.open('wb') as f:
        f.write(json.dumps(value,ensure_ascii=False,indent=2).encode('utf8'));f.flush();os.fsync(f.fileno())
    for attempt in range(60):
        try: os.replace(tmp,path);return
        except PermissionError:
            if attempt==59:raise
            time.sleep(.1)

def read_bound(path,wanted=None):
    raw=read_bytes_shared(path);actual=hashlib.sha256(raw).hexdigest()
    if wanted is not None:assert actual==wanted
    return json.loads(raw),actual

def verify_file(path,wanted,bytes_=None):
    p=Path(path)
    assert p.is_file()
    if bytes_ is not None:assert p.stat().st_size==bytes_
    assert sha(p)==wanted, str(p)
    return {'file':str(p),'bytes':p.stat().st_size,'sha256':wanted,'matches':True}

def main():
    pilot,pilot_sha=read_bound(PILOT,EXPECTED_PILOT)
    assert pilot['status']=='COUNT_SOURCE_PASS_RAW_OR_NATIVE_EVIDENCE_UNQUALIFIED'
    assert pilot.get('pilot_finished_utc') and not pilot.get('current_module')
    assert pilot.get('native_dispatch_observations_clean') is False
    assert pilot.get('actual_native_Count_certificate_and_raw_axiom_audit_PASS') is False
    count_rows=[r for r in pilot['builds'] if r.get('module')==COUNT]
    assert len(count_rows)==1
    count=count_rows[0]
    assert count['attempted'] and count['exit']==0 and count['state']=='PASS'
    assert count['all_expected_native_images_observed'] is True
    errors=count['image_observation_errors']
    assert errors==['[WinError 299] Solo se completó una parte de una solicitud ReadProcessMemory o WriteProcessMemory.']
    assert 'image_observation_error_events' not in count
    assert len([v for v in pilot['module_states'].values() if v=='PASS'])==34
    frozen,frozen_sha=read_bound(Path(pilot['source_dir'])/'build-plan.json',pilot['source_stage_build_plan_sha256'])
    assert len(frozen['modules'])==51
    sources=[]
    for module in frozen['modules']:
        for key in ['file','frozen_source']:verify_file(module[key],module['sha256'])
        sources.append({'module':module['module'],'sha256':module['sha256'],'staged_and_frozen_match':True})
    expected_count=next(m for m in frozen['modules'] if m['module']==COUNT)
    assert count['source_sha256']==expected_count['sha256']
    output=Path(pilot['source_dir'])/'.lake/build/lib/lean'
    actual_inventory={str(p.relative_to(output)):{'bytes':p.stat().st_size,'sha256':sha(p)}
                      for p in output.rglob('*') if p.is_file()}
    assert actual_inventory==pilot['fresh_custom_artifact_inventory']
    assert any(p.endswith('Final3840\\Certificate.olean') or p.endswith('Final3840/Certificate.olean') for p in actual_inventory)
    prior_artifacts=[verify_file(a['prior_file'],a['sha256'],a['bytes']) for a in pilot['reused_own_direct_artifact_inventory']]
    links,links_sha=read_bound(BASE/'luke-native-isolated-links.json',pilot['native_link_receipt_sha256'])
    preparation,preparation_sha=read_bound(BASE/'luke-native-isolated-preparation.json',links['preparation_receipt_sha256'])
    abi,abi_sha=read_bound(BASE/'luke-native-isolated-object-ABI-audit.json',links['object_ABI_audit_sha256'])
    dll_files=[]
    for row in links['dlls']:
        dll_files.append(verify_file(row['file'],row['sha256'],row['bytes']))
        lib=row['import_library'];dll_files.append(verify_file(lib['file'],lib['sha256'],lib['bytes']))
    tools=[verify_file(p,s) for p,s in pilot['pinned_tool_binary_hashes'].items()]
    libs=[verify_file(r['file'],r['sha256'],r['bytes']) for r in abi['pinned_linker_libraries']]
    native_objects=[r for r in preparation['objects'] if r['state']=='PASS']
    assert len(native_objects)==951 and len({r['module'] for r in native_objects})==951
    for row in native_objects:
        verify_file(row['source_c_file'],row['source_c_sha256'])
        verify_file(row['object_file'],row['object_sha256'])
        verify_file(row['actual_COFF_exports_file'],row['actual_COFF_exports_sha256'])
    for entry in preparation['source_and_input_olean_inventory_before'].values():
        verify_file(entry['file'],entry['source_sha256']);verify_file(entry['frozen_source'],entry['source_sha256'])
        for kind in ['.olean','.ilean']:
            a=entry[kind];verify_file(a['file'],a['sha256'],a['bytes'])
    dependency_snapshot,dependency_snapshot_sha=read_bound(BASE/'luke_native_dependency_artifact_snapshot.json',preparation['official_dependency_artifact_snapshot_sha256'])
    for p,entry in dependency_snapshot['records'].items():verify_file(p,entry['sha256'],entry['bytes'])
    dependencies=[]
    for expected in pilot['dependency_preflight']:
        p=Path(frozen['dependency_identity_root'])/'.lake/packages'/expected['name']
        observed={}
        for label,cmd,wanted in [('head',['git','-C',str(p),'rev-parse','HEAD'],expected['expected_head']),
                                 ('origin',['git','-C',str(p),'remote','get-url','origin'],expected['expected_origin'])]:
            result=subprocess.run(cmd,capture_output=True,text=True,encoding='utf8')
            assert result.returncode==0 and result.stdout.strip()==wanted
            observed[label]=result.stdout.strip()
        dependencies.append({'name':expected['name'],**observed,'matches':True})
    images=count['loaded_native_images'];assert len(images)==2
    for image in images:
        row=next(r for r in links['dlls'] if Path(r['file']).name.lower()==image['module'].lower())
        assert Path(image['path']).resolve()==Path(row['file']).resolve()
        assert image['sha256']==row['sha256'] and image['observed_utc']
        assert count['started_utc']<image['observed_utc']<count['finished_utc']
    count_image=next(i for i in images if i['module']=='luke_mathlib_count_native.dll')
    observations=count['cache_pointer_observations']
    complete=next(o for o in observations if o['all_three_slots_non_null'])
    assert complete['observed_utc']<count['finished_utc']
    assert len(complete['slots'])==3
    for slot in complete['slots']:
        row=next(r for r in links['actual_Count_closed_cache_PE_data_slots'] if r['cache']==slot['cache'])
        assert slot['symbol']==row['symbol'] and slot['read_bytes']==8
        assert slot['pointer_value']>0 and slot['is_null'] is False
        assert slot['slot_address']==count_image['base_address']+row['rva']
        assert row['actual_data_slot_is_nonexecuting_writable']
    assert count['initialization_completion_evidence']=='ALL_THREE_EXACT_DATA_SLOTS_OBSERVED_NON_NULL'
    logs=[verify_file(count[k+'_file'],count[k+'_sha256']) for k in ['stdout','stderr']]
    assert all(Path(x['file']).stat().st_size==0 for x in logs)
    assert count['created_suspended'] and count['assigned_to_own_job_before_resume'] and count['NtResumeProcess_status']==0
    result={'status':'PENDING_ROOT_NATIVE_IDENTITY_REVIEW_WITH_OBSERVER_LIMITATION',
        'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'family_id':pilot['id'],'source_commit':pilot['commit'],'lean_version':pilot['version'],'mathlib_pin':pilot['mathlib_pin'],
        'review_preparer_sha256':sha(__file__),'pilot_receipt_file':str(PILOT),'pilot_receipt_sha256':pilot_sha,
        'count_row_canonical_sha256':digest(count),'source_stage_build_plan_sha256':frozen_sha,
        'native_link_receipt_sha256':links_sha,'preparation_receipt_sha256':preparation_sha,'object_ABI_audit_sha256':abi_sha,
        'count_execution':{k:count[k] for k in ['module','source_sha256','command','started_utc','finished_utc','seconds','state','exit','stdout_sha256','stderr_sha256','job_peak_process_private_bytes']},
        'loaded_native_images':images,'initialization_complete_cache_slot_observation':complete,
        'all_native_images_correctly_observed':True,'all_three_exact_exported_cache_slots_observed_non_null':True,
        'native_dispatch_observations_clean':False,'continuous_observer_completeness':False,
        'image_observation_errors_preserved':errors,'observer_error_timing':'UNKNOWN; original guard did not record a timestamp or at-exit association.',
        'unknown_error_timing_remains_unresolved':True,
        'limited_conclusion':'Native identity and initialization are sufficiently observed by the successful time-stamped image/hash and exact non-null exported cache-slot observations, with unchanged inputs and actual Count source exit 0. Continuous observer completeness is false; unknown timing of WinError 299 remains unresolved. Root acceptance is required and is not supplied by this preparer.',
        'native_selection_evidence_notice':count['native_selection_evidence_notice'],
        'frozen_source_identity_count':len(sources),'frozen_source_identity_inventory':sources,
        'fresh_artifact_count':len(actual_inventory),'fresh_artifact_inventory_canonical_sha256':digest(actual_inventory),
        'prior_own_direct_artifact_count':len(prior_artifacts),'native_object_identity_count':len(native_objects),
        'source_and_input_olean_identity_module_count':len(preparation['source_and_input_olean_inventory_before']),
        'official_dependency_artifact_count':len(dependency_snapshot['records']),
        'official_dependency_artifact_snapshot_sha256':dependency_snapshot_sha,
        'dependencies':dependencies,'unchanged_native_DLL_and_import_libraries':dll_files,
        'unchanged_pinned_tools':tools,'unchanged_pinned_linker_libraries':libs,'count_stdout_stderr_identity':logs,
        'all_checked_source_object_artifact_and_dependency_identities_unchanged':True,
        'raw_count_audit_executed':False,'complete_project_scope_verified':False,
        'acceptance_requirements':{'separate_status':'ROOT_NATIVE_IDENTITY_REVIEW_ACCEPTED_WITH_OBSERVER_LIMITATION',
            'evidence_receipt_file':str(OUT),'evidence_receipt_sha256':'Root must fill the actual completed evidence SHA.',
            'pilot_receipt_sha256':pilot_sha,'count_row_canonical_sha256':digest(count),
            'native_dispatch_observations_clean':False,'continuous_observer_completeness':False,
            'unknown_error_timing_remains_unresolved':True,'qualification_scope':'Native identity/initialization only; no raw axiom or complete 51-source/35-endpoint qualification.'}}
    assert sha(PILOT)==pilot_sha,'Original attempted pilot must remain unchanged'
    immutable_json(OUT,result)
    print(json.dumps({'review':str(OUT),'sha256':sha(OUT),'status':result['status'],'checked_sources':len(sources),
        'checked_native_objects':len(native_objects),'checked_official_dependency_artifacts':len(dependency_snapshot['records']),
        'observer_error_timing':result['observer_error_timing'],'no_Lean_or_DLL_invocation':True},indent=2),flush=True)

if __name__=='__main__':main()
