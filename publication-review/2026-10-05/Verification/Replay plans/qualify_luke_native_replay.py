"""Independently qualify complete source and raw endpoint-output coverage."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os
from receipt_io import read_bytes_shared
from audit_axioms import parse
BASE=Path(__file__).resolve().parent
source=BASE/'luke-k4-ramsey-current-native-fresh-build.json'
schema=json.loads((BASE/'luke_native_qualified_replay_plan.json').read_text(encoding='utf8'))
frozen=json.loads((BASE/'builds/luke-k4-ramsey-current-direct/build-plan.json').read_text(encoding='utf8'))
raw=read_bytes_shared(source) if source.exists() else b'{}'
d=json.loads(raw.decode('utf8'))
checks={}
checks['completed_status']=d.get('status')=='PASS_WITH_NATIVE_EVALUATION' and bool(d.get('finished_utc'))
checks['exact_identity']=all(d.get(k)==schema[k] for k in ['id','commit','version','mathlib_pin'])
expected_sources={m['module']:m['sha256'] for m in frozen['modules']}
actual_sources={m['module']:m['sha256'] for m in d.get('modules',[])}
checks['exact_51_source_plan']=len(expected_sources)==51 and actual_sources==expected_sources
checks['all_51_frozen_source_bytes_unchanged']=all(
    Path(m['file']).exists() and hashlib.sha256(Path(m['file']).read_bytes()).hexdigest()==m['sha256']
    and (not m.get('frozen_source') or (Path(m['frozen_source']).exists() and hashlib.sha256(Path(m['frozen_source']).read_bytes()).hexdigest()==m['sha256']))
    for m in frozen['modules'])
passed={r['module']:r for r in d.get('builds',[]) if r.get('exit')==0 and r.get('module') in expected_sources}
checks['all_51_source_outputs_PASS']=len(passed)==51 and all(r.get('source_sha256')==expected_sources[n] for n,r in passed.items())
checks['all_51_module_states_PASS']=set(d.get('module_states',{}))==set(expected_sources) and all(v=='PASS' for v in d.get('module_states',{}).values())
outputs=[o for b in d.get('builds',[]) if b.get('exit')==0 and b.get('is_endpoint_audit') for o in parse(b.get('stdout',''))]
observed={o['endpoint']:o for o in outputs}
expected=set(schema['selected_endpoint_audit_field']['expected'])
general=set(schema['selected_endpoint_audit_field']['ordinary_general_endpoints'])
missing=sorted(expected-set(observed))
checks['all_35_selected_outputs_present']=len(expected)==35 and not missing
bad=[o for o in outputs if o['endpoint'] in expected and o['classification'] in {'SORRY_ADMISSION','UNRECOGNIZED_AXIOMS'}]
checks['selected_trust_boundary']=not bad and not d.get('selected_endpoint_uses_sorry') and not d.get('selected_unrecognized_axioms')
checks['all_11_general_endpoints_standard_only']=len(general)==11 and all(n in observed and not observed[n]['native_axioms'] and observed[n]['classification'] in {'STANDARD_KERNEL_AXIOMS','AXIOM_FREE'} for n in general)
count='K4Ramsey.Constructions.Final3840.Certificate'
checks['unchanged_Count_certificate_PASS']=count in passed and passed[count].get('source_sha256')==expected_sources[count]
checks['exact_count_raw_axiom_output']='K4Ramsey.Final3840.exact_count' in observed
links_path=BASE/'luke-native-isolated-links.json'
links_raw=read_bytes_shared(links_path) if links_path.exists() else b'{}'
links=json.loads(links_raw.decode('utf8'))
checks['native_adapter_actual_PE_receipt_bound']=(
    links.get('status')=='ACTUAL_LINKS_AND_PE_PASS_INITIALIZATION_UNTESTED'
    and d.get('native_link_receipt_sha256')==hashlib.sha256(links_raw).hexdigest()
    and len(links.get('dlls',[]))==2
    and all(links.get('two_DLL_DAG_import_checks',{}).values())
    and links.get('actual_Count_initializer_is_exported_executable') is True
    and len(links.get('actual_Count_closed_cache_PE_data_slots',[]))==3
    and all(r['actual_data_slot_is_nonexecuting_writable'] for r in links.get('actual_Count_closed_cache_PE_data_slots',[])))
checks['actual_native_DLL_bytes_unchanged']=len(links.get('dlls',[]))==2 and all(
    Path(r['file']).exists() and hashlib.sha256(Path(r['file']).read_bytes()).hexdigest()==r['sha256']
    for r in links.get('dlls',[]))
count_row=passed.get(count,{})
expected_images={r['sha256'] for r in links.get('dlls',[])}
checks['loaded_Count_native_image_identity_observed']=(
    count_row.get('all_expected_native_images_observed') is True
    and len(expected_images)==2
    and {r['sha256'] for r in count_row.get('loaded_native_images',[])}==expected_images)
identity_review=d.get('native_identity_review_with_observer_limitation',{})
limited_identity_qualified=False
if identity_review:
    try:
        decision_raw=read_bytes_shared(Path(identity_review['accepted_receipt_file']))
        evidence_raw=read_bytes_shared(Path(identity_review['evidence_receipt_file']))
        decision=json.loads(decision_raw);evidence=json.loads(evidence_raw)
        row_sha=hashlib.sha256(json.dumps(count_row,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8')).hexdigest()
        original_pilots=[r for r in d.get('raw_count_retry_attempts',[])
            if r.get('prior_pilot_receipt_sha256')==decision.get('pilot_receipt_sha256')]
        limited_identity_qualified=(
            hashlib.sha256(decision_raw).hexdigest()==identity_review['accepted_receipt_sha256']
            and hashlib.sha256(evidence_raw).hexdigest()==identity_review['evidence_receipt_sha256']==decision['evidence_receipt_sha256']
            and decision['status']=='ROOT_NATIVE_IDENTITY_REVIEW_ACCEPTED_WITH_OBSERVER_LIMITATION'
            and decision['accepted_by']=='/root' and bool(decision['accepted_utc'])
            and decision['count_row_canonical_sha256']==row_sha==evidence['count_row_canonical_sha256']
            and decision['native_link_receipt_sha256']==hashlib.sha256(links_raw).hexdigest()
            and decision['native_dispatch_observations_clean'] is False
            and decision['continuous_observer_completeness'] is False
            and decision['unknown_error_timing_remains_unresolved'] is True
            and decision['limited_scope_acknowledged'] is True
            and d.get('native_dispatch_observations_clean') is False
            and evidence['image_observation_errors_preserved']==count_row['image_observation_errors']
            and evidence['loaded_native_images']==count_row['loaded_native_images']
            and evidence['initialization_complete_cache_slot_observation'] in count_row['cache_pointer_observations']
            and bool(original_pilots)
            and all(hashlib.sha256(read_bytes_shared(Path(r['prior_pilot_snapshot']))).hexdigest()==decision['pilot_receipt_sha256'] for r in original_pilots))
    except (KeyError,OSError,ValueError):
        limited_identity_qualified=False
checks['native_identity_observer_policy_qualified']=(
    not count_row.get('image_observation_errors') or limited_identity_qualified)
checks['Count_and_raw_audit_pilot_completed']=d.get('actual_native_Count_certificate_and_raw_axiom_audit_PASS') is True
result={'generated_utc':datetime.now(timezone.utc).isoformat(),
        'status':'PASS_COMPLETE_EXACT_SCOPE' if all(checks.values()) else 'INCOMPLETE_OR_UNQUALIFIED',
        'replay_receipt':source.name,'replay_receipt_sha256':hashlib.sha256(raw).hexdigest(),
        'checks':checks,'missing_selected_outputs':missing,'unaccepted_selected_axioms':bad,
        'selected_output_count_unique':len(expected&set(observed)),
        'native_observer_limitation':{'observer_errors':count_row.get('image_observation_errors',[]),
            'continuous_observer_completeness':not bool(count_row.get('image_observation_errors')),
            'root_limited_identity_review_qualified':limited_identity_qualified,
            'error_timing':'Unknown; no exit-race or complete-observer claim is made.' if count_row.get('image_observation_errors') else 'No observer error recorded',
            'root_review':identity_review},
        'scope':'Independent source-identity and actual raw-output qualification. Native adapter provenance, originality, general statement fidelity and publication approval remain separately documented.'}
target=BASE/'luke-native-publication-qualification.json';tmp=target.with_suffix('.json.tmp')
tmp.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8');os.replace(tmp,target)
print(json.dumps({'status':result['status'],'checks':checks},indent=2))
