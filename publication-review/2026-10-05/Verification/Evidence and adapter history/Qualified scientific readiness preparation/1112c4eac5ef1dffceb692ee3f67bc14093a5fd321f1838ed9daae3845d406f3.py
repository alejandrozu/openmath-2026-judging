"""Read-only interpretation of fresh execution receipts for publication drafts.

Never changes the agents' plans or reports; an absent receipt is not a pass.
"""
from pathlib import Path
import json
from verification.receipt_io import read_json_shared, read_bytes_shared
import hashlib
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'verification'))
from execution_receipt_selection import receipt_path

HERE=Path(__file__).resolve().parent
BASE=HERE/'verification'
FAMILY_PROJECTS={
 'a060957':['sakana-a060957'], 'a100475':['sakana-a100475'],
 'a000224':['sakana-a000224'], 'ferrers-hierarchy':['sakana-ferrers'],
 'erdos21-sharp-residual':['sakana-erdos21-sharp-residual'],
 'erdos169-fourap':['sakana-erdos169-fourap'], 'opdp13-quartic':['sakana-opdp13'],
 'opdp43-halfturn':['sakana-opdp43'],
 'erdos1060-uniform-partial':['sakana-erdos1060-uniform-partial'],
 'erdos829-log-five-thirds':['sakana-erdos829-log-five-thirds'],
 'erdos944-order-bound':['sakana-erdos944-order-bound'],
 'opdp89-parity-local-maxima':['sakana-opdp89-parity-sharp'],
 'FOCUS-E3':['sakana-FOCUS-E3','sakana-FOCUS-E3-pullback'],
 'FOCUS-MATRIX':['sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2'],
 'DMS':['htpeo-dms-current','htpeo-dms-core'],
 'KOBON39':['htpeo-kobon471'], 'SUPPORT138':['chandragupt'],
 'FOCUS-RAMSEY':['sakana-FOCUS-RAMSEY'], 'RAMSEY':['htpeo-ramsey-current'],
 'FOCUS-GROTH':['sakana-FOCUS-GROTH'],
 'LUKEMADHAN-RAMSEY':['luke-k4-ramsey-current'],
 'E03-PIVOT-GENERIC':['matt-unitary-current'], 'K61':[]
}

def resource_checkpoint(row):
    guard=row.get('own_job_resource_receipt') or {}
    labels=[str(row.get(k,'')) for k in ['state','stop_reason','owned_process_stop_output']]
    labels.append(str(guard.get('state','')))
    resource_stops={'COMMIT_RESERVE','PHYSICAL_RESERVE','PHYSICAL_MEMORY_RESERVE',
                    'DISK_RESERVE','OWN_PRIVATE_LIMIT','PRIVATE_MEMORY_CEILING',
                    'OWN_ALLOCATION_FAILURE','OPERATIONAL_GUARD_ERROR'}
    return any(s.startswith(('ENVIRONMENT_BLOCKED','RESOURCE_','SCHEDULED_','SUPERSEDED_','NOT_INVOKED_')) or s in resource_stops for s in labels)

def state(project):
    path=receipt_path(project)
    if path.exists():
        d=read_json_shared(path)
        status=d.get('status')
        original_status=status
        boundary_hold=None
        if project=='htpeo-dms-current':
            # A held dispatcher retains its original receipt until its pending
            # successful row can be finalized. Report the SHA-bound hold as
            # scheduling state without changing or counting that original row.
            current_sha=hashlib.sha256(read_bytes_shared(path)).hexdigest()
            for hold_path in sorted(BASE.glob('dms-dispatcher-hold-*.json'), reverse=True):
                hold=read_json_shared(hold_path)
                if (hold.get('status')=='DISPATCHER_HELD_NO_ACTIVE_DMS_SOURCE_CHILD'
                    and hold.get('source_receipt_before_hold_sha256')==current_sha):
                    status='SOURCE_BOUNDARY_DISPATCHER_HELD'
                    boundary_hold={'receipt':hold_path.name,
                                   'module':hold.get('source',{}).get('module'),
                                   'actual_child_exit':hold.get('actual_child_exit'),
                                   'pending_original_row_finalization':True}
                    break
        # Chandragupt's dedicated complete receipt uses builds plus audit_results.
        if project=='chandragupt' and status is None:
            status=d.get('overall_status','UNCLASSIFIED_RECEIPT')
        builds=d.get('builds',[])
        source_names={m['module'] for m in d.get('modules',[])} or set(d.get('source_sha256',{}))
        successful=len({x.get('module') for x in builds if x.get('exit')==0 and x.get('module') in source_names})
        failed=sum(x.get('exit') is not None and x.get('exit')!=0 and not resource_checkpoint(x) for x in builds)
        checkpoint_modules={x.get('module') for x in builds
                            if x.get('exit') is not None and x.get('exit')!=0 and resource_checkpoint(x)}
        # An independent-DAG continuation preserves the original invocation
        # in a separate root record while deferring its descendants. Keep that
        # real allocation failure visible, without counting it as a proof failure.
        deferred_roots=d.get('resource_deferred_roots',{})
        checkpoint_modules.update(n for n,meta in deferred_roots.items()
            if resource_checkpoint(meta.get('invocation',{})))
        checkpoints=len(checkpoint_modules)
        supplemental_route=None
        native_path=BASE/'luke-k4-ramsey-current-native-fresh-build.json'
        if project=='luke-k4-ramsey-current' and path!=native_path and native_path.exists():
            native=read_json_shared(native_path)
            native_names={m['module'] for m in native.get('modules',[])}
            supplemental_route={
                'receipt':native_path.name,'status':native.get('status'),
                'successful_compilations':len({r.get('module') for r in native.get('builds',[]) if r.get('exit')==0 and r.get('module') in native_names}),
                'source_module_count':len(native_names),'current_module':native.get('current_module'),
                'complete_publication_qualification':False,
                'observer_limitation_preserved':native.get('native_dispatch_observations_clean') is False}
        result={'project':project,'status':status,'source_module_count':len(source_names),
                'original_receipt_status':original_status,'boundary_hold':boundary_hold,
                'supplemental_route':supplemental_route,
                'successful_compilations':successful,'failed_invocations':failed,'resource_checkpoint_invocations':checkpoints,
                'resource_deferred_roots':sorted(deferred_roots),
                'version':d.get('compiler_version',d.get('version','version in receipt')),
                'receipt':path.name,'failure':d.get('failure',''),
                'current_module':d.get('current_module',''),'execution_route':d.get('route','direct exact-pin source replay'),
                'selected_native_evaluation':bool(d.get('selected_native_evaluation')),
                'unfinished_baseline_axioms':bool(d.get('unfinished_baseline_axioms')),
                'selected_endpoint_uses_sorry':bool(d.get('selected_endpoint_uses_sorry')),
                'selected_unrecognized_axioms':bool(d.get('selected_unrecognized_axioms'))}
        if project=='htpeo-dms-current':
            result['qualified_alternative_route']=qualified_dms_composite_route()
        return result
    plan=BASE/'builds'/project/'build-plan.json'
    d=json.loads(plan.read_text(encoding='utf8')) if plan.exists() else {}
    return {'project':project,'status':'PLANNED_NOT_RUN' if d else 'NO_EXECUTION_RECEIPT',
            'source_module_count':len(d.get('modules',[])),'successful_compilations':0,
            'failed_invocations':0,'version':d.get('version','unrecorded'),'receipt':None,
            'failure':'','current_module':''}

def qualified_dms_composite_route():
    """A separately qualified scientific route; never promotes the original receipt."""
    path=BASE/'dms-v4-vector-composite-supplement-final-qualification-20261005.json'
    if not path.exists():return None
    raw=read_bytes_shared(path)
    assert hashlib.sha256(raw).hexdigest()=='7d401ae5c7003a1520dac33288b2335645bbd095a3327cc8ddefb2d17aa417ab'
    q=json.loads(raw)
    assert q.get('qualified') is True
    assert q['status']=='QUALIFIED_BODY_IDENTICAL_SOURCES_WITH_221_PREVIOUS_OWN_PASSES_AND_FRESH_ORGANIZER_SUPPLEMENT_STANDARD_ENDPOINTS'
    assert q['all228_body_identity_and2735_official_source_artifact_runtime_git_cache_identity']['source_count']==228
    assert (q['prior_own_original_cold_source_outputs_reused_readonly99'],
            q['prior_V3_new_own_cold_source_passes_reused_linked122'],
            q['new_V4_cold_source_passes'])==(99,122,7)
    reviews=q['selected123_actual_axiom_classifications']
    assert len(reviews)==123 and len({r['endpoint'] for r in reviews})==123
    counts={c:sum(r['classification']==c for r in reviews)
            for c in ['STANDARD_KERNEL_AXIOMS','AXIOM_FREE']}
    assert counts=={'STANDARD_KERNEL_AXIOMS':120,'AXIOM_FREE':3}
    assert not q['selected_admitted'] and not q['selected_unknown_axioms'] and not q['selected_native_trust']
    for pkey,hkey in [('final_source_receipt','final_source_receipt_sha256'),
                      ('organizer_supplemental_audit_receipt','organizer_supplemental_audit_receipt_sha256')]:
        assert hashlib.sha256(read_bytes_shared(Path(q[pkey]))).hexdigest()==q[hkey]
    supplement=read_json_shared(Path(q['organizer_supplemental_audit_receipt']))
    assert supplement['status']=='SUPPLEMENTAL_AUDIT123_STANDARD_OR_AXIOM_FREE_PASS'
    assert (supplement['frozen_original_audit_exit'],supplement['frozen_original_print_count'])==(1,120)
    assert q['original120_axiom_classes_and_sets_match_successful_supplement'] is True
    # The qualification covers only the displayed selected endpoint set.
    assert 'MGraph.k4subdiv_star6' not in {r['endpoint'] for r in reviews}
    star=next(r for r in q['all228_body_identity_and2735_official_source_artifact_runtime_git_cache_identity']['body_identity_records']
              if r['module']=='StarCert')
    return {'family':'DMS','status':q['status'],'qualified':True,
            'scientific_body_scope_complete':True,'selected_endpoint_scope_complete':True,
            'covers_entire_family_selected_scientific_scope':True,
            'qualification_record':path.name,'qualification_record_sha256':hashlib.sha256(raw).hexdigest(),
            'scientific_body_count':228,'modified_import_headers':4,
            'previous_original_owned_via_readonly_V1_copies':99,
            'previous_unaffected_V3_owned_cold_passes':122,'new_V4_cold_source_passes':7,
            'selected_endpoint_count':123,'selected_classification_counts':counts,
            'selected_native_evaluation_count':0,'selected_admitted_count':0,'selected_unknown_axiom_count':0,
            'final_source_receipt':Path(q['final_source_receipt']).name,
            'final_source_receipt_sha256':q['final_source_receipt_sha256'],
            'original_organizer_audit_exit':1,'original_organizer_audit_prints':120,
            'original_organizer_audit_requests':123,
            'supplemental_audit_receipt':Path(q['organizer_supplemental_audit_receipt']).name,
            'supplemental_audit_receipt_sha256':q['organizer_supplemental_audit_receipt_sha256'],
            'supplement_change':'Only import Star6Equiv added; all 123 original requests unchanged.',
            'outside_selected_native_finite_certificate':{'declaration':'MGraph.k4subdiv_star6',
                'source_module':'StarCert','source_line':66,'source_sha256':star['source_sha256'],
                'proof_mechanism':'native_decide','selected_endpoint':False},
            'whole_portfolio_standard_only_claim':False,
            'open_mathematical_premises_preserved':['FEEXTD10','FEEXISTD10','POLE','TDTRI','IID'],
            'competition_progress_retained':'0.15',
            'original_receipt_replaced':False,'general_DMS_proved':False}


def family_note(identifier):
    if identifier=='K61':
        return 'No submitted Lean project was located for this packet. The independent exact straight-line geometry recount is an ordinary certificate check, and is not represented as Lean replay. Originality remains separately under review.'
    projects=FAMILY_PROJECTS.get(identifier,[])
    if not projects:
        return 'No fresh execution receipt is mapped to this family. The absence of a receipt must not be presented as a successful replay.'
    parts=[]
    for project in projects:
        r=state(project)
        text=project+': '+str(r['status'])
        if r['receipt']:
            text+='; '+str(r['successful_compilations'])+'/'+str(r['source_module_count'])+' custom modules compiled successfully'
            if r['failed_invocations']:text+='; '+str(r['failed_invocations'])+' failed or timed-out invocations'
            if r['resource_checkpoint_invocations']:text+='; '+str(r['resource_checkpoint_invocations'])+' unfinished invocations stopped at a recorded resource checkpoint'
            if r.get('boundary_hold'):
                h=r['boundary_hold']
                text+='; '+str(h['module'])+' additionally exited '+str(h['actual_child_exit'])+' at the boundary, pending original row finalization; hold receipt Verification/'+h['receipt']
            text+='; receipt Verification/'+r['receipt']
            if 'direct-fresh-build' in r['receipt']:text+='; direct Lean CLI adapter, with the authored Lake native-precompilation policy kept separate'
            if 'native-fresh-build' in r['receipt']:text+='; isolated source-identical native adapter; compiler/native-evaluation trust is explicit; the earlier direct attempt is preserved separately'
            if 'native-fresh-build' in r['receipt']:
                native_record=read_json_shared(BASE/r['receipt'])
                if native_record.get('native_dispatch_observations_clean') is False:
                    text+='; positive native identity/initialization evidence has a separate root review, with one WinError299 retained, unknown error timing and incomplete continuous memory observation'
            if r.get('supplemental_route'):
                s=r['supplemental_route']
                text+='; separate native attempt '+str(s['status'])+' with '+str(s['successful_compilations'])+'/'+str(s['source_module_count'])+' source successes'
                if s['current_module']:text+=' and current module '+str(s['current_module'])
                text+='; not yet qualified as a complete replacement; receipt Verification/'+s['receipt']
                if s.get('observer_limitation_preserved'):
                    text+='; its memory-observer limitation is preserved separately'
        else:text+='; '+str(r['source_module_count'])+' source modules planned, no completed run receipt'
        parts.append(text)
    if identifier=='DMS':
        alternative=qualified_dms_composite_route()
        if alternative:
            parts.append('Separate qualified body-identical composite route: all 228 scientific bodies are checked through 99 previous original-owned outputs via read-only V1 copies, 122 unaffected V3-owned passes and seven new V4 source checks. The original frozen-source 119-module checkpoint is not replaced. The original organizer audit exited 1 with 120/123 prints; a separate supplement adds only import Star6Equiv and audits all 123 unchanged requests, with 120 standard-kernel and three axiom-free endpoints. A separate imported finite certificate, MGraph.k4subdiv_star6 in StarCert, uses native_decide outside that selected set; the whole portfolio is not asserted standard-only. The five infinite structural premises and general DMS conjecture remain open, and p=.15 is unchanged. Qualification: Verification/'+alternative['qualification_record'])
    if identifier=='erdos169-fourap':
        qualified=BASE/'e169-tactic-specific-v2-completed-qualification.json'
        if qualified.exists():
            raw=read_bytes_shared(qualified)
            assert hashlib.sha256(raw).hexdigest()=='57c466bc581ab50ab62c9fefeadc0a0a6637aee19c5151c652f387dfea56709d'
            route=json.loads(raw)
            assert route['status']=='PASS_BODY_IDENTICAL_IMPORT_ONLY_ROUTE_SELECTED_ENDPOINT_STANDARD_AXIOMS'
            assert hashlib.sha256(read_bytes_shared(Path(route['receipt']))).hexdigest()==route['receipt_sha256']
            parts.append('Separate qualified import-only route: all22 unchanged scientific proof bodies and the unchanged final audit pass, with standard kernel axioms only; seven import headers were narrowed under the same source and compiler pins. This does not replace the original frozen-source receipt. Qualification: Verification/'+qualified.name)
    return 'Fresh execution: '+'. '.join(parts)+'. Compiler pins, source hashes and endpoint axiom outputs are in Verification. Historical receipts and finite checks do not replace fresh replay.'

if __name__=='__main__':
    from datetime import datetime,timezone
    projects=sorted({p for ids in FAMILY_PROJECTS.values() for p in ids})
    projects+=sorted({p.parent.name for p in (BASE/'builds').glob('*/build-plan.json') if p.parent.name not in {'luke-k4-ramsey-current-direct','luke-k4-ramsey-current-native'}}-set(projects))
    held_families={'FOCUS-RAMSEY','RAMSEY','FOCUS-GROTH','K61'}
    records=[]
    for project in projects:
        record=state(project)
        families=[f for f,ids in FAMILY_PROJECTS.items() if project in ids]
        record['publication_families']=families
        record['publication_bucket']=('original_result_candidate' if any(f not in held_families for f in families)
                                      else 'candidate_under_review' if families else 'known_or_additional_source_project')
        records.append(record)
    data={'generated_utc':datetime.now(timezone.utc).isoformat(),
          'policy':'A fresh pass certifies only the exact executed scope, not novelty, signed acceptance or general claims outside its hypotheses.',
          'family_projects':FAMILY_PROJECTS,'projects':records,
          'no_lean_source_families':['K61']}
    (BASE/'publication_execution_summary.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf8')
    from collections import Counter
    print(json.dumps({'projects':len(data['projects']),'statuses':dict(Counter(x['status'] for x in data['projects']))},indent=2))
