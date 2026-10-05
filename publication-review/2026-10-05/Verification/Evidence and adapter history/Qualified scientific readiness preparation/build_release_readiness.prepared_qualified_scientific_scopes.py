"""Assemble an explicitly provisional, evidence-linked release checklist."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib, json, os
from verification_summary import FAMILY_PROJECTS, state
from verification.receipt_io import read_json_shared, read_bytes_shared

BASE=Path(__file__).resolve().parent
VER=BASE/'verification'
HELD={'K61','FOCUS-RAMSEY','RAMSEY','FOCUS-GROTH'}
coverage_path=VER/'selected-endpoint-output-coverage.json'
coverage=read_json_shared(coverage_path) if coverage_path.exists() else {'projects':[]}
coverage_by_project={r['project']:r for r in coverage['projects']}
def _bound_json(name, digest):
    path=VER/name
    raw=read_bytes_shared(path)
    assert hashlib.sha256(raw).hexdigest()==digest
    return path, json.loads(raw)

def _bound_receipt(path, digest):
    raw=read_bytes_shared(Path(path))
    assert hashlib.sha256(raw).hexdigest()==digest
    receipt=json.loads(raw)
    assert receipt.get('status')=='PASS' and receipt.get('finished_utc')
    return receipt

def _artifact_identities(rows):
    for row in rows:
        path=Path(row['file'])
        assert path.stat().st_size==row['bytes']
        assert hashlib.sha256(read_bytes_shared(path)).hexdigest()==row['sha256']

def _standard_selected(rows, count):
    assert len(rows)==count and len({r['endpoint'] for r in rows})==count
    assert all(r['classification']=='STANDARD_KERNEL_AXIOMS'
               and not r.get('native_axioms') and not r.get('unrecognized_axioms')
               and 'sorryAx' not in r.get('axioms',[]) for r in rows)

def qualified_scientific_scope(family):
    # Independently qualified evidence never rewrites the original raw status,
    # raw output coverage, missing outputs or recorded resource stops.
    if family=='erdos169-fourap':
        path,q=_bound_json('e169-tactic-specific-v2-completed-qualification.json',
            '57c466bc581ab50ab62c9fefeadc0a0a6637aee19c5151c652f387dfea56709d')
        assert q['status']=='PASS_BODY_IDENTICAL_IMPORT_ONLY_ROUTE_SELECTED_ENDPOINT_STANDARD_AXIOMS'
        receipt=_bound_receipt(q['receipt'],q['receipt_sha256'])
        assert q['authored_source_modules_passed']==22 and q['selected_endpoint_prints']==1
        assert len(q['scientific_body_identity_checks'])==22
        assert all(r['scientific_body_options_comments_identical'] for r in q['scientific_body_identity_checks'])
        _standard_selected(q['actual_selected_axiom_review'],1)
        _artifact_identities(q['actual_output_identities'])
        source_count,selected_count,kind,alternative=22,1,'BODY_IDENTICAL_IMPORT_ONLY_OPERATIONAL_ROUTE',True
        scope=q['qualification']
        receipts=[{'receipt':Path(q['receipt']).name,'sha256':q['receipt_sha256']}]
    elif family=='FOCUS-MATRIX':
        path,q=_bound_json('focus-matrix-three-seed-completed-artifact-roots-qualified-20261005.json',
            '4337a4f479fb2e6ef9436a7e7533797070de4b525a5642f8cde1b545803d4703')
        assert q['status']=='PASS_EXACT_THREE_SEED_213_SOURCE_18_STANDARD_SELECTED_ENDPOINT_SCOPE'
        assert (q['authored_sources_passed'],q['requested_selected_prints_passed'])==(213,18)
        assert q['selected_native_admitted_unknown_axioms']==0 and len(q['projects'])==3
        assert {p['project_id'] for p in q['projects']}==set(FAMILY_PROJECTS[family])
        receipts=[]
        for p in q['projects']:
            receipt=_bound_receipt(p['receipt'],p['receipt_sha256'])
            assert hashlib.sha256(read_bytes_shared(Path(p['plan']))).hexdigest()==p['plan_sha256']
            assert p['source_count']==71 and p['selected_print_count']==6
            assert p['all_current_own_output_hashes_rechecked'] is True
            assert len(p['source_artifact_roots'])==71
            for root in p['source_artifact_roots']:_artifact_identities(root['actual_artifacts'])
            assert len(p['actual_selected_audits'])==1
            for audit in p['actual_selected_audits']:
                _standard_selected(audit['six_actual_selected_prints'],6)
                assert hashlib.sha256(read_bytes_shared(Path(audit['stdout_file']))).hexdigest()==audit['stdout_sha256']
                _artifact_identities(audit['actual_artifacts'])
            receipts.append({'project':p['project_id'],'receipt':Path(p['receipt']).name,'sha256':p['receipt_sha256']})
        source_count,selected_count,kind,alternative=213,18,'UNCHANGED_FROZEN_ORIGINAL_THREE_SEED_RECEIPTS_INDEPENDENTLY_QUALIFIED',False
        scope=q['scoped_conclusion']
    elif family=='FOCUS-GROTH':
        path,q=_bound_json('groth-exact2-source5-completed-qualification-20261005.json',
            '9bc15bcba169f703e53b019ad2adaa7fca3645aaee07aa41a7df9e835ba009e1')
        assert q['status']=='PASS_EXACT_UNCHANGED_GROTH2_SOURCE5_SELECTED_OUTPUT_STANDARD_SCOPE'
        receipt=_bound_receipt(VER/'sakana-FOCUS-GROTH-fresh-build.json',q['completed_receipt_sha256'])
        assert (q['authored_source_passes'],q['selected_unique_prints'])==(2,5)
        _standard_selected(q['actual_selected_axiom_classifications'],5)
        _artifact_identities(q['current_own_artifact_identities'])
        for r in q['raw_log_identities']:
            assert hashlib.sha256(read_bytes_shared(Path(r['file']))).hexdigest()==r['sha256']
        source_count,selected_count,kind,alternative=2,5,'UNCHANGED_FROZEN_ORIGINAL_RESTRICTED_SCOPE_INDEPENDENTLY_QUALIFIED',False
        scope=q['scientific_scope']
        receipts=[{'receipt':'sakana-FOCUS-GROTH-fresh-build.json','sha256':q['completed_receipt_sha256']}]
    else:return None
    return {'family':family,'status':q['status'],'qualified':True,
            'scientific_body_scope_complete':True,'selected_endpoint_scope_complete':True,
            'covers_entire_family_selected_scientific_scope':True,
            'qualification_record':path.name,'qualification_record_sha256':hashlib.sha256(read_bytes_shared(path)).hexdigest(),
            'source_route_kind':kind,'is_body_identical_alternative_route':alternative,
            'scientific_body_count':source_count,'selected_endpoint_count':selected_count,
            'selected_classification_counts':{'STANDARD_KERNEL_AXIOMS':selected_count},
            'selected_native_evaluation_count':0,'selected_admitted_count':0,'selected_unknown_axiom_count':0,
            'qualified_receipts':receipts,'scientific_scope':scope,
            'raw_original_status_or_coverage_replaced':False,
            'novelty_score_resource_class_placement_or_release_acceptance_upgraded':False}

families=[]
for family, projects in FAMILY_PROJECTS.items():
    rows=[]
    for project in projects:
        r=state(project)
        c=coverage_by_project.get(project,{})
        r['selected_output_coverage']=c.get('output_coverage','NO_COVERAGE_RECEIPT')
        r['missing_selected_outputs']=c.get('missing_outputs',[])
        r['fresh_executed_scope_complete']=(str(r['status']).startswith('PASS') and r['selected_output_coverage']=='PASS')
        rows.append(r)
    original_complete=bool(rows) and all(r['fresh_executed_scope_complete'] for r in rows)
    alternatives=[r['qualified_alternative_route'] for r in rows
                  if r.get('qualified_alternative_route') and r['qualified_alternative_route'].get('qualified')]
    independently_qualified=qualified_scientific_scope(family)
    if independently_qualified and independently_qualified['is_body_identical_alternative_route']:
        alternatives.append(independently_qualified)
    scientific_routes=list(alternatives)
    if independently_qualified and not independently_qualified['is_body_identical_alternative_route']:
        scientific_routes.append(independently_qualified)
    qualified_alternative_complete=any(r.get('covers_entire_family_selected_scientific_scope')
                                     and r.get('scientific_body_scope_complete')
                                     and r.get('selected_endpoint_scope_complete') for r in alternatives)
    qualified_scientific_complete=any(r.get('covers_entire_family_selected_scientific_scope')
                                    and r.get('scientific_body_scope_complete')
                                    and r.get('selected_endpoint_scope_complete') for r in scientific_routes)
    families.append({'family':family,
                     'manuscript_class':'candidate_under_review' if family in HELD else 'original_result_candidate',
                     'fresh_Lean_projects':rows,
                     'fresh_Lean_scope_complete':original_complete,
                     'separate_qualified_body_identical_routes':alternatives,
                     'qualified_body_identical_alternative_scope_complete':qualified_alternative_complete,
                     'independently_qualified_scientific_routes':scientific_routes,
                     'independently_qualified_scientific_scope_complete':qualified_scientific_complete,
                     'scientific_and_selected_verification_scope_complete':original_complete or qualified_scientific_complete,
                     'no_Lean_source':family=='K61',
                     'release_status':'UNSENT_PRELIMINARY_REVIEW',
                     'additional_release_decisions':['Originality and exact statement fidelity determination',
                        'Two required independent technical judgments',
                        'Contributor-approved names, contribution roles, author order and publication affiliations',
                        'Resource class and scoring acceptance',
                        'Contributor approval of coordinated anthology or individual release']})
result={'generated_utc':datetime.now(timezone.utc).isoformat(),
        'judged_and_evaluated_by':'Alejandro Zarzuelo Urdiales',
        'event':'OpenMath 2026, 27 September–2 October; organizer sources for Harvard Innovation Labs and MIT kickoff are cited in the manuscripts',
        'scope':'Completion of fresh proof replay is separate from originality, scoring acceptance and publication authorization. A pending or partial route is never counted as a pass.',
        'approved_rulings':['October 4 amendments R1–R6','Late Luke/Madhan and Matt deliveries accepted for intake','DMS p=0.15 retained','Leanification mention only'],
        'family_counts':dict(Counter(r['manuscript_class'] for r in families)),
        'completed_fresh_original_family_scopes':sum(r['fresh_Lean_scope_complete'] for r in families if r['manuscript_class']=='original_result_candidate'),
        'completed_verified_original_family_scopes_including_qualified_body_identical_alternatives':sum(r['fresh_Lean_scope_complete'] or r['qualified_body_identical_alternative_scope_complete'] for r in families if r['manuscript_class']=='original_result_candidate'),
        'completed_verified_original_family_scopes_including_independently_qualified_scientific_scopes':sum(r['scientific_and_selected_verification_scope_complete'] for r in families if r['manuscript_class']=='original_result_candidate'),
        'verification_count_policy':'Strict raw receipt plus dated output-coverage count is retained separately. Independently qualified unchanged-original-source scopes and body-identical import/composite alternatives are distinct; neither overwrites raw statuses or publication decisions.',
        'coverage_receipt_sha256':hashlib.sha256(coverage_path.read_bytes()).hexdigest() if coverage_path.exists() else None,
        'families':families,
        'outbound_actions_performed':[]}
target=VER/'publication_release_readiness.json'
tmp=target.with_suffix('.json.tmp')
tmp.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8');os.replace(tmp,target)
print(json.dumps({'families':len(families),'classes':result['family_counts'],
                  'completed_fresh_original_family_scopes':result['completed_fresh_original_family_scopes']},indent=2))
