"""Assemble an explicitly provisional, evidence-linked release checklist."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib, json, os
from verification_summary import FAMILY_PROJECTS, state
from verification.receipt_io import read_json_shared

BASE=Path(__file__).resolve().parent
VER=BASE/'verification'
HELD={'K61','FOCUS-RAMSEY','RAMSEY','FOCUS-GROTH'}
coverage_path=VER/'selected-endpoint-output-coverage.json'
coverage=read_json_shared(coverage_path) if coverage_path.exists() else {'projects':[]}
coverage_by_project={r['project']:r for r in coverage['projects']}
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
    qualified_alternative_complete=any(r.get('covers_entire_family_selected_scientific_scope')
                                     and r.get('scientific_body_scope_complete')
                                     and r.get('selected_endpoint_scope_complete') for r in alternatives)
    families.append({'family':family,
                     'manuscript_class':'candidate_under_review' if family in HELD else 'original_result_candidate',
                     'fresh_Lean_projects':rows,
                     'fresh_Lean_scope_complete':original_complete,
                     'separate_qualified_body_identical_routes':alternatives,
                     'qualified_body_identical_alternative_scope_complete':qualified_alternative_complete,
                     'scientific_and_selected_verification_scope_complete':original_complete or qualified_alternative_complete,
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
        'completed_verified_original_family_scopes_including_qualified_body_identical_alternatives':sum(r['scientific_and_selected_verification_scope_complete'] for r in families if r['manuscript_class']=='original_result_candidate'),
        'coverage_receipt_sha256':hashlib.sha256(coverage_path.read_bytes()).hexdigest() if coverage_path.exists() else None,
        'families':families,
        'outbound_actions_performed':[]}
target=VER/'publication_release_readiness.json'
tmp=target.with_suffix('.json.tmp')
tmp.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8');os.replace(tmp,target)
print(json.dumps({'families':len(families),'classes':result['family_counts'],
                  'completed_fresh_original_family_scopes':result['completed_fresh_original_family_scopes']},indent=2))
