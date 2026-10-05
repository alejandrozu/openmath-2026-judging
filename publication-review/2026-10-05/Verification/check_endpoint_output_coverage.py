"""Independent read-only check that requested axiom prints actually appeared."""
from pathlib import Path
import json,re,os
from datetime import datetime,timezone
from audit_axioms import parse
from receipt_io import read_json_shared
from execution_receipt_selection import receipt_path
BASE=Path(__file__).resolve().parent
canonical=lambda s:s.replace('«','').replace('»','').strip()
rows=[]
for plan_path in sorted((BASE/'builds').glob('*/build-plan.json')):
 plan=json.loads(plan_path.read_text(encoding='utf8'))
 route=plan_path.parent.name
 project=plan.get('id',route)
 if project=='luke-k4-ramsey-current':
  selected=receipt_path(project)
  selected_route=selected.name.removesuffix('-fresh-build.json')
  if route!=selected_route:continue
 expected=[canonical(name) for name in plan.get('endpoints',[])]
 for module in plan.get('audit_modules',[]):
  source=plan_path.parent/module
  if source.exists():
   expected += [canonical(m) for m in re.findall(r'(?m)^\s*#print\s+axioms\s+([^\s]+)',source.read_text(encoding='utf8'))]
 if project=='luke-k4-ramsey-current':
  preflight=BASE/'luke-source-preflight.json'
  if preflight.exists():
   expected += [canonical(name) for names in json.loads(preflight.read_text(encoding='utf8'))['submitted_endpoint_audits'].values() for name in names]
 receipt=receipt_path(project)
 data=read_json_shared(receipt) if receipt.exists() else {}
 outputs=[]
 for build in data.get('builds',[]):
  if build.get('exit')==0 and (build.get('is_endpoint_audit') or build.get('module','').endswith('FreshAudit.lean')):
   outputs += parse(build.get('stdout',''))
 observed={canonical(o['endpoint']) for o in outputs}
 expected=set(expected)
 status=data.get('status',data.get('overall_status','NOT_RUN'))
 missing=sorted(expected-observed)
 completed_pass=str(status).startswith('PASS')
 rows.append({'project':project,'execution_route':route,'execution_status':status,
  'expected_selected_endpoints':len(expected),'printed_endpoints':len(observed),
  'missing_outputs':missing,'output_coverage':'MISSING_REQUIRED_PRINTS' if completed_pass and missing else ('PASS' if completed_pass and expected else ('SELECTED_SCOPE_NOT_DEFINED' if completed_pass else 'NOT_COMPLETE')),
  'parsed_endpoint_axioms':outputs,'receipt':receipt.name if receipt.exists() else None})
special=BASE/'chandragupt-pinned-build.json'
if special.exists() and not any(r['project']=='chandragupt' for r in rows):
 data=read_json_shared(special)
 outputs=[o for b in data.get('builds',[]) if b.get('exit')==0 for o in parse(b.get('stdout',''))]
 expected=set(data['endpoints']);observed={o['endpoint'] for o in outputs}
 rows.append({'project':'chandragupt','execution_status':data.get('overall_status','PASS' if data.get('all_pass') else 'UNCLASSIFIED'),
  'expected_selected_endpoints':len(expected),'printed_endpoints':len(observed),
  'missing_outputs':sorted(expected-observed),'output_coverage':'PASS' if expected<=observed else 'MISSING_REQUIRED_PRINTS',
  'parsed_endpoint_axioms':outputs,'receipt':special.name})
result={'generated_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'Checks requested selected axiom-output coverage independently of runner status. Does not certify novelty, semantic fidelity, or absent/unexecuted proofs.',
 'projects':rows}
target=BASE/'selected-endpoint-output-coverage.json';tmp=target.with_suffix('.json.tmp')
tmp.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8');os.replace(tmp,target)
print(json.dumps({'projects':len(rows),'completed_coverage_pass':sum(r['output_coverage']=='PASS' for r in rows),
 'missing_from_completed_pass':[r['project'] for r in rows if r['output_coverage']=='MISSING_REQUIRED_PRINTS']},indent=2))
