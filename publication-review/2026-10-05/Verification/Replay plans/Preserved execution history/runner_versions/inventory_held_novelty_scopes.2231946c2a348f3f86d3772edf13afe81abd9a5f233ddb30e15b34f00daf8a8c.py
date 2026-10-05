"""Source-only inventory for held originality/priority candidates; no compiler."""
from pathlib import Path
import hashlib,json,time
from full_mathlib_scope import classify
from lean_imports import read_imports
BASE=Path(__file__).resolve().parent
ids=['sakana-FOCUS-RAMSEY','htpeo-ramsey-current','sakana-FOCUS-GROTH']
rows=[]
for project in ids:
    file=BASE/'builds'/project/'build-plan.json';raw=file.read_bytes();plan=json.loads(raw)
    total=0;mismatches=[]
    for mod in plan['modules']:
        data=Path(mod['file']).read_bytes();total+=len(data)
        if hashlib.sha256(data).hexdigest()!=mod['sha256']:mismatches.append(mod['module'])
    scope=classify(plan)
    audits=[{'name':name,'sha256':hashlib.sha256((file.parent/name).read_bytes()).hexdigest(),
      'imports':read_imports(file.parent/name)} for name in plan['audit_modules']]
    row={'id':project,'version':plan['version'],'mathlib_pin':plan.get('mathlib_pin'),
      'source_plan_sha256':hashlib.sha256(raw).hexdigest(),'source_modules':len(plan['modules']),
      'source_bytes':total,'source_hash_mismatches':mismatches,'import_scope':scope,
      'endpoints':plan.get('endpoints',[]),'selected_audits':audits,
      'lean_options':plan.get('lean_options',{}),'additional_dependency_libs':plan.get('additional_dependency_libs',[]),
      'first_frozen_module':plan['modules'][0]['module'],
      'status':'PREPARED_FROZEN_SOURCE_SCOPE_NO_FRESH_COMPILER_INVOCATION',
      'qualification':'Originality or priority hold remains distinct from compilation. All hashes and source imports inspected read-only; successful future replay would not itself establish novelty.'}
    rows.append(row);print(project,len(plan['modules']),total,'whole',scope['whole_Mathlib_closure_count'],'mismatches',len(mismatches),flush=True)
out=BASE/'held-novelty-candidate-source-inventory.json';assert not out.exists()
out.write_text(json.dumps({'recorded_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'projects':rows},indent=2),encoding='utf8')
