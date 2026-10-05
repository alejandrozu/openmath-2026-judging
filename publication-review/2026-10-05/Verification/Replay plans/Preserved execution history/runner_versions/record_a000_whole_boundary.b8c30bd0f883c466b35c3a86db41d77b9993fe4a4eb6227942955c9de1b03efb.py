"""Read-only exact A000 literal-import and selected-audit boundary evidence."""
from pathlib import Path
import hashlib,json
from full_mathlib_scope import classify
from lean_imports import read_imports
from receipt_io import read_bytes_shared
BASE=Path(__file__).resolve().parent;project='sakana-a000224'
file=BASE/'builds'/project/'build-plan.json';raw=file.read_bytes();plan=json.loads(raw)
receipt_raw=read_bytes_shared(BASE/(project+'-fresh-build.json'));receipt=json.loads(receipt_raw)
scope=classify(plan);whole=scope['authored_transitive_whole_Mathlib_closure']
mods={m['module']:m for m in plan['modules']};passed={r['module'] for r in receipt['builds'] if r['exit']==0}
rows=[{'module':n,'whole_roots':roots,'already_fresh_passed':n in passed,
       'source_sha256':mods[n]['sha256'],'imports':read_imports(mods[n]['file'])} for n,roots in whole.items()]
def closure(roots):
    seen=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n in seen or n not in mods:continue
        seen.add(n);todo.extend(read_imports(mods[n]['file']))
    return seen
audits=[]
for name in plan['audit_modules']:
    p=file.parent/name;imports=read_imports(p);deps=closure(imports)
    audits.append({'audit':name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
      'imports':imports,'authored_dependency_closure':sorted(deps),
      'whole_import_dependencies':sorted(deps & whole.keys()),
      'whole_roots':sorted({r for n in deps & whole.keys() for r in whole[n]}),
      'requires_separate_sole_literal_importer_lease':bool(deps & whole.keys()) or 'Mathlib' in imports})
out={'project':project,'source_plan_sha256':hashlib.sha256(raw).hexdigest(),
 'current_receipt_sha256':hashlib.sha256(receipt_raw).hexdigest(),'fresh_sources_passed':len(passed),
 'five_authored_whole_modules':rows,'selected_audits':audits,
 'qualification':'Read-only source and actual-success evidence; no source invocation. Whole-module and audit boundaries need a separately coordinated sole literal importer lease.'}
target=BASE/'a000224-whole-module-audit-boundary-evidence.json';assert not target.exists()
target.write_text(json.dumps(out,indent=2),encoding='utf8')
print(json.dumps({'modules':rows,'audits':[{k:a[k] for k in ['audit','whole_import_dependencies','whole_roots','requires_separate_sole_literal_importer_lease']} for a in audits]}),flush=True)
