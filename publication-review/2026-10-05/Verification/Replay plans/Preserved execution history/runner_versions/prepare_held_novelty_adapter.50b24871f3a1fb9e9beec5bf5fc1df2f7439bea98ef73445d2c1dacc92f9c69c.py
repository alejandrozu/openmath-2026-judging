"""Prepare a separate root-reviewable held-scope adapter; no Lean invocation."""
from pathlib import Path
import ast,hashlib,json
BASE=Path(__file__).resolve().parent
original=BASE/'run_source_plan.py';raw=original.read_bytes();text=raw.decode('utf8')
inventory=json.loads((BASE/'held-novelty-candidate-source-inventory.json').read_text())
ht=next(p for p in inventory['projects'] if p['id']=='htpeo-ramsey-current')
planfile=BASE/'builds/htpeo-ramsey-current/build-plan.json';planraw=planfile.read_bytes();plan=json.loads(planraw)
assert hashlib.sha256(planraw).hexdigest()==ht['source_plan_sha256']
whole=set(ht['import_scope']['authored_transitive_whole_Mathlib_closure']);assert len(whole)==11
boundary={'project':plan['id'],'source_plan_sha256':ht['source_plan_sha256'],
 'whole_authored_modules':[m for m in plan['modules'] if m['module'] in whole],
 'whole_roots':ht['import_scope']['direct_whole_Mathlib_import_modules'],
 'selected_audits':ht['selected_audits'],'granular_source_successes_required':2092,
 'qualification':'Prepared source boundary only. Originality hold remains; no source attempt or successful replay is implied.'}
evidence=BASE/'ht-ramsey-mixed-source-boundary-evidence.json';assert not evidence.exists()
evidence.write_text(json.dumps(boundary,indent=2),encoding='utf8')
changes=[]
def change(before,after):
 global text
 assert text.count(before)==1,repr(before)
 text=text.replace(before,after);changes.append({'before':before,'after':after})
change("'matt-unitary-current','htpeo-dms-current'}", "'matt-unitary-current','htpeo-dms-current','sakana-FOCUS-RAMSEY','sakana-FOCUS-GROTH','htpeo-ramsey-current'}")
change(" assert project=='sakana-a000224' and third_worker_continuation and not full_mathlib_source_mode, 'Only the root-authorized A000 granular remainder with separate whole-import lease deferred'",
 " assert project in {'sakana-a000224','htpeo-ramsey-current'} and third_worker_guarded and not full_mathlib_source_mode, 'Only the explicitly root-reviewed mixed-source granular remainder; whole-import lease deferred'\n assert project!='sakana-a000224' or third_worker_continuation,'Existing narrower A000 deferral policy unchanged'")
needle="paths=[str(dest)]"
insert="""if full_mathlib_source_mode and project=='htpeo-ramsey-current':
 evidence=json.loads((BASE/'ht-ramsey-mixed-source-boundary-evidence.json').read_text())
 assert evidence['source_plan_sha256']==hashlib.sha256((dest/'build-plan.json').read_bytes()).hexdigest()
 expected={m['module']:m['sha256'] for m in evidence['whole_authored_modules']}
 whole=set(full_scope['authored_transitive_whole_Mathlib_closure'])
 assert whole==set(expected) and len(whole)==11
 assert lease.get('ht_ramsey_whole_scope_only_authorized') is True,'Separate reviewed HT eleven-module whole-import lease required'
 assert prior,'All2092 granular sources require actual cold source successes before whole-import scope'
 granular={m['module'] for m in plan['modules']}-whole
 actual_passes={r['module'] for r in prior['builds'] if r['exit']==0 and not r.get('stop_reason')}
 assert len(granular)==2092 and granular<=actual_passes
 for m in plan['modules']:
  if m['module'] in expected:assert m['sha256']==expected[m['module']]
 for a in evidence['selected_audits']:assert hashlib.sha256((dest/a['name']).read_bytes()).hexdigest()==a['sha256']
"""
change(needle,insert+needle)
ast.parse(text)
derived=BASE/'run_held_novelty_plan.py';assert not derived.exists();derived.write_text(text,encoding='utf8')
receipt={'status':'PREPARED_NOT_EXECUTED_ROOT_REVIEW_REQUIRED','original_runner':str(original),
 'original_runner_sha256':hashlib.sha256(raw).hexdigest(),'derived_runner':str(derived),
 'derived_runner_sha256':hashlib.sha256(derived.read_bytes()).hexdigest(),'exact_operational_changes':changes,
 'held_sources':'All original entrant2107 source files and every selected audit source are unchanged.',
 'ht_granular_command_flags':['--pilot-third-slot','--defer-whole-imports'],
 'ht_whole_command_flags':['--pilot-third-slot','--full-mathlib-source-mode'],
 'resource_policy':'Granular6GiB own/5GiB commit; separate whole10GiB own/11GiB commit after2092 granular passes; existing physical/disk/commit floors and suspended-before-job-assignment behavior unchanged.',
 'boundary_evidence':str(evidence),'boundary_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
 'qualification':'Prepared isolated adapter only; no compiler or source change. It additionally whitelists the two short held candidates for later actual fresh attempts under the already authorized6/5 guard.'}
out=BASE/'held-novelty-guarded-adapter-preparation.json';assert not out.exists();out.write_text(json.dumps(receipt,indent=2),encoding='utf8')
print(json.dumps({'status':receipt['status'],'derived_runner_sha256':receipt['derived_runner_sha256'],'source_counts':{'ht_granular':2092,'ht_whole':11,'sak_ramsey':2,'sak_groth':2}}),flush=True)
