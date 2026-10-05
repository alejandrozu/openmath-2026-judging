"""Additive dated root resource/scope approval; never alters prepared receipts."""
from pathlib import Path
import hashlib,json,time
BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p):return {'file':str(p),'sha256':sha(p)}
a=BASE/'a000224-five-whole-module-guard-preparation.json';ap=json.loads(a.read_text())
h=BASE/'held-novelty-guarded-adapter-preparation.json';hp=json.loads(h.read_text())
assert ap['runner_sha256']=='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'
assert sha(BASE/'run_source_plan.py')==ap['runner_sha256']
assert hp['derived_runner_sha256']=='56952859e73e8773c44c84328e50144580527b82280da9d22229a2862ecedc10'
assert sha(BASE/'run_held_novelty_plan.py')==hp['derived_runner_sha256']
inventory=json.loads((BASE/'held-novelty-candidate-source-inventory.json').read_text())
doc={'recorded_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
 'status':'ROOT_EXECUTION_SCOPE_AND_RESOURCE_POLICY_APPROVED_NO_SCIENTIFIC_VERDICT',
 'approval_authority':'Root agent coordinating the user-authorized fresh Lean replay; this is not an additional human publishing/award approval.',
 'a000_approval':{'prepared_receipt':record(a),'runner':record(BASE/'run_source_plan.py'),
   'source_plan':record(BASE/'builds/sakana-a000224/build-plan.json'),
   'source_boundary_evidence':record(BASE/'a000224-whole-module-audit-boundary-evidence.json'),
   'scope':'Five exact whole-Mathlib authored modules plus selected audit only after166 granular own cold source successes and hashes.',
   'lease_requirement':'a000_whole_scope_only_authorized:true; exact holder/source-plan SHA; exclusive whole-import lease.',
   'pilot_policy':'One newly cold whole module first; actual measured PASS then unchanged guarded continuation.'},
 'held_approval':{'prepared_receipt':record(h),'adapter':record(BASE/'run_held_novelty_plan.py'),
   'source_plans':[record(BASE/'builds'/p['id']/'build-plan.json') for p in inventory['projects']],
   'source_inventory':record(BASE/'held-novelty-candidate-source-inventory.json'),
   'ht_mixed_boundary':record(BASE/'ht-ramsey-mixed-source-boundary-evidence.json'),
   'scope':'SakRam2 and Grot2 pilot/guarded replay after main granular scope; HT2092 granular source deferral, then exact11 whole modules/audit under separate explicit lease after2092 cold source successes.',
   'ht_whole_lease_requirement':'ht_ramsey_whole_scope_only_authorized:true plus exact holder/source-plan SHA and exclusive whole-import lease.'},
 'guards':{'granular':record(BASE/'matt_resource_guard.py'),'whole':record(BASE/'full_mathlib_resource_guard.py')},
 'scheduling':{'granular':'At most TWO measured granular source importers,6GiB own/5GiB commit dispatch with existing physical/disk/commit floors.',
   'whole':'SOLE whole10GiB own/11GiB commit source importer, serialized against both granular workers; existing physical/disk/commit floors unchanged.',
   'next_release':'E169 lease ends first; main granular resumes with Luke. When Luke completes/checkpoints, main pauses at a completed source boundary for DMS whole resume. A000/HT whole phases require later explicit handoffs.'},
 'scientific_qualification':'These approvals authorize concrete source execution and resource guards only. They do not establish mathematical novelty, eligibility, authorship, awards, successful compilation, or publication readiness. Original PREPARED records remain immutable.'}
out=BASE/'root-resource-scope-approvals-20261005.json';assert not out.exists()
out.write_text(json.dumps(doc,indent=2),encoding='utf8');print(json.dumps({'receipt':str(out),'sha256':sha(out)}),flush=True)
