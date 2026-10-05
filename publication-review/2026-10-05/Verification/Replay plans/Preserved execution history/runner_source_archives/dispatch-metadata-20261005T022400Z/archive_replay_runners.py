"""Add immutable operational-source snapshots; never rewrite prior versions."""
from pathlib import Path
import hashlib,json,time
BASE=Path(__file__).resolve().parent
dest=BASE/'runner_versions'
dest.mkdir(exist_ok=True)
rows=[]
for name in ('run_source_plan.py','audit_axioms.py','lean_imports.py','resource_metrics.py',
             'matt_resource_guard.py','native_resource_guard.py','receipt_io.py',
             'full_mathlib_resource_guard.py','full_mathlib_scope.py','hold_dms_dispatcher.py','record_dependency_working_tree_caveats.py',
             'dms_pending_row_boundary.py','finalize_dms_boundary_checkpoint.py','record_a000_whole_boundary.py',
             'checkpoint_kobon_for_e169.py','run_remaining_main_granular_queue.py','inventory_held_novelty_scopes.py',
             'run_held_novelty_plan.py','prepare_held_novelty_adapter.py','record_root_scope_approvals.py'):
    original=BASE/name
    if not original.exists():continue
    raw=original.read_bytes();sha=hashlib.sha256(raw).hexdigest()
    file=dest/(original.stem+'.'+sha+original.suffix)
    if file.exists():assert file.read_bytes()==raw
    else:file.write_bytes(raw)
    rows.append({'original':str(original),'sha256':sha,'immutable_snapshot':str(file)})
receipt={'saved_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
 'qualification':'CURRENT_OPERATIONAL_CODE_SNAPSHOTS_FOR_FUTURE_INVOCATIONS; no claim that older running processes loaded these versions.',
 'files':rows}
name=dest/('snapshot-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'.json')
assert not name.exists();name.write_text(json.dumps(receipt,indent=2),encoding='utf8')
print(name,flush=True)
