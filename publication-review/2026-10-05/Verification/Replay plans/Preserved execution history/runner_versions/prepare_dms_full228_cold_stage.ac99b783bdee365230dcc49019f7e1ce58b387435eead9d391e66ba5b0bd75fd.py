"""Authorized cold import-only staging; never compiles or copies proof outputs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,difflib
BASE=Path(__file__).resolve().parent
def sha(raw):return hashlib.sha256(raw).hexdigest()
def digest(path):return sha(Path(path).read_bytes())
def save_new(path,value):
    assert not path.exists(),str(path)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    return digest(path)
complete_path=BASE/'dms-full228-complete-official-closure-and-reuse-proposal-20261005.json'
assert digest(complete_path)=='620fe0d86aff72859d8b9d97d8f793988710a145f200ae3cb4f05ea322f2bd2a'
complete=json.loads(complete_path.read_bytes())
binding_path=BASE/'dms-original119-immutable-receipt-binding-20261005.json'
assert digest(binding_path)=='aec27ee3a48676b1dadf8910c80a7dbc57e115c20cb7016565b1237740d5e248'
binding=json.loads(binding_path.read_bytes())
assert digest(binding['immutable_original119_receipt'])==binding['original119_receipt_sha256']
prior=json.loads(Path(complete['prior_full228_proposal']).read_bytes())
plan_path=Path(complete['hypothetical_plan'])
assert digest(plan_path)==complete['hypothetical_plan_sha256']
plan=json.loads(plan_path.read_bytes())
dest=BASE/'builds'/plan['id']
assert not dest.exists(), 'The separate cold diagnostic tree must not already exist'
original=BASE/'builds/htpeo-dms-current'
changes={row['module']:row for row in prior['only_import_changes']}
dest.mkdir()
modules=[];identities=[]
for row in plan['modules']:
    source=Path(row['original_file'])
    raw=source.read_bytes()
    assert sha(raw)==row['original_sha256']
    if row['module'] in changes:
        change=changes[row['module']]
        start,end=change['replaced_bytes_start'],change['replaced_bytes_end']
        assert raw[start:end]==b'import Mathlib'
        replacement=change['proposed_header_span'].encode('utf8')
        staged=raw[:start]+replacement+raw[end:]
        assert raw[:start]+raw[end:]==staged[:start]+staged[start+len(replacement):]
        body=sha(raw[:start]+raw[end:])
        assert body==change['remainder_body_sha256']
    else:
        staged=raw;body=sha(raw)
    assert sha(staged)==row['sha256']
    relative=source.relative_to(original)
    target=dest/relative
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as stream:stream.write(staged)
    modules.append(dict(row,file=str(target.resolve())))
    identities.append({'module':row['module'],'relative_path':relative.as_posix(),
        'original_source':str(source),'original_source_sha256':sha(raw),
        'staged_source':str(target.resolve()),'staged_source_sha256':sha(staged),
        'header_changed':row['module'] in changes,
        'scientific_body_options_comments_sha256':body,
        'body_identity':True,'whole_file_identity':raw==staged})
audits=[]
for row in prior['original_and_proposed_audit_identity_inventory']:
    src=Path(row['original_file']);raw=src.read_bytes()
    assert sha(raw)==row['original_and_proposed_sha256']
    target=dest/src.relative_to(original)
    with target.open('xb') as stream:stream.write(raw)
    audits.append(dict(row,staged_file=str(target.resolve()),staged_sha256=sha(raw)))
plan=dict(plan,source_dir=str(dest.resolve()),modules=modules,
    status='PREPARED_COLD_IMPORT_ONLY_DIAGNOSTIC_NO_REUSE_NO_COMPILATION',builds=[],
    scientific_route_qualification='All228 bodies/options/comments unchanged; three reviewed import spans differ. Separate diagnostic route, not full original-source replay.',
    original119_immutable_receipt=binding['immutable_original119_receipt'],
    original119_immutable_receipt_sha256=binding['original119_receipt_sha256'],
    exact_full_official_closure=complete['complete_official_graph']['source_artifact_manifest'],
    exact_full_official_closure_sha256=complete['complete_official_graph']['source_artifact_manifest_sha256'])
actual_plan=dest/'build-plan.json'
plan_sha=save_new(actual_plan,plan)
identity_file=dest/'stage-source-identity-manifest.json'
identity_sha=save_new(identity_file,{'status':'COLD_ACTUAL_STAGE_ALL_BODIES_AUDITS_IDENTICAL_NO_OWN_OUTPUTS',
    'sources':identities,'audits':audits,'custom_compiled_artifacts_present':False})
assert not list(dest.rglob('*.olean')) and not list(dest.rglob('*.ilean'))

base_runner=BASE/'run_source_plan.py'
old=base_runner.read_bytes()
assert sha(old)=='70ff209c7ac651c1e0ab25e9f629a9fc50c4b85ed1f510666e851e8f69c53534'
text=old.decode('utf8')
needle=" 'sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2','matt-unitary-current','htpeo-dms-current'}"
assert text.count(needle)==1
text=text.replace(needle,needle[:-1]+",'htpeo-dms-current-import-pruned-diagnostic'}")
needle2="plan=json.loads((dest/'build-plan.json').read_text())"
assert text.count(needle2)==1
extra="""
# Exact import-only DMS adapter: no full-source mode or cross-route output reuse.
assert project=='htpeo-dms-current-import-pruned-diagnostic' and worker_threads==1
assert third_worker_guarded and not full_mathlib_source_mode and not independent_resource_mode and not defer_whole_import_mode
from verify_dms_full228_stage import verify_stage
dms_stage_preflight=verify_stage(require_cold=not (BASE/(project+'-fresh-build.json')).exists())
plan['import_only_stage_identity_preflight']=dms_stage_preflight
"""
text=text.replace(needle2,needle2+'\n'+extra)
new=text.encode('utf8')
runner=BASE/'run_dms_import_pruned_plan.py'
with runner.open('xb') as stream:stream.write(new)
diff=''.join(difflib.unified_diff(old.decode().splitlines(True),text.splitlines(True),
    fromfile='run_source_plan.py@70ff209c',tofile=runner.name))
diff_file=BASE/'dms-import-pruned-runner-prepared.diff'
with diff_file.open('xb') as stream:stream.write(diff.encode('utf8'))
record={'status':'ACTUAL_COLD_STAGE_AND_GUARDED_RUNNER_PREPARED_NO_REUSE_NO_LEAN_INVOCATION',
    'prepared_utc':datetime.now(timezone.utc).isoformat(),
    'stage':str(dest.resolve()),'diagnostic_source_plan':str(actual_plan),'diagnostic_source_plan_sha256':plan_sha,
    'stage_identity_manifest':str(identity_file),'stage_identity_manifest_sha256':identity_sha,
    'full228_body_and_audit_identity':True,'source_count':228,'changed_import_headers':3,
    'selected_print_requests':123,'original_project':'htpeo-dms-current',
    'immutable_original119_receipt':binding['immutable_original119_receipt'],
    'immutable_original119_receipt_sha256':binding['original119_receipt_sha256'],
    'complete_reviewed_proposal':str(complete_path),'complete_reviewed_proposal_sha256':digest(complete_path),
    'official_full_source_artifact_closure':plan['exact_full_official_closure'],
    'official_full_source_artifact_closure_sha256':plan['exact_full_official_closure_sha256'],
    'prepared_runner':str(runner),'prepared_runner_sha256':sha(new),
    'base_runner':str(base_runner),'base_runner_sha256':sha(old),
    'runner_diff':str(diff_file),'runner_diff_sha256':digest(diff_file),
    'resource_guard':'UNCHANGED6GiB_OWN/5GiB_COMMIT_DISPATCH;4GB_DISK/6GiB_PHYSICAL;CONTINUOUS1GB_DISK/3GiB_PHYSICAL/1GiB_COMMIT;J1',
    'current_custom_outputs':[],'cross_route_output_reuse':'NOT_IMPLEMENTED_OR_AUTHORIZED',
    'qualification':'Root authorized cold staging only. Actual reuse/staged verifier review and any source pilot require a separate explicit resource lease; no current main runner was changed.'}
out=BASE/'dms-full228-cold-stage-and-adapter-preparation-20261005.json'
out_sha=save_new(out,record)
assert digest(BASE/'htpeo-dms-current-fresh-build.json')==binding['original119_receipt_sha256']
assert digest(base_runner)==sha(old)
print(json.dumps({'preparation':str(out),'preparation_sha256':out_sha,
    'plan_sha256':plan_sha,'runner_sha256':sha(new),'runner_diff_sha256':digest(diff_file),
    'sources':len(modules),'audits':len(audits),'status':record['status']},indent=2),flush=True)
