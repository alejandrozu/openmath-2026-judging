"""Freeze concrete all-cache housekeeping policy; no cache removal or Lean."""
from pathlib import Path
import ast, collections, datetime, hashlib, json, subprocess

BASE=Path(__file__).resolve().parent
OUT=BASE/'proposals/official-binary-ltar-cache-storage-assessment-20261005'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def ref(path):return {'file':str(path),'sha256':sha(path)}
assessment=OUT/'root-review-storage-assessment-and-small-batch-proposal.json'
assert sha(assessment)=='5539f9727babf819d1db83caa09347ec26bf85398d4b6d861054505d4076f910'
a=json.loads(assessment.read_text(encoding='utf8'))
manifest=Path(a['full_exact_candidate_manifest']['file'])
assert sha(manifest)=='a833366f8f7f35102ad204be351655605e04e7ca53e37ea5ea520592cac910cd'
rows=json.loads(manifest.read_text(encoding='utf8'));assert len(rows)==25906
helper=BASE/'task_official_binary_ltar_cache_housekeeping_20261005.py'
ast.parse(helper.read_text(encoding='utf8'))
pins={'4.30.0-rc2':'c1e30e172c8fda21e6776bf1f10351e882ee31b9',
      '4.33.1':'0df444a360eaa60ab8c11dca51a86af692955474',
      '4.34.1':'d13f23b723b8a846827a245b89c10fc7d3f11612'}
bindings=[];presence={};remote=[]
for version,pin in pins.items():
    installed=BASE/f'lean-{version}-installation.json'
    install=json.loads(installed.read_text(encoding='utf8'));assert install['complete'] is True
    passed=BASE/f'mathlib-{version}-cache-retry.json'
    receipt=json.loads(passed.read_text(encoding='utf8'));assert receipt['status']=='PASS'
    plan_file=BASE/f'official-cache-plan-{version}.json'
    assert sha(plan_file)==receipt['official_plan_sha256']
    plan=json.loads(plan_file.read_text(encoding='utf8'))
    root=BASE/'dependencies'/version/'mathlib'
    actual=subprocess.run(['git','--no-optional-locks','rev-parse','HEAD'],cwd=root,capture_output=True,text=True,check=True).stdout.strip()
    assert actual==pin
    compiler=BASE/'runtimes'/f'lean-{version}-windows/bin/lean.exe'
    count=collections.Counter()
    for row in plan:
        trace=Path(row['trace']).resolve();assert trace.is_relative_to((BASE/'dependencies'/version).resolve())
        for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
            if trace.with_suffix(suffix).is_file():count[suffix]+=1
        assert trace.with_suffix('.olean').is_file(),str(trace)
    presence[version]=dict(count)
    binding={'version':version,'mathlib_pin':pin,'dependency_source_root':str(root),
        'installation_receipt':ref(installed),'official_cache_PASS_receipt':ref(passed),'official_cache_plan':ref(plan_file),
        'runtime_lean_binary':ref(compiler),'official_mathlib_source':ref(root/'Mathlib.lean'),
        'official_mathlib_olean':ref(root/'.lake/build/lib/lean/Mathlib.olean'),'cache_plan_module_count':len(plan),
        'source_runtime_and_installed_compiled_roots_are_never_cleanup_targets':True}
    bindings.append(binding)
    request=root/'Cache/Requests.lean';infra=root/'Cache/Infra.lean'
    bases=['https://lakecache.blob.core.windows.net/mathlib4'] if version=='4.30.0-rc2' else [
        'https://lakecache.blob.core.windows.net/mathlib4-master','https://lakecache.blob.core.windows.net/mathlib4']
    remote.append({'version':version,'repository':'leanprover-community/mathlib4','mathlib_pin':pin,
        'cached_filename_is_preserved_official_CacheHashing_key':True,
        'candidate_canonical_default_refetch_URL_templates':[base+'/f/{official_cache_key_filename}.ltar' for base in bases],
        'filename_substitution':'For every manifest row use the 16 hexadecimal basename without .ltar as official_cache_key_filename. The current per-file SHA-256 in that same preserved row is the re-fetch byte-integrity check.',
        'URL_policy_primary_source':ref(request),'container_policy_primary_source':ref(infra) if infra.exists() else None,
        'URL_qualification':'These are source-derived official default recovery addresses, not newly observed original HTTP telemetry. The pinned official get- route remains the authoritative resolver if a container/URL override was configured.',
        'refetch_recipe':'Keep the exact runtime/dependency source and recorded original official Cache.Hashing plan. Set MATHLIB_CACHE_DIR to the exact same task version cache directory and run the official Cache tool get- (download only), then verify each restored archive SHA-256 against the preserved candidate manifest before any use. Do not alter source pins or unpack into scientific sources.'})
policy={'status':'PREPARED_ONLY_ALL25906_TASK_BINARY_CACHE_HOUSEKEEPING_NOT_EXECUTED',
    'prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'assessment':ref(assessment),'candidate_manifest':ref(manifest),
    'exact_cache_root':str(BASE/'download-cache'),'exact_versions':list(pins),'candidate_count':25906,
    'candidate_logical_bytes':1312369944,'all_candidates_are_single_link_task_owned_mapped_official_binary_downloads':all(r['observed_link_count']==1 for r in rows),
    'preserved_provider_bindings':bindings,'actual_installed_provider_artifact_presence':presence,
    'remote_content_key_and_refetch_recipe_for_every_row':remote,
    'root_instruction_scope':'Prepare all25,906 .ltar cache download removals only; actual removal remains forbidden until concrete root helper/manifest approval.',
    'explicit_never_targets':['Entrant scientific-source ZIPs/tars','Actual extracted Lean runtimes','Pinned official Mathlib/package source trees','Installed official .olean/private/server/ilean/ir providers','Authored Lean proof sources','Own proof compilation outputs','Existing immutable plans/receipts/profiles/source-hash manifests'],
    'historical_archive_exists_policy':'Do not edit archive_exists flags in historical cache plans/profiles. A future exact cleanup receipt states that binary download files are now absent while historical snapshots and extracted provider validation remain preserved.',
    'current_verifier_dependency_contract':'Root reviewed current DMS/FC verifiers: they bind the official cache PASS receipt and exact installed provider identities, not current downloaded .ltar existence. This housekeeping is not a new proof or new official-provider qualification.',
    'all_input_identity_and_hash_checks_required_before_any_remove':True,'no_active_cache_reader_writer_extractor_required':True,
    'each_remove_is_single_file_native_DeleteFileW_no_recursive_or_shell_string_operation':True,
    'source_runtime_or_provider_rewrite_allowed':False,'directory_removal_allowed':False,
    'execute_approval_schema':{'approved':True,'purpose':'TASK_OWNED_OFFICIAL_BINARY_LTAR_CACHE_ONLY_HOUSEKEEPING',
        'approved_helper_sha256':'EXACT_PREPARED_HELPER_SHA_REQUIRED','approved_policy_sha256':'EXACT_POLICY_SHA_REQUIRED',
        'approved_manifest_sha256':sha(manifest),'approved_archive_count':25906,
        'no_active_cache_writer_or_extractor_required':True,'preserve_all_source_runtime_compiled_provider_and_proof_outputs':True},
    'known_recovery_limit':'Preserved exact manifests and official download recipes support network recovery, not an offline guarantee that remote archives remain available.'}
target=OUT/'all-cache-housekeeping-policy.json'
with target.open('x',encoding='utf8',newline='\n') as stream:json.dump(policy,stream,ensure_ascii=False,indent=2);stream.write('\n')
packet={'status':'CONCRETE_ALL25906_CACHE_ONLY_HELPER_AND_POLICY_PREPARED_NOT_INVOKED',
    'prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'policy':ref(target),'helper':ref(helper),
    'candidate_manifest':ref(manifest),'assessment':ref(assessment),'candidate_count':25906,'candidate_reported_native_bytes':1312369944,
    'preserved_provider_artifact_presence':presence,'helper_syntax_ast_valid':True,
    'preflight_command_NOT_EXECUTED':['C:/Users/Propietario/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe','-X','utf8',str(helper),'--mode','preflight'],
    'execute_command_NOT_EXECUTED':['C:/Users/Propietario/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe','-X','utf8',str(helper),'--mode','execute','--approval','EXACT_ROOT_REVIEWED_APPROVAL_RECORD'],
    'files_deleted':0,'housekeeping_helper_invocations':0,'Lean_or_download_invocations':0,
    'existing_source_runtime_dependency_output_plan_receipt_or_PDF_changes':False}
out=OUT/'all-cache-housekeeping-root-review-preparation.json'
with out.open('x',encoding='utf8',newline='\n') as stream:json.dump(packet,stream,ensure_ascii=False,indent=2);stream.write('\n')
print(json.dumps({'packet':ref(out),'policy':ref(target),'helper':ref(helper),'presence':presence,'deleted':0},indent=2))
