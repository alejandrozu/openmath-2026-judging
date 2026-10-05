"""Independent executable metadata recheck; no Lean/compiler or artifact writes."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
from lean_imports import read_imports,stripped
BASE=Path(__file__).resolve().parent
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def read_bound(name,digest):
    p=BASE/name;assert sha(p)==digest,(name,'inputSHA');return json.loads(p.read_text(encoding='utf8'))
started=time.monotonic();errors=[];counts={'source183':0,'all200_source_headers':0,'official_sources':0,'official_artifacts':0,'custom_closed_sources':0,'per_source_exposures_rederived':0}
def failure(kind,detail):
    if len(errors)<30:errors.append({'kind':kind,'detail':detail})
def assert_check(condition,kind,detail):
    if not condition:failure(kind,detail)
scope=read_bound('original-E65-tactic-aware-resource-scope-20261005.json','47ed60dae2f8c65df991072ece7152e80f5594f79f54fd51d5e88d5e31b738ab')
prep=read_bound('original-E65-source-replay-preparation-20261005.json','96f74d38af628c8763632c3a0869d7fa2404796ecf66de70fd13d6b0652e1e06')
graph=read_bound('original-E65-granular189-prerequisite-exposure-graph-20261005.json','73adf962348c8ab1debfb2efd04fbfc39c82da25f2ebe2cb88614c0c0300c296')
manifest=read_bound('original-E65-granular189-official-source-artifact-manifest-20261005.json','70891fd7cccd675e798a251777feb1c31382db08c83d2575106d5e920cecbdd3')
plan=read_bound('builds/sundai-erdos3-original-image-source/build-plan.json','0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15')
assert sha(BASE/'lean_imports.py')=='4e0387c48c2a857fd1e69c872cbbd9c66b9741cfb661ef8a3e670bc7cd0ab8aa'
safe=set(scope['truly_no_Mathlib_or_Tactic_custom_closed_subset']);whole=set(scope['future_whole_resource_sources'])
assert len(safe)==183 and len(whole)==16
source_rows={r['module']:r for r in plan['modules']};assert len(source_rows)==200
custom_imports={}
for name,row in source_rows.items():
    current=read_imports(row['file']);counts['all200_source_headers']+=1
    assert_check(current==graph['all200_custom_imports'][name],'CUSTOM_HEADER_CHANGED',name)
    custom_imports[name]=current
    if name in safe:
        assert_check(sha(row['file'])==row['sha256'],'CUSTOM_SOURCE_SHA_CHANGED',name);counts['source183']+=1
        assert_check(row['lean_options']=={'pp.unicode.fun':True,'autoImplicit':False,'relaxedAutoImplicit':False},'FC_SEMANTIC_OPTIONS_CHANGED',name)
custom_memo={}
def custom_closure(name):
    if name in custom_memo:return custom_memo[name]
    found={name}
    for d in custom_imports[name]:
        if d in source_rows:found.update(custom_closure(d))
    custom_memo[name]=found;return found
for name in safe:
    assert_check(custom_closure(name)<=safe,'DEFERRED_CUSTOM_DEPENDENCY',name);counts['custom_closed_sources']+=1
official={r['module']:r for r in manifest};assert len(official)==6223
safe_official=set(scope['no_Tactic_official_union_modules']);assert len(safe_official)==6075
assert_check('Mathlib' not in safe_official and 'Mathlib.Tactic' not in safe_official,'WHOLE_EXPOSED_IN_GRANULAR_UNION','Mathlib/Mathlib.Tactic')
for number,name in enumerate(sorted(safe_official),1):
    row=official[name];file=Path(row['source_file'])
    assert_check(sha(file)==row['source_sha256'] and file.stat().st_size==row['source_bytes'],'OFFICIAL_SOURCE_SHA_CHANGED',name)
    imports=list(dict.fromkeys(d for d in read_imports(file) if d!='all'))
    code=stripped(file.read_text(encoding='utf8'));prelude=bool(re.search(r'^\s*prelude\s*$',code,re.M))
    implicit=name!='Init' and not prelude and 'Init' not in imports
    effective=imports+(['Init'] if implicit else [])
    assert_check(imports==row['literal_source_imports'] and effective==row['effective_import_dependencies'],'OFFICIAL_EFFECTIVE_IMPORT_CHANGED',name)
    assert_check(set(effective)<=safe_official,'OFFICIAL_PREREQUISITE_OUTSIDE_GRANULAR_UNION',name)
    counts['official_sources']+=1
    for artifact in row['official_artifacts']:
        fileout=Path(artifact['file'])
        assert_check(fileout.is_file() and fileout.stat().st_size==artifact['bytes'] and sha(fileout)==artifact['sha256'],'OFFICIAL_ARTIFACT_CHANGED',name+' / '+fileout.name)
        counts['official_artifacts']+=1
    if number%500==0:print('ROOT_NO_TACTIC183_METADATA_RECHECK_UNITS',number,flush=True)
official_memo={}
def exposure(name):
    if name in official_memo:return official_memo[name]
    found={name}
    for dep in official[name]['effective_import_dependencies']:found.update(exposure(dep))
    official_memo[name]=found;return found
graph_rows={r['module']:r for r in graph['sources']};union=set();orders=set()
for name in scope['truly_no_Tactic_topological_order']:
    direct=set()
    for c in custom_closure(name):direct.update(d for d in custom_imports[c] if d not in source_rows)
    direct.add('Init');found=set()
    for d in direct:found.update(exposure(d))
    assert_check(found==set(graph_rows[name]['exact_effective_official_exposure_modules']),'PER_SOURCE_EXPOSURE_CHANGED',name)
    assert_check('Mathlib' not in found and 'Mathlib.Tactic' not in found,'PER_SOURCE_WHOLE_EXPOSURE',name)
    assert_check(set(d for d in custom_imports[name] if d in source_rows)<=orders,'TOPOLOGICAL_ORDER_INVALID',name)
    orders.add(name);union.update(found);counts['per_source_exposures_rederived']+=1
assert_check(union==safe_official and orders==safe,'GRANULAR_EXPOSURE_UNION_OR_ORDER_CHANGED','183/6075')
assert counts=={'source183':183,'all200_source_headers':200,'official_sources':6075,'official_artifacts':30375,'custom_closed_sources':183,'per_source_exposures_rederived':183},counts
runtime=BASE/'runtimes/lean-4.33.1-windows/bin/lean.exe'
assert_check(sha(runtime)==prep['compiler_binary_sha256'],'COMPILER_BINARY_CHANGED','Lean4.33.1')
for package in prep['exact_original_nine_packages']:
    actual=subprocess.run(['git','rev-parse','HEAD'],cwd=package['prepared_source_path'],capture_output=True,text=True,check=True).stdout.strip()
    assert_check(actual==package['original_manifest_rev'],'DEPENDENCY_GIT_PIN_CHANGED',package['name'])
result={'status':'ROOT_READ_ONLY_EXACT_NO_MATHLIB_OR_TACTIC183_SOURCE_PROVIDER_RECHECK_PASS' if not errors else 'ROOT_READ_ONLY_METADATA_RECHECK_MISMATCH',
 'started_and_finished_as_metadata_only':True,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'seconds':round(time.monotonic()-started,3),'checked_counts':counts,'bounded_errors_first30':errors,
 'scope_sha256':'47ed60dae2f8c65df991072ece7152e80f5594f79f54fd51d5e88d5e31b738ab',
 'manifest_sha256':'70891fd7cccd675e798a251777feb1c31382db08c83d2575106d5e920cecbdd3',
 'source_plan_sha256':'0d140b36c59231a9eaf79a2f6277355d0b4cc08b815e5d817df54c370dcfbf15',
 'recheck_helper_sha256':sha(__file__),'compiler_binary_sha256':prep['compiler_binary_sha256'],
 'whole16_source_or_audit_invocation_authorized':False,'Std_external_source_and14prints_accepted':False,
 'sources_or_adapters_changed':False,'outputs_copied_linked_aliased':False,'Lean_or_compiler_invoked':False,
 'qualification':'Successful metadata checks authenticate the exact proposed closed183 source/provider scope. They do not establish source elaboration or selected theorem/axiom outcomes, and do not admit whole source compilation.'}
target=BASE/'original-E65-root-noTactic183-source-provider-recheck-20261005.json';temp=target.with_suffix('.json.tmp')
temp.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8');os.replace(temp,target)
print(json.dumps({'status':result['status'],'checked_counts':counts,'errors_first30':errors,'seconds':result['seconds'],
 'result_file':str(target),'result_sha256':sha(target),'Lean_invoked':False},indent=2))
