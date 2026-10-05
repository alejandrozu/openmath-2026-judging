"""Static source/dependency identity and operational-footprint preflight."""
from pathlib import Path
import hashlib,json,os,subprocess,datetime
base=Path(__file__).resolve().parent
dest=base/'builds/luke-k4-ramsey-current-direct'
plan=json.loads((dest/'build-plan.json').read_text(encoding='utf8'))
manifest=json.loads((dest/'lake-manifest.json').read_text(encoding='utf8'))
original=Path(plan['dependency_identity_root'])
sources=[]
for m in plan['modules']:
 sources.append({'module':m['module'],'source_sha256':m['sha256'],
  'frozen_match':hashlib.sha256(Path(m['frozen_source']).read_bytes()).hexdigest()==m['sha256'],
  'direct_staged_match':hashlib.sha256(Path(m['file']).read_bytes()).hexdigest()==m['sha256']})
deps=[]
for p in manifest['packages']:
 path=original/manifest['packagesDir']/p['name']
 head=subprocess.run(['git','-C',str(path),'rev-parse','HEAD'],capture_output=True,text=True,encoding='utf8')
 url=subprocess.run(['git','-C',str(path),'remote','get-url','origin'],capture_output=True,text=True,encoding='utf8')
 build=(path/'.lake/build').resolve()
 native=[f for f in build.rglob('*') if f.is_file() and f.name.endswith(('.c.o','.cpp.o','.dll','.a','.lib'))]
 cfiles=[f for f in build.rglob('*.c') if f.is_file()]
 deps.append({'name':p['name'],'HEAD':head.stdout.strip(),'origin':url.stdout.strip(),
  'identity_matches_frozen_manifest':head.returncode==0 and url.returncode==0 and head.stdout.strip()==p['rev'] and url.stdout.strip()==p['url'],
  'cached_C_file_count':len(cfiles),'cached_C_total_bytes':sum(f.stat().st_size for f in cfiles),
  'native_operational_object_count':len(native),'native_operational_total_bytes':sum(f.stat().st_size for f in native)})
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Static preflight only; no Lean proof or Lake build invoked',
 'family_project_id':plan['id'],'route_id':plan['reproduction_route_id'],'source_commit':plan['commit'],
 'source_files':sources,'all_51_source_bytes_match':len(sources)==51 and all(v['frozen_match'] and v['direct_staged_match'] for v in sources),
 'dependencies':deps,'all_9_dependency_identities_match':len(deps)==9 and all(d['identity_matches_frozen_manifest'] for d in deps),
 'custom_proof_outputs':len(list((dest/'.lake/build').glob('lib/lean/**/*.olean'))),
 'native_Lake_footprint_prediction':'Pinned Lake fetchImportLibs fetches the whole external library shared target for precompiled custom imports; missing Mathlib C object/shared outputs could therefore be materialized in the dependency junction. Object size is platform-dependent and is not inferred solely from C source size.',
 'direct_adapter_footprint_prediction':'All explicit compiler outputs are confined to the separate custom build/lib/lean directory. No whole-library native target is requested; before/after external native-object metadata is recorded to verify the observed operational boundary.',
 'pinned_Lake_source_reference':'Lean 4.34.1 source Lake/Build/Module.lean lines 133–142 at compiler commit 5045d0056413266e57c625dcd7c365b10e377c52'}
result['status']='STATIC_PREFLIGHT_PASS' if result['all_51_source_bytes_match'] and result['all_9_dependency_identities_match'] and result['custom_proof_outputs']==0 else 'STATIC_PREFLIGHT_REVIEW_REQUIRED'
p=base/'luke-direct-static-preflight.json';tmp=p.with_suffix('.json.tmp')
with tmp.open('w',encoding='utf8') as f:json.dump(result,f,indent=2);f.flush();os.fsync(f.fileno())
os.replace(tmp,p)
print(result['status'],len(sources),'sources;',len(deps),'dependency identities; native cached objects',sum(d['native_operational_object_count'] for d in deps))
