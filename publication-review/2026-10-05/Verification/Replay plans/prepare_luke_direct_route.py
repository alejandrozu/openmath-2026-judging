"""Prepare a byte-identical, source-only Luke replay through direct Lean CLI.

No proof is invoked and no dependency source or dependency cache is changed.
"""
from pathlib import Path
import hashlib,json,os,shutil

base=Path(__file__).resolve().parent
original=base/'builds/luke-k4-ramsey-current'
dest=base/'builds/luke-k4-ramsey-current-direct'
original_plan=json.loads((original/'build-plan.json').read_text(encoding='utf8'))
manifest=json.loads((original/'lake-manifest.json').read_text(encoding='utf8'))
dest.mkdir(parents=True,exist_ok=True)
assert not list((dest/'.lake/build').glob('lib/lean/**/*.olean')), 'The direct route must start cold'
plan={k:v for k,v in original_plan.items() if k!='modules'}
plan.update({'id':'luke-k4-ramsey-current','reproduction_route_id':'luke-k4-ramsey-current-direct','source_dir':str(dest),'modules':[],
 'route':'Direct Lean CLI operational adapter, all source bytes unchanged',
 'authored_lake_policy':'K4Ramsey and Tests precompileModules=true; original Lake policy remains preserved in the separate prepared native-Lake route.',
 'operational_difference':'Direct Lean -o/-i is used to avoid materializing the entire Mathlib native shared-library object closure. Native tactics must execute and pass through Lean; no theorem or assumption is edited.',
 'dependency_identity_root':str(original),
 'dependency_library_paths':[str((original/manifest['packagesDir']/p['name']/'.lake/build/lib/lean').resolve()) for p in manifest['packages']]})
for m in original_plan['modules']:
 source=Path(m['source'])
 assert hashlib.sha256(source.read_bytes()).hexdigest()==m['sha256']
 relative=Path(m['file']).relative_to(original)
 target=dest/relative;target.parent.mkdir(parents=True,exist_ok=True)
 shutil.copy2(source,target)
 assert hashlib.sha256(target.read_bytes()).hexdigest()==m['sha256']
 plan['modules'].append({**m,'file':str(target),'frozen_source':str(source)})
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(original/name,dest/name)
plan['source_file_count']=len(plan['modules'])
plan['semantic_options']='No project-wide semantic Lean options are declared in the frozen lakefile; file-local options remain byte-identical. The adapter records its explicit CLI resource worker flag, default -j1; authored WeightedCandidate -j1 remains -j1.'
p=dest/'build-plan.json';tmp=p.with_suffix('.json.tmp')
with tmp.open('w',encoding='utf8') as f:
 json.dump(plan,f,indent=2);f.flush();os.fsync(f.fileno())
os.replace(tmp,p)
print('Prepared',len(plan['modules']),'byte-identical source files; no proof invocation')
