"""Independent fresh build driven by the module list in REPLAY_PROJECTS.json (used for Focus_Evidence projects):
copies each listed source to its module path, writes a fresh lakefile pinned to the recorded Mathlib, builds the
audit imports and prints axioms of every endpoint. Paths at the top are those of the audit machine."""
import json, subprocess, os, shutil, sys
SRC='/tmp/claude-0/packs/e02/Math_Competition_Completed_Results_Submission'
plan={p['id']:p for p in json.load(open(SRC+'/Reproduction_Tools/REPLAY_PROJECTS.json'))}
PK={'4.33.1':'/tmp/claude-0/pk433','4.34.1':'/tmp/claude-0/build/erdos21/.lake/packages'}
MAN={'4.33.1':'/tmp/claude-0/build/a100475/lake-manifest.json','4.34.1':'/tmp/claude-0/build/erdos21/lake-manifest.json'}
env=dict(os.environ, PATH=os.path.expanduser('~/.elan/bin')+':'+os.environ['PATH'])
for pid in sys.argv[1:]:
    p=plan[pid]; v=p['lean_version']; d='/tmp/claude-0/build2/'+pid
    shutil.rmtree(d, ignore_errors=True); os.makedirs(d+'/.lake')
    os.symlink(PK[v], d+'/.lake/packages')
    man=json.load(open(MAN[v])); man['packagesDir']='.lake/packages'
    json.dump(man, open(d+'/lake-manifest.json','w'), indent=1)
    open(d+'/lean-toolchain','w').write('leanprover/lean4:v'+v+'\n')
    mods=[]
    for m in p['modules']:
        dst=d+'/'+m['module']+'.lean'; os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy(SRC+'/'+m['source'], dst); mods.append(m['module'].replace('/','.'))
    rev=p['package_pins'].get('mathlib')
    opts=''.join(f'{k} = {json.dumps(v2) if not isinstance(v2,bool) else str(v2).lower()}\n' for k,v2 in p.get('lean_options',{}).items())
    open(d+'/lakefile.toml','w').write(f'name = "{man["name"]}"\n\n[leanOptions]\n{opts}\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\nrev = "{rev}"\n\n[[lean_lib]]\nname = "Fresh"\nroots = {json.dumps(mods)}\n')
    log=open(d+'/fresh-build.log','w')
    au=p['audit_units']; imports=sorted({i for u in au for i in u['imports']})
    r=subprocess.run(['lake','build']+imports, cwd=d, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=7200)
    log.write(f'\nBUILD_EXIT {r.returncode}\n'); log.flush()
    eps=[e for u in au for e in u['endpoints']]
    open(d+'/FreshAudit.lean','w').write('\n'.join('import '+i for i in imports)+'\n\n'+'\n'.join('#print axioms '+e for e in eps)+'\n')
    r2=subprocess.run(['lake','env','lean','FreshAudit.lean'], cwd=d, env=env, capture_output=True, text=True, timeout=3600)
    log.write('AUDIT_EXIT %d\n%s\n%s\n'%(r2.returncode, r2.stdout, r2.stderr)); log.close()
    print(pid, 'build', r.returncode, 'audit', r2.returncode, flush=True)
