"""Independent fresh build of Sakana project sources from Reproduction_Sources/<project> with the pinned
Lean toolchain and a Mathlib cache obtained by `lake exe cache get` (no entrant-supplied .olean files),
followed by an axiom audit of the endpoints listed in Reproduction_Tools/REPLAY_PROJECTS.json.
Usage: python3 fresh_build_reproduction_sources.py <packages_dir> <project> [...]"""
import json, subprocess, os, shutil, sys
SRC='/tmp/claude-0/packs/e02/Math_Competition_Completed_Results_Submission'
plan={p['id']:p for p in json.load(open(SRC+'/Reproduction_Tools/REPLAY_PROJECTS.json'))}
env=dict(os.environ, PATH=os.path.expanduser('~/.elan/bin')+':'+os.environ['PATH'])
pk=sys.argv[1]; projs=sys.argv[2:]
for p in projs:
    d='/tmp/claude-0/build/'+p
    shutil.rmtree(d, ignore_errors=True); shutil.copytree(SRC+'/Reproduction_Sources/'+p, d)
    if not os.path.exists(d+'/lake-manifest.json') and os.path.exists(d+'/replay-receipt/lake-manifest.json'):
        shutil.copy(d+'/replay-receipt/lake-manifest.json', d)
    os.makedirs(d+'/.lake', exist_ok=True); os.symlink(pk, d+'/.lake/packages')
    log=open(d+'/fresh-build.log','w')
    au=plan[p]['audit_units']
    imports=sorted({i for u in au for i in u['imports']})
    r=subprocess.run(['lake','build']+imports, cwd=d, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=5400)
    log.write(f'\nBUILD_EXIT {r.returncode}\n'); log.flush()
    eps=[e for u in au for e in u['endpoints']]
    open(d+'/FreshAudit.lean','w').write('\n'.join('import '+i for i in imports)+'\n\n'+'\n'.join('#print axioms '+e for e in eps)+'\n')
    r2=subprocess.run(['lake','env','lean','FreshAudit.lean'], cwd=d, env=env, capture_output=True, text=True, timeout=1800)
    log.write('AUDIT_EXIT %d\n%s\n%s\n'%(r2.returncode, r2.stdout, r2.stderr)); log.close()
    print(p, 'build', r.returncode, 'audit', r2.returncode, flush=True)
