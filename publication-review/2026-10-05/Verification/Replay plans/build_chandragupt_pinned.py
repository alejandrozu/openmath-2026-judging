"""Fresh pinned Lean compilation of every archived Chandragupt Lean module."""
from pathlib import Path
import zipfile,re,subprocess,os,json,hashlib,time
BASE=Path(__file__).resolve().parent
ZP=next((BASE.parents[1]/'judging_audit/repository/OpenMath-Judging/contestants/E04/13-archives').glob('*.zip'))
z=zipfile.ZipFile(ZP);prefix=z.namelist()[0].split('/')[0]+'/lean/'
dest=BASE/'builds/chandragupt';dest.mkdir(parents=True,exist_ok=True)
subprocess.run(['compact.exe','/C',str(dest)],capture_output=True,check=True)
files=['MM3/Brent.lean','MM3/Scheme138.lean','MM3/Scheme138Gauged.lean','MM3/Scheme139Exotic.lean','MM3/Scheme143Core1809.lean','MM3/Certificates.lean','MM3.lean']
assert set(files)=={n.removeprefix(prefix) for n in z.namelist() if n.startswith(prefix) and n.endswith('.lean')}
hashes={}
for n in files:
 raw=z.read(prefix+n);txt=raw.decode('utf8');stripped=re.sub(r'/\-.*?\-/','',txt,flags=re.S)
 assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|run_meta)\b|#eval|#run|\bIO\.',stripped),n
 p=dest/n;p.parent.mkdir(exist_ok=True);p.write_bytes(raw);hashes[n]=hashlib.sha256(raw).hexdigest()
endpoints=['MM3.'+n for n in ['scheme138_valid','scheme138_identities','scheme138_support','scheme138Gauged_valid','scheme138Gauged_identities','scheme138Gauged_support','scheme139Exotic_valid','scheme139Exotic_identities','scheme139Exotic_support','scheme143Core1809_valid','scheme143Core1809_identities','scheme143Core1809_support']]
(dest/'FreshAudit.lean').write_text('import MM3.Certificates\n'+''.join('#print axioms '+e+'\n' for e in endpoints))
lean=BASE/'runtimes/lean-4.34.1-windows/bin/lean.exe';env=dict(os.environ);env['LEAN_PATH']=str(dest)
out={'project':'chandragupt','commit':'479c2416b6261ee841052eef4881df0e40054f3f','compiler':str(lean),'version':subprocess.run([str(lean),'--version'],capture_output=True,text=True).stdout.strip(),'scope':'Every archived Lean module freshly compiled under pinned4.34.1; no submitted compiled artifact used','source_sha256':hashes,'endpoints':endpoints,'builds':[],'status':'RUNNING'}
rp=BASE/'chandragupt-pinned-build.json'
for n in files+['FreshAudit.lean']:
 start=time.monotonic();args=[str(lean),'-DmaxRecDepth=100000','-DmaxHeartbeats=0','-o',str(Path(n).with_suffix('.olean')),n]
 p=subprocess.run(args,cwd=dest,env=env,capture_output=True,text=True,encoding='utf8',timeout=600)
 out['builds'].append({'module':n,'command':args,'exit':p.returncode,'seconds':round(time.monotonic()-start,2),'stdout':p.stdout,'stderr':p.stderr})
 rp.write_text(json.dumps(out,indent=2));print(n,p.returncode,out['builds'][-1]['seconds'],flush=True)
 if p.returncode:out['status']='FAIL';break
else:out['status']='PASS'
out['compiled_bytes']=sum(p.stat().st_size for p in dest.rglob('*') if p.is_file());rp.write_text(json.dumps(out,indent=2))
print(out['status'],out['builds'][-1]['stdout'],flush=True)
