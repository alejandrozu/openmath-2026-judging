"""Portable selected-axiom reproduction. It never publishes or modifies sources."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,re,subprocess,sys
B=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    rows=json.loads((B/'proofs/source-manifest.json').read_text(encoding='utf-8'))
    for row in rows:assert sha(B/row['path'])==row['sha256'],row['module']
    expected=json.loads((B/'proofs/selected-endpoints.json').read_text(encoding='utf-8'))
    allowed={'propext','Classical.choice','Quot.sound'}
    env=dict(os.environ);env['LEAN_NUM_THREADS']='1'
    command=['lake','env','lean','-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','SelectedAxiomAudit.lean']
    result=subprocess.run(command,cwd=B/'lean',env=env,capture_output=True,text=True,encoding='utf-8')
    actual={}
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",result.stdout):
        axioms=sorted({x.strip() for x in raw.split(',') if x.strip()})
        assert name not in actual
        actual[name]=axioms
    for name in re.findall(r"'([^']+)' does not depend on any axioms",result.stdout):
        assert name not in actual;actual[name]=[]
    success=result.returncode==0 and set(actual)=={x['endpoint'] for x in expected} and all(set(x)<=allowed for x in actual.values())
    for row in rows:assert sha(B/row['path'])==row['sha256']
    timestamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');out=B/'reproduction-evidence'/timestamp;out.mkdir(parents=True,exist_ok=False)
    (out/'stdout.txt').write_text(result.stdout,encoding='utf-8');(out/'stderr.txt').write_text(result.stderr,encoding='utf-8')
    receipt={'status':'PASS_EXACT_SELECTED_SCOPE' if success else 'UNQUALIFIED','checked_utc':datetime.now(timezone.utc).isoformat(),'actual_exit_code':result.returncode,'command':command,'unique_prints':len(actual),'selected_axioms':actual,'stdout_sha256':sha(out/'stdout.txt'),'stderr_sha256':sha(out/'stderr.txt'),'scope':'Universal CharZero tensor identity plus support<=138; exact support=138 and specialization remain outside this selected reproduction.'}
    (out/'actual-reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':receipt['status'],'output':str(out),'unique_prints':len(actual)}))
    raise SystemExit(0 if success else 1)
if __name__=='__main__':main()
