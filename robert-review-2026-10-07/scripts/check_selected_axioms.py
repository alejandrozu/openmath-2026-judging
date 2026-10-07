"""Compile exact selected axiom/type outputs. Kernel axiom allowlist is mandatory."""
from pathlib import Path
import json,re,subprocess,hashlib,sys
ROOT=Path(__file__).resolve().parents[1]
EXPECTED=json.loads((ROOT/'proofs/selected-endpoints.json').read_text(encoding='utf8'))
allowed={'propext','Classical.choice','Quot.sound'}
result=subprocess.run(['lake','env','lean','SelectedAxiomAudit.lean'],cwd=ROOT/'lean',capture_output=True,text=True,encoding='utf8')
log=ROOT/'proofs/live-selected-axiom-output.txt';log.write_text(result.stdout+'\n'+result.stderr,encoding='utf8')
assert result.returncode==0, 'Lean did not finish successfully; see live-selected-axiom-output.txt'
actual={}
for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",result.stdout):
    axioms={x.strip() for x in raw.split(',') if x.strip()}
    assert axioms<=allowed,(name,axioms-allowed)
    assert name not in actual,('Repeated endpoint',name)
    actual[name]=sorted(axioms)
for name in re.findall(r"'([^']+)' does not depend on any axioms",result.stdout):
    assert name not in actual
    actual[name]=[]
assert set(actual)=={x['endpoint'] for x in EXPECTED},('Coverage mismatch',len(actual),len(EXPECTED))
receipt={'state':'PASS','count':len(actual),'selected_endpoints':actual,'output_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
 'scope':'Selected endpoints only. Admitted general/asymptotic Target statements are explicitly excluded.'}
(ROOT/'proofs/live-selected-verification.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
print(json.dumps({'state':'PASS','selected_endpoints':len(actual)}))
