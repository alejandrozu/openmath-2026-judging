from pathlib import Path
import json,zipfile,re,ast,hashlib,datetime
from fractions import Fraction
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging';inp=json.loads((ROOT/'review/chandra-original-check-input.json').read_text(encoding='utf8'));report=[]
for path,ns in [('solutions/support_138/solution.json','Scheme138'),('solutions/support_138_gauged/solution.json','Scheme138Gauged'),('solutions/core1809_support_143/solution.json','Scheme143Core1809')]:
 raw=json.loads(inp[path]);m={k:[[Fraction(v[0],v[1]) if isinstance(v,list) else Fraction(v) for v in row] for row in raw[k]] for k in ['u','v','w']};assert all(len(m[k])==23 and all(len(row)==9 for row in m[k]) for k in m)
 mismatches=[];gf2=[]
 for a in range(9):
  for b in range(9):
   for cc in range(9):
    expected=int(b//3==a%3 and cc//3==b%3 and cc%3==a//3)
    actual=sum(m['u'][t][a]*m['v'][t][b]*m['w'][t][cc] for t in range(23))
    if actual!=expected:mismatches.append([a,b,cc,str(actual),expected])
    parity=sum(int(m['u'][t][a]!=0 and m['v'][t][b]!=0 and m['w'][t][cc]!=0) for t in range(23))%2
    if parity!=expected:gf2.append([a,b,cc,parity,expected])
 lean=inp['lean/MM3/'+ns+'.lean'];scales={k:int(re.search(r'def s'+k+r'\s*:\s*Int\s*:=\s*(\d+)',lean).group(1)) for k in m}
 identical=True
 for k in m:
  text=re.search(r'def '+k+r'\s*:.*?:=\s*(\[.*?\n\])',lean,re.S).group(1);ints=ast.literal_eval(text.replace('(','').replace(')',''))
  identical=identical and ints==[[int(v*scales[k]) for v in row] for row in m[k]] and all((v*scales[k]).denominator==1 for row in m[k] for v in row)
 support=sum(v!=0 for mat in m.values() for row in mat for v in row);assert not mismatches and identical
 report.append({'path':path,'rank_terms':23,'support':support,'identities_checked':729,'mismatches':mismatches,'Lean_scaled_data_identical':identical,'scale_factors':scales,'GF2_same_support_pattern_mismatch_count':len(gf2),'GF2_first_counterexample':gf2[:1]})
out={'checked_at':datetime.datetime.now().astimezone().isoformat(),'method':'Independent newly written exact Fraction checker plus static data correspondence; no contestant code or Lean compiler executed','reports':report,'result':'All3 complete tensors compute the declared3x3 multiplication tensor; integer-scaled Lean literals match originals exactly','remaining':'Fresh kernel closure, priority/independence/receipt and non-finite structural-family claims remain separate checks'}
(ROOT/'review/chandra-independent-tensor-check.json').write_text(json.dumps(out,indent=2),encoding='utf8');print(json.dumps(out))
idx=json.loads((ROOT/'review/chandra-original-source-index.json').read_text(encoding='utf8'));z=zipfile.ZipFile(ROOT/idx['archive']);prefix=z.namelist()[0].split('/')[0]+'/'
for path in ['kaggle/analysis/REPORT_138_structure.md','results/round_2026-09-29b/lit_138_check.md','lean/README.md']:
 txt=z.read(prefix+path).decode('utf8',errors='replace');(ROOT/'review'/('chandra-'+Path(path).stem+'.txt')).write_text(txt,encoding='utf8')
 print(path,txt[:2500])
