from pathlib import Path
import json,zipfile,datetime
from fractions import Fraction
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging';idx=json.loads((ROOT/'review/chandra-original-source-index.json').read_text(encoding='utf8'));z=zipfile.ZipFile(ROOT/idx['archive']);prefix=z.namelist()[0].split('/')[0]+'/'
obj=json.loads(z.read(prefix+'kaggle/analysis/family_rational.json'));m={k:[[None for _ in range(9)] for _ in range(23)] for k in ['u','v','w']};zeros=set();poles=set()
def trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def mul(a,b):
 out=[Fraction(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return trim(out)
def power(p,n):
 out=[Fraction(1)]
 for _ in range(n):out=mul(out,p)
 return out
def evaluate(p,x):return sum(c*Fraction(x)**i for i,c in enumerate(p))
def factor(p):
 p=trim(p[:]);counts=[]
 for root in [0,-2]:
  count=0
  while len(p)>1 and evaluate(p,root)==0:
   q=[Fraction(0)]*(len(p)-1);q[-1]=p[-1]
   for i in range(len(q)-2,-1,-1):q[i]=p[i+1]+root*q[i+1]
   assert p[0]+root*q[0]==0;p=trim(q);count+=1
  counts.append(count)
 assert len(p)==1,'Unexpected polynomial root/factor scope'
 return counts[0],counts[1],p[0]
for key,(num,den) in obj.items():
 k,t,a=key.split(',');t=int(t);a=int(a)
 n=[Fraction(v) for v in num];v=[Fraction(x) for x in den];da,db,dc=factor(v);na,nb,nc=factor(n)
 m[k][t][a]=([x/dc for x in n],da,db)
 if da:poles.add('0')
 if db:poles.add('-2')
 if na:zeros.add('0')
 if nb:zeros.add('-2')
A=3*max(v[1] for mat in m.values() for row in mat for v in row if v);B=3*max(v[2] for mat in m.values() for row in mat for v in row if v)
common=mul(power([0,1],A),power([2,1],B))
tensor={}
for t in range(23):
 for a in range(9):
  if m['u'][t][a] is None:continue
  for b in range(9):
   if m['v'][t][b] is None:continue
   for c in range(9):
    if m['w'][t][c] is None:continue
    vals=[m[k][t][i] for k,i in [('u',a),('v',b),('w',c)]];poly=[Fraction(1)]
    for v in vals:poly=mul(poly,v[0])
    poly=mul(poly,mul(power([0,1],A-sum(v[1] for v in vals)),power([2,1],B-sum(v[2] for v in vals))))
    key=(a,b,c);tensor[key]=add(tensor.get(key,[Fraction(0)]),poly)
failed=[]
for a in range(9):
 for b in range(9):
  for c in range(9):
   target=int(b//3==a%3 and c//3==b%3 and c%3==a//3)
   if tensor.get((a,b,c),[Fraction(0)])!=(common if target else [Fraction(0)]):failed.append([a,b,c])
assert not failed
original=json.loads(z.read(prefix+'solutions/support_138/solution.json'))
def at_minus1(v):return Fraction(0) if v is None else evaluate(v[0],-1)/((-1)**v[1])
match=all(at_minus1(m[k][t][a])==(Fraction(*original[k][t][a]) if isinstance(original[k][t][a],list) else Fraction(original[k][t][a])) for k in m for t in range(23) for a in range(9))
assert match;assert zeros<=poles
result={'checked_at':datetime.datetime.now().astimezone().isoformat(),'method':'New independent symbolic checker built only from JSON polynomial coefficient arrays with exact rational constructors; no contestant program/string evaluation','identities':729,'mismatches':failed,'support':len(obj),'parameter_domain':'rational finite s outside '+str(sorted(poles)),'zeros_of_recorded_numerators':sorted(zeros),'poles':sorted(poles),'specialization_minus1_matches_original':match,'conclusion':'Exact one-parameter support138 scheme family verified on its regular rational domain. This does not prove family completeness, inequivalence of all points, dimension of every solution component, or no137after arbitrary gauge/boundary degeneration. No universal Lean theorem for the family is supplied.'}
(ROOT/'review/chandra-independent-family-check.json').write_text(json.dumps(result,indent=2),encoding='utf8');print(json.dumps(result))
