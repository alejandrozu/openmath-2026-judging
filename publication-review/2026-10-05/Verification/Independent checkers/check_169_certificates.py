from fractions import Fraction
import json
from pathlib import Path
D=[0,1,2,4,5,9,10,11,14,16,17,18,21,24,30,37,39,41,42,45,47]
ds=set(D); U=[26286,26726,26737,120061,120501,120512]; M=55**3
old2=lambda z:z%55 in ds and z//55%55 in ds
old3=lambda z:old2(z) and z//3025%55 in ds
allowed=lambda z:old3(z) or z in U
base_bad=[(a,d) for a in D for d in range(1,55) if all((a+k*d)%55 in ds for k in range(4))]
endpoints={x:[d for d in range(55) if all((x+k*d)%55 in ds for k in [1,2,3])] for x in [7,51]}
two={x:[d for d0 in range(55) if all((x+k*d0)%55 in ds for k in [-1,1,2]) for d in [d0+55*t for t in range(55)] if all(old2((x+k*d)%3025) for k in [-1,1,2])] for x in [2086,2526,2537]}
third={z:[t for t in range(55) if all(v%55 in ds for v in [z-t,z+1+t,z+1+2*t])] for z in [8,39]}
badpairs=[]
for u in U:
 for v in U:
  if u==v: continue
  for i in range(4):
   for j in range(i+1,4):
    delta=((v-u)*pow(j-i,-1,M))%M
    start=(u-i*delta)%M
    if all(allowed((start+k*delta)%M) for k in range(4)):badpairs.append((u,v,i,j))
carryall=all((u-d)//3025==u//3025 and (u+d)//3025==u//3025+1 and (u+2*d)//3025==u//3025+1 for u in U for d in two[u%3025])
prefix=sum(10**12//(55*a+b+1) for a in D for b in D)
tail=sum(1155*10**12//(1155*(55*a+b)+454) for a in D if a for b in D)
newprefix=sum(10**15//(M*d+u+1) for u in U for d in D)
newtail=sum(1155*10**15//(M*(1155*d+454)) for u in U for d in D if d)
weight=sum((Fraction(21,55)**j for j in range(1,21)),Fraction())
lower=Fraction(prefix,10**12)+Fraction(newprefix,10**15)+(Fraction(tail,10**12)+Fraction(newtail,10**15))*weight
result={'method':'Independent exact Python integer/rational recomputation of the frozen source certificates; this is not a Lean replay.', 'base_bad_pairs':base_bad,'endpoint_candidates':endpoints,'two_digit_candidates':two,'third_digit_candidates':third,'two_new_bad_cases':badpairs,'carry_bridge_checked':carryall,'old_prefix_floor':prefix,'old_tail_floor':tail,'new_prefix_floor':newprefix,'simple_new_tail_floor':newtail,'reciprocal_lower_exact':str(lower),'reciprocal_lower_decimal':float(lower),'strictly_exceeds_111_over_25':lower>Fraction(111,25)}
p=Path(__file__).parent/'erdos169_independent_finite_certificate.json'
tmp=p.with_suffix('.json.tmp');tmp.write_text(json.dumps(result,indent=2),encoding='utf-8');tmp.replace(p)
print(json.dumps(result,indent=2))
