"""Independent integer arithmetic checks. Does not import or run contestant code."""
import pathlib,sys,json,zipfile,hashlib,itertools,time,math,re
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT))
from library_core import connect,read_bytes
sys.stdout.reconfigure(encoding='utf-8');db=connect(ROOT);cache={}
def raw(fid):
 r=db.execute('SELECT * FROM files WHERE id=?',(fid,)).fetchone()
 if r['archive_path']:
  p=ROOT/r['archive_path'];z=cache.setdefault(str(p),zipfile.ZipFile(p)) if str(p) not in cache else cache[str(p)]
  b=z.read(r['archive_member'])
 else:b=read_bytes(ROOT,r)
 return r,b
def data(fid):return json.loads(raw(fid)[1])
def collatz(fid):
 d=data(fid);rules=d['rules'];valid=[];bad=[]
 for i,r in enumerate(rules):
  k=r['modulus_power'];q=r['residue'];es=r['exponents'];n=q;A=1;B=0;E=0;ok=(isinstance(k,int) and k>0 and 0<q<2**k and q%2==1)
  for e in es:
   u=3*n+1;v=(u&-u).bit_length()-1
   ok=ok and v==e and e>0; n=u//2**e;B=3*B+2**E;A*=3;E+=e
  ok=ok and k>=E+1 and A<2**E and A*q+B<2**E*q
  (valid if ok else bad).append(i)
 K=max(r['modulus_power'] for r in rules)
 covered={a for a in range(1,2**K,2) if any(a%2**r['modulus_power']==r['residue'] for r in rules)}
 return {'file_id':fid,'rules':len(rules),'independently_valid':len(valid),'invalid_indices':bad,'union_modulus':2**K,'covered_odd_classes':len(covered),'total_odd_classes':2**(K-1),'_covered':covered,'_rules':rules,'meaning':'Exact infinite residue-class descent, not universal Collatz convergence or novelty'}
def triangle_count(lines):
 # Homogeneous rational vertices; normalize denominator positive, so signs are exact.
 n=len(lines);points={};dups=[]
 for i,j in itertools.combinations(range(n),2):
  a,b,c=lines[i];d,e,f=lines[j];v=(b*f-c*e,c*d-a*f,a*e-b*d)
  if v==(0,0,0):dups.append((i,j))
  if v[2]<0:v=tuple(-x for x in v)
  points[i,j]=v
 count=0
 for i,j,k in itertools.combinations(range(n),3):
  p=points[i,j];q=points[i,k];r=points[j,k]
  if not p[2] or not q[2] or not r[2]:continue
  area=p[0]*(q[1]*r[2]-q[2]*r[1])-p[1]*(q[0]*r[2]-q[2]*r[0])+p[2]*(q[0]*r[1]-q[1]*r[0])
  if area==0:continue
  good=True
  for h,(a,b,c) in enumerate(lines):
   if h in (i,j,k):continue
   vals=[a*v[0]+b*v[1]+c*v[2] for v in (p,q,r)]
   if min(vals)<0<max(vals):good=False;break
  if good:count+=1
 return count,dups
assert triangle_count([[1,0,0],[0,1,0],[1,1,-1]])==(1,[])
assert triangle_count([[1,0,0],[0,1,0],[1,1,-1],[1,0,-2]])==(2,[])
start=time.time();results={'method':'Assistant-authored arbitrary-precision integer checks; contestant scripts and proof code not executed. Geometric face counts verify payload arithmetic only, not historical novelty, full upper bounds, or organizer checker approval.','collatz':[],'kobon':[]}
for fid in [344272,901]:
 r=collatz(fid);results['collatz'].append(r);print('COLLATZ',fid,r['rules'],r['independently_valid'],r['covered_odd_classes'],r['union_modulus'],flush=True)
j=db.execute("SELECT id FROM files WHERE team_id='E10' AND original_path='work_packages/OPENMATH_2026/CONTEST_CANDIDATES/H4/solution.json' AND version LIKE '%2fd9fd64%'").fetchone()
if j:
 r=collatz(j[0]);results['collatz'].append(r);print('COLLATZ',j[0],r['rules'],r['independently_valid'],r['covered_odd_classes'],flush=True)
K=max(int(math.log2(r['union_modulus'])) for r in results['collatz']);sets={}
for r in results['collatz']:
 sets[r['file_id']]={a for a in range(1,2**K,2) if a%r['union_modulus'] in r['_covered']}
 r.pop('_covered');r.pop('_rules')
results['collatz_synergy']=[{'left':a,'right':b,'left_only':len(sets[a]-sets[b]),'right_only':len(sets[b]-sets[a]),'union_odd_classes':len(sets[a]|sets[b]),'modulus':2**K} for a,b in itertools.combinations(sets,2)]
rows=list(db.execute("SELECT * FROM files WHERE team_id='E57' AND original_path LIKE 'kobon-triangles/submissions/n%/solution.json'"));ids=[1207]+[r['id'] for r in rows]
for idx,fid in enumerate(ids):
 r,b=raw(fid);d=json.loads(b);lines=d['lines'];count,dups=triangle_count(lines)
 record={'file_id':fid,'team':r['team_id'],'path':r['original_path'],'sha256':hashlib.sha256(b).hexdigest(),'n':len(lines),'triangles_independent':count,'duplicate_line_pairs':dups,'version':r['version']};results['kobon'].append(record)
 print('KOBON',idx+1,'/',len(ids),r['team_id'],len(lines),count,flush=True)
out=ROOT/'judging/independent-certificate-checks.json';out.write_text(json.dumps(results,ensure_ascii=False,indent=2),encoding='utf-8');print('DONE',round(time.time()-start,2),'s',flush=True)
for z in cache.values():z.close()
