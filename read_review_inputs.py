import pathlib,sys,json,re,hashlib,gzip,zipfile
sys.stdout.reconfigure(encoding='utf-8')
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT))
from library_core import connect,read_bytes as uncached_read
zc={}
def read_bytes(root,r):
 if r['archive_path']:
  p=root/r['archive_path'];key=str(p)
  if key not in zc:zc[key]=zipfile.ZipFile(p)
  return zc[key].read(r['archive_member'])
 return uncached_read(root,r)
db=connect(ROOT);out=ROOT/'judging';ledger=[]
ids=[344219,344224,344299,344301,7657,345968,345971,345976,346207,346211,346220,347014,347047,351696,346316,346318,743,53,58,1238]
for fid in ids:
 r=db.execute('SELECT * FROM files WHERE id=?',(fid,)).fetchone();raw=read_bytes(ROOT,r);s=raw.decode('utf-8',errors='replace')
 (out/f'source-read-{fid}.txt').write_text(s,encoding='utf-8')
 ledger.append({'id':fid,'team':r['team_id'],'path':r['original_path'],'version':r['version'],'sha256_read':hashlib.sha256(raw).hexdigest(),'read':True,'limits':'Static text review; not a compiler or mathematical acceptance'})
 if fid in [351696,743,53,1238,345968,345976,7657]:
  print('\nSOURCE',fid,r['original_path'])
  if fid==351696:
   for line in s.splitlines():
    if re.search('^\||^#{1,4} |formal|threshold|inverse|reflection|OPEN|missing|authoritative',line,re.I): print(line[:650])
  elif fid==743:
   for line in s.splitlines():
    if re.search('^#{1,4} |^\| (G-PM|E\d|M2|Selected)|progress|minor',line,re.I): print(line[:650])
  elif fid in [53,1238]:
   for m in re.finditer(r'(?im)^#{1,3} .*?(?:progress|difficulty|trust|axiom|scope|novelty).*$',s):print(s[m.start():m.start()+1400])
  else:print(s[:11000])
(out/'source-reading-ledger.json').write_text(json.dumps(ledger,ensure_ascii=False,indent=2),encoding='utf-8')
# Read full selected local Lean sources; broad scans include intentionally unfinished research.
patterns={'E06':['CamposSamotij/%.lean'],'E08':['%ramsey-k4-multiplicity/artifact/lean_v2/%.lean','%kobon-n39-lavaskiller/lean/%.lean','%dms-star6/formal_sources/%.lean'], 'E10':['%OM26_H7_ERDOS_3/H7_D%.lean'], 'E11':['lean/equivalence/%.lean','lean/climb1-library/Converse.lean','lean/climb1-library/VonNeumann4.lean','lean/three-term/Solution.lean'],'E65':['lean/%.lean']}
patterns['E02']=['Claim_Evidence/%.lean','Focus_Evidence/%.lean','Reproduction_Sources/%.lean','Ordinary_Evidence/%.lean']
def uncomment(s):
 # Nested Lean block comments and line comments; retain strings conservatively.
 buf=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2;continue
  if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
  if depth:i+=1;continue
  if s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  buf.append(s[i]);i+=1
 return ''.join(buf)
audit=[];seen=set()
for team,ps in patterns.items():
 for p in ps:
  for r in db.execute('SELECT * FROM files WHERE team_id=? AND original_path LIKE ?',(team,p)):
   if r['id'] in seen:continue
   seen.add(r['id']);raw=read_bytes(ROOT,r);s=uncomment(raw.decode('utf-8',errors='replace'))
   tokens={word:len(re.findall(r'\b'+word+r'\b',s)) for word in ['sorry','admit','axiom','native_decide','unsafe','implemented_by','skipKernelTC']}
   audit.append({'file_id':r['id'],'team':team,'path':r['original_path'],'version':r['version'],'sha256':hashlib.sha256(raw).hexdigest(),'tokens':tokens,'flag_context':[s[max(0,m.start()-150):m.start()+200] for m in re.finditer(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|skipKernelTC)\b',s)],'endpoints':[x[:700] for x in re.findall(r'(?m)^\s*(?:theorem|lemma)\s+[^\n]+',s)]})
(out/'static-formal-source-audit.json').write_text(json.dumps({'meaning':'Text inspection only; unused holes can be outside endpoint closure, and clean text does not prove kernel acceptance. No entrant code was executed.','files':audit},ensure_ascii=False,indent=2),encoding='utf-8')
print('FULL SOURCE READS',len(ledger),'LEAN TEXT FILES',len(audit))
for a in audit:
 if any(a['tokens'].values()):print('FLAG',a['team'],a['file_id'],a['path'],a['tokens'])
scores=json.loads((out/'Ulam_UnsolvedMath_ChatGPT_5.6_Sol_Ultra_Difficulty_v1.0.json').read_text(encoding='utf-8'))['records']
for r in scores:
 if r['problem_number'] in ['OPG-37271','EP-169','EP-21','EP-944','EP-829','EP-887'] or re.search('latin.tableau|positive.coefficients|quaternion|Boltzmann|Busy.Beaver|A100475|A060957|A000224',r['name']+' '+r['statement'],re.I):print('D',r['problem_id'],r['problem_number'],r['name'],r['chatgpt_difficulty_0_1000'],r['statement'][:550])
