import pathlib,sys,json,re
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT));sys.stdout.reconfigure(encoding='utf-8')
from library_core import connect,read_bytes
db=connect(ROOT)
for fid in [349908,347040,346252]:
 r=db.execute('SELECT * FROM files WHERE id=?',(fid,)).fetchone();s=read_bytes(ROOT,r).decode('utf-8')
 print(fid,r['original_path'])
 if fid==349908:
  print(s[:1800]);print([x[:300] for x in s.splitlines() if x.startswith('def ')][:20])
 else:
  for m in re.finditer(r'\bsorry\b',s):print(s[max(0,m.start()-140):m.start()+140])
