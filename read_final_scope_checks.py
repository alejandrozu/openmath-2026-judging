import pathlib,sys,re
root=pathlib.Path('OpenMath-Judging');sys.path.insert(0,str(root));from library_core import connect,read_bytes
c=connect(root);sys.stdout.reconfigure(encoding='utf8')
for team,pattern in [('E02','%OEIS224.lean.txt'),('E02','%LatinTableau.lean%'),('E12','%heilbronn%py'),('E09','README.md')]:
 rows=c.execute('select * from files where team_id=? and original_path like ? and bytes<250000 limit 10',(team,pattern)).fetchall()
 for r in rows:
  t=read_bytes(root,r,150000).decode('utf8',errors='replace')
  if team=='E12':
   found=[line[:180] for line in t.splitlines() if re.search('square|triangle|domain|unit|0\.0|1\.0|corners|boundary',line,re.I)]
   print(r['id'],r['original_path'],'\n'.join(found[:18]))
  else:print(r['id'],r['original_path'],t[:9000])
