import sys,json,pathlib
root=pathlib.Path('OpenMath-Judging');sys.path.insert(0,str(root));from library_core import *
sys.stdout.reconfigure(encoding='utf-8');c=connect(root)
for fid in [58675,343951,344087,344154]:
 r=c.execute('select * from files where id=?',(fid,)).fetchone();print('FILE',fid,r['original_path']);print(read_bytes(root,r).decode('utf-8',errors='replace')[:7200])
p=json.loads((root/'judging/atlas-target-candidates.json').read_text(encoding='utf-8'))['matches'][0]
print('PROFILEKEYS',list(p));print(json.dumps(p,ensure_ascii=False)[:2400])
