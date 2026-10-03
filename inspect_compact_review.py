import json,sys,pathlib,sqlite3
from pypdf import PdfReader
sys.stdout.reconfigure(encoding='utf-8')
r=pathlib.Path('OpenMath-Judging');d=json.loads((r/'judging/preliminary-assessment.json').read_text(encoding='utf-8'))
print('TOP KEYS',list(d))
print('FIRST FAMILY',json.dumps(next(iter(d['families'].values())),ensure_ascii=False)[:4500])
print('GROUP SCHEMA',json.dumps(json.loads((r/'contestants.json').read_text(encoding='utf-8'))[0],ensure_ascii=False)[:3500])
print('RESULT KEYS',list(d['results'][0]))
print('TALLY TYPE',type(d.get('tallies')).__name__)
for x in d['results']:
 if x['family_id'] and x['modality_proposal']!='NONE':
  print(x['id'],x['family_id'],x['title'],'|',x['exact_claim'][:260].replace('\n',' '),'|',x['modality_proposal'],x['p_scope_if_claim_valid'],x['catalogue_file_ids'])
c=sqlite3.connect(r/'catalogue.sqlite');print('TABLES',c.execute("select name,sql from sqlite_master where type='table'").fetchall())
p=PdfReader(r/'contestants/EVENT/02-papers/competition_handbook_final.pdf')
print('HANDBOOK\n'+'\n'.join(p.pages[i].extract_text() for i in range(2,min(7,len(p.pages)))))
