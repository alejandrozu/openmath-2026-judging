import pathlib,json,sqlite3,sys,collections
sys.stdout.reconfigure(encoding='utf-8');root=pathlib.Path('OpenMath-Judging');d=json.loads((root/'judging/preliminary-assessment.json').read_text(encoding='utf-8'));c=sqlite3.connect(root/'catalogue.sqlite');c.row_factory=sqlite3.Row
out=[]
for r in d['results']:
 if r['team_id']!='E02':continue
 ds=(r.get('evidence') or {}).get('dossier',{})
 out.append({'id':r['id'],'claim':r['exact_claim'],'dossier':ds})
(root/'judging/compact-inputs.json').write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf-8')
for t in json.loads((root/'contestants.json').read_text(encoding='utf-8')):
 if t['has_review_material_or_manifests'] or t['identified_work_group']:
  print(t['group_id'],t['name'],'AUTHORS',t['authors'],'COMMIT',t['immutable_commit'])
print('SAKANA SCHEMA',list(out[0]['dossier']));print(json.dumps(out[0]['dossier'],ensure_ascii=False)[:8500])
print('SAKANA source files')
for row in c.execute("select id,original_path,bytes,category from files where team_id='E02' and category in ('01-submission','02-papers','03-novelty') and bytes<200000 order by id"):
 print(tuple(row))
