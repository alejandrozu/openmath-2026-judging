import pathlib,sys,json
root=pathlib.Path('OpenMath-Judging');sys.path.insert(0,str(root));from library_core import connect,read_bytes
sys.stdout.reconfigure(encoding='utf-8');c=connect(root)
for row in c.execute("select * from files where team_id in ('E12','E09','E03') and (original_path like '%README.md' or original_path like '%final_report%' or original_path like '%SUMMARY.md' or original_path like '%paper.tex' or original_path like '%SUBMISSION.md') and bytes<100000 order by id limit 70"):
 print(row['id'],row['team_id'],row['original_path'],row['bytes'])
 if row['team_id']=='E12' and ('README' in row['original_path'] or 'final_report' in row['original_path']):
  t=read_bytes(root,row).decode('utf-8',errors='replace');print(t[:6500])
d=json.loads((root/'judging/compact-inputs.json').read_text(encoding='utf-8'))
for x in d:
 if x['id'] in ['E02-a000224','E02-ferrers-hierarchy','E02-opdp89-parity-local-maxima','E02-opdp13-quartic']:
  print(x['id'],json.dumps(x['dossier'].get('target'),ensure_ascii=False))
