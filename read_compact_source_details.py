import pathlib,sys,json,sqlite3
sys.stdout.reconfigure(encoding='utf-8');root=pathlib.Path('OpenMath-Judging');sys.path.insert(0,str(root));from library_core import connect,read_bytes
c=connect(root);d=json.loads((root/'judging/preliminary-assessment.json').read_text(encoding='utf-8'))
for r in d['results']:
 if r['team_id']!='E02':continue
 ds=(r.get('evidence') or {}).get('dossier',{});fe=ds.get('formal_evidence',{})
 print('\n'+r['id']+'\nNOVELTY '+json.dumps(ds.get('prior_art',{}),ensure_ascii=False)[:1400]+'\nENDPOINTS '+json.dumps(fe.get('endpoints',[]),ensure_ascii=False)[:950]+'\nVERIFY '+fe.get('verification_scope',''))
ids=[349425,349424,350548,349430,349443,351603,351604,351605,351606]
texts=[]
for fid in ids:
 row=c.execute('select * from files where id=?',(fid,)).fetchone()
 if row:texts.append('FILE '+str(fid)+' '+row['original_path']+'\n'+read_bytes(root,row).decode('utf-8',errors='replace'))
(root/'judging/extended-source-reading.txt').write_text('\n\n'.join(texts),encoding='utf-8')
print('\nEXTENDED FILE',root/'judging/extended-source-reading.txt')
