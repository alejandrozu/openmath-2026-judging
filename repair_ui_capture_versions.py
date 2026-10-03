import pathlib,sys,json,hashlib,os
BASE=pathlib.Path(__file__).resolve().parent;ROOT=BASE/'OpenMath-Judging';sys.path.insert(0,str(ROOT))
from library_core import connect,classify
db=connect(ROOT)
source=json.loads((BASE/'outputs/OpenMath-morning-Chandragupt-private-source.json').read_text(encoding='utf-8'))
variants={}
for s in source:
    data=('Source: '+s['url']+'\nObserved: '+str(s.get('checked_at'))+'\nRepresentation: rendered GitHub UI extraction; may be incomplete, not original bytes.\n\n'+s['text']).replace('\n',os.linesep).encode('utf-8')
    variants.setdefault(s['url'],[]).append((s,data))
repaired=[];added=[]
for r in db.execute("SELECT * FROM files WHERE local_path!='' AND local_path LIKE 'contestants/E04/%UI-extraction.txt'").fetchall():
    p=ROOT/r['local_path'];data=p.read_bytes()
    assert any(data==v for s,v in variants[r['source']])
    db.execute('UPDATE files SET bytes=?,sha256=? WHERE id=?',(len(data),hashlib.sha256(data).hexdigest(),r['id']))
    if len(data)!=r['bytes']:repaired.append(r['id'])
    for s,v in variants[r['source']]:
        if v==data:continue
        digest=hashlib.sha256(v).hexdigest();dest=p.with_name(digest[:12]+'-earlier-'+p.name)
        if not dest.exists():dest.write_bytes(v)
        rel=dest.relative_to(ROOT).as_posix()
        if db.execute('SELECT 1 FROM files WHERE local_path=?',(rel,)).fetchone():continue
        db.execute('INSERT INTO files(team_id,category,topic,basis,original_path,local_path,archive_path,archive_member,bytes,sha256,crc32,version,source,verification) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)',('E04',r['category'],r['topic'],r['basis'],r['original_path'],rel,'','',len(v),digest,'','Separate earlier UI capture observed '+str(s.get('checked_at')),r['source'],r['verification']))
        added.append(rel)
db.commit()
report={'reason':'Same URL observed multiple times: source captures now kept separately; original contestant files unchanged','corrected_generated_capture_metadata':repaired,'additional_capture_versions':added,'all_contents_matched_saved_source':True}
(ROOT/'ui-capture-version-repair.json').write_text(json.dumps(report,indent=2),encoding='utf-8');print(json.dumps(report));db.close()
