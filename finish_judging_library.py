"""Incremental original-attachment and nested-archive import; never executes entries."""
import sys,pathlib,json,hashlib,zipfile,shutil,csv,datetime
BASE=pathlib.Path(__file__).resolve().parent; ROOT=BASE/'OpenMath-Judging'
sys.path.insert(0,str(ROOT))
from library_core import connect,classify,CATEGORIES,read_bytes
db=connect(ROOT); now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,ensure_ascii=False,indent=2),encoding='utf-8')
provenance=json.loads((ROOT/'archive-provenance.json').read_text(encoding='utf-8'))
imports=[]
def add(gid,name,local='',archive='',member='',data=None,size=0,crc='',version='',source='',verification='',category=None,basis=None):
    if db.execute('SELECT 1 FROM files WHERE team_id=? AND local_path=? AND archive_path=? AND archive_member=?',(gid,local,archive,member)).fetchone():return
    cat,topic,why=classify(name)
    db.execute('INSERT INTO files(team_id,category,topic,basis,original_path,local_path,archive_path,archive_member,bytes,sha256,crc32,version,source,verification) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)',(gid,category or cat,topic,basis or why,name,local,archive,member,len(data) if data is not None else size,hashlib.sha256(data).hexdigest() if data is not None else '',crc,version,source,verification))
def archive(gid,p,version,source,parent=None):
    rel=p.relative_to(ROOT).as_posix()
    if db.execute('SELECT 1 FROM archives WHERE local_path=?',(rel,)).fetchone():return
    with zipfile.ZipFile(p) as z:
        bad=z.testzip();assert bad is None,(p,bad)
        members=[i for i in z.infolist() if not i.is_dir()]
        for i in members:
            add(gid,(parent+' :: ' if parent else '')+i.filename,archive=rel,member=i.filename,size=i.file_size,crc=f'{i.CRC:08x}',version=version,source=source,verification='Original archive SHA-256 and all member CRCs verified; no mathematical validation')
    digest=sha(p)
    db.execute('INSERT INTO archives(team_id,local_path,sha256,member_count,version,source) VALUES(?,?,?,?,?,?)',(gid,rel,digest,len(members),version,source))
    add(gid,p.name,local=rel,data=p.read_bytes(),version=version,source=source,verification='SHA-256 and archive member CRCs verified',category='13-archives')
    provenance.append({'team_id':gid,'path':rel,'sha256':digest,'members':len(members),'version':version,'parent_original_path':parent})
    imports.append({'team_id':gid,'path':rel,'members':len(members),'source':source})

qpath=pathlib.Path('C:/Users/Propietario/Downloads/reopenmathfinalworkandjudgingmaterials.zip')
qdest=ROOT/'contestants/E17/13-archives/Gmail-original-attachments-1a0ffb744e576946.zip'
if not qdest.exists():shutil.copy2(qpath,qdest)
archive('E17',qdest,'Original Gmail attachments received 05:03:14 CEST; retrieved via browser Download all. This is NOT the absent 27MB source ZIP.','https://mail.google.com/mail/u/0/#all/1a0ffb744e576946')
with zipfile.ZipFile(qdest) as z:
    assert {pathlib.PurePosixPath(i.filename).name for i in z.infolist() if not i.is_dir()}=={'OPENMATH_SUBMISSION.md','VALIDATION.md','COMPLETION.md','COMPLETION.json'}

for gid,name,source in [('EVENT','competition_handbook_final.pdf','https://mail.google.com/mail/u/0/#all/1a0a2f0be44db6e4'),('EVENT','OpenMath-library-shared-drive-index.txt','https://drive.google.com/drive/folders/1oM0Za-ohLsaY3yd5-kDsdKb8MOWPdy7-')]:
    original=pathlib.Path('C:/Users/Propietario/Downloads')/name if name.endswith('.pdf') else BASE/'outputs'/name
    cat=classify(name)[0] if name.endswith('.pdf') else '12-correspondence'
    dest=ROOT/'contestants'/gid/cat/name
    if not dest.exists():shutil.copy2(original,dest)
    add(gid,name,local=dest.relative_to(ROOT).as_posix(),data=dest.read_bytes(),source=source,version='Original handbook downloaded from Gmail' if name.endswith('.pdf') else 'Shared event folder listing, not an entrant packet',verification='Original downloaded bytes, SHA-256 recorded' if name.endswith('.pdf') else 'Rendered browser listing capture',category=cat)

starter=ROOT/'contestants/EVENT/13-archives/OpenMath_Six_Problems_Lean.zip'
if not starter.exists():shutil.copy2(pathlib.Path('C:/Users/Propietario/Downloads/OpenMath_Six_Problems_Lean.zip'),starter)
archive('EVENT',starter,'Shared organizer starter files; NOT a contestant result','https://drive.google.com/file/d/10XfoInD6d8G75CDlJ8nwRA6oe9TUPk3K/view')

processed=set()
for depth in range(4):
    candidates=[r for r in db.execute("SELECT * FROM files WHERE category='13-archives' AND archive_member!=''").fetchall() if r['id'] not in processed]
    if not candidates:break
    for r in candidates:
        processed.add(r['id'])
        if not r['original_path'].lower().endswith('.zip'):continue
        payload=read_bytes(ROOT,r)
        dest=ROOT/'contestants'/r['team_id']/'13-archives'/('nested-'+str(r['id'])+'-'+pathlib.PurePosixPath(r['archive_member']).name)
        if not dest.exists():dest.write_bytes(payload)
        archive(r['team_id'],dest,r['version']+' | Nested archive; inherits parent claim/receipt limits',r['source'],r['original_path'])

# Separate bundled dependency source from the entrants' own formalization.
for r in db.execute("SELECT id,original_path,basis FROM files WHERE original_path LIKE '%/.lake/%' OR original_path LIKE '.lake/%' OR original_path LIKE '%/node_modules/%' OR original_path LIKE '%/site-packages/%'").fetchall():
    if r['basis']!='User classification override':
        cat,topic,basis=classify(r['original_path']);db.execute('UPDATE files SET category=?,topic=?,basis=? WHERE id=?',(cat,topic,basis,r['id']))
groups=json.loads((ROOT/'contestants.json').read_text(encoding='utf-8'))
for g in groups:db.execute('UPDATE teams SET aliases=? WHERE id=?',(' '.join(str(a) for a in g.get('accounts',[])+g.get('authors',[])),g['group_id']))
db.commit()
for t in db.execute('SELECT id FROM teams').fetchall():
    for cat in CATEGORIES:
        p=ROOT/'contestants'/t['id']/cat/'FILE-INDEX.csv'
        with p.open('w',encoding='utf-8-sig',newline='') as f:
            w=csv.writer(f);w.writerow(['id','original_path','topic','bytes','version','source','local_path','archive_path','archive_member','sha256','crc32','basis'])
            for r in db.execute('SELECT * FROM files WHERE team_id=? AND category=? ORDER BY original_path,id',(t['id'],cat)):
                vals=[r[k] for k in ['id','original_path','topic','bytes','version','source','local_path','archive_path','archive_member','sha256','crc32','basis']]
                w.writerow(["'"+v if isinstance(v,str) and v.startswith(('=','+','-','@')) else v for v in vals])
summary=json.loads((ROOT/'collection-summary.json').read_text(encoding='utf-8'))
summary.update(updated_at=now,files=db.execute('SELECT COUNT(*) FROM files').fetchone()[0],archive_members=db.execute("SELECT COUNT(*) FROM files WHERE archive_member!=''").fetchone()[0],archive_count=db.execute('SELECT COUNT(*) FROM archives').fetchone()[0],categories=dict(db.execute('SELECT category,COUNT(*) FROM files GROUP BY category').fetchall()),original_qichao_manifests_retrieved=True,original_handbook_retrieved=True,shared_starter_archive_retrieved=True,additional_imports=summary.get('additional_imports',[])+imports)
summary['contestant_work_files']=dict(db.execute("SELECT team_id,COUNT(*) FROM files WHERE category NOT IN ('12-correspondence','13-archives') AND source!='Collected official hill leaderboards' AND team_id!='EVENT' GROUP BY team_id").fetchall())
dump(ROOT/'collection-summary.json',summary);dump(ROOT/'archive-provenance.json',provenance)
start=ROOT/'START-HERE.txt';text=start.read_text(encoding='utf-8');text=text.replace('351,695 local file entries include 351,392 members of 18 original archives.',f"{summary['files']:,} local file entries include {summary['archive_members']:,} members of {summary['archive_count']} preserved archives (including nested bundles and shared starter files).")
text+='\nOriginal Qichao manifests and the handbook were successfully retrieved via Gmail UI after connector URLs failed.\nThe shared Drive folder was checked: organizer slides/reference/guest-list material and a Lean starter ZIP, no additional entrant packets visible. Starter files are explicitly shared references.\nMatt inline illustration download failed; the repository, source message and image filename remain preserved.\n'
start.write_text(text,encoding='utf-8')
gaps=ROOT/'contestants/E03/MISSING-MATERIALS.txt'
if 'Original inline lean-unitary.png not retrieved' not in gaps.read_text(encoding='utf-8'):gaps.write_text(gaps.read_text(encoding='utf-8')+'\nOriginal inline lean-unitary.png not retrieved: connector download denied and Gmail media download timed out. Public repository and message link-card retained.\n',encoding='utf-8')
assert db.execute('PRAGMA integrity_check').fetchone()[0]=='ok'
print(json.dumps({'files':summary['files'],'archives':summary['archive_count'],'new_imports':imports},ensure_ascii=False))
db.close()
