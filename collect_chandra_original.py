from pathlib import Path,PurePosixPath
import subprocess,zipfile,io,json,sqlite3,sys,hashlib,datetime
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT));from library_core import classify
SHA='479c2416b6261ee841052eef4881df0e40054f3f';repo='ChandraguptSharma07/matrix-multiplication-tensor-3x3'
dest=ROOT/'contestants/E04/13-archives'/('GitHub-original-'+SHA+'.zip');dest.parent.mkdir(parents=True,exist_ok=True)
if not dest.exists():
 p=subprocess.run(['gh','api','repos/'+repo+'/zipball/'+SHA],capture_output=True,timeout=60)
 if p.returncode:raise RuntimeError(p.stderr.decode('utf8',errors='replace'))
 if not p.stdout.startswith(b'PK'):raise RuntimeError('Not a ZIP')
 dest.write_bytes(p.stdout)
z=zipfile.ZipFile(dest);assert z.testzip() is None;prefix=z.namelist()[0].split('/')[0]+'/'
c=sqlite3.connect(ROOT/'catalogue.sqlite');registered=[]
for member in z.infolist():
 if member.is_dir():continue
 path=member.filename[len(prefix):];raw=z.read(member);sha=hashlib.sha256(raw).hexdigest();cat,topic,basis=classify(path)
 existing=c.execute('select id from files where team_id=? and original_path=? and sha256=?',('E04',path,sha)).fetchone()
 if existing:fid=existing[0]
 else:
  cursor=c.execute('INSERT INTO files(team_id,category,topic,basis,original_path,local_path,archive_path,archive_member,bytes,sha256,crc32,version,source,verification) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)',('E04',cat,topic,'Original pinned GitHub repository; static role inference',path,None,str(dest.relative_to(ROOT)),member.filename,len(raw),sha,f'{member.CRC:08x}',SHA,'Authenticated GitHub snapshot '+repo,'Original archive CRC and member SHA256 verified'))
  fid=cursor.lastrowid
 registered.append({'id':fid,'path':path,'bytes':len(raw),'sha256':sha})
local=str(dest.relative_to(ROOT));ash=hashlib.sha256(dest.read_bytes()).hexdigest()
if not c.execute('select id from files where local_path=?',(local,)).fetchone():
 c.execute('INSERT INTO files(team_id,category,topic,basis,original_path,local_path,archive_path,archive_member,bytes,sha256,crc32,version,source,verification) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)',('E04','13-archives','Matrix multiplication','Exact authenticated pinned repository ZIP',dest.name,local,None,None,dest.stat().st_size,ash,None,SHA,'Authenticated GitHub snapshot '+repo,'Original ZIP SHA256 and all CRC checks passed'))
c.commit()
key={}
for m in z.infolist():
 path=m.filename[len(prefix):]
 if path in ['solutions/support_138/solution.json','solutions/support_138_gauged/solution.json','solutions/core1809_support_143/solution.json','README.md','HANDOFF.md'] or path.endswith('.lean'):
  key[path]=z.read(m).decode('utf8',errors='replace')
out=ROOT/'review/chandra-original-check-input.json';out.write_text(json.dumps(key,ensure_ascii=False,indent=2),encoding='utf8')
report={'retrieved_at':datetime.datetime.now().astimezone().isoformat(),'repo':repo,'commit':SHA,'archive':local,'archive_sha256':ash,'files':len(registered),'members':registered,'crc_errors':0,'no_contestant_code_executed':True,'key_artifact_paths':list(key)}
(ROOT/'review/chandra-original-source-index.json').write_text(json.dumps(report,indent=2),encoding='utf8')
print(json.dumps({'files':len(registered),'bytes':dest.stat().st_size,'key_paths':list(key)}))
