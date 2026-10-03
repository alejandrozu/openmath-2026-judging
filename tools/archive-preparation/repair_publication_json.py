"""Escape-aware JSON privacy transformation, preserving all numeric lexemes."""
from pathlib import Path
import json,re,hashlib,sqlite3,zipfile,collections
ROOT=Path(__file__).resolve().parent;DEST=ROOT/'OpenMath-GitHub-Archive';CACHE=ROOT/'OpenMath-GitHub-Assets'
m=json.loads((DEST/'publication-manifest.json').read_text(encoding='utf8'))
EMAIL=re.compile(r'(?<![\w.+-])[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}(?![\w.-])')
TOKEN=re.compile(r'"(?:\\.|[^"\\])*"')
def clean(s):
    s=EMAIL.sub('[REDACTED CONTACT]',s)
    s=re.sub(r'(?i)((?:phone|mobile|telephone|teléfono|tel|whatsapp)(?: number)?\s*[:=]\s*[\"\']?)(\+?[\d ()-]{8,25})',r'\1[REDACTED PHONE]',s)
    s=re.sub(r'(?m)^(Authorization|Cookie|Set-Cookie):[^\r\n]*',r'\1: [REDACTED CREDENTIAL]',s)
    s=re.sub(r'(?i)([?&](?:access_token|auth_token|api_key|signature|x-amz-signature|pwd)=)[^&\s\"<>]+',r'\1REDACTED',s)
    s=re.sub(r'https://chat\.whatsapp\.com/[A-Za-z0-9]+','[REDACTED GROUP INVITATION]',s)
    for base in (str(ROOT),str(ROOT).replace('\\','/')):s=s.replace(base,'.')
    s=s.replace('C:/Users/Propietario/Desktop/to do.txt','[LOCAL PRIVATE OBLIGATIONS RECORD]')
    return s
def sha(b):return hashlib.sha256(b).hexdigest()
changed=[]
for e in m['files']:
    if not e['redacted'] or Path(e['path']).suffix.lower()!='.json':continue
    source=ROOT/e['path'];text=source.read_text(encoding='utf-8-sig')
    def string_token(match):
        old=json.loads(match.group());new=clean(old)
        return json.dumps(new,ensure_ascii=False) if new!=old else match.group()
    text=TOKEN.sub(string_token,text);json.loads(text);b=text.encode('utf8');h=sha(b)
    if h==e['sha256']:continue
    e.update(sha256=h,bytes=len(b),redacted=True);changed.append(e)
    if e['storage']=='git':(DEST/e['path']).write_bytes(b)
    else:(CACHE/'objects'/h).write_bytes(b)
print('JSON publication copies corrected:',len(changed),flush=True)
c=sqlite3.connect(CACHE/'catalogue.snapshot.sqlite')
c.execute('CREATE INDEX IF NOT EXISTS publication_local_path ON files(local_path)')
for e in changed:
    if e['path'].startswith('OpenMath-Judging/'):
        c.execute('UPDATE files SET sha256=?,bytes=? WHERE local_path=?',(e['sha256'],e['bytes'],e['path'][len('OpenMath-Judging/'):]))
c.commit();assert c.execute('PRAGMA integrity_check').fetchone()[0]=='ok';c.close()
b=(CACHE/'catalogue.snapshot.sqlite').read_bytes();h=sha(b);(CACHE/'objects'/h).write_bytes(b)
entry=next(e for e in m['files'] if e['path']=='OpenMath-Judging/catalogue.sqlite')
entry.update(sha256=h,bytes=len(b),original_sha256=sha((ROOT/'OpenMath-Judging/catalogue.sqlite').read_bytes()),redacted=True)
# Repack only live referenced objects. Unreferenced intermediate objects remain local.
objects={e['sha256'] for e in m['files'] if e['storage']=='release'}
assets=[];mapping={};z=None;total=0
for h in sorted(objects):
    p=CACHE/'objects'/h;size=p.stat().st_size
    if z is None or total+size>650*1024*1024:
        if z:z.close()
        name=f'openmath-materials-{len(assets)+1:03d}.zip';assets.append(name);z=zipfile.ZipFile(CACHE/(name+'.new'),'w',compression=zipfile.ZIP_DEFLATED,compresslevel=5);total=0
    with p.open('rb') as f:prefix=f.read(4)
    compression=zipfile.ZIP_STORED if prefix.startswith((b'PK',b'\x1f\x8b')) else zipfile.ZIP_DEFLATED
    z.write(p,'objects/'+h,compress_type=compression);mapping[h]=name;total+=size
if z:z.close()
for name in assets:(CACHE/(name+'.new')).replace(CACHE/name)
for e in m['files']:
    if e['storage']=='release':e.update(asset=mapping[e['sha256']],object='objects/'+e['sha256'])
m['assets']=[{'name':name,'bytes':(CACHE/name).stat().st_size,'sha256':sha((CACHE/name).read_bytes())} for name in assets]
m['privacy_transformations']['json']='String-token redaction preserves JSON escaping and every original numeric lexeme.'
(DEST/'publication-manifest.json').write_text(json.dumps(m,ensure_ascii=False,indent=2),encoding='utf8')
(CACHE/'publication-manifest.json').write_text(json.dumps(m,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({'assets':m['assets'],'paths':len(m['files'])},indent=2),flush=True)
