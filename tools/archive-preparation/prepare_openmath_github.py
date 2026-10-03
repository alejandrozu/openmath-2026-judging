"""Prepare an OpenMath-only publication snapshot. Never executes contestant code."""
from pathlib import Path
import json, sqlite3, hashlib, re, zipfile, shutil, datetime, csv, io, collections

ROOT=Path(__file__).resolve().parent
DEST=ROOT/'OpenMath-GitHub-Archive'
CACHE=ROOT/'OpenMath-GitHub-Assets'
DEST.mkdir(exist_ok=True); CACHE.mkdir(exist_ok=True)
STAMP=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
TEXT_EXT={'.txt','.md','.json','.jsonl','.csv','.tsv','.html','.xml','.yaml','.yml','.py','.ps1','.cmd','.bat','.js','.ts','.lean','.v','.thy','.tex','.bib','.rst','.toml','.sh','.c','.h','.cpp','.jl','.sage','.log','.out','.err'}
EMAIL=re.compile(r'(?<![\w.+-])[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}(?![\w.-])')
SECRETS=re.compile(rb'(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,}|sk-(?:proj-)?[A-Za-z0-9_-]{35,}|AKIA[A-Z0-9]{16}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|ya29\.[A-Za-z0-9_-]{30,})')
REDACTIONS=[]; EXCLUSIONS=[]; FLAGS=[]; ENTRIES=[]; PAYLOAD={}

def digest(b): return hashlib.sha256(b).hexdigest()

def clean_text(s):
    s=EMAIL.sub('[REDACTED CONTACT]',s)
    # Contact phones, rather than arbitrary mathematical integers.
    s=re.sub(r'(?i)((?:phone|mobile|telephone|teléfono|tel|whatsapp)(?: number)?\s*[:=]\s*[\"\']?)(\+?[\d ()-]{8,25})',r'\1[REDACTED PHONE]',s)
    s=re.sub(r'(?m)^(Authorization|Cookie|Set-Cookie):[^\r\n]*',r'\1: [REDACTED CREDENTIAL]',s)
    s=re.sub(r'(?i)([?&](?:access_token|auth_token|api_key|signature|x-amz-signature)=)[^&\s\"<>]+',r'\1REDACTED',s)
    s=SECRETS.sub(b'[REDACTED CREDENTIAL]',s.encode('utf8')).decode('utf8')
    # Replace workstation paths, preserving relative library/source paths.
    for base in (str(ROOT),str(ROOT).replace('\\','/'),str(ROOT).replace('\\','\\\\')):
        s=s.replace(base,'.')
    s=s.replace('C:/Users/Propietario/Desktop/to do.txt','[LOCAL PRIVATE OBLIGATIONS RECORD]')
    return s

def scan_zip(b,label,depth=0):
    if depth>4: FLAGS.append({'path':label,'reason':'nested archive depth exceeded'});return
    try:
        with zipfile.ZipFile(io.BytesIO(b)) as z:
            for n in z.namelist():
                if n.endswith('/'): continue
                if Path(n).suffix.lower()=='.zip':
                    scan_zip(z.read(n),label+'!'+n,depth+1)
                elif Path(n).suffix.lower() in TEXT_EXT or Path(n).name in {'.env','LICENSE','lean-toolchain'}:
                    with z.open(n) as stream:
                        tail=b''
                        while True:
                            block=stream.read(1024*1024)
                            if not block:break
                            if SECRETS.search(tail+block):
                                FLAGS.append({'path':label+'!'+n,'reason':'credential-like literal in original archive'});break
                            tail=block[-200:]
    except zipfile.BadZipFile:
        FLAGS.append({'path':label,'reason':'archive could not be inspected'})

def add_file(p,relative,force_bytes=None):
    b=force_bytes if force_bytes is not None else p.read_bytes()
    original=digest(b)
    istext=p.suffix.lower() in TEXT_EXT or p.name in {'START-HERE.txt','lean-toolchain','LICENSE'}
    if istext:
        try:
            s=b.decode('utf-8-sig')
            if p.suffix.lower()=='.json':
                # Redact decoded string tokens; retain all numeric lexemes and JSON escaping.
                def clean_token(match):
                    old=json.loads(match.group());new=clean_text(old)
                    return json.dumps(new,ensure_ascii=False) if old!=new else match.group()
                cleaned=re.sub(r'"(?:\\.|[^"\\])*"',clean_token,s)
                json.loads(cleaned)
            else:cleaned=clean_text(s)
            b=cleaned.encode('utf8')
            if b!=s.encode('utf8'): REDACTIONS.append(relative)
        except UnicodeDecodeError:pass
    if SECRETS.search(b): FLAGS.append({'path':relative,'reason':'credential-like literal in binary file'})
    if p.suffix.lower()=='.zip': scan_zip(b,relative)
    h=digest(b)
    # Keep browsable current documents in Git, large data and historical trees in release assets.
    historical_tree=relative.startswith(('outputs/OpenMath-morning-artifacts/','outputs/OpenMath-late-morning-artifacts/','outputs/OpenMath-library-full-archives/','outputs/sakana/'))
    storage='release' if len(b)>1024*1024 or p.suffix.lower() in {'.zip','.gz','.sqlite'} or historical_tree else 'git'
    if storage=='git':
        q=DEST/relative;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
    else:
        q=CACHE/'objects'/h;q.parent.mkdir(exist_ok=True);q.write_bytes(b) if not q.exists() else None
        PAYLOAD[h]=q
    ENTRIES.append({'path':relative,'bytes':len(b),'sha256':h,'original_sha256':original,'source_bytes':p.stat().st_size,'storage':storage,'redacted':h!=original})

sources=[]
for p in (ROOT/'OpenMath-Judging').rglob('*'):
    if not p.is_file():continue
    rel=p.relative_to(ROOT).as_posix()
    if '__pycache__' in p.parts or p.suffix in {'.pyc'} or p.name in {'app-started.json','catalogue-incomplete-first-build.sqlite'}:
        EXCLUSIONS.append({'path':rel,'reason':'runtime/cache or failed first-build artifact; not current material'});continue
    if p.suffix.lower()=='.png' and ('native-' in p.name):
        EXCLUSIONS.append({'path':rel,'reason':'UI screenshot may expose unrelated desktop context; structured verification retained','sha256':digest(p.read_bytes())});continue
    sources.append(p)
for p in (ROOT/'outputs').rglob('*'):
    if not p.is_file():continue
    parts=p.relative_to(ROOT/'outputs').parts
    selected=any('openmath' in x.lower() for x in parts) or parts[0]=='sakana' or p.name.startswith(('Jamie-','Chandragupt-'))
    if not selected:continue
    rel=p.relative_to(ROOT).as_posix()
    if p.parent==ROOT/'outputs' and p.suffix.lower() in {'.png','.jpeg','.jpg'}:
        EXCLUSIONS.append({'path':rel,'reason':'receipt/UI screenshot contains personal contact details; text receipts retained','sha256':digest(p.read_bytes())});continue
    if '__pycache__' in p.parts or p.suffix=='.pyc':continue
    sources.append(p)
# Research scripts restricted to OpenMath. Mixed personal-obligation synchronizers are not published.
mixed=('continuity','obligation','current_action','today_obligation','wispr','expense','refresh_todo')
for base in (ROOT,ROOT/'outputs'):
    for p in base.glob('*.py'):
        if p.name=='prepare_openmath_github.py':continue
        s=p.read_text(encoding='utf-8-sig')
        if 'OpenMath' not in s and 'openmath' not in s and 'chandra' not in p.name:continue
        if any(x in p.name.lower() for x in mixed) or any(x in s for x in ['DNI Monday','Wispr personal','HackNation optional']):
            EXCLUSIONS.append({'path':p.relative_to(ROOT).as_posix(),'reason':'mixed obligation synchronizer; its OpenMath outputs are included'});continue
        sources.append(p)
sources.append(ROOT/'compact_review_decisions.json')
sources=sorted(set(sources))
print('Preparing',len(sources),'files',flush=True)
for i,p in enumerate(sources):
    rel=p.relative_to(ROOT).as_posix()
    if p.name=='catalogue.sqlite':continue
    add_file(p,rel)
    if (i+1)%1500==0:print('Prepared',i+1,flush=True)

# Consistent SQLite backup, preserving all 353195 indexes and all existing review notes.
snapshot=CACHE/'catalogue.snapshot.sqlite'
src=sqlite3.connect(ROOT/'OpenMath-Judging/catalogue.sqlite'); dst=sqlite3.connect(snapshot);src.backup(dst);src.close()
tables=dst.execute("select name from sqlite_master where type='table'").fetchall()
for (table,) in tables:
    columns=dst.execute('pragma table_info('+table+')').fetchall()
    textcols=[col[1] for col in columns if 'TEXT' in col[2].upper()]
    if not textcols:continue
    rows=dst.execute('select rowid,'+','.join(textcols)+' from '+table).fetchall()
    updates=[]
    for row in rows:
        old=list(row[1:]);new=[clean_text(v) if isinstance(v,str) else v for v in old]
        if new!=old:updates.append(tuple(new)+ (row[0],))
    if updates:dst.executemany('update '+table+' set '+','.join(x+'=?' for x in textcols)+' where rowid=?',updates)
    print('SQLite sanitized',table,len(updates),flush=True)
# Refresh hashes for redacted loose files; retain original hashes in publication manifest.
dst.execute('CREATE INDEX IF NOT EXISTS publication_local_path ON files(local_path)')
for e in ENTRIES:
    if e['path'].startswith('OpenMath-Judging/') and e['redacted']:
        dst.execute('update files set sha256=?,bytes=? where local_path=?',(e['sha256'],e['bytes'],e['path'][len('OpenMath-Judging/'):]))
dst.commit();counts={'teams':dst.execute('select count(*) from teams where id!="EVENT"').fetchone()[0],'file_entries':dst.execute('select count(*) from files').fetchone()[0],'file_summaries':dst.execute('select count(*) from file_reviews').fetchone()[0]};dst.close()
add_file(ROOT/'OpenMath-Judging/catalogue.sqlite','OpenMath-Judging/catalogue.sqlite',snapshot.read_bytes())

manifest={'generated_at':STAMP,'permissions':'User expressly confirmed permissions to publish all affected private and unaccepted packets on 2026-10-03. This does not transfer ownership.','counts':counts,'files':ENTRIES,'exclusions':EXCLUSIONS,'privacy_transformations':{'redacted_text_files':len(REDACTIONS),'contacts':'Unnecessary email/phone/header credentials redacted from loose publication copies. Original archives and scholarly licenses retained unless credential scan blocks release.','originals':'Untouched originals remain locally; public manifest records original and publication SHA256.'},'credential_scan':{'archive_scan':'All text members, including nested ZIPs, streamed through credential-pattern checks','flags':FLAGS}}
(CACHE/'publication-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({'prepared':len(ENTRIES),'git':sum(e['storage']=='git' for e in ENTRIES),'release_paths':sum(e['storage']=='release' for e in ENTRIES),'unique_payloads':len(PAYLOAD),'flags':len(FLAGS),'counts':counts,'redacted':len(REDACTIONS)},indent=2),flush=True)
if FLAGS:
    print('Publication blocked: inspect local credential scan paths, never print secret values.');raise SystemExit(2)
# Content-addressed, deduplicated release packs; keep comfortably below 2GiB limit.
assets=[]; z=None; raw=0; sequence=0; mapping={}
for h,p in sorted(PAYLOAD.items()):
    size=p.stat().st_size
    if z is None or raw+size>650*1024*1024:
        if z:z.close()
        sequence+=1;name=f'openmath-materials-{sequence:03d}.zip';z=zipfile.ZipFile(CACHE/name,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=5);assets.append(name);raw=0
    # Already compressed artifacts require no second compression pass.
    with p.open('rb') as f: prefix=f.read(4)
    compression=zipfile.ZIP_STORED if prefix.startswith((b'PK',b'\x1f\x8b')) else zipfile.ZIP_DEFLATED
    z.write(p,'objects/'+h,compress_type=compression);raw+=size;mapping[h]=name
if z:z.close()
for e in ENTRIES:
    if e['storage']=='release':e['asset']=mapping[e['sha256']];e['object']='objects/'+e['sha256']
manifest['assets']=[{'name':n,'bytes':(CACHE/n).stat().st_size,'sha256':digest((CACHE/n).read_bytes())} for n in assets]
(DEST/'publication-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf8')
(CACHE/'publication-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf8')
print('Assets',json.dumps(manifest['assets'],indent=2),flush=True)
