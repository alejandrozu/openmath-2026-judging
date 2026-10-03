"""Build the offline contestant library from collected sources and originals."""
import pathlib, sys, json, sqlite3, shutil, hashlib, zipfile, re, html, base64, urllib.request, csv, datetime
BASE=pathlib.Path(__file__).resolve().parent; OUT=BASE/'outputs'; ROOT=BASE/'OpenMath-Judging'
sys.path.insert(0,str(ROOT));sys.stdout.reconfigure(encoding='utf-8')
from library_core import CATEGORIES, classify
NOW=datetime.datetime.now(datetime.timezone.utc).astimezone(datetime.timezone(datetime.timedelta(hours=2))).isoformat(timespec='seconds')
def load(name,default=None):
    p=OUT/name
    return json.loads(p.read_text(encoding='utf-8-sig')) if p.exists() else default
def dump(path,data):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
directory=load('OpenMath-team-directory-current.json');groups=list(directory['groups'])
for g in groups:
    if g['group_id']=='E73':
        g=dict(g,name='Terry Wang — future competition interest',status='Missed this competition; interested in future challenges. No current entry.',claims=[],gaps=['No current competition result submitted.'])
        groups[groups.index(next(x for x in groups if x['group_id']=='E73'))]=g
new_sources=load('OpenMath-library-ui-source.json',[])
gopal=next((x for x in new_sources if x['source'].startswith('Gopal')),None)
if gopal and not any(g['group_id']=='E74' for g in groups):
    groups.append({'group_id':'E74','name':'Gopal Anantharaman — unmatched registration claim','classification':'Additional candidate / registration identity unresolved','is_potential_entrant_unit':True,'identified_work_group':False,'has_review_material_or_manifests':False,'source_record_ids':['E74'],'authors':['Gopal Anantharaman'],'accounts':[],'status':'September 18 says registered with another profile; no result packet received or account/team mapping verified','claims':[],'gaps':['Identify the alternate profile and actual team before merging; no submitted result or repository found'],'repo':None,'immutable_commit':None,'records':[{'record_id':'E74','name':'Gopal Anantharaman','reply_route':gopal['url'],'source_evidence_files':['OpenMath-library-ui-source.json'],'latest_evidence':gopal['text']}],'leaderboard_runs':[],'score_policy':None,'archived_collections':[]})
ROOT.mkdir(exist_ok=True)
if (ROOT/'catalogue.sqlite').exists():raise RuntimeError('Existing catalogue found. Use an explicit incremental import; do not overwrite user notes.')
db=sqlite3.connect(ROOT/'catalogue.sqlite');db.row_factory=sqlite3.Row
db.executescript('''
PRAGMA foreign_keys=ON;
CREATE TABLE teams(id TEXT PRIMARY KEY,name TEXT,aliases TEXT,status TEXT,potential INTEGER,overview TEXT,record_ids TEXT);
CREATE TABLE files(id INTEGER PRIMARY KEY,team_id TEXT REFERENCES teams(id),category TEXT,topic TEXT,basis TEXT,original_path TEXT,local_path TEXT,archive_path TEXT,archive_member TEXT,bytes INTEGER,sha256 TEXT,crc32 TEXT,version TEXT,source TEXT,verification TEXT);
CREATE INDEX files_team_category ON files(team_id,category,original_path);
CREATE INDEX files_team_topic ON files(team_id,topic);
CREATE TABLE archives(id INTEGER PRIMARY KEY,team_id TEXT,local_path TEXT,sha256 TEXT,member_count INTEGER,version TEXT,source TEXT);
CREATE TABLE notes(team_id TEXT PRIMARY KEY REFERENCES teams(id),body TEXT);
''')
all_groups={g['group_id']:g for g in groups}
all_groups['EVENT']={'group_id':'EVENT','name':'Event sources and unmatched correspondence','status':'Shared rules, source snapshots and invitations; not a contestant','source_record_ids':[],'accounts':[],'claims':[],'gaps':[],'is_potential_entrant_unit':False}
for gid,g in all_groups.items():
    folder=ROOT/'contestants'/gid;folder.mkdir(parents=True,exist_ok=True)
    for key in CATEGORIES:(folder/key).mkdir(exist_ok=True)
    overview='\n'.join([g['name'],'Updated: '+NOW,'Status: '+g['status'],'Records: '+', '.join(g['source_record_ids']),'Authors: '+', '.join(str(a) for a in g.get('authors',[])),'Accounts: '+', '.join(g.get('accounts',[])),'','RESULTS / CLAIMS (not independently judged)',*g.get('claims',[]),'','MISSING MATERIAL / ADMISSION QUESTIONS',*g.get('gaps',[]),'','Repository: '+str(g.get('repo') or 'Not delivered / not designated'),'Collected revision: '+str(g.get('immutable_commit') or 'Not designated'),'','Classification is based on file paths, names and source context. It does not certify the mathematical claims.'])
    if g.get('score_policy'):overview+='\n\nLeanification exception: five contributors approved by user. Adjusted overall score = 0.8 × raw overall score; both scores unassigned. Organizer acknowledgment not verified.'
    (folder/'TEAM.txt').write_text(overview,encoding='utf-8')
    clean={k:v for k,v in g.items() if k not in ('records','archived_collections')}
    clean['source_routes']=[{'record_id':r['record_id'],'route':r.get('reply_route'),'latest_evidence':r.get('latest_evidence'),'receipt_notes':r.get('receipt_notes')} for r in g.get('records',[])]
    dump(folder/'TEAM.json',clean)
    db.execute('INSERT INTO teams VALUES(?,?,?,?,?,?,?)',(gid,g['name'],' '.join(g.get('accounts',[])),g['status'],int(g.get('is_potential_entrant_unit',False)),overview,json.dumps(g['source_record_ids'])))

seen=set(); archived_keys=set();archive_checks=[];unavailable=[]
def insert_file(gid,path,local='',archive='',member='',size=0,digest='',crc='',version='',source='',verification='',category=None,topic=None,basis=None):
    token=(gid,local or archive,member)
    if token in seen:return
    seen.add(token);cat,top,why=classify(path)
    db.execute('INSERT INTO files(team_id,category,topic,basis,original_path,local_path,archive_path,archive_member,bytes,sha256,crc32,version,source,verification) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)',(gid,category or cat,topic or top,basis or why,path,local,archive,member,size,digest,crc,version,source,verification))

archives=[]
for a in load('OpenMath-late-morning-archive-index.json'):
    archives.append(dict(a,group_id=a['record_id'].split('-')[0],repo=a['repository'],commit=a['immutable_commit'],version='Pinned review snapshot; official acceptance unresolved'))
archives.extend(a for a in load('OpenMath-library-full-archive-index.json') if a.get('retrieved'))
sakana_path=OUT/'OpenMath-morning-artifacts/Math_Competition_Completed_Results_Submission_Bundle.zip'
archives.append({'group_id':'E02','repo':'SakanaAI/autolab-100','commit':'email ZIP','archive_path':str(sakana_path),'archive_sha256':sha(sakana_path),'version':'Email supplement received 06:19:17 CEST, after cutoff; distinct from on-time PDF','source_url':'https://mail.google.com/mail/u/0/#all/1a0fffd2419ec392'})
for a in archives:
    gid=a['group_id'];original=pathlib.Path(a['archive_path']);dest=ROOT/'contestants'/gid/'13-archives'/original.name
    shutil.copy2(original,dest);digest=sha(dest);assert digest==a['archive_sha256'],str(original)
    rel=dest.relative_to(ROOT).as_posix();source=a.get('source_url','https://github.com/'+a['repo']);version=a['version']
    with zipfile.ZipFile(dest) as z:
        members=[i for i in z.infolist() if not i.is_dir()]
        for i in members:
            parts=pathlib.PurePosixPath(i.filename).parts
            path='/'.join(parts[1:]) if len(parts)>1 else i.filename
            insert_file(gid,path,archive=rel,member=i.filename,size=i.file_size,crc=f'{i.CRC:08x}',version=version+' | '+a.get('commit',''),source=source,verification='Original archive SHA-256 verified; ZIP member CRC recorded; not mathematical validation')
            archived_keys.add((a['repo'].lower(),a.get('commit',''),path))
    insert_file(gid,original.name,local=rel,size=dest.stat().st_size,digest=digest,version=version,source=source,verification='Original archive SHA-256 verified',category='13-archives')
    db.execute('INSERT INTO archives(team_id,local_path,sha256,member_count,version,source) VALUES(?,?,?,?,?,?)',(gid,rel,digest,len(members),version,source))
    archive_checks.append({'team_id':gid,'path':rel,'sha256':digest,'members':len(members),'version':version})
    print(gid+' indexed '+str(len(members))+' archived files',flush=True)

repo_map={g['repo'].lower():g['group_id'] for g in groups if g.get('repo')}
repo_map['casimirknights/ramtastic']='E07'
def copy_file(gid,original,original_path,source,version,expected=None,category=None,topic=None,preservation='Saved original or separately labelled source extraction'):
    p=pathlib.Path(original)
    if not p.exists():unavailable.append({'team_id':gid,'path':str(p),'reason':'Collected index references a file missing on disk'});return
    cat,top,_=classify(original_path);cat=category or cat;digest=sha(p)
    if expected:assert digest==expected,str(p)
    name=re.sub(r'[^\w. -]','_',pathlib.PurePosixPath(original_path).name)[:100] or 'file'
    identity=hashlib.sha256((str(p.resolve())+'|'+gid).encode()).hexdigest()[:12]
    dest=ROOT/'contestants'/gid/cat/(identity+'-'+name)
    if not dest.exists():shutil.copy2(p,dest)
    insert_file(gid,original_path,local=dest.relative_to(ROOT).as_posix(),size=dest.stat().st_size,digest=digest,version=version,source=source,verification=preservation,category=cat,topic=topic or top)

for name in ['OpenMath-morning-public-artifact-index.json','OpenMath-morning-supplement-index.json']:
    for a in load(name,[]):
        if not a.get('retrieved'):continue
        gid=repo_map.get(a['repo'].lower(),'EVENT')
        if (a['repo'].lower(),a.get('commit',''),a['path']) in archived_keys:continue
        copy_file(gid,a['local_path'],a['path'],a.get('url',name),'Earlier saved revision '+str(a.get('commit','')),a.get('sha256'),preservation='Downloaded source file SHA-256 verified')

# Exact email bodies and received filenames, not merely search snippets.
messages=[m for b in load('OpenMath-library-email-readback.json')['batches'] for m in b['responses']]
address_map={};thread_map={}
for g in groups:
    for r in g.get('records',[]):
        query=r.get('inbox_query') or ''
        for address in re.findall(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',query):address_map.setdefault(address.lower(),set()).add(g['group_id'])
        route=r.get('reply_route') or ''
        match=re.search(r'/#(?:sent|all|inbox)/([0-9a-f]+)',route)
        if match:thread_map[match.group(1)]=g['group_id']
address_map.update({k:{v} for k,v in {'[REDACTED CONTACT]':'E17','[REDACTED CONTACT]':'E10','[REDACTED CONTACT]':'E10','[REDACTED CONTACT]':'E06','[REDACTED CONTACT]':'E06','[REDACTED CONTACT]':'E02','[REDACTED CONTACT]':'E02','[REDACTED CONTACT]':'E02','[REDACTED CONTACT]':'E57','[REDACTED CONTACT]':'E03','[REDACTED CONTACT]':'E05','[REDACTED CONTACT]':'E08'}.items()})
def plain_payload(p):
    if p.get('filename'):return ''
    body=p.get('body')or{};value=body.get('content')
    if value is None:
        encoded=body.get('base64_url_content')or body.get('data')
        if encoded:value=base64.urlsafe_b64decode(encoded+'='*((-len(encoded))%4)).decode('utf-8',errors='replace')
    text=str(value or '')
    if p.get('mime_type')=='text/html':
        text=re.sub(r'<(?:br|/div|/p)[^>]*>','\n',text,flags=re.I);text=html.unescape(re.sub(r'<[^>]+>','',text))
    children=p.get('parts')or[]
    # Prefer plain text in alternatives; preserve other material in source JSON.
    if p.get('mime_type')=='multipart/alternative':
        text+='\n'+plain_payload(next((c for c in children if c.get('mime_type')=='text/plain'),children[0] if children else {}))
    else:text+='\n'+'\n'.join(plain_payload(c)for c in children)
    return text
mail_group={};mail_bodies={};shared=[]
for m in messages:
    headers={x['name'].lower():x['value']for x in m['payload']['headers']};subject=headers.get('subject','')
    if 'Kobon triangle manuscript following' in subject:continue
    addresses=re.findall(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',' '.join(headers.get(k,'')for k in ['from','to','cc']))
    matches=set.union(set(),*(address_map.get(a.lower(),set())for a in addresses))
    if not matches and m.get('thread_id') in thread_map:matches.add(thread_map[m['thread_id']])
    if not matches:matches={'EVENT'}
    body=plain_payload(m['payload']);mail_group[m['id']]=matches;mail_bodies[m['id']]=body
    for gid in matches:
        folder=ROOT/'contestants'/gid/'12-correspondence';p=folder/('email-'+m['id']+'.txt')
        p.write_text('\n'.join([subject,'Date: '+headers.get('date',''),'From: '+headers.get('from',''),'To: '+headers.get('to',''),'Receipt/message id: '+m['id'],'','BODY',body]),encoding='utf-8')
        insert_file(gid,p.name,local=p.relative_to(ROOT).as_posix(),size=p.stat().st_size,digest=sha(p),source='https://mail.google.com/mail/u/0/#all/'+m['id'],version='Received/sent correspondence; original timestamp retained',verification='Connector-decoded MIME text, not an original .eml byte stream',category='12-correspondence')
        if gid=='EVENT':shared.append({'name':headers.get('from',''),'subject':subject,'message':m['id'],'kind':'Unmatched invitation/organizer correspondence; not presumed entrant'})

# Original supported attachments are fetched while their connector URLs are valid.
attachment_downloads=[]
for wrapped in load('OpenMath-library-original-attachment-downloads.json',[])+load('OpenMath-library-inline-attachment-downloads.json',[]):
    if wrapped['status']!='fulfilled':continue
    row=wrapped['value'];request=row['task'];data=row['result'].get('structuredContent')or{};filename=request['filename']
    if filename not in ('COMPLETION.json','COMPLETION.md','VALIDATION.md','OPENMATH_SUBMISSION.md','Math_Competition_Completed_Results_Submission.pdf','competition_handbook_final.pdf','lean-unitary.png'):continue
    gids={'E17'}if request['message_id']=='1a0ffb744e576946'else {'E03'}if filename=='lean-unitary.png'else {'E02'}if filename.startswith('Math_Competition')else {'EVENT'}
    uri=data.get('file_uri')or{};url=uri.get('download_url')
    for gid in gids:
        category=classify(filename)[0];p=ROOT/'contestants'/gid/category/('attachment-'+request['message_id']+'-'+filename)
        status={'team_id':gid,'message_id':request['message_id'],'filename':filename}
        try:
            if not url:raise ValueError('Connector returned no original-file download URL')
            with urllib.request.urlopen(url,timeout=30)as response:p.write_bytes(response.read())
            expected=data.get('size_bytes')
            status.update(retrieved=True,path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p),declared_attachment_bytes=expected)
            insert_file(gid,filename,local=p.relative_to(ROOT).as_posix(),size=p.stat().st_size,digest=sha(p),version='Email attachment; received timestamp in corresponding email',source='https://mail.google.com/mail/u/0/#all/'+request['message_id'],verification='Original-file URI downloaded; SHA-256 recorded',category=category)
        except Exception as exc:status.update(retrieved=False,error=str(exc))
        attachment_downloads.append(status)

for a in load('OpenMath-morning-attachment-index.json',[]):
    if a['name'].endswith('.zip'):continue
    gid='E17' if a.get('message_id')=='1a0ffb744e576946'else 'E02'
    if any(x.get('retrieved')and x['team_id']==gid and x['filename']==a['name']for x in attachment_downloads):continue
    copy_file(gid,a['local_path'],a['name'],'https://mail.google.com/mail/u/0/#all/'+a.get('message_id',''),'Earlier preserved email attachment',a.get('sha256'),preservation=a.get('preservation','Decoded attachment extraction; original byte identity not verified'))

# Save UI captures separately from originals; retain private-file extraction limitations.
for row in load('OpenMath-morning-Chandragupt-private-source.json',[]):
    url=row['url'];path=url.split('/blob/')[-1].split('/',1)[-1];name=hashlib.sha256(url.encode()).hexdigest()[:12]+'-'+pathlib.PurePosixPath(path).name+'.UI-extraction.txt'
    p=ROOT/'contestants/E04'/classify(path)[0]/name;p.write_text('Source: '+url+'\nObserved: '+str(row.get('checked_at'))+'\nRepresentation: rendered GitHub UI extraction; may be incomplete, not original bytes.\n\n'+row['text'],encoding='utf-8')
    insert_file('E04',path+' [UI text capture]',local=p.relative_to(ROOT).as_posix(),size=p.stat().st_size,digest=sha(p),version='Observed private revision; final designation unconfirmed',source=url,verification='UI-derived text, not original bytes; truncation possible',category=classify(path)[0])

for sourcefile in ['OpenMath-morning-ui-source.json','OpenMath-late-morning-ui-source.json','OpenMath-library-ui-source.json']:
    for n,row in enumerate(load(sourcefile,[])):
        label=row.get('source')or row.get('kind','');text=row.get('text','')
        if any(word in label.lower()for word in ('jury','hacknation','company','superradiant','wispr','signal')):continue
        gid=row.get('group_id')
        if not gid:
            for needle,target in [('Woohyuk','E08'),('Raj','E09'),('Chandragupt','E04'),('Sri','E69'),('Gopal','E74'),('Luke','E01'),('Frederik','E12'),('Sakana','E02')]:
                if needle.lower()in label.lower():gid=target;break
        if gid not in all_groups:gid='EVENT'
        # Conversation list contains irrelevant personal snippets; team captures start after the list.
        if 'LinkedIn' in label and 'Cargar más conversaciones\n'in text:text=text.split('Cargar más conversaciones\n',1)[1]
        if 'WhatsApp' in label and 'Use WhatsApp on your phone' in text:text=text[text.index('Use WhatsApp on your phone'):]
        if 'Terry' in label:continue  # No entry; retained roster already records future interest, without Tesla obligations.
        p=ROOT/'contestants'/gid/'12-correspondence'/(sourcefile.replace('.json','')+'-'+str(n)+'.txt')
        p.write_text(label+'\nSource: '+str(row.get('url',''))+'\nObserved: '+str(row.get('checked_at')or row.get('observed'))+'\n\n'+text,encoding='utf-8')
        insert_file(gid,p.name,local=p.relative_to(ROOT).as_posix(),size=p.stat().st_size,digest=sha(p),source=str(row.get('url','')),version='Source snapshot; read scope shown in capture',verification='Visible UI source text; not an uploaded original',category='12-correspondence')

for sourcefile in ['OpenMath-morning-event-projects.json','OpenMath-morning-leaderboards.json','OpenMath-late-morning-leaderboards.json','OpenMath-library-hill-results.json','OpenMath-Luma-roster.json']:
    p=OUT/sourcefile
    if p.exists():copy_file('EVENT',p,sourcefile,sourcefile,'Shared event/hill source snapshot',category='12-correspondence')
for g in groups:
    gid=g['group_id'];runs=g.get('leaderboard_runs',[])
    if runs:
        p=ROOT/'contestants'/gid/'06-data/hill-results.json';dump(p,runs)
        insert_file(gid,'hill-results.json',local=p.relative_to(ROOT).as_posix(),size=p.stat().st_size,digest=sha(p),source='Collected official hill leaderboards',version='Reported successful runs, not all private experiments',verification='Leaderboard values as observed; no independent evaluation',category='06-data')
    if gid=='E02':
        for name in ['CLAIMS.json','focus-candidates.json']:
            p=OUT/'OpenMath-by-team/E02'/name
            if p.exists():copy_file(gid,p,name,'Sakana source ZIP claim/focus dossiers','Email supplement after cutoff',category='01-submission')
    folder=ROOT/'contestants'/gid
    missing=list(g.get('gaps',[]))
    if gid=='E04':missing.append('Original private repository files not downloaded; available UI captures are labelled and may truncate code.')
    if gid=='E07':missing.append('bosonic_arrow linked repository returned GitHub 404. Ramtastic public lead collected; not confirmed as a final submission.')
    if gid=='E58':missing.append('Linked busybeaver repository is empty (GitHub 409); no files exist to retrieve there.')
    if gid=='E17':missing.append('Actual advertised 27MB source ZIP/Git bundle was not attached; only the four delivered manifests can be collected.')
    if not db.execute('SELECT 1 FROM files WHERE team_id=? AND category NOT IN (?,?) LIMIT 1',(gid,'12-correspondence','13-archives')).fetchone():missing.append('No contestant work file received or accessible in the reviewed sources. Hill result/registration/contact evidence is preserved separately.')
    (folder/'MISSING-MATERIALS.txt').write_text('\n'.join(missing) or 'No additional collection gap recorded; admission and mathematical review are separate.',encoding='utf-8')

db.commit()
# Every file gets a category ledger within its team, including members kept inside local ZIPs.
for gid in all_groups:
    for cat in CATEGORIES:
        rows=db.execute('SELECT id,original_path,topic,bytes,version,local_path,archive_path,archive_member,sha256,crc32,basis,source FROM files WHERE team_id=? AND category=? ORDER BY original_path,id',(gid,cat))
        p=ROOT/'contestants'/gid/cat/'FILE-INDEX.csv'
        with p.open('w',encoding='utf-8-sig',newline='')as f:
            writer=csv.writer(f);writer.writerow(['id','original_path','topic','bytes','version','local_file','local_archive','archive_member','sha256','crc32','classification_basis','source'])
            for row in rows:writer.writerow(list(row))
summary={'created_at':NOW,'grouped_contestant_contact_records':len(groups),'source_contact_accounts':sum(len(g['source_record_ids'])for g in groups),'provisional_potential_entrant_units':sum(g.get('is_potential_entrant_unit',False)for g in groups),'official_team_count':None,'files':db.execute('SELECT COUNT(*)FROM files').fetchone()[0],'archive_members':sum(a['members']for a in archive_checks),'archive_count':len(archive_checks),'categories':dict(db.execute('SELECT category,COUNT(*)FROM files GROUP BY category').fetchall()),'contestant_work_files':dict(db.execute('SELECT team_id,COUNT(*) FROM files WHERE category NOT IN ("12-correspondence","13-archives") GROUP BY team_id').fetchall()),'new_contact':'E74 Gopal registration identity unresolved','attachment_downloads':attachment_downloads,'unavailable_collected_files':unavailable,'all_original72_preserved':all(any(f'E{i:02d}'in g['source_record_ids']for g in groups)for i in range(1,73)),'all33_extra_accounts_preserved':all(any(f'E{i:02d}'in g['source_record_ids']for g in groups)for i in range(34,67)),'contestant_code_executed':False,'outbound_messages':False,'classification':'Path/name inferred and editable; originals retained'}
assert summary['all_original72_preserved']and summary['all33_extra_accounts_preserved']
assert db.execute('SELECT COUNT(*)FROM files WHERE archive_member IS NOT NULL AND archive_member!=""').fetchone()[0]==summary['archive_members']
assert not unavailable, unavailable
dump(ROOT/'collection-summary.json',summary);dump(ROOT/'archive-provenance.json',archive_checks);dump(ROOT/'unmatched-correspondence-index.json',shared)
dump(ROOT/'contestants.json',[{k:v for k,v in g.items()if k not in ('records','archived_collections')}for g in groups])
readme=f'''OPENMATH JUDGING — LOCAL CONTESTANT LIBRARY
Created {NOW}

Open the Desktop shortcut “OpenMath Judging”, or run judging_app.py with the bundled Python runtime.
This is a native desktop app; it uses local files and SQLite, without a web server or website.

Choose a contestant/team on the left. The Team tab shows exact claims, roster and gaps.
Choose a purpose category, then the Classified files tab. Search by filename, source, version or mathematical topic.
Every received local file and every original ZIP member has a catalogue entry and category index.
Select any file for a text preview. Double-click or “Save selected file as…” saves the complete file.
No contestant scripts, Lean builds or executables are run by this app.
Use Apply classification to correct an inferred category/topic, and Review notes to save private notes.

There are {len(groups)} grouped contestant/contact records covering {summary['source_contact_accounts']} source identities, plus shared event sources.
All original 72 records and all 33 extra accounts are retained. Gopal is an additional unmatched registration claim.
These contact/account groups are not a verified official team count.
{summary['files']:,} local file entries include {summary['archive_members']:,} members of {summary['archive_count']} original archives.
Large datasets remain fully local inside their archives, browsable individually, avoiding hundreds of thousands of duplicated extracted files.
The per-team numbered folders contain loose files and FILE-INDEX.csv ledgers for every archive member.

VERSION AND RECEIPT RULES
Pinned deadline versions, earlier snapshots and later public revisions are retained separately.
An accessible repository is not automatically an official final submission or accepted award entry.
Sakana on-time PDF and late source ZIP remain distinct. Matt/Jamie newer public revisions are labelled separately.
Leanification: five contributors approved by user; adjusted overall score = 0.8 × raw overall score. Neither score assigned.

COLLECTION LIMITS
Qichao's advertised source ZIP/Git bundle was not attached; only actual received manifests are included.
Chandragupt private original download remains blocked; labelled UI captures preserved, possible truncation visible.
bosonic_arrow is inaccessible and sasap91/busybeaver is empty. Undelivered/private hill artifacts remain gaps.
Successful public hill boards are retained; they do not expose every private climb/experiment/artifact.
No mathematical verification or award decision is implied by file classification or archive integrity.
Unrelated company, billing, visa and personal obligations are excluded from this library.
'''
(ROOT/'START-HERE.txt').write_text(readme,encoding='utf-8')
db.close();print(json.dumps({k:v for k,v in summary.items()if k not in ('attachment_downloads','contestant_work_files','categories')},ensure_ascii=False,indent=2))
