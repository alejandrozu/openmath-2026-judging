import pathlib, json, urllib.request, zipfile, hashlib, datetime, concurrent.futures, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT = pathlib.Path(__file__).resolve().parent / 'outputs'
DEST = OUT / 'OpenMath-library-full-archives'
DEST.mkdir(exist_ok=True)
def load(name): return json.loads((OUT/name).read_text(encoding='utf-8-sig'))
groups = load('OpenMath-team-directory-current.json')['groups']
plans = []
already = {(a['repository'].lower(), a['immutable_commit']) for a in load('OpenMath-late-morning-archive-index.json')}
for g in groups:
    if g['repo'] and g['immutable_commit'] and g['group_id'] not in ('E04','E02'):
        key=(g['repo'].lower(),g['immutable_commit'])
        if key not in already:
            plans.append({'group_id':g['group_id'],'repo':g['repo'],'commit':g['immutable_commit'],'version':'Pinned collected revision; final designation governed by team receipt'})
for row in load('OpenMath-library-repo-commits.json'):
    if row['status']!='fulfilled': continue
    obj=row['value']; res=obj['result']
    if res.get('isError'): continue
    try: data=json.loads(res['structuredContent']['content'])
    except Exception: continue
    if not isinstance(data,list) or not data: continue
    commit=data[0]['sha']; repo=obj['repo']
    g=next((g for g in groups if g['repo'] and g['repo'].lower()==repo.lower()),None)
    if not g and repo=='CasimirKnights/Ramtastic': g=next(g for g in groups if g['group_id']=='E07')
    if not g: continue
    if not any(p['repo'].lower()==repo.lower() and p['commit']==commit for p in plans) and (repo.lower(),commit) not in already:
        plans.append({'group_id':g['group_id'],'repo':repo,'commit':commit,'commit_date':data[0]['commit']['committer']['date'],'version':'Latest public revision collected separately; not an author-designated final'})
(OUT/'OpenMath-library-archive-plan.json').write_text(json.dumps(plans,indent=2),encoding='utf-8')
def fetch(p):
    target=DEST/(p['group_id']+'-'+p['repo'].replace('/','-')+'-'+p['commit']+'.zip')
    row=dict(p,source_url='https://codeload.github.com/'+p['repo']+'/zip/'+p['commit'])
    try:
        if not target.exists():
            request=urllib.request.Request(row['source_url'],headers={'User-Agent':'OpenMath-local-readonly-archive'})
            with urllib.request.urlopen(request,timeout=90) as response, target.with_suffix('.partial').open('wb') as output:
                while block:=response.read(1024*1024): output.write(block)
            target.with_suffix('.partial').replace(target)
        digest=hashlib.sha256(target.read_bytes()).hexdigest()
        with zipfile.ZipFile(target) as archive:
            members=[i for i in archive.infolist() if not i.is_dir()]
            bad=archive.testzip()
            if bad: raise ValueError('CRC failed: '+bad)
            row.update(archive_path=str(target),archive_bytes=target.stat().st_size,archive_sha256=digest,file_count=len(members),uncompressed_bytes=sum(i.file_size for i in members),all_member_crc_verified=True)
        row['retrieved']=True
    except Exception as exc: row.update(retrieved=False,error=str(exc))
    row['checked_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(json.dumps({k:v for k,v in row.items() if k not in ('source_url','archive_path')},ensure_ascii=False),flush=True)
    return row
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    rows=list(pool.map(fetch,plans))
(OUT/'OpenMath-library-full-archive-index.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2),encoding='utf-8')
print('Complete: '+str(sum(x['retrieved'] for x in rows))+'/'+str(len(rows)),flush=True)
