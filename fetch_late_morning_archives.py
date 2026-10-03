import pathlib, urllib.request, zipfile, hashlib, json, concurrent.futures, datetime, sys
sys.stdout.reconfigure(encoding='utf-8')
root=pathlib.Path(__file__).resolve().parent/'outputs'
dest=root/'OpenMath-late-morning-artifacts'; dest.mkdir(exist_ok=True)
jobs=[('E08','lavaskiller/openmath-2026-htpeo','76c63b8e425e551a930060a6871b84fe3b4780db'),('E09','srirangam-r/kobon_triangles','eed14659a9b2f4ca12777da5d557f2b620b966f6'),('E12-cloud','FSvOAI/Heilbronn','94f6a70e804f64b904a215d119802ca91df626b4'),('E12-results','FSvOAI/Heilbronn','9d1d55531855fd275266ac33ab97e3baaa95078c')]
def get(job):
 rid,repo,sha=job; url=f'https://codeload.github.com/{repo}/zip/{sha}'; target=dest/f'{rid}-{sha}.zip'
 req=urllib.request.Request(url,headers={'User-Agent':'OpenMath read-only artifact collection'})
 if not target.exists():
  with urllib.request.urlopen(req,timeout=120) as src, target.open('wb') as out:
   while chunk:=src.read(1024*1024): out.write(chunk)
 index=[]; extracted=[]
 with zipfile.ZipFile(target) as z:
  for item in z.infolist():
   if item.is_dir(): continue
   rel=pathlib.PurePosixPath(item.filename); parts=rel.parts[1:]
   if not parts or any(p in ('..','') for p in parts) or rel.is_absolute(): raise ValueError('Unsafe archive member')
   path='/'.join(parts)
   selected=rid in ('E08','E09') or ('summary' in path.lower() or 'report' in path.lower() or path.endswith('DONE') or 'progress.log' in path or 'result_vertices' in path or 'README' in path)
   record={'path':path,'bytes':item.file_size,'crc':item.CRC,'retrieved_in_archive':True}
   if selected:
    data=z.read(item); output=dest/rid/sha/path; output.parent.mkdir(parents=True,exist_ok=True); output.write_bytes(data)
    record.update(local_path=str(output),sha256=hashlib.sha256(data).hexdigest()); extracted.append(record)
   index.append(record)
 result={'record_id':rid,'repository':repo,'immutable_commit':sha,'source_url':url,'archive_path':str(target),'archive_bytes':target.stat().st_size,'archive_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'file_count':len(index),'extracted_count':len(extracted),'files':index,'executed':False,'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 (root/f'OpenMath-late-morning-{rid}-archive-index.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
 print(json.dumps({k:v for k,v in result.items() if k!='files'}),flush=True)
 return result
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 results=list(pool.map(get,jobs))
(root/'OpenMath-late-morning-archive-index.json').write_text(json.dumps([{k:v for k,v in r.items() if k!='files'} for r in results],ensure_ascii=False,indent=2),encoding='utf-8')
