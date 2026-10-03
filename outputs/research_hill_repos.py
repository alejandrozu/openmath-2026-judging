import json,urllib.request,concurrent.futures
from pathlib import Path
root=Path(__file__).resolve().parent
accounts=['hl728','danamouk','n0rang2','rohith18p','octavianboji','vyahhi','kevinsrun','willow2014','advaith-appajodu','ottogin']
def read(a):
 try:
  req=urllib.request.Request('https://api.github.com/users/'+a+'/repos?per_page=100&sort=updated',headers={'User-Agent':'OpenMath-read-only-review'})
  with urllib.request.urlopen(req,timeout=20) as r: p=json.load(r)
  return {'account':a,'repos':[{k:x.get(k) for k in ['name','html_url','description','pushed_at','fork','language']} for x in p]}
 except Exception as e:return {'account':a,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: data=list(pool.map(read,accounts))
(root/'OpenMath-priority-account-repositories.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
for x in data:
 print(json.dumps(x,ensure_ascii=True))
