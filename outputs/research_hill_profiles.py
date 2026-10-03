import json, urllib.request, concurrent.futures
from pathlib import Path
from datetime import datetime, timezone
root=Path(__file__).resolve().parent
inv=json.loads((root/'OpenMath-complete-team-inventory.json').read_text(encoding='utf-8-sig'))
accounts=[x['account'] for x in inv['leaderboard_accounts'] if not x['mapped_contact']]
def fetch(account):
    url='https://api.github.com/users/'+account
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'OpenMath-entrant-read-only-review'})
        with urllib.request.urlopen(req,timeout=20) as r: p=json.load(r)
        return {'account':account,'source':url,'identity_caution':'Same-handle GitHub profile; AutoLab-to-GitHub ownership needs source confirmation.', 'profile':{k:p.get(k) for k in ['login','name','html_url','bio','blog','email','company','location','public_repos','type']}}
    except Exception as e:return {'account':account,'source':url,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:results=list(pool.map(fetch,accounts))
(root/'OpenMath-hill-public-profiles.json').write_text(json.dumps({'captured':datetime.now(timezone.utc).isoformat(),'profiles':results},ensure_ascii=False,indent=2),encoding='utf-8')
for x in results:
    p=x.get('profile',{})
    print(json.dumps({'account':x['account'],'name':p.get('name'),'blog':p.get('blog'),'email':p.get('email'),'bio':p.get('bio'),'error':x.get('error')},ensure_ascii=True))
