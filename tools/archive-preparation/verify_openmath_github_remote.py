"""Verify public repository tree and release digests, without reading auth tokens."""
from pathlib import Path
import subprocess, json, hashlib, urllib.request, datetime, base64
ROOT=Path(__file__).resolve().parent; DEST=ROOT/'OpenMath-GitHub-Archive'
REPO='alejandrozu/openmath-2026-judging';TAG='snapshot-2026-10-03'
def api(path):return json.loads(subprocess.check_output(['gh','api',path],text=True,encoding='utf8'))
def git(*args):return subprocess.check_output(['git',*args],cwd=DEST,text=True,encoding='utf8').strip()
manifest=json.loads((DEST/'publication-manifest.json').read_text(encoding='utf8'))
repo=api('repos/'+REPO);assert repo['private'] is False and repo['visibility']=='public'
tree=api('repos/'+REPO+'/git/trees/main?recursive=1');assert tree['truncated'] is False
remote={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
local={}
for line in git('ls-tree','-r','HEAD').splitlines():
    meta,path=line.split('\t',1);local[path]=meta.split()[2]
assert remote==local,'Remote Git tree does not exactly match local commit'
release=api('repos/'+REPO+'/releases/tags/'+TAG);assets={x['name']:x for x in release['assets']};checks=[]
for expected in manifest['assets']:
    actual=assets[expected['name']];assert actual['state']=='uploaded';assert actual['size']==expected['bytes']
    algorithm_hash=actual.get('digest')
    if algorithm_hash:
        assert algorithm_hash=='sha256:'+expected['sha256'],'Remote asset digest mismatch'
    else:
        h=hashlib.sha256()
        with urllib.request.urlopen(actual['browser_download_url']) as stream:
            for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
        assert h.hexdigest()==expected['sha256'],'Downloaded asset digest mismatch'
    checks.append({'name':expected['name'],'bytes':expected['bytes'],'sha256':expected['sha256'],'verified_remote':True})
assert set(assets)=={x['name'] for x in manifest['assets']}
for e in manifest['files']:
    if e['storage']=='git':assert e['path'] in remote
    else:assert e['asset'] in assets
# Anonymous API access independently verifies public visibility.
request=urllib.request.Request('https://api.github.com/repos/'+REPO,headers={'User-Agent':'OpenMath-archive-verification','Accept':'application/vnd.github+json'})
with urllib.request.urlopen(request) as stream:anonymous=json.load(stream)
assert anonymous['private'] is False
readme=api('repos/'+REPO+'/contents/README.md');assert base64.b64decode(readme['content'])==(DEST/'README.md').read_bytes()
report={'verified_at':datetime.datetime.now().astimezone().isoformat(timespec='seconds'),'repository':repo['html_url'],'public':True,'anonymous_access_verified':True,'commit':git('rev-parse','HEAD'),'git_tree_exact_match':True,'git_blob_count':len(remote),'publication_paths':len(manifest['files']),'catalogue_counts':manifest['counts'],'release':release['html_url'],'release_assets':checks,'all_manifest_paths_have_verified_git_or_release_storage':True,'mathematical_acceptance':'Preliminary proposals; not final scoring or proof acceptance','permission':'User confirmed all affected author permissions; original third-party ownership preserved'}
(ROOT/'outputs/OpenMath-GitHub-publication-verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps(report,ensure_ascii=False,indent=2))
