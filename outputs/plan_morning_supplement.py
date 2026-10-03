import json,pathlib,re
r=pathlib.Path(__file__).parent
old=json.loads((r/'OpenMath-morning-public-artifact-index.json').read_text())
seen={(x['repo'],x['commit'],x['path']) for x in old}
trees=json.loads((r/'OpenMath-morning-repo-trees-source.json').read_text())
trees+=json.loads((r/'OpenMath-morning-new-account-repo-source.json').read_text())['trees']
jobs=[]
for t in trees:
 repo,sha=t['repo'],t['sha']; tree=json.loads(t['result']['value']['structuredContent']['content'])['tree']
 for b in tree:
  p=b['path']; keep=False
  if b['type']!='blob' or b.get('size',0)>5000000: continue
  if repo=='lazyluca/hyprgraph_containers': keep=p.endswith(('.log','.txt')) or p.startswith('paper/')
  elif repo=='srirangam-r/kobon_triangles': keep=(p.startswith(('proofs/','arrangements/','tools/','checker/')) or p in ['NOVELTY.md','DISCLOSURE.md','CREDITS.md']) or (p.startswith('work/') and p.endswith(('.py','.sh','.json','.md','.txt')) and b.get('size',0)<200000)
  elif repo=='Rohith18p/rsi-kobon-triangles': keep=p.startswith('kobon-triangles/') and p.endswith(('.json','.md','.py','.txt'))
  elif repo=='grandchallenge/MATHSOLVE': keep=p.startswith(('work_packages/OPENMATH_2026/OM26_H7_ERDOS_3/','work_packages/OPENMATH_2026/OM26_H4_COLLATZ_MODULAR_DESCENT/','work_packages/OPENMATH_2026/OM26_H1_KOBON_TRIANGLES/','work_packages/OPENMATH_2026/CONTEST_CANDIDATES/','work_packages/OPENMATH_2026/AUTHORITATIVE_SOURCE_POOL/')) and p.endswith(('.lean','.py','.json','.md','.txt','.yaml','.lock'))
  elif repo=='Koerbser/erdos-3-autolab': keep=p.startswith(('lean/','docs/','harmonic/','hills/')) and p.endswith(('.lean','.py','.json','.md','.txt','.yaml','.toml'))
  elif repo=='FSvOAI/Heilbronn': keep=p.endswith(('.lean','.py','.json','.md','.txt','.pdf'))
  elif repo=='wilsonwu-ai/sundai-erdos-3': keep=p.endswith(('.lean','.md','.json','.txt','.yaml','.py')) or p=='lean-toolchain'
  elif repo=='SHAFF622/Sundai-RL': keep=True
  if keep and (repo,sha,p) not in seen: jobs.append({'repo':repo,'commit':sha,'path':p,'size':b.get('size'),'url':f'https://raw.githubusercontent.com/{repo}/{sha}/{p}'})
(r/'OpenMath-morning-supplement-plan.json').write_text(json.dumps(jobs,indent=2),encoding='utf-8')
print(json.dumps({repo:sum(x['repo']==repo for x in jobs) for repo in sorted(set(x['repo'] for x in jobs))},indent=2))
