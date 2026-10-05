"""Extract byte-pinned Petersen color data and independently check finite windows."""
from pathlib import Path
import ast,hashlib,json,re
BASE=Path(__file__).parent
SOURCE=BASE/'verification/builds/htpeo-dms-current'
DATA=BASE/'dms_gp_periodic_certificate_data.json'

def literal(text,name):
    start=re.search(r'def '+name+r'\s*:.*?:=\s*',text).end()
    assert text[start]=='['
    depth=0
    for j in range(start,len(text)):
        depth+=(text[j]=='[')-(text[j]==']')
        if depth==0:return ast.literal_eval(text[start:j+1])
    raise ValueError(name)

def extracted():
    rows=[]
    plan=json.loads((SOURCE/'build-plan.json').read_text(encoding='utf-8'))
    planned={x['module']:x for x in plan['modules']}
    for k in range(1,16):
        tp=SOURCE/f'GPn{k}T.lean';ap=SOURCE/f'GPn{k}.lean'
        t=tp.read_text(encoding='utf-8');a=ap.read_text(encoding='utf-8')
        match=re.search(r'def idx.*?if J < n - n % (\d+) - (\d+)',t,re.S)
        period,seam=map(int,match.groups())
        threshold,nmin=map(int,re.search(r'def chi.*?if n < (\d+) then \(smallTab.getD \(n - (\d+)\)',t,re.S).groups())
        cap,nmin2=map(int,re.search(r'theorem Wsmall : ∀ n, n < (\d+) → (\d+) ≤ n',a).groups())
        rep=int(re.search(r"j' < (\d+) \+ n %",a).group(1))
        assert nmin==nmin2
        locators={}
        for mod,path,text in [(f'GPn{k}T',tp,t),(f'GPn{k}',ap,a)]:
            digest=hashlib.sha256(path.read_bytes()).hexdigest()
            assert digest==planned[mod]['sha256']
            locators[mod]={'source':planned[mod]['source'],'sha256':digest,
                'lines':{name:1+text[:re.search(r'(?m)^(?:def|theorem) '+name+r'\b',text).start()].count('\n')
                    for name in (['tabs','smallTab','idx','chi'] if mod.endswith('T') else ['Wsmall','rep','star5'])}}
        rows.append({'k':k,'n_min':nmin,'period':period,'seam_base':seam,'periodic_threshold':threshold,
            'finite_cap_exclusive':cap,'representative_base':rep,'window_block_count':3*k+1,
            'tabs':literal(t,'tabs'),'smallTab':literal(t,'smallTab'),'locators':locators})
    source_directories={str(Path(loc['source']).parent).replace('\\','/') for row in rows for loc in row['locators'].values()}
    assert len(source_directories)==1,source_directories
    return {'scope':'Exact literal data for GP(n,k), 1≤k≤15, n≥2k+1, except GP(3,1).',
        'source_commit':plan['commit'],'source_directory':next(iter(source_directories)),'families':rows}

def chi(row,n,j):
    if n<row['periodic_threshold']:return row['smallTab'][n-row['n_min']][j]
    p,s=row['period'],row['seam_base'];cut=n-n%p-s
    idx=j%p if j<cut else p+j-cut
    return row['tabs'][n%p][idx]

def half_edges(k,v):
    j,t=v
    if t==0:return [((j,0),(j+1,0)),((j-1,0),(j-1,0)),((j,1),(j,1))]
    return [((j,1),(j,0)),((j,2),(j+k,1)),((j-k,2),(j-k,1))]

def window_ok(row,n,start):
    k=row['k']
    def color(e):return chi(row,n,(start+e[0])%n)[e[1]]
    for t in [0,1]:
        center=(2*k,t)
        incident=half_edges(k,center)
        for e2,z2 in incident:
            for e3,z3 in incident:
                if e2==e3:continue
                assert color(e2)!=color(e3),(row['k'],n,start,'improper',e2,e3)
                for e1,_ in half_edges(k,z2):
                    if color(e1)!=color(e3):continue
                    for e4,_ in half_edges(k,z3):
                        assert color(e4)!=color(e2),(row['k'],n,start,'alternating',e1,e2,e3,e4)

def graph_ok(row,n):
    k=row['k'];edges=[];colors=[];inc=[[] for _ in range(2*n)]
    for j in range(n):
        ends=[(2*j,2*((j+1)%n)),(2*j,2*j+1),(2*j+1,2*((j+k)%n)+1)]
        for typ,(u,v) in enumerate(ends):
            eid=len(edges);edges.append((u,v));colors.append(chi(row,n,j)[typ]);inc[u].append(eid);inc[v].append(eid)
    for v in range(2*n):assert len({colors[e] for e in inc[v]})==len(inc[v])==3
    def visit(v,trail,path):
        if len(trail)==4:
            assert len({colors[e] for e in trail})>2,(k,n,'bicolored',trail,path)
            return
        for eid in inc[v]:
            if eid in trail:continue
            u,w=edges[eid];other=w if u==v else u
            visit(other,trail+[eid],path+[other])
    for v in range(2*n):visit(v,[],[v])

if DATA.exists() and not SOURCE.exists():data=json.loads(DATA.read_text(encoding='utf-8'))
else:
    data=extracted();temp=DATA.with_suffix('.tmp');temp.write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8');temp.replace(DATA)
report={'scope':'Independent finite local-window and graph coloring checks; universal extension uses the stated representative arithmetic proof. This is not a Lean replay or a historical novelty determination.','source_commit':data['source_commit'],'rows':[],'all_pass':False}
for row in data['families']:
    k,p,s,T,N,B=[row[x] for x in ['k','period','seam_base','periodic_threshold','finite_cap_exclusive','representative_base']]
    assert N==B+p and B%p==0 and B>=T and B>=s+3*k+p
    assert row['n_min']==(4 if k==1 else 2*k+1)
    assert len(row['tabs'])==p and len(row['smallTab'])==T-row['n_min']
    assert all(len(tab)==p+s+r for r,tab in enumerate(row['tabs']))
    assert all(tab[:p]==row['tabs'][0][:p] for tab in row['tabs'])
    assert all(len(tab)==n for n,tab in enumerate(row['smallTab'],row['n_min']))
    assert all(len(c)==3 and all(0<=v<5 for v in c) for tab in row['tabs']+row['smallTab'] for c in tab)
    count=0
    for n in range(row['n_min'],N):
        graph_ok(row,n)
        for j in range(n):window_ok(row,n,j);count+=1
    report['rows'].append({'k':k,'n_min':row['n_min'],'period':p,'seam_base':s,'periodic_threshold':T,
        'finite_cap_exclusive':N,'representative_base':B,'graphs_checked':N-row['n_min'],
        'local_windows_checked':count,'all_pass':True})
    print('GP',k,'finite graphs',N-row['n_min'],'windows',count,'PASS',flush=True)
report['all_pass']=True;report['total_graphs_checked']=sum(r['graphs_checked'] for r in report['rows'])
report['total_windows_checked']=sum(r['local_windows_checked'] for r in report['rows'])
out=BASE/'dms_gp_independent_certificate_audit.json';temp=out.with_suffix('.tmp');temp.write_text(json.dumps(report,indent=2),encoding='utf-8');temp.replace(out)
print(json.dumps({k:report[k] for k in ['all_pass','total_graphs_checked','total_windows_checked']},indent=2))
