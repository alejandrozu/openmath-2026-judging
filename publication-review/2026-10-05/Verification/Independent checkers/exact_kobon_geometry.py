"""Reviewer-owned exact bounded-face count. JSON/ZIP data only; no entrant execution."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import gcd,lcm
import json,zipfile,hashlib
BASE=Path(__file__).resolve().parent

def count(raw):
    ls=[]
    for row in raw:
        row=[F(x) for x in row]; q=lcm(*(x.denominator for x in row)); row=[int(q*x) for x in row]
        g=gcd(gcd(abs(row[0]),abs(row[1])),abs(row[2])); row=tuple(x//g for x in row)
        if next(x for x in row if x)<0: row=tuple(-x for x in row)
        ls.append(row)
    assert len(set(ls))==len(ls) and all(a or b for a,b,c in ls)
    pts={}; on=[set() for _ in ls]; parallel=0
    for i,j in combinations(range(len(ls)),2):
        a,b,c=ls[i];d,e,f=ls[j];w=a*e-b*d
        if not w: parallel+=1;continue
        p=(F(b*f-c*e,w),F(c*d-a*f,w));pts[i,j]=p;on[i].add(p);on[j].add(p)
    edges=[]
    for line,vertices in zip(ls,on):
        a,b,_=line; order=sorted(vertices,key=lambda p:b*p[0]-a*p[1])
        edges.append({frozenset((u,v)) for u,v in zip(order,order[1:])})
    triangles=[]
    for i,j,k in combinations(range(len(ls)),3):
        if any(t not in pts for t in ((i,j),(i,k),(j,k))): continue
        x,y,z=pts[i,j],pts[i,k],pts[j,k]
        if len({x,y,z})==3 and frozenset((x,y)) in edges[i] and frozenset((x,z)) in edges[j] and frozenset((y,z)) in edges[k]: triangles.append((i,j,k))
    unique=set(pts.values())
    return {'lines':len(ls),'triangular_faces':len(triangles),'parallel_pairs':parallel,'distinct_vertices':len(unique),'simple':not parallel and len(unique)==len(ls)*(len(ls)-1)//2,'normalized_lines_sha256':hashlib.sha256(json.dumps(ls,separators=(',',':')).encode()).hexdigest()}
