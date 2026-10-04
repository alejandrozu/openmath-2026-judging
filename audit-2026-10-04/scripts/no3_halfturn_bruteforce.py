"""Brute force: all 2n-point no-three-in-line subsets of the n x n grid; minimum positive one-sided
half-turn miss |{p in A : R(p) not in A}|. Usage: python3 no3_halfturn_bruteforce.py 8"""
import itertools, sys
from math import gcd
def solutions(n):
    rows=list(itertools.combinations(range(n),2))
    sols=[]
    def collinear(a,b,c):
        return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])==0
    def rec(r,pts,colcount):
        if r==n: sols.append(tuple(pts)); return
        for (x1,x2) in rows:
            if colcount[x1]>=2 or colcount[x2]>=2: continue
            new=[(x1,r),(x2,r)]
            ok=True
            for p in new:
                for a,b in itertools.combinations(pts,2):
                    if collinear(a,b,p): ok=False;break
                if not ok: break
            if not ok: continue
            # pair with existing point (new pair is horizontal, row has only these two)
            for a in pts:
                if collinear(a,new[0],new[1]): ok=False;break
            if not ok: continue
            colcount[x1]+=1; colcount[x2]+=1
            rec(r+1,pts+new,colcount)
            colcount[x1]-=1; colcount[x2]-=1
    rec(0,[],[0]*n)
    return sols
for n in range(3,int(sys.argv[1])+1):
    S=solutions(n)
    misses=[]
    for s in S:
        st=set(s); rot={(n-1-x,n-1-y) for x,y in s}
        misses.append(len(st-rot))
    pos=[m for m in misses if m>0]
    print(n,'solutions',len(S),'min positive one-sided miss',min(pos) if pos else None, 'symmetric count',misses.count(0))
