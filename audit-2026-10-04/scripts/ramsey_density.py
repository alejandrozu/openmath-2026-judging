"""Floating-point recomputation of the K4 monochromatic density of a weighted two-colour blow-up template
(hill schema weighted-two-color-blowup-v1: weights + red_rows, diagonal colour = block colour).
Density = sum over ordered 4-tuples of blocks (repeats allowed) of w_a w_b w_c w_d [all six pairs same colour] / Q^4.
Usage: python3 ramsey_density.py solution.json"""
import json, numpy as np, sys
from fractions import Fraction
d=json.load(open(sys.argv[1]))
w=np.array(d['weights'],dtype=np.float64); Q=w.sum(); n=len(w)
R=np.array([[c=='1' for c in row] for row in d['red_rows']],dtype=bool)
print('n',n,'Q',int(Q),'symmetric',bool((R==R.T).all()))
u=w/Q
tot=0.0
for A in (R, ~R):
    Af=A.astype(np.float64)
    for a in range(n):
        idx=np.nonzero(A[a])[0]
        if len(idx)==0: continue
        B=Af[np.ix_(idx,idx)]; uu=u[idx]
        P=B*uu[None,:]
        Qm=P@B
        inner=(uu*(Qm*P).sum(axis=1)).sum()
        tot+=u[a]*inner
print('density %.12f'%tot)
