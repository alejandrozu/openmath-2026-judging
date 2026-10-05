"""Independent exact integer recount of the 192-class Cayley construction.

Reads no entrant executable or imported result receipt. Integer NumPy operations
are bounded below signed-64 overflow; Python Fraction checks the final ratio.
"""
from pathlib import Path
from fractions import Fraction
import json,hashlib
import numpy as np

HERE=Path(__file__).resolve().parent
Q=41
vertices=[(a,e,s,x) for a in range(3) for e in range(2) for s in range(2) for x in range(16)]
assert len(vertices)==192

def numerator(v):
    a,e,s,x=v
    inside=x.bit_count() in (0,1,4)
    z=0 if inside else Q
    if s:
        return (32 if inside else 0) if a==0 else z
    if a==0:
        if e==0:return z
        return 22 if x==0 else (Q if inside else 0)
    return (Q if inside else 0) if e==0 else z

def difference(u,v):
    return ((v[0]-u[0])%3,u[1]^v[1],u[2]^v[2],u[3]^v[3])

matrix=np.array([[numerator(difference(u,v)) for v in vertices] for u in vertices],dtype=np.int64)
assert np.array_equal(matrix,matrix.T)
assert int(matrix.min())>=0 and int(matrix.max())<=Q
assert Q**6*len(vertices)**3 < 2**63

def rooted_sum(table):
    root=table[0]
    total=0
    for j in range(len(vertices)):
        g=root*table[j]
        term=int((g[:,None]*g[None,:]*table).sum(dtype=np.int64))*int(root[j])
        total+=term
    return total

red=rooted_sum(matrix)
blue=rooted_sum(Q-matrix)
count=red+blue
assert count==1013294255057839
rooted=Fraction(count,Q**6)
density=Fraction(count,Q**6*len(vertices)**3)
assert rooted==Fraction(1013294255057839,4750104241)
assert density==Fraction(1013294255057839,33620705806123008)
out={'scope':'Independent exact data-only Cayley-root recount for the 192-class construction; does not check the 3840 refinement, native Lean execution, or historical priority.',
     'method':'Z3 x Z2 x Z2 x Z2^4 difference kernel, integer six-edge sum; all fixed-width intermediate and total bounds below 2^63; exact final Fraction.',
     'source_revision':'2cf216ba885fbb1b2d1b2d4920efeaa6ba438842',
     'source_url':'https://github.com/lukevs/k4-ramsey/blob/2cf216ba885fbb1b2d1b2d4920efeaa6ba438842/K4Ramsey/Constructions/Clebsch192/Model.lean',
     'vertex_count':len(vertices),'denominator':Q,'rooted_red_integer':red,'rooted_blue_integer':blue,
     'rooted_total_integer':count,'density_fraction':str(density),'density_decimal':float(density),
     'matrix_sha256':hashlib.sha256(matrix.tobytes()).hexdigest(),'all_pass':True}
(HERE/'luke_clebsch192_independent_recount.json').write_text(json.dumps(out,indent=2),encoding='utf8')
print(json.dumps(out,indent=2))
