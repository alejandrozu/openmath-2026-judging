"""Exact check of a rank-23 3x3 matrix-multiplication scheme (Brent equations) and its support.
Convention (as declared in the entrant's lean/README): A, B row-major; C stored column-major,
target T[3i+j][3j+k][3k+i] = 1. Usage: python3 chandra_tensor_check.py solutions/support_138/solution.json"""
import json, sys
from fractions import Fraction as Fr
d = json.load(open(sys.argv[1]))
def parse(x):
    if isinstance(x, list): return Fr(x[0], x[1])
    return Fr(str(x))
U, V, W = [[[parse(x) for x in row] for row in d[k]] for k in ('u', 'v', 'w')]
supp = sum(1 for M in (U, V, W) for r in M for x in r if x != 0)
bad = 0
for a in range(9):
    for b in range(9):
        for c in range(9):
            s = sum(U[t][a] * V[t][b] * W[t][c] for t in range(len(U)))
            i, j = divmod(a, 3); j2, k = divmod(b, 3); k2, i2 = divmod(c, 3)
            bad += s != (1 if (j == j2 and k == k2 and i == i2) else 0)
print(f"terms {len(U)}  support {supp}  failed identities {bad}/729")
