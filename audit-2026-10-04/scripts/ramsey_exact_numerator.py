"""EXACT monochromatic-K4 numerator of a weighted two-colour blow-up template, by multi-modular arithmetic.
numer = sum over ordered (a,b,c,d) of w_a w_b w_c w_d [all six pairs same colour; diagonal = block colour].
Each residue is computed with float64 BLAS matrix products whose intermediate values stay below 2^53
(exact), then the integer is reconstructed by the Chinese remainder theorem. Density = numer / (sum w)^4.
Usage: python3 ramsey_exact_numerator.py solution.json [claimed_numerator/claimed_denominator]"""
import json, sys
import numpy as np
from fractions import Fraction
d = json.load(open(sys.argv[1]))
w = [int(x) for x in d['weights']]; n = len(w); Q = sum(w)
R = np.array([[c == '1' for c in row] for row in d['red_rows']], dtype=bool)
assert (R == R.T).all()
PRIMES = [1048573, 1048571, 1048559, 1048549, 1048517, 1048507, 1048447]   # < 2^20, product > 2^139
def residue(p):
    wp = np.array([x % p for x in w], dtype=np.float64)
    tot = 0
    for A in (R, ~R):
        Af = A.astype(np.float64)
        for a in range(n):
            idx = np.nonzero(A[a])[0]
            if len(idx) == 0:
                continue
            B = Af[np.ix_(idx, idx)]; u = wp[idx]
            P = B * u[None, :]                        # entries < 2^20
            Qm = np.mod(P @ B, p)                      # sums < 2^30, exact
            Rb = np.mod((Qm * P).sum(axis=1), p)       # products < 2^40, sums < 2^50, exact
            inner = int(np.mod((Rb * u).sum(), p))     # < 2^50, exact
            tot = (tot + (w[a] % p) * inner) % p
    return tot
res = [residue(p) for p in PRIMES]
M = 1
for p in PRIMES: M *= p
x = 0
for p, r in zip(PRIMES, res):
    Mi = M // p; x += r * Mi * pow(Mi, -1, p)
numer = x % M
assert numer < M // 2 and numer <= Q ** 4
dens = Fraction(numer, Q ** 4)
print('n', n, 'sum w', Q, 'numerator', numer)
print('density', dens, '=', float(dens))
if len(sys.argv) > 2:
    num, den = map(int, sys.argv[2].split('/'))
    print('matches claim:', dens == Fraction(num, den))
