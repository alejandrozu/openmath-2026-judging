import ast
import hashlib
import itertools
import json
import re
from pathlib import Path

ROOT = Path(__file__).parent
BUILDS = ROOT / 'verification' / 'builds'
report = {'purpose': 'Independent exact arithmetic audit used for source-faithful ordinary proof expositions; not a replacement for fresh Lean replay.'}

# Ordinary Eratosthenes, independent of the submitted loose surviving-residue sieve.
limit = 1_000_000
sieve = bytearray(b'\x01') * (limit + 1)
sieve[0:2] = b'\x00\x00'
for q in range(2, int(limit ** .5) + 1):
    if sieve[q]:
        sieve[q*q:limit+1:q] = b'\x00' * ((limit-q*q)//q + 1)
primes = [q for q in range(2, limit + 1) if sieve[q]]
def step(n):
    return int(str(primes[n-1])[::-1])
exceptions = []
for n, p in enumerate(primes, 1):
    if p >= 10000:
        break
    if step(n) <= n:
        t1, t2 = step(n), step(step(n))
        t3 = step(t2)
        assert n < t2 or n < t3
        exceptions.append({'prime': p, 'index': n, 'orbit_prefix': [n, t1, t2, t3], 'first_growth_step': 2 if n < t2 else 3})
report['a100475'] = {'pi_100000': sum(sieve[:100001]), 'pi_1000000': len(primes), 'small_prime_count': sum(sieve[:10000]), 'nonincreasing_small_indices': exceptions}

# Read the literal supplied L-free witness and enumerate all cyclic subsets.
e3path = BUILDS/'sakana-FOCUS-E3-pullback'/'R17SplitReplay.lean'
e3src = e3path.read_text(encoding='utf-8')
literal = e3src.split('def B :', 1)[1].split('theorem B_card', 1)[0]
B = set((int(x), int(y)) for x, y in re.findall(r'\((\d+),\s*(\d+)\)', literal))
assert len(B) == 79
assert all(not all(z in B for z in [(x,y),(x,(y+d)%13),(x,(y+2*d)%13),((x+d)%13,y)]) for x in range(13) for y in range(13) for d in range(1,13))
apmasks = set(sum(1 << ((a+k*d)%13) for k in range(4)) for a in range(13) for d in range(1,13))
free_masks = [m for m in range(1 << 13) if not any(m & a == a for a in apmasks)]
assert max(m.bit_count() for m in free_masks) == 6
six_example = [0, 1, 2, 4, 5, 7]
assert sum(1 << x for x in six_example) in free_masks
report['FOCUS-E3'] = {'B_rows': {str(x): sorted(y for xx,y in B if xx == x) for x in range(13)}, 'L_patterns_checked': 13*13*12, 'all_cyclic_subsets_checked': 1 << 13, 'distinct_four_AP_sets': len(apmasks), 'four_AP_free_subset_count': len(free_masks), 'max_cyclic_four_AP_free_cardinality': 6, 'six_point_example': six_example, 'witness_source_sha256': hashlib.sha256(e3path.read_bytes()).hexdigest()}

def lean_literal(text, name):
    return ast.literal_eval(re.search(r'def '+re.escape(name)+r'[^\n]*:= (\[[^\n]+\])', text).group(1))
def mul(A, B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
I = [[int(i == j) for j in range(23)] for i in range(23)]
matrix = []
for seed in range(3):
    directory = BUILDS/f'sakana-FOCUS-MATRIX-seed{seed}'
    datafile = next(directory.glob('*KernelData.lean'))
    src = datafile.read_text(encoding='utf-8')
    factors = {k: lean_literal(src, f'data_{k}') for k in ['u','v','w']}
    assert all(len(F) == 23 and all(len(row) == 9 for row in F) for F in factors.values())
    support = sum(x != 0 for F in factors.values() for row in F for x in row)
    assert support == 139
    pairs = []
    for pair in ['uv','uw','vw']:
        piv = lean_literal(src, f'pivData_{pair}')
        A, C = factors[pair[0]], factors[pair[1]]
        full = [[A[t][i//9]*C[t][i%9] for t in range(23)] for i in range(81)]
        minor = [full[i] for i in piv]
        inverse = lean_literal(src, f'LData_{pair}')
        assert len(set(piv)) == 23 and mul(inverse, minor) == I
        pairs.append({'pair': pair, 'pivot_rows': piv, 'integer_left_inverse_verified': True, 'column_rank_over_Q': 23})
    matrix.append({'seed': seed, 'total_support': support, 'data_sha256': hashlib.sha256(datafile.read_bytes()).hexdigest(), 'pairs': pairs})
report['FOCUS-MATRIX'] = matrix

# Determinant/sign criterion from ordinary affine geometry, without the evaluator.
kobonfile = BUILDS/'htpeo-kobon471'/'KobonCert'/'Data.lean'
kobonsrc = kobonfile.read_text(encoding='utf-8')
sol_literal = kobonsrc.split('def sol :',1)[1].split('def reportFaces',1)[0]
lines = [tuple(int(v.replace('(', '').replace(')', '').strip()) for v in row.split(',')) for row in re.findall(r'⟨([^⟩]+)⟩', sol_literal)]
assert len(lines) == 39
def cross(p,q):
    a,b,c = p; d,e,f = q
    return (b*f-c*e, c*d-a*f, a*e-b*d)
def dot(p,P):
    return sum(a*b for a,b in zip(p,P))
verts = {ij: cross(lines[ij[0]], lines[ij[1]]) for ij in itertools.combinations(range(39),2)}
assert all(P[2] != 0 for P in verts.values())
assert all(dot(lines[k], verts[i,j]) != 0 for i,j,k in itertools.combinations(range(39),3))
faces = []
for i,j,k in itertools.combinations(range(39),3):
    tri = [verts[i,j], verts[i,k], verts[j,k]]
    good = True
    for line in lines:
        signs = [dot(line,P)*P[2] for P in tri]
        if not (all(s >= 0 for s in signs) or all(s <= 0 for s in signs)):
            good = False
            break
    if good:
        faces.append([i,j,k])
assert len(faces) == 471
report['KOBON39'] = {'line_count': 39, 'line_coefficients': lines, 'nonparallel_pairs': len(verts), 'nonconcurrent_triples': 9139, 'triangle_count': len(faces), 'face_triples': faces, 'literal_data_sha256': hashlib.sha256(kobonfile.read_bytes()).hexdigest()}
path = ROOT/'final_four_independent_certificate_audit.json'
tmp = path.with_suffix('.tmp')
tmp.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding='utf-8')
tmp.replace(path)
print(json.dumps({'audit': str(path), 'A100475_exception_count': len(exceptions), 'E3_AP_free_subsets': len(free_masks), 'MMT_seed_count': len(matrix), 'Kobon_triangles': len(faces)}, indent=2))
