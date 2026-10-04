"""Numerical exploration of sup Q(A)/C(A) over 3 x n sign matrices (Sakana FOCUS-GROTH proves <= sqrt(3/2)).
Columns reduce to 4 projective sign types with nonnegative weights. Equal weights give exactly 2/sqrt(3)."""
import numpy as np, itertools
rng = np.random.default_rng(1)
E = np.array([[1, 1, 1], [1, 1, -1], [1, -1, 1], [-1, 1, 1]], float)
X = np.array(list(itertools.product([1, -1], repeat=3)), float)
C = lambda w: max((w * np.abs(E @ x)).sum() for x in X)
def Q(w, starts=8, iters=200):
    best = 0
    for _ in range(starts):
        U = rng.normal(size=(3, 3)); U /= np.linalg.norm(U, axis=1, keepdims=True)
        for _ in range(iters):
            V = E @ U; nv = np.linalg.norm(V, axis=1)
            G = sum(w[k] * np.outer(E[k], V[k] / nv[k]) for k in range(4) if nv[k] > 1e-12)
            U = G / np.linalg.norm(G, axis=1, keepdims=True)
        best = max(best, (w * np.linalg.norm(E @ U, axis=1)).sum())
    return best
w = np.ones(4) / 4
print("equal weights ratio", Q(w) / C(w), "2/sqrt3 =", 2 / np.sqrt(3), "sqrt(3/2) =", np.sqrt(1.5))
print("max over 300 random weightings", max(Q(w) / C(w) for w in rng.dirichlet(np.ones(4), 300)))
