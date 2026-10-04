"""Maximum odd-residue coverage reachable by ANY rule set in the Collatz hill format, versus the
classical (Terras) stopping-time set.

Hill rule (k, r, [e1..es]): Syracuse steps C(n)=(3n+1)/2^v2(3n+1) with exact valuations along the
representative r, k >= E+1 (E = e1+..+es), A=3^s < D=2^E and A*r+B < D*r (descent for all n = r mod 2^k).
A residue R mod 2^K is coverable iff some k <= K and some prefix length s satisfy these checks for q = R mod 2^k.
Usage: python3 collatz_ceiling.py [K=12] [smax=99]
"""
import sys
K = int(sys.argv[1]) if len(sys.argv) > 1 else 12
SMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 99

def v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c

def rule_ok(k, q, smax):
    n, A, B, E = q, 1, 0, 0
    for _ in range(smax):
        e = v2(3 * n + 1)
        if E + e + 1 > k:
            return False
        B = 3 * B + 2 ** E; A *= 3; E += e; n = (3 * n + 1) >> e
        if A < 2 ** E and A * q + B < 2 ** E * q:
            return True
    return False

def terras(r, k):
    """Classical: odd r mod 2^k has stopping time <= k (coefficient test on the T-map)."""
    A, x = 1, r
    for j in range(1, k + 1):
        if x % 2:
            A *= 3; x = (3 * x + 1) // 2
        else:
            x //= 2
        if A < 2 ** j:
            return True
    return False

hill = sum(1 for R in range(1, 2 ** K, 2)
           if any(rule_ok(k, R % 2 ** k, SMAX) for k in range(1, K + 1) if R % 2 ** k))
cls = sum(1 for R in range(1, 2 ** K, 2) if terras(R, K))
print(f"mod 2^{K}: odd classes {2 ** (K - 1)}; max coverable in hill format {hill}; classical stopping-time set {cls}")
