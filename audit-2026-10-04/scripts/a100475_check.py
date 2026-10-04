"""A100475 (positive starts): T(n) = decimal reversal of the n-th prime. Elementary proof check.
Rosser (1938): p_n > n ln n for n >= 1. For n >= 22027, ln n > 10, so p_n > 10n has more digits than n;
primes > 5 do not end in 0, so rev(p_n) has as many digits as p_n, hence T(n) >= 10^digits(n) > n.
So T is strictly increasing above 22026 and every cycle would lie below 22027; we check there are none.
"""
import math
N = 3_000_000
s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
for i in range(2, int(N ** .5) + 1):
    if s[i]:
        s[i * i::i] = bytearray(len(s[i * i::i]))
primes = [i for i in range(N + 1) if s[i]]
T = lambda n: int(str(primes[n - 1])[::-1])
N0 = math.ceil(math.e ** 10)
low = [n for n in range(1, 200000) if T(n) <= n]
print("threshold", N0, "| n < 200000 with T(n) <= n:", len(low), "max", max(low))
cyc = []
for x in range(1, N0):
    seen, y = set(), x
    while y < N0 and y not in seen:
        seen.add(y); y = T(y)
    if y < N0:
        cyc.append(x)
print("starting points below threshold with a periodic orbit:", cyc)
