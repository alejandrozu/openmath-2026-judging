"""Sanity checks for a Kobon lower-bound catalogue (n -> number of bounded triangular faces).
* upper bound: Tamura floor(n(n-2)/3), minus 1 when n = 0 or 2 mod 6 (Clement-Bader 2007);
* monotonicity: K(n+1) >= K(n) (add a line far from all vertices), so a row below an earlier row is not a record;
* Furedi-Palasti (1984) general construction: K(n) >= floor(n(n-3)/3); a row at or below it is not a record.
Usage: edit ROWS / CAND below (taken from Rohith Poola's catalogue as listed in the compact review)."""
ROWS = """7 11|13 47|18 93|19 107|31 290|35 338|37 431|38 450|39 470|40 494|41 533|43 587|44 608|45 645|46 667|47 691|48 721|49 767|50 792|51 815|52 850|53 901|54 927|55 954|56 990|57 1045|58 1036|59 1086|60 1137|61 1190|62 1185|63 1243|64 1302|65 1365|66 1329|67 1383|68 1438|69 1494|70 1525|71 1590|72 1657|73 1727|74 1438|75 1489|76 1540|77 1595|78 1650|79 1708|80 1767|81 1829|82 1891|83 1956|84 2021|85 2090|86 2159|87 2233|88 2307|89 2384|90 2461|91 2542|92 2623|93 2709|94 2795|95 2885|96 2977|97 3071"""
CAND = set(map(int, "39 40 44 47 48 51 52 55 56 58 59 60 61 62 63 64 66 67 68 69 70 71 72 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96".split()))
K = {int(a): int(b) for a, b in (r.split() for r in ROWS.split('|'))}
best, bestn, survivors = 0, None, []
for n in sorted(K):
    ub = n * (n - 2) // 3 - (1 if n % 6 in (0, 2) else 0)
    fp = n * (n - 3) // 3
    notes = []
    if K[n] > ub: notes.append('EXCEEDS UPPER BOUND')
    if K[n] < best: notes.append(f'below earlier row n={bestn} ({best})')
    if K[n] <= fp: notes.append(f'<= Furedi-Palasti {fp}')
    if K[n] == ub: notes.append('perfect (meets upper bound)')
    if n in CAND and not any(x.startswith(('below', '<=')) for x in notes): survivors.append(n)
    print(f"n={n:3d} K>={K[n]:5d} ub={ub:5d} FP={fp:5d} {'NEW?' if n in CAND else '    '} {'; '.join(notes)}")
    if K[n] > best: best, bestn = K[n], n
print("candidate rows surviving both checks:", survivors, len(survivors), "of", len(CAND))
