"""Reproduce every local CFSD-1000 D value in review-data.json from its stored normalized components,
then show sensitivity to the human-effort/exposure inputs (H, X). Diagnostic only: the competition
uses the recorded D values unchanged (chair ruling of 4 Oct 2026).
Usage: python3 opdp_cfsd_sensitivity.py OpenMath-Judging/review/review-data.json"""
import json, sys
d = json.load(open(sys.argv[1]))
W = d['difficulty_method']['component_weights_points']
def cfsd(nc):
    R = sum(W[k] * min(1, max(0, v)) for k, v in nc.items())
    return round(1000 * (1 - (1 - R / 1000) ** 1.4)), R
def hx(H, X):  # 0.8 * normalized H (H1..H9) + 0.2 * normalized X (X1..X5)
    return 0.8 * max(0, (H - 1) / 8) + 0.2 * max(0, (X - 1) / 4)
mism = 0
print(f"{'family':18s} {'D':>4s} {'repro':>5s} {'H':>3s} {'X':>3s} {'D(H2,X1)':>8s} {'D(H0,X0)':>8s}")
for fam, p in sorted(d['problems'].items()):
    calc = p.get('calculation')
    if not calc or 'normalized_components' not in calc:
        print(f"{fam:18s} {p.get('D_0_1000_proposed'):4d}   published value reused (no local profile)")
        continue
    nc = dict(calc['normalized_components']); D0 = p['D_0_1000_proposed']
    rep, _ = cfsd(nc); mism += rep != D0
    i = p.get('inputs', {})
    a = dict(nc); a['human_resistance'] = hx(2, 1)
    b = dict(nc); b['human_resistance'] = hx(0, 0)
    print(f"{fam:18s} {D0:4d} {rep:5d} {str(i.get('H')):>3s} {str(i.get('X')):>3s} {cfsd(a)[0]:8d} {cfsd(b)[0]:8d}")
print("reproduction mismatches:", mism)
nc0 = {k: 0.0 for k in W}; print("CFSD of an all-zero profile:", cfsd(nc0)[0])
