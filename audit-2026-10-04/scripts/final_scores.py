"""Recompute OpenMath 2026 scores from review/review-data.json under the chair rulings of 4 Oct 2026.

Rulings applied:
  * D values: unchanged (OPDP extension values as recorded in review-data.json).
  * Bonuses: removed (b = 1 for every family, including former M1 focus rows).
  * Modality multiplier m unchanged (M3B = 1/2).
  * Collatz rows: p = 0 unless novel mathematics is shown (none found, see report section 6).
  * FOCUS-GROTH (Sakana): new formalized restricted theorem -> P1 lower end, p = 0.01.
  * Classes: Company vs Non-company only.
Usage: python3 final_scores.py /path/to/OpenMath-Judging/review/review-data.json > final-scores.csv
"""
import json, sys, csv
from decimal import Decimal as Dec

path = sys.argv[1] if len(sys.argv) > 1 else 'OpenMath-Judging/review/review-data.json'
d = json.load(open(path))
OVERRIDE_P = {'E05-RULES': Dec('0'), 'E10-H4': Dec('0'), 'E02-FOCUS-GROTH': Dec('0.01')}

teams = {t['id']: t for t in d['teams']}
fam_best = {}   # (team, family) -> (F, result row)
for r in d['results']:
    D = r.get('D_proposed'); p = r.get('proposed_p')
    if D is None or p in (None, 'None') or r.get('proposed_modality') not in ('M1', 'M3A', 'M3B'):
        continue   # M2 rows are counted separately (family counts), never in S/A
    p = OVERRIDE_P.get(r['id'], Dec(str(p)))
    m = Dec(str(r.get('proposed_m', '1')))
    F = m * p * Dec(D) ** 2 / 1000          # b = 1
    key = (r['team_id'], r['family_id'])
    if key not in fam_best or F > fam_best[key][0]:
        fam_best[key] = (F, r, p, m, D)

w = csv.writer(sys.stdout, lineterminator='\n')
w.writerow(['entry', 'name', 'class', 'S', 'A', 'A_family', 'M2_count', 'M2_adjusted', 'scored_families'])
for tid, t in teams.items():
    fams = [(k[1], v) for k, v in fam_best.items() if k[0] == tid and v[0] > 0]
    S = sum((v[0] for _, v in fams), Dec(0))
    A, Afam = (max(((v[0], f) for f, v in fams)) if fams else (Dec(0), ''))
    cls = 'Company' if str(t.get('entrant_class', '')).startswith('Company') else 'Non-company'
    m2 = t.get('M2_proposed_integer_count', 0) or 0
    m2a = t.get('M2_adjusted_overall_value', m2)
    detail = '; '.join(f"{f} D{v[4]} m{v[3]} p{v[2]} F={v[0].quantize(Dec('0.000001'))}" for f, v in sorted(fams))
    w.writerow([tid, t['name'], cls, S.quantize(Dec('0.000001')), A.quantize(Dec('0.000001')), Afam, m2, m2a, detail])
