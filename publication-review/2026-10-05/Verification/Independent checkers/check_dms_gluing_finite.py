"""Independent small finite checks supporting the DMS gluing exposition.

Python 3; standard library only. Run without -O. Writes only the requested output
JSON, never manuscript inputs or Lean sources. The tests enumerate normalized
color-permutation cases and four literal H6 colorings. They do not establish the
five open structural premises, replay Lean, or check the whole cubic census.
Optional --source-dir verifies the frozen source hashes before computation.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import itertools
import json

SOURCE_RECORDS = [{'file': 'MhFact_7d291f6ca774e1da.lean', 'sha256': 'c2bcf9fca278110f87a1da0eb94387a9233ae797abf1d25896be701452ecdfac', 'authored_source_unchanged': True, 'locators': [{'name': 'g2fChk_ok', 'line': 469}, {'name': 'g2mChk_ok', 'line': 1000}, {'name': 'g2f', 'line': 742}, {'name': 'g2m', 'line': 1231}]}, {'file': 'MhFact_c64b6bd62b78d841.lean', 'sha256': '994b9b3dec8f85d136214c673a40adcd8aa890fa46213a89945e750d81b3fa85', 'authored_source_unchanged': True, 'locators': [{'name': 'glue_M', 'line': 90}, {'name': 'glue_F', 'line': 228}, {'name': 'Cut2.side', 'line': 1161}, {'name': 'Cut2.cl5', 'line': 1341}, {'name': 'Cut2.step5', 'line': 1616}, {'name': "ex1_2c''", 'line': 1790}]}, {'file': 'MhFact_657e581f1145250f.lean', 'sha256': '1f273f23b1d3d42a45df21b670b0a8fdc39484fb2c2c0c1327046030e373e02e', 'authored_source_unchanged': True, 'locators': [{'name': 'Cut2.RecipeD', 'line': 885}, {'name': 'Cut2.RecipeE', 'line': 890}, {'name': 'Cut2.sr_a', 'line': 1161}, {'name': 'Cut2.sr_b', 'line': 1106}]}, {'file': 'MhFact_341b6e5e1be16205.lean', 'sha256': '146216703f43870c428da41e5a07d26e0f1e4f281d4339f125d822c09dfde117', 'authored_source_unchanged': True, 'locators': [{'name': 'ex1red', 'line': 784}]}, {'file': 'MhFact_3e79907cfcc0085b.lean', 'sha256': '27cd672ddb75372ea981e3e50d882f10058bf7e5277da660fd41d44d6aa65f2f', 'authored_source_unchanged': True, 'locators': [{'name': 'smallFacts', 'line': 502}]}, {'file': 'MhFact_9e7dda3374e6b172.lean', 'sha256': 'bb4b9fe6adbc02b4131d6fcaa5b526573812c8ae9cdce94b61e940537f150b3d', 'authored_source_unchanged': True, 'locators': [{'name': 'glue3', 'line': 223}]}, {'file': 'MhFact_413193082c4b8758.lean', 'sha256': 'e45f35db6492cd6be96473a5d92eb1ba96b196476b73f324c2e3e98a01733f09', 'authored_source_unchanged': True, 'locators': [{'name': 'brick', 'line': 310}, {'name': 'cont_2cr', 'line': 471}, {'name': 'layer_3cut', 'line': 503}]}, {'file': 'MhFact_54ed0ff9a1ed26b6.lean', 'sha256': '9fd5e47ab90a45bc4edea20f2e0ac56564181e7594c396a688187471c8847d38', 'authored_source_unchanged': True, 'locators': [{'name': 'uncross', 'line': 213}, {'name': 'removable', 'line': 1495}, {'name': 'scl_step', 'line': 2068}, {'name': 'scl_stepA', 'line': 2497}]}, {'file': 'MhFact_4f913d5550e57c85.lean', 'sha256': '5c1b7e4b3beb5cd4ed33604fb2eb92d98f80dee63e2b4c02586f1f14a2b9daaf', 'authored_source_unchanged': True, 'locators': [{'name': 'scl4', 'line': 501}, {'name': 'scl6', 'line': 531}, {'name': 'scl8', 'line': 550}, {'name': 'scl10', 'line': 571}]}, {'file': 'MhFact_fbae65436c8cc8bf.lean', 'sha256': '1a23edcc85dd81ae5d2e3792f6c26fca5bcfcaf35677a703c9747fd4c1f56551', 'authored_source_unchanged': True, 'locators': [{'name': 'scl12', 'line': 46}]}, {'file': 'MhFact_e1599bf3f3c26bdb.lean', 'sha256': 'd1cdad7dadd7430adf0ade2910a78d1045ae15522656e031a95cfd88180052f1', 'authored_source_unchanged': True, 'locators': [{'name': 'scl14', 'line': 55}]}, {'file': 'MhFact_c3375be11cf311ee.lean', 'sha256': '7c8db901a192780b62790a52f272d8c8e2a97291bbf84f88975d0c2ebc2e6f77', 'authored_source_unchanged': True, 'locators': [{'name': 'hasm_converse', 'line': 1498}]}, {'file': 'MhFact_eff6661027b6cbd2.lean', 'sha256': '2abd8ec408aa5d051ecb32562129e7dfe385529e62217f82bd0426912f187dcc', 'authored_source_unchanged': True, 'locators': [{'name': 'digClassB', 'line': 418}, {'name': 'digClassZ', 'line': 490}, {'name': 'to_dig', 'line': 510}, {'name': 'repChk_sound', 'line': 1801}, {'name': 'concl_of_iso', 'line': 1895}]}, {'file': 'MhFact_cc801c1ba060f9c7.lean', 'sha256': 'd5cfe7d0ff4387c63d421373e1562fd44bb2335eeda0d9115aca48acfa8c792d', 'authored_source_unchanged': True, 'locators': [{'name': 'd1012_of', 'line': 156}, {'name': 'd14_of', 'line': 189}]}, {'file': 'MhFact_38b6f78a47fdf12e.lean', 'sha256': '4bc1147c78338ce22dbfb0e4faf92633a9dc4a63e6023609fcabf4e193c15028', 'authored_source_unchanged': True, 'locators': [{'name': 'd1012', 'line': 65}, {'name': 'base12', 'line': 70}]}, {'file': 'MhFact_66a4a19c81528d5b.lean', 'sha256': 'c97ccb0881f7489e85e0dfb0de146f20e081f5210558713d3ea16a315c8f6859', 'authored_source_unchanged': True, 'locators': [{'name': 'd14', 'line': 158}, {'name': 'simple14', 'line': 163}, {'name': 'b14d', 'line': 167}, {'name': 'iid14', 'line': 170}]}, {'file': 'MhFact_30194dab4e05fdcf.lean', 'sha256': 'd20437b0d190bf52fd38a3c7a3a712eff9363f383e5c27c9c62c7ec12ba0f8e9', 'authored_source_unchanged': True, 'locators': [{'name': 'small_side3', 'line': 644}]}, {'file': 'MhFact_33aabc50b1cec1ba.lean', 'sha256': 'e1c7efcc3fdc9f8ee2f2621ec86a8bc12c3c037144d70453d72b2ddb329dd604', 'authored_source_unchanged': True, 'locators': [{'name': 'TriPiece', 'line': 50}, {'name': 'h6_c2d', 'line': 258}, {'name': 'h6_c3d', 'line': 260}, {'name': 'lift_gen', 'line': 629}]}, {'file': 'MhFact_bde9371a01dd2855.lean', 'sha256': '0a12ccef590de3917d887a908d467400621e00aba6dad120049f6f40999717d4', 'authored_source_unchanged': True, 'locators': [{'name': 'TDTRI', 'line': 307}, {'name': 'tri_brick_td', 'line': 196}, {'name': 'hred14_step', 'line': 484}, {'name': 'hred14c_of', 'line': 592}, {'name': 'rootcs4', 'line': 624}]}, {'file': 'MhFact_2e993e3b07378767.lean', 'sha256': '9388fdb92e5ed9e9dd1ede845e0a6f18fa2df7cef8b28a1f5567acd448823550', 'authored_source_unchanged': True, 'locators': [{'name': 'smallhostd', 'line': 144}, {'name': 'layer28', 'line': 148}]}, {'file': 'MhFact_90b4662cdeba097d.lean', 'sha256': 'db2905b45d3fd23dbce21078ca40ff621288dd8183ac787e0636b9f9339b729f', 'authored_source_unchanged': True, 'locators': [{'name': 'iic_of', 'line': 96}]}, {'file': 'Star6Corollaries.lean', 'sha256': 'f692f15a62ab1bc9078a6148e04a962879ab530246381eceab4cf8c33ebecaf8', 'authored_source_unchanged': True, 'locators': [{'name': 'star6_cubic_bridgeless_le14', 'line': 48}, {'name': 'matching_colour_class_10_14', 'line': 64}, {'name': 'star6_leaf_le14', 'line': 82}, {'name': 'star6_subcubic_le7', 'line': 92}]}]

def finite_checks():
    checks = []
    perms5 = list(itertools.permutations(range(5)))
    for s2, sp, t2, tp in itertools.product(range(5), repeat=4):
        if s2 == sp or t2 == tp or {s2, sp} == {0, 1} or ({t2, tp} == {0, 1}):
            continue
        assert any(({p[0], p[1]}.isdisjoint({0, 1}) and {p[t2], p[tp]}.isdisjoint({s2, sp}) for p in perms5))
    checks.append({'name': 'normalized_g2m', 'tuples_total': 625, 'permutations': 120, 'status': 'PASS'})
    perms4 = list(itertools.permutations(range(1, 5)))
    for r1, r2, x1, x2 in itertools.product(range(1, 5), repeat=4):
        assert any(({p[x1 - 1], p[x2 - 1]}.isdisjoint({r1, r2}) for p in perms4))
    checks.append({'name': 'normalized_g2f', 'tuples_total': 256, 'permutations': 24, 'status': 'PASS'})
    perms3 = list(itertools.permutations((2, 3, 4)))
    for a1, a2 in itertools.product(range(6), repeat=2):
        for b1, b2 in itertools.product((2, 3, 4), repeat=2):
            assert any((p[b1 - 2] != a1 and p[b2 - 2] != a2 for p in perms3))
    checks.append({'name': 'normalized_perm_4c', 'tuples_total': 324, 'permutations': 6, 'status': 'PASS'})
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (4, 5), (4, 5), (5, 3)]
    colors = [[0, 5, 2, 1, 5, 3, 5, 0, 4], [0, 5, 2, 1, 5, 3, 0, 5, 4], [0, 2, 5, 5, 1, 4, 5, 0, 3], [0, 2, 5, 5, 1, 4, 0, 5, 3]]
    for c in colors:
        inc = [[j for j, e in enumerate(edges) if v in e] for v in range(6)]
        for row in inc:
            assert len({c[j] for j in row}) == len(row)
            assert sum((c[j] == 5 for j in row)) == 1

        def walk(v, chosen):
            if len(chosen) == 4:
                assert not (c[chosen[0]] == c[chosen[2]] and c[chosen[1]] == c[chosen[3]])
                return
            for j in inc[v]:
                if j in chosen:
                    continue
                a, b = edges[j]
                walk(b if v == a else a, chosen + [j])
        for v in range(6):
            walk(v, [])
    checks.append({'name': 'printed_triangle_digon_H6_MC_certificates', 'color_rows': 4, 'properness': 'PASS', 'matching': 'PASS', 'all_distinct_edge_four_walks': 'PASS'})
    assert sum([5, 24, 56, 78, 57]) == 220
    assert sum([1, 21, 124, 356, 482, 341]) == 1325
    assert 1325 - 341 == 984
    return checks

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('dms_gluing_finite_independent_check.json'))
    parser.add_argument('--source-dir', type=Path, default=None)
    args = parser.parse_args()
    script = Path(__file__).resolve()
    output = args.output.resolve()
    if output == script:
        raise ValueError('Output must not replace this checker.')
    if not __debug__:
        raise RuntimeError('Run this checker without Python -O: assertions are load-bearing.')
    checked_sources = []
    if args.source_dir is not None:
        for record in SOURCE_RECORDS:
            path = args.source_dir / record['file']
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != record['sha256']:
                raise ValueError('Frozen source hash mismatch: ' + record['file'])
            checked_sources.append({'file': record['file'], 'sha256': actual, 'status': 'PASS'})
    results = finite_checks()
    result = {
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'PASS',
        'scope': 'Normalized g2m/g2f/perm_4c and four literal triangle-digon H6 MC certificates only',
        'checker_sha256': hashlib.sha256(script.read_bytes()).hexdigest(),
        'source_directory_locator': 'entries/dms-star6/artifact/lean/pack4/src',
        'frozen_source_records': SOURCE_RECORDS,
        'frozen_source_hash_validation': 'PASS' if checked_sources else 'NOT_REQUESTED',
        'source_hash_checks': checked_sources,
        'checks': results,
        'census_count_arithmetic': {'order_10_12_marking_rows': 220,
                                   'order_14_marking_rows': 1325,
                                   'order_14_simple_rows': 341,
                                   'order_14_nonsimple_rows': 984},
        'limitations': [
            'The marking-row totals are arithmetic checks, not independent census completeness checks.',
            'No Lean compilation or theorem axiom audit is performed by this script.',
            'The five infinite structural hypotheses remain unproved.',
            'No manuscript inputs or authored sources are modified.'
        ]
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + '.tmp')
    temporary.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    temporary.replace(output)
    print(json.dumps({'status': result['status'], 'output': str(output),
                      'checker_sha256': result['checker_sha256'],
                      'frozen_sources_checked': len(checked_sources), 'checks': results}))


if __name__ == '__main__':
    main()
