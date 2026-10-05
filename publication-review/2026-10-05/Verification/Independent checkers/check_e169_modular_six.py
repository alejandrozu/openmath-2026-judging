"""Independent modular four-AP certificate for the six-residue E169 alphabet.

Standard-library Python 3. Checks finite arithmetic only; no Lean replay and no
reciprocal-sum conclusion. Writes only the requested result JSON. The zero-new-
residue case uses the ordinary least-nonzero-base55-digit descent described in
the manuscript and a complete enumerated certificate for the21 base digits.
One-new cases are directly enumerated; reversal handles the other two positions.
Two-or-more-new cases use inverses of the position gaps1,2,3 modulo55^3.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import itertools
import json
import time

D = {0,1,2,4,5,9,10,11,14,16,17,18,21,24,30,37,39,41,42,45,47}
U = {26286,26726,26737,120061,120501,120512}
BASE = 55
MODULUS = BASE**3

def old(x):
    return x % BASE in D and x // BASE % BASE in D and x // BASE**2 % BASE in D

def allowed(x):
    return old(x) or x in U

def require(condition, label):
    if not condition:
        raise AssertionError(label)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('e169_modular_six_independent_check.json'))
    args = parser.parse_args()
    started = time.monotonic()
    require(len(D)==21 and sum(D)==433, 'Base digit identity')
    require(len(U)==6 and all(0<=u<MODULUS and not old(u) for u in U), 'New residues are distinct and outside the old alphabet')
    base_cases = 0
    for a in range(BASE):
        for d in range(1,BASE):
            base_cases += 1
            require(not all((a+k*d)%BASE in D for k in range(4)), 'Old base four-AP at '+str((a,d)))
    # If d mod55^3 is nonzero, its least nonzero base55 digit is at rank0,1 or2.
    # All lower digits of a+k*d coincide. At that rank the digits are precisely
    # floor(a/55^rank)+k*floor(d/55^rank) mod55, contradicting the base certificate.
    # This establishes the zero-new case; the script does not falsely enumerate
    # the9261^4 possible old residue tuples.
    one_new_cases = 0
    for u in sorted(U):
        for position in (0,1):
            for d in range(1,MODULUS):
                one_new_cases += 1
                require(not all(old((u+(k-position)*d)%MODULUS) for k in range(4) if k!=position),
                        'One-new progression at '+str((u,position,d)))
    # Reversing a progression replaces d by -d modM and positions0,1 by3,2.
    inverses = {gap:pow(gap,-1,MODULUS) for gap in (1,2,3)}
    require(all(gap*inverse%MODULUS==1 for gap,inverse in inverses.items()), 'Gap inverses')
    two_new_cases = 0
    for u,v in itertools.permutations(sorted(U),2):
        for i,j in itertools.combinations(range(4),2):
            d = (v-u)*inverses[j-i]%MODULUS
            a = (u-i*d)%MODULUS
            progression = [(a+k*d)%MODULUS for k in range(4)]
            require(d!=0 and progression[i]==u and progression[j]==v, 'Pair reconstruction')
            two_new_cases += 1
            require(not all(allowed(x) for x in progression), 'Two-new progression at '+str((u,v,i,j,d)))
    require(base_cases==2970 and one_new_cases==1996488 and two_new_cases==180, 'Enumeration coverage')
    output = args.output.resolve()
    script = Path(__file__).resolve()
    require(output!=script, 'Output must not replace the checker')
    result = {'created_utc':datetime.now(timezone.utc).isoformat(), 'status':'PASS',
        'seconds':round(time.monotonic()-started,3), 'checker_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),
        'base':BASE, 'modulus':MODULUS, 'old_digits':sorted(D), 'new_residues':sorted(U),
        'alphabet_size':len(D)**3+len(U),
        'checks':{'base_digit_nonzero_progressions':base_cases,
                  'zero_new_case':'Least-nonzero-base55-digit descent with enumerated base certificate',
                  'one_new_explicit_cases_positions_0_1':one_new_cases,
                  'one_new_positions_2_3':'Reversal bijection d to -d moduloM',
                  'two_or_more_new_explicit_pair_cases':two_new_cases,
                  'gap_inverses':inverses},
        'conclusion':'The digit-product alphabet enlarged by the six stated residues is modular four-AP-free modulo55^3 for every nonzero step.',
        'limitations':['This is an independent finite arithmetic check plus the stated elementary digit descent, not a Lean replay.',
                       'The reciprocal-sum lower bound and final positive-integer set assembly are outside this checker.',
                       'No manuscript inputs, proof sources, cached artifacts or proof plans are modified.']}
    output.parent.mkdir(parents=True,exist_ok=True)
    temporary=output.with_suffix('.tmp')
    temporary.write_text(json.dumps(result,indent=2),encoding='utf-8')
    temporary.replace(output)
    print(json.dumps({'status':'PASS','seconds':result['seconds'],'output':str(output),'checks':result['checks']}))

if __name__=='__main__':
    main()
