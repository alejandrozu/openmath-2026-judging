"""Classify the submitted Luke endpoint audits after the full cold replay."""
from pathlib import Path
import argparse,json,re,hashlib,os,time
from audit_axioms import STANDARD,is_native,parse
from receipt_io import read_bytes_shared
base=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--route',choices=['lake','direct','native'],default='lake');args=parser.parse_args()
source=base/({'direct':'luke-k4-ramsey-current-direct-fresh-build.json',
             'native':'luke-k4-ramsey-current-native-fresh-build.json',
             'lake':'luke-k4-ramsey-current-fresh-build.json'}[args.route])
replay_snapshot=read_bytes_shared(source)
r=json.loads(replay_snapshot.decode('utf8'))
assert r['status']=='PASS_WITH_NATIVE_EVALUATION','Complete successful replay is required before this audit summary'
preflight=json.loads((base/'luke-source-preflight.json').read_text(encoding='utf8'))
expected={name for names in preflight['submitted_endpoint_audits'].values() for name in names}
graphon=preflight['submitted_endpoint_audits']['Audits.Graphon']
ordinary=set(graphon[:11])
standard=STANDARD
actual={}
for row in r['builds']:
    if not row.get('is_endpoint_audit') or row.get('exit')!=0:continue
    for printed in parse(row.get('stdout','')):actual[printed['endpoint']]=printed['axioms']
rows=[]
for name in sorted(expected):
    axioms=actual.get(name)
    unknown=None if axioms is None else sorted(a for a in axioms if a not in standard and not is_native(a))
    native_used=None if axioms is None else sorted(a for a in axioms if is_native(a))
    rows.append({'endpoint':name,'axioms':axioms,'ordinary_general_theorem':name in ordinary,
    'native_axioms':native_used,'unexpected_axioms':unknown,
    'declared_trust_boundary_matches':axioms is not None and not unknown and (name not in ordinary or not native_used)})
result={'created_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'reproduction_route':args.route,
'source_commit':r['commit'],'lean_version':r['version'],'mathlib_pin':r['mathlib_pin'],
'replay_report_sha256':hashlib.sha256(replay_snapshot).hexdigest(),
'axiom_classifier_sha256':hashlib.sha256((base/'audit_axioms.py').read_bytes()).hexdigest(),
'analyzer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'expected_endpoint_count':len(expected),'printed_endpoint_count':len(set(actual)&expected),
'all_expected_endpoints_present':expected<=set(actual),
'all_declared_trust_boundaries_match':all(v['declared_trust_boundary_matches'] for v in rows),
'general_standard_only_count':sum(v['ordinary_general_theorem'] and v['declared_trust_boundary_matches'] for v in rows),
'native_endpoint_count':sum(bool(v['native_axioms']) for v in rows),'endpoints':rows,
'trust_notice':'The general graphon, finite-realization and asymptotic arguments are distinguished from the explicit finite table certificates. Native evaluation adds trust in the Lean compiler and runtime, including Lean4.34 generated _native.native_decide.ax declarations; it is not represented as a kernel-only exact-arithmetic certificate.'}
result['status']='PASS_WITH_DECLARED_NATIVE_TRUST' if result['all_declared_trust_boundaries_match'] else 'ENDPOINT_TRUST_REVIEW_REQUIRED'
p=base/({'direct':'luke-k4-ramsey-direct-endpoint-axioms.json',
         'native':'luke-k4-ramsey-native-endpoint-axioms.json',
         'lake':'luke-k4-ramsey-endpoint-axioms.json'}[args.route]);tmp=p.with_suffix('.json.tmp')
with tmp.open('w',encoding='utf8') as f:
    f.write(json.dumps(result,indent=2));f.flush();os.fsync(f.fileno())
for attempt in range(60):
    try:os.replace(tmp,p);break
    except PermissionError:
        if attempt==59:raise
        time.sleep(.1)
print(result['status'],result['printed_endpoint_count'],'endpoints;',result['general_standard_only_count'],'general standard-only;',result['native_endpoint_count'],'native')
