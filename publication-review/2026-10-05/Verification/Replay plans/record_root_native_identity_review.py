"""Record root's limited review; never invoke Lean or modify its receipt."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
from receipt_io import read_bytes_shared

BASE=Path(__file__).resolve().parent
def digest(raw): return hashlib.sha256(raw).hexdigest()
def canonical(value): return digest(json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
evidence_path=BASE/'luke-native-identity-observer-limitation-review.json'
evidence_raw=read_bytes_shared(evidence_path)
assert digest(evidence_raw)=='37d02bd72946b0310ed3162f837745df5deb12127b94a46fa231954fd04b855c'
evidence=json.loads(evidence_raw)
pilot_raw=read_bytes_shared(BASE/'luke-k4-ramsey-current-native-fresh-build.json')
assert digest(pilot_raw)=='f96afa977949375778b0666754a20238403718d93919f08508ed9d3f4370229d'
pilot=json.loads(pilot_raw)
count=[r for r in pilot['builds'] if r.get('module')=='K4Ramsey.Constructions.Final3840.Certificate' and r.get('state')=='PASS']
assert len(count)==1
count=count[0]
assert count['exit']==0 and canonical(count)==evidence['count_row_canonical_sha256']
assert count['loaded_native_images']==evidence['loaded_native_images']
assert evidence['initialization_complete_cache_slot_observation'] in count['cache_pointer_observations']
slots=evidence['initialization_complete_cache_slot_observation']['slots']
assert {s['cache'] for s in slots}=={'bCache','dCache','pathsCache'}
assert all(s['read_bytes']==8 and s['pointer_value']!=0 and not s['is_null'] for s in slots)
assert evidence['image_observation_errors_preserved']==count['image_observation_errors']
assert len(count['image_observation_errors'])==1 and '299' in count['image_observation_errors'][0]
assert evidence['all_checked_source_object_artifact_and_dependency_identities_unchanged'] is True
assert evidence['native_dispatch_observations_clean'] is False
assert evidence['continuous_observer_completeness'] is False
assert evidence['unknown_error_timing_remains_unresolved'] is True
links_raw=read_bytes_shared(BASE/'luke-native-isolated-links.json')
assert digest(links_raw)==evidence['native_link_receipt_sha256']==pilot['native_link_receipt_sha256']
links=json.loads(links_raw)
assert {r['sha256'] for r in count['loaded_native_images']}=={r['sha256'] for r in links['dlls']}
for r in links['dlls']:
    assert digest(Path(r['file']).read_bytes())==r['sha256']
    assert digest(Path(r['import_library']['file']).read_bytes())==r['import_library']['sha256']
decision={
    'status':'ROOT_NATIVE_IDENTITY_REVIEW_ACCEPTED_WITH_OBSERVER_LIMITATION',
    'accepted_by':'/root','accepted_utc':datetime.now(timezone.utc).isoformat(),
    'evidence_receipt_file':str(evidence_path),'evidence_receipt_sha256':digest(evidence_raw),
    'pilot_receipt_sha256':digest(pilot_raw),
    'count_row_canonical_sha256':canonical(count),
    'native_link_receipt_sha256':digest(links_raw),
    'native_dispatch_observations_clean':False,'continuous_observer_completeness':False,
    'unknown_error_timing_remains_unresolved':True,'limited_scope_acknowledged':True,
    'basis':'The actual unchanged source exited0, both loaded native-image identities were time-stamped and SHA-matched, and all three exact exported cache slots were read successfully as non-null before source completion. The reviewed source/object/dependency/adapter identities remain unchanged.',
    'limitation':'One preserved WinError299 has unknown timing. This review does not label the observer clean or complete, infer an exit race, claim a function-call trace, or settle mathematical originality.',
    'scope':'Accept positive native identity/initialization evidence with the stated observer limitation. A plain actual RawCount axiom inspection and the remaining51-source/35-selected/11-general scope must still complete separately.',
    'source_or_original_receipt_mutated':False,'Lean_or_DLL_invoked':False
}
path=BASE/'luke-native-root-identity-acceptance-with-limitation.json'
assert not path.exists()
raw=json.dumps(decision,ensure_ascii=False,indent=2).encode('utf8')
path.write_bytes(raw)
print(json.dumps({'file':str(path),'sha256':digest(raw),'status':decision['status']},indent=2))
