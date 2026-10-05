"""Select a completed qualified replacement without promoting partial work."""
from pathlib import Path
import hashlib
from receipt_io import read_json_shared

BASE=Path(__file__).resolve().parent

def qualified_luke_native_path():
    native=BASE/'luke-k4-ramsey-current-native-fresh-build.json'
    gate=BASE/'luke-native-publication-qualification.json'
    if not native.exists() or not gate.exists():return None
    g=read_json_shared(gate)
    if g.get('status')!='PASS_COMPLETE_EXACT_SCOPE':return None
    from receipt_io import read_bytes_shared
    raw=read_bytes_shared(native)
    if hashlib.sha256(raw).hexdigest()!=g.get('replay_receipt_sha256'):return None
    d=read_json_shared(native)
    if d.get('status')!='PASS_WITH_NATIVE_EVALUATION' or not d.get('finished_utc'):return None
    return native

def receipt_path(project):
    if project=='chandragupt':return BASE/'chandragupt-pinned-build.json'
    if project=='luke-k4-ramsey-current':
        native=qualified_luke_native_path()
        if native:return native
        direct=BASE/'luke-k4-ramsey-current-direct-fresh-build.json'
        if direct.exists():return direct
    return BASE/(project+'-fresh-build.json')
