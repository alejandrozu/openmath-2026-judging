"""Only prepare updated passive-AST/full-diff metadata; never run the qualifier."""
from pathlib import Path
from datetime import datetime, timezone
import ast, difflib, hashlib, json
B = Path(__file__).resolve().parent
H = B / 'proposals' / 'e65q-v1'
P = B / 'proposals' / 'e65qual-final-v2'
T = B / 'qualify_original_e65_composite_199plusStd.py'

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert not P.exists()
assert digest(H / 'helper.py') == '5698279e9fe90c19d12e8d77d0948b145f353e2310d803326ffcbe7a6e90b306'
assert digest(H / 'packet.json') == '5e1636109820058f05b208672b03cdf2dbdc58b9629a2381d6fac60233a87e4b'
assert digest(H / 'full.diff') == '4b726cea5e9bec49d0f1473de940876ca3fd694205e38702bc4ae3af42f5a6d4'
old = (H / 'helper.py').read_text(encoding='utf8')
text = T.read_text(encoding='utf8')
ast.parse(text, filename=str(T))
P.mkdir()
full = P / 'candidate.full.diff'
mini = P / 'v1-to-v2.minimal.diff'
full.write_text(''.join(difflib.unified_diff([], text.splitlines(keepends=True), fromfile='/dev/null', tofile=str(T))), encoding='utf8', newline='\n')
mini.write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True), text.splitlines(keepends=True), fromfile=str(H / 'helper.py'), tofile=str(T))), encoding='utf8', newline='\n')
packet = json.loads((H / 'packet.json').read_text(encoding='utf8'))
packet.update({'created_utc': datetime.now(timezone.utc).isoformat(), 'preparation_revision': 2,
               'producer_file': str(Path(__file__).resolve()), 'producer_sha256': digest(Path(__file__)),
               'candidate_helper_sha256': digest(T), 'full_new_file_diff': str(full), 'full_new_file_diff_sha256': digest(full),
               'minimal_v1_to_v2_diff': str(mini), 'minimal_v1_to_v2_diff_sha256': digest(mini),
               'preserved_previous_helper': str(H / 'helper.py'), 'preserved_previous_helper_sha256': digest(H / 'helper.py'),
               'preserved_previous_packet': str(H / 'packet.json'), 'preserved_previous_packet_sha256': digest(H / 'packet.json'),
               'sole_operational_change': 'Assert all200 actual compilation-order identities are unique, exhaustive and topological before checking every199 own source row.'})
packet['future_root_completion_review_schema_TEMPLATE_ONLY_NO_ACTIVE_APPROVAL']['qualification_helper_sha256'] = digest(T)
file = B / 'sundai-erdos3-original-image-source-fresh-build.json'
raw = file.read_bytes()
current = json.loads(raw)
packet['dated_raw_receipt_snapshot_not_final_qualification'] = {
    'file': str(file), 'sha256': hashlib.sha256(raw).hexdigest(), 'status': current['status'],
    'finished_utc': current.get('finished_utc'),
    'actual_own_source_passes_at_read': sum(r.get('exit') == 0 and not r.get('is_endpoint_audit') for r in current['builds']),
    'actual_own_audit_passes_at_read': sum(r.get('exit') == 0 and r.get('is_endpoint_audit') for r in current['builds']),
}
output = P / 'review-packet.json'
output.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + '\n', encoding='utf8', newline='\n')
print(json.dumps({'helper_sha256': digest(T), 'packet': str(output), 'packet_sha256': digest(output),
                  'full_diff_sha256': digest(full), 'minimal_diff_sha256': digest(mini),
                  'candidate_executed': False, 'Lean_invoked': False}))
