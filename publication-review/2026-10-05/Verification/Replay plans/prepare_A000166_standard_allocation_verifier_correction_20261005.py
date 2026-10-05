"""Prepare a separate, unexecuted A000166 verifier measurement correction."""
import ast
import difflib
import hashlib
import json
import pathlib

V = pathlib.Path(__file__).resolve().parent
original = V / 'qualify_A000166_granular_completion_readonly_prepared_20261005.py'
expected = 'a41ca1d3e7d79c8b43b6df3cd9c5fcc532a656b2e98a0ad85ca8ff13fa03fa85'
sha = lambda data: hashlib.sha256(data).hexdigest()
data = original.read_bytes()
assert sha(data) == expected
source = data.decode('utf-8')
replacements = {
    "    ensure(s['actual_allocation_bytes_saved'] == before['stored_bytes_GetCompressedFileSizeW'] - after['stored_bytes_GetCompressedFileSizeW'], 'Storage measured saved bytes')":
    "    ensure(after['standard_allocation_bytes'] <= before['standard_allocation_bytes'], 'Storage standard allocation increased')\n"
    "    ensure(s['actual_allocation_bytes_saved'] == before['standard_allocation_bytes'] - after['standard_allocation_bytes'], 'Storage measured standard allocation saved bytes')",
    "        'before_allocated_bytes': before['stored_bytes_GetCompressedFileSizeW'], 'after_allocated_bytes': after['stored_bytes_GetCompressedFileSizeW'],":
    "        'before_allocated_bytes': before['standard_allocation_bytes'], 'after_allocated_bytes': after['standard_allocation_bytes'],\n"
    "        'allocation_measurement': 'FileStandardInfo standard_allocation_bytes, matching frozen storage interface03a6 lines208/214',\n"
    "        'before_GetCompressedFileSizeW_bytes': before['stored_bytes_GetCompressedFileSizeW'], 'after_GetCompressedFileSizeW_bytes': after['stored_bytes_GetCompressedFileSizeW'],\n"
    "        'GetCompressedFileSizeW_measurement_nonincreasing': True,",
    "    'post_exit_storage_actual_class_counts': dict(classes), 'post_exit_storage_sidecar_checks': storage_checks,":
    "    'post_exit_storage_actual_class_counts': dict(classes), 'post_exit_storage_sidecar_checks': storage_checks,\n"
    "    'storage_measurement_correction': {'original_a41_verifier_sha256': 'a41ca1d3e7d79c8b43b6df3cd9c5fcc532a656b2e98a0ad85ca8ff13fa03fa85',\n"
    "        'failed_authorized_a41_attempt_record': 'A000166-a41-authorized-review-measurement-mismatch-actual-20261005T082057639017Z.json',\n"
    "        'failed_attempt_record_sha256': 'f2424c9e91970b12dede25e074d95f8e3181aa5891868f270af8b27ab9a880ad',\n"
    "        'saved_field_measurement': 'FileStandardInfo standard_allocation_bytes, as explicitly used by frozen interface03a6',\n"
    "        'both_allocation_measurements_checked_nonincreasing': True, 'no_actual_source_or_storage_records_modified': True},",
}
for before, after in replacements.items():
    assert source.count(before) == 1, before
    source = source.replace(before, after)
# Bind the preserved failed attempt and original verifier before any future run.
anchor = 'BOUND = {\n'
assert source.count(anchor) == 1
source = source.replace(anchor, anchor +
    "    'qualify_A000166_granular_completion_readonly_prepared_20261005.py': 'a41ca1d3e7d79c8b43b6df3cd9c5fcc532a656b2e98a0ad85ca8ff13fa03fa85',\n" +
    "    'A000166-a41-authorized-review-measurement-mismatch-actual-20261005T082057639017Z.json': 'f2424c9e91970b12dede25e074d95f8e3181aa5891868f270af8b27ab9a880ad',\n")
ast.parse(source)
folder = V / 'proposals/A000166-standard-allocation-verifier-correction-20261005'
folder.mkdir(parents=True, exist_ok=True)
def immutable(path, b):
    if path.exists():
        assert path.read_bytes() == b, path
    else:
        with path.open('xb') as out:
            out.write(b)
immutable(folder / ('original-a41-' + expected + '.py'), data)
candidate = V / 'qualify_A000166_granular_completion_standard_allocation_readonly_prepared_20261005.py'
new = source.encode('utf-8')
immutable(candidate, new)
diff = ''.join(difflib.unified_diff(data.decode('utf-8').splitlines(True), source.splitlines(True), fromfile=original.name, tofile=candidate.name)).encode('utf-8')
diff_path = folder / 'standard-allocation-measurement-only-full-minimal.diff'
immutable(diff_path, diff)
packet = {
    'status': 'PREPARED_UNEXECUTED_SEPARATE_A000166_VERIFIER_MEASUREMENT_CORRECTION',
    'original': {'file': str(original), 'sha256': expected},
    'candidate': {'file': str(candidate), 'sha256': sha(new)},
    'full_minimal_diff': {'file': str(diff_path), 'sha256': sha(diff)},
    'failed_authorized_attempt_record': {'file': str(V / 'A000166-a41-authorized-review-measurement-mismatch-actual-20261005T082057639017Z.json'), 'sha256': 'f2424c9e91970b12dede25e074d95f8e3181aa5891868f270af8b27ab9a880ad'},
    'unchanged_frozen_storage_interface_sha256': '03a6f7118d97e97e646b81cdb5508fab512eb23f65dc1465cd28d141d9cbd99b',
    'actual166_receipt_sha256': 'ba420144481cf50ca830a1e44db44e90de417464fa672491c1f41925036b370f',
    'change': 'Saved allocation equality follows FileStandardInfo standard_allocation_bytes, matching interface03a6; both standard allocation and GetCompressedFileSizeW still must be nonincreasing. Both measurements are recorded without relabelling one as the other.',
    'unchanged_checks': 'All source/artifact/ancestry/CLI/resource/log/custom-closure/sidecar/content/native identity/WOF/chronology/final source rechecks remain.',
    'future_execution_requires_root_review': True,
    'compiler_or_storage_operation_invoked': False,
    'current_receipt_or_original_verifier_modified': False,
}
packet_path = folder / 'prepared-correction-review-packet.json'
packet_bytes = (json.dumps(packet, indent=2) + '\n').encode('utf-8')
immutable(packet_path, packet_bytes)
print(json.dumps({'candidate': str(candidate), 'candidate_sha256': sha(new), 'diff': str(diff_path), 'diff_sha256': sha(diff), 'packet': str(packet_path), 'packet_sha256': sha(packet_bytes)}))
