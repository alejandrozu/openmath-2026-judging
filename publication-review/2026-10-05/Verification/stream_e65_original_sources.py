"""Hash an immutable public image layer and retain only source/manifest data.

No image is run. No Linux executable or compiled artifact is extracted.
"""
from pathlib import Path, PurePosixPath
import hashlib, http.client, json, os, re, shutil, tarfile, time, urllib.error, urllib.parse, urllib.request
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parent
OUT = BASE / 'e65-original-image-source'
OUT.mkdir(exist_ok=True)
RECEIPT = BASE / 'e65-original-image-source-review.json'
metadata = json.loads((BASE / 'e65-immutable-image-metadata-review.json').read_text(encoding='utf8'))
layer = next(x for x in metadata['layers'] if x['digest'] ==
    'sha256:fa7e7ffe483461956ae4428fea688a6f7f91253dc986d6f060a7b4ba2f8451c4')
result = {'started_utc': datetime.now(timezone.utc).isoformat(), 'status': 'RUNNING_SOURCE_ONLY_STREAM',
    'image': metadata['image'], 'layer_digest': layer['digest'], 'layer_expected_bytes': layer['size'],
    'source_root': str(OUT), 'files': [], 'layers_executed': 0,
    'compiled_artifacts_retained': 0, 'linux_binaries_retained': 0}
if RECEIPT.exists():
    old = RECEIPT.read_bytes()
    attempt = 1
    archived = BASE / ('e65-original-image-source-review-attempt-' + str(attempt) + '.json')
    while archived.exists():
        attempt += 1
        archived = BASE / ('e65-original-image-source-review-attempt-' + str(attempt) + '.json')
    archived.write_bytes(old)
    result['previous_attempt'] = {'receipt': archived.name, 'sha256': hashlib.sha256(old).hexdigest()}

def save():
    temp = RECEIPT.with_suffix('.json.tmp')
    temp.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf8')
    os.replace(temp, RECEIPT)

class StripCrossHostAuth(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        redirected = super().redirect_request(request, fp, code, msg, headers, newurl)
        if redirected and urllib.parse.urlsplit(request.full_url).netloc != urllib.parse.urlsplit(newurl).netloc:
            redirected.remove_header('Authorization')
        return redirected

def anonymous_token():
    url = 'https://ghcr.io/token?' + urllib.parse.urlencode({
        'service': 'ghcr.io', 'scope': 'repository:ottogin/lean-mathlib:pull'})
    with urllib.request.urlopen(url, timeout=30) as response:
        return json.loads(response.read(65536))['token']

class HashedReader:
    def __init__(self, opener, token):
        self.opener = opener
        self.token = token
        self.stream = None
        self.segment_end = -1
        self.sha = hashlib.sha256()
        self.count = 0
        self.next_progress = 256 * 1024 * 1024
        self.next_guard = 0
        self.transport_retries = 0
        result['range_requests'] = []
    def close(self):
        if self.stream:
            self.stream.close()
            self.stream = None
    def new_range(self):
        self.close()
        end = min(layer['size'] - 1, self.count + 128 * 1024 * 1024 - 1)
        for attempt in range(2):
            request = urllib.request.Request('https://ghcr.io/v2/ottogin/lean-mathlib/blobs/' + layer['digest'],
                headers={'Authorization': 'Bearer ' + self.token,
                         'Range': 'bytes=' + str(self.count) + '-' + str(end)})
            try:
                self.stream = self.opener.open(request, timeout=60)
                break
            except urllib.error.HTTPError as error:
                if error.code != 401 or attempt:
                    raise
                self.token = anonymous_token()
        content_range = self.stream.headers.get('Content-Range', '')
        match = re.fullmatch(r'bytes (\d+)-(\d+)/(\d+)', content_range)
        if (self.stream.status != 206 or not match or int(match[1]) != self.count
            or int(match[3]) != layer['size'] or int(match[2]) > end):
            raise RuntimeError('Unexpected bounded Range response')
        self.segment_end = int(match[2])
        result['range_requests'].append({'start': self.count, 'end': self.segment_end,
            'status': self.stream.status, 'content_range': content_range})
    def read(self, count=65536):
        if self.count == layer['size']:
            return b''
        now = time.monotonic()
        if now >= self.next_guard:
            if shutil.disk_usage(BASE).free < 1024 ** 3:
                raise RuntimeError('SOURCE_CAPTURE_ENVIRONMENT_DISK_RESERVE')
            self.next_guard = now + 0.5
        if count < 0:
            count = 65536
        while True:
            if self.stream is None or self.count > self.segment_end:
                self.new_range()
            try:
                data = self.stream.read(min(count, self.segment_end + 1 - self.count))
            except (OSError, http.client.IncompleteRead):
                data = b''
            if data:
                self.transport_retries = 0
                break
            self.close()
            self.transport_retries += 1
            if self.transport_retries > 8:
                raise RuntimeError('Repeated Range transport truncation')
        self.sha.update(data)
        self.count += len(data)
        if self.count >= self.next_progress:
            print(json.dumps({'compressed_bytes_read': self.count, 'sources_retained': len(result['files'])}), flush=True)
            self.next_progress += 256 * 1024 * 1024
        return data

save()
started = time.monotonic()
reader = None
try:
    opener = urllib.request.build_opener(StripCrossHostAuth())
    reader = HashedReader(opener, anonymous_token())
    try:
        with tarfile.open(fileobj=reader, mode='r|gz') as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                if name.is_absolute() or '..' in name.parts:
                    raise RuntimeError('Unsafe archive member path')
                if not member.isfile() or '.wh.' in name.name:
                    continue
                parts = name.parts
                if parts[:2] != ('opt', 'formal-conjectures'):
                    continue
                relative = PurePosixPath(*parts[2:])
                root_source = member.name.endswith('.lean') and '.lake' not in parts
                metadata_file = relative.name in {'lake-manifest.json', 'lean-toolchain', 'lakefile.lean', 'lakefile.toml',
                                                  'LICENSE', 'LICENSE.txt', 'LICENSE.md', 'NOTICE'}
                if not (root_source or metadata_file):
                    continue
                if member.size > 16 * 1024 * 1024:
                    raise RuntimeError('Unexpectedly large selected source member')
                target = OUT.joinpath(*relative.parts)
                target.resolve().relative_to(OUT.resolve())
                target.parent.mkdir(parents=True, exist_ok=True)
                with archive.extractfile(member) as source:
                    raw = source.read(member.size + 1)
                if len(raw) != member.size:
                    raise RuntimeError('Source member size mismatch')
                target.write_bytes(raw)
                result['files'].append({'path': relative.as_posix(), 'bytes': len(raw),
                                        'sha256': hashlib.sha256(raw).hexdigest()})
        # Complete compressed-byte identity even if tar reaches its logical EOF
        # before trailing gzip/tar padding ends.
        while reader.read(1024 * 1024):
            pass
    finally:
        reader.close()
    actual_digest = 'sha256:' + reader.sha.hexdigest()
    if actual_digest != layer['digest'] or reader.count != layer['size']:
        raise RuntimeError('Full immutable layer identity mismatch')
    root_manifest = OUT / 'lake-manifest.json'
    if not root_manifest.exists():
        raise RuntimeError('Original root lake-manifest was not found')
    packages = json.loads(root_manifest.read_text(encoding='utf8')).get('packages', [])
    result.update({'status': 'ORIGINAL_SOURCE_LAYER_DIGEST_VERIFIED', 'actual_layer_digest': actual_digest,
        'compressed_bytes_read': reader.count, 'retained_bytes': sum(f['bytes'] for f in result['files']),
        'original_dependency_packages': [{'name': p.get('name'), 'url': p.get('url'),
                                         'rev': p.get('rev'), 'inputRev': p.get('inputRev')} for p in packages],
        'conclusion': 'Selected original image sources and manifests were recovered from a fully digest-verified immutable layer. The image was not executed; this is dependency/source provenance, not proof replay. The deleted whole FC Git revision is still not inferred solely from source matches.'})
except Exception as error:
    result.update({'status': 'SOURCE_STREAM_INCOMPLETE_UNVERIFIED', 'error_type': type(error).__name__,
        'error': str(error)[:300], 'compressed_bytes_read': reader.count if reader else 0,
        'conclusion': 'Retained partial source bytes are unverified against the complete layer and must not be represented as exact image recovery.'})
finally:
    result['finished_utc'] = datetime.now(timezone.utc).isoformat()
    result['seconds'] = round(time.monotonic() - started, 2)
    save()
    print(json.dumps({'status': result['status'], 'compressed_bytes_read': result.get('compressed_bytes_read', 0),
        'retained_files': len(result['files']), 'retained_bytes': result.get('retained_bytes'),
        'original_dependency_packages': result.get('original_dependency_packages', [])}, indent=2), flush=True)
if result['status'] != 'ORIGINAL_SOURCE_LAYER_DIGEST_VERIFIED':
    raise SystemExit(1)
