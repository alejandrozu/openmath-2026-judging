"""Read public immutable OCI metadata only; never run or unpack an image."""
from pathlib import Path
import hashlib, json, os, urllib.request, urllib.parse
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parent
REPO = 'ottogin/lean-mathlib'
DIGEST = 'sha256:964547ad81e109c78545512867bae70b710c55d833078674878faad7de0ebb85'
token_url = 'https://ghcr.io/token?' + urllib.parse.urlencode({'service': 'ghcr.io', 'scope': 'repository:' + REPO + ':pull'})
with urllib.request.urlopen(token_url, timeout=30) as response:
    token = json.loads(response.read(65536))['token']

def fetch(url, expected, limit):
    request = urllib.request.Request(url, headers={'Authorization': 'Bearer ' + token,
        'Accept': 'application/vnd.docker.distribution.manifest.v2+json, application/vnd.oci.image.manifest.v1+json'})
    with urllib.request.urlopen(request, timeout=30) as response:
        raw = response.read(limit + 1)
    if len(raw) > limit:
        raise RuntimeError('Metadata size exceeds bounded read')
    sha = 'sha256:' + hashlib.sha256(raw).hexdigest()
    if sha != expected:
        raise RuntimeError('Immutable metadata digest mismatch')
    return json.loads(raw), sha, len(raw)

manifest_url = 'https://ghcr.io/v2/' + REPO + '/manifests/' + DIGEST
manifest, manifest_sha, manifest_bytes = fetch(manifest_url, DIGEST, 2 * 1024 * 1024)
config_digest = manifest['config']['digest']
config_url = 'https://ghcr.io/v2/' + REPO + '/blobs/' + config_digest
config, config_sha, config_bytes = fetch(config_url, config_digest, 2 * 1024 * 1024)
histories = [h.get('created_by', '') for h in config.get('history', []) if 'formal-conjectures' in h.get('created_by', '')]
selected_labels = {key: value for key, value in config.get('config', {}).get('Labels', {}).items()
                   if key in {'org.opencontainers.image.revision', 'org.opencontainers.image.source', 'org.opencontainers.image.version'}}
result = {'checked_utc': datetime.now(timezone.utc).isoformat(), 'status': 'IMMUTABLE_METADATA_DIGESTS_VERIFIED',
    'image': 'ghcr.io/' + REPO + '@' + DIGEST,
    'manifest_url': manifest_url, 'manifest_sha256': manifest_sha, 'manifest_bytes': manifest_bytes,
    'config_url': config_url, 'config_sha256': config_sha, 'config_bytes': config_bytes,
    'platform': {'os': config.get('os'), 'architecture': config.get('architecture')},
    'created': config.get('created'), 'selected_revision_labels': selected_labels,
    'formal_conjectures_history': histories,
    'layers': manifest['layers'],
    'conclusion': 'The digest-verified config clones Formal Conjectures from its default branch and deletes repository/package .git directories. The inspected metadata does not give an immutable FC or Mathlib revision label. Recovering the exact root lake-manifest from the 3.33 GB source/cache layer would be a separate streamed source inspection; no layer, Linux binary or compiled cache was downloaded or executed by this check. Compatible Windows replay remains distinct from replay of the original image.',
    'authentication': 'Anonymous pull token used only in memory; not saved or printed.'}
target = BASE / 'e65-immutable-image-metadata-review.json'
temporary = target.with_suffix('.json.tmp')
temporary.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf8')
os.replace(temporary, target)
print(json.dumps({'status': result['status'], 'metadata_bytes': manifest_bytes + config_bytes,
                  'revision_labels': selected_labels, 'layer_downloaded': False}, indent=2))
