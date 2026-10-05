"""Read-only extension of root's completed-owned artifact storage proposal.

No compression, copy, deletion, install or scientific/compiler operation occurs.
Only own completed outputs and stable generated metadata/log files are inventoried.
"""
from pathlib import Path
from collections import defaultdict
from datetime import datetime, timezone
import hashlib, json, os, shutil, time
from receipt_io import read_bytes_shared

BASE = Path(__file__).resolve().parent
DESKTOP = Path('C:/Users/Propietario/Desktop/OpenMath 2026/Publication package 2026-10-04/Verification')
PRODUCER = BASE / 'assess_completed_own_artifact_storage_readonly.py'
OLD = BASE / 'completed-own-artifact-storage-compression-proposal-20261005.json'
OLD_SHA = 'b2c44a282a7ea2c07285ea4b8832d4f4f999fff5cf6e4e13645ad34486a01a96'

def sha(raw): return hashlib.sha256(raw).hexdigest()
assert sha(OLD.read_bytes()) == OLD_SHA
# Reuse only the reviewed native metadata definitions, not its executing producer.
producer_source = PRODUCER.read_text(encoding='utf8')
prefix, marker, remainder = producer_source.partition('before_processes=process_snapshot()')
assert marker and 'def native_metadata(path):' in prefix
namespace = {'__file__':str(PRODUCER), '__name__':'readonly_native_metadata_definitions'}
exec(compile(prefix, str(PRODUCER), 'exec'), namespace)
native_metadata = namespace['native_metadata']
process_snapshot = namespace['process_snapshot']
original = json.loads(OLD.read_bytes())
started = time.time()
before_processes = process_snapshot()

def protected_name(path):
    name = str(path).replace('\\','/').lower()
    return 'dms' in name or 'a000224' in name

def eligible_identity(info):
    return (info['link_count']==1 and not info['FILE_ATTRIBUTE_REPARSE_POINT']
            and not info['FILE_ATTRIBUTE_ENCRYPTED'])

def summarize(rows):
    distinct = {}
    for row in rows:
        key = (row['volume_serial'],row['file_index_high'],row['file_index_low'])
        distinct.setdefault(key,row)
    values = list(distinct.values())
    return {'paths':len(rows),'unique_inodes':len(values),
        'logical_bytes':sum(r['logical_bytes'] for r in values),
        'stored_bytes_GetCompressedFileSizeW':sum(r['stored_bytes_GetCompressedFileSizeW'] for r in values),
        'standard_allocation_bytes':sum(r['standard_allocation_bytes'] or 0 for r in values)}

completed = []
excluded = []
for row in original['exact_proposed_owned_output_files']:
    path = Path(row['file']).resolve()
    if protected_name(path):
        excluded.append({'file':str(path),'reason':'All DMS/A000 active or protected route paths are excluded wholesale'});continue
    info = native_metadata(path)
    if not eligible_identity(info):
        excluded.append({'file':str(path),'reason':'Shared, encrypted or existing reparse/WOF inode','metadata':info});continue
    assert info['logical_bytes']==row['expected_logical_bytes']
    completed.append({**info,'expected_content_sha256_from_own_completed_receipt':row['expected_content_sha256'],
        'own_completed_receipt_provenance':row['provenance'],
        'proposed_lzx_role':'Potential stronger lossless LZX pilot; additional gain has not been measured',
        'current_compression_interpretation':'ordinary NTFS-compressed' if info['FILE_ATTRIBUTE_COMPRESSED'] else 'not ordinarily NTFS-compressed'})

# Only generated verification files within these exact task-owned metadata scopes.
scopes = [BASE]
for folder in ['proposals','operational_history','runner_versions','m2_runner_source_archives',
               'runner_source_archives','native_runner_source_versions','guarded-source-logs',
               'attempt_receipts','native_object_pilots','queue_snapshot_history']:
    path = BASE/folder
    if path.is_dir():scopes.append(path)
if DESKTOP.is_dir():scopes.append(DESKTOP)
metadata = []
seen = set()
suffixes = {'.json','.py','.diff','.txt','.log','.md','.csv'}
mutable_names = ('register','summary','current-queue','remaining-main-granular-queue',
                 'package_manifest','package_index','hold-','watchdog')
for scope in scopes:
    if scope == BASE:
        paths = [p for p in scope.iterdir() if p.is_file()]
    else:
        paths = []
        for directory, folders, files in os.walk(scope, followlinks=False):
            folders[:] = [n for n in folders if not any(t in n.lower() for t in
                ['source archives','dependency sources','runtimes','dependencies','builds'])
                and not (Path(directory)/n).is_symlink()]
            paths.extend(Path(directory)/name for name in files)
    for candidate in paths:
        path = candidate.resolve()
        if str(path) in seen:continue
        seen.add(str(path))
        if candidate.is_symlink() or path.suffix.lower() not in suffixes or protected_name(path):continue
        if not (path.is_relative_to(BASE.resolve()) or path.is_relative_to(DESKTOP.resolve())):continue
        if any(t in path.name.lower() for t in mutable_names):continue
        try:
            pre = path.stat()
            if pre.st_mtime > started-600:continue
            raw = read_bytes_shared(path)
            if path.suffix.lower()=='.json':
                doc = json.loads(raw)
                state = doc.get('status','') if isinstance(doc,dict) else ''
                if state in {'RUNNING','WAITING_THIRD_WORKER_DISPATCH_GATES','WAITING_RESOURCE_DISPATCH_GATES'}:continue
                if isinstance(doc,dict) and doc.get('current_module'):continue
            info = native_metadata(path)
            post = path.stat()
            if (pre.st_size,pre.st_mtime_ns)!=(post.st_size,post.st_mtime_ns):continue
            if not eligible_identity(info):continue
            metadata.append({**info,'content_sha256':sha(raw),'measured_stable_pre_post':True,
                'last_write_at_least600_seconds_before_assessment':True,
                'scope':'desktop copied verification metadata' if path.is_relative_to(DESKTOP.resolve()) else 'task generated verification metadata/source-runner/log archive',
                'still_requires_future_quiescence_and_content_recheck_before_any_mutation':True})
        except (OSError,ValueError) as error:
            excluded.append({'file':str(path),'reason':'Read-only metadata could not be stably inventoried','error':str(error)})

groups = defaultdict(list)
for row in metadata:groups[row['scope']].append(row)
out = {'status':'READ_ONLY_COMPLETED_OWN_STRONGER_LZX_AND_STABLE_METADATA_ASSESSMENT_NO_ACTION',
    'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(Path(__file__).read_bytes()),
    'prior_root_proposal':str(OLD),'prior_root_proposal_sha256':OLD_SHA,
    'native_metadata_definition_producer_sha256':sha(PRODUCER.read_bytes()),
    'processes_before':before_processes,'processes_after':process_snapshot(),
    'current_disk_free_bytes':shutil.disk_usage(BASE).free,
    'completed_owned_output_summary':summarize(completed),'completed_owned_outputs':completed,
    'stable_generated_metadata_summary':summarize(metadata),'stable_generated_metadata':metadata,
    'metadata_scope_totals':{scope:summarize(rows) for scope,rows in groups.items()},
    'top_metadata_by_stored_bytes':sorted(metadata,key=lambda r:r['stored_bytes_GetCompressedFileSizeW'],reverse=True)[:30],
    'excluded_special_or_protected_paths':excluded,
    'savings_qualification':{'guaranteed_additional_savings_bytes':0,
        'absolute_loose_upper_bound_bytes':summarize(completed)['stored_bytes_GetCompressedFileSizeW']+summarize(metadata)['stored_bytes_GetCompressedFileSizeW'],
        'ordinary_NTFS_to_LZX_recompression_candidate_bytes':sum(r['stored_bytes_GetCompressedFileSizeW'] for r in completed+metadata if r['FILE_ATTRIBUTE_COMPRESSED']),
        'interpretation':'Existing allocated/stored bytes are measured. Stronger-LZX gain is not guaranteed; an independently reviewed small pilot would be needed to measure it.'},
    'future_contract':'No actual action authorized by this metadata. Exact root-reviewed targets, renewed task/loader quiescence, SHA/file-ID/linkcount1 preservation, bounded temporary-allocation pilot, continuous reserve and single compressor required.',
    'explicit_exclusions':['all DMS/A000 paths and protected/shared inodes','live or recently written metadata',
        'entrant archives/scientific Lean sources','runtime/dependencies/user files/apps/system/pagefile'],
    'compression_deletion_copy_install_compiler_source_or_existing_receipt_mutation_performed':False}
target=BASE/'completed-own-stronger-lzx-and-stable-metadata-storage-assessment-20261005.json'
with target.open('x',encoding='utf8',newline='\n') as stream:json.dump(out,stream,indent=2);stream.write('\n')
print(json.dumps({'packet':str(target),'sha256':sha(target.read_bytes()),'completed_outputs':out['completed_owned_output_summary'],
    'stable_metadata':out['stable_generated_metadata_summary'],'free_disk':out['current_disk_free_bytes'],'actions':0},indent=2))
