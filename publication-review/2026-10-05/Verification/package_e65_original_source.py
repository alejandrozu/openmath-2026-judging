"""Preserve digest-verified source data; never execute the recovered image."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,zipfile
from lean_imports import read_imports
BASE=Path(__file__).resolve().parent
raw=(BASE/'e65-original-image-source-review.json').read_bytes()
receipt=json.loads(raw)
assert receipt['status']=='ORIGINAL_SOURCE_LAYER_DIGEST_VERIFIED'
ROOT=BASE/'e65-original-image-source'
image_manifest=json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf8'))
assert (ROOT/'lean-toolchain').read_text(encoding='utf8').strip()=='leanprover/lean4:v4.33.1'
deps=json.loads((BASE/'dependencies/4.33.1/mathlib/lake-manifest.json').read_text(encoding='utf8'))
image_pins={p['name']:p['rev'] for p in image_manifest['packages']}
live_pins={p['name']:p['rev'] for p in deps['packages']}
live_pins['mathlib']='0df444a360eaa60ab8c11dca51a86af692955474'
assert all(live_pins.get(k)==v for k,v in image_pins.items()),'Original dependency pins differ from prepared official cache'
files=[]
for row in receipt['files']:
    rel=Path(row['path'])
    p=ROOT/rel
    assert p.resolve().is_relative_to(ROOT.resolve())
    actual=hashlib.sha256(p.read_bytes()).hexdigest()
    assert actual==row['sha256'],str(rel)
    files.append({'path':rel.as_posix(),'bytes':p.stat().st_size,'sha256':actual})
compat=json.loads((BASE/'builds/official-fc-util433/build-plan.json').read_text(encoding='utf8'))
comparison=[]
for m in compat['modules']:
    p=ROOT/Path(*m['module'].split('.')).with_suffix('.lean')
    h=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
    comparison.append({'module':m['module'],'original_image_sha256':h,'compatible_plan_sha256':m['sha256'],'identical':h==m['sha256']})
entrant=json.loads((BASE/'builds/sundai-erdos3-current/build-plan.json').read_text(encoding='utf8'))
reachable={};pending=[]
for m in entrant['modules']:
    pending += [i for i in read_imports(m['file']) if (ROOT/Path(*i.split('.')).with_suffix('.lean')).exists()]
while pending:
    module=pending.pop()
    if module in reachable:continue
    p=ROOT/Path(*module.split('.')).with_suffix('.lean')
    reachable[module]={'module':module,'relative_source':p.relative_to(ROOT).as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    pending += [i for i in read_imports(p) if (ROOT/Path(*i.split('.')).with_suffix('.lean')).exists() and i not in reachable]
DEST=Path('C:/Users/Propietario/Desktop/OpenMath 2026/Publication package 2026-10-04/Verification/Recovered original dependency sources')
DEST.mkdir(parents=True,exist_ok=True)
archive=DEST/'E65_original_image_sources.zip';temporary=archive.with_suffix('.zip.tmp')
with zipfile.ZipFile(temporary,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for row in files:z.write(ROOT/row['path'],row['path'])
with zipfile.ZipFile(temporary) as z:
    assert z.testzip() is None
    assert set(z.namelist())=={r['path'] for r in files}
    for row in files:assert hashlib.sha256(z.read(row['path'])).hexdigest()==row['sha256']
os.replace(temporary,archive)
result={'generated_utc':datetime.now(timezone.utc).isoformat(),'status':'SOURCE_PROVENANCE_AND_PINS_VERIFIED_NO_ORIGINAL_PROOF_RUN',
        'image':receipt['image'],'verified_layer':receipt['layer_digest'],
        'verified_layer_receipt_sha256':hashlib.sha256(raw).hexdigest(),
        'source_archive':str(archive),'source_archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
        'retained_source_files':len(files),'retained_source_bytes':sum(r['bytes'] for r in files),
        'files':files,'compiler':'4.33.1','dependency_pins':image_pins,'all_pins_match_prepared_official_dependencies':True,
        'compatible_source_comparison':comparison,'original_reachable_entrant_dependency_closure':sorted(reachable.values(),key=lambda r:r['module']),
        'original_FC_Git_revision':'Not supplied by the image; deleted Git metadata and one matching file cannot establish a whole-tree Git revision',
        'qualification':'Image-layer source identity and compiler/dependency pins are recovered. The current compatible FC utility source set has material differences. Its replay must not be labeled an original-image replay.',
        'images_executed':0,'compiled_artifacts_retained':0,'linux_binaries_retained':0}
target=BASE/'e65-original-source-provenance-comparison.json';target.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8')
(DEST/target.name).write_bytes(target.read_bytes())
(DEST/'e65-original-image-source-review.json').write_bytes(raw)
print(json.dumps({'status':result['status'],'source_files':len(files),'source_bytes':result['retained_source_bytes'],
                  'compatible_modules':len(comparison),'identical_modules':sum(r['identical'] for r in comparison),
                  'reachable_original_dependency_modules':len(reachable),'archive_bytes':archive.stat().st_size},indent=2))
