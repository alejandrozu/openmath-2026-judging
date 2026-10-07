"""Pinned source/template preparation and actual log/PDF inventory, stdlib only."""
from pathlib import Path, PurePosixPath
from urllib.request import Request, urlopen
from datetime import datetime, timezone
from io import BytesIO
import argparse
import hashlib
import json
import os
import re
import stat
import zipfile

SPRINGER_URL = 'https://media.springer.com/full/springer-instructions-for-authors-assets/zip/468198_LaTeX_DL_468198_01072021.zip'
ZIP_SHA = '2e5bbfde3deae204cf6f2926ba2d9088d02bec969a442f01db1fc5b373074453'
ZIP_BYTES = 189200
MEMBERS = {
    'LaTeX_DL_468198_240419/svjour3.cls': 'e9840b9fdd767d9ecf92e2c79319084b4764810ed27c792872ac8be8ceae0a07',
    'LaTeX_DL_468198_240419/svglov3.clo': 'a0b9f3522e6ef83f3dd8d5901c74745d515355ccd61f0a148668283aabdb5467',
}

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def safe_path(root, relative):
    part = PurePosixPath(relative)
    assert not part.is_absolute() and '..' not in part.parts
    assert re.fullmatch(r'[A-Za-z0-9_.\-/]+', relative)
    p = (root / Path(*part.parts)).resolve()
    assert p.is_relative_to(root)
    return p

def load_manifest(args):
    p = Path(args.manifest).resolve()
    assert re.fullmatch(r'[0-9a-f]{64}', args.manifest_sha256)
    assert sha(p) == args.manifest_sha256
    d = json.loads(p.read_text(encoding='utf8'))
    assert d['schema'] == 'publication-22-tex-replay-source-manifest-v1'
    assert d['status'] == 'FROZEN_EXACT_SOURCES_READY_FOR_TYPESETTING_BUILD_NOT_YET_COMPILED'
    assert d['standalone_count'] == 21 and len(d['sources']) == 22
    assert sum(x['role'] == 'ROBERT_SVJOUR3_SUBMISSION_DERIVATIVE' for x in d['sources']) == 1
    assert sum(x['role'] == 'CURRENT_STANDALONE' for x in d['sources']) == 21
    root = p.parent.resolve()
    seen = set()
    for row in d['sources']:
        assert row['relative_path'] not in seen
        seen.add(row['relative_path'])
        f = safe_path(root, row['relative_path'])
        assert f.suffix == '.tex' and f.is_file()
        assert f.stat().st_size == row['bytes'] and sha(f) == row['sha256']
    return root, d

def prepare(args):
    root, d = load_manifest(args)
    target_row = next(x for x in d['sources'] if x['role'] == 'ROBERT_SVJOUR3_SUBMISSION_DERIVATIVE')
    target = safe_path(root, target_row['relative_path']).parent
    req = Request(SPRINGER_URL, headers={'User-Agent': 'OpenMath-typesetting-reproduction'})
    with urlopen(req, timeout=45) as f:
        assert f.status == 200
        blob = f.read(ZIP_BYTES + 1)
    assert len(blob) == ZIP_BYTES and hashlib.sha256(blob).hexdigest() == ZIP_SHA
    z = zipfile.ZipFile(BytesIO(blob))
    assert z.testzip() is None
    seen = set()
    for e in z.infolist():
        name = PurePosixPath(e.filename)
        assert not name.is_absolute() and '..' not in name.parts and not any(':' in p for p in name.parts)
        assert e.filename.casefold() not in seen
        seen.add(e.filename.casefold())
        assert not stat.S_ISLNK(e.external_attr >> 16)
        assert e.file_size <= 2 * 1024 * 1024
    records = []
    for name, expected in MEMBERS.items():
        data = z.read(name)
        actual = hashlib.sha256(data).hexdigest()
        assert expected and actual == expected
        dest = target / PurePosixPath(name).name
        if dest.exists():
            assert dest.is_file() and sha(dest) == actual
        else:
            dest.write_bytes(data)
        records.append({'file': dest.relative_to(root).as_posix(), 'bytes': len(data), 'sha256': actual})
    load_manifest(args)
    output = root / 'actual_template_and_source_preflight.json'
    assert not output.exists()
    output.write_text(json.dumps({'status': 'ACTUAL_PINNED_TEMPLATE_SOURCE_PREFLIGHT_PASS_NOT_COMPILATION',
        'checked_utc': datetime.now(timezone.utc).isoformat(), 'manifest_sha256': args.manifest_sha256,
        'template_url': SPRINGER_URL, 'template_ZIP_SHA256': ZIP_SHA, 'runtime_only_members': records,
        'no_public_vendor_redistribution_claim': True, 'source_count': 22,
        'source_files_unchanged': True}, indent=2)+'\n', encoding='utf8')
    if args.github_output:
        rel_root = root.relative_to(Path.cwd().resolve()).as_posix()
        values = '\n'.join(rel_root+'/'+x['relative_path'] for x in d['sources'])
        with Path(args.github_output).open('a', encoding='utf8') as f:
            f.write('root_files<<TEX_REPLAY_ROOT_FILES\n'+values+'\nTEX_REPLAY_ROOT_FILES\n')

def record(args):
    root, d = load_manifest(args)
    rows=[]
    all_pass = args.compilation_outcome == 'success'
    for source in d['sources']:
        f=safe_path(root, source['relative_path'])
        pdf=f.with_suffix('.pdf'); log=f.with_suffix('.log')
        issues=[]; pages=None; engine_output_format=None
        if not pdf.is_file():
            issues.append('PDF_MISSING')
        elif not (pdf.read_bytes().startswith(b'%PDF-') and b'%%EOF' in pdf.read_bytes()[-2048:]):
            issues.append('PDF_HEADER_OR_FINAL_EOF_MISSING')
        if not log.is_file():
            issues.append('LOG_MISSING')
        else:
            text=log.read_text(encoding='utf8', errors='replace')
            matches=re.findall(r'Output written on\s+.*?\.(pdf|xdv)\s*\((\d+)\s+pages?\b', text, flags=re.S)
            if matches:
                engine_output_format=matches[-1][0]
                pages=int(matches[-1][1])
            else:
                issues.append('NO_ACTUAL_LOG_PAGE_COUNT')
            if re.search(r'(^!|Emergency stop|Fatal error occurred)',text,flags=re.M):
                issues.append('COMPILER_ERROR_DIAGNOSTIC')
            if source['role']=='ROBERT_SVJOUR3_SUBMISSION_DERIVATIVE' and pages is not None and pages>25:
                issues.append('SVJOUR3_PAGE_COUNT_EXCEEDS_25')
        all_pass = all_pass and not issues
        row={'source':source,'issues':issues,'pages_from_actual_compiler_log':pages,
             'actual_engine_log_output_format':engine_output_format,
             'PDF':None,'log':None}
        for kind,p in [('PDF',pdf),('log',log)]:
            if p.is_file():
                row[kind]={'file':p.relative_to(root).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
        rows.append(row)
    load_manifest(args)
    out=root/'actual_typesetting_result.json'
    assert not out.exists()
    data={'status':'ACTUAL_ALL22_COMPILED_WITH_SVJOUR3_AT_MOST25_PAGES_REQUIRES_VISUAL_QA' if all_pass else 'ACTUAL_TYPESETTING_FAILURE_OR_INCOMPLETE_PRESERVED',
          'checked_utc':datetime.now(timezone.utc).isoformat(),'compilation_step_outcome':args.compilation_outcome,
          'manifest_sha256':args.manifest_sha256,'source_count':22,'results':rows,
          'run':{k:os.environ.get(k) for k in ['GITHUB_SHA','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT']},
          'actual_page_counts_are_log_observations_not_visual_QA':True,
          'XeLaTeX_XDV_log_count_accepted_only_with_complete_PDF_and_successful_compilation_step':True,
          'math_proof_or_journal_acceptance_or_author_approval_claimed':False}
    out.write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'status':data['status'],'result_file':str(out)},indent=2))
    if not all_pass:
        raise SystemExit(1)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['prepare','record'])
    p.add_argument('--manifest',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--github-output')
    p.add_argument('--compilation-outcome',default='not_run')
    a=p.parse_args()
    (prepare if a.mode=='prepare' else record)(a)

if __name__=='__main__':
    main()
