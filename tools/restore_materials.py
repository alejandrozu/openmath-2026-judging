"""Restore verified release-backed files; never execute contestant programs."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, urllib.request, zipfile, shutil, tempfile, os
ROOT=Path(__file__).resolve().parents[1]
if os.name=='nt':ROOT=Path('\\\\?\\'+str(ROOT))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def main():
    a=argparse.ArgumentParser();a.add_argument('--force',action='store_true');args=a.parse_args()
    m=json.loads((ROOT/'publication-manifest.json').read_text(encoding='utf8'))
    cache=ROOT/'.material-cache';cache.mkdir(exist_ok=True)
    for asset in m['assets']:
        pack=cache/asset['name']
        if not pack.exists() or sha(pack)!=asset['sha256']:
            url=f"https://github.com/{m['repository']}/releases/download/{m['release_tag']}/{asset['name']}"
            print('Downloading',asset['name'],flush=True)
            tmp=pack.with_suffix('.partial')
            with urllib.request.urlopen(url) as source,tmp.open('wb') as out:shutil.copyfileobj(source,out)
            if tmp.stat().st_size!=asset['bytes'] or sha(tmp)!=asset['sha256']:raise RuntimeError('Release integrity failure: '+asset['name'])
            tmp.replace(pack)
        with zipfile.ZipFile(pack) as z:
            for entry in m['files']:
                if entry.get('asset')!=asset['name']:continue
                rel=PurePosixPath(entry['path'])
                if rel.is_absolute() or '..' in rel.parts or ':' in str(rel):raise ValueError('Unsafe manifest path')
                target=ROOT.joinpath(*rel.parts)
                if not target.resolve().is_relative_to(ROOT.resolve()):raise ValueError('Unsafe target')
                if target.exists():
                    if sha(target)==entry['sha256']:continue
                    if not args.force:raise RuntimeError('Changed local file preserved: '+str(target)+'; use --force only to restore the archived snapshot')
                target.parent.mkdir(parents=True,exist_ok=True)
                tmp=target.with_name(target.name+'.restore-partial');h=hashlib.sha256();size=0
                with z.open(entry['object']) as source,tmp.open('wb') as out:
                    for block in iter(lambda:source.read(1024*1024),b''):out.write(block);h.update(block);size+=len(block)
                if size!=entry['bytes'] or h.hexdigest()!=entry['sha256']:raise RuntimeError('Object integrity failure: '+entry['path'])
                tmp.replace(target)
    print('All release-backed materials restored. Run python tools/verify_archive.py.')
if __name__=='__main__':main()
