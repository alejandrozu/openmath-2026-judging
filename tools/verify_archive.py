"""Verify the publication snapshot; mathematical acceptance is a separate process."""
from pathlib import Path
import hashlib, json, sqlite3, sys, os
ROOT=Path(__file__).resolve().parents[1]
if os.name=='nt':ROOT=Path('\\\\?\\'+str(ROOT))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def main():
    m=json.loads((ROOT/'publication-manifest.json').read_text(encoding='utf8'));errors=[]
    for e in m['files']:
        p=ROOT/e['path']
        if not p.is_file():errors.append('Missing '+e['path'])
        elif p.stat().st_size!=e['bytes'] or sha(p)!=e['sha256']:errors.append('Changed '+e['path'])
    d=ROOT/'OpenMath-Judging/catalogue.sqlite'
    if d.exists():
        c=sqlite3.connect('file:'+d.as_posix()+'?mode=ro',uri=True)
        if c.execute('pragma integrity_check').fetchone()[0]!='ok':errors.append('SQLite integrity failure')
        for table,key in [('files','file_entries'),('file_reviews','file_summaries')]:
            if c.execute('select count(*) from '+table).fetchone()[0]!=m['counts'][key]:errors.append('Unexpected '+table+' count')
        c.close()
    review=json.loads((ROOT/'OpenMath-Judging/review/review-data.json').read_text(encoding='utf8'))
    for k,n in [('teams',70),('people',80),('results',226),('problems',70)]:
        if len(review[k])!=n:errors.append('Unexpected review '+k+' count')
    if errors:
        print('\n'.join(errors));return 1
    print(f"Verified {len(m['files'])} publication paths, all byte hashes and review/catalogue counts. Scores remain preliminary.");return 0
if __name__=='__main__':sys.exit(main())
