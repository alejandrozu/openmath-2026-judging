import sys,pathlib,json
sys.stdout.reconfigure(encoding='utf-8')
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT))
from library_core import connect,read_bytes
db=connect(ROOT)
if sys.argv[1]=='read':
    for fid in sys.argv[2:]:
        r=db.execute('SELECT * FROM files WHERE id=?',(int(fid),)).fetchone()
        print('\nFILE',fid,r['team_id'],r['original_path'],'VERSION',r['version'])
        print(read_bytes(ROOT,r).decode('utf-8',errors='replace'))
elif sys.argv[1]=='list':
    team=sys.argv[2];pattern=sys.argv[3] if len(sys.argv)>3 else '%'
    for r in db.execute('SELECT id,original_path,bytes,version FROM files WHERE team_id=? AND original_path LIKE ? ORDER BY original_path,id',(team,pattern)):
        print(r['id'],r['original_path'],r['bytes'],r['version'])
