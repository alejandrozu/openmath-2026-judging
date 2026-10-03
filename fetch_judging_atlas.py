import pathlib,urllib.request,gzip,json,re,hashlib,sys
sys.stdout.reconfigure(encoding='utf-8')
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging/judging';ROOT.mkdir(exist_ok=True)
ref='e0e18186a142fb4f61cfc06716aac4fb31bc3b81';name='Ulam_MathDB_ProofAtlas_OPDP_Assessments_v1.8.json.gz';p=ROOT/name
if not p.exists():
    with urllib.request.urlopen('https://media.githubusercontent.com/media/alejandrozu/ulam-opdp-difficulty-atlas/'+ref+'/data/'+name,timeout=120) as response,p.open('wb') as f:
        while chunk:=response.read(1024*1024):f.write(chunk)
assert p.stat().st_size==62168329
assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()=='588153f0f188722c8876399930262ab989d197eb10fdf95c26db0ee4dbe910e5'
print('Downloaded frozen atlas, verified LFS SHA-256',flush=True)
decoder=json.JSONDecoder();matches=[];count=0
patterns=re.compile(r'collatz|kobon|grothendieck constant|busy.?beaver|ramsey multiplicity|multiplicity constant|matrix multiplication|3.{0,3}3 matrices|chern|čern|cerny|heilbronn|star.edge.colou?r|diverg.{0,35}reciprocal|reciprocal.{0,35}diverg|unitary.{0,30}synthesis',re.I)
with gzip.open(p,'rt',encoding='utf-8') as f:
    buf=''
    while not (m:=re.search(r'"records"\s*:\s*\[',buf)):buf+=f.read(262144)
    buf=buf[m.end():]
    while True:
        buf=buf.lstrip(' \r\n\t,')
        if buf.startswith(']'):break
        try:row,end=decoder.raw_decode(buf)
        except json.JSONDecodeError:
            more=f.read(262144)
            if not more:raise
            buf+=more;continue
        buf=buf[end:];count+=1
        target=row.get('source_text',{});text=row.get('title','')+' '+target.get('statement','')
        if patterns.search(text):matches.append(row)
        if count%20000==0:print('Scanned',count,flush=True)
assert count==102819,count
(ROOT/'atlas-target-candidates.json').write_text(json.dumps({'commit':ref,'record_count_scanned':count,'matches':matches},ensure_ascii=False,indent=2),encoding='utf-8')
for r in matches:print(r['problem_id'],r['title'][:110],r.get('intrinsic_difficulty',{}).get('score'),r.get('assessment_gate'))
print('Candidate records',len(matches))
