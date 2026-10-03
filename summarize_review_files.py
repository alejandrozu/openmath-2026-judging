"""Bounded static content index. Never imports or executes contestant code."""
from pathlib import Path
import sqlite3,json,zipfile,re,datetime,collections,io
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging'
d=json.loads((ROOT/'review/review-data.json').read_text(encoding='utf8'))
results={r['id']:r for r in d['results']};links=d['file_result_links']
c=sqlite3.connect(ROOT/'catalogue.sqlite');c.row_factory=sqlite3.Row
c.execute('CREATE TABLE IF NOT EXISTS file_reviews(file_id INTEGER PRIMARY KEY,summary TEXT NOT NULL,method TEXT NOT NULL,result_ids TEXT NOT NULL,content_read_bytes INTEGER NOT NULL,error TEXT)')
archives={};stats=collections.Counter();batch=[]
existing=set(x[0] for x in c.execute('select file_id from file_reviews'))
stats.update(dict(c.execute('select method,count(*) from file_reviews group by method').fetchall()))
binary={'.zip','.7z','.gz','.png','.jpg','.jpeg','.gif','.webp','.npz','.npy','.pkl','.olean','.ilean','.dll','.exe','.o','.pyc','.sqlite','.db','.mp4','.wav','.bin','.dat'}
roles={'01-submission':'Claims and submission scope','02-papers':'Exposition or paper','03-novelty':'Novelty/prior comparison','04-formal-proofs':'Formal source','05-certificates':'Certificate/witness data','06-data':'Result dataset','07-reproduction':'Checker/reproduction source','08-logs':'Experimental or author-reported verification log','09-team':'Attribution/provenance','10-build':'Build or library dependency','11-other':'Supporting artifact','12-correspondence':'Message/receipt evidence','13-archives':'Original packet archive'}
def read(row,limit):
 if row['local_path']:
  with (ROOT/row['local_path']).open('rb') as f:return f.read(limit)
 ap=row['archive_path']
 if ap not in archives:archives[ap]=zipfile.ZipFile(ROOT/ap)
 with archives[ap].open(row['archive_member']) as f:return f.read(limit)
rows=c.execute('SELECT * FROM files ORDER BY id').fetchall()
print(json.dumps({'categories':dict(collections.Counter(r['category'] for r in rows))}),flush=True)
for i,row in enumerate(rows):
 if row['id'] in existing:continue
 rid=links.get(str(row['id']),[]);ext=Path(row['original_path']).suffix.lower();cat=row['category']
 summary=roles[cat]+'. Topic: '+row['topic']+'. ';method='role-and-catalogue';error=None;n=0
 try:
  if ext not in binary:
   limit=131072 if rid or cat in ['01-submission','03-novelty','09-team'] else 8192
   raw=read(row,limit);n=len(raw);complete=n>=row['bytes'];text=raw.decode('utf8',errors='replace')
   if ext=='.pdf':
    if row['bytes']<8_000_000:
     from pypdf import PdfReader
     pdf=PdfReader(io.BytesIO(read(row,row['bytes'])));text='\n'.join((p.extract_text() or '') for p in pdf.pages[:3]);n=row['bytes'];summary+='PDF '+str(len(pdf.pages))+' pages. ';method='first-three-PDF-pages'
    else:text='';method='binary-PDF-role'
   else:method='complete-small-file' if complete else 'bounded-text-prefix'
   if ext in ['.lean','.v','.thy','.agda']:
    imports=re.findall(r'^\s*import\s+([^\n]+)',text,re.M)[:5]
    declarations=re.findall(r'\b(?:theorem|lemma|def|structure|class)\s+([\w.]+)',text)[:8]
    summary+='Declarations: '+(', '.join(declarations) or 'none in inspected prefix')+'. '
    if imports:summary+='Imports: '+', '.join(imports)+'. '
    if re.search(r'\bsorry\b|\badmit\b',text):summary+='Admission-like token appears in inspected source; comments, proposition macros and reachable proof dependencies must be distinguished. '
    summary+='Static reading alone does not certify statement fidelity or kernel closure.'
   elif ext in ['.json','.jsonl']:
    try:
     obj=json.loads(text)
     if isinstance(obj,dict):
      summary+='Fields: '+', '.join(list(obj)[:12])+'. '
      vals=[]
      for k,v in obj.items():
       if re.search('status|verdict|objective|score|bound|target|triangle|count|^n$|^result$',k,re.I) and isinstance(v,(str,int,float,bool)):
        vals.append(k+'='+str(v)[:65])
      if vals:summary+='Recorded values: '+', '.join(vals[:6])+'. '
     elif isinstance(obj,list):summary+='Array of '+str(len(obj))+' records. '
    except (ValueError,TypeError):summary+='Structured-data prefix; complete parse not available in bounded read. '
    summary+='Author/dataset labels are evidence of what was recorded, not an independently proved global theorem.'
   elif cat in ['07-reproduction','10-build']:
    names=re.findall(r'^(?:def|class|function)\s+([\w]+)',text,re.M)[:6]
    summary+=('Entry points: '+', '.join(names)+'. ' if names else '')+'Static implementation/configuration; not executed and not mathematical proof by itself.'
   else:
    clean=re.sub(r'\s+',' ',text).strip()
    if clean:summary+='Content lead (source excerpt): '+clean[:300]+'. '
    summary+=('Author-reported log; independent checking still required.' if cat=='08-logs' else 'Read alongside the linked contribution assessment.')
  else:summary+='Binary/dependency/packet retained; content is summarized by artifact role and its linked mathematical claim, not decoded or executed.'
 except Exception as exc:error=type(exc).__name__+': '+str(exc)[:160];summary+='READ GAP: '+error;method='read-error'
 if rid:
  summary+=' Linked assessment: '+'; '.join(x+': '+results[x]['thoughts'][:260] for x in rid[:3])
 stats[method]+=1;batch.append((row['id'],summary,method,json.dumps(rid),n,error))
 if len(batch)>=1000:
  c.executemany('INSERT OR REPLACE INTO file_reviews VALUES(?,?,?,?,?,?)',batch);c.commit();batch=[]
 if (i+1)%25000==0:print(json.dumps({'done':i+1,'methods':dict(stats)}),flush=True)
if batch:c.executemany('INSERT OR REPLACE INTO file_reviews VALUES(?,?,?,?,?,?)',batch);c.commit()
for z in archives.values():z.close()
report={'created_at':datetime.datetime.now().astimezone().isoformat(),'catalogue_files':len(rows),'summaries':c.execute('select count(*) from file_reviews').fetchone()[0],'methods':dict(stats),'read_error_count':c.execute('select count(*) from file_reviews where error is not null').fetchone()[0],'meaning':'Every file has a summary; textual summaries use bounded static content, PDF first3pages, binary files role-level. This is not a claim that every file was exhaustively manually read or freshly verified.'}
(ROOT/'review/file-summary-coverage.json').write_text(json.dumps(report,indent=2),encoding='utf8');print(json.dumps(report),flush=True)
