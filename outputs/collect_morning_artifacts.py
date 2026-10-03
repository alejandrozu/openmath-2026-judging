import json, urllib.request, pathlib, hashlib
from pypdf import PdfReader
root=pathlib.Path(__file__).parent
dest=root/'OpenMath-morning-artifacts'; dest.mkdir(exist_ok=True)
rows=json.loads((root/'OpenMath-morning-attachment-extractions.json').read_text(encoding='utf-8'))
index=[]
for row in rows:
 d=row['data']; name=row['request']['filename']; path=dest/name
 try:
  url=d['file_uri']['download_url']
  with urllib.request.urlopen(url,timeout=30) as r: path.write_bytes(r.read())
  if path.suffix=='.pdf':
   text='\n\n'.join(f'PAGE {i+1}\n'+(p.extract_text() or '') for i,p in enumerate(PdfReader(path).pages))
   path.with_suffix('.txt').write_text(text,encoding='utf-8')
  index.append({'filename':name,'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'bytes':path.stat().st_size,'message_id':row['request']['message_id']})
 except Exception as e: index.append({'filename':name,'error':str(e)})
(root/'OpenMath-morning-attachment-index.json').write_text(json.dumps(index,indent=2),encoding='utf-8')
print(json.dumps(index,indent=2))
