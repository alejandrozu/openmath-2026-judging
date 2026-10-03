import pathlib,sys,re,json,ast
sys.stdout.reconfigure(encoding='utf-8');root=pathlib.Path('OpenMath-Judging');sys.path.insert(0,str(root));from library_core import connect,read_bytes
c=connect(root)
for r in c.execute("select * from files where team_id='E04' and category!='12-correspondence'"):
 print(r['id'],r['original_path'],r['bytes'])
 if r['bytes']<300000 and r['category']!='13-archives':
  t=read_bytes(root,r).decode('utf-8',errors='replace')
  for name in ['u','v','w']:
   m=re.search(r'def '+name+r'\b[^\n]*:=\s*(\[)',t)
   if m:
    start=m.start(1);level=0;end=None
    for i in range(start,len(t)):
     if t[i]=='[':level+=1
     elif t[i]==']':
      level-=1
      if level==0:end=i+1;break
    if end:
     try:
      a=ast.literal_eval(t[start:end]);print('PARSED',name,len(a),[len(x) for x in a][:3]);(root/'judging'/('chandra-'+str(r['id'])+'-'+name+'.json')).write_text(json.dumps(a),encoding='utf-8')
     except Exception as e:print('PARSE ERROR',e)
    else:print('TRUNCATED',name)
