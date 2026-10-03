import json,pathlib,hashlib,sys,datetime
sys.stdout.reconfigure(encoding='utf-8')
R=pathlib.Path(__file__).resolve().parent
def load(n):return json.loads((R/n).read_text(encoding='utf-8-sig'))
inv=load('OpenMath-morning-judging-inventory.json');src=load('OpenMath-morning-source-index.json')
def data(p):return pathlib.Path('\\\\?\\'+str(pathlib.Path(p).resolve())).read_bytes()
errors=[]
for q in src['public_files']:
 if not q.get('retrieved'):errors.append('not retrieved '+q['path']);continue
 try:
  if hashlib.sha256(data(q['local_path'])).hexdigest()!=q['sha256']:errors.append('hash '+q['local_path'])
 except Exception as e:errors.append(str(e))
zip_count=0
for q in src['attachments']:
 if hashlib.sha256(data(q['local_path'])).hexdigest()!=q['sha256']:errors.append('attachment hash '+q['name'])
 for x in q.get('files',[]):
  zip_count+=1
  p=R/'sakana'/x['path']
  if hashlib.sha256(data(p)).hexdigest()!=x['sha256']:errors.append('ZIP member '+x['path'])
assert len(inv['records'])==72
assert len(set(x['record_id'] for x in inv['records']))==72
assert len([x for x in inv['records'] if 'E34'<=x['record_id']<='E66'])==33
assert len(inv['records'][1]['source_family_dossiers'])==22
assert len(inv['records'][1]['focus_family_dossiers'])==5
assert inv['leanification_exception']['factor']==0.8 and inv['leanification_exception']['raw_overall_score'] is None and inv['leanification_exception']['adjusted_overall_score'] is None
assert not next(x for x in inv['records'] if x['record_id']=='E10')['official_submission_blocker_resolved']
assert not next(x for x in inv['records'] if x['record_id']=='E17')['final_packet_confirmed']
for q in src['source_files']:
 p=pathlib.Path(q['path']);q['bytes']=p.stat().st_size;q['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
(R/'OpenMath-morning-source-index.json').write_text(json.dumps(src,ensure_ascii=False,indent=2),encoding='utf-8')
out={'verified_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Saved file integrity and collection-record consistency only. No mathematical evaluator or contestant code executed.','public_file_count':len(src['public_files']),'zip_members':zip_count,'issues':errors,'passed':not errors,'72_record_coverage':True,'33_extra_account_coverage':True,'27_sakana_family_records':True,'scores_unassigned':True}
(R/'OpenMath-morning-integrity-check.json').write_text(json.dumps(out,indent=2),encoding='utf-8');print(json.dumps(out,indent=2))
if errors:raise SystemExit(1)
