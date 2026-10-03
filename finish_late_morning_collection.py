import pathlib,json,hashlib,zipfile,datetime,sys,re,collections,concurrent.futures
sys.stdout.reconfigure(encoding='utf-8')
R=pathlib.Path(__file__).resolve().parent/'outputs';NOW=datetime.datetime.now(datetime.timezone.utc).astimezone(datetime.timezone(datetime.timedelta(hours=2))).isoformat(timespec='seconds')
def load(n):return json.loads((R/n).read_text(encoding='utf-8-sig'))
def save(n,d):(R/n).write_text(json.dumps(d,ensure_ascii=False,indent=2),encoding='utf-8')
d=load('OpenMath-team-directory-current.json');root=R/'OpenMath-by-team';root.mkdir(exist_ok=True)
groups=d['groups']; allids=[id for g in groups for id in g['source_record_ids']]
assert len(allids)==len(set(allids))==73
assert all(f'E{i:02d}' in allids for i in range(1,73))
assert len([g for g in groups if g['is_potential_entrant_unit']])==59
assert len([g for g in groups if g['has_review_material_or_manifests']])==13
for g in groups:
 folder=root/g['group_id'];folder.mkdir(exist_ok=True)
 (folder/'review-packet.json').write_text(json.dumps(g,ensure_ascii=False,indent=2),encoding='utf-8')
 lines=[g['group_id']+' — '+g['name'],g['classification'],g['status'],'Source records: '+', '.join(g['source_record_ids']),'Accounts: '+', '.join(g['accounts']),'','RESULTS / SCOPE',*g['claims'],'','MISSING / DECISIONS',*g['gaps'],'','Immutable revision: '+str(g['immutable_commit']),'','Original archived collections:']
 lines.extend(a['archive_path']+' | SHA256 '+a['archive_sha256'] for a in g['archived_collections'])
 lines.extend(['','All source routes, saved file paths, receipts, exact hill metrics, and earlier proof dossiers are in review-packet.json. No contestant code executed.'])
 (folder/'READ-ME.txt').write_text('\n'.join(lines),encoding='utf-8')
 # Sakana's large family selection is one team, not 27 teams. Retain per-family dossiers in that team's folder.
 if g['group_id']=='E02':
  for src in [R/'sakana/Math_Competition_Completed_Results_Submission/Claim_Evidence/CLAIMS.json',R/'sakana/Math_Competition_Completed_Results_Submission/Focus_Evidence/focus-candidates.json']:
   (folder/src.name).write_bytes(src.read_bytes())
table=['OPENMATH — team folders','Updated: '+NOW,'59 potential entrant/contact units, not official team count. All original72 plus Terry contact preserved.','18 identified work groups/leads;13groups have review material/manifests.','',*[(g['group_id']+' | '+g['name']+' | '+g['classification']+' | '+g['status']) for g in groups]]
(root/'INDEX.txt').write_text('\n'.join(table),encoding='utf-8')
def verify_archive(a):
 p=pathlib.Path(a['archive_path']);sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==a['archive_sha256']
 with zipfile.ZipFile(p) as z:
  count=sum(not i.is_dir() for i in z.infolist());assert count==a['file_count'];bad=z.testzip();assert bad is None,bad
 return {'record_id':a['record_id'],'sha256':sha,'all_member_crc_verified':True,'file_count':count}
archives=load('OpenMath-late-morning-archive-index.json')
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:checks=list(pool.map(verify_archive,archives))
# Remove irrelevant group-member phone directory from readback; preserve actual scheduling message text.
ui=load('OpenMath-late-morning-ui-source.json')
for row in ui:
 if row['source']=='Full current jury instructions':
  text=row['text'];offset=text.find('Hi everyone,')
  if offset>=0:row['text']=text[offset:];row['redaction_note']='Irrelevant chat-list/group-phone-directory prefix omitted.'
save('OpenMath-late-morning-ui-source.json',ui)
luma=next(x for x in ui if x['source']=='Fresh Luma registration table')['text']
counts={'Going':len(re.findall(r'^Going$',luma,re.M)),'Not Going':len(re.findall(r'^Not Going$',luma,re.M))}
assert counts=={'Going':30,'Not Going':1},counts
verify={'verified_at':NOW,'original72_preserved_once':True,'all33_extra_accounts_preserved':True,'new_interest_record':'E73','group_folders':len(groups),'potential_entrant_units':59,'actual_official_team_count':None,'review_material_groups':13,'fresh_luma_status_counts':counts,'archive_integrity':checks,'total_archive_files':sum(a['file_count'] for a in archives),'selected_files_extracted':sum(a['extracted_count'] for a in archives),'code_executed':False,'messages_sent':False}
save('OpenMath-late-morning-verification.json',verify)
index=load('OpenMath-late-morning-source-index.json');paths={x['path'] for x in index['source_files']}
paths.add(str(R/'OpenMath-late-morning-verification.json'));paths.add(str(root/'INDEX.txt'))
for g in groups:paths.add(str(root/g['group_id']/'review-packet.json'));paths.add(str(root/g['group_id']/'READ-ME.txt'))
index['source_files']=[{'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(map(pathlib.Path,paths))]
index['verified_at']=NOW;index['team_folder_root']=str(root);index['integrity']=verify
save('OpenMath-late-morning-source-index.json',index)
print(json.dumps(verify,ensure_ascii=False,indent=2))
