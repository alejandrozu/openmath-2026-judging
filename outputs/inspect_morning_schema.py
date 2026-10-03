import json,pathlib,sys
sys.stdout.reconfigure(encoding='utf-8')
r=pathlib.Path(__file__).parent
for name in ['OpenMath-judging-fetch-map.json','OpenMath-complete-team-inventory.json','OpenMath-additional-hill-account-assessment.json','OpenMath-morning-email-source.json','OpenMath-morning-attachment-index.json','obligations-current-data.json']:
 d=json.loads((r/name).read_text(encoding='utf-8-sig'));print(name, list(d.keys()) if isinstance(d,dict) else f'list {len(d)}')
 if isinstance(d,list):print('item keys',list(d[0].keys()))
for name,key in [('Claim_Evidence/CLAIMS.json','claims'),('Focus_Evidence/focus-candidates.json','candidates')]:
 d=json.loads((r/'sakana/Math_Competition_Completed_Results_Submission'/name).read_text(encoding='utf-8'));print(name,[(x.get('claim_id',x.get('id')),x.get('title'),x.get('classification',{}).get('proposed_modality')) for x in d[key]])
f=json.loads((r/'OpenMath-judging-fetch-map.json').read_text(encoding='utf-8'));print('records',[(x['record_id'],x['name']) for x in f['records']])
