import json,pathlib,sys
sys.stdout.reconfigure(encoding='utf-8');p=pathlib.Path('OpenMath-Judging/judging')
r=json.loads((p/'Ulam_UnsolvedMath_ChatGPT_5.6_Sol_Ultra_Rationales_v1.0.json').read_text(encoding='utf-8'))
print('SCORING META',json.dumps({k:v for k,v in r.items() if k!='records'},ensure_ascii=False)[:18000]);print('FIRST RATIONALE',json.dumps(r['records'][0],ensure_ascii=False)[:7000])
d=json.loads((p/'preliminary-assessment.json').read_text(encoding='utf-8'))
print('TEAM KEYS',d['teams'][0]); print('SAKANA ROWS')
for x in d['results']:
 if x['team_id']=='E02':
  print(x['id'],x['family_id'],x['modality_proposal'],x['p_scope_if_claim_valid'],'\nCLAIM',x['exact_claim'],'\nSCOPE',x['progress_rationale'])
