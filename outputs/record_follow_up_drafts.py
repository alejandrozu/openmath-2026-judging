from pathlib import Path
import json, re
from datetime import datetime
from zoneinfo import ZoneInfo

root = Path(__file__).resolve().parent
draft_path = root / 'OpenMath-follow-up-drafts-UNSENT.json'
drafts = json.loads(draft_path.read_text(encoding='utf-8'))
stamp = datetime.now(ZoneInfo('Europe/Paris')).isoformat(timespec='minutes')
drafts['preparedAt'] = stamp
draft_path.write_text(json.dumps(drafts, ensure_ascii=False, indent=2), encoding='utf-8')
lines = ['OPENMATH FOLLOW-UP DRAFTS — UNSENT', 'Prepared: '+stamp,
         'Basis: last audit October 2 23:19 CEST; no fresh inbox/repository review in this drafting turn.',
         'Official cutoff: October 2 23:59 EDT / October 3 05:59 CEST.',
         'One three-line draft per contacted team. Chandragupt: wait, conditional access reminder only. No messages sent.']
for entry in drafts['messages']:
    assert len(entry['lines']) <= 3
    lines += ['',entry['recipient'], 'Recommendation: '+entry['recommendation'], *entry['lines'], 'Rationale: '+entry['rationale']]
(root/'OpenMath-follow-up-drafts-UNSENT.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8-sig')
todo = Path('[LOCAL PRIVATE OBLIGATIONS RECORD]')
text = todo.read_text(encoding='utf-8-sig')
text = re.sub(r'^Last updated:.*$', 'Last updated: '+stamp+' (Europe/Paris)', text, count=1, flags=re.M)
text = text.replace('LATEST USER DECISIONS\n', 'LATEST USER DECISIONS\n- '+stamp+': User requested drafts of at most three lines per team, with rationale and special attention to unfinished entries. Ten drafts prepared for review; no sends authorized or performed on this turn. Chandragupt should wait because access reply was just sent.\n',1)
text = text.replace('1. [Tonight / next immediate decision] Review OpenMath status and choose missing-packet follow-ups', '1. [Tonight / next immediate decision] Review the short follow-up drafts and select sends')
text += '\nDATED HISTORY — '+stamp+'\nUser requested a message and rationale for each of the ten contacted teams, maximum three lines per draft. Prepared focused missing-packet reminders for Luke/Madhan, Sakana, Matt, Chris and Woohyuk; acknowledgement/final-status checks for Luca and Chaewon; final-version/claim clarification for Raj; roster clarification for Mateus. Chandragupt draft is conditional: wait for his response/invitation and recheck access before using it. No inbox or repository refresh occurred in this drafting turn; basis is the 23:19 audit. No message, submission or organizer decision was sent. Other task statuses preserved.\nDrafts: '+str(root/'OpenMath-follow-up-drafts-UNSENT.txt')+'\nStructured drafts: '+str(draft_path)+'\n'
todo.write_text(text,encoding='utf-8-sig')
data_path = root/'obligations-current-data.json'
data=json.loads(data_path.read_text(encoding='utf-8'))
data['drafting_updated'] = stamp
data['follow_up_drafts'] = {'file':str(draft_path),'status':'UNSENT — user review only','count':10,'no_new_status_audit':True,'chandragupt':'Wait; recent access reply already sent. Recheck invitation before using conditional reminder.'}
data['latest_user_decisions'].append(stamp+': Three-line team follow-up drafts and rationales prepared; user selects sends. No external messages sent.')
data['ordered'][0][2] = 'Review short OpenMath follow-up drafts and select sends'
data['ordered'][0][3] = 'Ten drafts prepared from the 23:19 audit: missing-material reminders, acknowledgement/final-status checks and roster clarification. Chandragupt: wait, as access reply was just sent. All drafts UNSENT; user review pending. Official cutoff unchanged.'
data['ordered'][0][4] = 'OpenMath-follow-up-drafts-UNSENT.txt'
data_path.write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({'drafts':len(drafts['messages']),'max_lines':max(len(x['lines']) for x in drafts['messages']),'sent':0,'desktop_updated':str(todo),'timestamp':stamp}))
