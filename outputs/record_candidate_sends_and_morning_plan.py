import json,re,html
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo

ROOT=Path(__file__).resolve().parent
STAMP=datetime.now(ZoneInfo('Europe/Paris')).isoformat(timespec='minutes')
REPORT='OpenMath-33-account-contact-drafts-UNSENT.html'
def read(n):return json.loads((ROOT/n).read_text(encoding='utf-8-sig'))
def write(n,d):(ROOT/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
receipts=read('OpenMath-additional-candidate-SENT-receipts.json')['receipts']
receipt_by={x['id']:x for x in receipts}
admins=read('OpenMath-organizer-unblock-and-exception-SENT.json')
review=read('OpenMath-33-account-contact-drafts-UNSENT.json')
assert len(receipt_by)==18 and all(x['sent'] and x['body_matches'] for x in receipts)
assert len(admins['receipts'])==4 and all(x['sent'] and x['body_matches'] for x in admins['receipts'])
policy=review['policy']

# Keep the approved text, while making its verified send state unambiguous.
drafts=read('OpenMath-additional-candidate-drafts-UNSENT.json')
drafts['updated']=STAMP
drafts['status']='HISTORICAL FILENAME: all eighteen approved messages now SENT/verified; not an unsent queue.'
for d in drafts['drafts']:
    d.update(sent=True,receipt=receipt_by[d['id']],recommendation='SENT/verified; await response, do not resend.')
write('OpenMath-additional-candidate-drafts-UNSENT.json',drafts)
write('OpenMath-additional-candidate-messages-SENT.json',drafts)
sent_text=['OPENMATH — EIGHTEEN CANDIDATE MESSAGES SENT/VERIFIED',STAMP,'All emails checked against exact recipient, body, sender and SENT label; recipient reads not claimed.']
for d in drafts['drafts']:
    sent_text += ['',d['id']+' — '+d['name'],'To: '+d['contact']['email'],'Receipt: '+receipt_by[d['id']]['message_id']]+d['lines']
(ROOT/'OpenMath-additional-candidate-messages-SENT.txt').write_text('\n'.join(sent_text)+'\n',encoding='utf-8')
old_text=ROOT/'OpenMath-additional-candidate-drafts-UNSENT.txt'
text=old_text.read_text(encoding='utf-8-sig')
if not text.startswith('SUPERSEDED — SENT'):
    old_text.write_text('SUPERSEDED — SENT/VERIFIED '+STAMP+'\nAll eighteen messages below were authorized and sent. This historical filename is NOT an unsent queue. See OpenMath-additional-candidate-SENT-receipts.json.\n\n'+text,encoding='utf-8')

inventory=read('OpenMath-complete-team-inventory.json')
inventory['updated']=STAMP
for entry in inventory['entries']:
    if entry['id'] in receipt_by:
        entry.update(sent=True,receipt=receipt_by[entry['id']],recommendation='SENT/verified; await reply, do not resend.')
    if entry['id']=='E06':
        entry['team_size_exception']=policy
        entry['status']+=' Five-person exception approved by user and communicated; adjusted overall score = 0.8 × raw overall score. Final named authorship still to confirm.'
    if entry['id']=='E10':
        entry['status']='Frozen judging packet requested through reply-by-email before cutoff. Five AutoLab jobs already queued; zero-dollar LLM-cap blocker documented. Zero-LLM-cost evaluation requested from Serge; no spend authorized. Official receipt/evaluation and final packet still pending.'
        entry['workflow_receipts']=[x for x in admins['receipts'] if x['key'].startswith('Jamie')]
    if entry['id']=='E05':
        entry['status']+=' New 00:18 CEST reply confirms current packet 9bc116919c27e63db193e03ae6b567a9f2a09579; preserved submission 57c1ad7f2af78339260fcc4d8498a05dda4cfc77, final=false. Waiting for Serge’s final-evaluation workflow confirmation; BB6 is separate.'
inventory['current_account_review']=REPORT
inventory['morning_collection']=review['morning_collection']
write('OpenMath-complete-team-inventory.json',inventory)

status=read('OpenMath-team-status.json')
status.update(reviewed=STAMP,outreach_updated=STAMP,next_review_file=REPORT)
status['outreach_summary'].update(additional_registered_messages_sent=18,additional_registered_drafts_unsent=0,admin_messages_sent_this_turn=4,new_account_drafts_unsent=33)
status['team_size_exceptions']=[policy]
for team in status['teams']:
    if team['name'].startswith('Luca'):
        team['missing']='Team-size eligibility resolved by user: five contributors allowed with 0.8 × otherwise overall score. Confirm all five names/roles and complete credits, frozen revision and official receipt; independent rebuild and source-statement fidelity review still needed. Do not require a team split or reopen the size exception.'
        team['team_size_exception']=policy
    if team['name']=='Chaewon Yoon':
        team['materials']+=' New reply received: current review packet commit 9bc116919c27e63db193e03ae6b567a9f2a09579; preserved submission commit 57c1ad7f2af78339260fcc4d8498a05dda4cfc77.'
        team['missing']='No final receipt; preserved signed report passed=true, official=true, final=false. Author is ready but has not run --final pending workflow confirmation, now requested from Serge. BB6 explicitly separate. Independent certificate/formal review remains.'
for row in status['additional_projects']:
    if row[0].startswith('Jamie'):
        row[2]='Fresh canonical campaign source: five registered AutoLab jobs queued, zero official submissions, strict zero-dollar LLM cap blocks launch. Reply-by-email frozen judging intake offered before cutoff. Serge/Artem asked for official receipt and evaluation of fixed artifacts without an agent/LLM stage. Packet delivery and official recognition still pending; no spending authorized. Prior-work/conditional claims need careful separation.'
    if row[0].startswith('Shafeeq'):
        row[2]+=' AutoLab directly links SHAFF622 GitHub, name/project match established; E15 already sent. Exact final packet and roster remain pending.'
status['organizer_actions']=[
 'Confirm timestamped frozen-packet intake/official receipt and zero-LLM-cost evaluation for Jamie’s five queued jobs; preserve original deadline and do not duplicate jobs.',
 'Answer Chaewon’s --final versus organizer-side final evaluation question and separate Busy Beaver entry; confirm official submission/export workflow for all teams.',
 'Record user-approved Leanification five-person exception: adjusted overall score = 0.8 × raw overall score; confirm named credits, not team splitting.',
 'Six pending registrations were approved/Going previously; mathematical eligibility and acceptance remain separate.',
 'Resolve Woohyuk’s target/admission questions and recording request. Assign independent reviewers and retain received frozen artifacts.',
 'After user review only, send remaining account drafts or organizer relay; 18 additional candidate messages already sent. Collect all results/formalizations at 06:21 CEST October 3.'
]
status['suggested_review_order']=[x.replace('Chandragupt rank23/support138 after repo invite','Chandragupt accessible rank23/support138 packet: independent checks and novelty review') for x in status['suggested_review_order']]
status['coverage'].insert(0,STAMP+': E16–E33 sent and exact-recipient/body/SENT verified; four workflow/exception messages likewise verified. All 33 public GitHub contact profiles and selected owner-linked sites read; readiness drafts and relay remain unsent. Fresh Jamie canonical source exposes strict zero-dollar LLM cap; no spend or contestant-code execution. Morning collection scheduled once for October 3 06:21 Europe/Paris.')
write('OpenMath-team-status.json',status)

ob=read('obligations-current-data.json')
ob.update(reviewed=STAMP,drafting_updated=STAMP,next_openmath_review_file=REPORT)
decision=f'{STAMP}: E16–E33 candidate messages SENT/verified. User approved five-person Leanification with 0.8 overall-score multiplier; exception communicated to team and organizers. Jamie email intake offered and zero-LLM-cost evaluation requested; official receipt/packet still pending. All 33 account readiness drafts and organizer relay remain UNSENT for user review. Single morning collection scheduled October 3 06:21 CEST.'
ob['latest_user_decisions'].append(decision)
ob['latest_user_decisions']=[x.replace('Await private invitation; do not invent Stephen GitHub username.','Invitation accepted and packet accessible; final receipt/independent review pending. Do not invent Stephen GitHub username.') for x in ob['latest_user_decisions']]
ob['openmath_outreach']=status['outreach_summary']
ob['follow_up_drafts']={'file':str(ROOT/'OpenMath-33-account-contact-drafts-UNSENT.json'),'status':'33 account drafts and organizer relay UNSENT for review; E16–E33 already SENT/verified','sent_candidate_receipts':str(ROOT/'OpenMath-additional-candidate-SENT-receipts.json'),'not_unique_team_count':True}
ob['leanification_exception']=policy
ob['morning_collection']=review['morning_collection']
ob['ordered'][0]=['1','Immediate / before cutoff','Review all 33 account drafts and organizer relay','Eighteen additional candidate emails are SENT/verified. Eleven new accounts have direct email/LinkedIn routes; sixteen need organizer relay; four overlaps already covered; two organizers need classification rather than contestant reminders. Preserve every potentially useful partial result/formalization.',REPORT]
ob['ordered'][1]=['2','Before cutoff / on organizer reply','Finish submission-route confirmation','Jamie has a working email intake offer, but his packet/official receipt and five queued jobs remain pending. Serge/Artem asked for zero-LLM-cost artifact evaluation and Chaewon final workflow. Leanification size exception is decided; only names/roles/credits remain to confirm.','OpenMath-organizer-unblock-and-exception-SENT.json']
ob['ordered'].insert(2,['3','Scheduled October 3 06:21 CEST','Collect all final OpenMath material','Single collection run will retrieve all team/hill/claim/formalization artifacts, freeze identifiers/receipts, deduplicate aliases and produce the judging queue; no automatic new messages.','OpenMath-morning-collection-plan.txt'])
for n,row in enumerate(ob['ordered'],1):row[0]=str(n)
for w in ob['waiting']:
    if w[0]=='W9':w[2]='Official intake/zero-cost final evaluation, frozen records and judging assignments';w[3]='Jamie fallback email offered; canonical record shows five queued jobs blocked by zero-dollar LLM cap. Chaewon explicitly awaits --final workflow confirmation. Requests sent to Serge/Artem; packet/official receipts not yet confirmed.';w[4]='Before cutoff / morning collection; no extra account sends before user review.'
    if w[0]=='W22':w[2]='Final five-person Leanification names/roles/credits';w[3]='Five-person exception DONE by user, communicated to Luca/Ueverton and Serge/Artem. Adjusted overall score = 0.8 × raw overall score; all five retain credits.';w[4]='Confirm authorship before scoring; do not require splitting.';w[5]='Size eligibility resolved; attribution pending'
for entry in ob['entrants']:
    if entry[0].startswith('Luca'):
        entry[3]='Five-person exception approved and communicated; adjusted overall score = 0.8 × raw overall score. '+next(t['result']+' Remaining: '+t['missing'] for t in status['teams'] if t['name'].startswith('Luca'))
    if entry[0]=='Chaewon Yoon':
        entry[3]+=' New author reply and final-workflow dependency: see OpenMath-team-status.json.'
ob['closed'].append('Eighteen additional registered-candidate emails SENT/verified '+STAMP+'. Leanification five-contributor exception decided and communicated, with 0.8 × raw overall score. Four workflow/exception emails SENT/verified; Jamie actual final intake/evaluation still pending.')
write('obligations-current-data.json',ob)

plan='''OPENMATH — MORNING COLLECTION PLAN
Scheduled once: October 3, 2026, 06:21 Europe/Paris (CEST).
Automation: openmath-morning-submission-collection. Existing COUNT=1 schedule verified in the saved automation.

Read Desktop to do and current structured records first. No new messages are authorized by this scheduled collection; use later human approval if provided.
Retrieve final replies/packets from all known 15 groups, 18 registered candidates, six interested contacts, all seven hills and all 33 additional accounts. Keep baseline-level scores in the inventory because novel methods/formalizations may still matter.
Create a deduplicated team register and per-hill/per-claim artifact index: names/aliases, contributions, entrant class, claim/modality, immutable commit/hash, event-window delta/provenance, receipt timestamp/channel/status, accessible repository, papers/editable sources, novelty/limitations, Lean version/declarations/axioms/build logs, exact certificates/checkers, reproduction commands/data/dependencies, resource/AI disclosures, scores and missing items.
Keep server receipts, judge email intake, self-reported submitted flags, evaluation reports and mathematical acceptance distinct. Freeze submitted revisions; record later documentation/reproduction separately from new score-bearing claims.
Leanification: five contributors allowed by user. Record raw overall score and adjusted overall score = 0.8 × raw overall score; do not apply a per-member score adjustment or invent a score before judging. Confirm all five names/credits.
Jamie: email fallback offered, no actual new packet/official acknowledgement yet. Five native jobs already registered/queued; strict zero-dollar LLM cap is a separate blocker. Serge asked for evaluation of fixed artifacts without agent/LLM spend. Do not duplicate jobs, authorize spending or execute untrusted contestant code.
Chaewon: new reply confirms review commit 9bc116919c27e63db193e03ae6b567a9f2a09579 and submission commit 57c1ad7f2af78339260fcc4d8498a05dda4cfc77; final=false. Author awaits final workflow. Busy Beaver separate.
Chandragupt: private packet accessible; verify frozen revision, exact all-729 identity/certificate coverage, formalization claims and novelty/equivalence later. Do not reopen the completed invitation task.
Output complete inventory/report plus a review queue showing ready packets, independent-review needs and missing/blocking materials. Include unsuccessful/partial work without inflating it into solved conjectures. State any inaccessible sources instead of claiming complete retrieval. Update Desktop and structured records, then report meaningful findings to Alejandro.
'''
(ROOT/'OpenMath-morning-collection-plan.txt').write_text(plan,encoding='utf-8')

desktop=Path('[LOCAL PRIVATE OBLIGATIONS RECORD]')
text=desktop.read_text(encoding='utf-8-sig')
(ROOT/'to-do-before-eighteen-candidate-sends.txt').write_text(text,encoding='utf-8')
text=re.sub(r'Last updated: .*',f'Last updated: {STAMP} (Europe/Paris)',text,count=1)
text=text.replace('LATEST USER DECISIONS\n','LATEST USER DECISIONS\n- '+decision+'\n',1)
text=text.replace('- OpenMath: the specifically authorized fifteen group follow-ups and six interest enquiries are complete. User will review the eighteen new-candidate drafts and additional-account recommendations before any further sends.','- OpenMath: fifteen group follow-ups, six interest enquiries and eighteen additional-candidate emails are SENT/verified. All new 33-account drafts and organizer relay remain UNSENT pending review. Leanification five-person exception is decided: adjusted overall score = 0.8 × raw overall score.')
start=text.index('RECOMMENDED ORDER\n')
end=text.index('DONE / CLOSED\n')
ordered='RECOMMENDED ORDER\n'
for row in ob['ordered']:
    ordered+=f'{row[0]}. [{row[1]}] {row[2]}\n   {row[3]}\n   Evidence: {row[4]}\n\n'
text=text[:start]+ordered+'\n'+text[end:]
text=text.replace('DONE / CLOSED\n','DONE / CLOSED\n- Eighteen additional registered-candidate emails: SENT/verified '+STAMP+'.\n- Leanification five-person exception: DONE by user and communicated. Raw score still to judge; adjusted overall score = 0.8 × raw overall score.\n',1)
text=re.sub(r'^- W9 \|.*$', '- '+' | '.join(next(w for w in ob['waiting'] if w[0]=='W9')),text,flags=re.M)
text=re.sub(r'^- W22 \|.*$', '- '+' | '.join(next(w for w in ob['waiting'] if w[0]=='W22')),text,flags=re.M)
text+='\nDATED HISTORY — '+STAMP+' — EIGHTEEN SENDS, EXCEPTION AND MORNING COLLECTION\n'+decision+'\nRead back all 18 candidate messages and four workflow/exception messages against sender/recipient/body/SENT. Jamie’s canonical campaign source identifies the zero-dollar LLM-cap launch blocker as well as the missing intake route; no spending occurred. Newly published contact routes found for Anthony, Haroon, Felix, Octavian, Luiz, Claudio and Kaita; Wilson profile is an alias-confirmation route. Sixteen accounts still need organizer relay; do not invent emails or treat unrelated public repositories as a generic direct-message channel.\nSources: '+str(ROOT/'OpenMath-additional-candidate-SENT-receipts.json')+'; '+str(ROOT/'OpenMath-organizer-unblock-and-exception-SENT.json')+'\nReview: '+str(ROOT/REPORT)+'\nCollection plan: '+str(ROOT/'OpenMath-morning-collection-plan.txt')+'\n'
desktop.write_text(text,encoding='utf-8')

# Prominent notices prevent historical reports being mistaken for a fresh send queue.
banner='<aside style="padding:20px;background:#fff0c7;border:2px solid #b77912;font:18px system-ui"><strong>UPDATED '+html.escape(STAMP)+': E16–E33 are now SENT/verified.</strong> Review the <a href="'+REPORT+'">33 remaining account drafts/contact routes</a>. Leanification five-person exception: overall score × 0.8. Morning collection scheduled once at 06:21 CEST October 3. No new account drafts have been sent.</aside>'
for filename in ['OpenMath-next-messages-and-account-audit.html','OpenMath-complete-team-inventory.html','OpenMath-team-status.html','obligations-current.html']:
    p=ROOT/filename
    if p.exists():
        content=p.read_text(encoding='utf-8-sig')
        content=re.sub(r'(<body[^>]*>)',lambda m:m.group(1)+banner,content,count=1) if re.search(r'<body[^>]*>',content) else banner+content
        p.write_text(content,encoding='utf-8')
print(json.dumps({'timestamp':STAMP,'eighteen_sent_verified':True,'four_admin_sent_verified':True,'new_account_drafts_sent':False,'leanification_multiplier':policy['overall_score_multiplier'],'desktop_updated':True,'morning_collection':'2026-10-03 06:21 CEST'},ensure_ascii=False))
