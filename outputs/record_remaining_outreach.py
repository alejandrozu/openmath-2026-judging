import json,re,html
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo

ROOT=Path(__file__).resolve().parent
STAMP=datetime.now(ZoneInfo('Europe/Paris')).isoformat(timespec='minutes')
def read(n): return json.loads((ROOT/n).read_text(encoding='utf-8-sig'))
def write(n,d): (ROOT/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
sent=read('OpenMath-remaining-outreach-SENT-receipts.json')
direct={x['account']:x for x in sent['direct_receipts']}
relay=sent['organizer_relay']; relay_accounts=set(relay['accounts'])
raj=read('OpenMath-Raj-identifier-clarification-SENT.json')
review=read('OpenMath-33-account-contact-drafts-UNSENT.json')
covered=set(sent['covered_existing_accounts'])
for a in review['accounts']:
    h=a['account']
    if h in direct:
        a.update(sent=True,new_draft_sent=True,receipt=direct[h],outreach_status='SENT directly / exact recipient and body verified; awaiting reply',recommendation='Await reply and retrieve frozen final packet after cutoff; do not send again.')
    elif h in relay_accounts:
        a.update(sent=False,new_draft_sent=False,relay_requested=True,relay_receipt=relay['message_id'],outreach_status='Individual draft SENT to organizers for forwarding; forwarding to account NOT yet confirmed',recommendation='Retrieve organizer forwarding confirmation and account-to-team/artifact map. Do not mark contestant as directly reached.')
    elif h in ['ottogin','sergeicu']:
        a.update(sent=True,new_draft_sent=True,receipt=relay,outreach_status='Organizer/reference classification enquiry SENT in joint organizer message',recommendation='Await classification and official artifact register; avoid counting organizer reference runs as new teams.')
    elif h in covered:
        a['outreach_status']='Already covered by verified E04/E15/E19/E23 outreach; new duplicate not sent.'
        a['recommendation']='Retrieve from existing conversation; preserve team/alias uncertainty until confirmed.'
review.update(updated=STAMP,status='Current: seven direct emails SENT/verified; twenty individual enquiries SENT to organizers for relay, forwarding pending; two organizer classifications SENT; four overlapping accounts already covered. Historical UNSENT filename retained for continuity.',current_report='OpenMath-outreach-readiness-current.html')
review['organizer_relay_draft'].update(sent=True,receipt=relay,accounts_needing_relay=relay['accounts'],forwarding_confirmed=False)
write('OpenMath-33-account-contact-drafts-UNSENT.json',review)
write('OpenMath-additional-hill-account-assessment.json',{'updated':STAMP,'scope':'All 33 accounts; scored run versus final review packet and direct contact versus requested forwarding are distinct.','accounts':review['accounts'],'latest_review':'OpenMath-outreach-readiness-current.html'})

inventory=read('OpenMath-complete-team-inventory.json')
teams=read('OpenMath-team-status.json')
raj_status='New October 3 00:30 CEST author reply claims K(18)<=94 for lines/pseudolines with arbitrary multiplicity; K(18)=93 without fourfold intersections; remaining all-8 case open. Reports new 93 construction and rational LP/DP plus SAT/DRAT proofs, no Lean files. Final paper/certificates/repository commit promised tonight; claims NOT independently adjudicated.'
for t in teams['teams']:
    if 'Raj Harshit' in t['name']:
        t.update(materials=raj_status,missing='Await frozen final commit, PDF/LaTeX, LP/DRAT certificates, independent checker, commands and final receipt. Human mathematical review remains. Identifier question answered via verified LinkedIn send.')
        t['sources']+=['OpenMath-Raj-predeadline-update.txt','OpenMath-Raj-identifier-clarification-SENT.json']
    if 'Mateus Mundstock' in t['name']:
        t.update(materials='Same five-person Leanification group according to Luca; user exception approved and communicated. Do not treat roster as a separate entrant without evidence.',missing='Confirm named five-person credits/contributions, frozen revision and official receipt; no split or new team-size approval needed.')
    if 'Luca Seiki' in t['name']: t['materials']+=' Five-person exception communicated; adjusted overall score = 0.8 × raw overall score.'
teams['reviewed']=STAMP
teams['coverage'].insert(0,STAMP+': Seven remaining direct emails SENT/verified. Twenty per-account readiness drafts and two organizer/reference classification enquiries SENT to Serge/Artem; forwarding still unconfirmed. Four LinkedIn routes actually require Premium. Raj fresh reply captured and submission-reference question answered. Complete retrieval map prepared for all 72 contact/account records and seven hills; final missing material explicitly pending.')
teams['current_retrieval_map']='OpenMath-judging-fetch-map.json'
write('OpenMath-team-status.json',teams)

byhandle={a['account']:a for a in review['accounts']}
for x in inventory['entries']:
    if x['name'] in byhandle:
        a=byhandle[x['name']]
        x.update(outreach_status=a['outreach_status'],sent=a['sent'],new_draft_sent=a['new_draft_sent'],retrieval_sources=list(dict.fromkeys(a['sources']+[a['contact']['autolab'],a['contact']['github']])))
        if a.get('receipt'): x['receipt']=a['receipt']
        if a.get('relay_receipt'): x['relay_receipt']=a['relay_receipt']
    if x['id']=='E06': x['status']='Repository delivered. Five contributors allowed, exception communicated, adjusted overall score = 0.8 × raw overall score. Confirm exact names/credits, final revision and official receipt; independent proof review pending.'
    if x['id']=='E09': x.update(status=raj_status,latest_clarification_receipt=raj)
    if x['id']=='E71': x['status']='October 3 00:14 CEST visible LinkedIn reply: has not done it yet, will take a look. No finished packet established; retrieve later reply without treating interest as an entry.'
inventory.update(updated=STAMP,current_account_review='OpenMath-outreach-readiness-current.html',current_retrieval_map='OpenMath-judging-fetch-map.json')
inventory['outreach_summary']['remaining_account_outreach']={'direct_verified':7,'organizer_relay_accounts':20,'forwarding_confirmed':False,'classification_accounts':2,'previously_covered_accounts':4,'receipts':'OpenMath-remaining-outreach-SENT-receipts.json','raj_clarification':'OpenMath-Raj-identifier-clarification-SENT.json'}
write('OpenMath-complete-team-inventory.json',inventory)

known_repos={
 'E04':['https://github.com/ChandraguptSharma07/matrix-multiplication-tensor-3x3'],
 'E05':['https://github.com/chaewon-research/openmath-2026'],
 'E06':['https://github.com/lazyluca/hyprgraph_containers'],
 'E09':['https://github.com/srirangam-r/kobon_triangles'],
 'E10':['https://github.com/grandchallenge/MATH-PROGRAMME','https://raw.githubusercontent.com/grandchallenge/MATH-PROGRAMME/main/governance/openmath_2026_campaign_state.json'],
 'E11':['https://github.com/Koerbser/erdos-3-autolab'],
 'E12':['https://github.com/FSvOAI/Heilbronn'],
 'E57':['https://github.com/Rohith18p/rsi-kobon-triangles']}
entries=[]
for x in inventory['entries']:
    sources=list(dict.fromkeys(x.get('retrieval_sources',x.get('sources',[]))+known_repos.get(x['id'],[])))
    rec=x.get('receipt') or {}; reply_route=rec.get('url'); email=rec.get('to')
    if x['id']=='E12': reply_route='https://www.linkedin.com/messaging/'; email=None
    if email: inbox_query='{from:'+email+' to:'+email+'} after:2026/09/15 -in:drafts'
    else: inbox_query=None
    repos=[s for s in sources if s.startswith('https://github.com/') and len(s.split('/'))>=5 and '/issues/' not in s and '/blob/' not in s]
    state='Candidate/contact only; final packet location awaiting reply' if int(x['id'][1:]) in range(16,34) or int(x['id'][1:])>=67 else 'Score/project/reference located; complete final artifact or receipt not established'
    if repos: state='Repository route located; final revision, completeness and receipt require verification'
    if x['id']=='E04': state='Private repository access verified; final revision/receipt and independent checks pending'
    if x['id']=='E05': state='Review packet delivered; official signed report final=false; workflow confirmation pending'
    if x['id']=='E06': state='Packet delivered; five-person exception settled; final named credits/receipt and independent review pending'
    if x['id']=='E07': state='Ramtastic repository located; Bosonic Arrow returned 404, access pending'
    if x['id']=='E10': state='Campaign sources located and judge email intake offered; final packet and zero-spend native scoring/official receipt pending'
    entries.append({'record_id':x['id'],'name':x['name'],'category':x['category'],'status':state,'latest_evidence':x['status'],'result_source_urls':sources,'reply_route':reply_route,'inbox_query':inbox_query,'outreach_status':x.get('outreach_status',x.get('recommendation')),'final_packet_confirmed':x['id'] in ['E04','E05','E06'],'official_final_receipt_confirmed':False,'retrieval_action':'Re-read exact contact conversation for final repository, receipt/report ID and immutable revision; use sources as leads. Preserve pre-cutoff submitted version and later documentation separately. If no final artifact exists, keep a missing-material record rather than inventing a result.'})
leaderboards=read('OpenMath-leaderboards-final-review.json')
hills=[]
for item in leaderboards:
    url=item['url']
    if url not in [h['leaderboard_url'] for h in hills]: hills.append({'leaderboard_url':url,'source_snapshot':'OpenMath-leaderboards-final-review.json','collection':'Read all exposed parameter/validation/held-out tables separately; resolve experiment/report IDs from author receipts and organizer register. Best-run tables alone are not all final submissions.'})
assert len(hills)==7
fetch={'updated':STAMP,'cutoff':'2026-10-03T06:00:00+02:00','last_submission_minute':'2026-10-03T05:59:00+02:00','collection_at':'2026-10-03T06:21:00+02:00','scope':'72 audit contact/account records, NOT 72 distinct teams; 15 work groups, 18 registered candidates, 33 extra accounts including overlaps/reference accounts, six interested contacts. Deduplicate only on evidence.','coverage':'Every known record has a retrieval route or an explicitly identified missing final-packet dependency. Repository/access and official final submission acceptance are different. Organizer relay delivery pending.','hill_sources':hills,'records':entries,'submission_register_request':relay,'checklist':['Freeze received/official pre-cutoff revision and message/receipt timestamp.','Exact claims, hypotheses, theorem provenance and event-window novelty.','PDF and editable paper; motivation/novelty/limitations document.','Lean toolchain and Mathlib version, actual declarations/axioms/build logs, source-statement fidelity.','Exact witnesses, rational certificates, independent checkers and input data.','Reproduction commands/dependencies; reports and experiment IDs; validation versus held-out protocol.','Named authors/contributions, team aliases, AI/compute disclosures; Leanification raw overall score and 0.8 adjusted score.','Record missing or inaccessible artifacts without treating baseline scores as proof or rejecting valuable formalization solely for tied scores.'],'unresolved':['Twenty accounts: organizer forwarding and direct packet delivery pending.','Jamie: final emailed packet, five queued jobs, zero-spend evaluation and official receipt pending.','Chaewon: final=false; organizer final-workflow confirmation pending.','Chris Bosonic Arrow: repository access pending.','Most groups/candidates: frozen final revision and receipt await their response.','Stephen reviewer identity/access to private materials not yet confirmed.'],'retrieval_safety':'Do not execute untrusted contestant code as part of collection. Do not authorize spending, modify submissions or assign mathematical acceptance.'}
write('OpenMath-judging-fetch-map.json',fetch)

e=html.escape
cards=[]
for x in entries:
    links=''.join('<li><a href="'+e(u)+'">'+e(u)+'</a></li>' if u.startswith('https://') else '<li>'+e(u)+'</li>' for u in x['result_source_urls'])
    route=('<a href="'+e(x['reply_route'])+'">Exact reply/conversation route</a>') if x['reply_route'] else 'Organizer relay / linked account route; final direct packet link pending'
    cards.append('<article><h2>'+e(x['record_id']+' — '+x['name'])+'</h2><p><strong>'+e(x['status'])+'</strong></p><p>'+e(x['latest_evidence'])+'</p><p>'+route+'</p>'+('<p>Inbox query: <code>'+e(x['inbox_query'])+'</code></p>' if x['inbox_query'] else '')+'<ul>'+links+'</ul><p>'+e(x['retrieval_action'])+'</p></article>')
intro='Seven direct account emails SENT/verified; twenty individual enquiries SENT to Serge/Artem for forwarding (not yet confirmed); organizer/reference classifications included. Four overlapping accounts already covered. Raj identifier question answered. All exact messages and receipts preserved.'
doc='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>OpenMath current outreach and judging retrieval</title><style>body{font:16px/1.5 system-ui;max-width:1080px;margin:32px auto;padding:0 20px;background:#f6f8fb;color:#192438}article{background:white;border:1px solid #cbd5e1;border-radius:10px;margin:16px 0;padding:18px}h2{font-size:21px}a,code{overflow-wrap:anywhere}.pending{background:#fff2ce;padding:18px}</style><h1>OpenMath outreach and judging retrieval</h1><p>'+e(STAMP)+'</p><p>'+e(intro)+'</p><p>Cutoff: October 3 06:00 CEST. One morning collection: 06:21 CEST. 72 records are contacts/accounts, not distinct teams.</p><div class="pending"><strong>Remaining external dependencies</strong><ul>'+''.join('<li>'+e(t)+'</li>' for t in fetch['unresolved'])+'</ul></div><p>Leanification: five allowed; adjusted overall score = 0.8 × raw overall score.</p><h2>All seven hills</h2><ul>'+''.join('<li><a href="'+e(h['leaderboard_url'])+'">'+e(h['leaderboard_url'])+'</a></li>' for h in hills)+'</ul>'+''.join(cards)+'</html>'
(ROOT/'OpenMath-outreach-readiness-current.html').write_text(doc,encoding='utf-8')
for f in ['OpenMath-33-account-contact-drafts-UNSENT.html','OpenMath-complete-team-inventory.html','OpenMath-team-status.html','OpenMath-next-messages-and-account-audit.html']:
    p=ROOT/f
    if p.exists():
        text=p.read_text(encoding='utf-8')
        banner='<aside style="padding:18px;background:#fff2ce;color:#192438"><strong>Current update '+e(STAMP)+'</strong>: '+e(intro)+' <a href="OpenMath-outreach-readiness-current.html">Open current outreach and result retrieval map</a>.</aside>'
        text=re.sub(r'(<body[^>]*>)',r'\1'+banner,text,count=1,flags=re.I) if re.search(r'<body',text,re.I) else text.replace('<h1>',banner+'<h1>',1)
        p.write_text(text,encoding='utf-8')
p=ROOT/'OpenMath-33-account-contact-drafts-UNSENT.txt'
p.write_text('SUPERSEDED '+STAMP+': '+intro+' Current report: OpenMath-outreach-readiness-current.html\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8')

ob=read('obligations-current-data.json')
ob['reviewed']=STAMP
ob['ordered'][0]=['1','Await external replies / collection scheduled','Retrieve frozen OpenMath packets and prepare judging',intro+' Final packets, forwarding acknowledgements and official workflow confirmations remain external dependencies.','OpenMath-outreach-readiness-current.html']
ob['follow_up_drafts']={'status':'Remaining outreach approved and performed: seven direct emails, twenty organizer-relayed enquiries, two organizer classifications. Four overlaps already covered. No additional contestant drafts awaiting user review in this batch.','direct_verified':7,'relay_accounts':20,'forwarding_confirmed':False,'receipts':'OpenMath-remaining-outreach-SENT-receipts.json'}
ob['openmath_fetch_map']='OpenMath-judging-fetch-map.json'
ob.setdefault('latest_user_decisions',[])
if isinstance(ob['latest_user_decisions'],list): ob['latest_user_decisions'].insert(0,{'date':STAMP,'decision':'Send all remaining necessary messages; verify retrieval routes so user can sleep and judge after cutoff. Performed direct sends/relay request; external forwarding/final packet dependencies remain explicit.'})
write('obligations-current-data.json',ob)

plan=ROOT/'OpenMath-morning-collection-plan.txt'
plan.write_text(plan.read_text(encoding='utf-8')+'\nLATEST '+STAMP+': Start from OpenMath-judging-fetch-map.json and OpenMath-outreach-readiness-current.html. Seven new direct emails, twenty organizer-forwarding requests and Raj clarification are verified sent. Check organizer relay acknowledgement and returned official acceptance/artifact register; do not call requested forwarding completed. Raj fresh claims/proofs/no-Lean/open-case details are in OpenMath-Raj-predeadline-update.txt. All 72 audit records and seven hill URLs are mapped.\n',encoding='utf-8')
desktop=Path('[LOCAL PRIVATE OBLIGATIONS RECORD]')
text=desktop.read_text(encoding='utf-8-sig')
text=re.sub(r'^Last updated: .*$', 'Last updated: '+STAMP+' (Europe/Paris)',text,count=1,flags=re.M)
decision='- '+STAMP+': User approved remaining necessary outreach. Seven new direct account emails SENT/verified; twenty individual readiness enquiries and two organizer classifications SENT to Serge/Artem for relay, forwarding still unconfirmed. Four overlaps already covered. Raj submission-reference question answered on LinkedIn/SENT verified. Complete 72-record/seven-hill retrieval map prepared; final packet/receipt/access dependencies remain pending. Collection stays October 3 06:21 CEST.\n'
text=text.replace('LATEST USER DECISIONS\n','LATEST USER DECISIONS\n'+decision,1)
text=re.sub(r'1\. \[Immediate / before cutoff\] Review all 33 account drafts and organizer relay\n.*?(?=\n2\. )','1. [Outreach DONE; waiting on authors/organizers] Retrieve final OpenMath materials\n   Seven direct messages verified; twenty account enquiries sent for organizer forwarding, not yet confirmed. Two reference-account classifications sent; four overlapping accounts already covered. All 72 contact/account records and seven hills have a retrieval route or explicit missing-material dependency. User can sleep; no further draft review is required for this batch.\n   Evidence: OpenMath-outreach-readiness-current.html; OpenMath-judging-fetch-map.json\n',text,count=1,flags=re.S)
text+='\nHISTORY '+STAMP+'\n'+decision+'Evidence: outputs/OpenMath-remaining-outreach-SENT-receipts.json; outputs/OpenMath-Raj-identifier-clarification-SENT.json; outputs/OpenMath-judging-fetch-map.json; outputs/OpenMath-outreach-readiness-current.html. Owners: authors deliver frozen artifacts; Serge/Artem forward 20 messages and supply official register/workflow; assistant collects at 06:21; user judges.\n'
desktop.write_text(text,encoding='utf-8')
assert len(direct)==7 and len(relay_accounts)==20 and len(entries)==72
assert all(r['sent'] and r['body_matches'] for r in direct.values())
print(json.dumps({'direct_sends':7,'relayed_account_requests':20,'forwarding_confirmed':False,'classification_accounts':2,'covered_overlaps':4,'retrieval_records':72,'hill_sources':7,'raj_clarification_sent':True,'updated':STAMP}))
