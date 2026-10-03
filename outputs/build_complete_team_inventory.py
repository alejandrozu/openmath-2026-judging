from pathlib import Path
import json,re,html
from datetime import datetime
from zoneinfo import ZoneInfo

root=Path(__file__).resolve().parent
stamp=datetime.now(ZoneInfo('Europe/Paris')).isoformat(timespec='minutes')
audit=json.loads((root/'OpenMath-team-status.json').read_text(encoding='utf-8'))
old=json.loads((root/'OpenMath-follow-up-drafts-UNSENT.json').read_text(encoding='utf-8'))
roster=json.loads((root/'OpenMath-Luma-roster.json').read_text(encoding='utf-8'))
raw=json.loads((root/'OpenMath-live-audit-raw.json').read_text(encoding='utf-8-sig'))
mail=json.loads((root/'OpenMath-expanded-mail-index.json').read_text(encoding='utf-8'))
li=json.loads((root/'LinkedIn-obligation-review.json').read_text(encoding='utf-8-sig'))

entries=[]
def add(name,category,status,lines,why,sources=(),recommendation='Draft only; user review pending',members=()):
    entries.append(dict(id='E%02d'%(len(entries)+1),name=name,category=category,status=status,lines=lines,rationale=why,sources=list(sources),recommendation=recommendation,members=list(members),sent=False))

for d in old['messages']:
    if d['recipient'].startswith('Mateus'): continue
    t=next(t for t in audit['teams'] if t['name'].startswith(d['recipient']))
    name=d['recipient']; lines=d['lines']; why=d['rationale']; status=t['materials']; members=[]
    if name.startswith('Luca'):
        name='Leanification / IMPA Tech — Luca, Mateus and Ueverton group'
        lines=[
            'Thanks, Luca, I have the repository and will begin reviewing; thank you also for clarifying that Leanification has five contributors.',
            'Please send their names/contributions and clarify how they map to the two teams Ueverton registered; I’ll check the roster issue with the organizers.',
            'Please confirm the final commit and official submission reference, and make the repository credits reflect everyone’s actual contribution.'
        ]
        why='New email October 2 23:09 CEST says five people; Ueverton’s September 26 email said two teams. Handbook entrant limit is four. Resolve with the chair while preserving real authorship; do not pretend roster is already settled or demand a duplicate packet from Mateus.'
        status='Packet received. Five-person group now reported; two-team registration and four-person entrant limit require reconciliation.'
        members=['Luca Seiki Pereira Fujii','Mateus Mundstock','Ueverton Souza','Felipe Leria','Augusto Schaefer Huff','Tiago Sánchez Ribeiro (registration-linked names; exact final five not yet named)']
    elif name.startswith('Chandragupt'):
        name='Chandragupt Sharma / Gopal Anantharaman’s registered group'
        members=['Gopal Anantharaman','Vardhan Ray','Chandragupt Sharma','Arvinder Shinh','Advaith Appajodu (registered links; final entrant roster unconfirmed)']
        why+=' Gopal’s registration links Chandragupt and Advaith; consolidate contact and confirm final roster rather than automatically treating all associated accounts as separate teams.'
    add(name,'Identified work / contact group',status,lines,why,t['sources'],d['recommendation'],members)

extras={r[0]:r for r in audit['additional_projects']}
add('Jamie Steeg / grandchallenge / GCL','Identified work / contact group','Public seven-hill campaign; current status explicitly says zero official submissions.',[
    'Hi Jamie, I found your seven-hill campaign; the status page still reports zero official submissions and an organizer-route blocker.',
    'Please send the strongest finished claim packets, pinned commits, proofs/certificates, papers and novelty notes, clearly marking conditional or unfinished results.',
    'Which exact submission step is blocking you? Please describe it so we can resolve the route before the cutoff.'
], 'Priority follow-up: substantial work may miss official submission because of an external workflow blocker. Internal accepted-agent statuses do not establish mathematical acceptance.',[extras['Jamie Steeg / grandchallenge'][1]])
add('Leon Koerbs / Cameron Fen — Erdős #3 Token Burner','Identified work / contact group','Public Lean packet found; original general hill remains unsolved.',[
    'Hi Leon and Cameron, I found your Erdős #3 Lean repository and would like to review the completed three-term result and related formalizations.',
    'Please confirm the final commit and submission references, and identify exactly which files/theorems are complete versus still contain sorry or open gaps.',
    'Please include the paper/novelty note, pinned reproduction steps and team credits; flag anything still blocking submission.'
], 'Acknowledge existing work; isolate completed formal claims from the unfinished general case and supporting files.',[extras['Leon Koerbs / Cameron Fen'][1]])
add('Frederik Smits van Oyen — K4 Ramsey and Heilbronn','Identified work / contact group','Two public Sundai projects, one person; no final combined packet identified.',[
    'Hi Frederik, I found your K4 Ramsey and Heilbronn projects; please share the final repositories, papers and submission references for any results you want judged.',
    'For each, separate finished proofs/certificates from search results, and explain the exact advance over the frozen reference or any useful formalization.',
    'Please confirm the final commits and reproduction steps, and tell me if anything is still incomplete or blocked.'
], 'One contact for two projects. Project descriptions do not establish improved mathematical records; request precise completed contribution rather than praise a breakthrough.',[extras['Frederik Smits van Oyen — Ramsey'][1],extras['Frederik — Heilbronn'][1]])
add('Ilknur Icke — Tissue Busy Beaver','Identified work / contact group','Toy kidney-development project; no final artifact link identified.',[
    'Hi Ilknur, I found Tissue Busy Beaver; are you submitting a formal mathematical result from it to OpenMath?',
    'If so, please share the repository, exact model/theorem, proof or certificate, paper, reproduction steps and submission reference before the cutoff.',
    'Please distinguish the toy-model result from biological validation, and let me know what is still unfinished or blocked.'
], 'First establish whether this Sundai demo is intended as a score-bearing entry; do not treat toy simulations as BB6 or validated biology.',[extras['Ilknur Icke — Tissue Busy Beaver'][1]])
add('Willem Nielsen — Adaptive Turing Machines','Identified work / contact group','Public project description, no final inspectable packet found.',[
    'Hi Willem, are you submitting a completed result from Adaptive Turing Machines? Please send the final repository and submission reference before the cutoff.',
    'Include the exact machine/witness, halting certificate and checker, paper and reproduction instructions; mark exploratory or unfinished work clearly.',
    'Let me know if access, checking or submission is blocking you so I can help.'
], 'Description alone cannot be judged. Ask for the exact halted witness/certificate and clarify intent.',[extras['Willem Nielsen — Adaptive Turing Machines'][1]])
add('Shafeeq — Ramsay Multiplier K4','Identified work / contact group','Two duplicate project cards; possible shaff622 account association unconfirmed.',[
    'Hi Shafeeq, I found both Ramsay Multiplier project pages; please confirm the final team, repository and whether shaff622 is your hill account.',
    'Please send the final exact graph/weights, density calculation, proof/certificate, paper and submission reference before the cutoff.',
    'Which version should we judge, and is anything still unfinished or blocked?'
], 'Deduplicate cards and resolve stale project descriptions versus the better validation score before selecting a result.',[extras['Shafeeq — Ramsay Multiplier K4'][1]])

already={'LUCA SEIKI PEREIRA FUJII','Mateus Mundstock','Ueverton Souza','Willem Nielsen','Stephen Wolfram','Jamie Steeg','Matt','Woohyuk Kang','Wenyi Wang','Chris Forrester','Chaewon Yoon','Gopal Anantharaman','Alexandra'}
focus={
 'Chenguang Xu':'your topology/formalization work','王启超':'your Lean/formalization work','Suraj Saxena':'your Kobon work','Will':'your Kobon work',
 'Mick Darling':'your OpenMath work','Ganesh Prakash Jamadar':'your AI-assisted mathematics work','Krish Vijay':'your formally checked reasoning work',
 'Kevin Srun':'any mathematical result you completed','Thinking Machines':'your team’s Ramsey work','Aaron Soetopo':'your OpenMath work',
 'Young Jae Koh':'your number-theory or complexity work','Yev Barkalov':'your OpenMath results','Stan':'your formalization work',
 'Antoine de Saint Germain':'your algebraic-combinatorics formalization','Ryan Bahadori':'your team’s OpenMath work','Yikun Ding':'your OpenMath results',
 'Sagnik Chatterjee':'your interaction-net/agent work','Japinder singh':'any OpenMath team you joined'
}
for r in roster:
    if r['name'] in already: continue
    pending='Approve' in r['status']
    name=r['name']
    if name=='Stan': name='Stan / Stanislav Srednyak'
    if name=='Thinking Machines': name='Thinking Machines — Jonathan Duran / Rishik Pavani / Zachary Norton'
    phrase=focus.get(r['name'],'your OpenMath work')
    lines=[f'Hi {r["name"]}, did you complete an OpenMath entry or join another team? Please confirm the final team and target.',
           f'If you are submitting {phrase}, please share the repository, paper/novelty note, formal proof or certificate and reproduction steps before the cutoff.',
           'Please send the submission reference or flag the exact blocker; I can then review the finished materials.']
    if pending:
        lines[2]='Your Luma registration still shows pending approval; is that or another submission step blocking you? Please tell me exactly what is missing.'
    status=('Registration pending approval. ' if pending else 'Registered Going. ')+'Proposed work only; no final packet linked in the checked records.'
    why='Use a participation/status question, not a demand to finish an unconfirmed entry. '+('Pending approval is an organizer-side issue; do not imply this person failed to submit or is eligible already.' if pending else 'A Going registration is not proof of a finished mathematical submission.')
    if r['name']=='Kevin Srun': why+=' Possible kevinsrun account; confirm mapping before merging.'
    if r['name']=='Will': why+=' Possible willow2014 account; confirm mapping. This is not established to be Micah’s website designer Will.'
    if r['name']=='Yev Barkalov': why+=' Do not infer that yavol is Yev from name similarity.'
    add(name,'Additional registered candidate',status,lines,why,[l['url'] for l in r['links']], 'Optional status check; higher priority for pending approval if actively submitting')

# Preserve every successful-run account, including pre-window baselines and probable aliases.
account_runs={}
for r in raw:
    if r['kind']!='leaderboard': continue
    header=None
    for line in r['text'].splitlines():
        if line.startswith('#\tClimber'): header=line.split('\t');continue
        if not re.match(r'^\d+\t',line): continue
        cells=line.split('\t'); account=cells[1]
        record={'hill':r['url'].split('/')[5],'url':r['url'],'values':dict(zip(header or [],cells)),
                'table':'held-out test' if len([q for q in r['text'].splitlines() if re.match(r'^\d+\t',q)])==1 and ('held-out test set' in r['text']) else 'validation/parameter table',
                'date':cells[-1], 'pre_window':cells[-1]<'2026-09-27'}
        if record not in account_runs.setdefault(account,[]): account_runs[account].append(record)
known={'lavaskiller':'Woohyuk / HTPeo','madhanj05':'Luke / Madhan','a-hamdi':'Sakana: Hamdi','rachtsy':'Sakana: Rachel',
       'wenyi-ai-wang':'Sakana: Wenyi','chandraguptsharma07':'Chandragupt','chaewon-research':'Chaewon',
       'lazyluca':'Luca / Leanification','srirangam-r':'Raj'}
probable={'advaith-appajodu':'Possibly Gopal/Chandragupt-associated Advaith; not confirmed final entrant',
          'kevinsrun':'Possibly Kevin Srun; needs confirmation','willow2014':'Possibly Will registered for Kobon; needs confirmation',
          'shaff622':'Possibly Shafeeq’s project; needs confirmation','sergeicu':'Possibly organizer/test account; do not send contestant reminder until confirmed',
          'ottogin':'Owns Erdős #3 hill and pre-window baselines; competitor versus infrastructure status unconfirmed'}
accounts=[]
for account,runs in sorted(account_runs.items()):
    mapped=known.get(account)
    accounts.append(dict(account=account,mapped_contact=mapped,association_note=probable.get(account),runs=runs))
    if mapped: continue
    hills=', '.join(dict.fromkeys(r['hill'].replace('-',' ') for r in runs))
    current=any(not r['pre_window'] for r in runs)
    lines=[f'Hi, I found the {account} hill account; please confirm the human author/team and whether these runs are intended as an OpenMath entry.',
           'If entering, please share the final repository, exact claim, paper/novelty note, approved proof or certificate and reproduction steps before the cutoff.',
           'Please include the pinned commit and submission reference, distinguish event-week advances from earlier baselines, and flag any blocker.']
    why='Account found in successful-run tables, but human identity/entrant status is not verified. '+('Some/all runs are before the common September 27 freeze; baseline-only work cannot be assumed to be a new competition result.' if any(r['pre_window'] for r in runs) else 'A validation score is not a final receipt or accepted mathematical result.')
    if account in probable: why+=' '+probable[account]+'.'
    if account=='hl728': why+=' Prioritize exact Ramsey held-out certificate and attribution.'
    if account=='vyahhi': why+=' Prioritize the 572171-step BB6 held-out certificate; bounded hill performance is not a global BB6 record.'
    if account=='rohith18p': why+=' Includes a 470-triangle n=39 construction plus 93 at n=18; retrieve both exact witnesses.'
    if account=='octavianboji': why+=' 468-triangle n=39 construction merits witness review.'
    add(account,'Unmapped or provisionally associated hill account',hills+'; '+('event-week run present' if current else 'only pre-window runs captured'),lines,why,list(dict.fromkeys(r['url'] for r in runs)), 'Identify human recipient and active entry before sending')

interest_names=['Tom de Groot','Edward Hogan','Sri Kamarthapu','Arham Shuaib','Alexandros Kyriakakis','Martin Dvorak']
for name in interest_names:
    sources=[r['url'] for r in li if r.get('person')==name]
    if name=='Martin Dvorak': sources=['https://mail.google.com/mail/u/0/#all/1a0ae525b14fa27b']
    add(name,'Interested outreach only — participation unconfirmed','Interest/invitation discussion; no matched final entrant or packet found.',[
        f'Hi {name.split()[0]}, did you end up participating in OpenMath or joining a team?',
        'If you have a finished entry, please send the repository, paper/novelty note, formal proof or certificate and submission reference before the cutoff.',
        'Otherwise, no action needed; I’ll keep you in mind for future events.'
    ],'Low-priority optional check, not an overdue obligation. Do not count interest as actual participation.',sources,'Usually skip tonight unless you know they entered')

exclusions=[
 ['Stephen Wolfram','Judge/speaker, not a contestant to chase'],['Alexandra / Hsu','Luma Not Going'],
 ['Rameez Malik','Explicitly declined'],['Thorge Lindner / Fermi','No current capacity; future events only'],
 ['Christoph Stephan group','Explicitly declined'],['Sébastien Gouëzel','Explicitly declined'],
 ['Filippo Nuccio / FALSE','Explicitly declined'],['Laura Monk','Declined competition concept'],
 ['Natarajan Shankar / SRI','Unavailable; forwarded interest elsewhere'],['Guillaume Claret / Formal Land','Declined; no entry established'],
 ['Yujin Tang','Introduced Sakana colleagues; not a separate entrant established'],
 ['Yiming Xu, Fiona Skerman, Yacin Hamami, Jack McCarthy, Harry Baik, Molly White / Topos','Information-forwarding contacts, not registered teams established'],
 ['Floris van Doorn','Asked about students/tool access; no entry established'],['Yaman Garg','Kickoff well-wish only; no entry established'],
 ['Other invitation recipients','Cold invitations only; preserved in source index, not assumed to have entered']]
invite_index=json.loads((root/'OpenMath-invitation-index.json').read_text(encoding='utf-8'))
invite_labels=[]
for r in invite_index:
    m=re.search(r'^(?:Hi|Dear)\s+([^,!\n]+)[,!]',r['snippet'])
    if m:
        label=m.group(1)
        if label not in invite_labels: invite_labels.append(label)

for e in entries: assert len(e['lines'])<=3
inventory={'updated':stamp,'scope':'Accessible event project cards, current Luma registration, captured seven hill leaderboards, received event email and recorded LinkedIn outreach. Not an official unique-team/submission count.',
           'counts':{'identified_work_contact_groups':15,'additional_registered_candidates':18,'leaderboard_accounts':len(accounts),'unmapped_or_provisional_accounts':len([a for a in accounts if not a['mapped_contact']]),'interested_outreach_only':6,'draft_records':len(entries)},
           'entries':entries,'leaderboard_accounts':accounts,'excluded_or_nonentrant_contacts':exclusions,'outreach_invitation_labels':invite_labels,
           'limitations':['Private/failed/unscored climb histories and official frozen entrant register unavailable; no claim that all 111 climbs or all worldwide entrants were inspected.',
                          'Sundai Pitch tab requires login; launched Projects tab has ten cards (duplicate Shafeeq and two Frederik projects).',
                          'Registration and account records overlap; these candidate records must not be called this many independent teams.',
                          'No new messages sent. No approval, eligibility, authorship or mathematical acceptance decision made.'],
           'new_leanification_evidence':{'luca_email':'https://mail.google.com/mail/u/0/#all/1a0fe744d01dfe16','time':'2026-10-02T23:09:53+02:00','summary':'Luca says team consists of five people registered with impatech accounts; exact names not given. Ueverton September 26 email said two teams. Handbook entrant limit four; roster/entry corrections require chair reconciliation.'}}
(root/'OpenMath-complete-team-inventory.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2),encoding='utf-8')
lines=['OPENMATH — COMPLETE ACCESSIBLE INVENTORY AND THREE-LINE FOLLOW-UP DRAFTS — UNSENT','Updated '+stamp,inventory['scope'],json.dumps(inventory['counts']),
       'All drafts UNSENT. User chooses sends. Chandragupt: wait for already-sent access reply. Unknown accounts: identify recipient/active entrant first.',
       'Cutoff: October 2 23:59 EDT / October 3 05:59 CEST. Do not promise that new work after cutoff earns credit.']
for e in entries:
    lines += ['',e['id']+' — '+e['name'],e['category'], 'Status: '+e['status'],'Recommendation: '+e['recommendation'],*e['lines'],'Rationale: '+e['rationale'],'Sources: '+'; '.join(e['sources'])]
lines+=['','EXCLUDED / NO CONTESTANT REMINDER']+['- '+n+': '+reason for n,reason in exclusions]
lines+=['','INVITATION-ONLY LABELS — NOT CONFIRMED ENTRANTS',', '.join(invite_labels),'','COVERAGE LIMITS']+inventory['limitations']
(root/'OpenMath-all-team-drafts-UNSENT.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8-sig')

def esc(v):return html.escape(str(v))
def rows_table(headers,rows):return '<div class="scroll"><table><tr>'+''.join('<th>'+esc(h)+'</th>' for h in headers)+'</tr>'+''.join('<tr>'+''.join('<td>'+esc(c)+'</td>' for c in r)+'</tr>' for r in rows)+'</table></div>'
body='<h1>OpenMath: complete accessible roster and drafts</h1><p>Updated '+esc(stamp)+'</p><p>'+esc(inventory['scope'])+'</p><p><b>All drafts UNSENT. '+esc(str(inventory['counts']))+'</b></p>'
body+='<p>New evidence: Luca reports five contributors; Ueverton originally registered two teams. Reconcile with the chair under the four-person entrant limit, preserving actual authorship.</p>'
body+=rows_table(['ID','Contact/account','Evidence class','Status','Recommended action'],[[e['id'],e['name'],e['category'],e['status'],e['recommendation']] for e in entries])
body+='<h2>Individual drafts and rationale</h2>'
for e in entries:
    body+='<article id="'+e['id']+'"><h3>'+esc(e['id']+' — '+e['name'])+'</h3><p><b>'+esc(e['recommendation'])+'</b></p><blockquote>'+ '<br>'.join(esc(s) for s in e['lines'])+'</blockquote><p><b>Rationale:</b> '+esc(e['rationale'])+'</p><p>'+ '; '.join('<a href="'+esc(s)+'">Source</a>' for s in e['sources'])+'</p></article>'
body+='<h2>All 42 captured leaderboard accounts</h2>'+rows_table(['Account','Matched/provisional owner','Runs'],[[a['account'],a['mapped_contact'] or a['association_note'] or 'Unknown human/team','; '.join(r['hill']+' '+str(r['values'])+' ('+r['table']+')' for r in a['runs'])] for a in accounts])
body+='<h2>No contestant reminder</h2>'+rows_table(['Contact','Reason'],exclusions)+'<h2>Invitation-only names/labels</h2><p>'+esc(', '.join(invite_labels))+'</p><h2>Coverage limits</h2><ul>'+''.join('<li>'+esc(s)+'</li>' for s in inventory['limitations'])+'</ul>'
page='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>OpenMath complete roster and drafts</title><style>body{font:16px/1.55 system-ui;margin:0;background:#f5f7fb;color:#17233a}main{max-width:1350px;margin:auto;padding:34px}table{border-collapse:collapse;background:white;width:100%}.scroll{overflow:auto}td,th{border:1px solid #d8dfeb;padding:12px;text-align:left;vertical-align:top;min-width:110px}th{background:#17334e;color:white}article{padding:20px;margin:20px 0;background:white;border-radius:10px}blockquote{margin:12px 0;padding:14px;background:#edf5fb;border-left:4px solid #337ea4}a{color:#165aad}td{overflow-wrap:anywhere}</style><main>'+body+'</main></html>'
(root/'OpenMath-complete-team-inventory.html').write_text(page,encoding='utf-8')

# Correct the old audit/draft records so future use cannot revive stale roster assumptions.
update='NEW October 2 23:09 CEST: Luca reports five contributors, while Ueverton September 26 said two registered teams. Confirm exact named rosters and chair-approved arrangement under the four-person entrant rule; preserve genuine credits.'
for t in audit['teams']:
    if t['name'].startswith(('Luca','Mateus')):t['missing']=update+' '+t['missing']
audit['roster_updated']=stamp
audit['complete_inventory_file']=str(root/'OpenMath-complete-team-inventory.json')
(root/'OpenMath-team-status.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2),encoding='utf-8')
old['superseded_by']=str(root/'OpenMath-all-team-drafts-UNSENT.txt')
old['warning']='Leanification separate-team assumption superseded by new five-person clarification; use new combined roster message. No original drafts sent.'
(root/'OpenMath-follow-up-drafts-UNSENT.json').write_text(json.dumps(old,ensure_ascii=False,indent=2),encoding='utf-8')
data_path=root/'obligations-current-data.json';data=json.loads(data_path.read_text(encoding='utf-8'))
data['drafting_updated']=stamp
data['follow_up_drafts']={'file':str(root/'OpenMath-complete-team-inventory.json'),'status':'UNSENT — user review pending','counts':inventory['counts'],'not_unique_team_count':True}
data['latest_user_decisions'].append(stamp+': User expanded drafts/inventory to every identifiable event team, registered candidate and leaderboard account, including Jamie. Complete accessible inventory prepared; no sends.')
data['ordered'][0][2]='Review complete OpenMath inventory and choose follow-up recipients'
data['ordered'][0][3]='Includes 15 identifiable work/contact groups, 18 additional registered candidates, 42 hill accounts (9 mapped; 33 unresolved/provisional), and 6 interested outreach contacts. Individual drafts at most three lines, with rationale. These are overlapping records, not independent team counts. All UNSENT.'
data['ordered'][0][4]='OpenMath-complete-team-inventory.html'
data['waiting'][-1][3]=update
data_path.write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
todo_path=Path('[LOCAL PRIVATE OBLIGATIONS RECORD]');todo=todo_path.read_text(encoding='utf-8-sig')
todo=re.sub(r'^Last updated:.*$','Last updated: '+stamp+' (Europe/Paris)',todo,count=1,flags=re.M)
todo=todo.replace('LATEST USER DECISIONS\n','LATEST USER DECISIONS\n- '+stamp+': Expanded to all identifiable event groups, registered candidates and hill accounts. Complete inventory/drafts are UNSENT. New Luca five-person clarification supersedes separate-team assumptions; chair/roster resolution needed.\n',1)
todo=todo.replace('1. [Tonight / next immediate decision] Review the short follow-up drafts and select sends','1. [Tonight / next immediate decision] Review the complete team inventory/drafts and select recipients')
todo+='\nDATED HISTORY — '+stamp+'\nUser requested every team in the detailed audit, including Jamie and all discoverable entrants. Rechecked Luma full registration (31 records), Sundai projects/Pitch access, Jamie current campaign, event-related received emails, captured seven-hill account tables, and recorded LinkedIn outreach. Added all 42 successful-run accounts; unknown/probable aliases preserved rather than counted as independent teams. '+update+'\nCounts (overlapping, not unique teams): '+str(inventory['counts'])+'\nThree-line drafts and rationale for every candidate record: '+str(root/'OpenMath-all-team-drafts-UNSENT.txt')+'\nBrowsable inventory: '+str(root/'OpenMath-complete-team-inventory.html')+'\nNo messages sent; no eligibility or roster decisions made. Declined invitees/judge/Not Going contacts excluded from contestant reminders. Private/unscored climb history and official final entrant register remain unavailable. All other task statuses preserved.\n'
todo_path.write_text(todo,encoding='utf-8-sig')
print(json.dumps(inventory['counts']))
