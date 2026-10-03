from pathlib import Path
import json,html,re
from datetime import datetime
from zoneinfo import ZoneInfo
root=Path(__file__).resolve().parent
stamp=datetime.now(ZoneInfo('Europe/Paris')).isoformat(timespec='minutes')
def read(name):return json.loads((root/name).read_text(encoding='utf-8-sig'))
def save(name,data):(root/name).write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
inv=read('OpenMath-complete-team-inventory.json')
emails=read('OpenMath-follow-email-receipts.json')
ui=read('OpenMath-follow-LinkedIn-receipts.json')
contacts=read('OpenMath-contact-routes-private.json')
roster=read('OpenMath-Luma-roster.json')
profiles=read('OpenMath-hill-public-profiles.json')['profiles']
autolab=read('OpenMath-Autolab-public-account-profiles.json')
assert len(autolab)==33
byid={x['id']:x for x in inv['entries']}
receipts=[]
for r in emails['receipts']:
 r=dict(r,channel='Email',recipient=byid[r['id']]['name'])
 r['url']='https://mail.google.com/mail/u/0/#sent/'+r['message_id']
 receipts.append(r)
receipts+=ui
martin=dict(emails['interest_martin'],channel='Email',recipient='Martin Dvořák',url='https://mail.google.com/mail/u/0/#sent/'+emails['interest_martin']['message_id'])
receipts.append(martin)
for r in receipts:
 r.setdefault('recipient',byid[r['id']]['name'])
 r.setdefault('channel','LinkedIn')
assert len(receipts)==21 and len({x['id'] for x in receipts})==21
assert set('E%02d'%i for i in range(1,16)).issubset({x['id'] for x in receipts})
for r in receipts:
 e=byid[r['id']];e.update(sent=True,recommendation='SENT and verified; await reply',receipt=r)
 if r['id']=='E04':e['lines']=r['body'].split('\n')
byid['E04']['status']='Invitation accepted; private repository accessible. Scheme, exact Python/C checkers, Lean certificate, paper and novelty documents in MD/DOCX/PDF and reproduction directory present at c9a07daa149509c7fcddcd13819f5196beed2123. README still says work in progress; final author confirmation, complete independent checks and frozen event receipt remain unverified.'
byid['E15']['status']='AutoLab profile links SHAFF622 GitHub, named Shafeeq Mohamed; matching SOC-Claw project establishes a strong identity link. Final Ramsey team/version/packet still needs confirmation. Follow-up sent to publicly published professional commit email.'
approved=['Chenguang Xu','王启超','Suraj Saxena','Will','Mick Darling','Ganesh Prakash Jamadar']
for c in contacts:c['status']=c['status'].strip().replace('\u200b','').strip()
for r in roster:
 c=next(x for x in contacts if x['name']==r['name']);r['status']=c['status']
save('OpenMath-Luma-roster.json',roster)
drafts=[]
for i in range(16,34):
 e=byid['E%02d'%i]
 key=e['name'].split(' — ')[0].split(' / ')[0]
 c=next(x for x in contacts if x['name'].casefold()==key.casefold())
 r=next(x for x in roster if x['name']==c['name'])
 lines=list(e['lines'])
 if c['name'] in approved:
  lines[0]=f"Hi {c['name']}, your registration is now approved; did you complete an OpenMath entry or join a team? Please confirm the team and target."
  lines[2]='Please share the final submission reference and flag any access, proof-checking or submission blocker so I can help.'
 e['status']='Registered Going (approval verified). No final packet located in the checked mail, registration or project records.'
 e['rationale']='Registration is confirmed, but a finished entry is not yet established. Ask for actual work and any blocker; avoid assuming the proposed topic became a submitted result.'
 if i==19:
  lines[0]='Hi Will, your registration is approved; did you complete Kobon work, and is willow2014 your hill account? Please confirm your final team.'
  lines[1]='If you want it judged, please share the exact line arrangement, checker, paper/novelty note, final repository and submission reference.'
  e['rationale']+=' Possible willow2014 overlap remains unconfirmed; consolidate rather than send another account reminder. This is not established to be Micah’s designer Will.'
 if i==23:
  lines[0]='Hi Kevin, did you complete an OpenMath entry, and is kevinsrun your hill account? Please confirm the final team and target.'
  lines[1]='If the 93-triangle Kobon result is yours, please share the exact arrangement, checker, paper/novelty note, final repository and submission reference.'
  e['rationale']+=' Likely kevinsrun overlap; ask once in this draft instead of making a second message. Ninety-three ties the existing 18-line lower bound.'
 if i==24:lines[0]='Hi Jonathan, Rishik and Zachary, did Thinking Machines complete Ramsey work or choose another target? Please confirm your final team.'
 if i==28:lines[1]='If you completed a theorem, formalization or proof-checking tool, please share its repository, precise claim, paper/novelty note and reproducible verification.'
 if i==29:
  lines[0]='Hi Antoine, did your cluster-algebra formalization or the team you were forming produce an OpenMath result? Please confirm the final scope and team.'
  e['rationale']+=' Your September 17 reply mentions contacting possible teammates; registration followed, but no later result email was found.'
 if i==32:lines[1]='If your interaction-net research produced a mathematical or verification result, please share the precise claim, repository, paper/novelty note and checking steps.'
 if i==33:lines[1]='If a team you joined has finished work, please share the repository, paper/novelty note, proof or certificate and reproduction steps.'
 e.update(lines=lines,sent=False,recommendation='UNSENT — user review required',contact={'email':c['email'],'linkedin':c['profile'] if c['profile']!='https://linkedin.com/in/none' else None,'source':'Live Luma guest table; outputs/OpenMath-contact-routes-private.json'},proposed=r['proposed'])
 drafts.append(e)
assert len(drafts)==18 and all(not x['sent'] and len(x['lines'])<=3 for x in drafts)
save('OpenMath-additional-candidate-drafts-UNSENT.json',{'updated':stamp,'scope':'All 18 additional registered candidates; none of these messages has been sent. Six registrations newly approved; twelve already Going. Registration approval is distinct from submission or judging acceptance.','drafts':drafts})
# Account-by-account assessment: captured hill performance, not a mathematical award decision.
assess={
 '1c1jp5dhwy':('Historical / low','Rank 23, support 139 on September 21: matches the old support baseline; pre-event provenance needs confirmation. No final packet identified.','No urgent reminder; ask about new formalization only if a current entry is established.'),
 'aaronatlan':('Lower priority','Grothendieck gap 1.414213 with area 4 and 80-bit certificate: compatible with the known two-by-two CHSH witness, not evidence of improving the best general lower bound.','Optional status/novelty enquiry if entering; do not label it a breakthrough.'),
 'advaith-appajodu':('Consolidate with E04','Rank 23, support 139: baseline-matching scored artifact. GitHub name Advaith Appajodu and Gopal registration associate this person with Chandragupt’s group; the final entrant roster remains unconfirmed.','Do not send another group reminder now; E04 already sent. Resolve exact team and credit.'),
 'alee792':('Historical / low','Kobon n=18: 90 triangles, below the known 93 construction; scored September 21 before the event.','No urgent reminder unless there is newer work or a useful formalization.'),
 'ashleychenyj':('Historical / low','Kobon n=18: 93, tying the known lower bound; September 21 pre-event score. No inspectable final packet identified.','No urgent chase on this score; ask for later work only if a current entry exists.'),
 'claudiagaes':('Lower priority','Kobon n=18: 93, a valid benchmark tie rather than the missing 94 arrangement or an upper-bound proof.','Optional final-artifact/novelty enquiry; no evidence that a breakthrough is being withheld.'),
 'claudioolmedo':('Historical / low','Kobon n=18: 93, baseline tie on September 20. No current final packet identified.','No urgent chase without newer work or competition-entry confirmation.'),
 'cloud-post-code':('Lower priority','BB6 validation: 178,727 steps, 180 ones, span 539. Scored candidate, substantially below the validation leader. No machine/trace packet identified.','Optional certificate/method enquiry; no global BB6 record established.'),
 'connorbuchheit':('Historical / low','Matrix rank 23, support 153 on September 20: worse than support 139 and the current 138 candidate.','No urgent reminder unless a new theorem, method or formalization was completed later.'),
 'danamouk':('High — obtain packet','Ramsey validation density 0.030142036534 beats the frozen 0.03014227343194 reference. Exact graph, rational weights and blow-up proof still absent. No Ramsey repository among the public repositories checked.','Yes, worth a targeted message after user review; confirm authorship and get the exact certificate.'),
 'ebaenamar':('Lower priority','Grothendieck gap 1.414213, area 4, 80 bits: known small witness scale; no new general lower-bound advance established.','Optional novelty/formalization status enquiry.'),
 'extraton618':('Lower priority','BB6 validation: 232,746 steps, 554 ones, span 684. Finite certified-run benchmark candidate; no final mathematical packet identified.','Optional machine/certificate and method enquiry if entering.'),
 'eychcue':('Historical / low','BB6 validation: 249,881 steps, 554 ones, span 735 on September 21; ties Hamdi/n0rang2 numerically but precedes event. Same metrics alone do not prove the same machine.','Provenance/independence enquiry only if claiming a current entry; no urgent completion reminder.'),
 'felixisaac':('Historical / low','Collatz private-target coverage 100%, minimum descent 0.525390, 269 rules on September 21. This does not cover all odd integers or prove global convergence.','No urgent chase on historical benchmark; ask only about new certificate/formalization.'),
 'fkaita':('Historical / low','Kobon n=18: 93 on September 21, known construction tie. No final packet identified.','No urgent reminder without current-entry evidence.'),
 'flaviabeppler':('Lower priority','Kobon n=18: 93 on September 28, ties the known construction; exact final arrangement/paper not identified.','Optional status/artifact enquiry if entering; useful method/formalization may still count.'),
 'frido22':('Lower priority','BB6 validation: 249,614 steps, 543 ones, span 973. Near the bounded validation leader, but no global BB6 advance or complete packet established.','Optional certificate/method enquiry; distinguish it from Chaewon’s same-step different-output result.'),
 'hl728':('Highest — obtain packet','Ramsey validation 0.030141720946 and held-out 0.030141921123 both beat the frozen reference. Strong score evidence, but GitHub has no public repositories and no exact packet/contact identity found.','Yes, prioritize an organizer introduction/account-to-team mapping; do not assume this is Hyunjin from initials.'),
 'kevinsrun':('Consolidate with E23','Kobon n=18: 93, known lower-bound tie. AutoLab links GitHub kevinsrun (display name Icer). Likely Kevin Srun registration overlap, not conclusively confirmed.','Use the unsent Kevin draft to confirm alias; no second account message.'),
 'luizfelipebarbosa':('Historical / low','Kobon n=18: 91 on September 20, below 93. GitHub names Luiz Felipe Barbosa; no final event packet identified.','No urgent reminder unless newer work exists.'),
 'n0rang2':('High — obtain packet','Ramsey 0.030142185839 beats frozen reference; BB6 validation 249,881 steps, 554 ones, span 735 ties leader metrics. Public repositories checked do not contain an event packet.','Yes, ask once for both result packets and final team; exact Ramsey witness takes priority.'),
 'octavianboji':('Medium — worth contacting','Kobon n=39: 468, behind current 471 and Rohith 470. A larger-n exact construction can be useful; no proof of optimality or final packet identified.','Yes, a short packet/status enquiry is reasonable after user review; keep n=39 distinct from n=18.'),
 'ottogin':('Organizer / reference','AutoLab links Artem Lukoianov’s GitHub and LinkedIn. Owns the Erdős #3 hill and has multiple pre-event baseline scores; n=18 Kobon 92 is also below 93.','Do not send a contestant reminder. Clarify organizer/reference versus actual entry status with the organizers.'),
 'rohith18p':('High — packet partly assembled','Public rsi-kobon-triangles repository has exact arrangements, counters/search tools, slide deck and notes. Official scores n=39: 470 and n=18: 93. Additional 46 claimed first listed constructions are development results, not all officially submitted. README’s #1 claim is stale: Woohyuk now has 471.','Yes, targeted final-paper/novelty/receipt request after review. Confirm whether collaboration with Raj is a joint event entry; their unrelated robotics coauthorship alone is insufficient.'),
 'sasap91':('Lower priority','BB6 validation: 228,641 steps, 647 ones, span 864. More ones than the step leader does not make it the step winner; no global BB6 advance established.','Optional machine/certificate and method enquiry; retain secondary metric distinction.'),
 'sergeicu':('Organizer / reference','Sundai event links the constitution in sergeicu/sundai-global; this is the organizer’s account. BB6 has 249,880 steps, 554 ones, span 735; competitor status not established.','No automatic contestant reminder; confirm whether this is demonstration/reference work.'),
 'shaff622':('Already contacted via E15','AutoLab links SHAFF622 GitHub, named Shafeeq Mohamed with matching SOC-Claw project. Ramsey 0.030142250482 beats frozen reference narrowly, while two Sundai descriptions are older and worse. Final exact packet not yet delivered.','E15 already sent. Await final version/team clarification rather than message twice.'),
 'solal24':('Lower priority','Kobon n=18: 93 tie; Grothendieck gap 1.414213, area 4, 80 bits. Both are baseline-level benchmark results.','Optional single enquiry for new formalizations/methods, not two reminders.'),
 'thomasoh0408':('Lower priority','Kobon n=18: 93 on September 28, known lower-bound tie. No final packet identified.','Optional final-artifact/novelty enquiry if claiming an entry.'),
 'vyahhi':('High — obtain certificate','Nikolay Vyahhi. Held-out BB6: 572,171 steps, 1,035 ones, span 1,380; validation 233,892 steps. Highest observed held-out score, but separate tables are not directly interchangeable. Ramsey result does not beat frozen reference. No event machine/trace packet identified among checked public repositories.','Yes, request exact transition table, replay/halting certificate, final method/paper and receipt; do not market it as a new global BB6 record.'),
 'willow2014':('Consolidate with E19','Kobon n=18: 93. Possibly Will’s registration (email willow.pine.2011), but blank GitHub identity/no recent public repository does not confirm it.','Use the unsent Will draft to ask once about the alias; do not create a second account reminder.'),
 'wilsonwu-ai':('Lower priority','Matrix rank 23, support 139 baseline tie and Grothendieck gap 1.414213 small witness. No complete final packet identified.','Optional combined status/novelty enquiry if entering; no evidence of rank-22 or new general Grothendieck bound.'),
 'yavol':('Historical / provenance','Ramsey 0.030141721098 beats frozen reference, but dated September 21. Collatz 100% weighted target coverage with three rules and BB6 246,872 steps are also pre-event. Identity is blank; do not equate yavol with Yev Barkalov.','Ask only to establish event participation, original provenance and any later work; do not chase as an unfinished new entry.')}
account_rows=[]
extra_routes=read('OpenMath-extra-account-contact-routes.json')
for a in inv['leaderboard_accounts']:
 if a['account'] not in assess:continue
 h=a['account'];p=next(x for x in profiles if x['account']==h).get('profile',{}); ap=next(x for x in autolab if x['account']==h)
 priority,summary,action=assess[h]
 route={'github':p.get('html_url'),'autolab':ap['url'],'direct':'No direct email/DM verified; request organizer introduction. A GitHub profile itself is not a messaging channel.'}
 if h=='rohith18p':route.update(email='[REDACTED CONTACT]',linkedin='https://www.linkedin.com/in/rohith-poola',direct='Published professional email or LinkedIn; relevant repository Issues also available.',source='https://rohith18p.github.io/')
 if h=='vyahhi':route.update(linkedin='https://www.linkedin.com/in/vyahhi',direct='Matched public LinkedIn profile; actual DM availability not yet tested.',source='https://www.linkedin.com/in/vyahhi')
 if h=='octavianboji':route.update(linkedin='https://ro.linkedin.com/in/octavian-boji',direct='Matched public LinkedIn profile; actual DM availability not yet tested.',source='https://ro.linkedin.com/in/octavian-boji')
 if h=='danamouk':route.update(email='[REDACTED CONTACT]',direct='Published professional address for Dana Moukheiber, probable owner of danamouk; confirm alias in message before attributing entry.',source='https://pmc.ncbi.nlm.nih.gov/articles/PMC9652771/')
 if h=='advaith-appajodu':route.update(linkedin='https://www.linkedin.com/in/advaithappajodu/',direct='Gopal’s registration-linked profile; consolidate through Chandragupt’s existing conversation.')
 if h in ['kevinsrun','willow2014']:
  e=byid['E23' if h=='kevinsrun' else 'E19'];route.update(e['contact']);route['direct']='Use this registered-candidate route to confirm the probable alias; draft UNSENT.'
 if h=='shaff622':route.update(email='[REDACTED CONTACT]',direct='Professional email from published Sundai-RL commit; E15 already sent.',source='https://github.com/SHAFF622/Sundai-RL/commit/4c8e7e20bd37c03618a13f90dac5b2f8b9be2f99')
 if h=='ottogin':route.update(linkedin='https://www.linkedin.com/in/artem-lukoianov/',direct='Existing organizer conversation; no contestant reminder.')
 if h=='sergeicu':route['direct']='Existing Serge organizer conversation; no contestant reminder.'
 draft=list(next(e['lines'] for e in inv['entries'] if e['category']=='Unmapped or provisionally associated hill account' and e['name']==h))
 if not draft:draft=[f'Hi {h}, did you produce any new OpenMath work beyond the currently listed hill result? Please confirm your final team and intended entry.', 'If so, please share the exact artifact, proof/checker, final repository and paper/novelty note, distinguishing completed claims from exploratory work.', 'Please confirm the final submission reference and flag any checking or submission blocker.']
 if h in ['hl728','danamouk','n0rang2']:
  greeting='Hi Dana, is danamouk your OpenMath hill account?' if h=='danamouk' else f'Hi {h}, are you submitting your Ramsey result to OpenMath, individually or with a team?'
  draft=[greeting+' The scored improvement looks worth reviewing.', 'Please send the final repository/commit, exact graph and rational weights, density proof/checker, paper/novelty note and submission reference.', 'What is still unfinished or blocking submission? Please also identify any other hill accounts used by your team.']
 if h=='rohith18p':draft=['Hi Rohith, I found your Kobon packet with the 39-line 470 arrangement and other constructions; please confirm the final team and whether this is a joint entry with Raj.', 'Please share the final commit, exact arrangements/checker, paper and novelty note, distinguishing officially scored results from development claims.', 'Please send the final submission reference and flag anything still unfinished or blocked; I will review the completed materials.']
 if h=='vyahhi':draft=['Hi Nikolay, are you submitting the BB6 result shown under vyahhi, including the 572,171-step held-out run?', 'Please share the exact machine, halting/replay certificate and checker, final repository/commit, paper/novelty note and submission reference.', 'Please explain the validation-versus-test results and flag any remaining checking or submission blocker.']
 if h=='octavianboji':draft=['Hi Octavian, are you submitting your 39-line Kobon arrangement with 468 triangles to OpenMath? Please confirm the final team.', 'Please share the exact line coefficients, checker, final repository/commit, paper/novelty note and submission reference.', 'Let me know what is still unfinished or blocked so I can review the completed result.']
 row={'account':h,'public_name':p.get('name'),'priority':priority,'maturity':'Scored artifact; complete final judging packet not established' if h!='rohith18p' else 'Public exact-artifact repository, tools and slide deck; polished final paper/receipt not established','assessment':summary,'recommendation':action,'runs':a['runs'],'contact':route,'lines':draft,'sent':h=='shaff622','sources':[r['url'] for r in a['runs']]+[ap['url'],p.get('html_url')],'identity_note':'AutoLab directly links this GitHub account. Human/team identity is only asserted where supported; similarity alone does not merge entries.'}
 account_rows.append(row)
 old=next(e for e in inv['entries'] if e['name']==h and int(e['id'][1:])>=34 and int(e['id'][1:])<=66)
 old.update(status=summary,rationale=summary,recommendation=action,contact=route,priority=priority,lines=draft)
 if h=='shaff622':old.update(sent=True,receipt=byid['E15']['receipt'],covered_by='E15',recommendation='Already contacted via E15; no separate message sent.')
 inv['leaderboard_accounts'][inv['leaderboard_accounts'].index(a)]['assessment']=summary
assert len(account_rows)==33
save('OpenMath-additional-hill-account-assessment.json',{'updated':stamp,'scope':'All 33 originally unmapped/provisional accounts, including later matched entrants and organizer/reference accounts. Scored results do not establish official event submission, eligibility, novelty or completed proof review.','accounts':account_rows})
inv.update(updated=stamp,outreach_summary={'identified_groups_sent':15,'interest_enquiries_sent':6,'pending_registrations_approved':6,'additional_registered_drafts_unsent':18,'verified_autolab_github_profiles':33},limitations=['Leaderboards cover successful scored runs, not all private/failed/unscored climbs. Frozen official final entrant register and final submission receipts remain unverified.','Authenticated Sundai Pitch has nine queue project links, all already in inventory; Projects has ten cards, including duplicates.','All 33 previously unmapped accounts now have AutoLab-to-GitHub links verified; these overlap team and registration records.','All 15 authorized group follow-ups plus six interest-only enquiries sent and provider/UI verified. Additional eighteen candidate drafts and new hill-account messages remain unsent.','Mathematical claims inspected and contextualized, not independently rebuilt or awarded.'])
save('OpenMath-complete-team-inventory.json',inv)
save('OpenMath-outreach-final-receipts.json',{'updated':stamp,'verification':'Provider SENT + recipient/body check for email; visible published message/issue for browser sends. This does not claim recipients have read them.','receipts':receipts,'registrations_approved':approved,'registration_evidence':'OpenMath-registrations-approved.png'})
heading='OPENMATH — NEW-CANDIDATE DRAFTS AND ACCOUNT AUDIT\nUpdated '+stamp+'\n\n15 group follow-ups + 6 interest enquiries SENT/verified; 6 pending registrations approved. All 18 drafts below are UNSENT for your review. Accounts overlap registered people and existing groups; these are not 72 independent teams.\n'
txt=heading+'\nADDITIONAL REGISTERED CANDIDATES — UNSENT\n'
for e in drafts:
 txt+='\n'+e['id']+' — '+e['name']+'\nReach: '+e['contact']['email']+'; '+str(e['contact']['linkedin'])+'\nRationale: '+e['rationale']+'\n'+'\n'.join(e['lines'])+'\n'
txt+='\nALL 33 PREVIOUSLY UNMAPPED / PROVISIONAL HILL ACCOUNTS\n'
for a in account_rows:
 txt+='\n'+a['account']+' — '+str(a['public_name'] or 'human identity unresolved')+' — '+a['priority']+'\nMaturity: '+a['maturity']+'\nAssessment: '+a['assessment']+'\nAction: '+a['recommendation']+'\nReach: '+json.dumps(a['contact'],ensure_ascii=False)+'\n'
 if a['lines']:txt+='Optional draft (UNSENT unless covered by existing E15):\n'+'\n'.join(a['lines'])+'\n'
(root/'OpenMath-next-messages-and-account-audit.txt').write_text(txt,encoding='utf-8')
(root/'OpenMath-additional-candidate-drafts-UNSENT.txt').write_text(txt.split('ALL 33 PREVIOUSLY')[0],encoding='utf-8')
esc=lambda x:html.escape(str(x or ''))
link=lambda u,label:f'<a href="{esc(u)}">{esc(label)}</a>' if u else ''
sections=[]
sections.append('<h1>OpenMath — outreach and next-message review</h1><p class="lead">15 team follow-ups sent · 6 interest enquiries sent · 6 registrations approved · 18 candidate drafts unsent</p><p>Updated '+esc(stamp)+'. Provider/UI verification establishes sending, not that recipients have read the messages.</p><p>These lists overlap. Fifteen contact groups, eighteen additional registration records and forty-two scored hill accounts are not independent team counts. All thirty-three formerly unmapped accounts were inspected individually.</p>')
sections.append('<h2>Completed sends</h2><table><tr><th>Recipient</th><th>Channel</th><th>Receipt</th></tr>'+''.join('<tr><td>'+esc(r['id']+' '+r['recipient'])+'</td><td>'+esc(r.get('channel','LinkedIn'))+'</td><td>'+link(r.get('url'),'Verified sent')+'</td></tr>' for r in sorted(receipts,key=lambda x:x['id']))+'</table><p>Leon/Cameron: public repository issue. Ilknur: company published contact address. Shafeeq: published professional commit email. No duplicate direct send was performed.</p>')
sections.append('<h2>Registrations</h2><p>Newly approved: '+esc(', '.join(approved))+'. Other twelve additional candidates were already Going. Registration acceptance does not establish a final mathematical submission or judging eligibility.</p>')
sections.append('<h2>Recommended next decisions</h2><ol><li>Review targeted drafts for hl728, danamouk, n0rang2, Rohith, Nikolay/vyahhi and Octavian. Confirm identity/contact for anonymous handles before sending.</li><li>Review the eighteen registered-candidate drafts. Kevin and Will drafts ask about likely hill aliases, avoiding duplicate outreach.</li><li>Resolve official submission route/receipts, Jamie’s blocker, Leanification final five-person roster versus four-person limit and Woohyuk admission/scope questions with organizers.</li><li>Review Chandragupt’s newly accessible private packet, then other exact Ramsey artifacts and supplied Luca/Chaewon/Raj packets. Preserve independent verification and precise mathematical scope.</li></ol>')
sections.append('<h2>18 additional registered candidates — all UNSENT</h2>')
for e in drafts:
 c=e['contact'];sections.append('<article class="candidate"><h3>'+esc(e['id']+' '+e['name'])+'</h3><p>'+link('mailto:'+c['email'],c['email'])+' '+link(c['linkedin'],'LinkedIn profile')+'</p><p><b>Why:</b> '+esc(e['rationale'])+'</p><blockquote>'+'<br>'.join(map(esc,e['lines']))+'</blockquote></article>')
sections.append('<h2>All 33 additional hill accounts</h2><p>Successful scores establish a benchmark artifact. They do not establish a polished paper, official event receipt, eligibility, novelty or independent proof approval. Pre-event means before September 27, not outside your September 15 review scope.</p>')
for a in account_rows:
 c=a['contact'];metrics='; '.join(r['hill'].replace('-',' ')+' / '+r['table']+' / '+', '.join(k+'='+v for k,v in r['values'].items() if k not in ['#','Climber']) for r in a['runs'])
 sections.append('<article class="account"><h3>'+esc(a['account']+' — '+(a['public_name'] or 'identity unresolved'))+'</h3><span class="badge">'+esc(a['priority'])+'</span><p><b>Maturity:</b> '+esc(a['maturity'])+'</p><p>'+esc(a['assessment'])+'</p><p class="metrics">'+esc(metrics)+'</p><p><b>Next action:</b> '+esc(a['recommendation'])+'</p><p><b>Reach:</b> '+esc(c['direct'])+' '+link('mailto:'+c['email'],c['email']) if c.get('email') else '<article class="account"><h3>'+esc(a['account']+' — '+(a['public_name'] or 'identity unresolved'))+'</h3><span class="badge">'+esc(a['priority'])+'</span><p><b>Maturity:</b> '+esc(a['maturity'])+'</p><p>'+esc(a['assessment'])+'</p><p class="metrics">'+esc(metrics)+'</p><p><b>Next action:</b> '+esc(a['recommendation'])+'</p><p><b>Reach:</b> '+esc(c['direct']))
 sections.append(' '+link(c.get('linkedin'),'LinkedIn')+' '+link(c.get('github'),'GitHub identity')+' '+link(c.get('autolab'),'AutoLab identity')+'</p>')
 if a['lines']:sections.append('<details><summary>Three-line draft / previous account draft — UNSENT, unless covered by E15</summary><blockquote>'+'<br>'.join(map(esc,a['lines']))+'</blockquote></details>')
 sections.append('</article>')
sections.append('<h2>New packet and mathematical context</h2><p>Chandragupt: accepted invitation, read private README and mathematical paper; current revision c9a07daa149509c7fcddcd13819f5196beed2123. Exact scheme, Python/C checking programs, Lean certificate, reproduction directory and paper/novelty files are present. Support 138 at rank 23 is the claim; no rank-22 or minimal-support proof is claimed. Independent checks, final commit confirmation and frozen event receipt remain outstanding.</p><p>Rohith: '+link('https://github.com/Rohith18p/rsi-kobon-triangles','public Kobon packet')+' contains arrangements, checking/search tools, deck and notes. '+link('https://oeis.org/A006066','OEIS')+' leaves n=39 unlisted and gives n=18 lower bound 93, upper bound 94. An unlisted value does not itself prove worldwide priority; inspect original artifacts and literature before awarding novelty. His extra values are development claims. The live n=39 board has 471/470/468, so his repository #1 wording is stale.</p><p>Captured primary evidence: seven hill descriptions and successful-run leaderboards, separate Ramsey/BB6 held-out tabs and n=39 Kobon tab; 33 public account profiles; Luma 31 registrations; authenticated Sundai pitch queue; supplied and publicly accessible repositories; current received email and LinkedIn conversations.</p><p>Private/failed/unscored climbs, unshared repositories and an official frozen final-submission register remain outside verified coverage. No contestant code was executed or proof build independently confirmed.</p>')
style='body{font:16px/1.55 system-ui;margin:0;background:#f4f6fa;color:#182336}main{max-width:1120px;margin:auto;padding:32px}h1{font-size:32px}h2{margin-top:42px}a{color:#145ac0}article{background:white;border:1px solid #dbe2eb;border-radius:10px;padding:18px;margin:15px 0}blockquote{margin:15px 0;padding:14px;background:#eef5ff;border-left:4px solid #2475b9;white-space:normal}table{border-collapse:collapse;width:100%;background:white}td,th{text-align:left;padding:10px;border:1px solid #dae0e8}.lead{font-weight:700;color:#105d44}.badge{display:inline-block;background:#e9edf7;padding:3px 8px;border-radius:5px}.metrics{font:13px/1.6 monospace;color:#596174}summary{cursor:pointer;color:#145ac0}'
(root/'OpenMath-next-messages-and-account-audit.html').write_text('<!doctype html><html lang="en"><meta charset="utf-8"><title>OpenMath outreach and account audit</title><style>'+style+'</style><main>'+''.join(sections)+'</main></html>',encoding='utf-8')
# Older filenames remain historical; mark them visibly superseded rather than silently keeping an UNSENT assertion.
for name in ['OpenMath-complete-team-inventory.html','OpenMath-team-status.html','obligations-current.html']:
 p=root/name
 if p.exists():
  s=p.read_text(encoding='utf-8-sig'); banner='<div style="padding:18px;background:#dcefe4;color:#153c29">'+esc(stamp)+': 15 team follow-ups and 6 interest enquiries sent/verified; 6 pending registrations approved. <a href="OpenMath-next-messages-and-account-audit.html">Current drafts, contact routes and account audit</a>. Older content below is historical.</div>'
  s=re.sub(r'(<body[^>]*>)',lambda m:m.group(1)+banner,s,count=1) if '<body' in s else banner+s
  p.write_text(s,encoding='utf-8')
old=root/'OpenMath-all-team-drafts-UNSENT.txt'
if old.exists():old.write_text('HISTORICAL DRAFT SNAPSHOT — SUPERSEDED '+stamp+'. E01–E15 and E67–E72 have since been sent. Use OpenMath-next-messages-and-account-audit.txt for current UNSENT drafts.\n\n'+old.read_text(encoding='utf-8-sig'),encoding='utf-8')
# Preserve all unrelated obligations, user decisions and earlier history.
todo=Path('[LOCAL PRIVATE OBLIGATIONS RECORD]'); text=todo.read_text(encoding='utf-8-sig')
(root/'to-do-before-outreach-final.txt').write_text(text,encoding='utf-8')
text=re.sub(r'^Last updated:.*$', 'Last updated: '+stamp+' (Europe/Paris)',text,count=1,flags=re.M)
newdecision='- '+stamp+': User-authorized E01–E15 team follow-ups SENT/verified, six interest-only status enquiries SENT/verified, six pending registrations APPROVED/Going. E16–E33 additional-candidate drafts and new hill-account outreach remain UNSENT for user review. All 33 account profiles assessed; group/account overlaps preserved. Chandragupt invitation accepted and packet now readable.\n'
text=text.replace('LATEST USER DECISIONS\n','LATEST USER DECISIONS\n'+newdecision,1)
text=text.replace('- OpenMath audit now available; user will decide which contestants to remind and then help. No additional contestant reminders authorized yet.','- OpenMath: the specifically authorized fifteen group follow-ups and six interest enquiries are complete. User will review the eighteen new-candidate drafts and additional-account recommendations before any further sends.')
text=text.replace('- Chandragupt access reply authorized and SENT/verified at 23:08 CEST October 2. Await private invitation; do not invent Stephen GitHub username.','- Chandragupt access reply and follow-up SENT/verified; invitation received 23:14 CEST October 2 and accepted. Private packet accessible, paper/novelty exports present; independent mathematical review/final receipt still pending. Do not invent Stephen GitHub username.')
text=re.sub(r'1\. \[Tonight / next immediate decision\] Review the complete team inventory/drafts and select recipients\n.*?(?=\n2\.)','1. [Immediate / before October 3 06:00 CEST cutoff] Review the UNSENT new-candidate and hill-account drafts\n   Fifteen group follow-ups and six interest enquiries sent; six pending registrations approved. Review eighteen additional registered-candidate drafts with verified email routes. Prioritize hl728, danamouk, n0rang2, Rohith, Nikolay/vyahhi and Octavian; resolve anonymous identities and possible overlaps before sending. Await current group replies rather than repeating messages.\n   Evidence: outputs/OpenMath-next-messages-and-account-audit.html\n',text,flags=re.S,count=1)
text=text.replace('- Chandragupt GitHub access reply: SENT and screenshot/receipt verified October 2, 23:08 CEST; repo invitation remains outstanding.','- Chandragupt GitHub access reply and follow-up: SENT/verified. Received invitation accepted; repository and paper/novelty documents read. Final author confirmation, receipt and independent checks remain future work.')
text=text.replace('- Ten approved OpenMath outreach messages: sent and verified previously. Artem’s no-tools WhatsApp reply: sent previously.','- Ten initial OpenMath outreach messages: sent and verified previously. The later fifteen team follow-ups and six interest-only enquiries are also sent/verified. Six pending Luma registrations are approved. Artem’s no-tools WhatsApp reply was sent previously.')
text=re.sub(r'^- W20 \|.*$', '- W20 | Tom / Edward / Sri / Arham / Alexandros / Martin | Reply to status enquiries about any actual OpenMath work | Six short enquiries sent and verified October 2, 23:49–23:54 CEST. | Await answers; no duplicate reminder queued. | Enquiry complete; participation/results unconfirmed',text,flags=re.M,count=1)
text=re.sub(r'^- W21 \|.*$', '- W21 | Chandragupt / judges | Final packet confirmation and independent review | Invitation delivered and accepted; scheme/checkers/Lean, paper and novelty MD/DOCX/PDF, reproduction directory present at c9a07daa149509c7fcddcd13819f5196beed2123. | Confirm final revision/event receipt and review exact identities/novelty; no second access request. | Access complete; judging pending',text,flags=re.M,count=1)
text=text.replace('Before cutoff / at closure; user controls further contestant reminders.','Before cutoff / at closure; current fifteen reminders are sent, new eighteen drafts await user review.')
text+='\n\nDATED HISTORY — '+stamp+' — OUTREACH AND ACCOUNT AUDIT COMPLETE\nUser authorized all fifteen identified groups and interest-only enquiries. Sent and verified 15 group requests (10 emails, 4 LinkedIn messages, 1 public GitHub repository issue) and 6 interest enquiries (5 LinkedIn, 1 email). Email SENT/recipient/body checked; browser messages and issue visibly published. Sending does not establish recipient read/response. Leon/Cameron used relevant GitHub issue because LinkedIn required Premium. Ilknur used her published company contact; Shafeeq used published professional commit address.\nSix pending Luma candidates approved: '+', '.join(approved)+'. Other twelve additional registrations were already Going. All eighteen bespoke drafts remain UNSENT. No new hill-account message sent; Shafeeq is covered by E15, Advaith by group E04, Kevin/Will aliases are asked in their unsent drafts.\nResearched all thirty-three provisional hill accounts, directly verified AutoLab-to-GitHub links; six high/medium priorities: hl728, danamouk, n0rang2, rohith18p, vyahhi, octavianboji. Organizer/reference accounts ottogin (Artem) and sergeicu kept distinct. Pre-event results retain provenance. Rohith public exact arrangements/tools/deck found; 470 at n=39 behind current Woohyuk 471, extra values are development claims. Scores do not prove official event submission, novelty, optimality or global Collatz/BB6 solutions.\nAuthenticated Sundai Pitch queue checked: nine project links, no new group beyond existing inventory. Seven hills reviewed; successful-run boards refreshed, including separate held-out BB6 and n=39 Kobon tables. Ramsey Rachel score changed slightly to 30140930507; rankings unchanged. All eighteen registered-candidate sender addresses searched since September 15; only Antoine September 17 interest reply found, no new final packet email.\nChandragupt invitation accepted; private matrix packet now inspectable, current revision c9a07daa149509c7fcddcd13819f5196beed2123. Paper/novelty MD/DOCX/PDF and reproduction directory present despite stale README work-in-progress status. Mathematical claim support 138 at rank 23; independent checking, final confirmation and receipt not completed.\nCurrent review artifact: '+str(root/'OpenMath-next-messages-and-account-audit.html')+'\nUnsent eighteen drafts: '+str(root/'OpenMath-additional-candidate-drafts-UNSENT.txt')+'\nStructured account assessment: '+str(root/'OpenMath-additional-hill-account-assessment.json')+'\nVerified receipts: '+str(root/'OpenMath-outreach-final-receipts.json')+'\nAll unrelated DONE/SHELVED/BLOCKED/IN PROCESS decisions preserved; expense-only Micah draft remains UNSENT.\n'
todo.write_text(text,encoding='utf-8')
data=read('obligations-current-data.json');data['reviewed']=stamp;data['openmath_outreach']=inv['outreach_summary'];data['latest_user_decisions']=data.get('latest_user_decisions',[])
if isinstance(data['latest_user_decisions'],list):data['latest_user_decisions'].append(newdecision.strip('- \n'))
data['next_openmath_review_file']='OpenMath-next-messages-and-account-audit.html';save('obligations-current-data.json',data)
ts=read('OpenMath-team-status.json');ts['outreach_updated']=stamp;ts['outreach_summary']=inv['outreach_summary'];ts['next_review_file']='OpenMath-next-messages-and-account-audit.html';save('OpenMath-team-status.json',ts)
print(json.dumps({'updated':stamp,'sent':len(receipts),'drafts_unsent':len(drafts),'accounts_assessed':len(account_rows),'autolab_profiles':len(autolab),'report':str(root/'OpenMath-next-messages-and-account-audit.html')},ensure_ascii=True))
