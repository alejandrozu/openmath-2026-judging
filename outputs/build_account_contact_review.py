import json, html, re
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parent
NOW = datetime.now(ZoneInfo('Europe/Paris')).isoformat(timespec='minutes')
def read(name):
    return json.loads((ROOT/name).read_text(encoding='utf-8-sig'))
def save(name, data):
    (ROOT/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
old = read('OpenMath-additional-hill-account-assessment.json')
profiles = {p['account']:p for p in read('OpenMath-account-contact-profile-readback.json')}
extra = read('OpenMath-extra-contact-source-readback.json')
assert len(profiles)==33
sent = read('OpenMath-additional-candidate-SENT-receipts.json')['receipts']
assert len(sent)==18 and all(x['sent'] and x['body_matches'] for x in sent)

contact_updates = {
    'alee792': {'email':'[REDACTED CONTACT]','source':'https://github.com/alee792','direct':'Published on the directly linked GitHub profile; email route ready, deliverability untested.'},
    'eychcue': {'email':'[REDACTED CONTACT]','source':'https://github.com/eychcue','direct':'Published on the directly linked GitHub profile; email route ready, deliverability untested.'},
    'felixisaac': {'email':'[REDACTED CONTACT]','linkedin':'https://linkedin.com/in/felixisaac','source':'https://github.com/FelixIsaac','direct':'Professional email and LinkedIn published on the owner’s profile README.'},
    'claudioolmedo': {'linkedin':'https://www.linkedin.com/in/claudioolmedo-com/','source':'https://github.com/claudioolmedo','direct':'LinkedIn linked by the owner’s GitHub profile. Messaging access untested; organizer relay if paid/blocked.'},
    'fkaita': {'linkedin':'https://www.linkedin.com/in/kaita-furukawa-7234a312a','source':'https://www.spkaikai.com/about-8','direct':'Owner-linked personal About page names Kaita Furukawa and links this LinkedIn profile. Messaging access untested.'},
    'luizfelipebarbosa': {'email':'[REDACTED CONTACT]','linkedin':'https://www.linkedin.com/in/luiz-felipe-barbosa-5989a9294','source':'https://lfpmb.com/','direct':'Email is published on the owner-linked personal site; LinkedIn also linked by GitHub.'},
    'octavianboji': {'email':'[REDACTED CONTACT]','source':'https://github.com/OctavianBoji','direct':'Email published on the directly linked GitHub profile; prefer this over an untested LinkedIn DM.'},
    'ottogin': {'email':'[REDACTED CONTACT]','source':'https://github.com/ottogin','direct':'Organizer: existing [REDACTED CONTACT]/[REDACTED CONTACT] correspondence; GitHub also publishes arteml@mit.edu.'},
    'wilsonwu-ai': {'linkedin':'https://www.linkedin.com/in/wilson1wu','source':'https://www.linkedin.com/in/wilson1wu','direct':'Indexed LinkedIn profile explicitly references github.com/wilsonwu-ai; profile accessible, contact overlay not loaded. Ask to confirm alias; DM/Premium availability untested.'},
    'kevinsrun': {'direct':'E23 email SENT/verified this turn to Kevin Srun, explicitly asking whether kevinsrun is his account. Await alias/result reply; do not duplicate.'},
    'willow2014': {'direct':'E19 email SENT/verified this turn to registered Will, explicitly asking whether willow2014 is the account. Await alias/result reply; do not duplicate.'},
}
labels = {
 '1c1jp5dhwy':'a rank-23 matrix-multiplication run with support 139',
 'aaronatlan':'your Grothendieck witness run',
 'advaith-appajodu':'your matrix-multiplication work',
 'alee792':'your earlier 90-triangle, 18-line Kobon run',
 'ashleychenyj':'your earlier 93-triangle, 18-line Kobon run',
 'claudiagaes':'your 93-triangle, 18-line Kobon run',
 'claudioolmedo':'your earlier 93-triangle, 18-line Kobon run',
 'cloud-post-code':'your 178,727-step Busy Beaver run',
 'connorbuchheit':'your earlier rank-23 matrix-multiplication run',
 'danamouk':'the danamouk Ramsey run improving on the frozen reference',
 'ebaenamar':'your Grothendieck witness run',
 'extraton618':'your 232,746-step Busy Beaver run',
 'eychcue':'your earlier 249,881-step Busy Beaver run',
 'felixisaac':'your earlier Collatz modular-descent run',
 'fkaita':'your earlier 93-triangle, 18-line Kobon run',
 'flaviabeppler':'your 93-triangle, 18-line Kobon run',
 'frido22':'your 249,614-step Busy Beaver run',
 'hl728':'your Ramsey validation and held-out improvements',
 'kevinsrun':'your possible 93-triangle Kobon entry',
 'luizfelipebarbosa':'your earlier 91-triangle, 18-line Kobon run',
 'n0rang2':'your Ramsey improvement and 249,881-step Busy Beaver run',
 'octavianboji':'your 468-triangle, 39-line Kobon run',
 'rohith18p':'your exact Kobon repository and 470-triangle, 39-line result',
 'sasap91':'your 228,641-step, 647-one Busy Beaver run',
 'shaff622':'your updated Ramsey hill result',
 'solal24':'your Kobon and Grothendieck witness runs',
 'thomasoh0408':'your 93-triangle, 18-line Kobon run',
 'vyahhi':'your 572,171-step held-out Busy Beaver run',
 'willow2014':'your possible 93-triangle Kobon entry',
 'wilsonwu-ai':'the wilsonwu-ai matrix-multiplication and Grothendieck runs',
 'yavol':'the earlier Ramsey, Collatz and Busy Beaver runs on yavol',
}
requirements = {
 'kobon-triangles':'exact line arrangements and triangle counts, checker/proof scope, final commit and reproduction steps',
 'busy-beaver-6-certificates':'exact transition tables, halting/trace certificates, final commit and reproduction steps',
 'clique-cluster-ramsey-multiplicity':'exact weighted graph, rational counts, blow-up argument, final commit and reproducible checker',
 'matrix-multiplication-tensor-3x3':'exact decomposition, all 729 tensor-identity checks, support/cost definitions and any Lean proofs',
 'grothendieck-constant-witnesses':'exact matrix/vector witness, certificate, checker and any new proof or formalization',
 'collatz-modular-descent':'exact descent rules, covered classes, proof/checker scope and reproducible certificates',
}
accounts = []
for a in old['accounts']:
    handle=a['account']; a['contact'].update(contact_updates.get(handle,{}))
    p=profiles[handle]
    a['contact_evidence_checked']=p['url']
    a['sources']=list(dict.fromkeys(a['sources']+[p['url']]+([a['contact']['source']] if a['contact'].get('source') else [])))
    if handle=='fkaita': a['public_name']='Kaita Furukawa'
    if handle=='yavol':
        a['identity_note'] += ' Hugging Face yavol names Yaroslav Volovich and links github.com/yavol; useful provisional human-name lead, no direct contact established. Do not equate with Yev Barkalov.'
        a['sources'].append('https://huggingface.co/yavol')
    target=a['public_name'] or handle
    if handle=='danamouk': target='Dana'
    if handle=='rohith18p': target='Rohith'
    if handle=='wilsonwu-ai': target='Wilson'
    first=f'Hi {target}, I saw {labels.get(handle,"your hill work")}; did you complete any OpenMath result, useful formalization or method you want judged? Please confirm your team/account.'
    if handle in ['hl728','n0rang2','rohith18p','vyahhi','octavianboji']:
        first=f'Hi {target}, I saw {labels[handle]}; please send the frozen packet for every result you want me to judge and confirm your final team.'
    if handle=='danamouk': first='Hi Dana, is danamouk your AutoLab account? Its Ramsey run improves on the frozen reference, and I would like to review the exact result and your final team.'
    if handle=='wilsonwu-ai': first='Hi Wilson, is wilsonwu-ai your AutoLab account? Did you complete matrix-multiplication/Grothendieck work, a useful formalization or another result you want judged?'
    hs=list(dict.fromkeys(x['hill'] for x in a['runs']))
    need='; '.join(requirements.get(h,'the exact claim, proof and reproducible artifact') for h in hs)
    second=f'Please share {need}, plus the paper and a short novelty/limitations note; useful partial results and formalizations are welcome.'
    third='Please confirm the final submission/reference and reviewer access, and flag any missing material or submission blocker so your work is not lost.'
    a['lines']=[first,second,third]
    a['outreach_status']='UNSENT — user review required'
    a['recommendation']='One short readiness enquiry is worthwhile to avoid losing a method, partial result or formalization; the visible benchmark alone does not settle novelty. '+a['recommendation']
    a['judging_readiness']='A hill score is visible, but a complete accessible final judging packet and receipt are not established.'
    a['contact_routes'] = []
    c=a['contact']
    if c.get('email'): a['contact_routes'].append({'channel':'Email','destination':c['email'],'status':'Published/registration-derived route; delivery untested unless an existing sent receipt is recorded','source':c.get('source',p['url'])})
    if c.get('linkedin'): a['contact_routes'].append({'channel':'LinkedIn','destination':c['linkedin'],'status':'Profile route; message availability not guaranteed. Use organizer relay if paid/blocked.','source':c.get('source',p['url'])})
    relay={'channel':'Organizer relay','destination':'Serge ([REDACTED CONTACT]) / Artem ([REDACTED CONTACT]), through their event/AutoLab account mapping','status':'Requires organizer forwarding or introduction; no direct account email invented','source':c['autolab']}
    a['contact_routes'].append(relay)
    a['preferred_contact']=(('Email: '+c['email']) if c.get('email') else ('LinkedIn: '+c['linkedin']) if c.get('linkedin') else 'Organizer relay needed; no direct email/DM verified')
    if handle in ['kevinsrun','willow2014']:
        entry='E23' if handle=='kevinsrun' else 'E19'
        receipt=next(x for x in sent if x['id']==entry)
        a['outreach_status']=f'Covered by {entry} SENT/verified; await alias reply. New draft below is contingency only.'
        a['recommendation']='Do not send a duplicate now; the registered candidate has already received a readiness/alias enquiry.'
        a['existing_contact_receipt']=receipt['message_id']
    elif handle=='shaff622':
        a['outreach_status']='Covered by E15 SENT/verified previously. New draft below is contingency only.'
        a['recommendation']='Do not repeat the group message. Retrieve the final reply/packet in the morning.'
    elif handle=='advaith-appajodu':
        a['outreach_status']='Consolidate with Chandragupt E04, already contacted; private team packet accessible. Separate entry/credit still needs confirmation.'
        a['recommendation']='Use Chandragupt’s existing conversation first; send this separate draft only if Advaith has a distinct result or missing contact.'
        a['lines']=['Hi Advaith, I am reviewing Chandragupt’s accessible matrix-multiplication packet; please confirm whether your hill run belongs to that team or a distinct entry.','If you have a separate result or formalization, please share its exact decomposition/checker, frozen repository, paper/novelty note and reproduction steps.','Please confirm your contribution/credits and any separate submission reference so I can judge it without duplicating the team’s work.']
        a['judging_readiness']='Related team packet now accessible; individual contribution and whether a separate entry exists remain unconfirmed.'
    elif handle in ['ottogin','sergeicu']:
        a['outreach_status']='Organizer/reference account. Draft for classification only; no automatic contestant reminder.'
        a['recommendation']='Clarify demonstration/reference versus actual entrant status and retain any reviewable formalizations; do not count organizer baselines as separate teams.'
        a['lines']=[f'Hi {"Artem" if handle=="ottogin" else "Serge"}, are the {handle} hill runs demonstration/reference work, or is any result intended as a competition entry?', 'For any result that should be reviewed, please identify its authors, event-window contribution, frozen artifacts/proofs and submission reference.', 'Please help map the remaining anonymous hill accounts to teams or forward their individual readiness enquiries so no useful result or formalization is missed.']
    a['sent']=False if handle not in ['shaff622'] else True
    a['new_draft_sent']=False
    a['rationale']='Preserve potential new mathematics, methods, partial results and formalizations even when a visible score ties or trails the benchmark. '+a['assessment']+' '+a['recommendation']
    assert len(a['lines'])==3
    accounts.append(a)

needs_relay=[a['account'] for a in accounts if not a['contact'].get('email') and not a['contact'].get('linkedin') and a['account'] not in ['sergeicu']]
relay_lines=[
 'Hi Serge and Artem, please map these AutoLab accounts to their final teams or forward the attached individual readiness drafts through your existing account contacts: '+', '.join(needs_relay)+'.',
 'Please ask for every finished or useful partial result/formalization, with frozen repository, exact claim/proof/certificate, paper/novelty note, reproduction steps and receipt; do not exclude benchmark ties solely by score.',
 'Please return one account-to-team/contact mapping and flag unregistered entrants, duplicate aliases and submission blockers so we can preserve and judge all the work.'
]
data={'updated':NOW,'status':'All 33 individual readiness drafts UNSENT. Existing E04/E15/E19/E23 outreach is preserved; do not duplicate those messages. Organizer classification/relay drafts also UNSENT.','coverage':'All 33 directly linked GitHub profiles read in the authenticated browser; published profile contact links and owner-linked personal sites checked. Additional selected portfolios and focused public searches reviewed. Gmail checked for inbound from new published addresses; no matching correspondence found. AutoLab profile exposes no direct-message action. Private platform account email directory not accessed.','accounts':accounts,'organizer_relay_draft':{'to':'[REDACTED CONTACT]','cc':'[REDACTED CONTACT]','lines':relay_lines,'sent':False,'accounts_needing_relay':needs_relay},'policy':{'team':'Leanification','allowed_contributors':5,'overall_score_multiplier':0.8,'formula':'adjusted_overall_score = 0.8 * raw_overall_score','raw_score':None,'adjusted_score':None,'owner':'User decision communicated to Luca/Ueverton and Serge/Artem','source':'OpenMath-organizer-unblock-and-exception-SENT.json'},'morning_collection':{'automation_id':'openmath-morning-submission-collection','when':'2026-10-03T06:21:00+02:00','one_run':True}}
save('OpenMath-33-account-contact-drafts-UNSENT.json',data)
save('OpenMath-additional-hill-account-assessment.json',{'updated':NOW,'scope':old['scope'],'accounts':accounts,'latest_review':'OpenMath-33-account-contact-drafts-UNSENT.html'})
lines=['OPENMATH — ALL 33 ACCOUNT CONTACT ROUTES AND READINESS DRAFTS',NOW,data['status'],'',data['coverage'],'','All scores need independent interpretation; benchmark ties may still carry a valuable formalization or method.']
for n,a in enumerate(accounts,1):
    lines += ['',f'{n:02d}. {a["account"]} — {a["public_name"] or "Human identity unconfirmed"}',a['outreach_status'],'Reach: '+a['preferred_contact'],'Alternatives: '+a['contact']['direct'],'Maturity/significance: '+a['assessment'],'Judging readiness: '+a['judging_readiness'],'Decision/rationale: '+a['recommendation'],'Draft (UNSENT):']+a['lines']+['Sources: '+'; '.join(a['sources'])]
lines += ['','ORGANIZER RELAY — UNSENT','To Serge; cc Artem']+relay_lines
(ROOT/'OpenMath-33-account-contact-drafts-UNSENT.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8')
e=html.escape
cards=[]
for n,a in enumerate(accounts,1):
    routes=''.join(f'<li>{e(x["channel"])}: {e(x["destination"])} — {e(x["status"])}</li>' for x in a['contact_routes'])
    source=' · '.join(f'<a href="{e(x)}">{e(x)}</a>' for x in a['sources'])
    cards.append(f'<article id="{e(a["account"])}"><h2>{n:02d}. {e(a["account"])} — {e(a["public_name"] or "identity unconfirmed")}</h2><p class="status">{e(a["outreach_status"])}</p><p><strong>Maturity and significance:</strong> {e(a["assessment"])}</p><p><strong>Ready to judge?</strong> {e(a["judging_readiness"])}</p><p><strong>Recommendation:</strong> {e(a["recommendation"])}</p><ul>{routes}</ul><p>{e(a["contact"]["direct"])}</p><div class="draft">'+''.join(f'<p>{e(x)}</p>' for x in a['lines'])+f'</div><details><summary>Evidence / sources</summary><p>{source}</p></details></article>')
doc='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>OpenMath — 33 account readiness drafts</title><style>body{font:16px/1.5 system-ui;max-width:1080px;margin:32px auto;padding:0 22px;background:#f7f8fb;color:#182438}article{background:white;border:1px solid #ccd5e1;border-radius:10px;padding:22px;margin:20px 0}h2{font-size:21px}.draft{background:#edf4ff;padding:12px 18px;border-left:4px solid #3568b8}.draft p{margin:8px 0}.status{font-weight:650;color:#634626}a{overflow-wrap:anywhere}li{margin:7px 0}</style><h1>All 33 accounts: contact routes and readiness drafts</h1><p>'+e(NOW)+'</p><p>'+e(data['status'])+'</p><p>'+e(data['coverage'])+'</p><p><strong>Review the high-priority accounts first, but keep all accounts in the collection register. A baseline score does not rule out a useful formalization, method or partial result.</strong></p>'+''.join(cards)+'<article><h2>Organizer relay — UNSENT</h2><p>To Serge; cc Artem. Individual account drafts above can be forwarded.</p><div class="draft">'+''.join('<p>'+e(x)+'</p>' for x in relay_lines)+'</div></article></html>'
(ROOT/'OpenMath-33-account-contact-drafts-UNSENT.html').write_text(doc,encoding='utf-8')
print(json.dumps({'accounts':len(accounts),'email_routes':sum(bool(a['contact'].get('email')) for a in accounts),'linkedin_routes':sum(bool(a['contact'].get('linkedin')) for a in accounts),'organizer_relay_needed':needs_relay,'new_drafts_sent':0,'report':'OpenMath-33-account-contact-drafts-UNSENT.html'},ensure_ascii=False))
