from pathlib import Path
import json,datetime,sqlite3,csv,re
BASE=Path(__file__).resolve().parent;ROOT=BASE/'OpenMath-Judging';OUT=ROOT/'review';stamp=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
d=json.loads((OUT/'review-data.json').read_text(encoding='utf8'));validation=json.loads((OUT/'review-validation.json').read_text(encoding='utf8'));c=sqlite3.connect(ROOT/'catalogue.sqlite');c.row_factory=sqlite3.Row
# Current collection metadata changes preserve original historical source reports.
groups=json.loads((ROOT/'contestants.json').read_text(encoding='utf8'));g=next(x for x in groups if x['group_id']=='E04')
g['source_access_update']={'at':stamp,'resolved':True,'commit':'479c2416b6261ee841052eef4881df0e40054f3f','source_index':str(OUT/'chandra-original-source-index.json'),'independent_checks':[str(OUT/'chandra-independent-tensor-check.json'),str(OUT/'chandra-independent-family-check.json')]}
g['status']='Complete pinned original source collected; exact tensors and rational family independently checked. Fresh kernel closure, priority/independence and official intake pending.'
g['gaps']=['Fresh pinned kernel closure and exact hill-target correspondence','Official intake/final receipt, freeze-time novelty and independent provenance','Unformalized generic structural and boundary-minimality assertions']
(ROOT/'contestants.json').write_text(json.dumps(groups,ensure_ascii=False,indent=2),encoding='utf8')
teamfile=ROOT/'contestants/E04/TEAM.json';tm=json.loads(teamfile.read_text(encoding='utf8'));tm['source_access_update']=g['source_access_update'];tm['current_status']=g['status'];teamfile.write_text(json.dumps(tm,ensure_ascii=False,indent=2),encoding='utf8')
(ROOT/'contestants/E04/MISSING-MATERIALS.txt').write_text('UPDATED '+stamp+'\nOriginal tensor/source hold RESOLVED: complete pinned1047file repository fetched via authenticated GitHub. All729identities and scaled Lean data checked for138/138/143; rational family also checked.\nRemaining: fresh pinned kernel closure, exact prior/independence and official intake. Generic structural/dimension/boundary claims are separate.\nSource: '+str(OUT/'chandra-original-source-index.json'),encoding='utf8')
for cat in set(r['category'] for r in c.execute('select category from files where team_id="E04"')):
 rows=c.execute('select * from files where team_id=? and category=? order by original_path,id',('E04',cat)).fetchall();folder=ROOT/'contestants/E04'/cat;folder.mkdir(parents=True,exist_ok=True)
 with (folder/'FILE-INDEX.csv').open('w',newline='',encoding='utf-8-sig') as f:
  w=csv.writer(f);w.writerow(rows[0].keys());w.writerows(tuple(r) for r in rows)
# Refresh linked assessments in older summaries while retaining all source bytes.
rs={r['id']:r for r in d['results']}
for fid,ids in d['file_result_links'].items():
 row=c.execute('select summary from file_reviews where file_id=?',(int(fid),)).fetchone()
 if row:
  old=row['summary'].split(' Linked assessment:')[0];suffix=' Linked assessment: '+'; '.join(rid+': '+rs[rid]['thoughts'][:260] for rid in ids[:3])
  c.execute('update file_reviews set summary=?,result_ids=? where file_id=?',(old+suffix,json.dumps(ids),int(fid)))
current=next(t for t in d['teams'] if t['id']=='E04');overview=(OUT/'people/E04.txt').read_text(encoding='utf8');c.execute('update teams set overview=?,status=? where id=?',(overview,g['status'],'E04'));c.commit()
counts={'source_contact_accounts':74,'grouped_contestant_contact_records':70,'provisional_potential_entrant_units':60,'official_team_count':None,'files':c.execute('select count(*) from files').fetchone()[0],'archive_members':c.execute("select count(*) from files where archive_path is not null and archive_path!=''").fetchone()[0],'archive_count':c.execute("select count(distinct archive_path) from files where archive_path is not null and archive_path!=''").fetchone()[0]}
state={'updated_at':stamp,'status':'COMPACT_PRELIMINARY_ANALYSIS_READY_FOR_CHAIR_REVIEW','pdf':str(OUT/'OpenMath-compact-review.pdf'),'editable_text':str(OUT/'OpenMath-compact-review.txt'),'structured_data':str(OUT/'review-data.json'),'OPDP_append':str(OUT/'OPDP-local-append.json'),'score_signoff':str(OUT/'score-signoff.csv'),'contribution_signoff':str(OUT/'contribution-signoff.csv'),'validation':str(OUT/'review-validation.json'),'scope':d['scope'],'pages':validation['pages'],'review_minutes':357,'new_local_D_profiles':61,'published_D_profiles_reused':9,'native_tabs':['Person / entry review','Problem profiles','Proposed scores','Classified files','Review notes'],'completed_analysis':'Every collected contribution has precise claim, assessment, novelty/formal evidence, proposed number or explicit0hold, OPDP scope and cross-family map. All indexed files summarized statically.','scores':'Proposals; not final awards. S/A family-deduplicated; M2 separate; Leanification raw1 versus adjusted overall0.8.','owners':{'chair':'Alejandro reviews scopes, bands, novelty and proposed scores','organizers':'Final intake/receipt/frozen focus/cutoff policy','qualified_reviewers':'Fresh proof/fidelity review, two-judge progress, three-assessor new Dmedian','authors':'Undelivered original payloads such as Qichao source'},'dependencies':d['limitations'],'Chandra_resolved':g['source_access_update'],'no_outbound_messages':True,'no_contestant_code_executed':True,'unrelated_obligations_changed':False}
(BASE/'outputs/OpenMath-compact-review-current.json').write_text(json.dumps(state,ensure_ascii=False,indent=2),encoding='utf8')
for name in ['obligations-current-data.json','OpenMath-team-status.json']:
 path=BASE/'outputs'/name;record=json.loads(path.read_text(encoding='utf-8-sig'));record['reviewed']=stamp;record['current_compact_judging_review']=state
 if isinstance(record.get('judging_library'),dict):
  lib=record['judging_library'];lib['updated_at']=stamp;lib['counts']=counts;lib['exception']='Leanification five contributors user-approved: rawM2=1, adjusted overall ranking value0.8; proposed, no organizer acknowledgement invented';lib['limits']=[x for x in lib.get('limits',[]) if 'Chandragupt original' not in x];lib['compact_review']=str(OUT/'OpenMath-compact-review.pdf')
 for t in record.get('teams',[]):
  if t.get('record_id')=='E04':t.update(materials='Complete pinned original1047file source available; exact independent tensor/family checks passed',missing=g['gaps'],current_preliminary_score='S=A28.82968, M2=0, pending formal/novelty/intake approval',original_source_index=str(OUT/'chandra-original-source-index.json'))
 record.setdefault('latest_user_decisions',[])
 if isinstance(record['latest_user_decisions'],list):record['latest_user_decisions'].append({'at':stamp,'request':'Short person and problem review profiles; complete preliminary scoring using OPDP for every attempted target; one-day chair review.','result':state['status'],'source':state['pdf']})
 path.write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf8')
start='''OPENMATH JUDGING — LOCAL PERSON / PROBLEM REVIEW
Updated {stamp}

Open the Desktop “OpenMath Judging” shortcut for the native app.
Start with review/OpenMath-compact-review.pdf:30pages, about357minutes of chair review including breaks.
Person / entry review: select any of80named/account profiles, sharing their entrant packet where work allocation is unknown.
Problem profiles:70canonical targets with every original and supporting contribution, exact scope, OPDP inputs, scientific frontier and paper ideas.
Proposed scores:70records,226result rows, family-deduplicated S/A and separate M2. All values are proposals, not awards.
Classified files: all{files:,}file entries have static content/role summaries and original-byte access. Every received original archive remains local.
Review notes: private editable notes saved locally; existing notes preserved.
Score signoff: review/score-signoff.csv and review/contribution-signoff.csv.
Full result notes: review/entries/<ID>.txt; full problem/OPDP notes: review/problems/<family>.txt.
No website, server or personal-obligation information in the app.

CURRENT HOLDS
Qichao27MBsource was never attached. Missing graphs/private hill payloads remain missing.
Chandra previous truncated-capture hold is RESOLVED: full pinned1047file source now collected; all729tensor identities and scaled Lean data checked, rational family checked independently.
No fresh Lean builds, final receipt/eligibility decision, exact priority clearance or required independent Dmedian is claimed.
Raj geometry transfer incomplete; Matt universal synthesis unproved; Heilbronn global cover incomplete. Current proposals0; partial work preserved.
Sakana on-time PDF and late ZIP remain separate; organizers/chair decide fixed-before-cutoff transfer.
Five-person Leanification exception: rawM2 family count1, adjusted overall ranking value0.8. No unsupported organizer acknowledgement.

Historical first-pass reports remain under judging/. The review/ files and first three native tabs carry the current proposals.
No contestant programs were executed, no messages sent, no awards/submissions/publications modified.
'''.format(stamp=stamp,files=counts['files'])
(ROOT/'START-HERE.txt').write_text(start,encoding='utf8')
# New source index extends, rather than silently rewrites, the original collection index.
source={'at':stamp,'original_collection_index':str(ROOT/'source-index.json'),'prior_integrity':str(ROOT/'preservation-verification.json'),'new_pinned_original':str(OUT/'chandra-original-source-index.json'),'mathematical_checks':[str(OUT/'chandra-independent-tensor-check.json'),str(OUT/'chandra-independent-family-check.json')],'all_file_summary_coverage':str(OUT/'file-summary-coverage.json'),'new_OPDP_analysis':str(OUT/'OPDP-local-append.json'),'primary_sources':sorted({u for p in d['problems'].values() for u in p['sources']}),'final_targeted_mail_refresh':'All-folder query Oct2+ Qichao/Chandragupt/support138 found existing four manifests only; no newly delivered ZIP. No outbound action.'}
(OUT/'source-index.json').write_text(json.dumps(source,ensure_ascii=False,indent=2),encoding='utf8')
desktop=Path('[LOCAL PRIVATE OBLIGATIONS RECORD]');text=desktop.read_text(encoding='utf-8-sig');text=re.sub(r'^Last updated:.*$', 'Last updated: '+stamp+' (Europe/Paris)',text,count=1,flags=re.M)
text=text.replace('User pauses OpenMath to check urgent commitments before continuing judging.','Urgent commitments checked at13:11; user has resumed OpenMath judging. Attendance and other statuses below remain unchanged.',1)
text=text.replace('CURRENT PRELIMINARY OPENMATH JUDGING —','PREVIOUS PRELIMINARY OPENMATH JUDGING —',1).replace('CURRENT OPENMATH JUDGING WORKSPACE —','PREVIOUS OPENMATH COLLECTION WORKSPACE —',1)
block='''CURRENT COMPACT OPENMATH REVIEW — {stamp}
User requests much shorter individual/person and problem profiles, completed preliminary contributions, scores and OPDP analysis for every target, reviewable in one day.
DONE:30page compact review book;70grouped records/74source identities,226contribution rows,70OPDP problem profiles,80person/account profile rows. All353,195indexed files have static summaries;0read errors. Native app now has Person/entry review, Problem profiles, Proposed scores and per-file summaries; private notes preserved.
Book: {pdf}
Data/OPDP: {data}; {opdp}
Approval tables: {scores}; {contributions}
Validation: {validation}. Expected chair review357minutes including breaks; deep fresh builds/priority clearance still separate.
SCORING PROPOSALS: SakanaS1697.401122/A308.025/M2=10; HTPeoS88.2753/A49.4214/M2=10; ChandraS=A28.82968/M2=0; ChaewonS=A6.555824; JamieS=A6.555824/M2=1; RohithS=A3.5739; Leon/CameronM2=3; WilsonM2=2; LeanificationrawM2=1, adjustedoverall0.8. Other current open proposals0. Qichao currentM2=0, potential5coherentgroups only after source delivery.
CHANDRA SOURCE HOLD RESOLVED: authenticated pinned original479c2416... fetched,1047files plus archive indexed. All729identities for138/gauged138/143 independently verified, exact scaled Lean data matched; rational138family independently checked for finite rational s outside0,-2. Generic family/dimension/inequivalence/boundary claims not automatically formalized; READMEscale table stale entries recorded. Source: {chandra}
Exact half-turn and hypergraph+3 questions proposedM3A because pre-event sources ask them; M3B alternative halves their points. Ramsey conservativeb=1 until frozen focus inclusion verified. Rajformalgeometry incomplete, Mattuniversalbound unproved and Frederikglobalcover incomplete: current0, possible scientific partials retained. Family overlap does not stack, M2separate, no synergy bonus.
PENDING owners/dependencies: Alejandro approves scopes/bands/proposals; other qualified judges review proof/fidelity/novelty and required independent Dmedian; organizers resolve official intake/frozenfocus/cutoff, especially Sakana PDFvsZIP; entrants supply absent actualsource, notably Qichao27MBZIP and Luke/Madhan graph. No fresh Lean build, final award or organizer acknowledgement invented.
No outbound messages, contestantcode execution or external submission/award/billing/access changes. Unrelated DONE/SHELVED/IN PROCESS obligations preserved. Previous12:15 symbolic values and Chandra missing-tensor notes below are historical; use this block and review/ files now.

'''.format(stamp=stamp,pdf=state['pdf'],data=state['structured_data'],opdp=state['OPDP_append'],scores=state['score_signoff'],contributions=state['contribution_signoff'],validation=state['validation'],chandra=str(OUT/'chandra-original-source-index.json'))
text=re.sub(r'CURRENT COMPACT OPENMATH REVIEW.*?(?=CURRENT TIME-SENSITIVE OBLIGATIONS)','',text,count=1,flags=re.S)
pos=text.index('CURRENT TIME-SENSITIVE OBLIGATIONS');text=text[:pos]+block+text[pos:]
text=text.replace('LATEST USER DECISIONS\n','LATEST USER DECISIONS\n- '+stamp+': Short review book and complete numerical OPDP proposals requested; current compact review saved, source Chandra hold resolved, no sends/awards.\n',1)
history='\nDATED HISTORY — '+stamp+' — COMPACT REVIEW READY\nCompleted all collected preliminary contribution/person/problem profiles and numerical proposals; all353,195files summarized,61local full-method OPDP extensions,30pagePDF visually checked and consistency tests passed. Resolved Chandra original download through existing authenticated GitHub; independently checked three tensors and the generic rational family without running entrant code. Native app updated; unassigned final acceptance/newDmedian/priority gates explicit. Sources: '+state['pdf']+'; '+state['validation']+'; '+str(OUT/'chandra-independent-tensor-check.json')+'; '+str(OUT/'chandra-independent-family-check.json')+'\n'
desktop.write_text(text+history,encoding='utf8')
print(json.dumps({'updated':stamp,'counts':counts,'desktop_updated':True,'structured_continuity_updated':True,'review_pdf':state['pdf']}))
