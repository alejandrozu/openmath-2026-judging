from pathlib import Path
import json,re,html,sqlite3,collections
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,PageBreak,KeepTogether
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging';OUT=ROOT/'review';d=json.loads((OUT/'review-data.json').read_text(encoding='utf8'));rs={r['id']:r for r in d['results']}
pdfmetrics.registerFont(TTFont('Segoe','C:/Windows/Fonts/segoeui.ttf'));pdfmetrics.registerFont(TTFont('SegoeBold','C:/Windows/Fonts/segoeuib.ttf'))
pdfmetrics.registerFontFamily('Segoe',normal='Segoe',bold='SegoeBold',italic='Segoe',boldItalic='SegoeBold')
navy=colors.HexColor('#183148');teal=colors.HexColor('#126C70');grey=colors.HexColor('#586878');light=colors.HexColor('#EDF3F5')
styles={'title':ParagraphStyle('title',fontName='SegoeBold',fontSize=23,leading=28,textColor=navy,spaceAfter=13),'h1':ParagraphStyle('h1',fontName='SegoeBold',fontSize=16,leading=20,textColor=navy,spaceAfter=10),'h2':ParagraphStyle('h2',fontName='SegoeBold',fontSize=11,leading=15,textColor=teal,spaceBefore=8,spaceAfter=5),'p':ParagraphStyle('p',fontName='Segoe',fontSize=9,leading=12,spaceAfter=7),'small':ParagraphStyle('small',fontName='Segoe',fontSize=8,leading=10.6,spaceAfter=5),'head':ParagraphStyle('head',fontName='SegoeBold',fontSize=8,leading=10.5,textColor=colors.white)}
story=[];plain=[]
def short(s,n):
 s=re.sub(r'\s+',' ',str(s)).strip()
 return s if len(s)<=n else s[:n].rsplit(' ',1)[0]+'…'
def p(s,style='p',raw=False):return Paragraph(s if raw else html.escape(str(s)),styles[style])
def add(s,style='p'):story.append(p(s,style));plain.append(str(s)+'\n')
def table(rows,widths,header=True,padding=5):
 cells=[[p(x,'head' if header and i==0 else 'small') for x in row] for i,row in enumerate(rows)]
 t=Table(cells,colWidths=widths,repeatRows=1 if header else 0,hAlign='LEFT')
 commands=[('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),6),('RIGHTPADDING',(0,0),(-1,-1),6),('TOPPADDING',(0,0),(-1,-1),padding),('BOTTOMPADDING',(0,0),(-1,-1),padding),('LINEBELOW',(0,0),(-1,-1),.35,colors.HexColor('#D6E1E5'))]
 if header:commands += [('BACKGROUND',(0,0),(-1,0),navy),('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,light])]
 t.setStyle(TableStyle(commands));story.append(t);plain.extend(' | '.join(map(str,r))+'\n' for r in rows)
def page():story.append(PageBreak())
def score(r):
 if r['proposed_modality']=='M2':return 'M2: separate family count'
 if r['proposed_modality']=='NONE':return 'No eligible packet / 0'
 return f"{r['proposed_modality']} · D {r['D_proposed']} · p {r['proposed_p']} · {float(r['proposed_points'] or 0):.3f} points before family union"
add('OpenMath • Chair review book','title');add('3 October 2026 | Compact proposals and scientific frontier','h2')
add('Start here. Review each available packet, approve or hold its precise contribution, then reconcile the problem profiles. This book covers all70 grouped records /74 source identities and226 contribution rows. They are not70 verified registered teams. Shared authors receive one entrant score; personal point splits are not invented.')
add('Review plan: 207 minutes for entries,60 for problem frontiers,45 for decisions and45 for breaks:357 minutes. Sakana and HTPeo need about20 minutes each; other material-bearing entries about10; missing/withdrawn accounts about1. Deep independent proof rebuilding and literature clearance cannot all be completed in that time.')
add('Proposed tally — material-bearing entries','h2')
rows=[['Entry / authors','S','A','M2 / adjusted','Disposition']]
for t in d['teams']:
 if not t['review_material']:continue
 disp={'E04':'Tensor verified; closure/priority','E09':'No formal geometry proof; potential17.870','E17':'Source missing; potential5 M2','E12':'Global cover incomplete','E03':'Unproved universal bound','E02':'Late ZIP / priority / new D','E08':'Scoped closures / novel classes','E06':'Five-person exception ×0.8'}.get(t['id'],'Scoped novelty / closure checks')
 rows.append([t['id']+' '+short(t['name'],70),f"{float(t['adjusted_S']):.3f}",f"{float(t['adjusted_A']):.3f}",str(t['M2_proposed_integer_count'])+' / '+t['M2_adjusted_overall_value'],disp])
table(rows,[230,54,54,72,109]);add('S and A are original-result review proposals. M2 counts are separate, contingent on faithful reusable novelty. No awards or official acceptance have been recorded. All other roster records currently have0 original points and0 M2.', 'small')
page();add('How to approve these proposals','h1')
add('One family: F = b × m × p × D² /1000. S is the sum of distinct family unions; A is the largest. Frozen focus b=1.1; other original targets b=1; new substantive variations m=0.5. Ramsey uses conservative b=1 here until its frozen focus inclusion is verified; confirmed focus would change both Ramsey families from35.280 to38.808.')
add('Progress starts at the lower band endpoint: P0=0; P1=.01–.05; P2=.05–.15; P3=.15–.35; P4=.35–.60; P5=.60–.85; P6=.85–.95; complete exact target=1. No value strictly between.95 and1. A complete small subquestion can be p=1 with its own small D; a narrowed restatement does not turn a partial parent solution into a full solution.')
add('OPDP extends to every attempted problem. Nine existing published competition-scale profiles are retained;61 local profiles use the same CFSD1000 methodology. Intrinsic /10 is one input, not D/100. Every local profile records its canonical scope, parent, source, inputs, calculation and axis rationale. New D values are one-assessor proposals: the required three-assessor median and two-judge progress decision have not been fabricated.')
add('Formalization is assessed by reachable endpoint, statement fidelity, axioms and exact certificate coverage. Static source reading and supplied PASS receipts are identified as such. No contestant code was executed and no fresh Lean build is claimed. Unproved hypotheses, incomplete geometry transfer, missing vectors and uncovered boxes remain explicit holds.')
add('Approval decisions with the largest effect','h2')
decisions=[['Decision','Proposed treatment'],['Sakana delivery','PDF received05:57:20 CEST, before06:00 cutoff; ZIP06:19:17, after cutoff. Decide whether immutable already-finished sources and administrative transfer are acceptable; internal build dates are not independent submission receipts.'],['Half-turn and +3 hypergraph targets','Propose M3A: the exact questions predate the event. If classified M3B instead, subtract54.450 and154.0125 from Sakana respectively. Short proofs still require priority checks.'],['New D / focus list','Ratify source binding and canonical scope; get required independent D assessments. Ramsey bonus excluded until frozen-focus evidence is confirmed.'],['Known-math M2','Propose Sakana10, HTPeo10, Leon/Cameron3, Wilson2, Jamie1, Leanification1. HTPeo7 minor candidates held;6 wrappers excluded. Qichao0 current,5 potential groups with source missing.'],['Leanification','All5 contributors are permitted by Alejandro. Raw M2 count1; adjusted overall ranking value0.8. Keep raw and adjusted values separate; no organizer acknowledgement invented.'],['Missing/incomplete mathematical payloads','Chandra original-source hold resolved: full1047file snapshot and exact tensors/family checked, proposed28.82968 pending fresh closure/priority. Raj0 pending formal geometry transfer; Matt0 unproved universal synthesis; Heilbronn0 incomplete cover.'],['Independence / collective frontier','Sealed independent submissions may each earn entrant credit; the same scientific result is counted once. Similarity, equal score or public baseline exposure does not by itself prove copying.']]
table(decisions,[142,377]);add('Record decisions in score-signoff.csv and contribution-signoff.csv, or the local app’s saved Review notes. Full contribution notes: review/entries/<resultID>.txt. Full OPDP and problem analyses: review/problems/<family>.txt.', 'small')
active=[t for t in d['teams'] if t['review_material']]
for t in active:
 page();add(t['id']+' • '+t['name'],'h1');add('Shared authors: '+(', '.join(t['authors']) or 'Unresolved attribution'),'small')
 add('Proposed S '+f"{float(t['adjusted_S']):.3f}"+' | A '+f"{float(t['adjusted_A']):.3f}"+' | M2 '+str(t['M2_proposed_integer_count'])+' / adjusted '+t['M2_adjusted_overall_value']+' | '+str(t['review_minutes'])+' minutes','h2')
 add(t['thoughts']);add('Pinned commit: '+str(t['commit'])+' | Repo: '+str(t['repo']),'small')
 primary=[rs[x] for x in t['result_ids'] if rs[x]['proposed_modality'] not in ['M2','NONE']]
 if t['id']=='E57':
  add('All66 straight-line witnesses were independently recounted and match their submitted triangle counts. Forty-six catalogue entries are marked NEW by the author; missing gallery values are not established world records. n39=470 is superseded here by HTPeo471; n18=93 ties known mathematics. One P1 parent family, not66 awards. The generalized conjecture and unrealized pseudoline optima receive0.','p')
  pairs=[r for r in primary if r['id']!='E57-R4'];pairs.sort(key=lambda r:int(re.search(r'K(\d+)',r['id']).group(1)))
  rows=[['n : triangles','n : triangles','n : triangles','n : triangles']]
  for start in range(0,len(pairs),4):rows.append([short(r['title'],45)+(' •candidate' if r['proposed_p']!='0' else '') for r in pairs[start:start+4]]+['']*(4-len(pairs[start:start+4])))
  table(rows,[130,130,130,129]);add('Each witness has its own entries/E57-K<n>.txt assessment and file summary. Candidate labels are proposed novelty holds; all entries deduplicate to3.5739 parent points.','small')
 else:
  rows=[['Contribution / precise assessment','Novelty / formalization / proposed score']]
  for r in primary:
   left=r['id']+' • '+r['title']+'\n'+short(r['thoughts'],390)
   right='Novelty: '+short(r['novelty'],160)+'\nFormal: '+short(r['formalization_and_correctness'],180)+'\n'+score(r)
   if r.get('potential_points_if_proof_chain_accepted') not in [None,'0']:right+='\nPotential accepted chain: '+str(r['potential_points_if_proof_chain_accepted'])
   rows.append([left,right])
  if len(rows)>1:table(rows,[299,220])
 m2=[rs[x] for x in t['result_ids'] if rs[x]['proposed_modality']=='M2']
 if m2:
  add('Known-mathematics formalizations','h2');add(t['M2_rationale'],'small')
  rows=[['Result ID / target','Scope / review focus']]
  for r in m2:rows.append([r['id']+' • '+short(r['title'],110),short(r['exact_claim'],235)])
  table(rows,[260,259],padding=3)
 gaps=list(dict.fromkeys(g for x in t['result_ids'] for g in rs[x]['acceptance_gaps']))
 add('Sign-off focus: '+'; '.join(gaps[:5]),'small')
page();add('Problem-centered scientific frontier','h1');add('Read these as virtual problem entrants: all partial and complete contributions are assembled together, with the same family-union rule. Their numbers are analytical references, not extra awards. A complementary result does not automatically raise p; it must close an additional logical obstacle.')
for k in ['KOBON','COLLATZ','RAMSEY-K4','MATRIX-3','ERDOS3','ERDOS169','DMS','BB6','GROTHENDIECK','CERNY','HEILBRONN9','UNITARY']:
 n=d['problems'][k]['scientific_profile'];add(k+' • OPDP D '+str(d['problems'][k]['D_0_1000_proposed']),'h2')
 for label in ['frontier','interaction','collective','paper']:add(label.capitalize()+': '+n[label],'small')
add('Other original targets','h2')
for k in ['OEIS-A100475','OEIS-A060957','OEIS-A000224','LATIN-TABLEAU','OPDP13-QUARTIC','NO3-HALFTURN','ERDOS1060','ERDOS21-VARIANT','ERDOS944','RBM4-PARITY','ERDOS829']:
 profile=d['problems'][k];r=rs[profile['result_ids'][0]];add(k+' | '+score(r),'h2');add(short(r['thoughts'],390)+' Novelty: '+short(r['novelty'],180),'small');add('Publication relation: '+('A family paper can include its quantitative strengthening without extra family credit.' if k in ['OEIS-A060957','OPDP13-QUARTIC','RBM4-PARITY'] else 'Standalone scoped result or related-family chapter, contingent on exact prior comparison and formal closure.')+' Full scope/inputs/source analysis: problems/'+k+'.txt.','small')
page();add('Every other record retained','h1');add('These records currently have0 original points and0 M2. No final inspectable mathematical packet was available, or the account expressed interest/withdrew. This is not a finding that unexposed/private work is mathematically worthless. All source identities, aliases and individual result rows remain in the local library.')
rows=[['Entry / identity','Disposition / source status','Result IDs']]
for t in d['teams']:
 if t['review_material']:continue
 rows.append([t['id']+' '+short(t['name'],100),short(t['status'],170),', '.join(t['result_ids'])])
table(rows,[191,227,101])
page();add('OPDP scope and difficulty index','h1');add('Each of the70 records has a full problem profile, including the target even where the attempted result earns0. Known-theorem rows have contextual D only; M2 ranking uses accepted families. P=published value retained; L=local single-assessor extension. Full factors, inputs, provenance and calculation are in OPDP-local-append.json and problems/<family>.txt.')
rows=[['Family','D / intrinsic','Origin','Contributors / rows']]
for k,v in d['problems'].items():rows.append([k,str(v['D_0_1000_proposed'])+' / '+str(v['intrinsic_0_10']), 'P' if v['published_reference'] else 'L',', '.join(v['contributors'])+' / '+str(len(v['result_ids']))])
table(rows,[206,80,42,191],padding=2)
page();add('Sources, files and review boundaries','h1')
coverage=d['file_summary_coverage'];methods=coverage['methods'];add(f"File summary coverage:{coverage['summaries']:,} /{coverage['catalogue_files']:,};0 read errors. {methods['complete-small-file']:,} complete small-file reads,{methods['bounded-text-prefix']:,} bounded text prefixes,{methods['first-three-PDF-pages']} first-three-page PDF summaries and{methods['role-and-catalogue']} binary/role summaries. These are static summaries, not individually verified mathematical claims. Full original files remain in the local catalogue/archive library.")
add('Primary sources used for the significant comparisons','h2')
sources=[('Rules','Local EVENT/02-papers/competition_handbook_final.pdf, sections1,3–6.'),('Difficulty methodology','judging/Ulam_UnsolvedMath_ChatGPT_5.6_Sol_Ultra_Rationales_v1.0.json; frozen Atlas companion profiles and local append.'),('Ramsey prior','https://arxiv.org/pdf/2206.04036 — final McKay note, not just the headline bound.'),('Half-turn pre-event question','https://wwwhomes.uni-bielefeld.de/achim/no3in/symmetry_remarks.html — near-half-turn question before event.'),('Erdős–Lovász +3 question','https://arxiv.org/html/2606.24878v2 — explicit question after +4 lemma.'),('OEIS conjectures','https://oeis.org/A100475 and https://oeis.org/A060957; exact archived Formal Conjectures snapshots for A000224.'),('Uniform synthesis baseline','https://arxiv.org/abs/2403.13692 —22/48 coefficient; no proof of Matt21/48.'),('Erdős829 exact convention','Google DeepMind Formal Conjectures /ErdosProblems/829.lean, archived source correspondence.'),('Contestant evidence','Original archives, immutable commits, source messages, target correspondence, proof endpoints, supplied axiom/build receipts and independently written arithmetic/geometry checks. Per-file IDs in the226 entry notes.')]
table([[a,b] for a,b in sources],[150,369],False)
add('Unresolved review dependencies','h2');add('Missing Qichao original source ZIP; absent graphs for several hill-only accounts; no fresh full Lean builds; exact prior-formal-library novelty; eligibility and sealed independence; new difficulty median; Sakana late-source transfer decision. Chandra tensor truncation is resolved and all729identities and the symbolic family were independently checked. Every available contribution has a review disposition, numerical proposal and explicit remaining check.')
add('Local tools','h2');add('Desktop OpenMath Judging shortcut opens the native app. Person/entry review, Problem profiles and Proposed scores are the first tabs. Classified files shows each file’s summary and original content. Review notes save locally. Editable signoff tables are CSV; no email, LinkedIn message, submission, award, publication or access change was made.')
def footer(canvas,doc):
 canvas.saveState();canvas.setStrokeColor(colors.HexColor('#D6E1E5'));canvas.line(38,35,A4[0]-38,35);canvas.setFont('Segoe',8);canvas.setFillColor(grey);canvas.drawString(38,22,'OpenMath • Internal chair review • Proposals, not awards');canvas.drawRightString(A4[0]-38,22,str(doc.page));canvas.restoreState()
doc=SimpleDocTemplate(str(OUT/'OpenMath-compact-review.pdf'),pagesize=A4,rightMargin=38,leftMargin=38,topMargin=36,bottomMargin=47,title='OpenMath compact chair review',author='Internal judging review')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
(OUT/'OpenMath-compact-review.txt').write_text('\n'.join(plain),encoding='utf8')
from pypdf import PdfReader
print(json.dumps({'pdf':str(OUT/'OpenMath-compact-review.pdf'),'pages':len(PdfReader(OUT/'OpenMath-compact-review.pdf').pages)}))
