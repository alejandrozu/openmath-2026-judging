"""Local single-assessor review, exact proposed scoring and OPDP append. Never executes entrants."""
from pathlib import Path
import sys,json,math,decimal,datetime,collections,sqlite3,re,hashlib,zipfile,gzip
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging';OUT=ROOT/'review';OUT.mkdir(exist_ok=True)
for n in ['people','problems','entries']: (OUT/n).mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT));from library_core import connect,read_bytes,CATEGORIES
sys.stdout.reconfigure(encoding='utf-8');DB=connect(ROOT);Dec=decimal.Decimal
old=json.loads((ROOT/'judging/preliminary-assessment.json').read_text(encoding='utf-8'))
decisions=json.loads((ROOT.parent/'compact_review_decisions.json').read_text(encoding='utf-8'))
groups=json.loads((ROOT/'contestants.json').read_text(encoding='utf-8'));gm={g['group_id']:g for g in groups}
stamp=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=2))).isoformat(timespec='seconds')
rationales=json.loads((ROOT/'judging/Ulam_UnsolvedMath_ChatGPT_5.6_Sol_Ultra_Rationales_v1.0.json').read_text(encoding='utf-8'));published={r['problem_id']:r for r in rationales['records']}
weights=rationales['general_methodology']['component_weights_points']
def clamp(x):return max(0,min(1,x))
def cfsd(inp):
 h=.5 if inp['H'] is None else .8*(inp['H']-1)/8+.2*(inp['X']-1)/4
 z={'ai_relative_core':inp['AI']/10,'intrinsic_difficulty':inp['D']/10,'human_resistance':h,'inverse_tractability':.5 if inp['T'] is None else 1-inp['T']/10,'verification_burden':(inp['Vtrue']+inp['Vfalse'])/20,'formalization_burden':inp['F']/10,'prerequisite_load':.75*inp['P']/10+.25*(inp['B']-1)/4,'context_and_ambiguity':.5*inp['literature']/10+.2*inp['ambiguity']/10+.15*(inp['context']+1)/2+.15*(inp['horizon']+1)/2,'tool_constraint':1-inp['L']/10}
 z={k:clamp(v) for k,v in z.items()};linear=sum(z[k]*weights[k] for k in weights);return int(Dec(str(1000*(1-(1-linear/1000)**1.4))).quantize(Dec('1'),rounding=decimal.ROUND_HALF_EVEN)),z,linear
# AI adjustment,H,X,T,Vtrue,Vfalse,F,P,B,L,literature,ambiguity,context,horizon.
params={
 'RAMSEY-K4':[-.5,8,4,3,3,7,4,7,2,9,7,1,1,1],
 'MATRIX-3':[-1,7,4,5,2,7,4,6,2,9,6,2,0,0],
 'BB6':[0,9,5,0,8,10,5,7,2,8,8,1,1,1],
 'UNITARY':[0,7,4,4,6,5,6,7,3,7,7,2,1,1],
 'HEILBRONN9':[-.5,6,3,4,5,3,4,6,2,9,6,2,0,0],
 'CERNY':[-.5,8,4,3,6,2,4,6,2,8,7,1,1,1],
 'OEIS-A100475':[-1,4,2,6,3,2,5,5,2,8,4,1,0,0],
 'OEIS-A060957':[-1,3,2,6,3,2,5,5,2,9,4,1,0,0],
 'OEIS-A000224':[-.5,4,2,5,4,2,6,5,2,8,5,1,0,1],
 'LATIN-TABLEAU':[-.5,5,3,5,4,2,5,6,2,8,6,2,1,0],
 'OPDP13-QUARTIC':[0,5,3,4,5,3,6,7,3,7,7,2,1,1],
 'NO3-HALFTURN':[-1.5,3,2,8,1,1,2,3,1,8,3,1,0,0],
 'ERDOS21-VARIANT':[-.5,5,3,6,3,2,5,5,2,8,5,1,0,0],
 'RBM4-PARITY':[.5,5,3,4,6,4,7,7,3,6,7,2,1,1]
}
canonical={
 'RAMSEY-K4':'Determine c4, the limiting minimum fraction of monochromatic four-vertex cliques over all two-colourings of complete graphs. A strict new upper bound is partial progress.',
 'MATRIX-3':'Determine the minimum support (number of nonzero scalar entries across the three factor lists, under stated rational gauge conventions) among exact rank23 decompositions of the3x3 matrix multiplication tensor. Rank23 itself is known.',
 'UNITARY':'Determine the least worst-case number C(n) of CNOT gates needed to realize every n-qubit unitary exactly, with arbitrary one-qubit gates free. A rigorously uniform constructive upper bound is partial progress.',
 'OEIS-A000224':'For a(n) the number of square residues modulo n including zero, classify the n for which a(n)*(a(n)-1) divides n^2-1, under the exact upstream OEIS conjectured equivalence. The submitted p*q*r result is only an infinite subcase.',
 'LATIN-TABLEAU':'The pre-existing Latin-tableau and matching-rank realization family; determine the claimed colour/rank realization under the exact source hypotheses. The submitted factor-preservation hierarchy is a partial result, not a full Latin-tableau solution.',
 'ERDOS21-VARIANT':'For every finite intersecting r-uniform hypergraph J of maximum degree at most3, prove4*tau(J)<=|J|+r+3 and sharpness of the additive3. This exact question is asked in the July2026 source after its +4 lemma.',
 'NO3-HALFTURN':'Determine the least positive one-sided half-turn miss of a2n-point no-three-collinear subset of the n by n integer grid, uniformly in n, and supply a sharp witness. The pre-event source asks why the minimum known miss is4 instead of2.',
 'ERDOS1060':'Let f(n) count positive k with k*sigma(k)=n. Prove f(n)<=n^{o(1/log log n)}, or the stronger polylogarithmic bound. A smaller positive uniform exponent coefficient is partial progress.',
 'ERDOS829':'Bound the number of ordered nonnegative integer representations x^3+y^3=n by a fixed power of log n. A smaller constant in a subexponential bound is partial progress.',
 'ERDOS944':'The pre-existing critical-edge-set problem for vertex-critical four-chromatic finite simple graphs. Necessary finite order constraints are partial progress, not a complete graph-existence answer.'
}
canonical['HEILBRONN9']='Prove that every configuration of nine points in the triangle with vertices (0,0),(1,0),(0,1) has a triangle of area at most the claimed exact bound, using the submitted area normalization. The proposed numerical target is 0.027426211734693878; unresolved boundary/corner cases prevent a global conclusion.'
canonical['OEIS-A000224']='For every integer n>1, let a(n) count the square residues modulo n including zero. Prove that a(n)*(a(n)-1) divides n^2-1 exactly when n is an odd prime. The submitted n=p*q*r theorem excludes only the product of three distinct odd primes.'
canonical['LATIN-TABLEAU']='For every finite Young diagram, form a graph on its cells with adjacency for cells in a common row or column. Prove there is a proper coloring such that, for each positive k, the first k color classes occupy as many cells as the largest union of k independent sets. The factor-preservation hierarchy supplies only partial rank realization.'
parent_map={'OPDP13-QUARTIC':['OPDP row13: holomorphic squared-norm/exponent problem'], 'RBM4-PARITY':['OPDP row89: Boltzmann-machine likelihood landscape'], 'NO3-HALFTURN':['OPDP row43: no-three-in-line problem; pre-existing near-half-turn subquestion'], 'ERDOS21-VARIANT':['Erdos21: intersecting-hypergraph cover bound; pre-existing +3 residual question']}
def profile(k,f):
 existing=f.get('published_D_candidate');intr=f['intrinsic_opdp'];contextual=k.startswith(('M2-','CERNY-PART-'))
 values=params.get(k,[-.5,None,None,None, max(1,round(intr['score']*.7,1)),2,max(2,round(intr['factors']['technical_depth']*2,1)),max(3,round(intr['score']*.8,1)),2,8,4,1,0,0])
 names=['adjustment','H','X','T','Vtrue','Vfalse','F','P','B','L','literature','ambiguity','context','horizon'];inp=dict(zip(names,values));inp['D']=intr['score'];inp['AI']=max(0,min(10,inp['D']+inp.pop('adjustment')))
 if existing:
  pr=published.get(existing['problem_id']);value=int(existing['value']);calculation=pr['calculation_trace'] if pr else {'source':'published companion record'};inputs=pr['source_inputs'] if pr else inp;mode='Existing published CFSD1000 value, reused without rescaling or changing its frozen source profile.'
 else:
  value,normalized,linear=cfsd(inp);inputs=inp;calculation={'normalized_components':normalized,'weighted_points':{n:normalized[n]*weights[n] for n in weights},'linear_barrier':linear,'transform_exponent':1.4,'final_value':value};mode='New local OPDP extension with CFSD1000 formula; one editorial assessor, not the required three-assessor median.'
 rows=[r for r in old['results'] if r['family_id']==k];sources=[]
 for r in rows:
  ds=(r.get('evidence') or {}).get('dossier',{});sources+=ds.get('target',{}).get('source_urls',[]);sources+=ds.get('prior_art',{}).get('primary_urls',[])
 if k=='RAMSEY-K4':sources+=['https://arxiv.org/pdf/2206.04036','https://app.autolab.ai/hills/alejandrozu/clique-cluster-ramsey-multiplicity']
 if k=='ERDOS21-VARIANT':sources+=['https://arxiv.org/html/2606.24878v2']
 if k=='NO3-HALFTURN':sources+=['https://wwwhomes.uni-bielefeld.de/achim/no3in/symmetry_remarks.html']
 if k=='UNITARY':sources+=['https://arxiv.org/abs/2403.13692']
 if existing:sources+=['https://github.com/alejandrozu/ulam-opdp-difficulty-atlas']
 factors=intr['factors'];rationale=intr['rationale']
 axis_notes={
 'intrinsic':rationale,
 'AI':'Statement has '+('exact finite certificate feedback' if inp.get('L',0)>=8 else 'specialist analytic/formal dependencies')+'; the dated tool-assisted protocol is an estimate, not an empirical solve run.',
 'attention':'H/X are historical-effort/exposure priors, not contestant hours. '+('Insufficient documentation: neutral normalized .5 used for scoring.' if inp.get('H') is None else 'The chosen bands are single-assessor estimates; no labor total was observed.'),
 'tractability':'Known targets use N/A and neutral full-resolution component; otherwise the band is an editorial chance of useful100-hour partial progress, not full resolution.',
 'verification':'Positive checking uses the stated '+('exact finite data/proof chain' if inp.get('Vtrue',0)<=4 else 'specialist semantic or analytic argument')+'; a negative/global resolution can have a different burden. No fresh Lean build is claimed.',
 'formalization':'Statement encoding and libraries require '+str(inp.get('F','source'))+'/10 burden; this is the target burden, not the quality of a submitted proof.',
 'prerequisites':'The target needs its '+f['category']+' background; preparation and breadth refer to a prepared researcher, not entrant prestige.',
 'tools':'Higher L means favorable exact-feedback/search/prover leverage. It does not turn a leaderboard number into a theorem.',
 'status':'Known/source theorem' if contextual else 'Source-claimed pre-event open target or explicitly parent-linked variation; no independently certified verified_open status invented.'}
 return {'id':'OPENMATH-'+k,'family_id':k,'statement':canonical.get(k,f['target']),'category':f['category'],'status_gate':'known_formalization_target' if contextual else 'source_claimed_open_or_pending_admission','parent_links':list(dict.fromkeys(r['family_id'] for r in rows)),'D_0_1000_proposed':value,'D_origin':mode,'intrinsic_0_10':intr['score'],'intrinsic_factors':factors,'inputs':inputs,'calculation':calculation,'axis_rationales':axis_notes,'sources':list(dict.fromkeys(sources)),'catalogue_file_ids':sorted(set(x for r in rows for x in r['catalogue_file_ids'])),'assessor_count':1,'confidence':'C1 provisional source-grounded editorial assessment; no C3','published_reference':existing,'scale_binding_pending':True,'review_before_final':'Chair ratifies canonical scope; new D requires three independent assessments and median under handbook3.3; do not adjust difficulty to fit result.'}
profiles={k:profile(k,f) for k,f in old['families'].items()}
for k,p in profiles.items():
 p['parent_links']=parent_map.get(k,['CERNY'] if k.startswith('CERNY-PART-') else ['ERDOS3'] if k.startswith(('M2-E3-','M2-AP-CONCLUSION')) else [])
 p['version']='local-review-v2';p['registration_timestamp']=None;p['assessed_at']=stamp
 p['steward']='Alejandro / qualified domain review pending';p['domain']=p['category'];p['official_admission']='pending, not created by this local append'
 p['success_criterion']=p['statement'];p['formal_statement_locator']='Per-result exact source correspondence and selected endpoint recorded in entries/<resultID>.txt; source availability remains a separate acceptance gate.'
 p['exclusions']='No borrowed parent D for a variation; no points for duplicate corollaries, known mathematics as an open result, unproved assumptions, incomplete global certificate coverage, or a leaderboard number without a packet.'
 p['focus_status']='Unverified focus inclusion; conservative M3A/no bonus' if k=='RAMSEY-K4' else 'Proposal inherited from curated target mapping; frozen target binding pending chair verification.'
 p['version_history']=[{'at':stamp,'action':'Canonical scope, full CFSD1000 extension and source/assessor gates recorded locally; frozen Atlas unchanged.'}]
rs=[];file_links=collections.defaultdict(list)
chandra_source=(OUT/'chandra-independent-tensor-check.json').exists()
for prior in old['results']:
 r=dict(prior);o=decisions['result_overrides'].get(r['id'],{});r['previous_p']=r['p_scope_if_claim_valid'];r['previous_modality']=r['modality_proposal'];r['proposed_modality']=o.get('modality',r['modality_proposal']);r['proposed_p']=o.get('p',r['p_scope_if_claim_valid']);r['thoughts']=o.get('thoughts',r['progress_rationale']);r['novelty']=o.get('novelty')
 ds=(r.get('evidence') or {}).get('dossier',{})
 if r['novelty'] is None:
  comparisons=ds.get('prior_art',{}).get('comparison',[])
  if comparisons:r['novelty']=' '.join(comparisons)
  elif r['proposed_modality']=='M2':r['novelty']='Known mathematics; only a genuinely new, faithful, useful, reusable event-window formalization may count. Exact prior-library overlap is not yet independently cleared.'
  elif r['proposed_p'] in ['0',None]:r['novelty']='No eligible original mathematical delta established in the available packet. This is not a finding that all underlying work lacks novelty.'
  else:r['novelty']='Candidate scoped mathematical delta; exact baseline and independently sealed provenance are required. A missing gallery value is not evidence of a world record.'
 r['recommendation']=o.get('recommendation','Propose this exact scope and family once, subject to the stated source, formal, novelty and deadline checks.' if r['proposed_modality']!='NONE' else 'No score-bearing result identified; retain the record for missing-material or disposition review.')
 r['D_proposed']=profiles[r['family_id']]['D_0_1000_proposed'] if r['family_id'] else None
 if r['family_id']=='RAMSEY-K4' and r['proposed_modality']=='M1':
  r['focus_bonus_alternative']=True;r['proposed_modality']='M3A'
  r['recommendation']+=' Conservative b=1 until inclusion in the frozen focus set is verified; confirmed M1 would multiply these points by1.1.'
 r['proposed_b']='1.1' if r['proposed_modality']=='M1' else '1';r['proposed_m']='.5' if r['proposed_modality']=='M3B' else '1'
 r['proposed_points']=str(Dec(r['proposed_b'])*Dec(r['proposed_m'])*Dec(r['proposed_p'] or '0')*Dec(r['D_proposed'] or 0)**2/1000) if r['proposed_modality'] not in ['M2','NONE'] else None
 if r['team_id']=='E09':
  r['potential_points_if_proof_chain_accepted']=r['proposed_points'];r['potential_p_if_proof_chain_accepted']=r['proposed_p']
  r['proposed_p']='0';r['proposed_points']='0'
  r['recommendation']='Current formal-only proposal0. The README explicitly states no formal proof and unproved guarded geometric facts. Potential parent union17.8695(p=.05) only if the entire approved geometry-to-certificate chain is accepted; not one award per finite order.'
 if r['team_id']=='E04' and chandra_source:
  names={'E04-SUPPORT138':['solutions/support_138/solution.json','lean/MM3/Scheme138.lean','lean/MM3/Certificates.lean','lean/MM3/Brent.lean'], 'E04-GAUGE':['solutions/support_138_gauged/solution.json','kaggle/analysis/family_rational.json','lean/MM3/Scheme138Gauged.lean'], 'E04-CORE143':['solutions/core1809_support_143/solution.json','lean/MM3/Scheme143Core1809.lean']}
  for path in names.get(r['id'],[]):r['catalogue_file_ids']+=[x['id'] for x in DB.execute('select id from files where team_id=? and original_path=? and version=?',('E04',path,'479c2416b6261ee841052eef4881df0e40054f3f'))]
  r['formalization_and_correctness']='Complete pinned original repo retrieved and CRC/member hashes verified. Our exact checker confirms all729 tensor identities and support138/138/143, and matches every rational coefficient to its scaled Lean literal. Core-only finite certificate endpoints use decide, not native_decide; no fresh kernel build. Generic rational family identity independently checked outside s=0,-2; no supplied universal Lean family theorem. README scale-factor table has stale entries; actual source/data correspondence passes.'
  r['acceptance_gaps']=['Fresh pinned kernel closure and exact hill-statement binding','Freeze-time priority/independence, including midweek public baseline exposure','Final official intake/receipt and registered family/D confirmation','Generic symmetry/inequivalence/dimension/boundary optimality claims require separate proof; no global137 impossibility']
  if r['id']=='E04-SUPPORT138':
   r['thoughts']='The complete rational construction passes all729 independently checked tensor identities with23 product terms and138 nonzeros. It improves the located139-support benchmark by one; it does not reduce tensor rank or show a faster practical implementation. Its support pattern fails4 GF(2) tensor equations, so a literal sign-only scheme with this pattern is impossible. This gives a concrete method distinction beyond the leaderboard number.'
   r['novelty']='Promising new138-support construction; bounded independent primary search found only the authors earlier139 baseline page, not an earlier138 result. The claimed prior support139 benchmark and global inequivalence still need full historical comparison. Midweek public exposure matters for independence, not freeze-time known-math reclassification.'
   r['recommendation']='Propose P2=.05 and28.82968 after fresh closure, priority and intake. Source truncation is resolved; do not retain the old missing-tensor hold.'
  elif r['id']=='E04-GAUGE':
   r['thoughts']='The gauged138 tensor is exact and shares the family credit. An independent rational-polynomial check confirms the entire support138 family for rational s outside0,-2 and specialization s=-1 to the original. Numerical Jacobian dimension, global inequivalence, minimum12constant gauges and no137boundary claims are separate statements, not implied by the finite certificates or search failures.'
   r['novelty']='Potentially substantive structural analysis of the new construction. The family identity is now independently checked algebraically, but its general parameter theorem is not included in the supplied Lean certificate; no separate formal-only award.'
   r['proposed_p']='0';r['proposed_points']='0';r['recommendation']='Supporting structure in the same support family, no additional points. Exact gauged existence is included in the original construction union; generic structural claims await formalization.'
  else:r['thoughts']='The independent exact check confirms the distinct143-support construction and its scaled Lean literals. It does not improve the138/139support frontier. Claimed different-core inequivalence and local optimality are research assertions; numerical failed searches do not prove an absolute floor.'
 elif r['team_id']=='E04' and r['proposed_p']!='0':
  r['potential_points_if_proof_chain_accepted']=r['proposed_points'];r['potential_p_if_proof_chain_accepted']=r['proposed_p']
  r['proposed_p']='0';r['proposed_points']='0'
  r['recommendation']+=' Current payload hold0 because complete v/w data and exact proof packet are absent; potential family28.82968 once the originals validate.'
 if not r['catalogue_file_ids'] and ds:
  paths=[e.get('source_path','') for e in ds.get('formal_evidence',{}).get('endpoints',[])]+ds.get('formal_evidence',{}).get('logs_and_receipts',[])
  for p in paths:
   matches=DB.execute('select id from files where team_id=? and (original_path=? or original_path like ?) order by id limit 6',(r['team_id'],p,'%/'+p)).fetchall() if p else []
   r['catalogue_file_ids']+= [m['id'] for m in matches]
 # Attach concise role notes to key source files; every file also receives an indexed content/role summary.
 for fid in r['catalogue_file_ids']:file_links[fid].append(r['id'])
 rs.append(r)
# No mathematical credit from board-only records without a packet. Preserve proposed D context.
for r in rs:
 if not gm[r['team_id']]['has_review_material_or_manifests'] and r['proposed_modality'] not in ['NONE','M2']:
  r['proposed_p']='0';r['proposed_points']='0';r['recommendation']='Hold missing payload; current proposed points0. Board metadata cannot establish an eligible exact theorem.'
teams=[]
m2_recommend={'E02':10,'E06':1,'E08':10,'E10':1,'E11':3,'E17':0,'E65':2}
m2_holdnotes={'E08':'Ten substantive claimed families proposed; seven minor/sanity helpers held for usefulness/new-library delta; six explicitly unclaimed wrappers excluded.', 'E17':'Five groups: generic potential/research/layered framework(CORE1,2,6); anchor/count-window(CORE3,4); C3/C4 finite optimality(CORE5); Kari shrink/phase(CORE7,8); reflection finite-depth(CORE9). All held because original source is missing.', 'E65':'Two groups: dyadic extremal equivalence; AP interface/conditional analytic transfer. The conditional three-term bridge is not a separate proved analytic theorem.'}
for g in groups:
 tr=[r for r in rs if r['team_id']==g['group_id']];union={}
 for r in tr:
  if r['proposed_modality'] in ['M2','NONE'] or not r['selected_for_family_union']:continue
  k=r['family_id'];previous=union.get(k)
  if previous is None or Dec(r['proposed_points'] or 0)>Dec(previous['proposed_points'] or 0):union[k]=r
 # Additional records of the same mathematical family replace, never stack.
 positive=[r for r in union.values() if Dec(r['proposed_points'] or 0)>0];values=[Dec(r['proposed_points']) for r in positive];raw=sum(values,Dec(0));big=max(values,default=Dec(0));factor=Dec('.8') if g['group_id']=='E06' else Dec(1)
 oldt=next(t for t in old['teams'] if t['id']==g['group_id']);m2=m2_recommend.get(g['group_id'],0)
 t={'id':g['group_id'],'name':g['name'],'authors':g['authors'],'accounts':g['accounts'],'source_record_ids':g['source_record_ids'],'entrant_class':oldt['entrant_class'],'status':g['status'],'review_material':g['has_review_material_or_manifests'],'result_ids':[r['id'] for r in tr],'family_unions':[{'family_id':r['family_id'],'representative':r['id'],'D':r['D_proposed'],'b':r['proposed_b'],'m':r['proposed_m'],'p':r['proposed_p'],'points':r['proposed_points']} for r in positive],'raw_S':str(raw),'raw_A':str(big),'adjusted_S':str(raw*factor),'adjusted_A':str(big*factor),'M2_proposed_integer_count':m2,'M2_potential_upper':oldt['M2_potential_distinct_count_upper_bound'],'M2_adjusted_overall_value':str(Dec(m2)*factor),'exception_factor':str(factor),'M2_rationale':m2_holdnotes.get(g['group_id'],'One family per admitted source theorem or reusable formal target; supporting lemmas remain in its union.'),'official_scores_locked':False,'commit':g['immutable_commit'],'repo':g['repo'],'thoughts':decisions['team_notes'].get(g['group_id'],'No inspectable final mathematical packet. Preserve the identity/account and disposition; no score is inferred from registration or public-run metadata.'),'gaps':g['gaps'],'review_minutes':20 if g['group_id'] in ['E02','E08'] else (10 if g['has_review_material_or_manifests'] else 1)}
 if g['group_id']=='E09':t['thoughts']+=' Current proposal0 under formal-only rule; 17.8695 is a potential accepted-proof scenario, not current credit.'
 if g['group_id']=='E04':t['thoughts']='Complete pinned original now retrieved:1047files. All729 identities independently verified for138,gauged138 and143, with exact Lean-data correspondence; symbolic rational family checked too. Proposed28.82968 for one improved-support family. No minimum-rank, global137 exclusion or runtime improvement established. Fresh closure, prior/independence and official intake remain.' if chandra_source else t['thoughts']+' Current source hold0; 28.82968 is the potential accepted complete-packet family score.'
 if g['group_id']=='E17':t['M2_potential_grouped_count']=5;t['M2_rationale']+=' Current proposal0, potential5 after original source delivery and formal-novelty review.'
 teams.append(t)
for k,p in profiles.items():
 related=[r for r in rs if r['family_id']==k];contributors=list(dict.fromkeys(r['team_id'] for r in related));best=sorted([r for r in related if r['proposed_points'] and Dec(r['proposed_points'])>0],key=lambda r:Dec(r['proposed_points']),reverse=True)
 p.update(result_ids=[r['id'] for r in related],contributors=contributors,collective_frontier_representative=best[0]['id'] if best else None,collective_frontier_points_once=best[0]['proposed_points'] if best else'0',collective_rule='Same result/family counted once scientifically; independently sealed entrant contributions may each score after review. No sum across duplicates or automatic synergy bonus.')
people=[]
for t in teams:
 names=t['authors'] or [t['name']]
 for name in names:
  people.append({'person_id':t['id']+'-'+str(len(people)+1),'display_name':name,'entrant_id':t['id'],'entry_name':t['name'],'shared_result_ids':t['result_ids'],'score_reference':t['id'],'individual_contribution_map':'No per-author theorem/work allocation supplied; shared packet attribution only. Do not invent an individual point split.','profile':t['thoughts']})
report={'generated_at':stamp,'purpose':'One-day single-chair review preparation; numerical proposals, not final awards','scope':{'groups':len(teams),'source_identities':74,'results':len(rs),'problems':len(profiles),'person_profile_rows':len(people),'files':DB.execute('select count(*) from files').fetchone()[0]},'rules':old['handbook'],'difficulty_method':rationales['general_methodology'],'score_status':'All numerical values are explicit proposals using existing frozen companion values or new local CFSD1000 profiles. Canonical D/admission, required independent assessors, proof/fidelity and eligibility still require sign-off. No official record altered.','classification_changes':['Half-turn sharp near-symmetry target proposed M3A because pre-event source asks it; M3B alternate remains visible.','ErdosLovasz+3 residual target proposed M3A because pre-event paper explicitly asks it; no parent O(r) credit.','Matt synthesis and Jamie conditional Kobon proposed p0 under formal-only rule.','Board-only exact packets absent: p0 hold, not mathematical rejection.'],'teams':teams,'people':people,'problems':profiles,'results':rs,'synergies':old['synergies'],'file_result_links':{str(k):v for k,v in file_links.items()},'review_budget':{'entry_minutes':sum(t['review_minutes'] for t in teams),'problem_frontier_minutes':60,'decision_and_reconciliation_minutes':45,'breaks_and_margin_minutes':45,'interpretation':'About one six-hour review day for chair triage/proposed-value approval, not completion of all independent proof/literature checks.'},'limitations':['No fresh Lean kernel build or execution of entrant code. Supplied PASS receipts remain internal evidence.','Original Qichao27MBsource absent; Chandra v/w tensor captures incomplete; final unexposed/private material missing.','No second judge or three-assessor difficulty median simulated.','No individual point allocation inside team/company entries.','No automatic publication/authorship decision or significance bonus.']}
if chandra_source:report['limitations'][1]='Original Qichao27MBsource absent; final unexposed/private material missing. Chandra old truncated-source hold resolved by authenticated pinned snapshot and independent tensor/family checks.'
(OUT/'review-data.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
(OUT/'OPDP-local-append.json').write_text(json.dumps({'schema':'openmath.opdp.local-review-append.v1','created_at':stamp,'base_atlas_unchanged':True,'local_only':True,'records':list(profiles.values()),'required_median_not_satisfied':True},ensure_ascii=False,indent=2),encoding='utf-8')
def file_title(fid):
 row=DB.execute('select original_path from files where id=?',(fid,)).fetchone();return row['original_path'] if row else 'unavailable'
def entry_text(r):
 p=profiles.get(r['family_id']);parts=[r['id']+' | '+r['title'],'Exact contribution: '+r['exact_claim'],'Assessment: '+r['thoughts'],'Novelty: '+r['novelty'],'Formalization: '+r['formalization_and_correctness'],'Proposal: '+r['recommendation']]
 if p:parts+=['OPDP target '+p['id']+' | intrinsic '+str(p['intrinsic_0_10'])+'/10 | competition D proposal '+str(p['D_0_1000_proposed'])+'/1000', 'Modality '+r['proposed_modality']+' | p '+str(r['proposed_p'])+' | b '+r['proposed_b']+' | m '+r['proposed_m']+' | numerical family points '+str(r['proposed_points'] if r['proposed_points'] is not None else 'M2 separate family count')]
 parts+=['Specific remaining checks: '+'; '.join(r['acceptance_gaps']),'Key files: '+'; '.join(str(fid)+' '+file_title(fid) for fid in r['catalogue_file_ids'])]
 if p:parts+=['Primary/source locators: '+'; '.join(p['sources'])]
 return '\n\n'.join(parts)
for r in rs:(OUT/'entries'/(r['id']+'.txt')).write_text(entry_text(r),encoding='utf-8')
for t in teams:
 text=t['id']+' '+t['name']+'\n\n'+t['thoughts']+'\n\nProposed raw S='+t['raw_S']+'; A='+t['raw_A']+'; M2='+str(t['M2_proposed_integer_count'])+'; adjusted S='+t['adjusted_S']+'; adjusted A='+t['adjusted_A']+'; adjusted M2 ranking value='+t['M2_adjusted_overall_value']+'\nShared authors: '+', '.join(t['authors'])+'\n'+t['M2_rationale']+'\n\n'+'\n\n'.join(entry_text(r) for r in rs if r['team_id']==t['id'])
 (OUT/'people'/(t['id']+'.txt')).write_text(text,encoding='utf-8')
for k,p in profiles.items():
 text=p['id']+'\n\nCanonical scope: '+p['statement']+'\n\nD='+str(p['D_0_1000_proposed'])+'; intrinsic='+str(p['intrinsic_0_10'])+'/10\n'+p['D_origin']+'\n\n'+p['collective_rule']+'\nCollective proposed frontier representative: '+str(p['collective_frontier_representative'])+'\n\n'+'\n\n'.join(entry_text(r) for r in rs if r['family_id']==k)
 (OUT/'problems'/(k+'.txt')).write_text(text,encoding='utf-8')
print(json.dumps({'scope':report['scope'],'budget':report['review_budget'],'new_D_profiles':sum(not x['published_reference'] for x in profiles.values())},ensure_ascii=False))
for t in teams:
 if t['review_material']:print(t['id'],'S',t['raw_S'],'A',t['raw_A'],'M2',t['M2_proposed_integer_count'])
