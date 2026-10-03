import pathlib,json,re,sys,hashlib
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT))
from library_core import connect,read_bytes
db=connect(ROOT);out=ROOT/'judging';d=json.loads((out/'preliminary-assessment.json').read_text(encoding='utf-8'))
r=db.execute('SELECT * FROM files WHERE id=349908').fetchone();raw=read_bytes(ROOT,r);s=raw.decode('utf-8')
def arr(name):return [int(x) for x in re.search(r'def '+name+r' : List [^:]+ := \[([^\]]+)\]',s).group(1).split(',')]
fac={k:arr('data_'+k) for k in ['u','v','w']};checks=[]
for pair in ['uv','uw','vw']:
 piv=arr('pivData_'+pair);L=arr('LData_'+pair);assert len(L)==529 and len(piv)==23
 M=[[fac[pair[0]][t*9+i//9]*fac[pair[1]][t*9+i%9] for t in range(23)] for i in piv]
 prod=[[sum(L[i*23+k]*M[k][j] for k in range(23)) for j in range(23)] for i in range(23)]
 passed=all(prod[i][j]==int(i==j) for i in range(23) for j in range(23));assert passed
 checks.append({'pair':pair,'inverse_product_equals_identity':passed,'rows_selected':piv,'full_tensor_leg_pair_shape':[81,23],'minor_shape':[23,23]})
matrix={'file_id':349908,'sha256':hashlib.sha256(raw).hexdigest(),'checks':checks,'meaning':'Independent exact integer left-inverse verification for the first retained known support139seed, three pair flattenings. Confirms full column rank at that seed, not whole nine-certificate bundle, Chandra tensor or global minimality. Source compiled alternative uses native_decide; kernel-only alternatives must be separately verified.'}
(out/'independent-matrix-rigidity-check.json').write_text(json.dumps(matrix,indent=2),encoding='utf-8')
row=next(r for r in d['results'] if r['id']=='E02-FOCUS-MATRIX');row['evidence']['independent_integer_check']=matrix
row['formalization_and_correctness']+=' Independent integer check confirms three 23×23 left-inverse products for the first seed. The compiled alternative file349908 explicitly uses native_decide, so that file is not itself a standard-axiom-only kernel proof. Final kernel alternatives and remaining seeds require endpoint-specific review.'
row['acceptance_gaps'].append('Distinguish native_decide compiled alternative from standard-axiom kernel certificate; verify exact selected closure and all nine pairs.')
# Attach text audit without treating unrelated imported stubs or metaprogram keywords as endpoint holes.
audit=json.loads((out/'static-formal-source-audit.json').read_text(encoding='utf-8'))
d['static_review']={'source_files_inspected':len(audit['files']),'by_team':{t:sum(x['team']==t for x in audit['files']) for t in sorted({x['team'] for x in audit['files']})},'source':'static-formal-source-audit.json','flag_interpretation':'Lexical scan only. Imported unfinished open statements, quoted syntax and answer(sorry) can appear without being proof dependencies. Reject only when an inadmissible axiom/hole reaches the selected endpoint. Native alternatives are distinct from kernel closure.'}
d['independent_arithmetic_review']={'source':'independent-certificate-checks.json','Kobon_arrangements_recounted':67,'HTPeo_n39':471,'Rohith_n39':470,'Collatz_rules_checked':769,'Collatz_overlap':'E05andE08exactlyequalcoverage;E10subset;combinedcoverageunchanged','matrix_source':'independent-matrix-rigidity-check.json'}
d['difficulty_warning']='The official frozen target-D register was not recovered. The atlas’s intrinsic OPDP difficulty is on a 0–10 scale and has not been rescaled. Published 0–1000 companion values are scenario candidates pending confirmation of the event’s scale and canonical targets, including duplicate and source-status issues. Unmatched official scores remain symbolic.'
d['review_findings']=[
 'HTPeo’s and Rohith’s exact n=39 triangle counts were confirmed independently: 471 and 470. These are lower bounds, not optimum claims.',
 'Rohith’s catalogue contains 66 arrangements. Its 46 NEW rows include n=39 / R1; they are not 46 additional families on top of R1. All computed counts matched.',
 'Chaewon’s 512 rules and HTPeo’s 234 rules cover exactly the same 1,765 odd residues modulo 4,096. Jamie’s 23-rule union lifts to 1,504 of those classes. Combining them adds no coverage.',
 'Leanification offers known Theorem B as one M2 family; supporting propositions and lemmas are not additional families. The user’s 0.8 exception is preserved separately.',
 'Leon earlier equivalence proof-body leaves the main goal sorry; separate Converse named equivalence is closed. Wilson answer(sorry) in a restated source proposition is not a proof admission.',
 'Sakana MatrixRigidityCompiled is explicitly a native_decide alternative; endpoint-specific kernel closure must be distinguished. Supplied imported formal-conjecture stubs cannot be judged by grep alone.',
 'Sakana has 27 claim dossiers, including complete OEIS refutation candidates. Late ZIP delivery, proof closure at cutoff, exact novelty and canonical difficulty remain independent checks.',
 'Raj’s claimed upper bounds of 94 generally and 93 in the triple-point scope need geometric soundness review. The open all-8/capacity case and 135 undecided cubes mean K(18)=93 is not established.',
 'Qichao’s scoped-core assessment uses manifests; the actual 27 MB source is absent. Chandra’s truncated captures prevent a full tensor check. Frederik’s global cover is incomplete.'
]
d['review_order']=[
 'Resolve cutoff, version and official intake questions before accepting results.',
 'Confirm canonical families, modalities and the competition difficulty scale.',
 'Review HTPeo’s formal Ramsey, Kobon and DMS endpoints, and Leanification’s closed Theorem B.',
 'Review all 27 Sakana families, starting with the two complete OEIS refutation claims. Confirm proof closure at cutoff.',
 'Check Raj’s upper-bound soundness and Jamie’s conditional predecessor lemmas.',
 'Compare Erdős formal bridges and the novelty of the three-term formalization against imported proofs.',
 'Approve exact-procedure certificates only within an explicitly recorded trust boundary.',
 'Keep partial and missing-packet records pending; do not silently drop them.'
]
categories={
 'OEIS-A100475':'Number theory / digit dynamics', 'OEIS-A060957':'Multiplicative combinatorics / subset products',
 'OEIS-A000224':'Number theory / quadratic residues', 'LATIN-TABLEAU':'Combinatorics / bipartite matching and Latin tableaux',
 'OPDP13-QUARTIC':'Real algebraic geometry / polynomial positivity', 'NO3-HALFTURN':'Discrete geometry / grid configurations',
 'M2-BERNOULLI':'Number theory / Bernoulli denominators', 'M2-QUATERNION':'Diophantine logic / quaternion algebra',
 'M2-LCM-RECURRENCE':'Number theory / arithmetic recurrences', 'M2-APERY':'Number theory / polynomial irreducibility',
 'M2-BASE3':'Digit combinatorics / reversal-add dynamics', 'M2-THETA':'Number theory / finite floor-sign sums',
 'M2-WOLSTENHOLME':'Number theory / p-adic valuations and congruences', 'M2-LCM-MATRIX':'Arithmetic linear algebra / LCM matrices',
 'M2-ERDOS887':'Analytic number theory / nearby divisors', 'M2-POLYGON':'Euclidean geometry / distance multiplicities',
 'ERDOS1060':'Analytic number theory / divisor-sum representation counts', 'ERDOS21-VARIANT':'Extremal combinatorics / hypergraph cover numbers',
 'ERDOS944':'Graph theory / critical edge sets', 'RBM4-PARITY':'Mathematical statistics / singular mixture and RBM geometry',
 'ERDOS829':'Analytic number theory / representations as sums of cubes', 'M2-G-PM':'Graph theory / perfect matchings',
 'M2-E942':'Number theory / powerful numbers and Diophantine approximation', 'M2-E44':'Additive combinatorics / Sidon sets',
 'M2-E123':'Additive number theory / complete multiplicative sets', 'M2-E918':'Infinite graph theory / chromatic cardinals',
 'M2-E292':'Number theory / arithmetic set closure', 'M2-E395':'Probability / reverse Littlewood–Offord inequalities',
 'M2-E698':'Number theory / binomial gcd inequalities', 'M2-E939':'Number theory / sums of powerful numbers',
 'M2-E477':'Additive number theory / polynomial ranges', 'M2-E295':'Number theory / Egyptian fractions',
 'M2-E703':'Extremal combinatorics / intersecting set families', 'M2-E748':'Additive combinatorics / sum-free sets',
 'M2-E1136':'Additive number theory / density and forbidden sums', 'M2-E358':'Number theory / consecutive sums and divisors',
 'M2-E619':'Graph theory / triangle-free supergraphs', 'M2-E1148':'Number theory / quadratic representations'
}
for key,category in categories.items():
 if key in d['families']:d['families'][key]['category']=category
for r in d['results']:
 if r['family_id'] in d['families']:r['problem_category']=d['families'][r['family_id']]['category']
# Improve compact diagnostic prose without modifying quoted source evidence, identifiers, Lean or paths.
replacements={
 'LateZIP':'Late ZIP ', 'versuson-timePDF':' versus on-time PDF ', 'provecutoff':'prove cutoff', 'cutofffixedsourceandproofclosure':' cutoff, fixed source and proof closure',
 'Freshindependentselectedendpointverification':'Fresh independent verification of the selected endpoint', 'NoveltystatusandfrozenfamilyD':'Novelty status and frozen family D',
 'fullparent':'full parent', 'fullno-three-in-line':'full no-three-in-line', 'Known/classification':'Known / classification', 'known/classificationunresolved':'known / classification unresolved',
 'three-term importedformalizationnovelty':'three-term imported formalization novelty', 'samefamily':'same family', 'all-n':'all-n',
 'Nooverlapstacking/nobonusinvented':'No overlapping scores stack; no bonus invented', 'families,especially':'families, especially',
 'sourceclosuredeadlineproofrequired':'source closure must be shown to exist at the deadline', 'upper-boundgeometricalsoundness':'upper-bound geometric soundness',
 'Jamieconditionalpredecessors':'Jamie’s conditional predecessor lemmas', 'exact-procedurecertificates':'exact-procedure certificates', 'recordedtrustscope':'recorded trust scope',
 'no-packet/partialcontacts':'contacts with partial or missing packets', 'canonicalfamily':'canonical family', 'densityformalization':'density formalization',
 'knownM2':'known M2', 'notErdős3':'not Erdős #3', 'standard-axiom-only':'standard-axiom-only',
 'Noexacttargettoassess':'No exact target to assess', 'CompetitionDunmatched':'Competition D unmatched', 'competitionDunmatched':'competition D unmatched',
 'published0–1000candidate':'published 0–1000 candidate', 'Noeligible':'No eligible', 'Global':'Global',
 'fullrecurrence':'full recurrence', 'Knownquaternion':'Known quaternion', 'Known denominator':'Known denominator',
 'self-contained':'self-contained', 'not H10(Q)solution':'not a solution of H10(Q)', 'one-parameter':'one-parameter',
 'Sharp miss0or≥4subquestion with5×5witness':'Sharp subquestion: zero or at least four missed points, with a 5×5 witness',
 'Knownfinite-step':'Known finite-step', 'One-step palindrome/nocarry':'One-step palindrome / no-carry', 'Knownhalf-sum':'Known half-sum',
 'Prime denominator statement and2/3valuations':'Prime denominator statement and valuations at 2 and 3',
 'not full composite/stronger Wolstenholme target':'not the full composite or stronger Wolstenholme target',
 'Evenregularpolygonmultiplicity bound; not generalconvex/Erdős94':'Even regular-polygon multiplicity bound; not general convex sets or Erdős #94',
 'uniformlimit':'uniform limit', 'polylog':'polylogarithmic', 'fullno-three':'full no-three',
 'Sharp specifiedmaxdegree3residual/peeling theorem':'Sharp specified residual / peeling theorem at maximum degree 3',
 'onlyif open/admitted':'only if open and admitted', 'parentO(r)already solved byKahn':'parent O(r) target already solved by Kahn',
 'Exactfour-visibleone-hiddennine-parameter fibre localmax/saddleclassification':'Exact local-maximum / saddle classification in the nine-parameter fibre with four visible and one hidden unit',
 'high-dimensionaltraining/generalOPDP89':'high-dimensional training or general OPDP89', 'leading constantforallsums ofcubes':'leading constant for all sums of cubes',
 'Earlierlog7/4version samefamily':'Earlier log(7)/4 version belongs to the same family',
 'Narrowfinitecounterexampletoauxiliarydiagonal-pullbackoptimality':'Narrow finite counterexample to auxiliary diagonal-pullback optimality',
 'Reconstructedbridge/cyclicupperproofdatesneed cutoffreview':'Reconstructed bridge / cyclic upper proof dates need cutoff review',
 'Restrictedsign-matrixestimateknown/classificationunresolved':'Restricted sign-matrix estimate: known status / classification unresolved',
 'demonstratednewarbitrary-realconstantbound':'demonstrated new bound for the arbitrary-real-coefficient constant',
 'PossibleM2formalizationonly':'Possible M2 formalization only',
 'Finiteone-legobstructionfor3knownseeds':'Finite one-leg obstruction for three known seeds', 'noglobalrank/supportimpossibility':'no global rank or support impossibility',
 'Exactsmallboundimprovement+genericlifting':'Exact small bound improvement plus generic lifting', 'onlyupperP1withrecord/noveltyjustification':'upper P1 only with record / novelty justification',
 'PublishedstrongerTechnionpriorunresolved':'Potential stronger Technion prior unresolved',
 'Finitehaltingwitness1235211/1519notglobalrecord':'Finite halting witness: 1,235,211 steps and 1,519 ones, no global record',
 'cannot awardoriginalglobalprogressforknown/subrecordmachine':'cannot award original global progress for a known or subrecord machine',
 'samefamily':'same family', 'uniononce':'union once', 'Noautomatic':'No automatic',
 'fullsquare-residue':'full square-residue', 'notconstant16orfullparentmaximality':'not constant 16 or full parent maximality',
 'oneleg':'one leg', 'allhypotheses':'all hypotheses', 'not historicalpriority':'not historical priority',
 'acceptedcountunawarded':'accepted count unawarded', 'Rawand.8adjustedseparate':'Raw and .8-adjusted scores separate'
}
def prose(v):
 if not isinstance(v,str):return v
 for a,b in replacements.items():v=v.replace(a,b)
 # Space between numeric parameters and ordinary words, preserving IDs inside evidence.
 for word in ['rules','classes','lines','steps','ones','span','modules','families','arrangements','rows','points','colours','declarations','copies','judges','primes','factors','witness','theorem']:
  v=re.sub(r'(\d)('+word+r')\b',r'\1 \2',v)
 return v
for r in d['results']:
 for key in ['progress_rationale','formalization_and_correctness','title']:r[key]=prose(r[key])
 r['acceptance_gaps']=[prose(x) for x in r['acceptance_gaps']]
for f in d['families'].values():f['intrinsic_opdp']['rationale']=prose(f['intrinsic_opdp']['rationale'])
for e in d['synergies']:
 for key in ['relationship','concrete_reuse','scope_limits']:e[key]=prose(e[key])
d['review_order']=[prose(x) for x in d['review_order']]
(out/'preliminary-assessment.json').write_text(json.dumps(d,ensure_ascii=False,indent=2),encoding='utf-8')
def rowtext(r):
 f=d['families'].get(r['family_id']);lines=[r['id']+' — '+r['title'],'1. Problem: '+r['problem_category'],r['exact_claim']]
 if f:lines+=['Difficulty: intrinsic OPDP '+str(f['intrinsic_opdp']['score'])+'/10; '+f['intrinsic_opdp']['rationale'],'Factor profile: '+str(f['intrinsic_opdp']['factors']),'Competition D: '+('published candidate '+str(f['published_D_candidate']['value'])+'; event binding unverified' if f['published_D_candidate'] else 'unmatched; keep symbolic')]
 lines+=['2. Improvement: '+r['progress_band']+'; proposed p='+str(r['p_scope_if_claim_valid']),r['progress_rationale'],'3. Formalization / correctness: '+r['formalization_and_correctness'],'Acceptance checks: '+'; '.join(r['acceptance_gaps']),'Conditional formula: '+str(r['conditional_score_formula'])+'; candidate points '+str(r['conditional_points_published_candidate']),'Source catalogue IDs: '+', '.join(map(str,r['catalogue_file_ids'])),'Official acceptance and score: UNAWARDED','']
 return '\n'.join(lines)
lines=['OPENMATH — PRELIMINARY JUDGING',d['generated_at'],'74 source identities / 70 grouped records / '+str(len(d['results']))+' result and disposition rows','SINGLE REVIEWER DRAFT. Logical scope and formal validity are separate. Missing submissions are N/A, not rejections.','Handbook: F=b*m*p*D²/1000; S=sum distinct families; A=max family. M2 is a separate count.',d['difficulty_warning'],'','INDEPENDENT CHECKS AND MAIN FINDINGS']+[prose(x) for x in d['review_findings']]+['']
for t in d['teams']:
 head=[t['id']+' '+t['name'],t['entrant_class'],'S (conditional): '+t['conditional_total_S_formula'],'A (conditional): '+t['conditional_A_formula'],'Priced candidate subtotal: S='+t['provisional_priced_S_subtotal']+'; A='+t['provisional_priced_A_subtotal']+'; unpriced families='+str(len(t['unpriced_families'])),'M2 possible family ceiling='+str(t['M2_potential_distinct_count_upper_bound'])+'; accepted count unawarded. A ceiling is not an endorsement of every trivial helper.','']
 if t.get('exception_note'):head.append(t['exception_note'])
 body='\n'.join(head+[rowtext(r) for r in d['results'] if r['team_id']==t['id']]);lines.append(body)
 folder=ROOT/'contestants'/t['id'];(folder/'PRELIMINARY-JUDGING.txt').write_text(body,encoding='utf-8')
lines+=['4. SYNERGY / OVERLAPS','']
for e in d['synergies']:lines+=['; '.join(e['teams'])+' — '+e['family'],e['relationship'],e['concrete_reuse'],'Limits: '+e['scope_limits'],'No jury bonus assigned.','']
(out/'PRELIMINARY-JUDGING.txt').write_text('\n'.join(lines),encoding='utf-8')
short=['OPENMATH — REVIEW QUEUE AND TALLY',d['generated_at'],'The native app has per-result assessment, all-entrant tally and synergy tabs.',d['difficulty_warning'],'','MAIN FINDINGS']+[prose(x) for x in d['review_findings']]+['','NEXT REVIEW ORDER']+[str(i+1)+'. '+s for i,s in enumerate(d['review_order'])]+['','TALLY BY ENTRANT (no final ranking)']
for t in d['teams']:short.append(t['id']+' '+t['name']+' | provisional priced S='+t['provisional_priced_S_subtotal']+' A='+t['provisional_priced_A_subtotal']+' | '+str(len(t['unpriced_families']))+' unpriced original families | M2 candidates ≤'+str(t['M2_potential_distinct_count_upper_bound'])+' | acceptance unawarded')
(out/'REVIEW-QUEUE-AND-TALLY.txt').write_text('\n'.join(short),encoding='utf-8')
print('Saved review, matrix certificate checks and reports; source scans',len(audit['files']))
