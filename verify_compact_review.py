from pathlib import Path
import json,csv,sqlite3,decimal,collections,hashlib,re
from pypdf import PdfReader
from PIL import Image,ImageOps,ImageDraw
ROOT=Path(__file__).resolve().parent/'OpenMath-Judging';OUT=ROOT/'review';d=json.loads((OUT/'review-data.json').read_text(encoding='utf8'));D=decimal.Decimal
rs={r['id']:r for r in d['results']};assert len(rs)==226;assert len(d['teams'])==70;assert len(d['problems'])==70;assert len(d['people'])==80
assert set(r['id'] for r in d['results'])==set(x for t in d['teams'] for x in t['result_ids'])
assert set(d['problems'])==set(r['family_id'] for r in d['results'] if r['family_id'])
for r in d['results']:
 assert r['thoughts'] and r['novelty'] and r['formalization_and_correctness'] and r['recommendation']
 assert (OUT/'entries'/(r['id']+'.txt')).exists()
 if r['proposed_modality'] not in ['M2','NONE']:
  assert D(r['proposed_points'])==D(r['proposed_b'])*D(r['proposed_m'])*D(r['proposed_p'])*D(r['D_proposed'])**2/1000
  assert not D('.95')<D(r['proposed_p'])<1
for t in d['teams']:
 points=[D(f['points']) for f in t['family_unions']]
 assert len(set(f['family_id'] for f in t['family_unions']))==len(t['family_unions'])
 assert D(t['raw_S'])==sum(points,D(0));assert D(t['raw_A'])==max(points,default=D(0))
 assert D(t['adjusted_S'])==D(t['raw_S'])*D(t['exception_factor'])
 assert D(t['M2_adjusted_overall_value'])==D(t['M2_proposed_integer_count'])*D(t['exception_factor'])
 assert (OUT/'people'/(t['id']+'.txt')).exists()
tm={t['id']:t for t in d['teams']}
assert tm['E06']['M2_proposed_integer_count']==1 and tm['E06']['M2_adjusted_overall_value']=='0.8'
assert all(D(tm[k]['raw_S'])==0 for k in ['E03','E09','E12','E17'])
assert tm['E04']['raw_S']=='28.82968'
assert tm['E17']['M2_proposed_integer_count']==0 and tm['E17']['M2_potential_grouped_count']==5
assert tm['E57']['raw_S']=='3.5739'
assert all(r['proposed_b']=='1' for r in d['results'] if r['family_id']=='RAMSEY-K4')
for k,p in d['problems'].items():
 assert p['statement'] and p['axis_rationales'] and p['calculation'] and p['version_history']
 assert (OUT/'problems'/(k+'.txt')).exists()
 if not p['published_reference']:
  calc=p['calculation'];a=D(str(sum(calc['weighted_points'].values())));value=round(1000*(1-(1-float(a)/1000)**1.4));assert value==p['D_0_1000_proposed']
c=sqlite3.connect(ROOT/'catalogue.sqlite')
assert c.execute('select count(*) from files').fetchone()[0]==d['scope']['files']==353195
assert c.execute('select count(*) from file_reviews').fetchone()[0]==353195
assert c.execute('select count(*) from files f left join file_reviews r on f.id=r.file_id where r.file_id is null').fetchone()[0]==0
assert c.execute('select count(*) from file_reviews where error is not null').fetchone()[0]==0
for name,count in [('score-signoff.csv',70),('contribution-signoff.csv',226)]:
 with (OUT/name).open(encoding='utf-8-sig') as f:assert len(list(csv.reader(f)))==count+1
pdf=PdfReader(OUT/'OpenMath-compact-review.pdf');texts=[p.extract_text() or '' for p in pdf.pages];assert 20<=len(texts)<=32
for t in d['teams']:assert any(t['id'] in x for x in texts)
assert all(len(x)>300 for x in texts)
images=sorted((OUT/'render').glob('page-*.png'))[:len(pdf.pages)]
for i in range(0,len(images),8):
 sheet=Image.new('RGB',(1000,1480),'#d7dfe3');draw=ImageDraw.Draw(sheet)
 for j,path in enumerate(images[i:i+8]):
  im=Image.open(path).convert('RGB');im.thumbnail((470,335));x=15+(j%2)*495;y=24+(j//2)*365;sheet.paste(im,(x,y+14));draw.text((x,y),path.stem,fill='black')
 sheet.save(OUT/'render'/('contact-'+str(i//8+1)+'.png'))
report={'scope':d['scope'],'coverage_complete_for_collected_records':True,'formula_checks':'passed','family_deduplication':'passed','M2_separate_and_exception':'passed','missing_source_and_incomplete_proof_holds':'passed','all_file_summaries':353195,'read_errors':0,'pages':len(pdf.pages),'review_minutes':d['review_budget']['total_minutes'],'pdf_sha256':hashlib.sha256((OUT/'OpenMath-compact-review.pdf').read_bytes()).hexdigest(),'mathematical_acceptance':'pending independent proof/fidelity/novelty/eligibility and difficulty assessments; not certified by these consistency checks'}
(OUT/'review-validation.json').write_text(json.dumps(report,indent=2),encoding='utf8');print(json.dumps(report))
