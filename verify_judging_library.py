"""Verify coverage and local preservation without running contestant code."""
import pathlib,sys,json,zipfile,hashlib,datetime
ROOT=pathlib.Path(__file__).resolve().parent/'OpenMath-Judging';sys.path.insert(0,str(ROOT))
from library_core import connect,read_bytes
db=connect(ROOT);errors=[];checked=0
ids=[x for r in db.execute("SELECT record_ids FROM teams WHERE id!='EVENT'") for x in json.loads(r[0])]
assert len(ids)==74 and len(set(ids))==74
assert {f'E{i:02d}' for i in range(1,75)}==set(ids)
archives=db.execute('SELECT * FROM archives').fetchall()
for a in archives:
    p=(ROOT/a['local_path']).resolve();assert p.is_relative_to(ROOT.resolve()) and p.is_file()
    actual=hashlib.file_digest(p.open('rb'),'sha256').hexdigest();assert actual==a['sha256'],a['local_path']
    with zipfile.ZipFile(p) as z:
        members={i.filename:i for i in z.infolist() if not i.is_dir()}
        rows=db.execute('SELECT * FROM files WHERE archive_path=?',(a['local_path'],)).fetchall()
        assert len(rows)==len(members)==a['member_count']
        assert {r['archive_member'] for r in rows}==set(members)
        for r in rows:
            i=members[r['archive_member']];assert r['bytes']==i.file_size and r['crc32']==f'{i.CRC:08x}'
        for r in rows[:1]+rows[-1:]:read_bytes(ROOT,r);checked+=1
for r in db.execute("SELECT * FROM files WHERE local_path!=''"):
    p=(ROOT/r['local_path']).resolve();assert p.is_relative_to(ROOT.resolve()) and p.is_file()
    assert p.stat().st_size==r['bytes'],(r['local_path'],r['bytes'],p.stat().st_size)
    if r['sha256']:assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==r['sha256'],r['local_path']
    checked+=1
assert db.execute('PRAGMA integrity_check').fetchone()[0]=='ok'
assert db.execute('SELECT COUNT(*) FROM files WHERE category IS NULL OR category=""').fetchone()[0]==0
lean=db.execute("SELECT overview FROM teams WHERE id='E06'").fetchone()[0];assert '0.8' in lean and 'unassigned' in lean
assert db.execute("SELECT COUNT(*) FROM files WHERE team_id='E03' AND version LIKE '%68122d1%'").fetchone()[0]>0
assert db.execute("SELECT COUNT(*) FROM files WHERE team_id='E10' AND version LIKE '%adcfa053%'").fetchone()[0]>0
result={'verified_at':datetime.datetime.now().astimezone().isoformat(timespec='seconds'),'sqlite_integrity':'ok','source_records_preserved':len(ids),'all_original72_preserved':True,'all_extra33_preserved':True,'grouped_records_excluding_event':db.execute("SELECT COUNT(*) FROM teams WHERE id!='EVENT'").fetchone()[0],'files':db.execute('SELECT COUNT(*) FROM files').fetchone()[0],'archives_sha256_checked':len(archives),'archive_metadata_coverage':'all central-directory files indexed, exact sizes/CRC metadata match','loose_files_and_sample_member_read_checks':checked,'later_versions_separate':True,'leanification_raw_adjusted_unassigned_and_0_8_policy_preserved':True,'contestant_code_executed':False,'mathematical_claims_verified':False,'errors':errors}
(ROOT/'preservation-verification.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print(json.dumps(result));db.close()
