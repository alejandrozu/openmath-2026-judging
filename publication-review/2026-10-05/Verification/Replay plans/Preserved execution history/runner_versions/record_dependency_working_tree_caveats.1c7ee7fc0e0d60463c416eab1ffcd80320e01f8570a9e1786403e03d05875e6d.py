"""Read-only source provenance check, including deliberately omitted tar symlinks."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
BASE=Path(__file__).resolve().parent;version=sys.argv[1]
manifest=json.loads((BASE/('dependencies-'+version+'-source-manifest.json')).read_text())
rows=[]
for item in manifest:
 path=Path(item['destination'])
 def git(args):return subprocess.run(['git','--no-optional-locks']+args,cwd=path,capture_output=True,text=True,encoding='utf8',check=True).stdout.rstrip('\r\n')
 status=git(['status','--porcelain=1','--untracked-files=no'])
 changes=[]
 for line in status.splitlines():
  file=line[3:].strip('"');mode=git(['ls-tree','HEAD','--',file])
  changes.append({'status':line[:2],'path':file,'git_tree_entry':mode,
   'head_symlink_target':git(['show','HEAD:'+file]) if mode.startswith('120000 ') else None})
 rows.append({'destination':str(path),'expected_commit':item['commit'],'actual_commit':git(['rev-parse','HEAD']),
  'origin_url':git(['remote','get-url','origin']),'tracked_changes':changes,
  'tracked_lean_source_changes':[c for c in changes if c['path'].endswith('.lean')],
  'source_archive_omitted_non_regular_members':item.get('omitted_non_regular_members',[]),
  'operational_untracked_files_not_part_of_entrant_source':'Dependency cache artifacts and source-completion/exporter receipts are present; ignored/untracked files are excluded from this source-only tracked comparison.'})
record={'version':version,'packages':rows,'status':'PASS_NO_TRACKED_LEAN_SOURCE_CHANGE' if all(not r['tracked_lean_source_changes'] and r['expected_commit']==r['actual_commit'] for r in rows) else 'SOURCE_PROVENANCE_HOLD',
 'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
report=BASE/('dependency-working-tree-caveats-'+version+'.json')
if report.exists():
 previous=report.read_bytes();sha=hashlib.sha256(previous).hexdigest();archive=report.with_name(report.stem+'.prior-'+sha+'.json')
 if archive.exists():assert archive.read_bytes()==previous
 else:archive.write_bytes(previous)
 record['previous_receipt']={'file':str(archive),'sha256':sha,'qualification':'PRESERVED_BEFORE_READ_ONLY_REFRESH; older leading-space trimming may have truncated the first porcelain path.'}
record['reader_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
temp=report.with_suffix('.json.tmp');temp.write_text(json.dumps(record,indent=2),encoding='utf8');os.replace(temp,report)
print(record['status'],len(rows),'packages',flush=True)
