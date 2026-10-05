"""Prepared RawCount-only retry. No invocation occurs on import.

Requires root review of actual Count source PASS and the original conservative
11 GiB dispatch-gate no-attempt. Preserves that entire pilot and its no-attempt
row. An explicit granular authorization selects the unchanged 6/5 GiB guard.
This adapter prints imported axioms only; it never recomputes the count.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, time
from receipt_io import read_bytes_shared
from audit_axioms import parse
from luke_native_source_guard import guarded, GIB

BASE=Path(__file__).resolve().parent
DEST=BASE/'builds/luke-k4-ramsey-current-native'
REPORT=BASE/'luke-k4-ramsey-current-native-fresh-build.json'
COUNT='K4Ramsey.Constructions.Final3840.Certificate'

def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def atomic(path,raw):
    tmp=path.with_suffix(path.suffix+'.tmp')
    with tmp.open('wb') as f:f.write(raw);f.flush();os.fsync(f.fileno())
    for attempt in range(60):
        try:os.replace(tmp,path);return
        except PermissionError:
            if attempt==59:raise
            time.sleep(.1)

def save(record):atomic(REPORT,json.dumps(record,ensure_ascii=False,indent=2).encode('utf8'))

def inventory(output):
    return {str(p.relative_to(output)):{'bytes':p.stat().st_size,'sha256':sha(p)}
            for p in output.rglob('*') if p.is_file()}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--authorization',required=True)
    parser.add_argument('--reviewed-pilot-receipt-sha256',required=True)
    parser.add_argument('--resource-lease-confirmed',action='store_true')
    args=parser.parse_args()
    assert args.authorization=='ROOT_REVIEWED_GRANULAR_RAW_COUNT_AUDIT_ONLY_RETRY_AUTHORIZED'
    assert args.resource_lease_confirmed
    raw=read_bytes_shared(REPORT)
    assert hashlib.sha256(raw).hexdigest()==args.reviewed_pilot_receipt_sha256
    record=json.loads(raw)
    assert record['status']=='COUNT_SOURCE_PASS_RAW_OR_NATIVE_EVIDENCE_UNQUALIFIED'
    assert record.get('pilot_finished_utc') and not record.get('current_module')
    assert record['module_states'].get(COUNT)=='PASS'
    frozen=json.loads((DEST/'build-plan.json').read_bytes())
    modules={m['module']:m for m in frozen['modules']}
    assert len(modules)==51
    for key in ['id','commit','version','mathlib_pin']:assert record[key]==frozen[key]
    for name,m in modules.items():
        assert sha(m['file'])==m['sha256']==sha(m['frozen_source'])
        imports=re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n\r]+)',Path(m['file']).read_text(encoding='utf8'),re.M)
        assert not any('Mathlib' in s.split() for s in imports), name+' uses literal Mathlib umbrella'
    count_rows=[r for r in record['builds'] if r.get('module')==COUNT and r.get('state')=='PASS' and r.get('exit')==0]
    assert len(count_rows)==1 and count_rows[0]['source_sha256']==modules[COUNT]['sha256']
    count=count_rows[0]
    assert count.get('all_expected_native_images_observed') is True and not count.get('image_observation_errors')
    original_raw_rows=[r for r in record['builds'] if r.get('module')=='Organizer.RawCount']
    assert len(original_raw_rows)==1
    old=original_raw_rows[0]
    assert old.get('state')=='NOT_INVOKED_RESOURCE_DISPATCH_GATE' and old.get('attempted') is False
    assert old['resource_policy']['initial_available_commit_bytes']==11*GIB
    output=DEST/'.lake/build/lib/lean'
    assert inventory(output)==record['fresh_custom_artifact_inventory']
    links_raw=(BASE/'luke-native-isolated-links.json').read_bytes()
    assert hashlib.sha256(links_raw).hexdigest()==record['native_link_receipt_sha256']
    links=json.loads(links_raw)
    assert {r['sha256'] for r in count['loaded_native_images']}=={r['sha256'] for r in links['dlls']}
    for row in links['dlls']:
        assert sha(row['file'])==row['sha256'] and sha(row['import_library']['file'])==row['import_library']['sha256']
    for tool,digest in record['pinned_tool_binary_hashes'].items():assert sha(tool)==digest
    preparation=json.loads((BASE/'luke-native-isolated-preparation.json').read_bytes())
    official={r['module'] for r in preparation['objects'] if not r['module'].startswith('K4Ramsey.')}
    assert len(official)==935 and 'Mathlib' not in official
    for expected in record['dependency_preflight']:
        path=Path(frozen['dependency_identity_root'])/'.lake/packages'/expected['name']
        for command,wanted in [(['git','-C',str(path),'rev-parse','HEAD'],expected['expected_head']),
                               (['git','-C',str(path),'remote','get-url','origin'],expected['expected_origin'])]:
            got=subprocess.run(command,capture_output=True,text=True,encoding='utf8')
            assert got.returncode==0 and got.stdout.strip()==wanted
    suffix=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    snapshot=BASE/'native_source_attempts'/('count-pilot-before-raw-retry-'+suffix+'.json')
    assert not snapshot.exists();atomic(snapshot,raw)
    runtime=BASE/'runtimes/lean-4.34.1-windows';lean=runtime/'bin/lean.exe'
    env=dict(os.environ)
    assert not env.get('LEAN_CC') and not env.get('LEAN_SYSROOT')
    env['PATH']=str(runtime/'bin')+';'+env['PATH']
    env['LEAN_PATH']=';'.join([str(output),*frozen['dependency_library_paths']]);env['LEAN_NUM_THREADS']='1'
    got=subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf8',env=env)
    assert got.returncode==0 and got.stdout.strip()==record['compiler_version_output']
    source=DEST/'Organizer/RawCount.lean';source_hash=sha(source)
    record.setdefault('raw_count_retry_attempts',[]).append({'started_utc':stamp(),
        'prior_pilot_snapshot':str(snapshot),'prior_pilot_receipt_sha256':args.reviewed_pilot_receipt_sha256,
        'runner_sha256':sha(__file__),'guard_sha256':sha(BASE/'luke_native_source_guard.py'),
        'axiom_classifier_sha256':sha(BASE/'audit_axioms.py'),'resource_policy':'granular 6 GiB own / 5 GiB commit / 6 GiB physical / 4 GB disk',
        'classification':'Print-only imported proof axiom inspection; no counting function invocation or compiler-option change.',
        'original_conservative_11GiB_no_attempt_row_preserved':True})
    record['status']='RUNNING_RAW_COUNT_ONLY_GRANULAR_RETRY';record['current_module']='Organizer.RawCount';save(record)
    command=[str(lean),'-j1',str(source.relative_to(DEST))]
    row=guarded(command,DEST,env,DEST/'logs'/('raw_count_axioms_granular_retry_'+suffix),whole_mathlib=False)
    row.update(module='Organizer.RawCount',source_sha256=source_hash,is_endpoint_audit=True,
               organizer_only=True,not_an_entrant_source_module=True,explicit_scoped_retry=True)
    assert sha(source)==source_hash
    record['builds'].append(row)
    printed=parse(row.get('stdout',''));observed={o['endpoint']:o for o in printed}
    required={'K4Ramsey.Final3840.exact_count','K4Ramsey.Final3840.exact_density'}
    clean=required<=set(observed) and all(observed[n]['classification']=='NATIVE_EVALUATION_TRUST'
        and not observed[n]['unrecognized_axioms'] for n in required)
    record['raw_count_endpoint_outputs']=printed
    record['raw_count_requested_endpoints']=sorted(required)
    record['actual_native_Count_certificate_and_raw_axiom_audit_PASS']=row['state']=='PASS' and clean
    record['status']=('COUNT_CERTIFICATE_PASS_SCOPE_INCOMPLETE' if record['actual_native_Count_certificate_and_raw_axiom_audit_PASS']
                      else 'COUNT_SOURCE_PASS_RAW_OR_NATIVE_EVIDENCE_UNQUALIFIED')
    record['raw_count_retry_finished_utc']=stamp();record.pop('current_module',None)
    record['fresh_custom_artifact_inventory']=inventory(output)
    record['review_boundary']='STOPPED_AFTER_SCOPED_RAW_COUNT_RETRY; no remaining source dispatch or process stop.'
    save(record)
    print(json.dumps({'status':record['status'],'raw_count_outputs':printed,'original_no_attempt_preserved':True},indent=2),flush=True)

if __name__=='__main__':main()
