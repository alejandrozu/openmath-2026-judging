"""Prepared post-review continuation. Importing this file dispatches no compiler.

Requires the actual Count plus raw-axiom pilot to have passed and a new root
authorization. Retains its complete provenance. The conservative 10/11 GiB
source guard is unchanged. No proof source, compiler option, or dependency edit.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, time
from receipt_io import read_bytes_shared
from audit_axioms import parse
from luke_native_source_guard import guarded

BASE = Path(__file__).resolve().parent
DEST = BASE/'builds/luke-k4-ramsey-current-native'
REPORT = BASE/'luke-k4-ramsey-current-native-fresh-build.json'

def stamp(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def atomic(path, raw):
    tmp = path.with_suffix(path.suffix+'.tmp')
    with tmp.open('wb') as f: f.write(raw); f.flush(); os.fsync(f.fileno())
    for attempt in range(60):
        try: os.replace(tmp,path); return
        except PermissionError:
            if attempt==59: raise
            time.sleep(.1)

def save(record): atomic(REPORT,json.dumps(record,ensure_ascii=False,indent=2).encode('utf8'))

def inventory(output):
    return {str(p.relative_to(output)):{'bytes':p.stat().st_size,'sha256':sha(p)}
            for p in output.rglob('*') if p.is_file()}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--authorization',required=True)
    parser.add_argument('--reviewed-pilot-receipt-sha256',required=True)
    parser.add_argument('--resource-lease-confirmed',action='store_true')
    parser.add_argument('--resource-policy',choices=['conservative','granular'],default='conservative')
    args=parser.parse_args()
    expected_authorization=('ROOT_REVIEWED_GRANULAR_LUKE_CONTINUATION_AUTHORIZED' if args.resource_policy=='granular'
                            else 'ROOT_REVIEWED_NATIVE_LUKE_CONTINUATION_AUTHORIZED')
    assert args.authorization==expected_authorization
    assert args.resource_lease_confirmed, 'The root must coordinate the actual source-import slot'
    prior_raw=read_bytes_shared(REPORT)
    assert hashlib.sha256(prior_raw).hexdigest()==args.reviewed_pilot_receipt_sha256
    record=json.loads(prior_raw)
    assert record.get('actual_native_Count_certificate_and_raw_axiom_audit_PASS') is True
    assert record.get('status')=='COUNT_CERTIFICATE_PASS_SCOPE_INCOMPLETE'
    assert not record.get('current_module'), 'A pilot or source worker is still active'
    frozen=json.loads((DEST/'build-plan.json').read_bytes())
    schema=json.loads((BASE/'luke_native_qualified_replay_plan.json').read_bytes())
    modules={m['module']:m for m in frozen['modules']}
    assert len(modules)==51
    for key in ['id','commit','version','mathlib_pin']:
        assert record[key]==frozen[key]==schema[key]
    assert record['id']=='luke-k4-ramsey-current'
    for name,m in modules.items():
        assert sha(m['file'])==m['sha256']==sha(m['frozen_source']), name+' source bytes changed'
    literal_umbrellas=[name for name,m in modules.items()
        if any('Mathlib' in imports.split() for imports in re.findall(
            r'^\s*(?:(?:public|private)\s+)?import\s+([^\n\r]+)',Path(m['file']).read_text(encoding='utf8'),re.M))]
    preparation=json.loads((BASE/'luke-native-isolated-preparation.json').read_bytes())
    official_closure={r['module'] for r in preparation['objects'] if not r['module'].startswith('K4Ramsey.')}
    if args.resource_policy=='granular':
        assert not literal_umbrellas and len(official_closure)==935 and 'Mathlib' not in official_closure
    assert {m['module']:m['sha256'] for m in record['modules']}=={n:m['sha256'] for n,m in modules.items()}
    output=DEST/'.lake/build/lib/lean'
    assert inventory(output)==record['fresh_custom_artifact_inventory'], 'Own recorded outputs changed'
    links_raw=(BASE/'luke-native-isolated-links.json').read_bytes()
    assert hashlib.sha256(links_raw).hexdigest()==record['native_link_receipt_sha256']
    links=json.loads(links_raw)
    for row in links['dlls']:
        assert sha(row['file'])==row['sha256'] and sha(row['import_library']['file'])==row['import_library']['sha256']
    for tool,digest in record['pinned_tool_binary_hashes'].items(): assert sha(tool)==digest
    for expected in record['dependency_preflight']:
        path=Path(frozen['dependency_identity_root'])/'.lake/packages'/expected['name']
        for command,wanted in [(['git','-C',str(path),'rev-parse','HEAD'],expected['expected_head']),
                               (['git','-C',str(path),'remote','get-url','origin'],expected['expected_origin'])]:
            got=subprocess.run(command,capture_output=True,text=True,encoding='utf8')
            assert got.returncode==0 and got.stdout.strip()==wanted
    snapshot=BASE/'native_source_attempts'/('count-pilot-before-continuation-'+stamp()[:19].replace(':','').replace('-','')+'.json')
    assert not snapshot.exists(); atomic(snapshot,prior_raw)
    record.setdefault('continuation_attempts',[]).append({'started_utc':stamp(),
        'reviewed_prior_receipt_sha256':args.reviewed_pilot_receipt_sha256,
        'prior_snapshot':str(snapshot),'runner_sha256':sha(__file__),
        'guard_sha256':sha(BASE/'luke_native_source_guard.py'),
        'axiom_classifier_sha256':sha(BASE/'audit_axioms.py'),
        'resource_lease_confirmed':True,'all_existing_Count_pilot_fields_retained':True,
        'resource_policy':args.resource_policy,
        'literal_Mathlib_umbrella_custom_modules':literal_umbrellas,
        'official_native_closure_unique_count':len(official_closure),
        'official_native_closure_has_Mathlib_root':'Mathlib' in official_closure,
        'classification_notice':'Resource-only policy selection for exact frozen granular imports; no compiler or mathematical option change.'})
    record['status']='RUNNING_NATIVE_ROUTE_CONTINUATION'
    record.pop('finished_utc',None)
    states=record['module_states']
    deps={n:[d for d in re.findall(r'^\s*import\s+(\S+)',Path(m['file']).read_text(encoding='utf8'),re.M)
             if d in modules] for n,m in modules.items()}
    order=[]; visiting=set(); visited=set()
    def visit(n):
        if n in visited:return
        assert n not in visiting, 'Cyclic custom source imports'
        visiting.add(n)
        for d in deps[n]: visit(d)
        visiting.remove(n); visited.add(n); order.append(n)
    for n in ['K4Ramsey.Constructions.Final3840.NumericalBound','Audits.Graphon',*modules]: visit(n)
    record['continuation_priority_compilation_order']=order
    runtime=BASE/'runtimes/lean-4.34.1-windows'; lean=runtime/'bin/lean.exe'
    env=dict(os.environ)
    assert not env.get('LEAN_CC') and not env.get('LEAN_SYSROOT')
    env['PATH']=str(runtime/'bin')+';'+env['PATH']
    env['LEAN_PATH']=';'.join([str(output),*frozen['dependency_library_paths']]); env['LEAN_NUM_THREADS']='1'
    got=subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf8',env=env)
    assert got.returncode==0 and got.stdout.strip()==record['compiler_version_output']
    attempted=set(); stop=None
    for name in order:
        if states.get(name)=='PASS':continue
        m=modules[name]
        blocked=[d for d in deps[name] if states.get(d)!='PASS']
        if blocked:
            states[name]='BLOCKED_BY_UNPASSED_SOURCE_IMPORT'
            record['builds'].append({'module':name,'state':states[name],'source_sha256':m['sha256'],
                                    'attempted':False,'dependency_failures':blocked,'is_endpoint_audit':name.startswith('Audits.')})
            save(record); continue
        assert sha(m['file'])==m['sha256']==sha(m['frozen_source'])
        target=output.joinpath(*name.split('.')); target.parent.mkdir(parents=True,exist_ok=True)
        assert not Path(str(target)+'.olean').exists(), 'Only recorded successful own outputs may be reused'
        command=[str(lean),'-j1','-o',str(target)+'.olean','-i',str(target)+'.ilean',str(Path(m['file']).relative_to(DEST))]
        record['current_module']=name; save(record); print('INVOKE_NATIVE_ROUTE_CONTINUATION '+name,flush=True)
        log=DEST/'logs'/('continuation_'+name.replace('.','_'))
        row=guarded(command,DEST,env,log,whole_mathlib=args.resource_policy=='conservative')
        row.update(module=name,source_sha256=m['sha256'],is_endpoint_audit=name.startswith('Audits.'))
        record['builds'].append(row); attempted.add(name)
        states[name]=row['state']
        if row['state']=='PASS':
            assert Path(str(target)+'.olean').exists()
            assert sha(m['file'])==m['sha256']==sha(m['frozen_source'])
        record['fresh_custom_artifact_inventory']=inventory(output)
        record.pop('current_module',None); save(record)
        print(name+' '+row['state']+' '+str(row.get('seconds',0)),flush=True)
        if row['state'].startswith(('ENVIRONMENT_BLOCKED','NOT_INVOKED_RESOURCE','OPERATIONAL_')):
            stop=row['state']; break
    if not stop and all(states.get(n)=='PASS' for n in modules):
        organizer=Path(schema['selected_endpoint_audit_field']['organizer_file'])
        assert organizer.resolve()==(DEST/'Organizer/Selected35.lean').resolve()
        command=[str(lean),'-j1',str(organizer.relative_to(DEST))]
        record['current_module']='Organizer.Selected35'; save(record)
        row=guarded(command,DEST,env,DEST/'logs/continuation_selected35_axioms',whole_mathlib=args.resource_policy=='conservative')
        row.update(module='Organizer.Selected35',source_sha256=sha(organizer),is_endpoint_audit=True,
                   organizer_only=True,not_an_entrant_source_module=True)
        record['builds'].append(row); record.pop('current_module',None)
        if row['state']!='PASS':stop=row['state']
    expected=set(schema['selected_endpoint_audit_field']['expected'])
    general=set(schema['selected_endpoint_audit_field']['ordinary_general_endpoints'])
    selected=[o for row in record['builds'] if row.get('exit')==0 and row.get('is_endpoint_audit')
              for o in parse(row.get('stdout','')) if o['endpoint'] in expected]
    observed={o['endpoint']:o for o in selected}
    bad=[o for o in selected if o['classification'] in {'SORRY_ADMISSION','UNRECOGNIZED_AXIOMS'}]
    general_bad=[n for n in general if n not in observed or observed[n]['native_axioms']
                 or observed[n]['classification'] not in {'STANDARD_KERNEL_AXIOMS','AXIOM_FREE'}]
    record['selected_endpoint_outputs']=selected
    record['selected_endpoint_outputs_unique']=len(observed)
    record['selected_endpoint_uses_sorry']=any(o['classification']=='SORRY_ADMISSION' for o in selected)
    record['selected_unrecognized_axioms']=[o for o in bad if o['classification']=='UNRECOGNIZED_AXIOMS']
    record['general_endpoint_trust_mismatches']=general_bad
    record['missing_selected_endpoint_outputs']=sorted(expected-set(observed))
    record['all_source_modules_attempted_or_dependency_blocked']=set(states)==set(modules)
    complete=not stop and all(states.get(n)=='PASS' for n in modules) and len(observed)==35 and not bad and not general_bad
    record['status']='PASS_WITH_NATIVE_EVALUATION' if complete else (stop or 'SOURCE_OR_ENDPOINT_SCOPE_INCOMPLETE')
    record['fresh_custom_artifact_inventory']=inventory(output)
    record['finished_utc']=stamp(); record.pop('current_module',None); save(record)
    print(json.dumps({'status':record['status'],'source_PASS':sum(states.get(n)=='PASS' for n in modules),
                      'selected_unique':len(observed),'missing':record['missing_selected_endpoint_outputs']},indent=2),flush=True)

if __name__=='__main__':main()
