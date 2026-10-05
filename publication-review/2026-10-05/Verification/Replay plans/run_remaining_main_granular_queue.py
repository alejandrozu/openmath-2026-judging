"""Root-authorized one-companion novelty queue; preserves exact source plans.

No process starts merely by importing.  Each project is piloted and guarded,
and each family receipt remains independently reviewable.  The companion lease
may be checkpointed with hold-main-granular-queue or hold-third-worker-dispatch.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,time
from receipt_io import read_json_shared
from resource_metrics import snapshot
BASE=Path(__file__).resolve().parent
PROJECTS=['sakana-ferrers','sakana-a060957','sakana-a100475',
          'sakana-FOCUS-MATRIX-seed0','sakana-FOCUS-MATRIX-seed1','sakana-FOCUS-MATRIX-seed2','sakana-a000224']
REPORT=BASE/'remaining-main-granular-queue.json'
def stamp():return time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
def hold():return (BASE/'hold-main-granular-queue').exists() or (BASE/'hold-third-worker-dispatch').exists()
def save(doc):
    temp=REPORT.with_suffix('.json.tmp');temp.write_text(json.dumps(doc,indent=2),encoding='utf8');os.replace(temp,REPORT)
def wait_gate(doc):
    while True:
        if hold():return False
        metrics={'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()}
        if metrics['disk_free_bytes']>=4_000_000_000 and metrics['free_physical_bytes']>=6*2**30 and metrics['available_commit_bytes']>=5*2**30:
            doc['last_dispatch_metrics']=metrics;save(doc);return True
        if doc.get('status')!='WAITING_RESOURCE_DISPATCH_GATES':
            doc['status']='WAITING_RESOURCE_DISPATCH_GATES';doc['wait_initial_metrics']=metrics;save(doc)
            print('QUEUE_GATE_WAIT',doc['current_project'],json.dumps(metrics),flush=True)
        time.sleep(2)
def invoke(project,flags,doc):
    if not wait_gate(doc):return False
    cmd=[sys.executable,'-X','utf8',str(BASE/'run_source_plan.py'),project,'1',*flags]
    doc['status']='RUNNING';doc['current_command']=cmd;save(doc)
    # Inherit the caller pipes; the source runner's own Win32 job guards each Lean child.
    code=subprocess.call(cmd,cwd=BASE.parents[2])
    receipt=BASE/(project+'-fresh-build.json')
    result=read_json_shared(receipt) if receipt.exists() else None
    doc['attempts'].append({'project':project,'command':cmd,'wrapper_exit':code,'finished_utc':stamp(),
      'receipt':str(receipt) if result else None,'status':result.get('status') if result else 'NO_SOURCE_RECEIPT',
      'receipt_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest() if receipt.exists() else None})
    save(doc)
    return bool(result) and code==0
def main():
    assert sys.argv[1:] == ['--execute'],'Explicit coordinated execution only'
    doc={'status':'PREPARED','started_utc':stamp(),'projects':PROJECTS,'attempts':[],
      'authorization':'ROOT_EXTENDED_SINGLE_GRANULAR_COMPANION_NOVELTY_LEASE_AFTER_OPDP89',
      'qualification':'One companion only; no whole DMS/E169/held projects. A000 literal sources and its audit are deferred for their separate lease.',
      'runner_source_sha256':hashlib.sha256((BASE/'run_source_plan.py').read_bytes()).hexdigest(),
      'queue_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if REPORT.exists():
        old=REPORT.with_name(REPORT.stem+'-prior-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'.json')
        assert not old.exists();old.write_bytes(REPORT.read_bytes());doc['prior_queue_receipt']=str(old)
    save(doc)
    for project in PROJECTS:
        doc['current_project']=project
        if hold():doc['status']='SCHEDULED_RESOURCE_CHECKPOINT';break
        file=BASE/(project+'-fresh-build.json');prior=read_json_shared(file) if file.exists() else None
        if prior and (prior['status'].startswith('PASS') or prior['status'] in {'BUILD_FAILED_OR_TIMED_OUT','ENDPOINT_AUDIT_OUTPUT_INCOMPLETE'}):
            doc['attempts'].append({'project':project,'status':'ACTUAL_COMPLETED_FAMILY_RECEIPT_PRESERVED','receipt':str(file)});save(doc);continue
        if project!='sakana-a000224' and not prior:
            if not invoke(project,['--pilot-third-slot'],doc):doc['status']='SCHEDULED_RESOURCE_CHECKPOINT' if hold() else 'OPERATIONAL_WRAPPER_BLOCKED';break
            pilot=read_json_shared(file)
            if pilot['status']!='SCHEDULED_RESOURCE_CHECKPOINT' or len(pilot['builds'])!=1 or pilot['builds'][0]['exit']!=0:
                doc['status']='FIRST_SOURCE_PILOT_DID_NOT_PASS';break
            subprocess.run([sys.executable,'-X','utf8',str(BASE/'archive_granular_first_pilot.py'),project],check=True,cwd=BASE.parents[2])
        flags=['--guarded-third-slot']+(['--defer-whole-imports'] if project=='sakana-a000224' else [])
        resource_stops={}
        while True:
            if not invoke(project,flags,doc):
                doc['status']='SCHEDULED_RESOURCE_CHECKPOINT' if hold() else 'OPERATIONAL_WRAPPER_BLOCKED';doc['finished_utc']=stamp();save(doc);return
            result=read_json_shared(file)
            if hold():doc['status']='SCHEDULED_RESOURCE_CHECKPOINT';save(doc);return
            if result['status'] in {'ENVIRONMENT_BLOCKED_DISK_RESERVE','ENVIRONMENT_BLOCKED_THIRD_WORKER_MEMORY','ENVIRONMENT_BLOCKED'}:
                last=result.get('builds',[])[-1] if result.get('builds') else {}
                key=(last.get('module'),last.get('stop_reason'),result['status'])
                resource_stops[key]=resource_stops.get(key,0)+1
                if resource_stops[key]>=2:
                    doc['status']='REPEATED_OWN_RESOURCE_STOP_REVIEW_REQUIRED';doc['finished_utc']=stamp()
                    doc['repeated_resource_stop']={'project':project,'module':key[0],'stop_reason':key[1],'count':resource_stops[key]}
                    save(doc);return
                doc['status']='WAITING_RESOURCE_RETRY_AFTER_OWN_CHECKPOINT';save(doc);time.sleep(2);continue
            if result['status'].startswith('ENVIRONMENT_BLOCKED'):
                doc['status']='OPERATIONAL_GUARD_BLOCKED_REVIEW_REQUIRED';doc['finished_utc']=stamp();save(doc);return
            break
        if project=='sakana-a000224':
            assert result['status']!='PASS','Whole-import deferred A000 scope cannot be completed PASS'
    else:doc['status']='AUTHORIZED_GRANULAR_SCOPE_COMPLETED_WHOLE_A000_LEASE_REMAINS'
    doc['finished_utc']=stamp();save(doc);print('QUEUE_STATUS',doc['status'],flush=True)
if __name__=='__main__':main()
