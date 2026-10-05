"""Guarded isolated C emission/objects from immutable Luke and official sources.

This prepares native objects only. It never links or loads a DLL, runs counting
diagnostics, changes theorems, writes .oleans, or writes shared dependency caches.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,struct,subprocess,time
from native_resource_guard import K,W,EXTENDEDLIMIT,MEMORYSTATUSEX,GIB,physical,memory,processes,own_tree,allocated
from receipt_io import read_json_shared

B=Path(__file__).resolve().parent
R=B/'runtimes/lean-4.34.1-windows'
S=B/'builds/luke-k4-ramsey-current-direct'
D=B/'builds/luke-k4-ramsey-native-isolated'
RECEIPT=B/'luke-native-isolated-preparation.json'
parser=argparse.ArgumentParser();parser.add_argument('--stage',choices=['emit','objects'],required=True);parser.add_argument('--resume',action='store_true');parser.add_argument('--handoff-token',required=True);args=parser.parse_args()
assert args.handoff_token=='ROOT_APPROVED_COORDINATED_NATIVE_PREPARATION'
frozen=json.loads((S/'build-plan.json').read_text(encoding='utf8'))
closure=json.loads((B/'luke_isolated_native_symbol_closure.json').read_text(encoding='utf8'))
selected=json.loads((B/'luke_selective_native_readonly_assessment.json').read_text(encoding='utf8'))['own_source_closure']
allmodules={m['module']:m for m in frozen['modules']}
source_inputs={n:allmodules[n] for n in selected}
env=dict(os.environ);env['PATH']=str(R/'bin')+';'+env['PATH'];env['LEAN_NUM_THREADS']='1'
env['LEAN_PATH']=';'.join([str(S/'.lake/build/lib/lean'),*frozen['dependency_library_paths']])
assert not env.get('LEAN_CC'),'Do not replace the pinned wrapper compiler'

def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save():
    tmp=RECEIPT.with_suffix('.json.tmp')
    with tmp.open('w',encoding='utf8') as o:json.dump(record,o,indent=2);o.flush();os.fsync(o.fileno())
    for attempt in range(60):
        try:os.replace(tmp,RECEIPT);return
        except PermissionError:
            if attempt==59:raise
            time.sleep(.1)
def source_inventory():
    rows={}
    for n,m in source_inputs.items():
        assert sha(m['file'])==m['sha256'] and sha(m['frozen_source'])==m['sha256'],n+' frozen/staged source changed'
        rows[n]={'source_sha256':m['sha256'],'file':m['file'],'frozen_source':m['frozen_source']}
        stem=S/'.lake/build/lib/lean'/Path(*n.split('.'))
        for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir']:
            p=Path(str(stem)+suffix)
            if p.exists():rows[n][suffix]={'file':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
        assert '.olean' in rows[n],n+' existing fresh direct proof output unavailable'
    return rows
def output_inventory():
    return {str(p.relative_to(D)):{'logical_bytes':p.stat().st_size,'allocated_bytes':allocated(p),'sha256':sha(p)} for p in sorted(D.rglob('*')) if p.is_file()}
def workspace_bytes():return sum(p.stat().st_size for p in D.rglob('*') if p.is_file())
def system_memory():
    s=MEMORYSTATUSEX();s.dwLength=ctypes.sizeof(s)
    if not K.GlobalMemoryStatusEx(ctypes.byref(s)):raise ctypes.WinError(ctypes.get_last_error())
    return {'physical_available_bytes':int(s.ullAvailPhys),'available_commit_bytes':int(s.ullAvailPageFile),'commit_limit_bytes':int(s.ullTotalPageFile)}
def exports(p):
    data=Path(p).read_bytes();machine,n,_,_,_,sizeopt,_=struct.unpack_from('<HHIIIHH',data,0)
    assert machine==0x8664,'Expected genuine Windows x64 COFF object'
    names=[]
    for i in range(n):
        offset=20+sizeopt+40*i;name=data[offset:offset+8].rstrip(b'\0').decode('ascii')
        size,ptr=struct.unpack_from('<II',data,offset+16)
        if name=='.drectve':names.extend(re.findall(r'-export:([^ ]+)',data[ptr:ptr+size].decode('ascii')))
    assert len(names)==len(set(names)),'Duplicate exports inside one object'
    return sorted(names)
def guarded(command,tag,private_cap,cwd):
    first_memory=system_memory()
    row={'command':command,'started_utc':stamp(),'private_cap_bytes':private_cap,'minimum_disk_free_bytes':shutil.disk_usage(B).free,
      'minimum_physical_available_bytes':first_memory['physical_available_bytes'],'minimum_available_commit_bytes':first_memory['available_commit_bytes'],
      'dispatch_memory_counters':first_memory,'workspace_logical_bytes_before':workspace_bytes(),'attempted':False}
    if row['minimum_disk_free_bytes']<4_000_000_000 or row['minimum_physical_available_bytes']<6*GIB or row['minimum_available_commit_bytes']<GIB:
        row['state']='NOT_INVOKED_RESOURCE_DISPATCH_GATE';return row
    if row['workspace_logical_bytes_before']>1_000_000_000:
        row['state']='NOT_INVOKED_WORKSPACE_BOUND';return row
    logs=D/'logs';logs.mkdir(exist_ok=True);so=logs/(tag+'.stdout.txt');se=logs/(tag+'.stderr.txt')
    tmp=D/'tmp';tmp.mkdir(exist_ok=True);child_env=dict(env);child_env['TEMP']=str(tmp);child_env['TMP']=str(tmp)
    job=K.CreateJobObjectW(None,None)
    if not job:raise OSError('Cannot create own Windows resource job')
    limits=EXTENDEDLIMIT();limits.BasicLimitInformation.LimitFlags=0x2000|0x0100|0x0200
    limits.ProcessMemoryLimit=private_cap;limits.JobMemoryLimit=private_cap
    if not K.SetInformationJobObject(job,9,ctypes.byref(limits),ctypes.sizeof(limits)):
        K.CloseHandle(job);raise OSError('Cannot install own private-memory limits')
    start=time.monotonic();seen={};peak=0;peak_rss=0;samples=0;stop=None
    try:
        with so.open('wb') as out,se.open('wb') as err:
            proc=subprocess.Popen(command,stdout=out,stderr=err,env=child_env,cwd=cwd,creationflags=0x08000000)
            row['attempted']=True;row['root_pid']=proc.pid
            if not K.AssignProcessToJobObject(job,W.HANDLE(int(proc._handle))):
                subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],capture_output=True);proc.wait();raise OSError('Own-job assignment failed')
            row['own_job_assignment']='PASS'
            while True:
                registry=processes();rows=[]
                for pid in own_tree(proc.pid,registry):
                    m=memory(pid)
                    if m:
                        rows.append(m);s=seen.setdefault(str(pid),{'exe':registry.get(pid,{}).get('exe',''),'peak_private_bytes':0,'peak_rss_bytes':0})
                        s['peak_private_bytes']=max(s['peak_private_bytes'],m['private_bytes']);s['peak_rss_bytes']=max(s['peak_rss_bytes'],m['peak_rss_bytes'])
                current=sum(m['private_bytes'] for m in rows);peak=max(peak,current);peak_rss=max(peak_rss,sum(m['rss_bytes'] for m in rows));samples+=1
                disk=shutil.disk_usage(B).free;now_memory=system_memory();phys=now_memory['physical_available_bytes'];commit=now_memory['available_commit_bytes']
                row['minimum_disk_free_bytes']=min(row['minimum_disk_free_bytes'],disk);row['minimum_physical_available_bytes']=min(row['minimum_physical_available_bytes'],phys)
                row['minimum_available_commit_bytes']=min(row['minimum_available_commit_bytes'],commit)
                if disk<1_000_000_000:stop='ENVIRONMENT_BLOCKED_DISK_RESERVE'
                elif phys<3*GIB:stop='ENVIRONMENT_BLOCKED_PHYSICAL_RESERVE'
                elif commit<GIB:stop='ENVIRONMENT_BLOCKED_AVAILABLE_COMMIT_RESERVE'
                elif current>private_cap:stop='ENVIRONMENT_BLOCKED_OWN_PRIVATE_LIMIT'
                elif workspace_bytes()>1_000_000_000:stop='ENVIRONMENT_BLOCKED_NATIVE_WORKSPACE_BOUND'
                elif time.monotonic()-start>900:stop='OPERATIONAL_TIMEOUT'
                if stop:K.TerminateJobObject(job,77);proc.wait(timeout=15);break
                if proc.poll() is not None:break
                time.sleep(.25)
            proc.wait(timeout=15);row['exit']=proc.returncode
            peak_limits=EXTENDEDLIMIT()
            if not K.QueryInformationJobObject(job,9,ctypes.byref(peak_limits),ctypes.sizeof(peak_limits),None):raise OSError('Own job peak-memory query failed')
            row['job_peak_process_private_bytes']=int(peak_limits.PeakProcessMemoryUsed);row['job_peak_aggregate_private_bytes']=int(peak_limits.PeakJobMemoryUsed)
            row['state']=stop or ('PASS' if proc.returncode==0 else 'COMPILER_FAILED')
    except Exception as e:
        K.TerminateJobObject(job,78);row.update(state='OPERATIONAL_ERROR',error=str(e))
    finally:K.CloseHandle(job)
    row.update(finished_utc=stamp(),seconds=round(time.monotonic()-start,3),polled_peak_tree_private_bytes=peak,
      polled_peak_tree_rss_bytes=peak_rss,counter_samples=samples,observed_own_processes=seen,workspace_logical_bytes_after=workspace_bytes(),
      stdout_file=str(so),stderr_file=str(se),stdout_sha256=sha(so),stderr_sha256=sha(se),
      stdout_excerpt=so.read_text(encoding='utf8',errors='replace')[:32768],stderr_excerpt=se.read_text(encoding='utf8',errors='replace')[:32768])
    return row

import ctypes
before=source_inventory()
if args.stage=='emit' and not args.resume:
    assert not RECEIPT.exists(),'Do not overwrite an existing native preparation; use reviewed resume'
    assert not D.exists() or not any(D.iterdir()),'Cold isolated native workspace required'
    D.mkdir(parents=True,exist_ok=True)
    record={'id':'luke-k4-ramsey-native-isolated-preparation','route':'direct-source-identical-C-emission-and-isolated-objects','status':'C_EMISSION_RUNNING',
      'started_utc':stamp(),'source_commit':frozen['commit'],'lean_version':frozen['version'],'mathlib_pin':frozen['mathlib_pin'],
      'compiler_pin':'5045d0056413266e57c625dcd7c365b10e377c52','no_DLL_link_or_load':True,'no_olean_output_or_source_edit':True,
      'custom_package':None,'source_and_input_olean_inventory_before':before,'emissions':[],'objects':[],
      'frozen_plan_sha256':sha(S/'build-plan.json'),'official_C_closure_sha256':sha(B/'luke_isolated_native_symbol_closure.json'),
      'guards':{'dispatch_disk_bytes':4_000_000_000,'dispatch_physical_bytes':6*GIB,'continuous_disk_bytes':1_000_000_000,
        'continuous_physical_bytes':3*GIB,'Lean_own_private_bytes':6*GIB,'C_own_private_bytes':2*GIB,'workspace_bytes':1_000_000_000,'checkpoint_objects':32},
      'environment':{'LEAN_NUM_THREADS':'1','LEAN_PATH':env['LEAN_PATH'],'no_LEAN_CC_override':True},
      'tool_hashes':{str(p):sha(p) for p in [R/'bin/lean.exe',R/'bin/leanc.exe',R/'bin/clang.exe']},
      'runner_sha256':sha(__file__),'resource_helper_sha256':sha(B/'native_resource_guard.py')}
else:
    assert RECEIPT.exists();record=read_json_shared(RECEIPT)
    assert record['source_and_input_olean_inventory_before']==before,'Existing frozen source/input oleans changed'
    assert record['frozen_plan_sha256']==sha(S/'build-plan.json') and record['official_C_closure_sha256']==sha(B/'luke_isolated_native_symbol_closure.json')
    assert record['tool_hashes']=={str(p):sha(p) for p in [R/'bin/lean.exe',R/'bin/leanc.exe',R/'bin/clang.exe']}
    for row in record['emissions']:
        if row['state']=='PASS':assert sha(row['output_c_file'])==row['output_c_sha256']
    for row in record['objects']:
        if row['state']=='PASS':assert sha(row['object_file'])==row['object_sha256']
    record.setdefault('phase_reentries',[]).append({'stage':args.stage,'started_utc':stamp(),'resume':args.resume,
      'executed_runner_sha256':sha(__file__),'new_dispatch_and_continuous_available_commit_floor_bytes':GIB,
      'commit_counter_scope':'Only invocations in this phase; earlier separate external guard receipt retains its actual dated scope'})
save()
if args.stage=='emit':
    complete={r['module'] for r in record['emissions'] if r['state']=='PASS'}
    order=['K4Ramsey.Constructions.Final3840.Data.Part06','K4Ramsey.Constructions.Final3840.Count']
    order+=sorted(set(selected)-set(order))
    record['emission_order']=order
    for n in order:
        if n in complete:continue
        m=source_inputs[n];assert sha(m['file'])==m['sha256']
        out=D/'ir'/Path(*n.split('.'));out.parent.mkdir(parents=True,exist_ok=True);out=Path(str(out)+'.c')
        assert not out.exists(),'Unexpected custom C output: do not overwrite a partial artifact without explicit new plan'
        command=[str(R/'bin/lean.exe'),'-j1','-c',str(out),str(Path(m['file']).relative_to(S))]
        record['current_operation']='emit '+n;save();print('EMIT',n,flush=True)
        row=guarded(command,'emit_'+n,6*GIB,str(S));row.update(module=n,source_sha256=m['sha256'],output_c_file=str(out))
        if row['state']=='PASS':
            assert out.exists();row.update(output_c_sha256=sha(out),output_c_bytes=out.stat().st_size,output_c_allocated_bytes=allocated(out))
        record['emissions'].append(row)
        assert source_inventory()==before,'A source or selected input .olean changed during C emission'
        record['source_and_input_olean_inventory_after']=before;save();print('EMIT_RESULT',n,row['state'],row.get('seconds'),row.get('output_c_bytes'),flush=True)
        if row['state']!='PASS':record['status']='C_EMISSION_CHECKPOINT';break
    else:record['status']='C_EMISSION_PASS'
else:
    assert record['status'] in ['C_EMISSION_PASS','OBJECTS_RUNNING','OBJECTS_CHECKPOINT'],'All exact custom C emissions must pass first'
    record['objects_runner_sha256']=sha(__file__)
    record['compiler_header_sha256']=sha(R/'include/lean/lean.h')
    record['official_dependency_artifact_snapshot_sha256']=sha(B/'luke_native_dependency_artifact_snapshot.json')
    record['status']='OBJECTS_RUNNING'
    done={r['module'] for r in record['objects'] if r['state']=='PASS'}
    object_inputs=[{'module':r['module'],'source':r['file'],'sha256':r['sha256'],'package':r['package']} for r in closure['records']]
    object_inputs += [{'module':r['module'],'source':r['output_c_file'],'sha256':r['output_c_sha256'],'package':'custom-default-none'} for r in record['emissions'] if r['state']=='PASS']
    assert len(object_inputs)==951 and len({r['module'] for r in object_inputs})==951
    record['expected_objects']=len(object_inputs)
    for item in object_inputs:
        n=item['module']
        if n in done:continue
        source=Path(item['source']);assert sha(source)==item['sha256']
        out=D/'objects'/Path(*n.split('.'));out.parent.mkdir(parents=True,exist_ok=True);out=Path(str(out)+'.c.o')
        assert not out.exists(),'Unexpected object: do not overwrite partial native output'
        command=[str(R/'bin/leanc.exe'),'-c','-O3','-DNDEBUG','-DLEAN_EXPORTING','-o',str(out),str(source)]
        record['current_operation']='object '+n;save()
        row=guarded(command,'object_'+n,2*GIB,str(D));row.update(module=n,package=item['package'],source_c_file=str(source),source_c_sha256=item['sha256'],object_file=str(out))
        assert sha(source)==item['sha256'],'Native compiler input changed'
        if row['state']=='PASS':
            assert out.exists();names=exports(out);ep=D/'exports'/Path(*n.split('.'));ep.parent.mkdir(parents=True,exist_ok=True);ep=Path(str(ep)+'.json')
            assert not ep.exists();ep.write_text(json.dumps(names,indent=2),encoding='utf8')
            row.update(object_sha256=sha(out),object_bytes=out.stat().st_size,object_allocated_bytes=allocated(out),
              actual_COFF_export_count=len(names),actual_COFF_exports_file=str(ep),actual_COFF_exports_sha256=sha(ep))
            done.add(n)
        record['objects'].append(row);save()
        if row['state']!='PASS':record['status']='OBJECTS_CHECKPOINT';print('OBJECT_STOP',n,row['state'],flush=True);break
        if len(done)%32==0:
            assert source_inventory()==before,'Frozen source/input .oleans changed'
            record['source_and_input_olean_inventory_after']=before;record['last_32_object_checkpoint_utc']=stamp();save()
            print('OBJECT_CHECKPOINT',len(done),'/951','workspace_bytes',workspace_bytes(),'disk_free',shutil.disk_usage(B).free,'physical_free',physical()['available_bytes'],flush=True)
    else:record['status']='OBJECTS_PASS_LINK_AND_INIT_UNTESTED'
record['source_and_input_olean_inventory_after']=source_inventory();assert record['source_and_input_olean_inventory_after']==before
record['isolated_output_inventory']=output_inventory();record['phase_finished_utc']=stamp();record.pop('current_operation',None);save()
print('NATIVE_PREPARATION_STATUS',record['status'],flush=True)
