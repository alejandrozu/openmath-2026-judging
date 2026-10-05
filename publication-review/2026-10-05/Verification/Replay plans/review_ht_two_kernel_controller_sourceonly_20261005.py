"""Read-only independent review facts; never import or invoke the controller."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, os, sys
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
from lean_imports import read_imports
from native_resource_guard import processes
from resource_metrics import snapshot

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
controller=BASE/'run_ht_ramsey_two_kernel_controller_prepared.py'
design=BASE/'ht-ramsey-two-kernel-controller-v2-design-preparation-20261005.json'
manifest_path=BASE/'ht-ramsey-independent2048-kernel-parallel-design-source-manifest-20261005.json'
plan_path=BASE/'builds/htpeo-ramsey-current/build-plan.json'
guard=BASE/'matt_resource_guard.py'
expected={controller:'1994efb38b409b5e12bbec589128c348d110308a49069e656b027100a48ee52e',
          design:'5bb46a012e043eaf97b21823f3d46c7ecef5aa0f36f7cc2b0ce426fd7c1a7070',
          manifest_path:'2c5963c0b5c5094b77206b80d9e02866a504d56991459a2f0ec3bacef147da15',
          plan_path:'94beb20b98cceefe3e5a7aa0a9cec34b4a60c15dd740f675711371a5afd494d3',
          guard:'ae0b64c7fbf47545365f3238977368042be342ddb973159ec65c98f64aa38a71'}
for p,d in expected.items():assert sha(p)==d
source=controller.read_text(encoding='utf8');ast.parse(source)
plan=json.loads(plan_path.read_bytes());manifest=json.loads(manifest_path.read_bytes())
entries={r['module']:r for r in plan['modules']}
assert len(entries)==2103
chunks=set(manifest['independent2048_kernel_chunk_names'])
assert len(chunks)==2048 and chunks=={n for n in entries if '.Chunk.' in n}
imports={}
for n,r in entries.items():
    assert sha(r['file'])==r['sha256']
    imports[n]=[v for v in read_imports(r['file']) if v!='all']
def custom_closure(n,active=None):
    active=set() if active is None else active
    assert n not in active,'custom import cycle'
    active.add(n);answer=set()
    for dep in imports[n]:
        if dep in entries:
            answer.add(dep);answer.update(custom_closure(dep,active))
    active.remove(n);return answer
closure_rows=[];common=set()
for item in manifest['kernel_sources']:
    n=item['module'];actual=custom_closure(n)
    assert n in chunks and imports[n]==item['direct_imports']
    assert sha(entries[n]['file'])==item['source_sha256']
    assert actual==set(item['entire_custom_prerequisite_closure']) and not actual&chunks
    common.update(actual)
    closure_rows.append({'module':n,'source_sha256':entries[n]['sha256'],'custom_prerequisite_count':len(actual)})
assert len(closure_rows)==2048 and len(common)==35
assert not any(v in {'Mathlib','Mathlib.Tactic'} for n in chunks|common for v in imports[n])
assert plan.get('lean_options',{})=={}
facts=[
 {'scope':'Thread-safe own job state', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'guarded_tree creates per-call unnamed job, local suspended Popen/root/thread handles, independent resource-row/seen/counters and unique redirected logs. All Win32 signatures are set at module import, before worker creation. CREATE_SUSPENDED precedes exact job assignment and initial-thread resume. Own job is the only termination target; no foreign process stop.'},
 {'scope':'Single canonical receipt writer', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'Only parent mutates report or calls save_atomic. Worker returns its module/command/guard. ThreadPool completion set may order results nondeterministically, but every append/save runs serially on parent. Immutable SHA-bound old boundary preserves all old rows, flags, CLI and resource provenance.'},
 {'scope':'Exactly two new attempted pilot invocations', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'Pilot allowed limit is 2; parent dispatch condition uses completed attempted count + active-future count. Resource no-attempt does not increment and is retried with the same output-free name after backpressure. Attempted failure counts toward limit and is retained. Exceptions/resource stop can yield fewer than two attempts and a checkpoint; never a full project PASS.'},
 {'scope':'No other Lean mandatory', 'assessment':'PASS_SOURCE_REVIEW_ONLY_WITH_SCHEDULER_BOUNDARY_REQUIREMENT',
  'evidence':'Startup rejects both any own Lean and any foreign Lean, and binds explicit all-other-source-lease-returned root approval. Loop rejects foreign Lean for further dispatch, while owned guarded jobs may finish. Detection is snapshot-based, not an OS-global compiler mutex: actual exclusive scheduler lease must remain valid and a new foreign worker could be observed only on the next loop.'},
 {'scope':'Retained prior own source and output identity', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'SHA-bound finished SCHEDULED_RESOURCE_CHECKPOINT, exact original modules, no failed rows/audits; every old PASS source SHA and complete present artifact set/SHA/size checked. Every new pending chunk must have zero custom outputs. All 2103 source hashes and all chunk import closures are checked before dispatch. No artifacts copied or aliased.'},
 {'scope':'Unchanged source and semantic command', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'Workers compile only frozen chunk source relative to existing stage with -j1, -DmaxHeartbeats=0, -DmaxRecDepth=100000 and original plan lean_options (actual empty). Same original pinned Lean/compiler cache/nine dependency HEADs and origins are verified. New source rows identify this controller and immediate fresh artifact hashes; old rows stay unchanged.'},
 {'scope':'Guard gates and resource accounting', 'assessment':'PASS_SOURCE_REVIEW_ONLY_NOT_EMPIRICAL_PARALLEL_CERTIFICATION',
  'evidence':'Parent and unchanged guard independently require 4GB disk/6GiB free physical/5GiB available commit before each dispatch. Each own job has6GiB private cap and .25s continuous1GB disk/3GiB physical/1GiB commit floors. Two launch checks can observe the same initial available budget before either allocation grows; continuous guards therefore remain necessary and a reserve stop is operational evidence rather than source failure. No global floor or own cap is silently changed.'},
 {'scope':'Source whitelist and no other operation', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'Only 2048 exact .Chunk. names accepted. Nine remaining nonchunk granular sources,11 whole modules and both organizer audits withheld. No source copy/body edit, compaction, deletion, alias, C/library target or cache materialization call appears. Only immutable boundary/guard logs and actual compilation outputs/receipt writes are created if later approved.'},
 {'scope':'Failure and final status fidelity', 'assessment':'PASS_SOURCE_REVIEW_ONLY',
  'evidence':'Known guard stop states become explicit environment/resource checkpoints; exception gives operational checkpoint; nonzero source exit is retained as BUILD_FAILED_OR_TIMED_OUT. Clean pilot and clean completed chunk scope both finish SCHEDULED_RESOURCE_CHECKPOINT, not project PASS. Executor waits for remaining owned future on exit; byte lock released finally.'},
]
line_locators=[]
for needle in ['def sources_ready','assert not lean_registry()','with ThreadPoolExecutor','new_invocations+len(active)>=limit','guarded_tree(command','def save_atomic','report[\'builds\'].append','if stop_reason','def guarded_tree','creationflags=0x08000000','AssignProcessToJobObject','resume_suspended_root','K.TerminateJobObject']:
    candidates=[]
    for label,path in [('controller',controller),('guard',guard)]:
        for i,l in enumerate(path.read_text(encoding='utf8').splitlines(),1):
            if needle in l:candidates.append({'file':label,'line':i})
    line_locators.append({'needle':needle,'locations':candidates})
registry=processes()
live=[{'pid':pid,**r} for pid,r in registry.items() if r['exe'].lower()=='lean.exe']
receipt={'status':'NO_BLOCKING_BUG_FOUND_BOUNDED_INDEPENDENT_SOURCE_REVIEW_NOT_EXECUTION_APPROVAL',
    'created_utc':datetime.now(timezone.utc).isoformat(),'reviewed_source_hashes':{p.name:d for p,d in expected.items()},
    'review_producer_sha256':sha(__file__),'full_controller_and_guard_and_design_read':True,
    'independent_source_checks':{'all_original_sources_checked':2103,'independent_kernel_sources_checked':2048,
        'shared_complete_custom_prerequisite_count':35,'no_chunk_to_chunk_edges':True,
        'no_literal_Mathlib_or_Tactic_in_exact_custom_scope':True,
        'official_transitive_umbrella_absence':'Bound original source manifest design; this review did not repeat the full official-provider closure scan.',
        'common_prerequisites':sorted(common),'chunk_source_rows':closure_rows},
    'assessments':facts,'line_locators':line_locators,'blocking_findings':[],
    'dated_non_dispatch_resource_snapshot':snapshot(),'dated_current_Lean_processes':live,
    'current_dispatch_qualification':False,
    'qualification':'A valid later SHA-bound explicit root approval, actual quiescent serial boundary, all other source workers returned and fresh gates are mandatory. Current source-only review is neither authorization nor empirical thread/parallel-proof qualification.',
    'actual_operations':{'controller_imports':0,'proof_invocations':0,'aliases':0,'source_edits':0,'compactions':0,'canonical_receipt_writes':0,
       'writes':'Only this independent review producer and uniquely dated additive review JSON.'}}
target=BASE/('ht-two-kernel-controller-independent-source-review-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'.json')
with target.open('x',encoding='utf8') as f:json.dump(receipt,f,indent=2);f.flush();os.fsync(f.fileno())
print(json.dumps({'record':str(target),'sha256':sha(target),'status':receipt['status'],'all_sources':2103,'chunks':2048,'shared':35,'live_Lean_count':len(live),'blocking_findings':[]}))
