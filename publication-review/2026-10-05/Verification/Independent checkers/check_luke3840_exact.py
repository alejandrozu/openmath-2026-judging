"""Independent data-only exact 3840-class objective recount.

No entrant program is executed. NumPy int64 is used only below proved overflow
bounds; all larger combinations are Python integers. This does not certify Lean.
Usage: python check_luke3840_exact.py --pilot
       python check_luke3840_exact.py
       python check_luke3840_exact.py --inputs luke3840_exact_inputs.npz
"""
from pathlib import Path
import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):
    os.environ[name]='1'
import argparse,ctypes,datetime,hashlib,json,math,re,shutil,time
import numpy as np

parser=argparse.ArgumentParser()
parser.add_argument('--pilot',action='store_true')
parser.add_argument('--inputs',type=Path)
args=parser.parse_args()
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'builds/luke-k4-ramsey-current-direct/K4Ramsey/Constructions/Final3840'
REPORT=HERE/('luke3840_independent_exact_pilot.json' if args.pilot else 'luke3840_independent_exact_recount.json')
Q=65536
EXPECTED=519196432373018212667371525712277942005760
EXPECTED_NUM=8450462766487926638466333426306607129
EXPECTED_DEN=280384030360880691940646801777885184000
LIMIT=2**63
started=time.monotonic()
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
class MemoryCounters(ctypes.Structure):
    _fields_=[('cb',ctypes.c_ulong),('PageFaultCount',ctypes.c_ulong),
        ('PeakWorkingSetSize',ctypes.c_size_t),('WorkingSetSize',ctypes.c_size_t),
        ('QuotaPeakPagedPoolUsage',ctypes.c_size_t),('QuotaPagedPoolUsage',ctypes.c_size_t),
        ('QuotaPeakNonPagedPoolUsage',ctypes.c_size_t),('QuotaNonPagedPoolUsage',ctypes.c_size_t),
        ('PagefileUsage',ctypes.c_size_t),('PeakPagefileUsage',ctypes.c_size_t)]
if os.name=='nt':
    kernel=ctypes.WinDLL('kernel32',use_last_error=True);psapi=ctypes.WinDLL('psapi',use_last_error=True)
    kernel.GetCurrentProcess.restype=ctypes.c_void_p
    process_handle=kernel.GetCurrentProcess()
    memory_fn=psapi.GetProcessMemoryInfo;memory_fn.argtypes=[ctypes.c_void_p,ctypes.c_void_p,ctypes.c_ulong]
def memory():
    if os.name!='nt':return {'measurement':'Windows peak RSS unavailable on this platform'}
    item=MemoryCounters();item.cb=ctypes.sizeof(item)
    assert memory_fn(process_handle,ctypes.byref(item),item.cb)
    return {'rss_bytes':item.WorkingSetSize,'peak_rss_bytes':item.PeakWorkingSetSize,
        'private_bytes':item.PagefileUsage,'peak_private_bytes':item.PeakPagefileUsage}
receipt={'started_utc':stamp(),'status':'PREPARING','method':'Independent frozen-data centered expansion with vertex permutation multiplicities and rigorously bounded int64 limb contractions; arbitrary-size Python integer recombination',
    'not_lean_verification':True,'entrant_executable_invoked':False,'floating_point_used':False,
    'process_and_thread_policy':'One process; all BLAS/OMP environment worker settings set to 1; no extra Python worker threads',
    'resource_policy':{'minimum_free_bytes':1_000_000_000,'maximum_rss_bytes':256*1024**2,'wall_seconds_limit':900},'phases':[]}
def save():
    receipt['seconds']=round(time.monotonic()-started,4);receipt['memory']=memory()
    temp=REPORT.with_suffix('.json.tmp')
    with temp.open('w',encoding='utf8') as f:json.dump(receipt,f,indent=2);f.flush();os.fsync(f.fileno())
    for attempt in range(60):
        try:os.replace(temp,REPORT);break
        except PermissionError:
            if attempt==59:raise
            time.sleep(.1)
last_guard=0.0
def guard(force=False):
    global last_guard
    now=time.monotonic()
    if not force and now-last_guard<.25:return
    last_guard=now
    available=shutil.disk_usage(HERE).free
    receipt['minimum_observed_free_bytes']=min(receipt.get('minimum_observed_free_bytes',available),available)
    mem=memory()
    if available<1_000_000_000 or mem.get('peak_rss_bytes',0)>256*1024**2 or now-started>900:
        receipt['status']='ENVIRONMENT_BLOCKED_RESOURCE_GUARD';receipt['finished_utc']=stamp();save()
        raise SystemExit('Independent recount stopped by its own resource guard')
def phase(name,**fields):
    guard(True);receipt['phases'].append({'name':name,'utc':stamp(),**fields});save();print(name,fields,flush=True)

def base_value(u,v):
    a=u//64==v//64;e=u//32%2==v//32%2;s=u//16%2==v//16%2
    z=(u%16)^(v%16);inside=z in (0,1,2,4,8,15);zero_type=0 if inside else Q
    if not s:return (51064 if inside else 0) if a else zero_type
    if a:return zero_type if e else (35139 if z==0 else (Q if inside else 0))
    return (Q if inside else 0) if e else zero_type
base=np.array([[base_value(i,j) for j in range(192)] for i in range(192)],dtype=np.int64)
hashes={}
if args.inputs:
    with np.load(args.inputs,allow_pickle=False) as payload:
        index=payload['block_index'].copy();blocks=payload['blocks'].copy()
    receipt['portable_input_sha256']=hashlib.sha256(args.inputs.read_bytes()).hexdigest()
else:
    plan=json.loads((SOURCE.parents[2]/'build-plan.json').read_text(encoding='utf8'))
    expected={Path(item['file']).resolve():item['sha256'] for item in plan['modules']}
    raw=(SOURCE/'Data.lean').read_bytes()
    for p in [SOURCE/'Data.lean',SOURCE/'Model.lean',SOURCE/'Count.lean',SOURCE/'Certificate.lean',SOURCE/'Symmetry.lean',SOURCE/'SymmetryProof.lean',SOURCE/'Arithmetic.lean',*sorted((SOURCE/'Data').glob('Part*.lean'))]:
        data=p.read_bytes();digest=hashlib.sha256(data).hexdigest()
        assert digest==expected[p.resolve()],str(p)+' differs from the frozen source plan'
        hashes[str(p.relative_to(SOURCE))]=digest
    index=np.fromstring(re.search(r'def blockIndexText : String := "([0-9,]+)"',raw.decode('utf8')).group(1),sep=',',dtype=np.int64).reshape(192,192)
    values=[]
    for p in sorted((SOURCE/'Data').glob('Part*.lean')):
        guard()
        values.extend(np.fromstring(s,sep=',',dtype=np.int64) for s in re.findall(r'"([0-9,]+)"',p.read_text(encoding='utf8')))
    blocks=np.array(values).reshape(-1,20,20)
    del values
    receipt['source_commit']=plan['commit'];receipt['source_hashes']=hashes
assert index.dtype==np.int64 and blocks.dtype==np.int64
assert index.shape==(192,192) and blocks.shape==(1248,20,20)
assert int(index.min())==0 and int(index.max())==1248 and int(blocks.min())>=0 and int(blocks.max())<=Q
support=(base!=0)&(base!=Q)
assert np.all(base==base.T) and not np.any(np.diag(support))
assert np.all(np.tril(index)==0)
assert np.array_equal((index>0),np.triu(support,1))
edges=[(i,j) for i in range(192) for j in range(i+1,192) if support[i,j]]
assert len(edges)==1248 and sorted(int(index[i,j]) for i,j in edges)==list(range(1,1249))
delta={(i,j):blocks[index[i,j]-1]-base[i,j] for i,j in edges}
zero=np.zeros((20,20),dtype=np.int64)
for matrix in delta.values():
    guard();assert np.all(matrix.sum(axis=0)==0) and np.all(matrix.sum(axis=1)==0)
M=max(int(np.abs(matrix).max()) for matrix in delta.values())
assert M<=Q
def d(i,j):
    if i<j:return delta.get((i,j),zero)
    if i>j:return delta.get((j,i),zero).T
    return zero
neighbors=[set(np.flatnonzero(support[i]).tolist()) for i in range(192)]
triangles=[];tetrahedra=[]
for i,j in edges:
    for k in sorted(neighbors[i]&neighbors[j]):
        if k<=j:continue
        triangles.append((i,j,k))
        for l in sorted(neighbors[i]&neighbors[j]&neighbors[k]):
            if l>k:tetrahedra.append((i,j,k,l))
assert len(triangles)==1152 and len(tetrahedra)==288
counts={'ordered_triangles':6*len(triangles),'ordered_tetrahedra':24*len(tetrahedra),'canonical_path_matrices':0,'ordered_paths':0,'ordered_cycles':0,'ordered_diamonds':0}
for i in range(192):
    guard()
    for j in range(i,192):
        common=neighbors[i]&neighbors[j];n=len(common);multiplicity=1 if i==j else 2
        counts['canonical_path_matrices']+=n;counts['ordered_paths']+=multiplicity*n
        counts['ordered_cycles']+=multiplicity*n*n
        if support[i,j]:counts['ordered_diamonds']+=multiplicity*n*n
assert counts=={'ordered_triangles':6912,'ordered_tetrahedra':6912,'canonical_path_matrices':17472,'ordered_paths':32448,'ordered_cycles':161472,'ordered_diamonds':36864}
# Check the full finite base transitivity used to multiply a root count by 192.
for i in range(192):
    guard()
    perm=np.array([((i//64+j//64)%3)*64+((i//32%2)^(j//32%2))*32+((i//16%2)^(j//16%2))*16+((i%16)^(j%16)) for j in range(192)])
    assert perm[0]==i and len(set(perm.tolist()))==192
    assert np.array_equal(base[np.ix_(perm,perm)],base)
receipt['integer_bounds']={
    'maximum_absolute_centered_entry':M,'path_20M2':20*M**2,'triangle_8000M3':8000*M**3,
    'triangle_coefficient_192Q3':192*Q**3,'triple_edge_product_M3':M**3,
    'base_triple_Q3':Q**3,'tetra_or_base_limb_dot_160000R20sq':160000*(2**20)**2,
    'cycle_limb_dot_400R13sq':400*(2**13)**2,
    'diamond_limb_dot_400MR13sq':400*M*(2**13)**2,'int64_limit_exclusive':LIMIT}
assert all(value<LIMIT for key,value in receipt['integer_bounds'].items() if key!='int64_limit_exclusive')
receipt['multiplicity_checks']=counts
phase('payload_and_overflow_bounds_checked',peak_rss_bytes=memory().get('peak_rss_bytes'))

def limbs(array,shift):
    radix=1<<shift
    result=[array%radix,(array//radix)%radix,array//(radix*radix)]
    assert max(int(np.abs(v).max()) for v in result)<radix
    # Exact reconstruction: original values fit int64 and reconstruction stays bounded.
    assert np.array_equal(array,result[0]+radix*result[1]+radix*radix*result[2])
    return result
def exact_dot(a,b,shift=20,weight=None):
    aa=limbs(a.reshape(-1),shift);bb=limbs(b.reshape(-1),shift);radix=1<<shift
    if weight is None:
        bound=a.size*radix**2
    else:
        bound=a.size*radix**2*int(np.abs(weight).max())
    assert bound<LIMIT
    total=0
    for r,x in enumerate(aa):
        for s,y in enumerate(bb):
            guard()
            value=np.dot(x if weight is None else x*weight.reshape(-1),y)
            total+=int(value)*radix**(r+s)
    return total
paths={}
def path(i,j,k):
    if i>j:return path(j,i,k).T
    key=(i,j,k)
    if key not in paths:
        guard();paths[key]=d(i,k)@d(j,k).T
        assert int(np.abs(paths[key]).max())<=20*M**2
    return paths[key]
def tetra_arrays(i,j,k,l):
    a=d(i,j)[:,:,None,None]*d(i,k)[:,None,:,None]*d(i,l)[:,None,None,:]
    b=d(j,k)[None,:,:,None]*d(j,l)[None,:,None,:]*d(k,l)[None,None,:,:]
    assert a.shape==(20,20,20,20)
    # b has a singleton first dimension and is broadcast across it without copying.
    return a,np.broadcast_to(b,a.shape)

# A bounded pilot confirms signed limb arithmetic against plain Python big integers.
t0=time.monotonic();first=tetrahedra[0];aa,bb=tetra_arrays(*first)
fast=exact_dot(aa,bb)
reference=int(np.sum(aa.astype(object)*bb.astype(object)))
assert fast==reference
i,j,k=triangles[0];p=path(i,j,k)
for weight,shift in [(None,13),(d(i,j),13)]:
    fast_pair=exact_dot(p,p,shift,weight)
    plain=sum(int(x)*int(y)*(1 if weight is None else int(z)) for x,y,z in zip(p.reshape(-1),p.reshape(-1),(np.ones((20,20),dtype=np.int64) if weight is None else weight).reshape(-1)))
    assert fast_pair==plain
pilot_seconds=time.monotonic()-t0
phase('small_contraction_pilot_pass',tetrahedron=first,pilot_seconds=round(pilot_seconds,4),one_tetrahedron_exact_value=str(fast),independent_python_big_integer_comparison=True)
del aa,bb
if args.pilot:
    receipt['status']='PILOT_PASS_NO_FULL_RECOUNT';receipt['finished_utc']=stamp();save();raise SystemExit(0)

receipt['status']='RUNNING'
if not args.inputs:
    input_path=HERE/'luke3840_exact_inputs.npz'
    temp=input_path.with_suffix('.npz.tmp')
    with temp.open('wb') as f:np.savez_compressed(f,block_index=index,blocks=blocks);f.flush();os.fsync(f.fileno())
    os.replace(temp,input_path)
    receipt['portable_input_file']=input_path.name;receipt['portable_input_sha256']=hashlib.sha256(input_path.read_bytes()).hexdigest()
    manifest={'created_utc':stamp(),'source_commit':receipt['source_commit'],'source_hashes':hashes,
        'numeric_input_file':input_path.name,'numeric_input_sha256':receipt['portable_input_sha256'],
        'numeric_input_shapes':{'block_index':[192,192],'blocks':[1248,20,20]},
        'base_definition':'Literal Model.lean baseNumerator: Q=65536; fractional values 51064 and 35139; full formula reproduced in check_luke3840_exact.py',
        'script_file':Path(__file__).name,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'expected_raw_numerator':str(EXPECTED),'expected_reduced_density':[str(EXPECTED_NUM),str(EXPECTED_DEN)],
        'method_scope':'Independent integer recount of source-defined rational weighted graphon, including repeated labels; does not replace Lean replay','pickle_used':False}
    mp=HERE/'luke3840_exact_inputs_manifest.json';mt=mp.with_suffix('.json.tmp')
    with mt.open('w',encoding='utf8') as f:json.dump(manifest,f,indent=2);f.flush();os.fsync(f.fileno())
    os.replace(mt,mp)

base_root=0
for w in (base,Q-base):
    c=w[0]
    for j in range(192):
        guard()
        a=(int(c[j])*c[:,None])*c[None,:]
        b=w[j,:,None]*w[j,None,:]*w
        assert int(a.max())<=Q**3 and int(b.max())<=Q**3
        base_root+=exact_dot(a,b)
base_term=160000*192*base_root
phase('base_root_recount_complete',root_red_plus_blue=str(base_root),raw_base_contribution=str(base_term))

triangle_sum=0
for i,j,k in triangles:
    guard()
    p=path(i,j,k)
    tri=int(np.sum(d(i,j)*p))
    coefficient=int(np.sum(base[i]*base[j]*base[k]-(Q-base[i])*(Q-base[j])*(Q-base[k])))
    triangle_sum+=coefficient*tri
triangle_at_sum=120*triangle_sum
phase('triangles_complete',triangleAt_sum=str(triangle_at_sum),unordered_triangles=len(triangles))

cycle_at_sum=0;diamond_at_sum=0
for i in range(192):
    guard()
    for j in range(i,192):
        common=sorted(neighbors[i]&neighbors[j]);mi=1 if i==j else 2
        for kr,k in enumerate(common):
            pk=path(i,j,k)
            for l in common[kr:]:
                guard();ml=1 if k==l else 2;pl=path(i,j,l)
                cyc=exact_dot(pk,pl,13)
                coef=int(base[i,j])*int(base[k,l])+(Q-int(base[i,j]))*(Q-int(base[k,l]))
                cycle_at_sum+=mi*ml*coef*cyc
                if support[i,j]:
                    dia=exact_dot(pk,pl,13,d(i,j))
                    diamond_at_sum+=mi*ml*(2*int(base[k,l])-Q)*dia
    if i%32==31:print('cycle/diamond coarse rows',i+1,'of 192',flush=True)
assert len(paths)==17472
phase('cycles_and_diamonds_complete',cycleAt_sum=str(cycle_at_sum),diamondAt_sum=str(diamond_at_sum),path_cache_bytes=sum(a.nbytes for a in paths.values()))

tetra_sum=0
for n,vertices in enumerate(tetrahedra):
    guard();aa,bb=tetra_arrays(*vertices)
    tetra_sum+=exact_dot(aa,bb)
    del aa,bb
    if n%32==31:print('unordered tetrahedra',n+1,'of',len(tetrahedra),flush=True)
tetra_at_sum=48*tetra_sum
phase('tetrahedra_complete',tetrahedronAt_sum=str(tetra_at_sum),unordered_tetrahedra=len(tetrahedra))

total=base_term+4*triangle_at_sum+3*cycle_at_sum+6*diamond_at_sum+tetra_at_sum
denominator=Q**6*3840**4;g=math.gcd(total,denominator)
num=total//g;den=denominator//g
receipt.update({'raw_numerator':str(total),'raw_denominator':str(denominator),
    'reduced_density_numerator':str(num),'reduced_density_denominator':str(den),
    'raw_numerator_matches_submitted_claim':total==EXPECTED,
    'reduced_density_matches_submitted_claim':num==EXPECTED_NUM and den==EXPECTED_DEN,
    'contributions':{'base':str(base_term),'four_triangle':str(4*triangle_at_sum),
        'three_cycle':str(3*cycle_at_sum),'six_diamond':str(6*diamond_at_sum),'tetrahedron':str(tetra_at_sum)},
    'status':'PASS_MATCH' if total==EXPECTED and num==EXPECTED_NUM and den==EXPECTED_DEN else 'FAIL_DISAGREEMENT',
    'finished_utc':stamp(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
save();print(receipt['status'],total,'/',denominator,'peak RSS',receipt['memory'].get('peak_rss_bytes'),flush=True)
raise SystemExit(0 if receipt['status']=='PASS_MATCH' else 1)
