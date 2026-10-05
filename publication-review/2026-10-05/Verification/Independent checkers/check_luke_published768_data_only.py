"""Exact known768 certificate recount from literal data, no entrant code execution.

Uses ordinary arbitrary-precision integer adjacency bitsets. The accompanying
finite checks compare the balanced-blow-up formula with a literal tuple sum.
They supplement the ordinary equality-pattern argument, not a Lean proof.
"""
from pathlib import Path
import argparse,datetime,hashlib,itertools,json,math,os,re,shutil,time
from fractions import Fraction

BASE=Path(__file__).resolve().parent
SOURCE_SHA='b5de696edd6947b5da2250b466e5eead3e9ff3ee8818cc197a6bbc8c651f3494'
from native_resource_guard import memory
from luke_native_source_guard import counters

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def finite_counts(rows,guard=None):
    n=len(rows);edges=triangles=cliques=loops=0
    for i in range(n):
        if guard and i%16==0:guard()
        later=rows[i]&~((1<<(i+1))-1)
        edges+=later.bit_count()
        while later:
            one=later&-later;j=one.bit_length()-1;later-=one
            common=rows[i]&rows[j]&~((1<<(j+1))-1)
            triangles+=common.bit_count()
            while common:
                one=common&-common;k=one.bit_length()-1;common-=one
                cliques+=(rows[k]&common).bit_count();loops+=1
    return {'unordered_edges':edges,'unordered_triangles':triangles,'unordered_four_cliques':cliques,'common_vertex_iterations':loops}

def complement(rows):
    n=len(rows);mask=(1<<n)-1
    return [(~r)&mask&~(1<<i) for i,r in enumerate(rows)]

def formula(n,red,blue):
    return n+14*blue['unordered_edges']+36*blue['unordered_triangles']+24*(red['unordered_four_cliques']+blue['unordered_four_cliques'])

def small_checks():
    pairs=list(itertools.combinations(range(4),2));checked=0
    for colors in range(1<<len(pairs)):
        rows=[0]*4
        for bit,(i,j) in enumerate(pairs):
            if colors&(1<<bit):rows[i]|=1<<j;rows[j]|=1<<i
        red=finite_counts(rows);blue=finite_counts(complement(rows))
        literal=sum(len({bool(rows[t[i]]&(1<<t[j])) for i,j in pairs})==1
                    for t in itertools.product(range(4),repeat=4))
        assert formula(4,red,blue)==literal
        checked+=1
    return {'two_color_graphs_checked':checked,'literal_ordered_tuples_per_graph':4**4,
            'purpose':'Finite corroboration of the ordinary equality-pattern identity; not universal Lean theorem certification.'}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',default=str(BASE/'builds/luke-k4-ramsey-current-native/K4Ramsey/Constructions/Published768/Data.lean'))
    parser.add_argument('--receipt',default=str(BASE/'luke-published768-independent-data-count.json'))
    parser.add_argument('--prepare-only',action='store_true')
    args=parser.parse_args();source=Path(args.source);target=Path(args.receipt)
    assert sha(source)==SOURCE_SHA
    text=source.read_text(encoding='utf8');rows=[]
    for body in re.findall(r'^\s+#\[(.*)\],?\s*$',text,re.M):
        tokens=re.findall(r'\(0x([0-9a-f]{16}) : UInt64\)',body)
        assert len(tokens)==12
        assert not re.sub(r'\(0x[0-9a-f]{16} : UInt64\)|[\s,]','',body)
        rows.append(sum(int(word,16)<<(64*w) for w,word in enumerate(tokens)))
    assert len(rows)==768
    assert all(not(r&(1<<i)) and r.bit_length()<=768 for i,r in enumerate(rows))
    assert all(bool(rows[i]&(1<<j))==bool(rows[j]&(1<<i)) for i in range(768) for j in range(i))
    estimate={'parsed_source_sha256':SOURCE_SHA,'row_count':768,'working_integer_row_bit_storage_upper_bound_bytes':2*768*96,
              'combined_common_vertex_iteration_upper_bound':math.comb(768,3),'counts_use_python_arbitrary_precision':True,
              'no_entrant_executable_or_Lean_compiler_or_DLL_load':True,'arithmetic_worker_threads':1}
    if args.prepare_only:print(json.dumps(estimate,indent=2));return
    assert not target.exists(),'Preserve every independently attempted receipt'
    started=datetime.datetime.now(datetime.timezone.utc).isoformat();begin=time.monotonic()
    minima={};samples=0
    def guard():
        nonlocal samples
        c=counters();samples+=1
        for k,v in c.items():minima[k]=min(minima.get(k,v),v)
        assert c['disk_free_bytes']>=1_000_000_000,'Independent recount disk reserve'
        assert c['physical_available_bytes']>=3*1024**3,'Independent recount physical reserve'
        assert c['available_commit_bytes']>=1024**3,'Independent recount commit reserve'
        assert memory(os.getpid())['private_bytes']<256*1024**2,'Independent recount memory bound'
    guard();checks=small_checks();red=finite_counts(rows,guard);blue=finite_counts(complement(rows),guard)
    numerator=formula(768,red,blue);denominator=768**4
    assert red['unordered_edges']==148608 and numerator==10487165184
    assert red['unordered_edges']+blue['unordered_edges']==math.comb(768,2)
    assert red['common_vertex_iterations']+blue['common_vertex_iterations']<=math.comb(768,3)
    density=Fraction(numerator,denominator)
    assert density==Fraction(4551721,150994944)
    assert 10486266368<numerator
    guard();own_memory=memory(os.getpid())
    record={'status':'PASS_INDEPENDENT_EXACT_KNOWN_CERTIFICATE_DATA_RECOUNT',
        'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'seconds':round(time.monotonic()-begin,6),'script_sha256':sha(__file__),'input_source':str(source),**estimate,
        'red':red,'blue':blue,'numerator':numerator,'denominator':denominator,
        'reduced_density_numerator':density.numerator,'reduced_density_denominator':density.denominator,
        'decimal_density':str(float(density)),'mckay_known_numerator':10486266368,'mckay_is_strictly_smaller':True,
        'guard_minimum_counters':minima,'guard_samples':samples,'peak_rss_bytes':own_memory['peak_rss_bytes'],
        'current_private_bytes':own_memory['private_bytes'],'finite_small_graph_checks':checks,
        'ordinary_identity_argument':'Blue diagonal blocks give n for all four equal; each unordered blue edge gives 8 tuples of multiplicity3+1 and6 of2+2; each blue triangle gives36 of2+1+1; each red or blue four-clique gives24 distinct ordered tuples. These exhaust the equality partitions of four positions.',
        'scope_notice':'An independent exact data recount and ordinary mathematical argument for the known768 certificate. Does not replace source replay, establish new Ramsey priority, or make the submitted universal formula-to-tuple equivalence Lean-proved.'}
    assert sha(source)==SOURCE_SHA
    temp=target.with_suffix('.tmp')
    with temp.open('wb') as f:f.write(json.dumps(record,indent=2).encode('utf8'));f.flush();os.fsync(f.fileno())
    os.replace(temp,target)
    print(json.dumps(record,indent=2),flush=True)

if __name__=='__main__':main()
