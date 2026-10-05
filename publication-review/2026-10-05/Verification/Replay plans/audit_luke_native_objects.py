"""Read-only actual COFF ABI/export audit, after all isolated objects succeed.

No linker/plugin action is performed. Export directives' ,data attributes are
retained in input files and normalized only for symbol-provider comparisons.
"""
from pathlib import Path
import collections,datetime,hashlib,json,mmap,os,re,struct
from receipt_io import read_bytes_shared

B=Path(__file__).resolve().parent
R=B/'runtimes/lean-4.34.1-windows'
snapshot=read_bytes_shared(B/'luke-native-isolated-preparation.json');receipt=json.loads(snapshot)
assert receipt['status']=='OBJECTS_PASS_LINK_AND_INIT_UNTESTED','Actual complete object preparation required'
assert len([r for r in receipt['objects'] if r['state']=='PASS'])==951

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        while part:=f.read(1024*1024):h.update(part)
    return h.hexdigest()
def coff(p):
    d=Path(p).read_bytes();machine,n,_,ptr,count,sizeopt,_=struct.unpack_from('<HHIIIHH',d,0)
    assert machine==0x8664,'Unexpected x64 COFF ABI'
    st=ptr+18*count;length=struct.unpack_from('<I',d,st)[0]
    assert st+length<=len(d),'Invalid COFF string table'
    sections={}
    for j in range(n):
        at=20+sizeopt+40*j
        size,ptr,relocptr,_,nrelocs,_,flags=struct.unpack_from('<IIIIHHI',d,at+16)
        sections[j+1]={'size':size,'ptr':ptr,'relocptr':relocptr,'nrelocs':nrelocs,'flags':flags}
    def symbol_name(index):
        raw=d[ptr_symbols+18*index:ptr_symbols+18*index+8]
        if raw[:4]==b'\0'*4:
            off=struct.unpack_from('<I',raw,4)[0];end=d.index(b'\0',st+off);return d[st+off:end].decode('utf8')
        return raw.rstrip(b'\0').decode('utf8')
    # The section loop uses raw-data pointers; recover the original symbol-table pointer.
    ptr_symbols=struct.unpack_from('<I',d,8)[0]
    defined=set();undefined=set();weak=set();definition_sections={};comdat_selection={};i=0
    while i<count:
        at=ptr_symbols+18*i;raw=d[at:at+8]
        if raw[:4]==b'\0'*4:
            off=struct.unpack_from('<I',raw,4)[0];end=d.index(b'\0',st+off);name=d[st+off:end].decode('utf8')
        else:name=raw.rstrip(b'\0').decode('utf8')
        value,section,ty,storage,aux=struct.unpack_from('<IhHBB',d,at+8)
        if storage==2:
            if section!=0 or value!=0:
                defined.add(name);definition_sections[name]=section
            else:undefined.add(name)
        elif storage==105:weak.add(name)
        elif storage==3 and section>0 and aux>0 and (sections[section]['flags']&0x1000):
            comdat_selection[section]=d[at+18+14]
        i+=1+aux
    entries=[]
    for i in range(n):
        at=20+sizeopt+40*i;name=d[at:at+8].rstrip(b'\0').decode('ascii');size,ptr=struct.unpack_from('<II',d,at+16)
        if name=='.drectve':entries.extend(re.findall(r'-export:([^ ]+)',d[ptr:ptr+size].decode('ascii')))
    exports={entry.split(',')[0] for entry in entries}
    assert len(exports)==len(entries),'Duplicated export directives'
    assert exports<=defined,'Export directive without a corresponding object definition'
    verified_refptr_comdat={}
    for name,section in definition_sections.items():
        if name.startswith('.refptr.') and section>0:
            sec=sections[section]
            if sec['flags']&0x1000 and comdat_selection.get(section)==2 and sec['size']==8 and sec['nrelocs']==1:
                virtual,index,kind=struct.unpack_from('<IIH',d,sec['relocptr'])
                target=symbol_name(index)
                if virtual==0 and kind==1 and target==name[len('.refptr.'):] and d[sec['ptr']:sec['ptr']+8]==b'\0'*8:
                    verified_refptr_comdat[name]=target
    return defined,undefined,exports,weak,entries,verified_refptr_comdat
def archive_symbols(p):
    with Path(p).open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as d:
        assert d[:8]==b'!<arch>\n';at=8
        while at+60<=len(d):
            name=d[at:at+16].decode('ascii').strip();size=int(d[at+48:at+58]);start=at+60
            if name=='/':
                n=struct.unpack_from('>I',d,start)[0];names=start+4+4*n
                assert names<=start+size
                return {s.decode('utf8') for s in d[names:start+size].split(b'\0') if s}
            at=start+size+(size%2)
    return set()

closure=json.loads((B/'luke_isolated_native_symbol_closure.json').read_text(encoding='utf8'))
flags=closure['official_metadata_flags']['shared_ldflags']['stdout']
libnames=set(re.findall(r'(?:^|\s)-l([^\s]+)',flags))
libraries=[];missing_libraries=[];runtime_defs=set()
for name in sorted(libnames):
    candidates=[R/'lib/lean'/('lib'+name+'.dll.a'),R/'lib/lean'/('lib'+name+'.a'),R/'lib'/('lib'+name+'.dll.a'),R/'lib'/('lib'+name+'.a')]
    found=[p for p in candidates if p.exists()]
    if not found:missing_libraries.append(name);continue
    p=found[0];names=archive_symbols(p);runtime_defs.update(names)
    libraries.append({'library_flag':'-l'+name,'file':str(p),'bytes':p.stat().st_size,'sha256':sha(p),'archive_index_symbol_count':len(names)})
# Compiler-rt is selected by the exact bundled Clang wrapper rather than an explicit -l flag.
for p in (R/'lib/clang').rglob('libclang_rt.builtins-x86_64.a'):
    names=archive_symbols(p);runtime_defs.update(names)
    libraries.append({'library_flag':'bundled compiler-rt builtins','file':str(p),'bytes':p.stat().st_size,'sha256':sha(p),'archive_index_symbol_count':len(names)})

providers=collections.defaultdict(set);rows=[];groups={'non_mathlib':set(),'mathlib_custom':set()};group_definitions={'non_mathlib':set(),'mathlib_custom':set()}
for row in receipt['objects']:
    if row['state']!='PASS':continue
    p=Path(row['object_file']);assert sha(p)==row['object_sha256'];assert sha(row['source_c_file'])==row['source_c_sha256']
    defined,undefined,exported,weak,entries,refptr_comdat=coff(p)
    archived=json.loads(Path(row['actual_COFF_exports_file']).read_text(encoding='utf8'))
    assert sorted(entries)==archived and sha(row['actual_COFF_exports_file'])==row['actual_COFF_exports_sha256']
    group='mathlib_custom' if row['package'] in ['mathlib','custom-default-none'] else 'non_mathlib'
    groups[group].update(exported);group_definitions[group].update(defined)
    for symbol in defined:providers[symbol].add(row['module'])
    rows.append({'module':row['module'],'package':row['package'],'group':group,'object_sha256':row['object_sha256'],
      'defined':defined,'undefined':undefined,'exports':exported,'weak':weak,'export_directive_count':len(entries),
      'verified_refptr_comdat':refptr_comdat,
      'data_export_count':sum(',data' in e for e in entries)})
all_defs=set(providers);duplicates={s:sorted(mods) for s,mods in providers.items() if len(mods)>1}
unresolved={};cross_group_hidden={};reverse={}
by_module={row['module']:row for row in rows}
permitted_refptr_duplicates={s:mods for s,mods in duplicates.items() if all(s in by_module[m]['verified_refptr_comdat'] for m in mods)}
hard_duplicates={s:mods for s,mods in duplicates.items() if s not in permitted_refptr_duplicates}
for row in rows:
    for s in row['undefined']:
        source_providers=providers.get(s,set())
        other={m for m in source_providers if by_module[m]['group']!=row['group']}
        if other and s not in groups['non_mathlib' if row['group']=='mathlib_custom' else 'mathlib_custom']:
            cross_group_hidden.setdefault(s,set()).add(row['module'])
        if row['group']=='non_mathlib' and any(by_module[m]['group']=='mathlib_custom' for m in source_providers):
            reverse.setdefault(s,set()).add(row['module'])
        if s not in all_defs and s not in runtime_defs:unresolved.setdefault(s,set()).add(row['module'])
dependency_snapshot=json.loads((B/'luke_native_dependency_artifact_snapshot.json').read_text(encoding='utf8'))
changed_deps=[]
for filename,item in dependency_snapshot['records'].items():
    p=Path(filename)
    if not p.exists() or p.stat().st_size!=item['bytes'] or sha(p)!=item['sha256']:changed_deps.append(filename)

count=next(row for row in rows if row['module']=='K4Ramsey.Constructions.Final3840.Count')
count_input=next(row for row in receipt['objects'] if row['module']=='K4Ramsey.Constructions.Final3840.Count')
count_c=Path(count_input['source_c_file']).read_text(encoding='utf8')
count_entries=coff(Path(count_input['object_file']))[4]
count_data_exports={entry.split(',')[0] for entry in count_entries if ',data' in entry}
closed_cache_rows=[]
for cache in ['bCache','dCache','pathsCache']:
    symbol='l_K4Ramsey_Final3840_Count_'+cache
    closed_cache_rows.append({'cache':cache,'symbol':symbol,'actual_COFF_data_export':symbol in count_data_exports,
      'C_global_representation_is_lean_object_pointer':('LEAN_EXPORT lean_object* '+symbol+';') in count_c,
      'initializer_assigns_generated_value':(symbol+' = _init_'+symbol+'();') in count_c,
      'initializer_marks_value_persistent':('lean_mark_persistent('+symbol+');') in count_c})
root_init='initialize_K4Ramsey_Constructions_Final3840_Count'
required_count={'l_K4Ramsey_Final3840_Count_'+name for name in ['baseRoot','triangleAt','cycleAt','diamondAt','tetrahedronAt','bCache','dCache','pathsCache']}
required_count.add(root_init)
result={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ACTUAL_OBJECT_AUDIT_COMPLETE_LINK_AND_INITIALIZATION_UNTESTED',
  'scope':'Read-only x64 COFF definitions/undefined references/export directives and exact pinned import-library indexes; no DLL link, load, initializer execution, numerical count, or theorem certification',
  'preparation_receipt_sha256':hashlib.sha256(snapshot).hexdigest(),'source_commit':receipt['source_commit'],'lean_version':receipt['lean_version'],
  'mathlib_pin':receipt['mathlib_pin'],'object_count':len(rows),'all_objects_x64_COFF':True,'all_source_and_object_hashes_match':True,
  'preserved_prior_held_object_attempts':[r for r in receipt['objects'] if r['state']!='PASS'],
  'native_cluster_actual_export_counts':{k:len(v) for k,v in groups.items()},'windows_export_limit_per_DLL':65535,
  'both_clusters_within_export_limit':all(len(v)<65535 for v in groups.values()),
  'unresolved_non_COMDAT_definition_collisions':hard_duplicates,
  'verified_compiler_generated_COMDAT_reference_pointer_duplicates':permitted_refptr_duplicates,
  'COMDAT_acceptance_rule':'Each accepted .refptr definition has actual IMAGE_SCN_LNK_COMDAT, selection ANY=2, an 8-byte zero relocation slot, and exactly one AMD64_ADDR64 relocation to the matching target; not merely a prefix-based exception.',
  'cross_cluster_hidden_symbol_references':{k:sorted(v) for k,v in cross_group_hidden.items()},
  'non_mathlib_to_mathlib_custom_reverse_references':{k:sorted(v) for k,v in reverse.items()},
  'strong_undefined_symbols_not_in_object_or_pinned_library_indexes':{k:sorted(v) for k,v in unresolved.items()},
  'missing_explicit_link_flag_libraries':missing_libraries,'required_Count_functions_initializer_and_caches_exported':required_count<=count['exports'],
  'actual_Count_package_prefix':'l_','actual_Count_initializer':root_init,'root_initializer_is_a_real_object_definition':root_init in count['defined'],
  'Count_closed_cache_global_representation':closed_cache_rows,
  'all_Count_closed_cache_data_cases_match':all(all(v for k,v in row.items() if k not in ['cache','symbol']) for row in closed_cache_rows),
  'Final3840_integerNum_not_present_in_this_frozen_module':'integerNum' not in count_c,
  'closed_constant_lookup_notice':'Pinned ir_interpreter.cpp constant evaluation dereferences an exported object-pointer data slot after complete initialization (object **); function-address selection alone would not justify these closed caches. Actual DLL loading/initializer completion remains untested in this object-only receipt.',
  'official_dependency_artifacts_byte_identical_to_dated_snapshot':not changed_deps,'changed_official_dependency_artifacts':changed_deps,
  'pinned_linker_libraries':libraries,'normalization_note':'COFF export entries retain ,data attributes in per-object archives; provider comparisons use the exact symbol before the comma.',
  'remaining_holds':['Actual two-DLL links and import-library output','Actual complete initializer execution before imports in a fresh process','Actual native Count dispatch evidence','Original unchanged numerical certificate execution','Endpoint axiom audit with the declared native trust boundary'],
  'objects':[{'module':r['module'],'package':r['package'],'group':r['group'],'object_sha256':r['object_sha256'],
    'defined_symbol_count':len(r['defined']),'strong_undefined_symbol_count':len(r['undefined']),'weak_symbol_count':len(r['weak']),
    'actual_export_count':len(r['exports']),'data_export_count':r['data_export_count']} for r in rows]}
p=B/'luke-native-isolated-object-ABI-audit.json';assert not p.exists();tmp=p.with_suffix('.json.tmp')
with tmp.open('w',encoding='utf8') as f:json.dump(result,f,indent=2);f.flush();os.fsync(f.fileno())
os.replace(tmp,p)
print(json.dumps({k:v for k,v in result.items() if k not in ['objects','pinned_linker_libraries']},indent=2))
