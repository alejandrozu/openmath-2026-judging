"""Read-only native route metadata audit. Never invokes Lean/C compilation or linking."""
from pathlib import Path
import collections,datetime,hashlib,json,mmap,os,re,struct,subprocess,time
base=Path(__file__).resolve().parent
plan=json.loads((base/'builds/luke-k4-ramsey-current-direct/build-plan.json').read_text(encoding='utf8'))
prior=json.loads((base/'luke_selective_native_readonly_assessment.json').read_text(encoding='utf8'))
runtime=base/'runtimes/lean-4.34.1-windows'
started=time.monotonic()
symbol=r'(?:lp_|l_|(?:runtime_|meta_)?initialize_)\w+'
export_re=re.compile(r'^LEAN_EXPORT[^\n{;]*?\b('+symbol+r')(?=\s*(?:\(|;|=))',re.M)
ref_re=re.compile(r'\b('+symbol+r')\b')
static_re=re.compile(r'^static[^\n]*?\b('+symbol+r')(?=\s*(?:\(|;|=))',re.M)
c_nondcode_re=re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|/\*[\s\S]*?\*/|//[^\n]*')
def pe_exports(path):
    with path.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as m:
        pe=struct.unpack_from('<I',m,0x3c)[0];assert m[pe:pe+4]==b'PE\0\0'
        nsects=struct.unpack_from('<H',m,pe+6)[0];sizeopt=struct.unpack_from('<H',m,pe+20)[0]
        opt=pe+24;magic=struct.unpack_from('<H',m,opt)[0]
        directories=opt+(112 if magic==0x20b else 96)
        er,es=struct.unpack_from('<II',m,directories)
        if er==0:return set()
        sections=[]
        for n in range(nsects):
            at=opt+sizeopt+40*n
            virtualsize,va,size,offset=struct.unpack_from('<IIII',m,at+8)
            sections.append((va,max(virtualsize,size),offset))
        def off(rva):
            for va,size,offset in sections:
                if va<=rva<va+size:return offset+rva-va
            raise ValueError('unmapped PE RVA')
        e=off(er);nn=struct.unpack_from('<I',m,e+24)[0];names=off(struct.unpack_from('<I',m,e+32)[0])
        exports=set()
        for n in range(nn):
            p=off(struct.unpack_from('<I',m,names+4*n)[0]);end=m.find(b'\0',p)
            exports.add(m[p:end].decode('ascii'))
        return exports

core_symbols=set();dll_records=[]
for p in sorted((runtime/'bin').glob('*.dll')):
    if p.name not in ['libInit_shared.dll','libLake_shared.dll','libleanshared.dll','libleanshared_1.dll','libleanshared_2.dll']:continue
    exports=pe_exports(p);core_symbols.update(exports)
    dll_records.append({'file':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exported_names':len(exports)})
print('Pinned core DLL export names',len(core_symbols),flush=True)
registry={};providers=collections.defaultdict(set);duplicates=[]
for lib in plan['dependency_library_paths']:
    ir=Path(lib).parent.parent/'ir'
    for p in ir.rglob('*.c'):
        text=p.read_text(encoding='utf8')
        match=re.search(r'^// Module: (.+)$',text,re.M)
        if not match:continue
        module=match.group(1).strip()
        imports=re.search(r'^// Imports: (.*)$',text,re.M)
        children=re.findall(r'(?:public |meta )*import (?:all )?([A-Za-z0-9_.]+)',imports.group(1)) if imports else []
        exports=set(export_re.findall(text))
        if module in registry:duplicates.append(module)
        registry[module]={'path':p,'bytes':p.stat().st_size,'imports':children,'exports':exports}
        for name in exports:providers[name].add(module)
    print('Indexed native C metadata',ir,'modules so far',len(registry),flush=True)
assert not duplicates,duplicates
selected=set();missing_imports=set()
def visit(module):
    if module in selected:return
    if module not in registry:
        if not module.startswith(('Init','Std','Lean','Lake')):missing_imports.add(module)
        return
    selected.add(module)
    for child in registry[module]['imports']:visit(child)
for module in prior['direct_mathlib_imports']:visit(module)
unresolved={};rounds=0
while True:
    extra=set();unresolved={};rounds+=1
    selected_exports=set().union(*(registry[m]['exports'] for m in selected))
    for module in sorted(selected):
        text=registry[module]['path'].read_text(encoding='utf8')
        local=registry[module]['exports']|set(static_re.findall(text))
        code=c_nondcode_re.sub(' ',text)
        refs=set(ref_re.findall(code))-local-selected_exports-core_symbols
        for name in refs:
            options=providers.get(name,set())
            if len(options)==1:extra.update(options-selected)
            elif len(options)>1:unresolved.setdefault(name,set()).add(module+' (ambiguous provider)')
            else:unresolved.setdefault(name,set()).add(module)
    if not extra:break
    for module in sorted(extra):visit(module)
    print('Symbol-closure expansion round',rounds,'added',len(extra),'selected',len(selected),flush=True)
records=[];packages=collections.Counter();allexports=set()
for module in sorted(selected):
    item=registry[module];p=item['path'];raw=p.read_bytes()
    package=next((Path(lib).parents[3].name for lib in plan['dependency_library_paths'] if p.is_relative_to(Path(lib).parent.parent/'ir')),'unknown')
    packages[package]+=1;allexports.update(item['exports'])
    records.append({'module':module,'package':package,'file':str(p),'bytes':item['bytes'],'sha256':hashlib.sha256(raw).hexdigest(),'exported_symbol_count':len(item['exports']),'imports':item['imports']})
header=(runtime/'include/lean/lean.h').read_text(encoding='utf8')
inline_api=set(re.findall(r'(?:static\s+(?:inline|LEAN_INLINE))[^;{}]*?\b(lean_\w+)\s*\(',header))
inline_api.update(re.findall(r'^\s*#define\s+(lean_\w+)\s*\(',header,re.M))
runtime_api=set();unresolved_runtime_api={};reverse_package_refs={};group_exports={'non_mathlib':set(),'mathlib':set()}
mathmods={r['module'] for r in records if r['package']=='mathlib'}
for r in records:
    module=r['module'];text=c_nondcode_re.sub(' ',registry[module]['path'].read_text(encoding='utf8'))
    group_exports['mathlib' if module in mathmods else 'non_mathlib'].update(registry[module]['exports'])
    calls=set(re.findall(r'\b(lean_\w+)\s*\(',text));runtime_api.update(calls)
    for name in calls-core_symbols-inline_api:
        unresolved_runtime_api.setdefault(name,set()).add(module)
    if module not in mathmods:
        reverse_imports=[name for name in registry[module]['imports'] if name.startswith('Mathlib.')]
        reverse_symbols=[name for name in set(ref_re.findall(text))-registry[module]['exports']-set(static_re.findall(text)) if providers.get(name,set())&mathmods]
        if reverse_imports or reverse_symbols:reverse_package_refs[module]={'imports':reverse_imports,'symbols':sorted(reverse_symbols)}
flags={}
# These exact metadata branches return before Leanc.main can spawn clang/linker.
for key,args in [('cflags',['--print-cflags']),('shared_ldflags',['-shared','--print-ldflags'])]:
    result=subprocess.run([str(runtime/'bin/leanc.exe'),*args],capture_output=True,text=True,encoding='utf8')
    assert result.returncode==0
    flags[key]={'command':[str(runtime/'bin/leanc.exe'),*args],'exit':result.returncode,'stdout':result.stdout.strip(),'stderr':result.stderr}
out={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PREPARED_READONLY_SYMBOL_AUDIT','source_commit':plan['commit'],'mathlib_pin':plan['mathlib_pin'],'lean_version':plan['version'],
    'no_compiler_or_linker_invoked':True,'active_lean_count_unchanged':True,'semantic_scope':'Native operational retry plan only; not a theorem proof or successful native link',
    'core_dlls':dll_records,'core_export_name_count':len(core_symbols),'indexed_generated_c_modules':len(registry),'selected_generated_c_modules':len(selected),'selected_c_source_bytes':sum(r['bytes'] for r in records),
    'selected_modules_by_package':dict(packages),'selected_exported_symbol_count':len(allexports),'single_windows_dll_export_count_limit':65535,
    'single_aggregate_export_count_below_limit':len(allexports)<65535,'missing_noncore_import_modules':sorted(missing_imports),'unresolved_prefixed_symbols':{k:sorted(v) for k,v in sorted(unresolved.items())},
    'unresolved_prefixed_symbol_count':len(unresolved),'closure_expansion_rounds':rounds,'official_metadata_flags':flags,'LEAN_CC_environment_override_present':bool(os.environ.get('LEAN_CC')),
    'selected_lean_runtime_api_calls':sorted(runtime_api),'header_inline_or_macro_api_count':len(inline_api),
    'unresolved_runtime_api_calls':{k:sorted(v) for k,v in sorted(unresolved_runtime_api.items())},
    'native_partition_exports':{k:len(v) for k,v in group_exports.items()},'non_mathlib_reverse_dependencies':reverse_package_refs,
    'selected_exports_also_in_core_dlls':sorted(allexports & core_symbols),
    'selected_export_names_with_multiple_source_providers':{k:sorted(v & selected) for k,v in providers.items() if len(v & selected)>1},
    'two_cluster_dag_is_lexically_acyclic':not reverse_package_refs,
    'two_cluster_note':'Prospective first DLL contains non-Mathlib generated C; second contains Mathlib plus source-identical custom computation C and links the first through a generated import library. Both must retain emitted initializers; custom C/export count and actual link/init need a later guarded pilot.',
    'prospective_object_args':['leanc.exe','-c','-O3','-DNDEBUG','-DLEAN_EXPORTING','-o','ISOLATED_OBJECT.c.o','OFFICIAL_UNMODIFIED.c'],
    'prospective_link_args':['leanc.exe','-shared','-o','ISOLATED_CLUSTER.dll','@EXACT_OBJECT_RESPONSE_FILE'],
    'linking_caveat':'Official wrapper adds the pinned runtime libraries and internal toolchain flags; an actual bounded link must still reject unresolved symbols. Generated-C prototypes are conservative overapproximations, and uncompiled custom-module C is not yet available for this lexical audit.',
    'initialization_caveat':'Every emitted runtime/meta/legacy initializer must be resolved and called; --load-dynlib alone is insufficient. No initializer stub, source rewrite or omission is proposed.',
    'records':records,'seconds':round(time.monotonic()-started,3)}
p=base/'luke_isolated_native_symbol_closure.json';tmp=p.with_suffix('.json.tmp')
with tmp.open('w',encoding='utf8') as f:json.dump(out,f,indent=2);f.flush();os.fsync(f.fileno())
os.replace(tmp,p)
print(json.dumps({k:v for k,v in out.items() if k not in ['records','core_dlls','unresolved_prefixed_symbols','official_metadata_flags']}),flush=True)
if unresolved:print('First unresolved names',list(unresolved)[:30],flush=True)
