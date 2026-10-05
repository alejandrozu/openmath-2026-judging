"""Read-only actual seed file identity + PE import evidence. No DLL/process loading."""
from pathlib import Path
import hashlib,json,struct,datetime,importlib.util
V=Path(__file__).resolve().parent
SEED=V/'isolated-header-pilots/root-r141-header-seed-20261005-0913/actual-seed.json'
OUTER=V/'root-HT-official-header-seed-93768-actual-outer-controller-exit0-20261005.json'
RUNTIME=V/'runtimes/lean-4.33.1-windows'
SYSTEM=Path('C:/Windows/System32')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
 return h.hexdigest()
def binding(p):
 p=Path(p).resolve();st=p.stat()
 return {'file':str(p),'sha256':sha(p),'bytes':st.st_size,'mtime_ns':st.st_mtime_ns,'native_stat_file_id':st.st_ino}
def bound_json(p,wanted):
 assert sha(p)==wanted,str(p)
 return json.loads(Path(p).read_bytes())
s=bound_json(SEED,'a466829aff3ae9182471fcd8cb7c00041909b91fca6c077ff05af0da66790aab')
o=bound_json(OUTER,'803d32ee4e0793d546fd5cbcef64593dc731a84664b363e39dabc9f8e857a44d')
assert o['actual_seed_receipt_sha256']==sha(SEED) and o['actual_controller_exit_code']==0
pehelper=V/'native_PE_tools.py';assert sha(pehelper)=='0a6a1fa29c2f2ac1a01e2bb45109be2203807434c32be873f93294a9df6ee016'
spec=importlib.util.spec_from_file_location('readonly_PE',pehelper);pe=importlib.util.module_from_spec(spec);spec.loader.exec_module(pe)
positive=s['loaded_image_observation']['observed_loaded_images'];conservative=s['conservative_native_library_inventory']
assert len(positive)==37 and len(conservative)==20
verified=[];before={}
for role,rows in [('positive_sampled_image',positive),('conservative_candidate_not_claimed_loaded',conservative)]:
 for old in rows:
  p=Path(old['file']).resolve();now=binding(p)
  assert all(now[k]==old[k] for k in ('sha256','bytes','mtime_ns','native_stat_file_id')),(role,str(p))
  before[str(p).lower()]=now;verified.append({'role':role,**now,'matches_all_recorded_identity_fields':True})
observed={Path(x['file']).name.lower():Path(x['file']).resolve() for x in positive}
assert len(observed)==37
# Parse only read-only bytes from installed API-set schema, not a process PEB or a loader call.
apifile=SYSTEM/'apisetschema.dll';apibinding=binding(apifile);allapi=apifile.read_bytes()
# This Windows schema image has a zero-function export directory; the older
# helper expects at least one export RVA. Read its section table directly.
apipeoff=struct.unpack_from('<I',allapi,0x3c)[0];assert allapi[apipeoff:apipeoff+4]==b'PE'+bytes(2)
apimachine,apicount=struct.unpack_from('<HH',allapi,apipeoff+4);assert apimachine==0x8664
apiopt=apipeoff+24;apisizeopt=struct.unpack_from('<H',allapi,apipeoff+20)[0]
api_sections=[]
for i in range(apicount):
 a=apiopt+apisizeopt+40*i;vs,va,bs,bo=struct.unpack_from('<IIII',allapi,a+8)
 api_sections.append({'name':allapi[a:a+8].rstrip(bytes(1)).decode('ascii'),'raw_offset':bo,'raw_bytes':bs})
sec=next(x for x in api_sections if x['name']=='.apiset');data=allapi[sec['raw_offset']:sec['raw_offset']+sec['raw_bytes']]
version,size,flags,count,entries,hashoff,hashfactor=struct.unpack_from('<IIIIIII',data,0)
assert version==6 and size<=len(data) and count<=4096
namespaces={};namespace_prefixes={}
def u16(off,n):
 assert off+n<=size and n%2==0
 return data[off:off+n].decode('utf-16-le')
for i in range(count):
 fl,no,nl,hashed,vo,vc=struct.unpack_from('<IIIIII',data,entries+24*i);assert vo+20*vc<=size
 vals=[]
 for j in range(vc):
  vf,ao,al,ho,hl=struct.unpack_from('<IIIII',data,vo+20*j)
  vals.append({'alias':u16(ao,al).lower() if al else '', 'host':u16(ho,hl).lower() if hl else '', 'flags':vf})
 name=u16(no,nl).lower();assert name not in namespaces;namespaces[name]=vals
 prefix=u16(no,hashed).lower();namespace_prefixes.setdefault(prefix,[]).append(name)
assert len(namespaces)==count
used_contracts={};unresolved=[];parse_failures=[];cache={}
def delayed_imports(path):
 d=Path(path).read_bytes();npe=struct.unpack_from('<I',d,0x3c)[0];n=struct.unpack_from('<H',d,npe+6)[0];so=struct.unpack_from('<H',d,npe+20)[0];opt=npe+24
 assert struct.unpack_from('<H',d,opt)[0]==0x20b
 base=struct.unpack_from('<Q',d,opt+24)[0];numdirs=struct.unpack_from('<I',d,opt+108)[0]
 if numdirs<=13:return []
 rv,sz=struct.unpack_from('<II',d,opt+112+8*13)
 if not rv:return []
 def offset(r):
  for i in range(n):
   a=opt+so+40*i;vs,va,bs,bo=struct.unpack_from('<IIII',d,a+8)
   if va<=r<va+max(vs,bs):assert r-va<bs;return bo+r-va
  raise ValueError('unresolved PE delay RVA')
 def string(r):
  pos=offset(r);return d[pos:d.index(b'\0',pos)].decode('ascii')
 vals=[];at=offset(rv)
 for i in range(max(1,sz//32)):
  fields=struct.unpack_from('<IIIIIIII',d,at+32*i)
  if not any(fields):break
  attrs,name,*rest=fields;assert attrs in (0,1)
  vals.append(string(name if attrs else name-base))
 return vals
# Ordinary resolution is observed path first, then pinned executable directory,
# then explicit System32. Unobserved paths are labelled static candidates.
def resolve(dll,importer):
 name=dll.lower();contract=name.removesuffix('.dll')
 if name.startswith(('api-','ext-')):
  vals=namespaces.get(contract);matched_name=contract;prefix_fallback=False
  if vals is None:
   candidates=namespace_prefixes.get(contract.rsplit('-',1)[0],[])
   if len(candidates)!=1:return [],{'kind':'UNRESOLVED_API_SET','contract':contract,'hashed_prefix_candidates':candidates}
   matched_name=candidates[0];vals=namespaces[matched_name];prefix_fallback=True
  alias=Path(importer).name.lower();matching=[v for v in vals if v['alias'] in (alias,alias.removesuffix('.dll')) and v['host']]
  selected=matching or [v for v in vals if not v['alias'] and v['host']]
  used_contracts[contract]={'requested_contract':contract,'matched_namespace_entry':matched_name,'namespace_hashed_prefix_fallback_candidate':prefix_fallback,'values':vals}
  targets=[]
  for v in selected:
   host=v['host'];p=observed.get(host) or SYSTEM/host
   if p.is_file():targets.append(p.resolve())
  return targets,{'kind':'API_SET_SCHEMA_V6_HASHED_PREFIX_STATIC_HOST_CANDIDATE' if prefix_fallback else 'API_SET_SCHEMA_V6_EXACT_STATIC_HOST','contract':contract,'matched_namespace_entry':matched_name,'hashed_prefix_fallback_candidate':prefix_fallback,'schema_values':vals,'selected_alias_or_default':selected,'actual_process_API_namespace_not_read':True}
 if name in observed:return [observed[name]],{'kind':'ACTUAL_POSITIVELY_SAMPLED_PATH'}
 for p,kind in ((RUNTIME/'bin'/dll,'PINNED_RUNTIME_STATIC_CANDIDATE'),(SYSTEM/dll,'EXPLICIT_SYSTEM32_STATIC_CANDIDATE')):
  if p.is_file():return [p.resolve()],{'kind':kind,'not_claimed_loaded':True}
 return [],{'kind':'UNRESOLVED_ORDINARY_DLL','dll':dll}
def inspect(p):
 key=str(p).lower()
 if key not in cache:
  obj=pe.inspect_pe(p)
  cache[key]={'file':obj['file'],'sha256':obj['sha256'],'bytes':obj['bytes'],'x64_PE32_plus':obj['x64_PE32_plus'],'is_DLL':obj['is_DLL'],
   'eager_imports':{n:len(v) for n,v in obj['imports'].items()},'delay_load_names_potential_only':delayed_imports(p),
   'named_export_forwarder_count':sum(x['forwarder'] is not None for x in obj['exports'].values()),
   'export_forwarders_are_not_expanded_as_whole_library_dependencies':True}
 return cache[key]
def graph(roots,label):
 todo=list(roots);done={};edges=[]
 while todo:
  p=todo.pop();key=str(p).lower()
  if key in done:continue
  assert len(done)<512,'Bounded static graph unit cap'
  try:info=inspect(p)
  except Exception as e:
   parse_failures.append({'label':label,'file':str(p),'error':repr(e)});continue
  done[key]=info
  for dll in info['eager_imports']:
   targets,how=resolve(dll,p)
   edge={'importer':str(p),'imported_name':dll,'import_kind':'PE_ORDINARY_EAGER_TABLE','symbol_count':info['eager_imports'][dll],'resolution':how,'targets':[str(t) for t in targets]}
   edges.append(edge)
   if not targets:unresolved.append({'label':label,**edge})
   else:todo.extend(targets)
  # Delay-load names are recorded but cannot prove activation and are not mandatory eager edges.
 return {'label':label,'roots':[str(p) for p in roots],'units':list(done.values()),'edges':edges,'units_count':len(done),'edge_count':len(edges),
  'static_unobserved_units':[x['file'] for x in done.values() if Path(x['file']).name.lower() not in observed]}
core=[Path(x['file']).resolve() for x in positive if Path(x['file']).resolve().is_relative_to(RUNTIME)]
assert len(core)==5
coregraph=graph(core,'five_positive_Lean_runtime_images_eager_import_graph')
allgraph=graph([Path(x['file']).resolve() for x in positive],'all37_positive_images_static_eager_import_graph')
# Preserve exact observed errors and interval information without attributing cause.
g=s['own_job_resource_receipt'];start=datetime.datetime.fromisoformat(g['started_utc']);end=datetime.datetime.fromisoformat(g['finished_utc'])
errors=[]
for e in s['loaded_image_observation']['toolhelp_errors']:
 t=datetime.datetime.fromisoformat(e['checked_utc']);errors.append({**e,'seconds_after_guard_start':(t-start).total_seconds(),'seconds_before_guard_finish':(end-t).total_seconds(),'cause_not_proved':True})
assert len(errors)==4 and s['loaded_image_observation']['successful_toolhelp_snapshots']==287
source_specs=[('Lean/Shell.lean',[(216,240),(413,432),(540,557)]),('Lean/Elab/Frontend.lean',[(279,313)]),('Lean/LoadDynlib.lean',[(27,38),(56,71),(74,108)]),('Lean/Environment.lean',[(2438,2449)])]
locators=[]
for rel,ranges in source_specs:
 p=RUNTIME/'src/lean'/rel;lines=p.read_text(encoding='utf-8').splitlines()
 locators.append({**binding(p),'ranges':[{'first_line':a,'last_line':z,'text':'\n'.join(lines[a-1:z])} for a,z in ranges]})
assert s['command']==g['command'] and s['actual_owned_child_exit']==0 and g['state']=='PASS'
assert s['literal_LEAN_NUM_THREADS']=='2' and s['plan_additional_lean_options']=={}
for a in s['command'][1:]:assert not a.startswith(('--plugin','-p','--load-dynlib','-l','--setup','-u','--trust','-t','--incr-header-load','--incr-load'))
installation=bound_json(V/'lean-4.33.1-installation.json','6ec3927af9b76cdb46a8fe74773113e72bee65066a4b7decf4547b646f39f99a')
assert installation['complete'] and installation['sha256']=='f63029c0e1e6daed0f4807481b6fcd8f8b77fbce6d63f205c7f9191072387a7a'
# Recheck all originally recorded image identities after pure graph reads.
for before_item in before.values():assert binding(before_item['file'])==before_item
assert sha(SEED)=='a466829aff3ae9182471fcd8cb7c00041909b91fca6c077ff05af0da66790aab' and sha(OUTER)=='803d32ee4e0793d546fd5cbcef64593dc731a84664b363e39dabc9f8e857a44d'
record={'status':'ACTUAL_SEED_POSITIVE_RUNTIME_IMAGE_AND_STATIC_LIBRARY_IDENTITY_READONLY_EVIDENCE_WITH_OBSERVER_GAPS',
 'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'producer':binding(__file__),'actual_seed':binding(SEED),'root_actual_outer_exit':binding(OUTER),'pure_PE_helper':binding(pehelper),
 'pinned_runtime_release_installation':binding(V/'lean-4.33.1-installation.json'),'runtime_release_asset_sha256':installation['sha256'],'recorded_compiler_identity':installation['compiler_check'],
 'counts':{'positive_snapshots':287,'positive_distinct_image_files':37,'positive_pinned_Lean_runtime_images':5,'positive_System32_images':32,'conservative_runtime_candidates':20,'conservative_logical_bytes':sum(x['bytes'] for x in conservative),'observer_errors_preserved':4},
 'all_recorded_images_and_candidates_current_identity_checks':verified,'before_and_after_file_identity_equal':True,
 'five_runtime_positive_image_bindings':[binding(p) for p in core],'API_set_schema_file':apibinding,'API_set_namespace_version':version,'API_set_namespace_contracts_count':count,'API_set_contracts_encountered':used_contracts,'prior_exact_contract_only_assessment':binding(V/'HT-R141-actual-seed-runtime-library-fidelity-readonly-evidence-20261005.json'),
 'five_Lean_runtime_eager_PE_graph':coregraph,'all37_positive_static_PE_graph':allgraph,'PE_unresolved_static_edges':unresolved,'PE_parse_failures':parse_failures,
 'actual_command':s['command'],'literal_LEAN_NUM_THREADS':s['literal_LEAN_NUM_THREADS'],'exact_scientific_options_unchanged':True,
 'CLI_plugin_dynlib_setup_snapshot_load_or_trust_override_present':False,'pinned_default_trust_level_not_claimed_zero':True,'local_primary_source_locators':locators,
 'original_four_WinError299_observations':errors,'actual_guard_seconds':g['seconds'],'positive_evidence_assessment':[
 'The exact recorded lean.exe and four Lean shared DLL files were positively observed during the actual seed and all five still match their recorded SHA, byte size,mtime and file identity.',
 'All37 observed image files and all20 conservative native candidates were independently rehashed before and after this read-only inspection; no file replacement or content drift was detected.',
 'PE ordinary import tables and the installed hashed API-set schema provide a static file identity graph; this is concrete additional evidence, not a replacement for the four missing ToolHelp observations.',
 'The literal command uses the same pinned executable,j2/env2/scientific options and no plugin,dynlib,setup,snapshot-load or trust override. Pinned shell passes an empty plugin array and absentsetup; arbitrary initializer/body native effects are outside this CLI-only observation.'
 ],
 'limitations':[
 'Four WinError299 calls remain preserved, including one near startup and three near the final fraction of a second; their cause is not established.',
 '287 positive snapshots are sampled evidence, not a complete continuous loader trace. This record cannot exclude every transient or final-interval module load.',
 'PE imports are static; delay-load names are potential, not evidence of activation. Named export forwarders and arbitrary runtime LoadLibrary calls are not a complete symbol-level/dynamic trace.',
 'API-set hosts are read from installed System32schema, not the exited process PEB. Where imported minor revisions differ, a unique schema HashedLength prefix yields a labelled static host candidate; this does not independently prove the operating system lookup algorithm or exited-process resolution. Unobserved paths remain static candidates.',
 'Positive runtime DLL identity and static PE graph do not qualify serialized source/region closure or selected theorem axioms. PhaseB needs its independently reviewed source/region/own-output identities and separately approved exact same-file load.',
 'System DLL fidelity is to the actual seed observations/current host files, not the Lean upstream release. No Windows system DLL is claimed part of the Lean release.',
 'No Lean,guard,process census,DLL loader,snapshot loader,compiler,or executable was invoked by this assessment.'
 ],'full_continuous_loader_trace_proved':False,'snapshot_load_authorization_or_success_inferred':False,'seed_canonical_source_output_hold_lease_or_runtime_mutated':False}
out=V/'HT-R141-actual-seed-runtime-library-fidelity-api-prefix-readonly-evidence-20261005.json';assert not out.exists();out.write_bytes((json.dumps(record,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
print(json.dumps({'record':str(out),'sha256':sha(out),'counts':record['counts'],'core_graph_units':coregraph['units_count'],'allpositive_graph_units':allgraph['units_count'],'unresolved':len(unresolved),'parse_failures':len(parse_failures)}),flush=True)
