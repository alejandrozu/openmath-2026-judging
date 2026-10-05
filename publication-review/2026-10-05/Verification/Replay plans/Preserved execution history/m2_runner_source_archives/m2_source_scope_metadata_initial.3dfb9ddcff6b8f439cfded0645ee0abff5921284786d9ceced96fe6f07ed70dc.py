"""Read-only all-eight-M2 exact source DAG, including custom dependency libraries."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
from lean_imports import read_imports,stripped
BASE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(path,value):
    temp=path.with_suffix(path.suffix+'.tmp');temp.write_text(json.dumps(value,ensure_ascii=False,indent=2),encoding='utf8');os.replace(temp,path)
inventory_file=BASE/'m2-novel-formalization-source-scope-inventory-20261005.json'
inventory=json.loads(inventory_file.read_text(encoding='utf8'));assert len(inventory['projects'])==8
oldtotal=sum(p['source_modules']-p['whole_scope_count_including_additional_libraries'] for p in inventory['projects']);assert oldtotal==600
prep=json.loads((BASE/'original-E65-source-replay-preparation-20261005.json').read_text(encoding='utf8'))
runtime=BASE/'runtimes/lean-4.33.1-windows';assert sha(runtime/'bin/lean.exe')==prep['compiler_binary_sha256']
roots=[{'id':'official_lean_core','source_root':runtime/'src/lean','pin':'4.33.1;819816b2e0a3bf405af45ae5c7af2491d8f5bee6'},
 {'id':'official_lean_lake','source_root':runtime/'src/lean/lake','pin':'4.33.1;819816b2e0a3bf405af45ae5c7af2491d8f5bee6'}]
for package in prep['exact_original_nine_packages']:
    head=subprocess.run(['git','rev-parse','HEAD'],cwd=package['prepared_source_path'],capture_output=True,text=True,check=True).stdout.strip()
    assert head==package['original_manifest_rev']
    roots.append({'id':package['name'],'source_root':Path(package['prepared_source_path']),'pin':head})
canonical=lambda name:name.replace('«','').replace('»','')
official={};official_unsafe={};official_visiting=set()
def provider(name):
    if name in official:return official[name]
    rel=Path(name.replace('.','/')+'.lean')
    found=[(r,r['source_root']/rel) for r in roots if (r['source_root']/rel).is_file()]
    assert len(found)==1,('OFFICIAL_SOURCE_RESOLUTION',name,found)
    root,file=found[0];code=stripped(file.read_text(encoding='utf8'))
    direct=list(dict.fromkeys(d for d in read_imports(file) if d!='all'))
    prelude=bool(re.search(r'^\s*prelude\s*$',code,re.M));implicit=name!='Init' and not prelude and 'Init' not in direct
    row={'module':name,'source_file':str(file),'source_sha256':sha(file),'identity_root':root['id'],'exact_pin':root['pin'],
      'literal_source_imports':direct,'prelude':prelude,'implicit_Init_added':implicit,
      'effective_import_dependencies':direct+(['Init'] if implicit else [])}
    official[name]=row
    if len(official)%1000==0:print('M2_PINNED_OFFICIAL_SOURCE_NODES',len(official),flush=True)
    return row
def unsafe_official(name):
    if name in official_unsafe:return official_unsafe[name]
    assert name not in official_visiting,('OFFICIAL_IMPORT_CYCLE',name)
    official_visiting.add(name);row=provider(name);found={name} if name in {'Mathlib','Mathlib.Tactic'} else set()
    for dep in row['effective_import_dependencies']:found.update(unsafe_official(dep))
    official_visiting.remove(name);official_unsafe[name]=found;return found
projects=[];contexts=[]
for old in inventory['projects']:
    plan_file=BASE/'builds'/old['id']/'build-plan.json';assert sha(plan_file)==old['plan_sha256']
    plan=json.loads(plan_file.read_text(encoding='utf8'));assert plan['version']=='4.33.1' and plan['mathlib_pin']==prep['exact_original_nine_packages'][0]['original_manifest_rev']
    own={canonical(r['module']):r for r in plan['modules']};assert len(own)==old['source_modules']
    all_custom=dict(own);additional_plans=[]
    for rawdir in plan.get('additional_dependency_libs',[]):
        additional=Path(rawdir);additional_file=additional/'build-plan.json'
        extra=json.loads(additional_file.read_text(encoding='utf8'))
        assert extra['version']=='plan' or extra['version']=='4.33.1' if False else extra['version']=='4.33.1'
        assert extra['mathlib_pin']==plan['mathlib_pin']
        additional_plans.append({'project_id':extra['id'],'source_plan_sha256':sha(additional_file),'source_count':len(extra['modules'])})
        for row in extra['modules']:all_custom.setdefault(canonical(row['module']),row)
    source_nodes={}
    for n,row in all_custom.items():
        file=Path(row['file']);assert sha(file)==row['sha256'],(old['id'],n,'SOURCE_SHA')
        source_nodes[n]={'module':n,'source_file':str(file),'source_sha256':row['sha256'],'literal_imports':read_imports(file),
          'effective_lean_options':row.get('lean_options',plan.get('lean_options',{})) if n in own else None,
          'own_source':n in own}
    memo={};visiting=set();closure_memo={}
    def custom_class(n):
        if n in memo:return memo[n]
        assert n not in visiting,('CUSTOM_IMPORT_CYCLE',old['id'],n)
        visiting.add(n);bad=set();closure={n};row=source_nodes[n]
        for dep in row['literal_imports']:
            if dep in source_nodes:
                bad.update(custom_class(dep));closure.update(closure_memo[dep])
            else:bad.update(unsafe_official(dep))
        # Every authored/custom source in these frozen plans has implicit Init.
        bad.update(unsafe_official('Init'))
        visiting.remove(n);memo[n]=bad;closure_memo[n]=closure;return bad
    for n in source_nodes:custom_class(n)
    old_whole=set(old['transitive_whole_Mathlib_scope_including_additional_libraries'])
    nominal=set(own)-old_whole
    assert len(nominal)==old['source_modules']-old['whole_scope_count_including_additional_libraries']
    safe_own={n for n in own if not memo[n]};whole_own=set(own)-safe_own
    newly_held=nominal-safe_own
    assert old_whole<=whole_own,(old['id'],'OLD_WHOLE_NOT_REDERIVED',old_whole-whole_own)
    safe_custom={n for n in source_nodes if not memo[n]}
    assert all(closure_memo[n]<=safe_custom for n in safe_custom)
    external_needed=set().union(*(closure_memo[n]-set(own) for n in safe_own)) if safe_own else set()
    external_unbuilt={n for n in external_needed if not Path(source_nodes[n]['source_file']).with_suffix('.olean').is_file()}
    immediate_own={n for n in safe_own if not (closure_memo[n]&external_unbuilt)}
    rows=[]
    for n in own:
        own_direct=source_nodes[n]['literal_imports']
        responsible={dep:sorted(memo[dep] if dep in source_nodes else unsafe_official(dep)) for dep in own_direct
            if (memo[dep] if dep in source_nodes else unsafe_official(dep))}
        rows.append({**source_nodes[n],'nominal_historical_granular':n in nominal,'whole_Mathlib_or_Tactic_official_roots':sorted(memo[n]),
          'resource_classification':'SOLE10_11_MATHLIB_OR_TACTIC' if memo[n] else 'GRANULAR6_5_NO_LITERAL_WHOLE_EXPOSURE',
          'responsible_direct_dependency_roots':responsible,'complete_custom_prerequisites':sorted(closure_memo[n]-{n}),
          'external_custom_prerequisites':sorted(closure_memo[n]-set(own)),
          'unbuilt_external_custom_prerequisites':sorted(closure_memo[n]&external_unbuilt)})
    audits=[]
    for audit in plan.get('audit_modules',[]):
        file=plan_file.parent/audit;raw=file.read_text(encoding='utf8');direct=read_imports(file);bad=set();needed=set()
        for d in direct:
            if d in source_nodes:bad.update(memo[d]);needed.update(closure_memo[d])
            else:bad.update(unsafe_official(d))
        selected=re.findall(r'#print\s+axioms\s+([^\s]+)',raw)
        audits.append({'audit':audit,'source_sha256':sha(file),'literal_imports':direct,'whole_Mathlib_or_Tactic_roots':sorted(bad),
          'safe_under_granular_resource_classification':not bad,'required_custom_sources':sorted(needed),'requested_print_names':selected})
    projects.append({'id':old['id'],'version':plan['version'],'mathlib_pin':plan['mathlib_pin'],'source_plan_sha256':sha(plan_file),
      'source_count':len(own),'historical_nominal_granular_count':len(nominal),'historical_whole_count':len(old_whole),
      'authoritative_whole_or_Tactic_count':len(whole_own),'authoritative_safe_granular_count':len(safe_own),
      'newly_reclassified_nominal_granular_count':len(newly_held),'newly_reclassified_nominal_granular_names':sorted(newly_held),
      'source_rows':rows,'audit_rows':audits,'safe_owned_source_names':sorted(safe_own),'whole_owned_source_names':sorted(whole_own),
      'safe_combined_custom_dependency_count':len(safe_custom),'safe_combined_custom_dependency_names':sorted(safe_custom),
      'safe_owned_subset_closed_in_combined_custom_graph':True,'safe_owned_source_external_prerequisite_names':sorted(external_needed),
      'safe_external_prerequisites_currently_unbuilt':sorted(external_unbuilt),
      'resource_safe_owned_sources_without_unbuilt_external_prerequisites':sorted(immediate_own),
      'resource_safe_not_yet_same_as_compilation_readiness':True,'additional_source_plans':additional_plans})
    contexts.append({'project_id':old['id'],'exact_custom_nodes':list(source_nodes.values()),
      'all_custom_nodes_Mathlib_or_Tactic_flags':{n:sorted(memo[n]) for n in sorted(memo)}})
    print('M2_SOURCE_CLASSIFICATION',old['id'],'oldgran',len(nominal),'safegran',len(safe_own),'newwhole',len(newly_held),flush=True)
assert all(set(row['effective_import_dependencies'])<=set(official) for row in official.values())
for row in official.values():row['transitive_Mathlib_or_Tactic_roots']=sorted(official_unsafe[row['module']])
official_file=BASE/'m2-eight-plans-pinned-official-source-import-graph-20261005.json';save(official_file,[official[n] for n in sorted(official)])
custom_file=BASE/'m2-eight-plans-contextual-custom-source-import-graph-20261005.json';save(custom_file,contexts)
result={'status':'AUTHORITATIVE_SOURCE_ONLY_MATHLIB_AND_TACTIC_EXPOSURE_PROPOSAL_NO_DISPATCH',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'historical_inventory_sha256':sha(inventory_file),
 'historical_nominal_granular_total':600,'historical_whole_total':112,
 'authoritative_safe_granular_total':sum(p['authoritative_safe_granular_count'] for p in projects),
 'authoritative_whole_or_Tactic_total':sum(p['authoritative_whole_or_Tactic_count'] for p in projects),
 'newly_reclassified_nominal_granular_total':sum(p['newly_reclassified_nominal_granular_count'] for p in projects),
 'all712_own_source_hashes_rechecked':True,'all_reached_additional_custom_source_hashes_rechecked':True,
 'official_source_nodes':len(official),'official_source_graph_file':str(official_file),'official_source_graph_sha256':sha(official_file),
 'contextual_custom_source_graph_file':str(custom_file),'contextual_custom_source_graph_sha256':sha(custom_file),
 'compiler_binary_sha256':prep['compiler_binary_sha256'],'exact_original_nine_package_pins':{p['name']:p['original_manifest_rev'] for p in prep['exact_original_nine_packages']},
 'projects':projects,'source_provider_resolution_policy':'Exact project own modules first, then explicitly declared additional source-library plans in authored LEAN_PATH order, then exact pinned official9packages/core/Lake. Whole exposure is transitive per source through both custom and official graphs.',
 'historical600_112_records_modified':False,'current_compiler_runners_changed':False,'source_body_import_or_option_changes':False,
 'official_artifact_hashes_newly_measured_by_this_source_only_review':False,'Lean_or_compiler_invoked':False,
 'output_copies_links_or_aliases_created':False,'Std_external_witness_accepted':False,
 'qualification':'This authoritative source-exposure proposal supersedes historical resource classification only after root review. Every nominal granular source exposing Mathlib or Mathlib.Tactic is held for sole10/11 policy; external safe custom prerequisites still require actual qualified outputs before downstream sources. No source elaboration, endpoint certification, artifact reuse or originalE65-container equivalence is implied.'}
out=BASE/'m2-eight-plans-authoritative-whole-tactic-scope-proposal-20261005.json';save(out,result)
print(json.dumps({'proposal':str(out),'proposal_sha256':sha(out),'official_graph_sha256':sha(official_file),
 'custom_graph_sha256':sha(custom_file),'old_granular_total':600,'safe_granular_total':result['authoritative_safe_granular_total'],
 'newly_held_total':result['newly_reclassified_nominal_granular_total'],
 'per_project':[{'id':p['id'],'old_granular':p['historical_nominal_granular_count'],'safe_granular':p['authoritative_safe_granular_count'],
 'newly_held':p['newly_reclassified_nominal_granular_count'],'unbuilt_safe_external_count':len(p['safe_external_prerequisites_currently_unbuilt'])} for p in projects],
 'Lean_invoked':False},indent=2))
