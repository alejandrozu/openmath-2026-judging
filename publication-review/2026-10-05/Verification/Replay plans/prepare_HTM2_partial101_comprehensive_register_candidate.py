"""Prepare partial101 qualification metadata only; no updater/Lean execution."""
from pathlib import Path
from datetime import datetime,timezone
import ast,difflib,hashlib,json
BASE=Path(__file__).resolve().parent
ORIGINAL=BASE/'update_replay_register.py'
CANDIDATE=BASE/'update_replay_register_HTM2_partial101_candidate.py'
DIFF=BASE/'comprehensive-register-HTM2-partial101-additive-minimal.diff'
PACKET=BASE/'comprehensive-register-HTM2-partial101-candidate-preparation-20261005.json'
QUAL=BASE/'root-HTM2-granular101-three-new-four-standard-qualified-20261005.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(ORIGINAL)=='45b683c464ea09aa0d3822dd10d8aa5e921dcf23bfbc1a789cc60640f64177c8'
assert sha(QUAL)=='ede28ac93ddfcae456936231e86b4f3c1db3a0d333e1b363b78e16061f9aa90e'
q=json.loads(QUAL.read_bytes());assert q['full122_project_qualified'] is False and q['whole21_and_selected33_deferred'] is True
assert sha(q['receipt_file'])==q['receipt_sha256']=='6380494f7b0e07d4a8882f3c3dcfbd43164f9484f89fc84392a4b5d2d9aa2853'
old=ORIGINAL.read_text(encoding='utf8')
anchor=' return scopes\n'
assert old.count(anchor)==1
addition=''' q,meta=qualified_record('root-HTM2-granular101-three-new-four-standard-qualified-20261005.json','ede28ac93ddfcae456936231e86b4f3c1db3a0d333e1b363b78e16061f9aa90e')
 if q:
  assert q['status']=='ROOT_QUALIFIED_HTM2_EXACT_GRANULAR101_SOURCES_97_PRIOR_DMS_ONE_PRIOR_OWN_THREE_NEW_AND_FOUR_STANDARD_SELECTED'
  assert (q['body_count_covered'],q['prior_owned_DMS97'],q['prior_owned_M2_StarCore1'],q['new_cold_source_passes'],q['actual_selected_prints'])==(101,97,1,3,4)
  assert q['full122_project_qualified'] is False and q['whole21_and_selected33_deferred'] is True
  standard_selected_scope(q['actual_selected_classifications'],4)
  assert hashlib.sha256(read_bytes_shared(Path(q['receipt_file']))).hexdigest()==q['receipt_sha256']
  linked=read_json_shared(Path(q['receipt_file']))
  assert linked['source_plan_sha256']==q['source_plan_sha256']
  assert q['all_four_raw_CLI_guard_log_source_output_hashes_checked'] is True and q['all122_source_hashes_checked'] is True
  scopes['htpeo-erdos-m2']={**meta,'family':'HTPeo-M2','status':q['status'],'qualified':True,
   'scientific_body_scope_complete':False,'selected_endpoint_scope_complete':False,
   'qualified_granular_subscope_complete':True,'qualified_selected_endpoint_subscope_complete':True,
   'scientific_body_count':101,'full_project_scientific_body_count':122,
   'prior_owned_DMS_source_passes':97,'prior_owned_M2_StarCore_source_passes':1,'new_cold_source_passes':3,
   'selected_endpoint_count':4,'full_project_selected_endpoint_count':37,
   'selected_classification_counts':{'STANDARD_KERNEL_AXIOMS':4},
   'whole_source_modules_deferred':21,'other_selected_endpoint_prints_deferred':33,
   'actual_linked_granular_receipt':q['receipt_file'],'actual_linked_granular_receipt_sha256':q['receipt_sha256'],
   'source_plan_sha256':q['source_plan_sha256'],'seed_receipt_sha256':q['seed_receipt_sha256'],
   'scope_relation':'Only exact granular101/122 bodies and four selected outputs are qualified:97 earlier DMS-owned passes,one earlier M2-owned StarCore pass,three new checks. Whole21 and33 other selected outputs remain unattempted. The default full-route status is unchanged.',
   'full_project_qualified':False,'original_raw_receipt_replaced':False,'novelty_or_scoring_or_publication_upgrade_implied':False}
 return scopes
'''
new=old.replace(anchor,addition)
new=new.replace("  chosen['effective_scientific_scope_status']='QUALIFIED_SELECTED_SCIENTIFIC_SCOPE'",
 "  chosen['effective_scientific_scope_status']='QUALIFIED_SELECTED_SCIENTIFIC_SCOPE' if qualified_scopes[pid]['scientific_body_scope_complete'] else 'PARTIALLY_QUALIFIED_GRANULAR_SCIENTIFIC_SCOPE'")
new=new.replace("chosen['qualified_selected_endpoint_coverage']={'status':'PASS_FROM_ACTUAL_COMPLETED_QUALIFICATION',",
 "chosen['qualified_selected_endpoint_coverage']={'status':'PASS_FROM_ACTUAL_COMPLETED_QUALIFICATION' if qualified_scopes[pid]['selected_endpoint_scope_complete'] else 'PASS_FROM_COMPLETED_GRANULAR_SUBSCOPE_QUALIFICATION_FULL_SCOPE_PENDING',")
ast.parse(new)
with CANDIDATE.open('x',encoding='utf8',newline='\n') as f:f.write(new)
with DIFF.open('x',encoding='utf8',newline='\n') as f:f.writelines(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=ORIGINAL.name,tofile=CANDIDATE.name))
packet={'status':'PREPARED_ADDITIVE_HTM2_PARTIAL101_CANDIDATE_NOT_EXECUTED',
 'created_utc':datetime.now(timezone.utc).isoformat(),'producer_sha256':sha(__file__),
 'current_production_updater_sha256':sha(ORIGINAL),'candidate':str(CANDIDATE),'candidate_sha256':sha(CANDIDATE),
 'minimal_additive_diff':str(DIFF),'minimal_additive_diff_sha256':sha(DIFF),'candidate_AST':'PASS_ONLY',
 'actual_root_qualification':str(QUAL),'actual_root_qualification_sha256':sha(QUAL),
 'actual_linked_granular_receipt':q['receipt_file'],'actual_linked_granular_receipt_sha256':q['receipt_sha256'],
 'qualified_body_subscope':'101/122 =97prior DMS+1prior own StarCore+3new',
 'qualified_selected_print_subscope':'4standard/37total;33 held',
 'full122_family_qualified':False,'whole21_held':True,'raw_default_or_prior_receipt_overrides':0,
 'candidate_executed_or_register_written':False,'compiler_or_canonical_prose_or_PDF_or_source_changes':0}
with PACKET.open('x',encoding='utf8',newline='\n') as f:json.dump(packet,f,indent=2);f.write('\n')
print(json.dumps({'packet':str(PACKET),'packet_sha256':sha(PACKET),'candidate_sha256':sha(CANDIDATE),
 'minimal_diff_sha256':sha(DIFF),'actual_register_or_compiler_execution':False},indent=2))
