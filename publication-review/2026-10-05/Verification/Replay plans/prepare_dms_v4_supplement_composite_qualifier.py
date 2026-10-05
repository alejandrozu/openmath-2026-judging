"""Prepare only a composite7/221/123 qualifier, retaining the original failed audit."""
from pathlib import Path
import hashlib,ast,json,difflib
BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
original=BASE/'qualify_dms_v4_vector_complete_route.py'
assert sha(original)=='bc34e0c971547d46d164b74007546f11e7c3c6aa83f288a44d62df505b8f03d8'
audit_runner=BASE/'audit_dms_v4_equiv_supplement.py'
text=original.read_text(encoding='utf8')
text=text.replace('linked into V4, and seven affected sources must have actual new V4 rows.',
    'linked into V4, and seven affected sources must have actual new V4 rows.\nThe frozen original120/123 audit exited1; a separate organizer supplement must\nprint all123 unchanged requests and is disclosed alongside that original failure.')
text=text.replace("assert approved['status']=='ROOT_APPROVED_DMS_V4_FINAL_QUALIFICATION_READ_ONLY'",
    "assert approved['status']=='ROOT_APPROVED_DMS_V4_COMPOSITE_FINAL_QUALIFICATION_WITH_SUPPLEMENT_READ_ONLY'")
needle="    assert len(requested)==len(set(requested))==123\n"
assert text.count(needle)==1
block="""
    # Preserve the real original organizer-audit failure; do not reclassify it PASS.
    original_audit_identity=audit_identity;original_parsed=parsed;original_raw=raw_print_receipts
    original_missing=sorted(set(requested)-{r['endpoint'] for r in original_parsed})
    expected_original_missing=['Star6.colourable_of_dms_cubic','Star6.dms_iff_cubic16','Star6.leaf_of_dms']
    assert original_missing==expected_original_missing and len(original_parsed)==120
    assert len(original_audit_identity)==len(original_raw)==1 and original_audit_identity[0]['exit']==1
    assert sorted(re.findall(r'Unknown constant `([^`]+)`',original_raw[0]['actual_stdout']))==expected_original_missing
    assert receipt_sha=='fb428dd280da30ba25480be5420157dfa7bbeb268c603b05edb0a17dd9eeb7ba'
    supplement_receipt_path=Path(approved['reviewed_supplemental_audit_receipt_file']).resolve()
    assert supplement_receipt_path.is_relative_to(BASE.resolve())
    supplement_sha=approved['reviewed_supplemental_audit_receipt_sha256']
    assert digest(supplement_receipt_path)==supplement_sha
    supplement=load(supplement_receipt_path)
    assert supplement['source_receipt_sha256']==receipt_sha and supplement['seed_receipt_sha256']==SEED_SHA
    assert supplement['audit_runner_sha256']==AUDIT_RUNNER_SHA_PLACEHOLDER
    assert digest(BASE/'audit_dms_v4_equiv_supplement.py')==AUDIT_RUNNER_SHA_PLACEHOLDER
    assert supplement['scientific_source_compilation_invocations']==0 and supplement['protected221_identities_rechecked_after'] is True
    assert supplement['frozen_failed_original_audit_and_plan_preserved'] is True
    assert supplement['original7_V4_output_hashes_before']==supplement['original7_V4_output_hashes_after']
    assert digest(supplement['root_approval'])==supplement['root_approval_sha256']
    supplementary_file=STAGE/'FreshAuditSupplement.lean'
    assert digest(supplementary_file)==supplement['supplement_source_sha256']=='0496d62e6a5cc83f98a73fc0c534eaa0469b1f9cd28f5e13f0fe9cbc1dcd0001'
    assert supplementary_file.read_bytes()==b'import Star6Equiv\\n'+(STAGE/'FreshAudit1.lean').read_bytes()
    assert re.findall(r'^\\s*#print\\s+axioms\\s+(\\S+)',stripped(supplementary_file.read_text(encoding='utf8')),re.M)==requested
    row=supplement['audit_row'];assert row['module']=='FreshAuditSupplement.lean' and row['is_endpoint_audit'] is True
    relative=supplementary_file.relative_to(STAGE)
    expected_command=[str(lean),'-j1','-DmaxHeartbeats=0','-DmaxRecDepth=100000','-o',str(relative.with_suffix('.olean')),str(relative)]
    identity=exact_invocation_identity(row,supplementary_file,expected_command)
    assert row['exit']==0 and row.get('stop_reason') is None
    parsed=parse_axioms(row['stdout'])
    old_by_name={r['endpoint']:r for r in original_parsed};new_by_name={r['endpoint']:r for r in parsed}
    for name,old in old_by_name.items():
        assert name in new_by_name and old['classification']==new_by_name[name]['classification']
        assert sorted(old['axioms'])==sorted(new_by_name[name]['axioms'])
    audit_identity=[{'audit':'FreshAuditSupplement.lean','source_sha256':digest(supplementary_file),'requested_endpoints':requested,
        'attempted':True,'exit':row['exit'],'stop_reason':row.get('stop_reason'),
        'actual_audit_source_command_guard_and_raw_log_identity':identity,'printed_endpoints':[r['endpoint'] for r in parsed]}]
    raw_print_receipts=[{'audit':'FreshAuditSupplement.lean','actual_stdout':row['stdout'],'actual_stderr':row['stderr'],
        'actual_command':row['command'],'actual_exit':row['exit'],'actual_row':row}]
""".replace('AUDIT_RUNNER_SHA_PLACEHOLDER',repr(sha(audit_runner)))
text=text.replace(needle,needle+block)
text=text.replace("'QUALIFIED_BODY_IDENTICAL_ROUTE_WITH_PREVIOUS_OWN_COLD_OUTPUT_REUSE_NATIVE_EVALUATION_DISCLOSED'",
    "'QUALIFIED_BODY_IDENTICAL_SOURCES_WITH_221_PREVIOUS_OWN_PASSES_AND_FRESH_ORGANIZER_SUPPLEMENT_NATIVE_DISCLOSED'")
text=text.replace("'QUALIFIED_BODY_IDENTICAL_ROUTE_WITH_PREVIOUS_OWN_COLD_OUTPUT_REUSE_STANDARD_ENDPOINTS'",
    "'QUALIFIED_BODY_IDENTICAL_SOURCES_WITH_221_PREVIOUS_OWN_PASSES_AND_FRESH_ORGANIZER_SUPPLEMENT_STANDARD_ENDPOINTS'")
needle="        'actual_raw_print_receipts':raw_print_receipts,'compiler_invocations_in_this_helper':0,\n"
assert text.count(needle)==1
block="""        'frozen_original_audit_exit1_120of123_fully_preserved':{'identity':original_audit_identity,'parsed120':original_parsed,
            'missing_exact3':original_missing,'actual_raw_audit_receipt':original_raw,'original_source_receipt_sha256':receipt_sha},
        'organizer_supplemental_audit_receipt':str(supplement_receipt_path),'organizer_supplemental_audit_receipt_sha256':supplement_sha,
        'supplementary_import_only_change':'importStar6Equiv added to separate organizer audit; all123 original requests and all228 scientific bodies/options unchanged',
        'original120_axiom_classes_and_sets_match_successful_supplement':True,
"""
text=text.replace(needle,needle+block)
text=text.replace('dms-v4-vector-complete-route-final-qualification-20261005.json','dms-v4-vector-composite-supplement-final-qualification-20261005.json')
target=BASE/'qualify_dms_v4_supplement_composite.py';assert not target.exists();ast.parse(text)
target.write_text(text,encoding='utf8',newline='\n')
diff=BASE/'dms-v4-supplement-composite-qualifier-full-operational.diff';assert not diff.exists()
diff.write_text(''.join(difflib.unified_diff(original.read_text(encoding='utf8').splitlines(keepends=True),text.splitlines(keepends=True),fromfile=original.name,tofile=target.name)),encoding='utf8',newline='\n')
runner_diff=BASE/'dms-v4-supplement-one-audit-runner-full-implementation.diff';assert not runner_diff.exists()
runner_diff.write_text(''.join(difflib.unified_diff([],audit_runner.read_text(encoding='utf8').splitlines(keepends=True),fromfile='/dev/null',tofile=audit_runner.name)),encoding='utf8',newline='\n')
packet=BASE/'dms-v4-supplement-runner-composite-qualifier-preparation-20261005.json';assert not packet.exists()
packet.write_text(json.dumps({'status':'PREPARED_ONLY_NO_MATERIALIZATION_OR_LEAN_OR_QUALIFICATION',
    'files':[{'file':str(p),'sha256':sha(p)} for p in [audit_runner,target,runner_diff,diff]],
    'science':'7 actual V4new+221 prior own passes unchanged; no source rebuild or V5; frozen original120/123exit1 disclosed',
    'future_audit_scope':'One separately approved organizer-only file with onlyimportStar6Equiv+same123requests',
    'future_final_scope':'Read-only compositequalification requires actualsupp123+allcurrent source/artifact/guard/pin identities; sorry/unknown/missing preventsqualification',
    'compiler_invocations':0,'output_aliases':0,'qualification_executions':0},indent=2)+'\n',encoding='utf8')
print(json.dumps({'audit_runner_sha256':sha(audit_runner),'qualifier_sha256':sha(target),'runner_full_diff_sha256':sha(runner_diff),
    'qualifier_full_diff_sha256':sha(diff),'preparation_sha256':sha(packet)},indent=2))
