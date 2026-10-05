"""Classify printed selected endpoint axioms without treating placeholders as proofs."""
import re
STANDARD={'propext','Classical.choice','Quot.sound'}
LEGACY_NATIVE={'Lean.trustCompiler','Lean.ofReduceBool','Lean.ofReduceNat'}
def is_native(name):
 # Pinned Lean's Meta.Native/CoreM generates `ax` followed only by numeric
 # auxiliary-name components. A similarly prefixed custom axiom is unknown.
 return name in LEGACY_NATIVE or re.search(r'(?:^|\.)_native\.(?:native_decide|bv_decide)\.ax(?:_\d+)*$',name) is not None
def parse(text):
 rows=[]
 # Legal Lean names may contain apostrophes. The closing quote is the one
 # immediately before the fixed diagnostic phrase, not the first apostrophe.
 for match in re.finditer(r"'([^\n]+?)'\s+depends on axioms:\s*\[([^\]]*)\]",text,re.S):
  axioms=[n.strip() for n in match.group(2).split(',') if n.strip()]
  native=[n for n in axioms if is_native(n)]
  unknown=[n for n in axioms if n not in STANDARD and not is_native(n) and n!='sorryAx']
  kind='SORRY_ADMISSION' if 'sorryAx' in axioms else ('UNRECOGNIZED_AXIOMS' if unknown else ('NATIVE_EVALUATION_TRUST' if native else 'STANDARD_KERNEL_AXIOMS'))
  rows.append({'endpoint':match.group(1),'axioms':axioms,'native_axioms':native,'unrecognized_axioms':unknown,'classification':kind})
 for match in re.finditer(r"'([^\n]+?)'\s+does not depend on any axioms",text):
  rows.append({'endpoint':match.group(1),'axioms':[],'native_axioms':[],'unrecognized_axioms':[],'classification':'AXIOM_FREE'})
 return rows
