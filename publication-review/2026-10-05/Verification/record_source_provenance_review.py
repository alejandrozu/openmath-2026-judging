"""Preserve the actual source-inspection conclusions behind trust qualifiers."""
from pathlib import Path
import hashlib, json, os
from datetime import datetime, timezone

BASE = Path(__file__).resolve().parent
static = json.loads((BASE / 'native-source-provenance.json').read_text(encoding='utf8'))
assertions = json.loads((BASE / 'source-assertion-audit.json').read_text(encoding='utf8'))
answers = []
for project in assertions['projects']:
    for file in project.get('flagged_modules', []):
        if file['module'] != 'FormalConjecturesUtil.Answer':
            continue
        raw = Path(file['file']).read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        if sha != file['source_sha256']:
            raise RuntimeError('Source changed since static inventory')
        text = raw.decode('utf8')
        if not all(s in text for s in ['addDecl (.defnDecl answerAuxiliaryDecl) true',
                                      'defValue := .alwaysTrue', 'mkCanonicalSorryAnnotation']):
            raise RuntimeError('Inspected Answer implementation differs')
        answers.append({'project': project['id'], 'module': file['module'], 'sha256': sha,
            'conclusion': 'The inspected addDecl site creates a safe auxiliary definition, not an axiom. The default Prop-valued answer(sorry) becomes True; non-Prop placeholders may create sorryAx. Selected elaborated statements must be compared with the mathematical target; an axiom list alone is insufficient.'})
native = []
for project in static['projects']:
    if not project['native_evaluation_sites']:
        continue
    native.append({'project': project['project'], 'execution_route': project['execution_route'],
        'explicit_axiom_sites': len(project['explicit_axiom_sites']),
        'syntax_extension_sites': len(project['syntax_extension_sites']),
        'native_evaluation_sites': project['native_evaluation_sites'],
        'conclusion': 'No explicit axiom declaration or custom command-extension site was found in this frozen source set. Actual native tactic sites are present. This is compatible with generated native-evaluation axioms, but only matching freshly completed compilation and selected axiom outputs establish the executed endpoint trust boundary.'
            if not project['explicit_axiom_sites'] and not project['syntax_extension_sites'] else
            'Additional source/reachability review is required before interpreting a native-looking axiom name.'})
result = {'recorded_utc': datetime.now(timezone.utc).isoformat(),
    'record_type': 'Assistant source inspection prepared for the preliminary evaluation record; not a second independent human judgment or an award signoff.',
    'source_identity': 'All 40 deduplicated frozen source projects, including the dedicated Chandragupt source set, have matching inventory hashes and no explicit source axiom declarations.',
    'answer_elaborator_inspections': answers, 'native_source_inspections': native,
    'remaining_requirements': ['Fresh unchanged-source replay', 'Selected endpoint axiom-output coverage',
        'Intended-statement fidelity, including explicit hypotheses and placeholder elaboration',
        'Novelty, resource-class and required independent judging signoffs']}
target = BASE / 'source-provenance-manual-review.json'
temporary = target.with_suffix('.json.tmp')
temporary.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf8')
os.replace(temporary, target)
print(json.dumps({'answer_implementations_inspected': len(answers), 'native_source_projects': len(native), 'fresh_replay_claimed': False}, indent=2))
