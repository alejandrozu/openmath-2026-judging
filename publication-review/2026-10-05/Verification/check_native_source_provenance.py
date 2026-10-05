"""Read-only, frozen-source gate for interpreting native-looking axiom output.

This is a static inventory, not a fresh Lean replay or a claim that syntax
extensions cannot generate declarations. No live build receipt is read here.
"""
from pathlib import Path
import hashlib, json, os, re
from datetime import datetime, timezone
from lean_imports import stripped

BASE = Path(__file__).resolve().parent
ROWS = []
CACHE = {}
SCANNER_REVISION = 1
prior_path = BASE / 'native-source-provenance.json'
if prior_path.exists():
    prior = json.loads(prior_path.read_text(encoding='utf8'))
    if prior.get('scanner_revision', 1) == SCANNER_REVISION:
        for row in prior.get('projects', []):
            for file in row.get('files', []):
                if file.get('sha256') and 'imports' in file:
                    CACHE[file['sha256']] = {key: file[key] for key in
                        ['imports', 'explicit_axiom_sites', 'native_evaluation_sites',
                         'syntax_extension_sites', 'admission_sites']}

def sites(clean, pattern):
    return [{'line': clean.count('\n', 0, m.start()) + 1,
             'text': clean[m.start():clean.find('\n', m.start()) if '\n' in clean[m.start():] else len(clean)].strip()[:250]}
            for m in re.finditer(pattern, clean, re.M)]

plans = [(json.loads(p.read_text(encoding='utf8')), p.parent.name)
         for p in sorted((BASE / 'builds').glob('*/build-plan.json'))]
special = BASE / 'chandragupt-pinned-build.json'
if special.exists():
    completed = json.loads(special.read_text(encoding='utf8'))
    plans.append(({'id': 'chandragupt', 'modules': [
        {'module': name.removesuffix('.lean').replace('/', '.'),
         'file': str(BASE / 'builds' / 'chandragupt' / name),
         'source': name, 'sha256': sha}
        for name, sha in completed['source_sha256'].items()]}, 'chandragupt'))
for plan, route in plans:
    project = plan.get('id', route)
    if project == 'luke-k4-ramsey-current' and route != 'luke-k4-ramsey-current-direct':
        continue
    files = []
    for module in plan.get('modules', []):
        path = Path(module['file'])
        if not path.exists():
            files.append({'module': module.get('module'), 'source': module.get('source'), 'status': 'MISSING_FROZEN_SOURCE'})
            continue
        raw = path.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        if sha not in CACHE:
            clean = stripped(raw.decode('utf8'))
            CACHE[sha] = {
                'imports': [name.replace('«','').replace('»','')
                    for line in clean.splitlines() if re.match(r'^\s*(public\s+)?(meta\s+)?import\s',line)
                    for name in re.sub(r'^\s*(public\s+)?(meta\s+)?import\s+','',line).split()],
                'explicit_axiom_sites': sites(clean, r'(?<![.\w`])axiom\s+[^\s:(]+'),
                'native_evaluation_sites': sites(clean, r'\b(?:native_decide|bv_decide|ofReduceBool|ofReduceNat|trustCompiler)\b'),
                'syntax_extension_sites': sites(clean, r'^\s*(?:private\s+|public\s+|scoped\s+)?(?:elab|macro|macro_rules|syntax)\b'),
                'admission_sites': sites(clean, r'\b(?:sorry|admit|sorryAx)\b')}
        files.append({'module': module.get('module'), 'source': module.get('source', path.name),
            'sha256': sha, 'matches_frozen_plan': sha == module.get('sha256'),
            **CACHE[sha]})
    missing = [f['source'] for f in files if f.get('status') == 'MISSING_FROZEN_SOURCE']
    mismatched = [f['source'] for f in files if f.get('matches_frozen_plan') is False]
    axioms = [{'source': f['source'], **s} for f in files for s in f.get('explicit_axiom_sites', [])]
    native = [{'source': f['source'], **s} for f in files for s in f.get('native_evaluation_sites', [])]
    extensions = [{'source': f['source'], **s} for f in files for s in f.get('syntax_extension_sites', [])]
    admissions = [{'source': f['source'], **s} for f in files for s in f.get('admission_sites', [])]
    gate = ('FROZEN_SOURCE_IDENTITY_HOLD' if missing or mismatched else
            'EXPLICIT_AXIOMS_REQUIRE_ENDPOINT_REACHABILITY_REVIEW' if axioms else
            'SYNTAX_EXTENSIONS_REQUIRE_REVIEW' if extensions else
            'NO_EXPLICIT_AXIOM_DECLARATIONS_NATIVE_SITES_PRESENT' if native else
            'NO_EXPLICIT_AXIOM_DECLARATIONS_NO_NATIVE_SITES')
    ROWS.append({'project': project, 'execution_route': route,
        'source_static_gate': gate, 'missing_sources': missing, 'mismatched_sources': mismatched,
        'explicit_axiom_sites': axioms, 'native_evaluation_sites': native,
        'syntax_extension_sites': extensions, 'admission_sites': admissions, 'files': files})

result = {'generated_utc': datetime.now(timezone.utc).isoformat(),
    'scanner_revision': SCANNER_REVISION,
    'scope': 'Every frozen custom module in each deduplicated source plan; official pinned dependency implementation is outside this static inventory.',
    'interpretation': 'A native-looking axiom name is not accepted as evidence of a generated native_decide/bv_decide certificate by itself. Pair this source inventory with freshly compiled unchanged modules and actual selected endpoint axiom output. Any explicit axiom or syntax-extension site needs reachability/implementation review. Absence of explicit axiom syntax is a static observation, not a general no-axiom theorem. Admissions in unrelated modules do not decide selected-endpoint validity.',
    'projects': ROWS}
target = BASE / 'native-source-provenance.json'
temporary = target.with_suffix('.json.tmp')
temporary.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf8')
os.replace(temporary, target)
print(json.dumps({'projects': len(ROWS), 'source_identity_holds': [r['project'] for r in ROWS if r['missing_sources'] or r['mismatched_sources']],
    'explicit_axiom_projects': [r['project'] for r in ROWS if r['explicit_axiom_sites']],
    'syntax_extension_projects': [r['project'] for r in ROWS if r['syntax_extension_sites']],
    'native_site_projects': [r['project'] for r in ROWS if r['native_evaluation_sites']]}, indent=2))
