"""Classify the exact authored import DAG; do not rewrite imports or source."""
from lean_imports import read_imports
def classify(plan):
    names={m['module'].replace('«','').replace('»',''):m for m in plan['modules']}
    imports={n:read_imports(m['file']) for n,m in names.items()}
    direct=[n for n,ds in imports.items() if 'Mathlib' in ds]
    memo={}
    def roots(n):
        if n in memo:return memo[n]
        found={n} if 'Mathlib' in imports[n] else set()
        for d in imports[n]:
            if d in names:found.update(roots(d))
        memo[n]=sorted(found);return memo[n]
    closure={n:roots(n) for n in names if roots(n)}
    return {'direct_whole_Mathlib_import_modules':direct,'authored_transitive_whole_Mathlib_closure':closure,
      'source_module_count':len(names),'whole_Mathlib_closure_count':len(closure),
      'qualification':'Literal whole-Mathlib imports and their transitive authored dependencies; exact imported source bytes are preserved. External library internals retain their independently recorded pin provenance.'}
