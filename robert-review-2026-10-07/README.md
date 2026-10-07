# Robert Huynh: Erdős585 research and formal proof companion

This dated review preserves Robert Huynh's public work at revision1efc324e155ef0b6a7081c5f695c6c825e7debef and the additive research/formalization by Alejandro Zarzuelo Urdiales. Original source copyright and Apache2 notices are preserved. Author-reported written arguments, known mathematical ingredients and unresolved formal claims remain distinct.

## Verified proof sources

- [106 frozen author source files](proofs/frozen-source-manifest.json), matched byte for byte to the sources in the completed audit.
- [84 selected existing endpoints](proofs/existing-endpoints.json), all using standard kernel axioms in the actual prior compile and axiom audit.
- [New verified endpoints](proofs/new-endpoints.json), with actual additive compiler receipts. The current18 additive endpoints extend the Haar converse to arbitrary ambient modules, verify graph-semantic Hamilton-cycle transfer and balanced-deletion counts, and certify a zero-degree counterexample to the written cherry lemma. These supporting pieces do not close main BM/F/V110.
- [Complete selected theorem index](proofs/selected-endpoints.json).

There are four deliberately admitted general/asymptotic target statements in Openmath/Target.lean. They are not certified results and none of the selected endpoints depends on sorryAx. A successful selected audit does not prove the parent Erdős585 problem.

## Reproduce

The Lake project is in [lean/](lean/), pinned to Lean4.33.1 and FormalConjectures137aec5c7abd3aa61f7a73138a97279acfc79e93; its manifest fixes Mathlib0df444a360eaa60ab8c11dca51a86af692955474. From this directory:

```sh
cd lean
lake update
lake exe cache get
lake build
cd ..
python scripts/check_selected_axioms.py
```

The selected audit requires an actual successful Lean exit, exact endpoint coverage and the allowlist propext,Classical.choice,Quot.sound. It does not use native_decide or a custom main-theorem axiom. New evidence is appended without relabelling old operational failures as passes.

## Written arguments and research

[Written proof dossiers](written-proofs/manifest.json) retain their ordinary-proof status. Main substitution, quantitative BM/F/V110, the complete two-round move bridge, and the11/12 upper exclusions must not be called fully Lean verified without their exact additional proofs. The concise manuscript and primary-literature novelty matrix are being finalized against these explicit boundaries.

Evaluated by Alejandro Zarzuelo Urdiales in connection with OpenMath2026 at Harvard and MIT. Competition scores remain separate provisional judging records; this archive asserts no signed award or journal acceptance.
