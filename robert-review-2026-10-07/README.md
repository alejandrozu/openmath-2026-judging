# Robert Huynh: Erdős585 research and formal proof companion

This dated review preserves Robert Huynh's public work at revision `1efc324e155ef0b6a7081c5f695c6c825e7debef` and the additional research and formalization by Alejandro Zarzuelo Urdiales. Original source copyright and Apache2 notices are preserved. The [current canonical coauthored manuscript](manuscript/Robert_Huynh_concise.pdf) is the 23-page compiled SV author-review edition with immutable Lean links. [Editable sources](manuscript/Sources/) and [current QA/typesetting evidence](../author-return/2026-10-07/README.md) accompany it. Older11/generic20 editions are dated history.

## Verified proof sources

- [106 frozen author source files](proofs/frozen-source-manifest.json), matched byte for byte to the sources in the completed audit.
- [84 selected existing endpoints](proofs/existing-endpoints.json), all using standard kernel axioms in the actual prior compile and axiom audit.
- [186 additional verified endpoints](proofs/new-endpoints.json), with actual compiler receipts: full substitution preservation and prescribed-vertex equivalence; uniform full-host two-round sharpness; a general Sidon-palette obstruction without finite ambient space; the extended twin density range; Hamilton decomposition of every exact-four-colour prime-field Haar component; the full near-regular factor/cut-retention Lemma F; and the independent uniform two-shore spectral sampling theorem B2.2. The current 21-source sampling development derives the matrix concentration, fixed-count law, centering and quantitative probability budget. Main BM remains unproved.
- [270 selected declarations in total](proofs/selected-endpoints.json). Declaration counts measure audited proof coverage, not discoveries or competition points.
- [68 additional source modules](proofs/additive-source-manifest.json), including nine attributed modules of known third-party matrix-Bernstein and Haxell foundations. Known mathematics and additive formalizations retain attribution; these foundations do not establish main BM.

The previous 192-endpoint source snapshot at `8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f` passed a clean [GitHub build and exact selected audit](https://github.com/alejandrozu/openmath-2026-judging/actions/runs/37641375097). Its [actual output](proofs/portable-ci/37641375097/) is retained. The current270-endpoint source snapshot at `70c5ec3107658182f22c207d4c50f53f9cb3e602` also passed a clean [GitHub build and exact audit](https://github.com/alejandrozu/openmath-2026-judging/actions/runs/37663424314); [actual output](proofs/portable-ci/37663424314/) is retained. The current journal manuscript retains that exact proof revision, full F/B2.2 statements and the complete original result catalogue. The [written proof dossier](written-proofs/manifest.json), including the preserved QB5 source parts, remains a separate mathematical supplement.

There are four deliberately admitted general/asymptotic target statements in `Openmath/Target.lean`. They are not certified results and none of the selected endpoints depends on `sorryAx`. A successful selected audit does not prove the parent Erdős 585 problem.

| Claim | Exact source for human review | Scope |
|---|---|---|
| Quartic extraction | [QB5 main](lean/Openmath/Proofs/QB5/Main.lean) | Bipartite maximum degree six; threshold 3n−5 |
| Twin density extension | [TwinDensityExtension](lean/TwinDensityExtension.lean) | Nonempty actual hosts; e+2≥3v; no singleton left twins |
| Substitution | [R1](lean/R1.lean), [projection](lean/Projection.lean) | Faithful actual links; parallel skeleton edges distinguished; d≤7 |
| Vertex deletion | [PrescribedVertex](lean/PrescribedVertex.lean) | Conditional B6 iff every prescribed deletion; does not prove B6 |
| Haar components | [HaarComponents](lean/HaarComponents.lean) | Exactly four colours: every actual component has two spanning cycles exhausting its edges |
| General Sidon barrier | [InfiniteAffinePaletteBarrier](lean/InfiniteAffinePaletteBarrier.lean) | Arbitrary characteristic-three ambient module; finite Sidon palette |
| Two-round sharpness | [CycleComposition](lean/CycleComposition.lean) | Every q=3^k, k≥2; literal two-round moves in full host; common 54-vertex support |
| Matrix Bernstein | [SLT](lean/SLT/PORTING.md) | Published third-party operator-norm concentration foundation |
| Haxell foundation | [Port record](lean/IndependentTransversals/PORTING.md) | Sufficient IT non-domination criterion; no claim of the sharper hypergraph constant |
| Full Lemma F | [LemmaF](lean/LemmaF.lean), [arbitrary-partition transport](lean/PartitionTransport.lean) | Actual near-regular factor and retained cuts under the exact written numerical hypotheses; not main BM |
| Sampling foundations | [source/endpoint index](proofs/new-audits/SAMPLING_ACTUAL/current-source-DAG.json) | Actual compressed-matrix tails, uniform conditioning, regular spectral centering and budgets used by B2.2; no main Hamiltonicity conclusion |
| Full spectral sampling B2.2 | [B22](lean/B22.lean) | Actual independent uniform m-subsets; binary regular matrix; genuine second singular value; exact density/probability hypotheses and conclusion |

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

The selected audit requires an actual successful Lean exit, exact endpoint coverage and the allowlist `propext,Classical.choice,Quot.sound`. It does not use `native_decide` or a custom main-theorem axiom. New evidence is appended without relabelling old operational failures as passes. A manually triggered [GitHub workflow](../.github/workflows/robert-proof-check.yml) provides a fresh portable build and exact selected audit; its run status is evidence separate from the completed Windows source checks.

## Written arguments and research

[Primary-literature comparison for five families](research/research_five_comparison_matrix.md) and [the other three families](research/root_novelty_assessment.json) distinguish exact prior theorems from unresolved priority. The frozen research records retain their dated proof statuses; the current theorem index records subsequent actual formal completion.

[Written proof dossiers](written-proofs/manifest.json) preserve the original arguments. The quantitative main BM Hamiltonicity proof, its complete sampling/router/factor chain, the avoidance-conditioned E110 bridge and finite 11/12 upper exclusions remain outside the certified main results. Private exponent-eleven/B2 proofs were unavailable. The eighteen-vertex least-order claim needs its complete census. [The cherry-lemma correction](written-proofs/BM_cherry_correction.md) records a genuine missing positive-degree hypothesis, without calling the whole packing theorem Lean verified.

Several ingredients are prior mathematics: AFK/Olson zero-sum selection, Eppstein's subdivided-double Hamilton lift, classical Sidon/2-cap geometry, generic five-regular pair-free existence, and specified abelian/dihedral Haar decomposition cases. Formal checking does not establish historical novelty. No absence of search results is presented as a proof of priority.

Evaluated by Alejandro Zarzuelo Urdiales in connection with OpenMath2026 at Harvard and MIT. Competition scores remain separate provisional judging records; this archive asserts no signed award or journal acceptance.

The independently attributed [Chandragupt Sharma universal matrix family](../chandra-support138-family-2026-10-07/) is a sibling source project. It is not a Robert Huynh result.
