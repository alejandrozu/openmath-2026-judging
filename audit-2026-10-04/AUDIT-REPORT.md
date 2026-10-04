# OpenMath 2026: independent audit of the preliminary judging and final score proposal

**Date:** 4 October 2026
**Prepared for:** the competition chair (Alejandro Zarzuelo Urdiales)
**Audited material:** this repository at commit `04c270a` plus the release packs `openmath-materials-001.zip` and `openmath-materials-004.zip` (SHA-256 checked against `publication-manifest.json`)
**Status:** audit and recommendation. These are proposed final values under the chair rulings listed in section 1; they still need the chair's sign-off in `OpenMath-Judging/review/score-signoff.csv` before they become the official record.

---

## Contents

0. [Summary](#0-summary)
1. [Chair rulings applied in this audit](#1-chair-rulings-applied-in-this-audit)
2. [Sources and method](#2-sources-and-method)
3. [Verification results](#3-verification-results)
4. [Assessment of the preliminary report](#4-assessment-of-the-preliminary-report)
5. [Entrant-by-entrant assessment](#5-entrant-by-entrant-assessment)
6. [Do the hills and the zero scores contain new mathematics?](#6-do-the-hills-and-the-zero-scores-contain-new-mathematics)
7. [Final scores and rankings](#7-final-scores-and-rankings)
8. [Decisions still open for the chair](#8-decisions-still-open-for-the-chair)
9. [Difficulty values: observations and recommended fixes](#9-difficulty-values-observations-and-recommended-fixes)
10. [Other process recommendations](#10-other-process-recommendations)
11. [Appendices](#appendices)

---

## 0. Summary

**The preliminary report's arithmetic is correct and most of its dispositions are sound.** All 226 result rows and every entrant total reproduce exactly from `F = b·m·p·D²/1000`. Its holds for missing or unformalized work (Matt, Raj, Heilbronn, Qichao, board-only accounts) are consistent with the formal-only rule.

**Errors and inconsistencies found.** Under the chair's rulings, each is now either corrected in the scores below or moot.

- **Collatz credit:** credit was given to Collatz coverage that contains no novel mathematics. The submitted coverage (1,765 of 2,048 odd classes mod 4096; 94 of 128 mod 256) is exactly the maximum any rule set in the hill format can reach, and it lies inside the classical stopping-time set (Terras). Corrected to 0.
- **Ramsey focus bonus:** applied inconsistently. Now moot, because all bonuses are removed.
- **Kobon novelty labels:** 34 of the 46 catalogue rows labelled "candidate" cannot be records. They are at or below the Füredi–Palásti construction or below an earlier row of the same catalogue. This does not change any score.
- **Sakana's Grothendieck theorem:** a new, formalized restricted theorem was scored 0. It is now counted at p = .01 under the new-mathematics rule.
- **Class and timing items:** Chandragupt was labelled a team, and Sakana's late source ZIP had no pinned pre-cutoff commit. Both are moot under the class merger and the timing leniency.

**Formal verification done for this audit.** I compiled the entrants' Lean sources myself, from source, with the pinned toolchains and official Mathlib caches, and audited the axioms of every endpoint. This covered:

- 16 Sakana projects: Erdős 21 +3, A100475, A060957, OPDP13 quartic, RBM4 parity, half-turn, Ferrers, Erdős 169, Erdős 944, Erdős 1060, Erdős 829, the Grothendieck theorem, both Erdős 3 certificates, the Ramsey lifting and matrix-rigidity seed 0;
- Chandragupt's support-138 certificate;
- HTPeo's generic Ramsey lifting theorem and their Kobon K(39) ≥ 471 certificate.

Every one builds and depends only on `propext`, `Classical.choice` and `Quot.sound`, or on fewer axioms. I also recomputed both Ramsey densities **exactly** (multi-modular arithmetic), Chandragupt's 729 tensor identities, the Collatz ceilings and several other claims (section 3.3). [Appendix A](#appendix-a-fresh-lean-builds) lists what was built and what was not.

**Final proposal.** D values are unchanged, there are no bonuses, and the classes are Company and Non-company.

| Class | Rank | Entrant | S (total) | A (biggest) | A family | M2 families |
|---|---|---|---:|---:|---|---:|
| Company | 1 | E02 Sakana AI team (Rachel Teo, Wenyi Wang, Hamdi Abderrahmene) | **1699.570** | **308.025** | Erdős–Lovász +3 residual | **10** |
| Company | – | E24 Thinking Machines | 0 | 0 | – | 0 |
| Non-company | 1 | E08 HTPeo (Woohyuk Kang, Hyunjin Lee, Sanghyeon Lee, Youchan Oh) | **87.950** | **49.421** | DMS (star chromatic index) | **10** |
| Non-company | 2 | E04 Chandragupt Sharma | **26.209** | **26.209** | 3×3 matrix multiplication, support 138 | 0 |
| Non-company | 3 | E57 Rohith Poola | **3.249** | **3.249** | Kobon | 0 |
| Non-company | – | E11 Leon Koerbs / Cameron Fen | 0 | 0 | – | 3 |
| Non-company | – | E65 Wilson Wu | 0 | 0 | – | 2 |
| Non-company | – | E10 Jamie Steeg | 0 | 0 | – | 1 |
| Non-company | – | E06 Leanification (five-person team) | 0 | 0 | – | 1 (adjusted 0.8, chair exception) |

Every other record is 0 / 0 / 0. Section 7 gives the full rankings and the conditional items.

**New mathematics among the hills and the zero scores.** The only unscored new mathematics I found is on the **Ramsey hill**. Three accounts posted upper bounds below the frozen McKay reference during the event window:

| Entrant / account | Date posted | Density |
|---|---|---:|
| E01 Luke Van Seters / Madhan (`madhanj05`) | 2 Oct | 0.030140335647 |
| E43 `danamouk` | 28 Sep | 0.030142036534 |
| E15 Shafeeq (`shaff622`) | 27 Sep; opening-time check needed | 0.030142250482 |

None of the three submitted the template. Score them only if the template is retrieved and re-verified; the recommendation is p = .01, worth 7.056 each.

Nothing else on any hill is new:

- the Kobon boards tie 93 at n = 18 or reach 468 = n(n−3)/3 at n = 39;
- BB6 runs are far below the known BB(6) lower bounds;
- the matrix boards are at support 139 or 153;
- the Grothendieck boards sit at the CHSH value √2;
- the Collatz weighted coverage was already saturated by the organizer reference account (3 rules, 20 Sep);
- no Erdős 3 proof was submitted.

Among packets scored 0, only Sakana's Grothendieck theorem qualified, and it is now counted.

**Difficulty values.** These are used unchanged, as ruled, and they cannot change any placement (section 7.5). Section 9 lists concrete calibration problems I found in the OPDP-extension values, with twelve fixes for future editions.

---

## 1. Chair rulings applied in this audit

The chair issued these rulings on 4 October 2026. Where they depart from the handbook (`OpenMath-Judging/contestants/EVENT/02-papers/competition_handbook_final.pdf`), the departure is noted. Section 10 recommends publishing them as rule amendments together with the results.

| # | Ruling | Effect | Handbook reference |
|---|---|---|---|
| R1 | **Lenient deadline treatment.** Sakana's source ZIP (received 06:19:17 CEST, 19 minutes after the 06:00 CEST cutoff) is accepted. The on-time PDF (05:57:20) and repository access given at 05:57 made the content available. Pending official-receipt holds for other entrants are treated the same way. | Sakana's results are scored. | §8 allows only administrative cures after cutoff. |
| R2 | **Difficulty values from the OPDP extension are accurate and used unchanged.** | All D values are as recorded in `review/review-data.json`. | §3.3 asks for a three-assessor median for new targets. |
| R3 | **Every result that is new mathematics, is formalized (or certified by an approved exact checker) and runs is counted**, even when another entrant later or independently did better. | Superseded but new results keep their own score (Rohith's K(39) ≥ 470, Sakana's Ramsey bound). New formalized results that were scored 0 are counted. The per-entrant family union still applies, so one entrant cannot stack several results in one family. | Consistent with §6 (independent results each earn entrant credit). |
| R4 | **No bonuses.** The 1.1× focus multiplier and any significance bonus are removed. | b = 1 for every family. | §4.1 (focus bonus 1.1). |
| R5 | **Collatz** earns its small value only if the entrant produced novel mathematics, even mathematics that does not bring the conjecture closer. | Novelty tested in section 5.5. None was found, so the score is 0. | §5, prior mathematics. |
| R6 | **Two classes only: Company and Non-company.** Individual and team are merged. | Rankings are per class. | §2.2, §4.1 (three classes). |
| – | **Leanification five-person exception** (an earlier chair ruling): raw M2 count 1, adjusted ranking value 0.8. | Kept as recorded. | §2.2 (entrants of one to four people). |

The modality multiplier is unchanged: M3B variations still count ½.

---

## 2. Sources and method

### 2.1 Documents read

- The handbook, all ten sections, including the scoring formula on page 3 (checked against the rendered page) and the progress bands in §5.
- The OPDP methodology (`judging/methodology-extracted.txt`, `judging/Ulam_OPDP_Methodology_v1.0.docx`), the atlas README (`judging/README.md`), the CFSD-1000 definition (`review/review-data.json → difficulty_method`) and the 100-problem week list.
- The **current preliminary report**: `review/OpenMath-compact-review.txt` / `.pdf` (3 Oct, 14:50 CEST), with `review/review-data.json` (all 226 result rows and 70 problem profiles), `review/score-signoff.csv`, `review/contribution-signoff.csv`, `review/review-validation.json`, and the contribution notes in `review/entries/` and problem profiles in `review/problems/` for every scored, contested or hill row.
- The earlier first pass, `judging/PRELIMINARY-JUDGING.txt` (3 Oct, 12:10 CEST). It is superseded; it is cited only where it records something the later report dropped.
- Contestant packets, read directly from the original archives:
  - Sakana: the `Math_Competition_Completed_Results_Submission` bundle, in particular `CLAIMS.json`, the focus cards, `REPRODUCE.md`, `REPLAY_PROJECTS.json` and the Lean sources of every project built;
  - HTPeo: repository snapshot `76c63b8`;
  - Chandragupt: repository snapshot `479c241`;
  - Chaewon: novelty statement and results;
  - Jamie: H4;
  - the hill leaderboard snapshots in `contestants.json` and `outputs/` (observed 3 Oct, 08:37 UTC);
  - event pages and correspondence.

### 2.2 Independent checks run

Every script is in `scripts/`, and Appendix B gives the commands.

- **Score arithmetic:** recomputed for every row and entrant, both under the original rules and under the rulings (`final_scores.py`, which produces `final-scores.csv`).
- **Fresh Lean builds:** copy the entrant's own sources, pin the recorded Lean toolchain and Mathlib commit, fetch the official Mathlib cache with `lake exe cache get`, build the selected endpoint modules from source (no entrant `.olean` files are used) and run `#print axioms` on every endpoint named in the entrant's replay plan.
- **Exact and exhaustive checks:**
  - exact Ramsey numerators by multi-modular arithmetic (`ramsey_exact_numerator.py`);
  - the Collatz format ceiling and the classical stopping-time sets;
  - an elementary proof of A100475;
  - Ramsey densities recomputed from both certificates;
  - Chandragupt's Brent identities and support;
  - the half-turn gap by exhaustive enumeration for n ≤ 8;
  - the Kobon catalogue against upper bounds, monotonicity and Füredi–Palásti;
  - a numerical exploration of the three-row Grothendieck ratio;
  - reproduction and sensitivity analysis of every local CFSD-1000 D value.

### 2.3 Not done

- **A second human referee reading of every proof.** Handbook §9.1 step 4 requires two qualified reviews. That remains the chair's process step.
- **Complete literature searches** for every novelty claim. Section 8 lists the specific checks still owed.
- **Builds of every project.** Builds not completed in this audit are listed as such in Appendix A, and nothing is claimed for them.

---

## 3. Verification results

### 3.1 Arithmetic

- **Rows:** all 226 rows of `review-data.json` reproduce `F = b·m·p·D²/1000` exactly with the report's inputs, and every entrant's S and A reproduce.
- **Families:** no family appears twice within one entrant.
- **Example:** under the original rules, Sakana's total is 1697.401122. That is the sum of 15 family values, with two M3B families at m = ½ and three M1 focus families at b = 1.1.

### 3.2 Fresh Lean builds (summary)

Full details are in Appendix A. Every completed build compiled with exit code 0, and every audited endpoint depends only on standard axioms. No `sorryAx`, no `Lean.ofReduceBool` (that is, no `native_decide`) and no custom axioms were found.

| Entrant | Result | Lean / Mathlib | Endpoints audited | Status |
|---|---|---|---|---|
| Sakana | Erdős–Lovász +3 residual (`erdos21-sharp-residual`) | 4.34.1 / `d13f23b` | `residual_cover_bound_sharp`, `cover_bound_sharp`, `erdos_lovasz_lower_three`, … | ✅ 3113 jobs, standard axioms; definitions of uniform, intersecting, cover number and degree checked to be the standard ones |
| Sakana | A100475 (`a100475`) | 4.33.1 / `0df444a` | `OeisA100475.not_periodic`, `.conjecture` | ✅ |
| Sakana | A060957 (`a060957`) | 4.33.1 / `0df444a` | `subset_product_counterexample`, `interpolation_conjecture_false`, two arbitrary-gap theorems | ✅ |
| Sakana | OPDP13 quartic (`opdp13`) | 4.34.1 / `d13f23b` | 5 endpoints (exponent semigroup, lower bound, log growth, near-boundary upper bound, least index) | ✅ |
| Sakana | RBM4 parity (`opdp89-parity-sharp`) | 4.33.1 / `0df444a` | `sharp_parity_classification`, `collapsed_local_max_iff`, `nonstable_parameter_saddle` | ✅ |
| Sakana | Half-turn gap (`opdp43`) | 4.34.1 / `d13f23b` | `grid_half_turn_gap`, `sharp_half_turn_gap` | ✅ |
| Sakana | Ferrers / Latin tableau (`ferrers`) | 4.33.1 / `0df444a` | 4 endpoints | ✅ |
| Sakana | Erdős 169, sum > 111/25 (`erdos169-fourap`) | 4.34.1 / `d13f23b` | `explicit_four_ap_free_reciprocal_gt` | ✅ |
| Sakana | Erdős 944 order bound | 4.34.1 / `d13f23b` | `erdos944_order_linear`, `_quadratic`, `_exact` | ✅ |
| Sakana | Erdős 1060 partial bound | 4.33.1 / `0df444a` | `canonical_count_eventually_upper`, `canonical_count_upper`, `entropyConstant_lt_old` | ✅ |
| Sakana | Grothendieck restricted bounds (FOCUS-GROTH) | 4.33.1 / `0df444a` | `row3_Q_le_sqrt_three_halves_mul_C` + 4 semantic cases | ✅ |
| Sakana | Erdős 3 finite obstruction (FOCUS-E3 + pullback bridge) | 4.33.1 / `0df444a` | 5 + 3 endpoints | ✅ |
| Sakana | Erdős 829, log(5/3) | 4.33.1 / `0df444a` | `canonicalCubeCount_eventually_exp`, `…_eventual_threshold` | ✅ |
| Sakana | Ramsey lifting (FOCUS-RAMSEY) | 4.33.1 / `0df444a` | `lifting_bound`, `density_tendsto`, `density_sub_P_abs_le`, `RamseyC4.c4_le_Pval` | ✅ |
| Sakana | Matrix one-leg rigidity, seed 0 (FOCUS-MATRIX-seed0) | 4.33.1 / `0df444a` | `rational_injective_{uv,uw,vw}`, `remaining_factor_unique_{uv,uw,vw}` | ✅ 1764 jobs |
| Chandragupt | Support-138 certificate (`lean/`, core Lean only) | 4.34.1 / none | `scheme138_valid` (no axioms), `scheme138_identities` (`propext`, `Quot.sound`), `scheme138_support` (no axioms) | ✅ 9 jobs; `gen.py --check` matches the JSON data |
| HTPeo | Generic Ramsey lifting (`RamseyCert.Limit`) | 4.33.1 / `0df444a` | `ramseyMultK4_le_density : T.Symmetric → 0 < T.total → ramseyMultK4 ≤ T.density` | ✅ The 2,048 per-chunk kernel-count modules (about 4 h here) were replaced by an exact independent recomputation of the numerator (3.3) |
| HTPeo | Kobon K(39) ≥ 471 (`KobonCert`) | 4.33.1 / `0df444a` | `kobon_lower_bound`, `kobon_nonoverlapping` (471 pairwise-disjoint open triangles from 39 distinct real lines) | ✅ 1145 jobs |

**A build checks the encoded statement, not its fidelity to the registered target.** Statement fidelity was spot-checked for Erdős 21, A100475, A060957 and the support-138 certificate. The second referee should repeat this for the rest.

### 3.3 Independent numerical, exact and exhaustive checks

| Check | Result |
|---|---|
| HTPeo Ramsey template (`solution_v2.json`, n = 1024, Q = 50,762,939) | **Exact** numerator recomputed by multi-modular arithmetic (7 primes, CRT): 200137750014677779172692777477 / 50762939⁴ = **0.030139911990**, identical to the claimed rational. |
| Sakana Ramsey template (`FOCUS-RAMSEY/certificate/solution.json`, Q = 47,314,248) | **Exact:** 75525646867723584998137743109 / 2505750190359427899123170347008 = **0.030140932308**, identical to the claim. |
| Reference values | McKay (final note of arXiv:2206.04036, the hill's reference): 10486266368/768⁴ = **0.030142273432**. Parczyk–Pokutta–Spiegel–Szabó Theorem 1.1: 0.030144857036. Both entrants beat both. |
| Chandragupt support-138 scheme | 23 terms, support **138**, **729/729** Brent identities hold exactly, in the convention declared in his Lean README. |
| Collatz, hill-format ceiling | Over all rule sets permitted by the hill (exact valuations, k ≥ E+1, descent at the least representative), at most **1,765 / 2,048** odd classes mod 4096 can be covered, and at most **94 / 128** mod 256. The classical stopping-time set (Terras) is 1,822 mod 4096 and 109 mod 256. |
| A100475 | Elementary proof confirmed: Rosser's p_n > n ln n gives T(n) > n for every n ≥ 22,027, and no orbit below that threshold is periodic. Only 17 values of n have T(n) ≤ n, all at most 1,221. Sakana's Lean proof follows the same growth-plus-finite-check route. |
| Half-turn gap | Exhaustive enumeration of all 2n-point no-three-in-line sets for n ≤ 8: the minimum positive one-sided miss is 4, attained at n = 5 and n = 8. This is consistent with the theorem. |
| Kobon catalogue (Rohith, 66 rows) | No row exceeds the Tamura / Clément–Bader upper bound. Only **12 of the 46** rows labelled candidate survive the two necessary checks (section 5.4). |
| Grothendieck, three-row sign matrices | The numerical supremum of Q/C found is about **1.178** (equal weights give 2/√3 ≈ 1.1547). Sakana's proved bound √(3/2) ≈ 1.2247 is valid, but probably not sharp. |
| CFSD-1000 D values | All 61 local profiles reproduce exactly from their stored components (section 9). |

---

## 4. Assessment of the preliminary report

### 4.1 What is right

- The scoring formula, the family-union logic and all arithmetic.
- Correct identification of the large structural risks: the late Sakana ZIP, the absence of fresh builds, single-assessor D values, missing sources (Qichao), incomplete geometry (Raj) and incomplete covers (Heilbronn).
- Zero scores for unformalized or unverifiable work, and the separation of M2 counts from S and A.
- The Chandragupt hold was correctly resolved: the complete pinned source is present and the tensor identities check.
- The HTPeo / Chaewon Collatz duplication (an identical union) and Jamie's subset relation are correct.
- The numerical reading of the Ramsey prior work (McKay reference; Parczyk et al.) is correct, and both entrant bounds beat it.

### 4.2 Errors and inconsistencies

| # | Finding | Effect | Resolution under the rulings |
|---|---|---|---|
| E1 | **Collatz credit without novel mathematics.** Chaewon (6.556) and Jamie (6.556) were credited, while HTPeo's identical coverage got 0. The submitted unions equal the hill-format ceiling and are subsets of the classical stopping-time set; the hill's public weighted coverage was already saturated by the organizer reference account `ottogin` with 3 rules on 20 September. | Both scores were wrong and inconsistent. | **0 for all Collatz entries** (R5; section 5.5). |
| E2 | **Ramsey focus bonus inconsistent.** Ramsey alone was kept at b = 1, although the hill list names it one of the six organizer-deck problems alongside Kobon, Collatz, matrix, Grothendieck and BB6, which all got b = 1.1. | ±3.528 for Sakana and HTPeo. | Moot: b = 1 everywhere (R4). |
| E3 | **Kobon novelty labels.** 34 of Rohith's 46 rows labelled "candidate" are at or below the general Füredi–Palásti construction ⌊n(n−3)/3⌋ (e.g. n = 80: 1,767 against 2,053), or below an earlier row of the same catalogue (K(n+1) ≥ K(n)). | None (one parent family), but the labels are wrong. | Correct the labels (section 5.4). |
| E4 | **Entrant class:** Chandragupt (one person) was labelled a team. | Ranking class. | Moot (R6). |
| E5 | **No pinned pre-cutoff commit for Sakana.** The 05:57 e-mail gave access to `SakanaAI/autolab-100`, but the report pins no commit. | Timing gate. | Moot (R1). Still recommended for provenance (section 10). |
| E6 | **Sakana's Grothendieck theorem scored p = 0** although it is a formalized theorem not located in the literature. | −3.147 for Sakana. | Counted at p = .01 (R3; section 5.1). |
| E7 | **Inconsistent "known versus open" treatment of short proofs of OEIS conjectures.** A100475 (Rosser plus a finite check) was scored as a complete open target (M3A, 292.681); A046969 Conjecture I (von Staudt–Clausen / Kummer) was kept as M2. | Up to +119.716 for Sakana if made consistent. | Chair decision (section 8, item D1). |
| E8 | **The DMS band (P3) depends on a check not yet done** (removing the previously known five-colour classes), which the report itself names. | HTPeo's DMS score: 49.421 (P3) or 16.474 (P2). | P3 kept provisionally; fallback stated (section 8, item D3). |
| E9 | **HTPeo's 10 counted M2 families are not listed in the summary**, only "10 of 17". | Transparency. | Listed in section 5.2. |
| E10 | **All new D values come from a single assessor, assigned after the solutions were read.** The report itself labels even the "published" values "companion scale candidate only; frozen mapping not verified". | Scale and calibration risk. | Used unchanged (R2); recommendations in section 9. |

---

## 5. Entrant-by-entrant assessment

The notation follows the handbook: D is difficulty, m the modality multiplier (M3B = ½), p the progress coefficient, and F = m·p·D²/1000 with b = 1.

### 5.1 E02 Sakana AI team (Company): Rachel Teo, Wenyi Wang, Hamdi Abderrahmene

Delivery: a PDF at 05:57:20 CEST and a ZIP at 06:19:17 CEST, accepted under R1. Formal status: 16 projects rebuilt fresh by this audit (section 3.2); only A000224 and matrix-rigidity seeds 1–2 were not.

| Family | Exact accepted claim (short) | Modality | D | m | p | **F** | Verified here |
|---|---|---|---:|---:|---:|---:|---|
| ERDOS21-VARIANT | 4τ(J) ≤ \|J\| + r + 3 for intersecting r-uniform hypergraphs of maximum degree ≤ 3, lifted to all; answers the +3 question asked after Lemma 2 of arXiv:2606.24878 (July 2026). Sharpness example from the source paper. | M3A | 555 | 1 | 1 | **308.025** | Fresh build; definitions checked |
| OEIS-A100475 | No positive start has an ultimately periodic orbit under n ↦ reverse(p_n) | M3A | 541 | 1 | 1 | **292.681** | Fresh build; elementary proof re-derived |
| OEIS-A060957 | Refutes the whole-interval subset-product interpolation conjecture; arbitrary-length exponent gaps | M3A | 527 | 1 | 1 | **277.729** | Fresh build |
| RBM4-PARITY | Sharp classification of collapsed points for the 4-visible / 1-hidden RBM under four-parity data | M3B | 727 | ½ | 1 | **264.2645** | Fresh build |
| OPDP13-QUARTIC | Exact exponent semigroup and sharp boundary scale for the quartic Hermitian power family | M3B | 644 | ½ | 1 | **207.368** | Fresh build |
| NO3-HALFTURN | One-sided half-turn miss of a 2n-point no-three-in-line set is 0 or ≥ 4; sharp at a 5×5 witness | M3A | 330 | 1 | 1 | **108.900** | Fresh build; brute force n ≤ 8 |
| LATIN-TABLEAU | Ferrers defect hierarchy (partial toward the Latin tableau question) | M3A | 650 | 1 | .15 | **63.375** | Fresh build |
| OEIS-A000224 | Excludes products of three distinct odd primes (infinite subcase) | M3A | 622 | 1 | .15 | **58.0326** | Build not completed (Appendix A) |
| RAMSEY-K4 | c₄ ≤ 0.0301409323 (weighted 1024-block template, formal lifting) | M3A | 840 | 1 | .05 | **35.280** | Exact density recomputed; lifting rebuilt |
| ERDOS944 | Necessary order bound n ≥ (27r+19)/4 (finite regime) | M3A | 721 | 1 | .05 | **25.99205** | Fresh build |
| ERDOS1060 | Uniform exponent constant ≈ .363272 < log 3/3 | M3A | 574 | 1 | .05 | **16.4738** | Fresh build |
| ERDOS169 | Explicit finite four-AP-free set with reciprocal sum > 111/25 = 4.44 (beats Walker's 4.43975) | M3A | 538 | 1 | .05 | **14.4722** | Fresh build |
| ERDOS829 | Coefficient log(5/3) in the subexponential bound | M3A | 530 | 1 | .05 | **14.045** | Fresh build |
| MATRIX-3 | One-leg rigidity of three known support-139 seeds | M1 | 724 | 1 | .01 | **5.24176** | Seed 0 fresh build (6 endpoints); seeds 1–2 not rebuilt |
| ERDOS3 | 79-point strong-L-free witness mod 13 beats every diagonal pullback (≤ 78); cyclic 4-AP-free maximum is 6 | M1 | 674 | 1 | .01 | **4.54276** | Fresh build of both certificates |
| GROTHENDIECK | Q(A) ≤ √(3/2)·C(A) for every 3×n sign matrix; √2 bounds for four named matrices | M1 | 561 | 1 | .01 | **3.14721** | Fresh build; numerical check |
| BB6 | 6-state machine halting after 1,235,211 steps | M1 | 974 | 1 | 0 | 0 | Not new (far below known BB(6) bounds) |
| **Total** | | | | | | **S = 1699.56988**, **A = 308.025** (ERDOS21-VARIANT) | |

**M2 (company class): 10 families.**

- M2-BERNOULLI (A046969 Conjecture I)
- M2-QUATERNION (OPDP67)
- M2-LCM-RECURRENCE (A135508)
- M2-APERY (odd prime-power irreducibility)
- M2-BASE3
- M2-THETA
- M2-WOLSTENHOLME
- M2-LCM-MATRIX (A060841)
- M2-ERDOS887 (constant 40)
- M2-POLYGON

**Notes.**

- **Grothendieck (newly counted, R3).** The theorem is formalized, builds, and no prior occurrence was located (Ben Li, arXiv:1712.08506, treats arbitrary real coefficients, which is a different statement). It is a narrow certified fact, P1 at its lower end. My numerical search suggests √(3/2) is not sharp: the supremum found is about 1.178.
- **Erdős 3 (kept at .01).** This refutes a finite auxiliary ansatz (diagonal pullbacks) with an exact witness. It is new and formalized, so it counts under R3. Its relevance to the parent problem is limited, which is why it sits at the lowest P1 value.
- **A046969 Conjecture I** is kept as M2, as Sakana itself proposed ("do not assert original-open novelty"). See section 8, item D1, for the consistency question with A100475.
- **Superseded results** still count (R3): HTPeo's Ramsey bound is stronger, but Sakana's is itself a new bound. Sakana's own later board runs (0.0301400185 on 3 Oct) fall in the same family, so the family score does not change.
- **No duplicate modality credit:** the entrant-proposed alternatives (M3A versus M3B for OPDP13 and RBM4, M1 versus M2 for the focus items) were checked and each contribution counts once.

### 5.2 E08 HTPeo (Non-company): Woohyuk Kang, Hyunjin Lee, Sanghyeon Lee, Youchan Oh

| Family | Claim | Modality | D | p | **F** | Verified here |
|---|---|---|---:|---:|---:|---|
| DMS | Five-colour proofs for specified infinite families (snark / Petersen / Möbius / inflation); six colours for bridgeless cubic loopless multigraphs up to 14 vertices; reduction and equivalence library (conjecture itself not claimed) | M3A | 574 | .15 (P3) | **49.4214** | Not rebuilt (four Lean packs, about 250 modules; Appendix A) |
| RAMSEY-K4 | c₄ ≤ 200137750014677779172692777477/6640289795261907019148161833841 ≈ 0.030139911990, with a generic formal blow-up / limit theorem | M3A | 840 | .05 | **35.280** | Exact numerator recomputed; lifting theorem rebuilt |
| KOBON | K(39) ≥ 471 (new; Füredi–Palásti gives 468, Rohith 470) | M1 | 570 | .01 | **3.249** | Recount by the review; fresh Lean build |
| BB6, CHSH, matrix 139, Collatz 234, Kobon n = 18 (93) | Baseline reconstructions | – | – | 0 | 0 | Not new |
| **Total** | | | | | **S = 87.9504**, **A = 49.4214** (DMS) | |

**M2: 10 families counted.**

- Petersen / Schönberger perfect matchings (G-PM)
- E942
- E44
- E123
- E918
- E292
- E395
- E698
- E939
- E477

Held as minor or sanity helpers (7): E295, E703, E748, E1136, E358, E619, E1148. Excluded as wrappers the team did not claim (6): E757, E261, E36, E649, E508, E1038.

E939, which exhibits explicit r = 7 and r = 8 examples, is the weakest of the counted ten; the chair may move it to the held list. That would make the count 9 and change no placement.

**Not new (checked).**

- **Erdős #1038:** HTPeo's own notes record that a public Lean proof of the same result existed from 15 September (`plby/lean-proofs`) and that the work followed it.
- **BB6:** a 249,881-step witness. The formal theorem `Counter.big_halting` concerns a non-blank start configuration. The "largest 5-state halting time below 250,000 = 134,467" computation is not formalized and can be derived from the 2024 BB(5) census.
- **DMS:** P3 holds only if the infinite families and reductions survive comparison with the previously known five-colour classes (Dvořák–Mohar–Šámal 2013 and later work). Fallback P2 (.05): DMS = 16.4738, S = 55.0028, A = 35.280. Under either value HTPeo stays first in the non-company class on S and A.

### 5.3 E04 Chandragupt Sharma (Non-company)

| Family | Claim | D | p | **F** |
|---|---|---:|---:|---:|
| MATRIX-3 | Rank-23 scheme for 3×3 matrix multiplication with support 138, one below the 139 of Smirnov 2013 (best located) | 724 | .05 | **26.2088** |

- **Verification:** exact check of all 729 identities; fresh build of the core-Lean certificate (validity and support theorems use no axioms); `gen.py --check` matches the JSON data.
- **Same family, no extra credit:**
  - the gauged support-138 variant;
  - the one-parameter rational family (checked symbolically by the review, but not formalized by the entrant);
  - a separate support-143 scheme (no improvement);
  - an unsuccessful search for support 137.

S = A = 26.2088; M2 = 0.

### 5.4 E57 Rohith Poola (Non-company)

**Scored family:** KOBON, D 570, p .01, **F = 3.249**.

- **New math (R3):** yes. K(39) ≥ 470 beats the general bound 468 and counts, although HTPeo's 471 is stronger.
- **The catalogue of 66 exact witnesses:** all triangle counts were recounted independently by the review. My two additional necessary tests were:
  1. *Monotonicity.* Adding a line far from all vertices keeps every bounded face, so K(n+1) ≥ K(n). Nine "candidate" rows (n = 58, 62, 66, 74–79) are below an earlier row of the same catalogue; n = 74–79 sit below the 1,727 of the perfect n = 73 arrangement.
  2. *Füredi–Palásti (1984) general construction,* K(n) ≥ ⌊n(n−3)/3⌋. This is the "classical general construction gives 468" at n = 39 recorded in HTPeo's packet. 34 of the 46 candidate rows are at or below it. For example, the n = 80–95 rows are 28–286 triangles below it.
- **Surviving candidates (12):** n = 39, 40, 44, 47, 48, 52, 55, 56, 61, 64, 72, 96, each 1–11 triangles above Füredi–Palásti. These are the only rows that could be new best-known lower bounds. They need comparison with the current Kobon tables, ideally by a second reviewer independent of the chair, who has published Kobon lower bounds himself (section 10).
- **The family union stays P1.** The report's .01 is kept. If several of the 12 rows are confirmed as new records, a written rationale under §5 ("start at the lower end unless a written rationale supports more") could justify .02–.03 (6.50–9.75). That would not change any placement.

### 5.5 Collatz: E05 Chaewon Yoon, E10 Jamie Steeg (H4), E08 HTPeo; all Non-company

**Ruling R5 test: is there novel mathematics? No.**

- **The rule format.** The hill's certificate format is a tuple (k, r, [e₁…e_s]). It certifies that every n ≡ r (mod 2^k) descends after s accelerated Syracuse steps with exact valuations (k ≥ E+1, 3^s < 2^E, descent at the least representative). This is the classical stopping-time framework (Terras 1976; Everett 1977), and Chaewon's novelty statement says so: "No invention of those methods is claimed."
- **What the format can reach.** Enumerating every rule the format allows shows that **no rule set can cover more than 1,765 of the 2,048 odd classes mod 4096** (`scripts/collatz_ceiling.py`).
  - Chaewon (512 rules) and HTPeo (234 rules) both reach exactly this ceiling.
  - Jamie's bounded classification (k ≤ 8, depth ≤ 4) reaches **94 / 128 mod 256, which is again the ceiling at that modulus**. Enumerating the valid bounded rules (309 of 1,016 prefixes) is a direct finite computation of the same classical property.
- **These sets are contained in the classical stopping-time sets** (1,822 mod 4096 and 109 mod 256), which are known mathematics.
- **The hill's weighted metrics** (coverage 1,000,000 ppm; minimum descent 525,390 ppm) were already reached by the organizer reference account `ottogin` with 3 rules on 20 September, and by `yavol` on 21 September, both before the event.
- **None of the three entries is a Lean formalization.**

Result: **0 original points** for Chaewon, Jamie (H4) and HTPeo (Collatz). Jamie keeps M2 = 1 (`ap_subprogression_of_le`, `ap_frequently_iff_every_length`). Chaewon's BB6 board run (249,614 steps) is not new.

### 5.6 E06 Leanification (Non-company): Augusto, Felipe Leria, Mateus, Tiago, Luca Seiki Pereira Fujii

- **M2 = 1:** Campos–Samotij hard-core hypergraph containers, Theorem B, with Proposition 2.2 and Lemmas 4.1–4.3 in the same family.
- **Adjusted ranking value 0.8** under the chair's five-person exception.
- **No original points.** A fresh build was not completed (Appendix A). The review's static reading reports standard axioms only.

### 5.7 E11 Leon Koerbs / Cameron Fen (Non-company)

- **M2 = 3:**
  - the three-term case via an external Kelley–Meka formalization;
  - the dyadic per-length extremal equivalence for every K ≥ 3;
  - the Gowers-norm four-term groundwork.
- **The finite harmonic construction (4.314) is not new.** It is below Walker's 4.43975 (and below Sakana's > 4.44), so it is not new mathematics and scores 0.

### 5.8 E65 Wilson Wu (Non-company)

- **M2 = 2:**
  - dyadic hill / extremal equivalence (k ≥ 4);
  - the AP interface with conditional three-term bridges. The conditional bridge is not a proof of the analytic bounds.
- **Independence review needed.** These overlap with Leon/Cameron (dyadic) and Jamie (AP conclusion). Each entrant keeps its own count only if the independence review (§6) finds the work sealed and independent. The Collective Frontier counts each result once.

### 5.9 E09 Raj Harshit Srirangam (Non-company)

- **Claims:** K(18) ≤ 94 with arbitrary multiplicities; ≤ 93 for multiplicity ≤ 3; K(14) = 54; even-n triple-point bounds.
- **New if proved, but not established.** The LP/DP/SAT/DRAT certificates check combinatorial encodings, but the geometric reduction (arrangement → constraint system) is neither formalized nor verified.
- **Result: 0.** Under the handbook, formalizing the chain after the cutoff is new work, not an administrative cure. The potential value if the chain had been complete at cutoff, without the bonus, would have been .05 × 324.9 = 16.245.

### 5.10 E03 Matt Bowring, E12 Frederik Smits van Oyen, E17 Qichao Wang (Non-company)

- **Matt.** The (21/48)·4ⁿ CNOT coefficient would be new if proved. The proof is nonrigorous and the entrant states it is not in Lean. **0.**
- **Frederik.** The nine-point Heilbronn cover is incomplete (2,581 unresolved and 529 missing leaves; boundary not covered), and the local bounds use tolerances. **0.**
- **Qichao.** The detailed Černý declarations are formal by description, but the 27 MB source was never received, so nothing can be run. **0 now.** If the pre-cutoff source is delivered (an administrative cure under R1), the review's five M2 groups can be evaluated, with a potential M2 count of up to 5.

---

## 6. Do the hills and the zero scores contain new mathematics?

### 6.1 Hill by hill

Sources: leaderboard snapshots observed 3 October, 08:37 UTC (`OpenMath-Judging/contestants.json`, `leaderboard_runs`). The event window opened 27 September at 16:00 UTC.

| Hill | Best values on the board | State of the art at freeze | New mathematics? |
|---|---|---|---|
| **Ramsey K₄ multiplicity** (`clique-cluster-ramsey-multiplicity`) | `lavaskiller` (HTPeo) 0.030139911990 (3 Oct); `wenyi-ai-wang` (Sakana) 0.030140018465; `a-hamdi` (Sakana) 0.030140048474; **`madhanj05` (E01) 0.030140335647 (2 Oct)**; `rachtsy` (Sakana) 0.030140930507; `hl728` (HTPeo) 0.030141720946; `yavol` (E66) 0.030141721098 (**21 Sep, pre-event**); **`danamouk` (E43) 0.030142036534 (28 Sep)**; `n0rang2` (HTPeo) 0.030142185839; **`shaff622` (E15) 0.030142250482 (27 Sep)**; `rohith18p` 0.030142314506 (reference not beaten); `ottogin` 0.030142649543 (organizer, not beaten); `vyahhi` 0.030144857036 (exactly Parczyk et al. Theorem 1.1) | McKay 0.030142273432 | **Yes.** Beyond HTPeo and Sakana (already scored), three accounts posted in-window bounds below McKay: E01, E43, E15. E66's is pre-event. See 6.3. |
| Kobon (`kobon-triangles`) | n = 18: 93 by several accounts (ties); 92, 91, 90 below. n = 39: `lavaskiller` 471, `rohith18p` 470, `octavianboji` (E55) 468 | K(18) ≥ 93; K(39) ≥ 468 (Füredi–Palásti) | Only HTPeo's 471 and Rohith's 470, both scored. E55's 468 equals the classical construction. |
| 3×3 matrix multiplication | Chandragupt rank 23 / support 138; everyone else 139 or 153 | Rank 23 / support 139 (Smirnov 2013) | Only Chandragupt's 138, already scored. |
| Grothendieck witnesses | All entries: gap 1.414213 (√2), area 4 | √2 is the CHSH / Tsirelson value; the real constant is known to be ≥ 1.676 (Davie, Reeds) | **No.** (Sakana's restricted theorem is in its packet, not on the board.) |
| BB6 certificates | Best 572,171 steps (`vyahhi`); others 178,727–249,881 | Known BB(6) lower bounds are astronomically larger (beyond 10↑↑15 since 2022) | **No.** |
| Collatz modular descent | Every entry: coverage 1,000,000 ppm, minimum descent 525,390 ppm, including `ottogin` (3 rules, 20 Sep) and `yavol` (21 Sep) | Classical stopping-time sets | **No** (section 5.5). |
| Erdős #3 (Lean proof of a fixed statement) | No accepted proof | Open | **No.** |

### 6.2 Zero-score entrants with packets or projects

| Entrant | Material | New mathematics, formalized and running? |
|---|---|---|
| E03 Matt Bowring | Synthesis coefficient | Claimed; not proved and not formalized → **no** |
| E05 Chaewon Yoon | Collatz 512 rules; BB6 run | **No** (section 5.5) |
| E06 Leanification | Known theorem formalization | Formalization only → M2 = 1 |
| E07 Hypernym | Pre-event Ramsey and BB search | Pre-event, not event output → **no** |
| E09 Raj Srirangam | Kobon upper bounds | Claimed; geometric reduction unverified → **no** |
| E10 Jamie Steeg | Collatz H4, conditional Kobon, baselines, AP bridge | **No** original mathematics; M2 = 1 |
| E11 Leon / Cameron | Harmonic 4.314; Erdős 3 infrastructure | **No** original (below Walker); M2 = 3 |
| E12 Frederik | Heilbronn partial cover | Incomplete → **no** |
| E13, E14 | Research leads | No formal result → **no** |
| E17 Qichao | Černý formal cores | Source missing → cannot run (potential M2 up to 5) |
| E65 Wilson Wu | Erdős 3 equivalences | M2 = 2 |
| E01, E15, E43 | Ramsey board values | **Yes, conditionally** (6.3) |
| E34–E66 (board-only accounts) | Board metadata | Only the Ramsey items above; everything else is a tie or below the state of the art |
| E16, E18–E33, E47, E56, E59, E67–E74 | No result, organizer accounts, or interest only | **No** |

Within scored packets, the zero-point items were rechecked as well:

- **Sakana Grothendieck:** new → now counted.
- **Sakana BB6:** not new.
- **HTPeo baselines, Erdős 1038 and the BB(5)-spectrum computation:** not new, or not formalized.
- **Chandragupt's support-143 scheme and parametric family:** no improvement, or not formalized by the entrant.

### 6.3 Recommendation for the three Ramsey board-only bounds

- **What the values show.** A Ramsey hill value is the exact blow-up density of a submitted template, computed by the hill's evaluator. The step from a template density to an upper bound on c₄ is a standard blow-up argument, and HTPeo and Sakana have formalized it generically (`RamseyCert.Limit`, `Lea.RamseyLifting`).
- **What is missing.** None of the three accounts sent the template, so the jury cannot run anything today.
- **Recommendation:**
  1. Retrieve each `solution.json`, through the AutoLab hill owner or directly from the entrant.
  2. Re-verify the density (`scripts/ramsey_density.py`, then the generic Lean lifting).
  3. Confirm the run time for `shaff622` was after 16:00 UTC on 27 September.
  4. Confirm the roster for `danamouk`.
- **Scoring.** If verified, score each at **P1 lower end, p = .01: F = 7.056** (D 840). The rationale for .01 rather than HTPeo's and Sakana's .05 is that those entrants also supplied the exact rational certificate and a formal finite-to-limit theorem; the board-only accounts supplied only the template.
- **Placement consequences.** If the chair prefers .05 for consistency, each would score 35.280, and E01 would rank above Chandragupt in the non-company S ranking. At .01 they rank between Chandragupt and Rohith, in timestamp order (`shaff622` 27 Sep, `danamouk` 28 Sep, `madhanj05` 2 Oct) per the §4.2 tie rule.

---

## 7. Final scores and rankings

### 7.1 Company class

| Rank | Entrant | S | A (family) | M2 |
|---|---|---:|---|---:|
| 1 | E02 Sakana AI team | **1699.56988** | **308.025** (ERDOS21-VARIANT, M3A, complete) | **10** |
| – | E24 Thinking Machines | 0 | 0 | 0 |

### 7.2 Non-company class

**Total output S**

| Rank | Entrant | S |
|---|---|---:|
| 1 | E08 HTPeo | **87.9504** |
| 2 | E04 Chandragupt Sharma | **26.2088** |
| 3 | E57 Rohith Poola | **3.249** |
| – | All others | 0 |

**Biggest accomplishment A**

| Rank | Entrant | A | Winning family, exact claim, status |
|---|---|---:|---|
| 1 | E08 HTPeo | **49.4214** | DMS, infinite five-colour families and reductions (accepted partial, P3) |
| 2 | E04 Chandragupt Sharma | **26.2088** | MATRIX-3, rank-23 support 138 (accepted partial, P2) |
| 3 | E57 Rohith Poola | **3.249** | KOBON, K(39) ≥ 470 and catalogue (accepted partial, P1) |

**M2 formalization families**

| Rank | Entrant | Families |
|---|---|---:|
| 1 | E08 HTPeo | **10** |
| 2 | E11 Leon Koerbs / Cameron Fen | **3** |
| 3 | E65 Wilson Wu | **2** |
| 4 | E10 Jamie Steeg | **1** |
| 5 | E06 Leanification | **1** (adjusted 0.8, chair exception) |

### 7.3 Conditional adjustments

None of these is included in the totals above.

| Item | Condition | Effect |
|---|---|---|
| C1 Ramsey board bounds (E01, E43, E15) | Template retrieved and verified; in-window timing and roster confirmed | +7.056 each at p = .01 (or 35.280 at .05). New non-company entries ranked by S between Chandragupt and Rohith at .01. |
| C2 A046969 Conjecture I as an original result | Chair adopts consistency with A100475 (D1) | Sakana S +119.716 (D 346, M3A, p = 1); M2 10 → 9. No placement change. |
| C3 DMS at P2 | Novelty comparison shows the families are largely known | HTPeo S 55.0028, A 35.280. Still first. |
| C4 Rohith P1 raised | Several of the 12 surviving rows confirmed as records | 6.50–9.75. No placement change at .01 for the others. |
| C5 Qichao source delivered | The pre-cutoff 27 MB source arrives and builds | M2 up to 5 (non-company M2 rank 2). |
| C6 HTPeo E939 moved to held | Chair judges it a trivial example | M2 10 → 9. Still first. |

### 7.4 Every other record

All other records are 0 S, 0 A, 0 M2, with dispositions as in the compact review: no final packet, pre-event work, ties with known values, organizer or reference accounts, or interest only.

### 7.5 Robustness: difficulty values cannot change any placement

- **Company:** Sakana is the only company entrant with points, so any change to its D values moves only its own totals.
- **Non-company:** HTPeo, Chandragupt and Rohith are separated by factors of about 3.4 and 8. Their families' D values (DMS 574, Ramsey 840, Kobon 570, Matrix 724) would have to move by tens of percent in opposite directions to reorder them, far beyond any adjustment considered in section 9.

This confirms the chair's statement that the D values "don't change any placement".

---

## 8. Decisions still open for the chair

| # | Decision | Recommendation |
|---|---|---|
| D1 | A046969 Conjecture I: M2 (as proposed by Sakana) or an original result? | Apply one rule to all short proofs of open OEIS conjectures: either both A046969-I and A100475 count as new mathematics, or neither does. If "listed as an open conjecture at freeze, with no located proof" defines open, A046969-I should move to M3A (C2). |
| D2 | Ramsey board-only bounds (E01, E43, E15) | Request the templates; score at p = .01 if verified (6.3). |
| D3 | DMS band | Ask the second referee to compare HTPeo's families with known five-colour classes; keep P3 only if most are new. |
| D4 | Kobon catalogue | Confirm or reject the 12 surviving rows against current tables (second referee). Fix the labels in the review files. |
| D5 | Literature checks still owed | Ball–Coxeter 13th ed. pp. 14–15 and the Nov–Dec 2004 SeqFan archive (A100475); Powell–Frame 1983 (A046969); Handelman and Tan–To (OPDP13); Fishburn–Reeds and the low-dimension Bell-inequality literature (Grothendieck three-row); current Ramsey multiplicity literature after September 2024; DMS known classes. |
| D6 | Fresh builds not completed here | Appendix A. Rerun with `scripts/fresh_build_*.py` before locking the record (handbook §9.1 step 2). |
| D7 | Two qualified reviews per accepted claim | Still required for "accepted" status (§9.1 step 4). The audit is one independent review. |
| D8 | Publish the rulings R1–R6 | As rule amendments with their rationale, before or together with the results (section 10). |

---

## 9. Difficulty values: observations and recommended fixes

Per R2, nothing in this section changes this round's scores. These observations are offered so that future D values match the mathematics more closely.

### 9.1 How D is currently produced

The competition D is the **CFSD-1000** transform of nine OPDP components.

- **Raw score:** R = 400·AI-relative + 170·intrinsic + 90·human-resistance + 150·inverse-tractability + 45·verification + 35·formalization + 40·prerequisites + 40·context + 30·tool-constraint, with each component in [0, 1].
- **Transform:** D = round(1000·(1 − (1 − R/1000)^1.4)).
- **Reproduction:** all 61 local profiles reproduce exactly from their stored components (`scripts/opdp_cfsd_sensitivity.py`); the other 9 targets reuse published companion values.

### 9.2 Observations

1. **Single assessor, assessed after the solution was known.**
   - All 61 local D values were proposed by one editorial assessor on 3 October, after the solutions had been read.
   - Handbook §3.3 asks for three independent assessments, a median, and assessment before reading the solution where feasible.
   - Post-hoc assessment by one assessor carries a known bias. Entrants register exactly the sub-questions they solved, and the assessor sees a complete proof of something that was labelled a conjecture.
2. **Human-effort and exposure inputs that contradict the methodology's own anchors.**
   - The Erdős–Lovász +3 residual, a question first asked in a July 2026 paper, is given H5 (1,000–3,000 specialist hours) and X3 (broad visibility).
   - The event-created M3B variations (OPDP13 quartic, RBM4 parity) are also given H5/X3, although the methodology reserves X0 for "private, newly posed".
   - Setting H/X to evidence-based levels (H2/X1, or H0/X0 for event-created variations) lowers these D values by 25–50 points, about 10–17% in F.
3. **Parent difficulty borrowed by a sub-target.**
   - MATRIX-3 is registered as "minimum support of rank-23 schemes" but carries the rank problem's H7/X4.
   - Handbook §3.2 says a variation "receives its own difficulty, not its parent's".
4. **The default for missing data sets a high floor.**
   - Missing H and not-applicable tractability default to a neutral 0.5. For a textbook helper (M2-E295, intrinsic 1.0) this supplies 120 of its 203 raw points, and the transform turns 203 into D = 272.
   - With the defaults at 0, the same profile would be D ≈ 114.
   - A textbook lemma at D 272 is worth 74 points at p = 1, more than any non-company entrant's full total except HTPeo's.
5. **The concave transform compresses the top and lifts the bottom.**
   - R = 203 → 272 (+34%); R = 426 → 541 (+27%); R = 730 → 840 (+15%).
   - Because the score is quadratic in D, a complete solution of a modest target outweighs partial progress on a hard one by a large margin. For example, the Erdős–Lovász residual (555) is valued at about 6× a P3 advance on DMS (574).
6. **Sub-question inversions.** The residual +3 constant in a lemma (D 555) sits at the level of the decades-old Kobon problem (570). A lemma-level refinement of a solved problem (Erdős 21 is solved, O(r), by Kahn) should sit well below an open classical problem.
7. **Elementary-proof signal.**
   - A100475 has a proof using Rosser's inequality and a finite check (section 3.3), yet its intrinsic difficulty of 5.4 corresponds to "T3 serious specialist project".
   - The methodology's own T1 anchor is "bounded proof, computation…; resolution may be directly checkable".
   - An indicative re-profile at intrinsic 2.0–3.0 and AI-relative 1.5–2.5 gives D ≈ 306–377, worth 94–142 points instead of 293.
   - This is reported as a calibration case, not a scoring change.
8. **AI-relative difficulty dominates.**
   - It carries 400 of the 1,000 raw points, versus 170 for intrinsic difficulty.
   - The event produced direct evidence: an AI-assisted team resolved several targets rated AI-relative 4.4–6.4 within a week. This is valuable calibration data.
9. **The scale mapping was never frozen.**
   - The first-pass report states that the official frozen target-D register was not recovered.
   - The compact review labels even the reused published values "companion scale candidate only; event frozen canonical D mapping not verified".
   - The event pages preserved in the archive show OPDP bands (T5–T7) for the research catalogue; no CFSD-1000 number appears in them.

### 9.3 Recommended fixes

| # | Fix | Addresses |
|---|---|---|
| F1 | **Freeze D at admission, before the solution is visible.** For targets registered after a solution exists, assign three assessors who see only the canonical statement and the sources. | 1, 6, 7 |
| F2 | **Three independent assessors, median, published spread** (as §3.3 already requires). Record each assessor's identity: human expert, model and protocol, or both. Require a human domain assessor for any target worth more than about 50 points. | 1 |
| F3 | **Evidence-anchored human effort and exposure.** H and X must cite evidence (age of the question, number of papers, citations, documented attempts). Default to H0–H1 / X0–X1 for questions younger than one year and for event-created variations. Require a written justification for H ≥ 3. | 2 |
| F4 | **Fragment and variation rule.** A sub-question, residual constant or variation gets its own profile with no inherited effort, exposure or known-barrier inputs. Cap it at its parent's D. Optionally multiply by a scope factor (e.g. 0.5–0.8) for lemma-level refinements of solved parents. | 3, 6 |
| F5 | **Missing-data policy.** Replace the neutral 0.5 for missing H and not-applicable tractability with evidence-based imputation, or with 0 for known or textbook targets, so that the floor reflects difficulty rather than missing data. | 4 |
| F6 | **Recalibrate the transform for scoring.** Either use a linear map from R for the competition scale, or keep CFSD for the atlas and publish a separate competition scale anchored so that textbook facts sit near 0–100. Alternatively lower the score exponent γ (handbook §4.1 sets γ = 2) when D comes from a concave scale. | 4, 5 |
| F7 | **An anchor ladder with pairwise checks.** Keep 8–10 well-understood anchors (e.g. Collatz 772, Erdős 3 674, Kobon 570, DMS 574, Grothendieck 561, a known textbook lemma at about 100). Require each new D to state which anchors it is harder or easier than; flag any inversion such as "a +3 lemma refinement ≈ Kobon". | 6 |
| F8 | **Post-solution calibration flag.** When an accepted proof is elementary (classical tools, short proof, bounded computation), trigger a blind re-assessment for the atlas record. Do not use it to rescore the solver retroactively within the same competition. | 7 |
| F9 | **Use the event outcomes as calibration data.** Fit P(solved or partial in a week \| D, AI-relative) on this event's targets and adjust the AI-relative weights and predictors. Publish the fit with the atlas. | 8 |
| F10 | **Publish the competition D register before the event** (problem ID → D, version, hash), and show contestants the exact number that will be used. | 9 |
| F11 | **Consistent "open versus known" rule.** Define "open at freeze" operationally (e.g. listed as a conjecture by OEIS, Formal Conjectures or the source, with no located proof) and apply it identically to all targets. This decides cases like A100475 and A046969-I. | 7 |
| F12 | **Confidence-aware scoring.** Use the interval's lower endpoint, or require more assessors, when the D interval is wide; never use C0 (excerpt-only) atlas records as competition D without recalibration. | 1, 9 |

### 9.4 Indicative effect of F3 alone, for information only

| Target | Recorded D | D with H2/X1 | D with H0/X0 |
|---|---:|---:|---:|
| ERDOS21-VARIANT | 555 | 514 | 504 |
| OEIS-A100475 | 541 | 515 | 505 |
| OEIS-A060957 | 527 | 512 | 502 |
| OEIS-A000224 | 622 | 598 | 588 |
| OPDP13-QUARTIC | 644 | 606 | 596 |
| RBM4-PARITY | 727 | 691 | 682 |
| NO3-HALFTURN | 330 | 313 | 301 |
| MATRIX-3 | 724 | 666 | 657 |
| RAMSEY-K4 | 840 | 782 | 773 |

Applied to Sakana's local targets (H2/X1 for pre-existing questions, H0/X0 for event-created variations), Sakana's total would move from 1697 to about 1534 under the original rules. **No placement changes.**

---

## 10. Other process recommendations

1. **Publish the rulings (R1–R6) as rule amendments** with a short rationale for each: the field was small, bonuses and three classes were designed for a much larger event, and delivery was handled leniently. The handbook says distinctions must be announced in advance; publishing the amendments with the results keeps the record transparent.
2. **Pin and archive Sakana's last pre-cutoff commit** of `SakanaAI/autolab-100`, and compare its Lean sources with the ZIP. This is not needed for scoring under R1, but it completes provenance. Note that the PDF inside the ZIP (built 03:53 CEST) differs from the e-mailed PDF (04:34 CEST); the ZIP's own replay receipts record matching source hashes (as noted in the preliminary review), but nothing ties the sources to the on-time PDF.
3. **Finish the fresh builds** listed as incomplete in Appendix A: HTPeo DMS (four packs) and the Ramsey per-chunk kernel count (optional, since the numerator is now independently exact); Sakana A000224 and matrix-rigidity seeds 1–2; the M2 projects (Leanification, Leon/Cameron, Wilson, Jamie, Sakana M2, HTPeo M2).
4. **Second referee for Kobon.** The chair has published Kobon lower bounds himself (OEIS), so Kobon novelty decisions should be signed by a second reviewer who is independent of him (§9.2).
5. **Independence review for the overlapping M2 families:** E3 dyadic (Leon/Cameron and Wilson) and the AP conclusion (Jamie and Wilson). The Collective Frontier counts each result once.
6. **Hill design for future editions.**
   - The Collatz hill's weighted metrics were saturated by a 3-rule reference before the event.
   - The Grothendieck board is stuck at the CHSH value.
   - The BB6 hill cannot produce new mathematics within its step budgets.
   - Retarget these at open finite questions whose improvement is new mathematics, as the Ramsey, Kobon (large n) and matrix-support hills did.
7. **Public record labels (§10.2).** Distinguish "verified M1/M3A solution" (only after two reviews) from "accepted formalized partial". The values above are proposals until signed in `review/score-signoff.csv`.

---

## Appendices

### Appendix A: Fresh Lean builds

Method: the entrant's sources are copied from the archive; the recorded `lean-toolchain` is used (Lean 4.33.1 or 4.34.1 via elan); Mathlib is fetched at the recorded commit with its official cache (`lake exe cache get`, `0df444a360ea…` or `d13f23b723b8…`); the audit imports from the entrant's replay plan are built with `lake build`, and `#print axioms` is run on every listed endpoint. No entrant `.olean` file was used.

| Project | Entrant | Lean | Jobs | Result |
|---|---|---|---:|---|
| erdos21-sharp-residual | Sakana | 4.34.1 | 3113 | ✅ 5 endpoints, standard axioms |
| a100475 | Sakana | 4.33.1 | 2843 | ✅ 2 endpoints, standard axioms |
| a060957 | Sakana | 4.33.1 | 3174 | ✅ 4 endpoints, standard axioms |
| opdp13 | Sakana | 4.34.1 | 3551 | ✅ 5 endpoints, standard axioms |
| opdp89-parity-sharp | Sakana | 4.33.1 | 2184 | ✅ 3 endpoints, standard axioms |
| opdp43 | Sakana | 4.34.1 | 3095 | ✅ 2 endpoints, standard axioms |
| ferrers | Sakana | 4.33.1 | 3071 | ✅ 4 endpoints, standard axioms |
| erdos169-fourap | Sakana | 4.34.1 | 8945 | ✅ 1 endpoint, standard axioms |
| erdos944-order-bound | Sakana | 4.34.1 | 1136 | ✅ 3 endpoints, standard axioms |
| erdos1060-uniform-partial | Sakana | 4.33.1 | 1979 | ✅ 3 endpoints, standard axioms |
| erdos829-log-five-thirds | Sakana | 4.33.1 | 2337 | ✅ 2 endpoints, standard axioms |
| FOCUS-GROTH | Sakana | 4.33.1 | 2441 | ✅ 5 endpoints, standard axioms |
| FOCUS-E3 | Sakana | 4.33.1 | 1193 | ✅ 5 endpoints (`B_card` uses only `propext`, `Quot.sound`) |
| FOCUS-E3-pullback | Sakana | 4.33.1 | 1201 | ✅ 3 endpoints, standard axioms |
| FOCUS-RAMSEY (lifting) | Sakana | 4.33.1 | 1214 | ✅ 4 endpoints, standard axioms |
| MM3 support-138 | Chandragupt | 4.34.1 (core) | 9 | ✅ validity/support: no axioms; identities: `propext`, `Quot.sound` |
| RamseyCert.Limit | HTPeo | 4.33.1 | 8707 | ✅ `ramseyMultK4_le_density`, standard axioms |
| KobonCert | HTPeo | 4.33.1 | 1145 | ✅ `kobon_lower_bound`, `kobon_nonoverlapping`, standard axioms (`sol_simple` uses none) |
| a000224 | Sakana | 4.34.1 | – | ⏸ stopped for time (171 modules); not verified here |
| FOCUS-MATRIX-seed0 | Sakana | 4.33.1 | 1764 | ✅ 6 endpoints, standard axioms |
| FOCUS-MATRIX seeds 1–2 | Sakana | 4.33.1 | – | ⏸ not built here |
| RamseyCert per-chunk count (2,048 modules) | HTPeo | 4.33.1 | – | ⏸ replaced by an exact independent numerator recomputation |
| DMS packs 2–5 | HTPeo | 4.33.1 | – | ⏸ not built (about 250 modules plus a 20,180-line core file) |
| M2 projects (all entrants) | – | – | – | ⏸ not built |

Full axiom lines for every completed build are in `fresh-build-summary.txt`.

### Appendix B: Reproduction

```sh
git clone https://github.com/alejandrozu/openmath-2026-judging.git
cd openmath-2026-judging && python tools/restore_materials.py   # release packs
# score recomputation under the rulings
python3 audit-2026-10-04/scripts/final_scores.py OpenMath-Judging/review/review-data.json > final-scores.csv
# exact / exhaustive checks
python3 audit-2026-10-04/scripts/collatz_ceiling.py 12        # -> 1765 (hill format), 1822 (classical)
python3 audit-2026-10-04/scripts/collatz_ceiling.py 8 4       # -> 94, 109
python3 audit-2026-10-04/scripts/a100475_check.py
python3 audit-2026-10-04/scripts/ramsey_density.py <solution.json>              # float, seconds
python3 audit-2026-10-04/scripts/ramsey_exact_numerator.py <solution.json> <num/den>   # exact, ~2 min
python3 audit-2026-10-04/scripts/chandra_tensor_check.py <support_138/solution.json>
python3 audit-2026-10-04/scripts/no3_halfturn_bruteforce.py 8
python3 audit-2026-10-04/scripts/kobon_catalogue_check.py
python3 audit-2026-10-04/scripts/grothendieck_row3_numeric.py
python3 audit-2026-10-04/scripts/opdp_cfsd_sensitivity.py OpenMath-Judging/review/review-data.json
# fresh Lean builds (needs elan; paths at the top of each script)
python3 audit-2026-10-04/scripts/fresh_build_reproduction_sources.py <mathlib-packages-dir> erdos21-sharp-residual ...
python3 audit-2026-10-04/scripts/fresh_build_replay_plan.py FOCUS-GROTH FOCUS-E3 ...
```

### Appendix C: Files in this folder

| File | Content |
|---|---|
| `AUDIT-REPORT.md` | This report |
| `final-scores.csv` | All 70 records: class, S, A, A family, M2, scored families with D, m, p, F under the rulings |
| `fresh-build-summary.txt` | Build exit codes and the axiom-audit lines for every project built |
| `scripts/` | All verification and recomputation scripts listed in Appendix B |
