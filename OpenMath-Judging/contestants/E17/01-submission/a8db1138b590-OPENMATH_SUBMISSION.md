# OpenMath final submission: checked certificates and exact proof boundaries for Černý research

Prepared 2026-10-03 (Asia/Shanghai). This is a **partial contribution** to the
Černý problem, centered on existing Lean results. It does **not** solve the
general conjecture or give an improved upper bound for arbitrary synchronizing
automata. No new mathematical research was undertaken in submission preparation.

## Target and contribution

The target is the Černý conjecture: every synchronizing complete deterministic
automaton on n states has a reset word of length at most (n−1)². A reset word
maps all states to one state, with every original letter charged cost one.

The submission supplies kernel-checked potential and graph-certificate
soundness, an abstract three-anchor lower bound, exact finite C3/C4 subset
paths, a literal six-state Kari obstruction to inverse monotonicity and its
base length/phase facts, and a finite-depth reflection-hole certificate.
It includes an exhaustive declaration/axiom inventory and reproducible checks.
These results delimit proposed proof methods; the abstract hypotheses and
paper-to-automaton bridges are exposed explicitly.

The authoritative exact statements are reproduced verbatim from the actual
Lean declarations in [submission/THEOREMS.md](submission/THEOREMS.md), with
qualified names, source lines, source SHA-256 values and axiom dependencies.
[submission/theorems.json](submission/theorems.json) is the corresponding
machine-readable inventory. There are **100 theorem declarations in ten
authoritative compilation units**, including repeated helper declarations in
standalone files. This count is not a count of 100 new mathematical results.

## FORMALLY VERIFIED submission core

All types, hypotheses and definitions in the linked sources are part of the
statements. Natural-number subtraction in the sources is truncated subtraction.

| Result and exact scope | Principal checked theorems | Authoritative source |
|---|---|---|
| For arbitrary step systems, local potential inequalities telescope along every list; a zero-potential goal forces word length ≥ initial potential. The cardinality-slope lemma is conditional on its stated slope assumptions. | `Orion.potential_along_word`, `Orion.lower_bound`, `Orion.cardinality_limit` | [lean/CertificateCore.lean](lean/CertificateCore.lean) |
| Arbitrary relational walks and existential quotient-edge local transfer; inclusion-type monotone simulation; finite dyadic timing lower bounds, optimal-tail rigidity and buffer arithmetic; eventual constancy of decreasing natural sequences. The genealogy timing assumptions are explicit. | `OrionResearch.potential_lower_bound`, `OrionResearch.quotient_local`, `OrionResearch.monotone_simulation_transfer`, `OrionResearch.genealogy_clock_lower_finite`, `OrionResearch.genealogy_tail_rigidity`, `OrionResearch.buffer_two_realizable`, `OrionResearch.sharp_buffer_split`, `OrionResearch.sharp_buffer_nonsplit`, `OrionResearch.sharp_capacity_obstruction`, `OrionResearch.eventually_constant_nat` | [ResearchCore.lean](post_baseline/lean_sprint/ResearchCore.lean) |
| Symbolic two-/three-anchor rotation and merge inequalities for all valid cardinalities and bits, and the full three-anchor potential value for n≥5. | `OrionAnchors.p2_rotation`, `OrionAnchors.p2_merge`, `OrionAnchors.p3_rotation`, `OrionAnchors.p3_merge`, `OrionAnchors.p3_full_value` | [AnchorPotentials.lean](post_baseline/lean_sprint/AnchorPotentials.lean) |
| In the explicitly defined count/window graph, any walk from the full feature to a cardinality-one goal has length ≥3n−4, n≥5. This is a lower bound in that graph, not the general exact quotient formula. | `OrionThreeGraph.one_step`, `OrionThreeGraph.full_lower_bound` | [ThreeAnchorGraph.lean](post_baseline/lean_sprint/ThreeAnchorGraph.lean) |
| In the separately defined finite C3 and C4 powerset tables, the listed witnesses attain the singleton goal and every goal-reaching list is at least as long: lengths 4 and 9 respectively. Every table edge has a checked one-step concrete subset-image correspondence. | `OrionExample.one_step_fidelity`, `OrionExample.optimal_subset_path` (separate namespaces in separate compilation units) | [Cerny3Checked.lean](post_baseline/lean_sprint/Cerny3Checked.lean), [Cerny4Checked.lean](post_baseline/lean_sprint/Cerny4Checked.lean) |
| For any `LayeredCertificate` satisfying all local index, internal/entrance-potential and K/U entrance hypotheses, the five invariants hold along every path. A path ending in K or U followed by its collapse letter costs at least the requested bound. | `Orion.DirectAttack.layered_invariants`, `Orion.DirectAttack.first_collapse_cost` | [LayeredPairBarrier.lean](direct_attack/LayeredPairBarrier.lean) |
| For the literal six-state preimage-mask system, no cardinality-nondecreasing inverse word takes any singleton to the full mask. Every inverse word reaching full has ≥1 decreasing step; a specific length-25 inverse word from singleton4 reaches full with exactly one decrease. | `KariInverseShrink.literal_preimage_correct`, `KariInverseShrink.no_monotone_inverse_reset`, `KariInverseShrink.reset_needs_shrink`, `KariInverseShrink.witness_resets`, `KariInverseShrink.witness_one_shrink`, `KariInverseShrink.witness_cost` | [KariInverseShrink.lean](direct_attack/KariInverseShrink.lean) |
| In that same literal base system, every singleton-to-full inverse word has length ≥25. The last decreasing edge is 45→44 or 47→60; a sole decrease is 47→60. The stated prefix/monotone-suffix hypotheses at 45/44 force cost ≥27; phase witnesses attain costs 25/27. | `KariProductBase.reset_length_lower`, `KariProductBase.to45_length_lower`, `KariProductBase.mono44_length_lower`, `KariProductBase.last44_length_lower`, `KariProductBase.last_negative_word`, `KariProductBase.single_negative_word`, `KariProductBase.one_phase_witness`, `KariProductBase.two_phase_witness` | [KariShrinkProducts.lean](direct_attack/KariShrinkProducts.lean) |
| In the abstract integer-hole recurrence, checked layers close through eight steps; every word of length ≤8 has `SafeRun`. The specified eight-letter prefix ends with holes [0,1,3], which are unsafe. | `ReflectionCoreCut.cut_closed`, `ReflectionCoreCut.run_in_layers`, `ReflectionCoreCut.no_avoid_first_eight`, `ReflectionCoreCut.witness_prefix_holes`, `ReflectionCoreCut.witness_final_unsafe` | [ReflectionCoreCut.lean](direct_attack/ReflectionCoreCut.lean) |

Some principal signatures, exactly as in the sources (all others and their
full hypotheses are in the inventory):

```lean
theorem full_lower_bound (n : Nat) (hn : 5 ≤ n) (goal : Feature) (length : Nat)
    (walk : Walk (Edge (n-3)) ⟨n-3, true, true, true⟩ goal length)
    (terminal : cardinality goal = 1) : 3*n-4 ≤ length

theorem optimal_subset_path :
    goal (run move initial witness) ∧
    ∀ w : List Bool, goal (run move initial w) → witness.length ≤ w.length

theorem reset_needs_shrink (q : Fin 6) (word : List (Fin 2))
    (hFull : (run (singleton q) word).val = 63) :
    1 ≤ shrinkCount (singleton q) word

theorem reset_length_lower (q : Fin 6) (word : List (Fin 2))
    (hFull : run (singleton q) word = 63) : 25 ≤ word.length

theorem no_avoid_first_eight (word : List (Fin 2)) (hLength : word.length ≤ 8) :
    SafeRun [] word
```

For the Kari system, masks encode subsets of {0,…,5}, full mask is63, and
the original rows are a=[4,4,2,3,1,5], b=[1,5,3,4,2,0]. Lists are processed
in **inverse** order; the corresponding original word has reversed letters.
The kernel proves the literal one-step preimage correspondence. No generic
arbitrary-DFA composition/reset interface is claimed. Likewise the C3/C4
theorem is stated in its explicit subset-table system, with one-step fidelity.

`SafeRun` requires safety **before each processed letter**; it does not
require the final hole list to be safe. The unsafe result after the eight-letter
prefix is consistent with `no_avoid_first_eight`. Transferring it to avoidance
at a ninth concrete letter is a paper argument. The formal reflection file
does not state an arbitrary-M avoiding-word or reset theorem.

## Paper proof and computational evidence: retained context only

| Status | Retained result/context | Source and boundary |
|---|---|---|
| **Paper proof** | For contiguous anchors r≥2, n≥r+2, L=⌊log₂(r−1)⌋: B_r(n)=3n+Lr−2^(L+1)−3. Capacity-two construction, genealogy bridge, exact language thresholds and layout results. | [ALL_PARAMETER_PROOF.md](post_baseline/ALL_PARAMETER_PROOF.md), [GENEALOGY_LOWER_BOUND.md](post_baseline/GENEALOGY_LOWER_BOUND.md), [SPRINT_REPRODUCTION.md](post_baseline/SPRINT_REPRODUCTION.md). B_r is an existential feature-quotient distance; representatives may change between edges. The general formula, concrete quotient bridge and attaining construction are not fully formalized. |
| **Paper proof** | Concrete all-p layered Figure3-family instantiation and specified-state threshold; Kari Cartesian products (n=6^d) and shrink/cost tradeoffs; reflection-family avoidance/support metrics and linear reset 5n−11. | [COMPRESS_OTHER_EXACT_LOWER.md](direct_attack/COMPRESS_OTHER_EXACT_LOWER.md), [KARI_PRODUCT_SHRINK_TRADEOFF.md](direct_attack/KARI_PRODUCT_SHRINK_TRADEOFF.md), [REFLECTION_CORE_TRADEOFF.md](direct_attack/REFLECTION_CORE_TRADEOFF.md). Only their exact abstract/base components above are formal. |
| **Paper proof** | Explicit fixed-root, defect-balancing and moving-root subclass square/strict-square criteria, including arbitrary high-order core permutations and short original root returns. | [RESULTS.md](direct_attack/RESULTS.md), [MOVING_ROOT_ALL_HIGH_ORDER.md](direct_attack/MOVING_ROOT_ALL_HIGH_ORDER.md), [SHORT_ROOT_RETURN_SQUARE.md](direct_attack/SHORT_ROOT_RETURN_SQUARE.md), [PROOF_AUDIT.md](direct_attack/PROOF_AUDIT.md). Their hypotheses do not cover all synchronizing automata; none is a Lean all-n reset theorem. |
| **Computational evidence** | Exact finite subset/Bellman certificates, baseline C2…C10 calculations, 83 baseline certificates, exhaustive small automata scopes, corruption rejection controls and deterministic replays. | `reference_results/`, `post_baseline/`, `direct_attack/data/`; final run receipts in `submission/`. Acceptance by Python/C++ is not Lean verification, even when output says VERIFIED. A local certificate family valid for infinitely many parameters still has a computational checker trust boundary unless its universal soundness is formalized. |
| **Exploratory / conjectured / open** | Saved pressure runs without independently audited coverage; general-layout formulas, remaining order-two/mixed-core targets, and the unrestricted conjecture. | Existing notes in `direct_attack/data/` and `RESULTS.md`. No new search, coverage extrapolation, or promotion to a universal theorem is made here. |

“Paper proof” means the repository contains an argument with the stated scope.
This preparation did not independently certify every paper's all-parameter
steps. Finite controls and successful reproduction do not replace that missing
formalization or an independent mathematical review.

The two frozen files `lean/Cerny3.lean` and `lean/Cerny4.lean` are **excluded
noncompiling baseline drafts**. Their finite existential decidability instance
fails elaboration and error recovery inserts `sorryAx`. This is not a successful
proof with an accepted hole. The checked copies prove the same mathematical
statements. All twelve tracked Lean sources were scanned; none contains a
code-level `sorry`, `admit`, custom `axiom`, `native_decide`, foreign proof
implementation, `unsafe`, `partial` or `opaque` declaration. Every theorem in
the ten selected units was compiled and had its axioms printed individually.

## Prior work and novelty

The classical Černý-family threshold, the Kari six-state automaton, powerset
search/BFS, potential telescoping, standard extension methods and binary-tree
optimization are prior work or standard arguments. We claim neither a new
critical automaton nor a newly discovered threshold25. The bounded existing
literature notes are [NOVELTY_AUDIT.md](post_baseline/NOVELTY_AUDIT.md) and
[LITERATURE_AND_BOTTLENECKS.md](direct_attack/LITERATURE_AND_BOTTLENECKS.md);
the baseline bibliography is [REFERENCES.md](docs/REFERENCES.md).

The contribution is these particular formal artifacts, explicit hypotheses,
method boundaries and reproducible evidence, relative to the imported kit.
Priority of the exact auxiliary statements is **not established**. Existing
negative literature-search evidence does not establish originality. No new
literature search or current rule/handbook verification was conducted for this
preparation request. Archived citations are inherited provenance, not newly
verified references.

## Repository baseline versus final contribution

| Layer | Immutable revision | Existing content versus final preparation |
|---|---|---|
| Imported AI-assisted kit | `b36adeac34a5088a7e2cd588f8c55221d04bd6eb` (`baseline/imported`) | 125 manifest entries, baseline Python code/certificates, paper two-anchor proof and uncompiled Lean drafts. These are pre-existing imported content, not discoveries of this preparation. |
| Completed anchor sprint / baseline of direct attack | `168ffff8f8c0de968ecde3fd7fcea4bea6e364b6` | General anchor paper results and five checked sprint modules already existed before the direct-attack branch. |
| Research snapshot entering this audit | `f30afd64643d785dff7ec5d44c730cb36a80dce6` | Existing direct-attack results and four direct Lean sources. This is the mathematical input snapshot. |
| Final submission preparation | The Git commit containing this document and its sealed inventory | Proof-status audit, exact statement inventory, selected formal core, compiler portability and Windows-launcher fixes, existing exporter repair, isolated reproduction harness and fresh check receipts. No theorem was weakened, and no new all-n proof was attempted. |

The input ZIP hash recorded in the existing ledger is
`62ccf3da5babdc02731be54a7a88444b0af7235b4fe76357930b4bc754742107`.
The external ZIP was not reread in this audit; the imported Git snapshot and
manifest were checked. A repository freeze does not by itself prove the
competition's official cutoff, eligibility or novelty baseline. The submitter
must use the event's actual baseline when making competition-window claims.

## Toolchain, dependencies and trust boundary

* Lean `leanprover/lean4:v4.19.0`, upstream compiler commit `6caaee842e94`.
  Checked locally on Windows x86_64 using the installed compiler directly.
  Executable SHA-256 and exact version output are in `submission/theorems.json`.
* Only bundled Lean `Std` and two local sprint imports are required. No Mathlib,
  downloaded package, SMT solver or native evaluation is required by the formal
  core. There is no Lake project; `lake build` is not the build command.
  Standalone files reuse names and must be compiled separately, as the harness
  does. Local imports use freshly compiled `.olean` files via `LEAN_PATH`.
* Proofs use kernel-evaluated `decide`, induction and ordinary tactics including
  `omega`. Printed dependencies are subsets of `propext`, `Classical.choice`
  and `Quot.sound`; no additional axiom is accepted. The Lean implementation,
  its standard library/toolchain and these standard axioms form the formal
  trust boundary. Binary hashes record the checked executable, not a separate
  verification of the compiler implementation.
* Python checks use the standard library, tested here with CPython 3.12.14.
  Full harness/replay requires Python≥3.10, Git and a C++11 g++ toolchain.
  Exact native compiler version/build invocations are in the native receipt.
  The optional historical Z3 experiments are unnecessary and were not rerun.
* Python/C++ algorithms, finite coverage assertions, manuscript arguments and
  parameter-transfer reasoning remain outside the Lean kernel. Hashes establish
  identity, not mathematical correctness. The manuscript source passes static
  consistency checks; its PDF compilation is still unverified and is not
  required to read this Markdown submission.

## Exact reproduction commands

Run from the repository root with an already installed Lean4.19.0 and g++.
The harness does not install dependencies or initiate new-result searches.
Use the versioned Lean executable via `--lean` to avoid elan update wrappers.
For ordinary
installations with those executables on PATH:

```sh
python submission/check.py --suite formal
python submission/check.py --suite baseline
python submission/check.py --suite post
python submission/check.py --suite native
python submission/check.py --suite direct
python submission/check.py --suite integrity
python submission/seal.py
git diff --check
git fsck --full
git status --porcelain=v1
git rev-parse HEAD
git rev-parse HEAD^{tree}
```

The exact locally tested compiler/runtime selection was:

```powershell
$PythonExe = 'C:/Users/29848/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
$LeanExe = 'C:/Users/29848/.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean.exe'
$CxxExe = 'E:/tool/programming/Dev-Cpp/MinGW64/bin/g++.exe'
& $PythonExe submission/check.py --suite formal --lean $LeanExe
& $PythonExe submission/check.py --suite baseline --lean $LeanExe
& $PythonExe submission/check.py --suite post
& $PythonExe submission/check.py --suite native --cxx $CxxExe
& $PythonExe submission/check.py --suite direct --lean $LeanExe --cxx $CxxExe
& $PythonExe submission/check.py --suite integrity
& $PythonExe submission/seal.py
& './post_baseline/lean_sprint/check.ps1' -LeanExe $LeanExe
$env:ORION_PYTHON = $PythonExe
cmd /c start_windows.bat --no-pause
```

`--suite all` combines the suites; separate runs provide clearer receipts.
Outputs go to ignored `results/openmath/`. The direct suite copies the current
source/data package to a fresh ignored directory and runs the existing
146-check `python -m direct_attack.reproduce` **without `--full`**. It replays
existing deterministic streams and checks certificates, preserving original
captures. It does not run the 227-command full-generation registry or fresh
exploratory searches. Original historical generators remain available as
provenance, outside the final submission checks.

The formal suite prints every theorem/axiom and records the two expected
archival compilation failures as exclusions; any failure in an authoritative
unit fails the suite. The baseline suite also compiles repaired exporter output
for C2…C5. Those generated files are reproduction tests, not additional priority
claims. The native suite builds all eight root C++ tools without initiating
new exploratory experiments. The integrity suite checks Git, the original
baseline manifest, the historical direct manifest with documented preparation
overrides, and the canonical final-package seal.

## Check receipts and immutable identity

[submission/VALIDATION.md](submission/VALIDATION.md) records the final outcomes;
`submission/validation_*.json` preserve literal commands, outputs and exit
codes. Historical captures are not relabelled as new runs. No mathematical
Lean source was changed during preparation.

The later packaging-only release uses the validated submission revision
`b8d7362e3466d17b1dc611a7ef1bead90c878074` as authoritative. Its
[final completion receipt](submission/COMPLETION.md) is included in the archive,
with a [machine-readable counterpart](submission/COMPLETION.json).
[STATUS.json](STATUS.json) clearly separates FINAL validation from the original
preparation environment. No mathematical source, theorem, proof, certificate,
experimental result or research claim changed in this release. The original
manuals were renamed byte-for-byte to ASCII paths:
[PDF](docs/ORION_RESEARCH_MANUAL.pdf) and [DOCX](docs/ORION_RESEARCH_MANUAL.docx).
[PATH_MIGRATIONS.json](submission/PATH_MIGRATIONS.json) maps names in preserved
historical manifests and literal execution receipts to their current paths.

`submission/SHA256.json` seals **canonical Git blob bytes** for every staged
package file except itself. This avoids platform-dependent checkout CRLF/LF
conversion. The manifest is bound by its containing Git commit. Source hashes
in the formal receipt describe the actual bytes compiled on this machine;
rerunning on another platform may change those byte hashes or timings while
checking the same canonical Git contents. The original ZIP manifest remains
unchanged; five CSVs require explicitly reported CRLF reconstruction from their
normalized baseline Git blobs. Root entry-point annotations, the Windows
launcher and the exporter repair are explicit baseline worktree overrides,
not changes to the freeze.
Eleven historical direct-attack files have mixed newline serialization that
Git normalized. [submission/HISTORICAL_EOL.json](submission/HISTORICAL_EOL.json)
preserves exact line-ending recipes from the retained original bytes, with both
canonical-LF and raw SHA-256 values. The integrity checker reconstructs the
historical bytes from the frozen Git blobs and requires an exact hash match;
it never substitutes a new hash for the historical manifest.

A commit cannot contain its own hash. The final submission identifier is the
full `git rev-parse HEAD` from the commit containing this document. Git's
`export-subst` expands the commit field in the two completion receipts when
creating the ZIP; its comment records the same immutable hash. In a Git
checkout, read the containing hash with `git rev-parse HEAD`. The archive
checker verifies the expanded identity and normalizes only those two metadata
fields when checking the canonical seal. Record that hash when uploading and
submit that exact revision. To check and produce the final portable archive
from a clean committed checkout:

```sh
python submission/package.py --check
python submission/package.py --release
python submission/package.py --verify-zip results/openmath/openmath-final.zip
```

The release script runs only packaging/integrity checks and verifies extraction,
all archived canonical hashes, file references and relative Markdown links.
Its archive command disables Git checkout line-ending conversion so the ZIP
preserves canonical sealed bytes across Windows and Unix configurations.
It compares all twelve Lean sources with the mathematical input revision;
unchanged validated sources do not require another formal build. The original
formal execution receipts remain authoritative. The script creates
`results/openmath/openmath-final.zip`, `openmath-final.COMPLETION.json` and
`openmath-final.zip.sha256`. The detached JSON records the full ZIP SHA-256,
final commit and observed clean/seal status. The ZIP cannot include its own
SHA-256 without changing the hashed bytes. Retain the detached receipt beside
the ZIP; no payload-only digest is mislabelled as the complete ZIP checksum.
Archive bytes are not claimed reproducible across Git/platform versions.
Without Git history, run `python submission/package.py --check-extracted` in
the extracted directory to check the seal and all links/paths.
The ZIP does not contain Git history. Full integrity reproduction requires the
repository at the exact commit (including `baseline/imported`); a Git bundle
of the final branch and baseline provides an offline copy of that history:

```sh
git bundle create ../openmath-final.bundle research/cerny-direct-attack baseline/imported
git bundle verify ../openmath-final.bundle
git clone ../openmath-final.bundle openmath-reproduction
```

Check out the [completion receipt's](submission/COMPLETION.md) final hash in the cloned repository before
running the commands above. No remote repository URL is configured in this
checkout, so an offline bundle is the portable full-reproduction artifact.

## AI and tool-use disclosure

The imported kit and subsequent research were AI-assisted, as recorded in
`STATUS.json`, `POST_BASELINE_RESEARCH_LEDGER.md` and the existing continuation
notes. These records are retained; the package is not presented as unaided
human work. They do not provide a complete independently certified log of
every historical model/version or human contribution, and none is invented.

For this preparation, OpenAI Codex performed source/document audit, proof-status
classification, packaging edits, compiler-path/exporter repairs and automated
validation through PowerShell, Git, Python, Lean4.19.0 and g++. No external
research retrieval, SMT discovery run or new formalization was used; repository
checks invoked no paid external APIs. Initial elan-shim version checks attempted
self-update and failed; final verification used the already installed versioned
compiler directly, with no dependency download or toolchain installation.
Lean validates the submitted formal terms; it does not certify originality,
authorship or the paper-only results. The human submitter is responsible for
their authorship/team declaration and competition disclosures.

## Remaining submission limitations

The general conjecture, full paper-to-DFA bridges and all-n product/subclass
formalizations remain open or unformalized as specified above. This package is
ready only as a partial, explicitly scoped formal contribution. It cannot be
submitted honestly as a complete solution. Priority, official competition
baseline/eligibility and required submitter metadata are not established by
this repository audit; event acceptance and upload have not been performed.
The paper manuscript's PDF compilation remains unverified. These limitations
do not invalidate the ten explicitly checked Lean compilation units.
