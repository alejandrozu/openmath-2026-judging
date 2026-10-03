# Final validation receipt

Date: 2026-10-03, Asia/Shanghai. Mathematical input revision:
`f30afd64643d785dff7ec5d44c730cb36a80dce6`. This preparation changed no
mathematical Lean source. All results below describe actual executions;
the JSON/log receipts retain literal commands, exit codes and output.

These are the validated mathematical/preparation executions. The later
packaging-only release preserves their inputs and outcomes. Its
[final completion receipt](COMPLETION.md) and detached transport receipt record
the final commit, archive hash and packaging checks; historical receipts below
are not rewritten as fresh executions.

| Check | Outcome | Receipt |
|---|---|---|
| Ten authoritative Lean modules; print/check all 100 theorem declarations and their axioms | PASS. Lean4.19.0; only subsets of propext, Classical.choice, Quot.sound. No sorryAx in any accepted module. | [validation_formal.json](validation_formal.json), [theorems.json](theorems.json), [THEOREMS.md](THEOREMS.md) |
| All twelve tracked Lean sources scanned for holes, custom axioms, native/foreign proof implementations and unclassified imports | PASS. Ten selected; two frozen drafts explicitly excluded. | [validation_formal.json](validation_formal.json) |
| Frozen `lean/Cerny3.lean`, `lean/Cerny4.lean` compilation | EXPECTED FAILURE. Finite goal decidability fails and compiler recovery prints sorryAx. Neither contributes a submitted theorem. Checked copies compile with unchanged mathematical statements. | [validation_formal.json](validation_formal.json), archival records in [theorems.json](theorems.json) |
| Existing PowerShell sprint build | PASS, all five modules. | [validation_sprint_build.log](validation_sprint_build.log) |
| Baseline unittest suite | PASS,14 methods; includes all729 labelled three-state binary automata,128 seeded random controls and corrupt-certificate rejection. | [validation_baseline.json](validation_baseline.json) |
| Every bundled baseline certificate | PASS,83/83:55 exact,11 bounds,17 nonsynchronizing. These are Python checks. | [validation_baseline.json](validation_baseline.json) |
| Baseline demo, C8 feature comparison/landmarks and60 single-transition C6 mutations | PASS, reconstructed into ignored output. | [validation_baseline.json](validation_baseline.json) |
| Repaired Lean exporter | PASS, generated C2/C3/C4/C5 files compile with no sorryAx. This reuses the already checked finite-goal proof repair. | [validation_baseline.json](validation_baseline.json) |
| Ten post-baseline checks, including uniform construction, layouts, normal form, languages, counts, affine certificates and manuscript source consistency | PASS. Affine checker covers r2…17 and10,343,428 local representatives; still a Python/certificate trust boundary. | [validation_post.json](validation_post.json) |
| Eight root C++ native tools | PASS, all built with g++4.9.2, C++11. No new pressure experiments were initiated. | [validation_native.json](validation_native.json) |
| Windows launcher with explicit installed Python and `--no-pause` | PASS, exit0; demo/compare and14 tests complete. | [validation_windows_launcher.json](validation_windows_launcher.json), [validation_windows_launcher.log](validation_windows_launcher.log) |
| Existing direct-attack default audit | PASS,146/146 registered checks, including certificate rejection controls, finite coverage checks, deterministic old-stream replays and four Lean checker controls. No --full generation or new exploration. Original scientific inputs preserved. | [validation_direct.json](validation_direct.json) |
| Python syntax compilation of preparation scripts, runtime helper and exporter | PASS, `python -m compileall -q submission direct_attack/submission_runtime.py src/lean_export.py`, exit0. | Recorded command; executable checks above also exercise the scripts. |
| Git whitespace/object integrity,125-entry imported baseline identity, historical direct manifest and43 cited qualified theorem names | PASS. Expected preparation overrides, five CSV CRLF reconstructions and eleven mixed-newline recipes are reported explicitly. | [validation_integrity_preseal.json](validation_integrity_preseal.json), [HISTORICAL_EOL.json](HISTORICAL_EOL.json) |
| Final canonical Git-blob seal and clean committed worktree | Checked after packaging with `python submission/seal.py`, `git diff --check`, `git fsck --full`, and `git status --porcelain=v1`. The containing commit binds the final seal; the completion receipt identifies the release. | [SHA256.json](SHA256.json), [final completion receipt](COMPLETION.md) |

The direct receipt includes exact scratch input hashes, not a fabricated final
commit hash. The audit ran against an isolated copy of the research files plus
the compiler-path repairs; later entry-point and proof-status documentation
edits do not alter those mathematical inputs. Timings and native executable
hashes are platform-specific and are not theorem claims.

The final seal uses canonical Git-index blob contents so a fresh checkout can
verify it regardless of CRLF/LF conversion. It excludes only the seal file
itself, which the final Git commit identifies. Historical manifests are
preserved as historical evidence rather than overwritten to conceal changes.

The paper manuscript's PDF compilation remains UNVERIFIED; static brace,
environment, citation and cross-reference checks passed. No new paper proof,
priority audit, competition-rule verification or external upload was performed.
The general Černý conjecture is still OPEN. The package is scoped to the
formal partial contribution described in the submission document.
