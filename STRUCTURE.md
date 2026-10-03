# Structure of the OpenMath archive

## Current judging documents

| Location | Contents and use |
|---|---|
| `OpenMath-Judging/review/OpenMath-compact-review.pdf` | Current short review book, 30 pages; start here. |
| `OpenMath-Judging/review/OpenMath-compact-review.txt` | Editable equivalent of the short review book. |
| `OpenMath-Judging/review/people/` | Group profiles plus individual/account views of joint work; no invented division of joint points. |
| `OpenMath-Judging/review/entries/` | One note per contribution: exact claim, assessment, novelty, formalization, score inputs, residual obstacles and file references. |
| `OpenMath-Judging/review/problems/` | One profile per problem/family, collecting all related entrants' results and opportunities for a joint scientific paper. |
| `OpenMath-Judging/review/review-data.json` | Machine-readable current teams, people, results, families, synergies, proposed scores and limitations. |
| `OpenMath-Judging/review/OPDP-local-append.json` | Existing published difficulty values and complete local analyses for additional targets. New local values still need the handbook's independent assessments/median. |
| `OpenMath-Judging/review/score-signoff.csv` | Chair approval of each entrant's proposed totals. |
| `OpenMath-Judging/review/contribution-signoff.csv` | Chair approval of each claim's scope and score. |
| `OpenMath-Judging/review/review-validation.json` | Formula, family deduplication, M2 exception and coverage consistency checks; not mathematical acceptance. |
| `OpenMath-Judging/review/file-summary-coverage.json` | Counts and limits of per-file static summaries. |
| `OpenMath-Judging/review/source-index.json` | Latest source index; extends the earlier collection index with the complete pinned matrix packet. |
| `OpenMath-Judging/review/chandra-*` | Exact tensor/family checks, original-source manifests and source readings. Distinguish independently checked identities from still-unproved structural claims. |

## Classified contestant material

`OpenMath-Judging/contestants/<entry-ID>/` retains identity/status, missing-material notes, file indexes and loose artifacts. Original ZIPs are indexed without flattening or executing their contents. `EVENT` is shared event material, not a contestant. The [contestant index](docs/CONTESTANTS.md) maps IDs to names.

| Folder | Meaning |
|---|---|
| `01-submission` | Submission statements, exact claims, completion manifests. |
| `02-papers` | Papers, explanatory documents and the official handbook. |
| `03-novelty` | Novelty, motivation, prior-work and bibliography material. |
| `04-formal-proofs` | Lean and other formal proof sources. |
| `05-certificates` | Constructions, witnesses and proof certificates. |
| `06-data` | Result datasets and numerical outputs. |
| `07-reproduction` | Checking/reproduction code and instructions. |
| `08-logs` | Runs, experiment and exploration logs. |
| `09-team` | Authorship, credits, licenses and provenance. |
| `10-build` | Dependencies, toolchains and build configuration. |
| `11-other` | Other support files. |
| `12-correspondence` | Relevant source messages and receipts, with unnecessary contacts removed. |
| `13-archives` | Original pinned packet and nested archives. |

Each `FILE-INDEX.csv` maps original paths/archive members to stable catalogue IDs. The classification is an editable filename/path inference, not a mathematical judgment.

## Catalogue and native tool

`OpenMath-Judging/catalogue.sqlite` holds teams, every indexed loose/archive file, per-file reviews and the archived review-note state. Restore it from release packs before running `judging_app.py`. `library_core.py` reads and materializes files; it does not execute entrant programs. The launcher is portable. The app presents person, problem, score and file views and saves your later notes locally.

## Rules, OPDP and earlier review history

`OpenMath-Judging/contestants/EVENT/02-papers/competition_handbook_final.pdf` is the competition handbook. `OpenMath-Judging/judging/` preserves the complete OPDP datasets/methodology, earlier preliminary assessment, source readings, static formal-source audit and independent certificate checks. **Use `review/` for current proposals; earlier symbolic values and old missing-source notes are historical.** `OpenMath-Judging/source-index.json`, preservation checks and archive provenance document the collection history.

## Research and communications history

`outputs/OpenMath-*` preserves successive audits, team directories, all hill/leaderboard/project snapshots, email/LinkedIn/WhatsApp source readbacks, repository trees/commit pins, submission fetch maps, approved outreach drafts and sent receipts. Filename `UNSENT` is preserved as historical draft status; inspect later `SENT` receipts for verified actions. No message is sent by this repository.

`outputs/OpenMath-morning-artifacts/`, `outputs/OpenMath-late-morning-artifacts/`, `outputs/OpenMath-library-full-archives/` and `outputs/sakana/` retain earlier extracted and verification copies. Repetition is intentional historical provenance; release packs deduplicate identical bytes. `outputs/Jamie-*` and `outputs/Chandragupt-*` preserve specific blocker/private-source evidence. Source/audit timestamps determine chronology; names such as `current` describe the snapshot when created.

Research/checking/build scripts from the workspace remain at their original relative paths. They are historical tools, some with capture-specific inputs or dependencies, and are not an instruction to rerun every script. **Only the restore and verify commands are needed to browse the archive.** Reproduction commands inside contestant material require separate review before execution.

## Publication and verification

`publication-manifest.json` is the exhaustive path-level manifest. Every release-backed path names a pack, content-addressed object, byte length and SHA256. Original hashes are recorded separately when a privacy transformation changed a loose copy. `tools/restore_materials.py` hydrates the exact directory layout; `tools/verify_archive.py` verifies all restored bytes and current review counts. `docs/COVERAGE.md` records omissions and genuine source gaps. The release assets are a required part of the repository archive, not optional supplementary data.

Third-party materials retain their notices and licenses. No blanket license grants rights to work beyond the original contributors' permission. Public sharing does not make a proposed score official or a candidate proof accepted.
