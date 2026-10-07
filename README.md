# OpenMath 2026 judging archive

OpenMath competition archive for Alejandro Zarzuelo Urdiales, with separately identified personal research companions. This snapshot preserves collected contestant materials, judging explanations, OPDP analysis, source evidence, research/checking scripts and outreach history.

**Scores and mathematical assessments are preliminary proposals, not final awards or accepted solutions.** Formal closure, literature/independence review, eligibility and official receipts remain separate gates. Apply the handbook with the chair-approved October 4 amendments and the October 5 waiver recorded in the current review hub; old snapshots are retained as history.

## Current proof and manuscript additions — 7 October 2026

- [Current20 coauthored manuscripts](author-return/2026-10-07/README.md):19 standalone PDFs plus Robert’s 23-page canonical SV paper; 69 pages and27 bounded families. Author decisions and novelty gates remain separate from typesetting/proof coverage.
- [Robert’s current paper](robert-review-2026-10-07/manuscript/Robert_Huynh_concise.pdf) and [proof/source guide](robert-review-2026-10-07/README.md): the270 selected declarations retain their exact audit scope; full F/B2.2 are dependencies, not main BM or parent585.
- [Chandra’s matrix-family companion](chandra-support138-family-2026-10-07/README.md) retains its characteristic-zero identity/support bound and stated specialization holds.
- [Alejandro’s separate clean matrix9-page paper](personal-matrix-hybrid-2026-10-07/manuscript/Hybrid_Composition_revised.pdf) and [current proof guide](personal-matrix-hybrid-2026-10-07/CURRENT_GUIDE.md): 11 sources/45 standard selected declarations; scheduled counts are not global optimality or measured speed.
- [Alejandro’s separate Kobon15/88-page release](https://github.com/alejandrozu/kobon-proof/releases/tag/manuscripts-2026-10-07) remains a personal project.

- [Unchanged unsigned12-page expanded judging audit](judging-review/2026-10-07/README.md):27 considered families, preserved dated scores and blank joint-signoff fields; no Stephen Wolfram endorsement.

Actual [proof](author-return/2026-10-07/evidence/proof_CI.json), [typesetting](author-return/2026-10-07/evidence/typesetting_CI.json) and [image QA](author-return/2026-10-07/evidence/current_document_QA.json) scopes are distinct. These are author-review manuscripts, not accepted journal papers. Private claims, contact drafts and visa/planning material are excluded.

## Preserved publication and judging review — 5 October 2026

Start with the **[current publication-review hub](publication-review/README.md)**: 26 PDFs / 315 pages, including 19 proposed original-result manuscripts and four candidates with separate scope or priority holds, plus the brief, anthology and known-results companion.

The chair has authorized this public review upload and waived the remaining proof runs for it. The hub preserves the actual partial HT Ramsey 2083/2103 and A000224 167/171 scopes and their unrun final audits; this waiver does not turn missing checks into passes. DMS p=.15 and Leanification mention only are retained. Earlier snapshot documents and score tables remain historical; use the dated amended proposals and verification records in the new review package.

## Start judging

1. Read the [30-page compact review book](OpenMath-Judging/review/OpenMath-compact-review.pdf), or its [editable text](OpenMath-Judging/review/OpenMath-compact-review.txt).
2. Use the [contestant index](docs/CONTESTANTS.md) and [problem-family index](docs/PROBLEMS.md). Each links to concise profiles and contribution notes.
3. Record decisions in [score-signoff.csv](OpenMath-Judging/review/score-signoff.csv) and [contribution-signoff.csv](OpenMath-Judging/review/contribution-signoff.csv). These tables are pending approval in the snapshot.
4. For individual files and the native local judging tool, restore the large materials as described below.

## Complete local copy

Git contains the browsable documents and smaller materials. The [snapshot release](https://github.com/alejandrozu/openmath-2026-judging/releases/tag/snapshot-2026-10-03) contains deduplicated large-file packs, including the SQLite catalogue, original submission ZIPs, large file indexes, historical extracted files and the full OPDP datasets. **Downloading GitHub's source ZIP alone does not include those packs.**

```sh
git clone https://github.com/alejandrozu/openmath-2026-judging.git
cd openmath-2026-judging
python tools/restore_materials.py
python tools/verify_archive.py
python OpenMath-Judging/judging_app.py
```

Python 3 with Tkinter is required for the native app. Restoration and checksum verification use only the standard library and do not run contestant code. The full material directory is restored to its original relative layout, including indexed archive members. Normal restoration preserves changed local files, including your later judging notes; `--force` explicitly restores the archived snapshot over changed files.

## Scope

- 70 grouped contestant/contact records, 74 source identities and 80 person/account profile rows. These are not an official count of registered teams.
- 226 contribution notes and 70 problem-family profiles, with exact proposed score inputs, formalization/novelty assessments and cross-entry relationships.
- 353,195 indexed file entries, including 352,881 archive members, each with a static file summary in the catalogue. Bounded or binary summaries are identified; this is not a claim that every file is a complete proof review.
- All collected relevant email, LinkedIn, WhatsApp, event, seven-hill/alternate-board and repository evidence in the preserved source snapshots. Inaccessible or never-delivered material cannot be included.
- User-confirmed permission to publish affected private and unaccepted packets. Contributors retain ownership and their original licenses; no blanket license is imposed on submissions.

Read [STRUCTURE.md](STRUCTURE.md) for the document map, [coverage and gaps](docs/COVERAGE.md) for limitations, and [publication-manifest.json](publication-manifest.json) for every included path, original/publication hash, release placement and exclusions. Unnecessary private contact details are redacted from loose copies. Original packet archives remain intact after credential scanning. UI receipt screenshots with personal details are represented by preserved structured/text evidence rather than public screenshots. Unrelated obligations and company/personal records are excluded.

## Verified snapshot

[GitHub publication verification](docs/PUBLICATION-VERIFICATION.json) records the verified archive commit, anonymous public access, exact Git tree and all four server-side release hashes. [Full restore and native app verification](docs/RESTORE-VERIFICATION.json) records successful restoration and hashing of all 14,328 preserved paths, SQLite integrity and read-only app startup. The verification records are added after the archive commit they check.
