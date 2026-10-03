# OpenMath 2026 judging archive

Competition-only archive for Alejandro Zarzuelo Urdiales. This snapshot preserves collected contestant materials, judging explanations, OPDP analysis, source evidence, research/checking scripts and outreach history.

**Scores and mathematical assessments are preliminary proposals, not final awards or accepted solutions.** Formal closure, literature/independence review, eligibility and official receipts remain separate gates. The handbook is authoritative; old snapshots are retained as history.

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
