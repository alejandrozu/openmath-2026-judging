"""Write navigation, hydration and verification tools for the publication snapshot."""
from pathlib import Path
import json, hashlib, datetime
ROOT=Path(__file__).resolve().parent; DEST=ROOT/'OpenMath-GitHub-Archive'
REPO='alejandrozu/openmath-2026-judging'; TAG='snapshot-2026-10-03'
manifest=json.loads((DEST/'publication-manifest.json').read_text(encoding='utf8'))
data=json.loads((DEST/'OpenMath-Judging/review/review-data.json').read_text(encoding='utf8'))
manifest['repository']=REPO;manifest['release_tag']=TAG
(DEST/'publication-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf8')

launcher=DEST/'OpenMath-Judging/Open OpenMath Judging.cmd'
launcher.write_text('@echo off\ncd /d "%~dp0"\npy -3 judging_app.py\nif errorlevel 9009 python judging_app.py\n',encoding='utf8')
for e in manifest['files']:
    if e['path']=='OpenMath-Judging/Open OpenMath Judging.cmd':
        b=launcher.read_bytes();e.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),redacted=True)
(DEST/'publication-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf8')

(DEST/'README.md').write_text('''# OpenMath 2026 judging archive

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
''',encoding='utf8')

(DEST/'STRUCTURE.md').write_text('''# Structure of the OpenMath archive

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
''',encoding='utf8')

docs=DEST/'docs';docs.mkdir(exist_ok=True)
rows=['# Contestant and contact-record index','', 'All numerical values below are proposed and contingent on acceptance. IDs are stable grouped records, not official registrations.','', '| ID | Name / profile | Contribution notes | Proposed S | Proposed A | M2 |','|---|---|---|---:|---:|---:|']
for t in data['teams']:
    links=' '.join(f'[{r}](../OpenMath-Judging/review/entries/{r}.txt)' for r in t['result_ids']) or 'No contribution packet'
    rows.append(f"| {t['id']} | [{t['name'].replace('|','/')}](../OpenMath-Judging/review/people/{t['id']}.txt) | {links} | {t['adjusted_S']} | {t['adjusted_A']} | {t['M2_proposed_integer_count']} |")
rows+=['','Leanification: five-person exception approved by the chair; raw formalization count and adjusted 0.8 value remain separate. No organizer acknowledgement is invented.']
(docs/'CONTESTANTS.md').write_text('\n'.join(rows),encoding='utf8')
rows=['# Problem-family index','','Each profile collects all related contributions, exact proposed difficulty and progress inputs, novelty/formalization notes, overlap and scientific synthesis. Local OPDP extensions are provisional until independent assessment.','']
for p in sorted((DEST/'OpenMath-Judging/review/problems').glob('*.txt')):
    title=p.read_text(encoding='utf8').splitlines()[0]
    rows.append(f'- [{title}](../OpenMath-Judging/review/problems/{p.name})')
(docs/'PROBLEMS.md').write_text('\n'.join(rows),encoding='utf8')
limitations=data['limitations']
(docs/'COVERAGE.md').write_text('''# Coverage and source gaps

This is a complete publication snapshot of the selected, collected OpenMath material, not a guarantee that every entrant delivered a packet or that private/unexposed hill artifacts were accessible.

The current catalogue has 70 grouped records and 353,195 file indexes/summaries. There are 226 contribution notes, 70 problem profiles and 80 individual/account profile views. Official registration, receipt, mathematical acceptance and score approval remain distinct.

Known unresolved source gaps include Qichao's actual 27 MB source ZIP, Luke/Madhan's complete graph/proof packet, Matt's failed inline-image download and unexposed/private hill artifacts. Signal history was not accessible and no competition packet there was verified. The complete pinned Chandragupt repository is now included; old statements that it was missing are historical.

## Current review limitations

'''+ '\n'.join('- '+str(v) for v in (limitations if isinstance(limitations,list) else [limitations]))+'''

## Publication transformations

The user confirmed author permissions for private/unaccepted packets. Loose correspondence and metadata have unnecessary contact details, credentials and workstation paths removed. Mathematical originals, packet ZIPs and scholarly attribution/license notices are preserved. No contestant code was executed during archiving. Runtime caches, an incomplete first-build catalogue and personal-detail UI screenshots are not published; corresponding text/structured receipts remain. Mixed obligation synchronizers and unrelated personal/company records are outside this competition archive.

Every selected path, original/publication hash, storage placement and exact excluded path/reason is recorded in `publication-manifest.json`. Hash changes caused by privacy transformations are explicit. The archived SQLite copy updates redacted loose-file hashes while retaining stable file IDs and original archive-member hashes. The original local workspace remains intact.

Scores are contingent proposals. A successful archive hash check is not a theorem-proof check. No final awards, submissions or official organizer acknowledgements are created here.
''',encoding='utf8')
tools=DEST/'tools';tools.mkdir(exist_ok=True)
(tools/'restore_materials.py').write_text('''"""Restore verified release-backed files; never execute contestant programs."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, urllib.request, zipfile, shutil, tempfile
ROOT=Path(__file__).resolve().parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def main():
    a=argparse.ArgumentParser();a.add_argument('--force',action='store_true');args=a.parse_args()
    m=json.loads((ROOT/'publication-manifest.json').read_text(encoding='utf8'))
    cache=ROOT/'.material-cache';cache.mkdir(exist_ok=True)
    for asset in m['assets']:
        pack=cache/asset['name']
        if not pack.exists() or sha(pack)!=asset['sha256']:
            url=f"https://github.com/{m['repository']}/releases/download/{m['release_tag']}/{asset['name']}"
            print('Downloading',asset['name'],flush=True)
            tmp=pack.with_suffix('.partial')
            with urllib.request.urlopen(url) as source,tmp.open('wb') as out:shutil.copyfileobj(source,out)
            if tmp.stat().st_size!=asset['bytes'] or sha(tmp)!=asset['sha256']:raise RuntimeError('Release integrity failure: '+asset['name'])
            tmp.replace(pack)
        with zipfile.ZipFile(pack) as z:
            for entry in m['files']:
                if entry.get('asset')!=asset['name']:continue
                rel=PurePosixPath(entry['path'])
                if rel.is_absolute() or '..' in rel.parts or ':' in str(rel):raise ValueError('Unsafe manifest path')
                target=ROOT.joinpath(*rel.parts)
                if not target.resolve().is_relative_to(ROOT.resolve()):raise ValueError('Unsafe target')
                if target.exists():
                    if sha(target)==entry['sha256']:continue
                    if not args.force:raise RuntimeError('Changed local file preserved: '+str(target)+'; use --force only to restore the archived snapshot')
                target.parent.mkdir(parents=True,exist_ok=True)
                tmp=target.with_name(target.name+'.restore-partial');h=hashlib.sha256();size=0
                with z.open(entry['object']) as source,tmp.open('wb') as out:
                    for block in iter(lambda:source.read(1024*1024),b''):out.write(block);h.update(block);size+=len(block)
                if size!=entry['bytes'] or h.hexdigest()!=entry['sha256']:raise RuntimeError('Object integrity failure: '+entry['path'])
                tmp.replace(target)
    print('All release-backed materials restored. Run python tools/verify_archive.py.')
if __name__=='__main__':main()
''',encoding='utf8')
(tools/'verify_archive.py').write_text('''"""Verify the publication snapshot; mathematical acceptance is a separate process."""
from pathlib import Path
import hashlib, json, sqlite3, sys
ROOT=Path(__file__).resolve().parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def main():
    m=json.loads((ROOT/'publication-manifest.json').read_text(encoding='utf8'));errors=[]
    for e in m['files']:
        p=ROOT/e['path']
        if not p.is_file():errors.append('Missing '+e['path'])
        elif p.stat().st_size!=e['bytes'] or sha(p)!=e['sha256']:errors.append('Changed '+e['path'])
    d=ROOT/'OpenMath-Judging/catalogue.sqlite'
    if d.exists():
        c=sqlite3.connect('file:'+d.as_posix()+'?mode=ro',uri=True)
        if c.execute('pragma integrity_check').fetchone()[0]!='ok':errors.append('SQLite integrity failure')
        for table,key in [('files','file_entries'),('file_reviews','file_summaries')]:
            if c.execute('select count(*) from '+table).fetchone()[0]!=m['counts'][key]:errors.append('Unexpected '+table+' count')
        c.close()
    review=json.loads((ROOT/'OpenMath-Judging/review/review-data.json').read_text(encoding='utf8'))
    for k,n in [('teams',70),('people',80),('results',226),('problems',70)]:
        if len(review[k])!=n:errors.append('Unexpected review '+k+' count')
    if errors:
        print('\u005cn'.join(errors));return 1
    print(f"Verified {len(m['files'])} publication paths, all byte hashes and review/catalogue counts. Scores remain preliminary.");return 0
if __name__=='__main__':sys.exit(main())
''',encoding='utf8')
(DEST/'.gitignore').write_text('.material-cache/\n__pycache__/\n*.pyc\n*.restore-partial\n',encoding='utf8')
(DEST/'RIGHTS.md').write_text('''# Attribution and permissions

The user expressly confirmed permission to publish all affected private and unaccepted OpenMath packets on October 3, 2026. Competition handbook sections 8.4, 9.2 and 10 govern publication authority, confidentiality and attribution. This archive does not transfer ownership or override original third-party licenses.

Each contestant's authors, baseline sources, credits, licenses and original notices are retained within their packet and catalogue. Joint entrants' points are not split into invented individual allocations. AI providers and organizers receive no automatic scholarly authorship. No blanket license is applied to third-party submissions or the combined archive.

The public review record is visibly preliminary. Publication of a candidate does not imply accepted mathematical correctness, verified novelty, official receipt or an award. Unnecessary private contacts and credentials are removed from loose publication copies, with original hashes recorded for provenance.
''',encoding='utf8')
print('Navigation and restore/verification tools written.')
