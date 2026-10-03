# Final completion receipt

Final immutable Git commit: `ac948e7001bff5428c22d236f96974856452d34d`.
`git archive` substitutes this field with the full containing commit hash;
in a Git checkout, obtain it with `git rev-parse HEAD`. The ZIP comment records
the same hash. This substitution changes release metadata only.

Mathematical input revision: `f30afd64643d785dff7ec5d44c730cb36a80dce6`.
Validated submission revision before this packaging-only release:
`b8d7362e3466d17b1dc611a7ef1bead90c878074`.
No mathematical Lean source, theorem statement, proof, certificate,
experimental result or research claim changed after those validated inputs.
The two manuals were renamed byte-for-byte; their historical names are mapped
in [PATH_MIGRATIONS.json](PATH_MIGRATIONS.json).

Validation status: the authoritative ten Lean modules and all 100 declarations
were compiled and audited with Lean 4.19.0 at the validated revision. The two
frozen draft files remain excluded. The original execution receipts remain in
[VALIDATION.md](VALIDATION.md); they are historical executions, not new runs.
This release rechecks mathematical input identity, the submission integrity
scripts, every relative Markdown link, the Git-blob seal, Git whitespace/object
integrity, clean worktree status, ZIP extraction and archived paths. It runs no
mathematical experiments. [package.py](package.py) fails release generation
unless these packaging checks pass.

Final archive filename: `openmath-final.zip`.
The complete ZIP's SHA-256 and the actual post-generation check results are
recorded in the detached `openmath-final.COMPLETION.json` beside the ZIP, with
`openmath-final.zip.sha256` for ordinary checksum tools. A ZIP cannot include
its own SHA-256: inserting the digest changes the bytes being hashed. Neither
this file nor the in-archive [COMPLETION.json](COMPLETION.json) substitutes a
payload hash for the complete archive's hash. Retain the detached receipt
together with the ZIP when submitting.

Seal status: [SHA256.json](SHA256.json) seals every canonical Git blob except
itself, including the unexpanded completion receipts. The containing commit
binds the seal. The archive checker normalizes only the two documented commit
substitutions before verifying the canonical hashes; it also checks their
expanded hashes equal the ZIP's immutable commit identity.
Archive generation disables checkout line-ending conversion for its Git
command, preserving the canonical sealed bytes on Windows as well as Unix.
Release generation requires a clean committed worktree before and after the
archive is produced; the detached receipt records the observed status.

Reproduce from the exact final Git checkout:

```sh
python submission/package.py --check
python submission/check.py --suite integrity
python submission/package.py --release
python submission/package.py --verify-zip results/openmath/openmath-final.zip
```

From an extracted ZIP, without Git history:

```sh
python submission/package.py --check-extracted
```

The [main submission](../OPENMATH_SUBMISSION.md) retains the exact formal scope,
paper/computational boundaries, trust assumptions and outstanding submission
limitations. Eligibility, authorship/team declarations, official baseline
acceptance and the external upload still require the submitter.
