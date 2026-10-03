# Lean 4 certificate for the 3x3 schemes

This directory holds a machine-checked certificate, in Lean 4 with no external libraries, that four rank-23 schemes for 3x3 matrix multiplication in this repository satisfy all 729 Brent identities, together with their support counts. It was built and checked on 2026-10-02 with the toolchain pinned in `lean-toolchain`.

## What was proven

For each of the four files

| JSON file | Lean data module | Scale factors (u, v, w) | Theorems |
|---|---|---|---|
| `solutions/support_138/solution.json` | `MM3/Scheme138.lean` | 8, 4, 16 | `scheme138_valid`, `scheme138_identities`, `scheme138_support` |
| `solutions/support_138_gauged/solution.json` | `MM3/Scheme138Gauged.lean` | 2, 2, 2 | `scheme138Gauged_valid`, `scheme138Gauged_identities`, `scheme138Gauged_support` |
| `solutions/exotic_139_support_139/solution.json` | `MM3/Scheme139Exotic.lean` | 2, 2, 1 | `scheme139Exotic_valid`, `scheme139Exotic_identities`, `scheme139Exotic_support` |
| `solutions/core1809_support_143/solution.json` | `MM3/Scheme143Core1809.lean` | 2, 1, 2 | `scheme143Core1809_valid`, `scheme143Core1809_identities`, `scheme143Core1809_support` |

the module `MM3/Certificates.lean` proves three statements about the integer data `su, sv, sw, u, v, w` of the data module:

1. `*_valid : brentOK su sv sw u v w = true`. The checker `brentOK` (in `MM3/Brent.lean`) returns `true` only if `u`, `v`, `w` each have 23 rows of 9 entries, the scale factors are nonzero, and for all `a, b, c` in `0..8`

       sum over t of u[t][a] * v[t][b] * w[t][c] = su * sv * sw * T[a][b][c],

   where `T[3i+j][3j+k][3k+i] = 1` and all other entries of `T` are `0` (`A` and `B` indexed row-major, `C` as `3 * column + row`). This is the Brent criterion used by `verify/verify.py` and `verify/verify.c`.
2. `*_identities`: the same 729 identities restated as a universally quantified proposition, obtained from `*_valid` through the soundness lemma `brentOK_sound`.
3. `*_support : support u v w = N` with `N` equal to 138, 138, 139 and 143 respectively: the number of nonzero entries of `u`, `v` and `w` together.

The integer data is the rational scheme with each factor matrix multiplied by the least common multiple of its denominators (the scale factors in the table). Scaling a factor matrix by a nonzero integer changes neither the set of nonzero entries nor the validity of the scheme (the identity is scaled by `su * sv * sw`), so the theorems certify the rational schemes as they appear in the JSON files.

All `*_valid` and `*_support` theorems are closed by the `decide` tactic, which means the Lean kernel itself evaluated the checker on the data; `#print axioms` reports that they depend on no axioms at all. The `*_identities` theorems depend on `propext` and `Quot.sound` (standard axioms introduced by `simp` in the soundness lemma). `native_decide`, which would trust the Lean compiler, was not needed and is not used anywhere.

## What was not proven

- Nothing about minimality: the certificate says nothing about whether support 138 is the smallest possible, about tensor rank 22, or about any scheme other than the four listed.
- The link between the JSON files and the Lean data modules is the generator `gen.py`, not Lean. A reader checks it by regenerating the modules and diffing (below), or by reading the 23 rows directly; the data modules are small.
- The Brent identities are the standard criterion for a bilinear scheme to compute the matrix product; that equivalence is stated in prose in `MM3/Brent.lean` and is not itself formalized as a statement about matrices.

## Toolchain

- Lean `leanprover/lean4:v4.34.1` (Lean 4.34.1, Lake 5.0.0), pinned in `lean-toolchain`; `elan` 4.2.4 selects it automatically inside this directory.
- Core Lean only: no Mathlib, no package dependencies (`lake-manifest.json` lists none).
- `elan` was installed into `~/.elan` without modifying any shell profile, so the shell needs `export PATH="$HOME/.elan/bin:$PATH"` (fish: `set -gx PATH $HOME/.elan/bin $PATH`).

Installation from scratch:

    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none --no-modify-path
    export PATH="$HOME/.elan/bin:$PATH"
    elan toolchain install leanprover/lean4:v4.34.1      # about 3 minutes, download of about 500 MB

## Commands

    cd lean && lake build                     # builds the library MM3, including all certificate theorems
    python3 lean/gen.py --check               # regenerates the data modules in memory and diffs them against MM3/*.lean
    python3 lean/gen.py                       # rewrites the four data modules from solutions/*/solution.json
    python3 lean/gen.py SOLUTION.json Name OUT.lean    # one scheme, explicit paths

To print the axioms used, run `lake env lean` on a file containing `import MM3` followed by `#print axioms MM3.scheme138_valid` and the other theorem names.

On a shared machine, prefix the build with `taskset -c 0-3` to cap it at four cores; that is how the timings below were taken.

## Build time

Clean build (`rm -rf .lake && lake build`), Intel Core i5 with 6 cores, 4 cores allowed: 14.9 s wall, 26.6 s CPU. The certificate module `MM3/Certificates.lean` took 13 s of that; the four `*_valid` theorems take about 6 s each in the elaborator, the eight other theorems well under a second. The data and checker modules build in about half a second each. (`decide +kernel` closes each `*_valid` theorem in about 2.3 s; plain `decide` was kept because it needed no options.)

## Corrupted scheme check

A copy of this directory was built with one entry of `MM3/Scheme138.lean` changed (row 1 of `u`, entry 5, from `8` to `7`). The build failed with

    error: MM3/Certificates.lean:20:2: Tactic `decide` proved that the proposition
      brentOK Scheme138.su Scheme138.sv Scheme138.sw Scheme138.u Scheme138.v Scheme138.w = true
    is false
    error: build failed

so a single wrong coefficient is caught. The copy was discarded; the directory here holds the unmodified data.

## Layout

- `lean-toolchain`: the toolchain pin.
- `lakefile.toml`: the package `mm3` with the single library `MM3`.
- `MM3.lean`: the library root, importing everything below.
- `MM3/Brent.lean`: the target tensor, the checker `brentOK`, the function `support`, and the soundness lemma `brentOK_sound`.
- `MM3/Scheme138.lean`, `MM3/Scheme138Gauged.lean`, `MM3/Scheme139Exotic.lean`, `MM3/Scheme143Core1809.lean`: generated integer data.
- `MM3/Certificates.lean`: the twelve theorems.
- `gen.py`: the generator (Python 3 standard library only).
- `.lake/`: build outputs, ignored by git.
