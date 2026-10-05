/-
  GPn2T.lean — generalized Petersen graphs GP(n,2), n ≥ 5: the colouring (tables and definitions).

  GP(n,2) = `GPk.gp n 2` (see GPPeriodic.lean): u_i = 2i, v_i = 2i+1; edges 3i: u_i u_{i+1}, 3i+1: u_i v_i,
  3i+2: v_i v_{i+2}.  Colouring: for n ≥ 15 a periodic part of period 5 (patterns P0..P4; block
  J < n - n mod 5 - 5 gets P_(J mod 5)) followed by a seam of length n mod 5 + 5 that depends on n mod 5;
  explicit colourings for 5 ≤ n < 15.  A pattern is [outer, spoke, inner] with colours 0..4.
  The tables were found by a SAT search on 2026-10-02 (search/gpsearch.py, search/gp2.json); this file was generated
  by search/gen_gpk.py.  The Lean proof does not depend on the search: all windows are checked by `decide`.
-/
import GPPeriodic

namespace GPn2
open BlockStar GPk

/-- row r (r = n mod 5): P0..P4 followed by the seam for this residue -/
def tabs : List (List (List Nat)) :=
  [[[1, 0, 3], [4, 0, 2], [3, 2, 1], [0, 1, 4], [2, 3, 4], [1, 0, 3],
    [2, 3, 2], [0, 4, 1], [2, 1, 4], [4, 3, 4]],
   [[1, 0, 3], [4, 0, 2], [3, 2, 1], [0, 1, 4], [2, 3, 4], [1, 3, 0],
    [2, 0, 2], [3, 4, 1], [0, 4, 1], [2, 3, 4], [4, 3, 4]],
   [[1, 0, 3], [4, 0, 2], [3, 2, 1], [0, 1, 4], [2, 3, 4], [1, 0, 3],
    [4, 2, 0], [3, 1, 0], [2, 4, 1], [0, 4, 1], [2, 3, 4], [4, 3, 4]],
   [[1, 0, 3], [4, 0, 2], [3, 2, 1], [0, 1, 4], [2, 3, 4], [4, 3, 0],
    [2, 0, 3], [1, 3, 2], [2, 0, 2], [3, 4, 1], [0, 4, 1], [2, 3, 4],
    [4, 3, 4]],
   [[1, 0, 3], [4, 0, 2], [3, 2, 1], [0, 1, 4], [2, 3, 4], [3, 0, 1],
    [0, 1, 0], [4, 2, 3], [1, 3, 2], [2, 0, 2], [3, 4, 1], [0, 4, 1],
    [2, 3, 4], [4, 3, 4]]]

/-- explicit colourings for n = 5..14 (row n - 5) -/
def smallTab : List (List (List Nat)) :=
  [[[0, 1, 2], [3, 2, 0], [1, 0, 1], [2, 3, 4], [4, 3, 4]],
   [[0, 1, 0], [2, 3, 0], [0, 3, 4], [1, 4, 2], [0, 3, 2], [4, 3, 1]],
   [[1, 0, 2], [4, 2, 0], [3, 0, 3], [2, 4, 1], [0, 4, 1], [2, 3, 4],
    [4, 3, 4]],
   [[1, 0, 2], [3, 0, 2], [4, 1, 0], [2, 1, 0], [3, 4, 1], [0, 4, 1],
    [2, 3, 4], [4, 3, 4]],
   [[1, 0, 1], [4, 2, 0], [0, 3, 2], [3, 1, 2], [4, 1, 0], [2, 3, 1],
    [0, 4, 1], [2, 3, 4], [4, 3, 4]],
   [[1, 0, 2], [3, 0, 2], [0, 4, 3], [4, 1, 3], [3, 1, 2], [2, 0, 2],
    [3, 4, 1], [0, 4, 1], [2, 3, 4], [4, 3, 4]],
   [[3, 4, 2], [4, 2, 4], [1, 0, 3], [2, 0, 3], [4, 1, 0], [3, 1, 2],
    [2, 4, 2], [1, 0, 3], [4, 0, 3], [2, 1, 0], [0, 1, 0]],
   [[1, 0, 3], [4, 0, 2], [3, 2, 0], [1, 0, 1], [2, 4, 1], [0, 3, 4],
    [1, 3, 2], [2, 0, 2], [3, 4, 1], [0, 4, 1], [2, 3, 4], [4, 3, 4]],
   [[1, 0, 2], [4, 0, 2], [2, 3, 4], [4, 1, 0], [3, 0, 1], [2, 4, 1],
    [0, 3, 4], [1, 3, 2], [2, 0, 2], [3, 4, 1], [0, 4, 1], [2, 3, 4],
    [4, 3, 4]],
   [[1, 0, 3], [3, 0, 2], [4, 2, 1], [3, 1, 0], [0, 2, 0], [3, 4, 1],
    [2, 4, 1], [0, 3, 4], [1, 3, 2], [2, 0, 2], [3, 4, 1], [0, 4, 1],
    [2, 3, 4], [4, 3, 4]]]

/-- index into row `n % 5` of `tabs` of the pattern of block `J` -/
def idx (n J : Nat) : Nat :=
  if J < n - n % 5 - 5 then J % 5 else 5 + (J - (n - n % 5 - 5))

/-- the pattern of block `J` -/
def chi (n J : Nat) : List Nat :=
  if n < 15 then (smallTab.getD (n - 5) []).getD J [] else (tabs.getD (n % 5) []).getD (idx n J) []

/-- the colouring -/
def col (n : Nat) : Fin (gp n 2).m → Fin 5 := bcol 3 ct ct_lt (chi n)

abbrev winsAll (n : Nat) : Prop :=
  ∀ j, j < n → winOK (gpkWir 2) ct (fun _ => ()) (fun q => chi n ((j + q) % n)) = true

end GPn2
