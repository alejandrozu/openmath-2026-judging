/-
  InflationDefs.lean — Petersen-type vertex inflation of a multigraph: definitions.

  Petersen graph = GP(5,2): outer vertices u0..u4, inner vertices v0..v4, edges u_i u_{i+1}, u_i v_i, v_i v_{i+2}.
  The *piece* is the Petersen graph minus the vertex u0: 9 vertices, numbered
      u1, u2, u3, u4 = 0, 1, 2, 3      v0, v1, v2, v3, v4 = 4, 5, 6, 7, 8,
  and 12 edges (`pe1 s`, `pe2 s` are the two ends of the edge number s):
      0: u1u2  1: u2u3  2: u3u4  3: u1v1  4: u2v2  5: u3v3  6: u4v4  7: v0v2  8: v1v3  9: v2v4  10: v3v0  11: v4v1.
  The three neighbours of the removed vertex u0 are the *ports* `portv 0 = u1`, `portv 1 = u4`, `portv 2 = v0`.

  Inflation `inflate H slot` of a multigraph `H` (StarCore's `MGraph`): every vertex `X` of `H` is replaced by a
  copy of the piece (vertex `(X, a)` has number `9 X + a`, piece edge `(X, s)` has number `12 X + s`), and every
  edge `e` of `H` becomes an *inter edge* (number `12 * H.n + e`) joining the port `slot e false` of the piece of
  the first end of `e` to the port `slot e true` of the piece of the second end of `e`.
  `PortsInj H slot`: no two edge-ends at the same vertex of `H` use the same port (so `H` is subcubic; if `H` is
  cubic, every port carries exactly one inter edge and the inflated graph is cubic).
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import StarCore
import MhFact_5c1eb3f583cf643f

namespace Inflation

def pe1 (s : Nat) : Fin 9 := match s with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 7 | _ => 8

def pe2 (s : Nat) : Fin 9 := match s with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | 7 => 6 | 8 => 7 | 9 => 8 | 10 => 4 | _ => 5

def portv (i : Fin 3) : Fin 9 := match i.val with
  | 0 => 0 | 1 => 3 | _ => 4

/-- the end of the edge `e` of `H` on side `b` (`false`: first end, `true`: second end) -/
def endOf (H : MGraph) (e : Fin H.m) (b : Bool) : Fin H.n := bif b then (H.ends e).2 else (H.ends e).1

/-- the vertex `(X, a)` of the inflated graph -/
def mkV {n : Nat} (X : Nat) (hX : X < n) (a : Fin 9) : Fin (n * 9) :=
  ⟨X * 9 + a.val, by have := a.isLt; omega⟩

/-- the Petersen-type inflation of `H` with port assignment `slot` -/
def inflate (H : MGraph) (slot : Fin H.m → Bool → Fin 3) : MGraph where
  n := H.n * 9
  m := H.n * 12 + H.m
  ends f :=
    if h : f.val < H.n * 12 then
      (mkV (f.val / 12) (by omega) (pe1 (f.val % 12)), mkV (f.val / 12) (by omega) (pe2 (f.val % 12)))
    else
      (mkV (endOf H ⟨f.val - H.n * 12, by have := f.isLt; omega⟩ false).val (Fin.isLt _)
          (portv (slot ⟨f.val - H.n * 12, by have := f.isLt; omega⟩ false)),
       mkV (endOf H ⟨f.val - H.n * 12, by have := f.isLt; omega⟩ true).val (Fin.isLt _)
          (portv (slot ⟨f.val - H.n * 12, by have := f.isLt; omega⟩ true)))

/-- no two edge-ends at the same vertex of `H` use the same port -/
def PortsInj (H : MGraph) (slot : Fin H.m → Bool → Fin 3) : Prop :=
  ∀ e b e' b', endOf H e b = endOf H e' b' → slot e b = slot e' b' → e = e' ∧ b = b'

end Inflation
