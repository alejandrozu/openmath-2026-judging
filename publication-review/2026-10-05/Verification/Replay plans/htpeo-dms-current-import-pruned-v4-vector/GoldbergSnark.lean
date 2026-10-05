/-
  GoldbergSnark.lean — every Goldberg snark G_k (k odd, k ≥ 5) has a star edge colouring with 5 colours.

  G_k: vertices v_a^t (a = 1..8, t ∈ Z/k); for every t the nine block edges
    v1v2, v1v7, v2v8, v3v4, v3v8, v4v7, v5v6, v6v7, v6v8   (all in block t)
  and the three link edges  v2^t v1^{t+1},  v4^t v3^{t+1},  v5^t v5^{t+1}   (block indices mod k).

  Encoding as a cyclic block graph (`BlockStar.BG`): vertex v_a^t has type a-1 and number 8t + (a-1) in
  `Fin (k * 8)`; the edge types 0..11 are the twelve edges above in this order, edge (t, s) has number
  12t + s in `Fin (k * 12)`.  All blocks have the same wiring (wiring kind `Unit`).
-/
import SeamStar

namespace GoldbergSnark
open BlockStar SeamSeq SeamStar

/-- tail type of the edge type `s` -/
def gsrc (s : Nat) : Nat := match s with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 5 | 8 => 5
  | 9 => 1 | 10 => 3 | _ => 4
/-- head type of the edge type `s` -/
def gdst (s : Nat) : Nat := match s with
  | 0 => 1 | 1 => 6 | 2 => 7 | 3 => 3 | 4 => 7 | 5 => 6 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 0 | 10 => 2 | _ => 4
/-- 1 iff the edge type `s` is a link to the next block -/
def gjmp (s : Nat) : Nat := match s with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | _ => 1

def goldbergWir : Wir Unit 8 12 where
  D := 1
  src := fun _ s => gsrc s
  jmp := fun _ s => gjmp s
  dst := fun _ s => gdst s
  hsrc := by intro w s; unfold gsrc; split <;> omega
  hdst := by intro w s; unfold gdst; split <;> omega
  hjmp := by intro w s; unfold gjmp; split <;> omega
  jumps := [0, 1]
  hjmps := by intro w s; unfold gjmp; split <;> decide

/-- the Goldberg snark G_k -/
def goldbergSnark (k : Nat) : MGraph := BG goldbergWir k (fun _ => ())

/-- colour patterns (colours 0..4) of the twelve edges of a block, rows P0, P1, P2, P3, Q, T0, T1, T2 -/
def gtab : List (List Nat) :=
  [[0, 4, 3, 2, 0, 3, 2, 0, 1, 1, 0, 0], [2, 4, 0, 1, 4, 0, 3, 2, 1, 3, 2, 4],
   [1, 4, 3, 3, 4, 0, 0, 1, 2, 0, 2, 3], [4, 1, 3, 0, 1, 3, 0, 2, 4, 2, 4, 1],
   [1, 0, 3, 1, 0, 3, 4, 1, 2, 2, 4, 3], [0, 1, 2, 2, 1, 3, 2, 0, 3, 4, 4, 4],
   [3, 1, 2, 3, 1, 2, 0, 3, 4, 0, 0, 3], [4, 1, 3, 3, 1, 2, 4, 0, 2, 2, 4, 1]]

/-- colour of the edge type `s` in the pattern with code `c` (the `% 5` only makes the bound evident) -/
def gct (c s : Nat) : Nat := ((gtab.getD c []).getD s 0) % 5

theorem gct_lt : ∀ c s, gct c s < 5 := fun _ _ => Nat.mod_lt _ (by decide)

/-- the colouring: edge `(t, s)` gets colour `gct (chi k t) s` -/
def goldbergCol (k : Nat) : Fin (goldbergSnark k).m → Fin 5 := bcol 12 gct gct_lt (chi k)

theorem W5 : winsAll goldbergWir (fun _ => ()) gct chi1 5 := by decide +kernel
theorem W9 : winsAll goldbergWir (fun _ => ()) gct chi1 9 := by decide +kernel
theorem W13 : winsAll goldbergWir (fun _ => ()) gct chi1 13 := by decide +kernel
theorem W7 : winsAll goldbergWir (fun _ => ()) gct chi3 7 := by decide +kernel
theorem W11 : winsAll goldbergWir (fun _ => ()) gct chi3 11 := by decide +kernel
theorem W15 : winsAll goldbergWir (fun _ => ()) gct chi3 15 := by decide +kernel

/-- **Goldberg snarks.** For every odd `k ≥ 5`, `goldbergCol k` is a star edge colouring of G_k with 5 colours. -/
theorem goldberg_star (k : Nat) (hodd : k % 2 = 1) (hk : 5 ≤ k) : (goldbergSnark k).Star 5 (goldbergCol k) :=
  seam_star goldbergWir rfl (fun _ => ()) gct gct_lt W5 W9 W13 W7 W11 W15 k hodd hk

end GoldbergSnark

#print axioms GoldbergSnark.goldberg_star
