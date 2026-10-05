/-
  FlowerSnark.lean — every flower snark J_n (n odd, n ≥ 5) has a star edge colouring with 5 colours.

  J_n (Isaacs): vertices a_j, b_j, c_j, d_j (j = 0..n-1); edges a_j b_j, a_j c_j, a_j d_j, b_j b_{j+1 mod n} for
  all j; c_j c_{j+1}, d_j d_{j+1} for j ≤ n-2; and c_{n-1} d_0, d_{n-1} c_0.

  Encoding as a cyclic block graph (`BlockStar.BG`): block j = {a_j, b_j, c_j, d_j}, vertex types
  a = 0, b = 1, c = 2, d = 3, so  a_j = 4j, b_j = 4j+1, c_j = 4j+2, d_j = 4j+3  in `Fin (n * 4)`;
  edge types 0: a_j b_j, 1: a_j c_j, 2: a_j d_j, 3: b_j b_{j+1}, 4: the edge from c_j to block j+1,
  5: the edge from d_j to block j+1; edge (j, s) has number 6j+s in `Fin (n * 6)`.
  Wiring kind 0 (blocks j ≤ n-2): c_j c_{j+1}, d_j d_{j+1};  kind 1 (the last block j = n-1): c_{n-1} d_0, d_{n-1} c_0.
-/
import SeamStar

namespace FlowerSnark
open BlockStar SeamSeq SeamStar

/-- tail type of the edge type `s` -/
def fsrc (s : Nat) : Nat := match s with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 2 | _ => 3
/-- 1 iff the edge type `s` leads to the next block -/
def fjmp (s : Nat) : Nat := match s with
  | 0 => 0 | 1 => 0 | 2 => 0 | _ => 1
/-- head type of the edge type `s` in a block of wiring kind `w` (`w = 1`: twisted) -/
def fdst (w s : Nat) : Nat := match s with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 1
  | 4 => if w = 0 then 2 else 3
  | _ => if w = 0 then 3 else 2

def flowerWir : Wir Nat 4 6 where
  D := 1
  src := fun _ s => fsrc s
  jmp := fun _ s => fjmp s
  dst := fdst
  hsrc := by intro w s; unfold fsrc; split <;> omega
  hdst := by intro w s; unfold fdst; split <;> first | omega | (split <;> omega)
  hjmp := by intro w s; unfold fjmp; split <;> omega
  jumps := [0, 1]
  hjmps := by intro w s; unfold fjmp; split <;> decide

/-- the flower snark J_n: block `J` has wiring kind `tw n J` (1 for the last block `J = n - 1`, else 0) -/
def flowerSnark (n : Nat) : MGraph := BG flowerWir n (fun J => tw n J)

/-- colour patterns (colours 0..4) of the six edges of a block, rows P0, P1, P2, P3, Q, T0, T1, T2 -/
def ftab : List (List Nat) :=
  [[0, 1, 2, 4, 3, 0], [1, 2, 3, 0, 0, 4], [2, 1, 0, 1, 3, 3], [4, 2, 0, 3, 4, 1],
   [2, 0, 3, 1, 1, 4], [0, 1, 2, 4, 0, 4], [2, 3, 1, 1, 4, 0], [0, 1, 2, 3, 3, 4]]

/-- colour of the edge type `s` in the pattern with code `c` (the `% 5` only makes the bound evident) -/
def fct (c s : Nat) : Nat := ((ftab.getD c []).getD s 0) % 5

theorem fct_lt : ∀ c s, fct c s < 5 := fun _ _ => Nat.mod_lt _ (by decide)

/-- the colouring: edge `(J, s)` gets colour `fct (chi n J) s` -/
def flowerCol (n : Nat) : Fin (flowerSnark n).m → Fin 5 := bcol 6 fct fct_lt (chi n)

theorem W5 : winsAll flowerWir id fct chi1 5 := by decide +kernel
theorem W9 : winsAll flowerWir id fct chi1 9 := by decide +kernel
theorem W13 : winsAll flowerWir id fct chi1 13 := by decide +kernel
theorem W7 : winsAll flowerWir id fct chi3 7 := by decide +kernel
theorem W11 : winsAll flowerWir id fct chi3 11 := by decide +kernel
theorem W15 : winsAll flowerWir id fct chi3 15 := by decide +kernel

/-- **Flower snarks.** For every odd `n ≥ 5`, `flowerCol n` is a star edge colouring of J_n with 5 colours. -/
theorem flower_star (n : Nat) (hodd : n % 2 = 1) (hn : 5 ≤ n) : (flowerSnark n).Star 5 (flowerCol n) :=
  seam_star flowerWir rfl id fct fct_lt W5 W9 W13 W7 W11 W15 n hodd hn

end FlowerSnark

#print axioms FlowerSnark.flower_star
