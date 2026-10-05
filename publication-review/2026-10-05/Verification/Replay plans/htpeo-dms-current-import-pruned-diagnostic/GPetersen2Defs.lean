/-
  GPetersen2Defs.lean — generalized Petersen graphs GP(k,2), k ≥ 5: a star edge colouring with 6 colours whose
  sixth colour class is exactly the set of spokes.

  GP(k,2): vertices u_i, v_i (i ∈ Z/k); edges u_i u_{i+1} (outer), u_i v_i (spokes), v_i v_{i+2} (inner).

  Encoding as a cyclic block graph (`BlockStar.BG`): block i = {u_i, v_i}, u_i = 2i, v_i = 2i+1 in `Fin (k * 2)`;
  edge types 0: u_i u_{i+1}, 1: u_i v_i, 2: v_i v_{i+2}; edge (i, s) has number 3i+s in `Fin (k * 3)`.
  A colour pattern of a block is a pair (o, w): outer edge colour o, inner edge colour w (both in 0..4); the
  spoke gets colour 5.
-/
import BlockStar
import SeamSeq

namespace GPetersen2
open BlockStar

def psrc (s : Nat) : Nat := match s with
  | 0 => 0 | 1 => 0 | _ => 1
def pdst (s : Nat) : Nat := match s with
  | 0 => 0 | _ => 1
def pjmp (s : Nat) : Nat := match s with
  | 0 => 1 | 1 => 0 | _ => 2

def gpWir : Wir Unit 2 3 where
  D := 2
  src := fun _ s => psrc s
  jmp := fun _ s => pjmp s
  dst := fun _ s => pdst s
  hsrc := by intro w s; unfold psrc; split <;> omega
  hdst := by intro w s; unfold pdst; split <;> omega
  hjmp := by intro w s; unfold pjmp; split <;> omega
  jumps := [0, 1, 2]
  hjmps := by intro w s; unfold pjmp; split <;> decide

/-- the generalized Petersen graph GP(k,2) -/
def gp2 (k : Nat) : MGraph := BG gpWir k (fun _ => ())

/-- colour of the edge type `s` in a block with pattern `(o, w)` (the `% 5` only makes the bound evident) -/
def pct (c : Nat × Nat) (s : Nat) : Nat := if s = 0 then c.1 % 5 else if s = 1 then 5 else c.2 % 5

theorem pct_lt : ∀ c s, pct c s < 6 := by
  intro c s; unfold pct; split_ifs <;> omega

/-- the periodic words A (length 5) and B (length 6), concatenated -/
def tabAB : List (Nat × Nat) :=
  [(1, 2), (0, 3), (4, 1), (2, 0), (3, 4),
   (1, 2), (3, 2), (4, 1), (3, 1), (2, 4), (3, 4)]

def S7 : List (Nat × Nat) := [(4, 2), (1, 2), (3, 0), (4, 1), (3, 1), (2, 0), (3, 0)]
def S8 : List (Nat × Nat) := [(4, 2), (3, 2), (1, 0), (3, 0), (4, 1), (3, 1), (2, 0), (3, 0)]
def S9 : List (Nat × Nat) := [(3, 0), (1, 2), (3, 2), (0, 4), (1, 4), (0, 2), (3, 1), (4, 1), (2, 0)]
def S13 : List (Nat × Nat) := [(3, 2), (0, 1), (3, 1), (2, 0), (3, 0), (1, 2), (3, 2), (4, 0), (1, 0), (2, 3), (1, 3), (4, 0), (1, 2)]
def S14 : List (Nat × Nat) := [(1, 2), (3, 2), (0, 1), (3, 1), (2, 0), (3, 0), (4, 2), (3, 2), (1, 0), (3, 0), (4, 1), (3, 1), (2, 0), (3, 0)]
def S19 : List (Nat × Nat) := [(4, 3), (2, 3), (1, 0), (4, 2), (3, 2), (1, 0), (3, 0), (4, 1), (3, 1), (2, 0), (3, 0), (4, 2), (3, 2), (1, 0), (3, 0), (4, 1), (2, 1), (3, 0), (2, 0)]

/-- the special sequences for k = 7, 8, 9, 13, 14, 19 (the k that are not of the form 5a + 6b) -/
def special (k : Nat) : List (Nat × Nat) :=
  if k = 7 then S7 else if k = 8 then S8 else if k = 9 then S9 else if k = 13 then S13
  else if k = 14 then S14 else S19

/-- for k = 5a + 6b with b = k mod 5: index into `tabAB` of the pattern of block `J` of the word A^a B^b -/
def gidx (k J : Nat) : Nat :=
  if J < k - 6 * (k % 5) then J % 5 else 5 + (J - (k - 6 * (k % 5))) % 6

/-- the pattern of block `J` -/
def pchi (k J : Nat) : Nat × Nat :=
  if k < 20 ∧ k < 6 * (k % 5) then (special k).getD J (0, 0) else tabAB.getD (gidx k J) (0, 0)

/-- the colouring -/
def gpCol (k : Nat) : Fin (gp2 k).m → Fin 6 := bcol 3 pct pct_lt (pchi k)

abbrev winsAll (k : Nat) : Prop :=
  ∀ j, j < k → winOK gpWir pct (fun _ => ()) (fun p => pchi k ((j + p) % k)) = true

end GPetersen2
