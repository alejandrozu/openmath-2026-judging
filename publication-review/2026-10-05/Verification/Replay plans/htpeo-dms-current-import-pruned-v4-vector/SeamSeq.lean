/-
  SeamSeq.lean — the block sequences "period 4 plus seam" used for the flower and Goldberg snarks, and the
  reduction of their cyclic windows of 4 consecutive blocks to the windows of the sequences of length 13 / 15.

  Pattern codes: 0,1,2,3 = P0..P3 (periodic part), 4 = Q (seam for n = 4t+1), 5,6,7 = T0,T1,T2 (seam for n = 4t+3).
    n = 4t+1 :  P0 P1 P2 P3 … P0 P1 P2 P3 Q            (`chi1`)
    n = 4t+3 :  P0 P1 P2 P3 … P0 P1 P2 P3 T0 T1 T2     (`chi3`)
  `tw n J = 1` iff `J` is the last block (used by the flower snark, whose last block is wired with a twist).
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

namespace SeamSeq

def tw (n J : Nat) : Nat := if J + 1 = n then 1 else 0
def chi1 (n J : Nat) : Nat := if J + 1 = n then 4 else J % 4
def chi3 (n J : Nat) : Nat := if n ≤ J + 3 then 5 + (J + 3 - n) else J % 4
/-- pattern code of block `J` of the sequence of length `n` (`n` odd) -/
def chi (n J : Nat) : Nat := if n % 4 = 1 then chi1 n J else chi3 n J

theorem modc {n j p : Nat} (hj : j < n) (hp : p ≤ n) :
    (j + p) % n = if j + p < n then j + p else j + p - n := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

/-- every cyclic window of 4 blocks of the sequence of length `n = 4t+1 ≥ 13` occurs in the sequence of length 13 -/
theorem rep1 {n : Nat} (h4 : n % 4 = 1) (h13 : 13 ≤ n) {j : Nat} (hj : j < n) :
    ∃ j', j' < 13 ∧ ∀ p, p ≤ 3 →
      tw 13 ((j' + p) % 13) = tw n ((j + p) % n) ∧ chi1 13 ((j' + p) % 13) = chi1 n ((j + p) % n) := by
  rcases (show j < 4 ∨ n ≤ j + 5 ∨ (4 ≤ j ∧ j + 5 < n) by omega) with c | c | c
  · refine ⟨j, by omega, ?_⟩
    intro p hp
    rw [modc hj (by omega)]
    simp only [tw, chi1]
    constructor <;> split_ifs <;> omega
  · refine ⟨j + 13 - n, by omega, ?_⟩
    intro p hp
    rw [modc hj (by omega)]
    simp only [tw, chi1]
    constructor <;> split_ifs <;> omega
  · refine ⟨4 + j % 4, by omega, ?_⟩
    intro p hp
    rw [modc hj (by omega)]
    simp only [tw, chi1]
    constructor <;> split_ifs <;> omega

/-- every cyclic window of 4 blocks of the sequence of length `n = 4t+3 ≥ 15` occurs in the sequence of length 15 -/
theorem rep3 {n : Nat} (h4 : n % 4 = 3) (h15 : 15 ≤ n) {j : Nat} (hj : j < n) :
    ∃ j', j' < 15 ∧ ∀ p, p ≤ 3 →
      tw 15 ((j' + p) % 15) = tw n ((j + p) % n) ∧ chi3 15 ((j' + p) % 15) = chi3 n ((j + p) % n) := by
  rcases (show j < 4 ∨ n ≤ j + 7 ∨ (4 ≤ j ∧ j + 7 < n) by omega) with c | c | c
  · refine ⟨j, by omega, ?_⟩
    intro p hp
    rw [modc hj (by omega)]
    simp only [tw, chi3]
    constructor <;> split_ifs <;> omega
  · refine ⟨j + 15 - n, by omega, ?_⟩
    intro p hp
    rw [modc hj (by omega)]
    simp only [tw, chi3]
    constructor <;> split_ifs <;> omega
  · refine ⟨4 + j % 4, by omega, ?_⟩
    intro p hp
    rw [modc hj (by omega)]
    simp only [tw, chi3]
    constructor <;> split_ifs <;> omega

end SeamSeq
