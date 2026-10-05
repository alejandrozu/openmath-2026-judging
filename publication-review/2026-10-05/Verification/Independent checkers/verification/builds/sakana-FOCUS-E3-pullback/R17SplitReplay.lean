-- Reconstructed proof partition; original B and final statements preserved.
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-! Verified finite lower witness only: a 79-point 4-point-L-free subset of (ZMod 13)^2.
This does NOT prove r4_cyclic(13) ≤ 6 or the Erdős #3 hill. -/

set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Erdos3R17

def B : Finset (ZMod 13 × ZMod 13) := {(0, 0), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 9), (1, 0), (1, 1), (1, 3), (1, 4), (1, 7), (1, 12), (2, 1), (2, 2), (2, 6), (2, 7), (2, 9), (3, 1), (3, 4), (3, 6), (3, 8), (3, 10), (3, 11), (4, 0), (4, 3), (4, 4), (4, 7), (4, 8), (4, 11), (5, 0), (5, 1), (5, 3), (5, 5), (5, 7), (5, 10), (5, 11), (6, 1), (6, 2), (6, 4), (6, 5), (6, 10), (6, 12), (7, 4), (7, 5), (7, 7), (7, 8), (7, 10), (7, 12), (8, 2), (8, 6), (8, 8), (8, 9), (8, 11), (8, 12), (9, 1), (9, 2), (9, 5), (9, 6), (9, 7), (9, 9), (10, 1), (10, 2), (10, 3), (10, 8), (10, 11), (10, 12), (11, 0), (11, 2), (11, 3), (11, 8), (11, 10), (11, 12), (12, 2), (12, 4), (12, 5), (12, 6), (12, 9), (12, 10)}

theorem B_card : B.card = 79 := by decide +kernel

theorem B_Lfree_row_0 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((0 : ZMod 13), y) ∈ B ∧ (0, y + d) ∈ B ∧ (0, y + 2 * d) ∈ B ∧ (0 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_1 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((1 : ZMod 13), y) ∈ B ∧ (1, y + d) ∈ B ∧ (1, y + 2 * d) ∈ B ∧ (1 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_2 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((2 : ZMod 13), y) ∈ B ∧ (2, y + d) ∈ B ∧ (2, y + 2 * d) ∈ B ∧ (2 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_3 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((3 : ZMod 13), y) ∈ B ∧ (3, y + d) ∈ B ∧ (3, y + 2 * d) ∈ B ∧ (3 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_4 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((4 : ZMod 13), y) ∈ B ∧ (4, y + d) ∈ B ∧ (4, y + 2 * d) ∈ B ∧ (4 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_5 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((5 : ZMod 13), y) ∈ B ∧ (5, y + d) ∈ B ∧ (5, y + 2 * d) ∈ B ∧ (5 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_6 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((6 : ZMod 13), y) ∈ B ∧ (6, y + d) ∈ B ∧ (6, y + 2 * d) ∈ B ∧ (6 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_7 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((7 : ZMod 13), y) ∈ B ∧ (7, y + d) ∈ B ∧ (7, y + 2 * d) ∈ B ∧ (7 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_8 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((8 : ZMod 13), y) ∈ B ∧ (8, y + d) ∈ B ∧ (8, y + 2 * d) ∈ B ∧ (8 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_9 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((9 : ZMod 13), y) ∈ B ∧ (9, y + d) ∈ B ∧ (9, y + 2 * d) ∈ B ∧ (9 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_10 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((10 : ZMod 13), y) ∈ B ∧ (10, y + d) ∈ B ∧ (10, y + 2 * d) ∈ B ∧ (10 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_11 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((11 : ZMod 13), y) ∈ B ∧ (11, y + d) ∈ B ∧ (11, y + 2 * d) ∈ B ∧ (11 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree_row_12 : ∀ y d : ZMod 13, d ≠ 0 →
    ¬ (((12 : ZMod 13), y) ∈ B ∧ (12, y + d) ∈ B ∧ (12, y + 2 * d) ∈ B ∧ (12 + d, y) ∈ B) := by
  decide +kernel

theorem B_Lfree : ∀ x y d : ZMod 13, d ≠ 0 →
    ¬ ((x, y) ∈ B ∧ (x, y + d) ∈ B ∧ (x, y + 2 * d) ∈ B ∧ (x + d, y) ∈ B) := by
  intro x
  fin_cases x
  · exact B_Lfree_row_0
  · exact B_Lfree_row_1
  · exact B_Lfree_row_2
  · exact B_Lfree_row_3
  · exact B_Lfree_row_4
  · exact B_Lfree_row_5
  · exact B_Lfree_row_6
  · exact B_Lfree_row_7
  · exact B_Lfree_row_8
  · exact B_Lfree_row_9
  · exact B_Lfree_row_10
  · exact B_Lfree_row_11
  · exact B_Lfree_row_12

end Erdos3R17

#print axioms Erdos3R17.B_card
#print axioms Erdos3R17.B_Lfree
