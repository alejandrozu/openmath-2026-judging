import SupportMask

noncomputable section
namespace OpenMathReview.Support138Family
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

theorem masked_identities_row6 (s : K) (hs : s ≠ 0) (hm : s ≠ -2)
    (b c : Fin 9) : coefficient s 6 b c = target 6 b c := by
  have h2 : s + 2 ≠ 0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hm
  fin_cases b <;> fin_cases c
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (2 : Fin 9) = {(3 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (4 : Fin 9) = {(11 : Fin 23), (12 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (11 : Fin 23) ∉ {(12 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (7 : Fin 9) = {(3 : Fin 23), (12 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (3 : Fin 23) ∉ {(12 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (0 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (0 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (0 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (4 : Fin 9) = {(11 : Fin 23), (16 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (11 : Fin 23) ∉ {(16 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (5 : Fin 9) = {(16 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (7 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (1 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (1 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (1 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (4 : Fin 9) = {(11 : Fin 23), (12 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (11 : Fin 23) ∉ {(12 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (7 : Fin 9) = {(12 : Fin 23), (17 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (12 : Fin 23) ∉ {(17 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (2 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (2 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (2 : Fin 9) (8 : Fin 9) = {(17 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (4 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (7 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (3 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (3 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (3 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (4 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (7 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (4 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (4 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (4 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (2 : Fin 9) = {(3 : Fin 23), (20 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (3 : Fin 23) ∉ {(20 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (4 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (7 : Fin 9) = {(3 : Fin 23), (17 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (3 : Fin 23) ∉ {(17 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (5 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (5 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (5 : Fin 9) (8 : Fin 9) = {(17 : Fin 23), (20 : Fin 23)} := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_insert (show (17 : Fin 23) ∉ {(20 : Fin 23)} by decide)]
    rw [Finset.sum_singleton]
    norm_num [target, u, v, w] <;> field_simp [hs, h2] <;> ring
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (4 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (7 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (6 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (6 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (6 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (4 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (7 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (7 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (7 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (7 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (0 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (0 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (0 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (1 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (1 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (1 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (2 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (2 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (2 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (3 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (3 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (3 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (4 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (4 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (4 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (5 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (5 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (5 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (6 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (6 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (6 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (7 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (7 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (7 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]
  · change coefficient s (6 : Fin 9) (8 : Fin 9) (8 : Fin 9) = target (6 : Fin 9) (8 : Fin 9) (8 : Fin 9)
    have hmask : activeTerms (6 : Fin 9) (8 : Fin 9) (8 : Fin 9) = (∅ : Finset (Fin 23)) := by decide
    rw [coefficient_eq_activeTerms s hs hm, hmask]
    rw [Finset.sum_empty]
    norm_num [target]

#print axioms masked_identities_row6
end OpenMathReview.Support138Family
