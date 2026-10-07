import ZeroOutside

noncomputable section
namespace OpenMathReview.Support138Family
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- A computational mask from frozen integer base coefficients, not an identity premise. -/
def activeTerms (a b c : Fin 9) : Finset (Fin 23) :=
  Finset.univ.filter (fun i => baseU i a ≠ 0 ∧ baseV i b ≠ 0 ∧ baseW i c ≠ 0)

/-- The finite sum is reindexed only after proving each omitted actual product zero. -/
theorem coefficient_eq_activeTerms (s : K) (hs : s ≠ 0) (hm : s ≠ -2)
    (a b c : Fin 9) : coefficient s a b c =
      ∑ i ∈ activeTerms a b c, u s i a * v s i b * w s i c := by
  classical
  unfold coefficient
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hnot
  have hbad : ¬ (baseU i a ≠ 0 ∧ baseV i b ≠ 0 ∧ baseW i c ≠ 0) := by
    simpa only [activeTerms, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  by_cases hu : baseU i a = 0
  · rw [u_zero_outside s i a hu]
    simp
  by_cases hv : baseV i b = 0
  · rw [v_zero_outside s i b hv]
    simp
  by_cases hw : baseW i c = 0
  · rw [w_zero_outside s i c hw]
    simp
  exact False.elim (hbad ⟨hu,hv,hw⟩)

#print axioms coefficient_eq_activeTerms
end OpenMathReview.Support138Family
