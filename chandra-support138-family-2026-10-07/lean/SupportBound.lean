import ZeroOutside

noncomputable section
namespace OpenMathReview.Support138Family
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

theorem count_le_of_zero_outside {R : Type*} [Zero R] [DecidableEq R]
    (f : Fin 23 → Fin 9 → K) (g : Fin 23 → Fin 9 → R)
    (h : ∀ i a, g i a = 0 → f i a = 0) : count f ≤ count g := by
  unfold count
  apply Finset.card_le_card
  intro p hp
  have hn : f p.1 p.2 ≠ 0 := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hg
  exact hn (h p.1 p.2 hg)

/-- The same literal family has at most138 nonzero scalar entries for every parameter. -/
theorem rational_family_support_le (s : K) : support s ≤ 138 := by
  have hu := count_le_of_zero_outside (u s) baseU (u_zero_outside s)
  have hv := count_le_of_zero_outside (v s) baseV (v_zero_outside s)
  have hw := count_le_of_zero_outside (w s) baseW (w_zero_outside s)
  calc
    support s = count (u s) + count (v s) + count (w s) := rfl
    _ ≤ count baseU + count baseV + count baseW := Nat.add_le_add (Nat.add_le_add hu hv) hw
    _ = 138 := by decide

#print axioms rational_family_support_le
#check @rational_family_support_le
end OpenMathReview.Support138Family
