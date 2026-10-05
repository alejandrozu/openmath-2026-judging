import Erdos3Blocks
import Erdos3Reduction

/-!
# A dyadic counting criterion for reciprocal summability

This proves an analytic transfer, not the missing progression-free counting
bound. Each natural number belongs to one logarithm block; its reciprocal
mass is bounded by the block's cardinality divided by its lower scale.
-/

namespace Erdos3Dyadic

open Erdos3Blocks

/-- A summable sequence of normalized block counts makes the reciprocals summable. -/
theorem reciprocal_summable_of_dyadic_counts (A : Set ℕ)
    (hcounts : Summable fun j : ℕ ↦
      ((logBlock A j).ncard : ℝ) / (2 : ℝ) ^ j) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  have hpartition : ∀ a : A, ∃! j : ℕ, a ∈ logBlock A j := by
    intro a
    exact ⟨Nat.log 2 (a : ℕ), rfl, fun j hj ↦ hj.symm⟩
  apply (summable_partition (f := fun a : A ↦ 1 / (a : ℝ))
    (s := logBlock A) (by intro a; positivity) hpartition).mpr
  constructor
  · intro j
    exact (logBlock_finite A j).summable (fun a : A ↦ 1 / (a : ℝ))
  · exact Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg (fun a ↦ by positivity))
      (fun j ↦ logBlock_mass_le A j) hcounts

/-- Any block-density bound by a convergent p-series is sufficient. -/
theorem reciprocal_summable_of_power_envelope (A : Set ℕ) {C p : ℝ}
    (hp : 1 < p)
    (hbound : ∀ j : ℕ, ((logBlock A j).ncard : ℝ) / (2 : ℝ) ^ j ≤
      C / ((j : ℝ) + 1) ^ p) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  apply reciprocal_summable_of_dyadic_counts
  have hseries : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ p) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (Real.summable_one_div_nat_rpow.mpr hp).comp_injective Nat.succ_injective
  have hscaled : Summable (fun j : ℕ ↦ C / ((j : ℝ) + 1) ^ p) := by
    simpa only [mul_one_div] using hseries.mul_left C
  exact Summable.of_nonneg_of_le (fun j ↦ by positivity) hbound hscaled

/-- An explicit sufficient counting hypothesis. It remains unproved here. -/
def APFreePowerEnvelope : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ C p : ℝ, 1 < p ∧
    ∀ A : Set ℕ, A.IsAPOfLengthFree k → ∀ j : ℕ,
      ((logBlock A j).ncard : ℝ) / (2 : ℝ) ^ j ≤ C / ((j : ℝ) + 1) ^ p

/-- Conditional route from a quantitative bound to the original hill conclusion.
The counting hypothesis is a parameter, not an established bound or an axiom. -/
theorem hill_of_apFree_power_envelope (hbound : APFreePowerEnvelope) :
    True ↔ ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply Erdos3Reduction.hill_of_apFreeSummability
  intro k hk A hA
  obtain ⟨C, p, hp, hcount⟩ := hbound k hk
  exact reciprocal_summable_of_power_envelope A hp (hcount A hA)

#print axioms reciprocal_summable_of_dyadic_counts
#print axioms reciprocal_summable_of_power_envelope
#check hill_of_apFree_power_envelope
#print axioms hill_of_apFree_power_envelope

end Erdos3Dyadic
