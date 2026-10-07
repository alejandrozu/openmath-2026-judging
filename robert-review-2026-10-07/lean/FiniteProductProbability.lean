/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import UniformOperatorSample
import Mathlib.MeasureTheory.Measure.Prod

/-! # Finite product-event assembly for independent shore selectors

This generic probability lemma only assembles finite event/fibre bounds. The
two-shore matrix theorem must supply those bounds using the proved sampling
theorems; none of its concentration or spectral conclusions are asserted here.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory Finset
open scoped BigOperators Classical

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
  [MeasurableSpace Ω] [MeasurableSpace Λ]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass Λ]

theorem finite_probability_real_event_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) : μ.real E = ∑ ω, if ω ∈ E then μ.real {ω} else 0 := by
  have hset : ((univ.filter fun ω : Ω => ω ∈ E) : Set Ω) = E := by
    ext ω
    simp
  have h := sum_measureReal_singleton (μ := μ) (univ.filter fun ω : Ω => ω ∈ E)
  rw [hset, sum_filter] at h
  exact h.symm

theorem finite_product_singleton_real (μ : Measure Ω) (ν : Measure Λ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ω : Ω) (η : Λ) :
    (μ.prod ν).real {(ω, η)} = μ.real {ω} * ν.real {η} := by
  rw [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

theorem finite_product_real_fiber_sum (μ : Measure Ω) (ν : Measure Λ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (E : Set (Ω × Λ)) :
    (μ.prod ν).real E = ∑ ω, μ.real {ω} * ν.real {η | (ω, η) ∈ E} := by
  rw [finite_probability_real_event_sum (μ.prod ν) E, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro ω _
  rw [finite_probability_real_event_sum ν {η | (ω, η) ∈ E}, mul_sum]
  apply sum_congr rfl
  intro η _
  by_cases hmem : (ω, η) ∈ E
  · simp only [hmem, if_true, Set.mem_ofPred_eq, finite_product_singleton_real]
  · simp only [hmem, if_false, Set.mem_ofPred_eq, mul_zero]

theorem finite_product_bad_fiber_bound (μ : Measure Ω) (ν : Measure Λ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (Ω × Λ)) (A : Set Ω) (b : ℝ) (hb : 0 ≤ b)
    (hfiber : ∀ ω ∉ A, ν.real {η | (ω, η) ∈ E} ≤ b) :
    (μ.prod ν).real E ≤ μ.real A + b := by
  rw [finite_product_real_fiber_sum]
  have hsum : ∑ ω, μ.real {ω} = 1 := by
    have h := sum_measureReal_singleton (μ := μ) (univ : Finset Ω)
    simpa using h
  calc
    _ ≤ ∑ ω, ((if ω ∈ A then μ.real {ω} else 0) + b * μ.real {ω}) := by
      apply sum_le_sum
      intro ω _
      have hw : 0 ≤ μ.real {ω} := measureReal_nonneg
      by_cases hA : ω ∈ A
      · rw [if_pos hA]
        have hbound : μ.real {ω} * ν.real {η | (ω, η) ∈ E} ≤ μ.real {ω} := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (measureReal_le_one (μ := ν) (s := {η | (ω, η) ∈ E})) hw
        linarith [mul_nonneg hb hw]
      · rw [if_neg hA]
        have hbound := mul_le_mul_of_nonneg_left (hfiber ω hA) hw
        simpa only [zero_add, mul_comm] using hbound
    _ = μ.real A + b := by
      rw [sum_add_distrib, ← mul_sum, ← finite_probability_real_event_sum μ A, hsum, mul_one]

#print axioms finite_product_real_fiber_sum
#print axioms finite_product_bad_fiber_bound
#check @finite_product_bad_fiber_bound
end OpenMathReview.Sampling
