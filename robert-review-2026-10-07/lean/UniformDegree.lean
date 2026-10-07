/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import UniformConditioning
import BernoulliDegree

/-! # Actual fixed-count sampled-neighbour tail

The count=m law is the proved uniform law on actual m-subsets. Its tail is
obtained from the genuine Bernoulli neighbour count and the proved mode loss.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

theorem actual_full_selected_degree_tail_zero {s : ℕ} (x : Fin s → ℝ)
    (hxsum : 0 < ∑ j, x j) :
    (uniformFixedColumnLaw s s le_rfl).real
      {ω | selectedDegree x ω ≥ 2 * ∑ j, x j} = 0 := by
  rw [uniformFixedColumnLaw_real_apply]
  have hnone : (fixedCountSelectors s s).filter
      (fun ω => ω ∈ {ω | selectedDegree x ω ≥ 2 * ∑ j, x j}) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hcard : (selectedColumns ω).card = s := (mem_filter.mp (mem_filter.mp hω).1).2
    have hsel : selectedColumns ω = univ := Finset.eq_of_subset_of_card_le (subset_univ _)
      (by simpa only [card_univ, Fintype.card_fin, hcard] using (le_rfl : s ≤ s))
    have hbad := (mem_filter.mp hω).2
    change 2 * (∑ j, x j) ≤ selectedDegree x ω at hbad
    simp only [selectedDegree, hsel] at hbad
    linarith
  rw [hnone]
  simp

theorem actual_uniform_selected_degree_tail {s m : ℕ} (hs : 0 < s)
    (hm0 : 0 < m) (hm : m ≤ s) (x : Fin s → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (p : unitInterval)
    (hmean : (p : ℝ) * (s : ℝ) = (m : ℝ)) (hD : 0 < (p : ℝ) * ∑ j, x j) :
    (uniformFixedColumnLaw s m hm).real
      {ω | selectedDegree x ω ≥ 2 * ((p : ℝ) * ∑ j, x j)} ≤
      2 * ((s : ℝ) + 1) * Real.exp (-((p : ℝ) * ∑ j, x j) / 3) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  by_cases hfull : m = s
  · have hpone : (p : ℝ) = 1 := by
      rw [hfull] at hmean
      have he : ((p : ℝ) - 1) * (s : ℝ) = 0 := by nlinarith only [hmean]
      have hz := (mul_eq_zero.mp he).resolve_right (ne_of_gt hsR)
      linarith
    subst m
    rw [hpone, one_mul] at hD ⊢
    rw [actual_full_selected_degree_tail_zero x hD]
    positivity
  · have hms : m < s := by omega
    have hmsR : (m : ℝ) < s := by exact_mod_cast hms
    have hp : 0 < (p : ℝ) := by
      by_contra hp
      have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) hsR.le
      linarith
    have hp1 : (p : ℝ) < 1 := by
      by_contra hp1
      have hprod := mul_le_mul_of_nonneg_right (le_of_not_gt hp1) hsR.le
      simp only [one_mul] at hprod
      linarith
    have hcond := uniformFixedColumnLaw_event_le s m p hp hp1 hms hmean
      {ω | selectedDegree x ω ≥ 2 * ((p : ℝ) * ∑ j, x j)}
    have htail := actual_selected_degree_tail x hx p hD
    calc
      _ ≤ ((s : ℝ) + 1) * ((bernoulliColumnLaw s p)
          {ω | selectedDegree x ω ≥ 2 * ((p : ℝ) * ∑ j, x j)}).toReal := hcond
      _ ≤ ((s : ℝ) + 1) * (2 * Real.exp (-((p : ℝ) * ∑ j, x j) / 3)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring

#print axioms actual_full_selected_degree_tail_zero
#print axioms actual_uniform_selected_degree_tail
#check @actual_uniform_selected_degree_tail
end OpenMathReview.Sampling
