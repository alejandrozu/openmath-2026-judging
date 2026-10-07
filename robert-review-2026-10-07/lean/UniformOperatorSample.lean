/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import UniformConditioning
import ReindexSampling

/-! # A genuine fixed-size uniform column-sampling norm tail

For the interior case 0<m<s, p=m/s, the sampling measure assigns equal mass to
every m-subset. The polynomial loss is derived, not assumed. This is a
one-shore norm theorem; B2.2 needs the two-shore and singular-value assembly.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped Matrix.Norms.L2Operator Classical

theorem actual_fixed_column_sample_norm_tail {I : Type*} [Fintype I]
    [DecidableEq I] {s m : ℕ} (hI : 0 < Fintype.card I)
    (F : Matrix I (Fin s) ℝ) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hm : m < s)
    (hmean : (p : ℝ) * (s : ℝ) = (m : ℝ))
    (c : ℝ) (hc : 0 < c) (hcol : ∀ j, finiteRowColumnEnergy F j ≤ c ^ 2)
    (t : ℝ) (ht : 0 < t) :
    (uniformFixedColumnLaw s m hm.le).real
      {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
        Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t} ≤
      2 * (Fintype.card I : ℝ) * ((s : ℝ) + 1) * Real.exp (-t) := by
  have hcond := uniformFixedColumnLaw_event_le s m p hp hp1 hm hmean
    {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
      Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t}
  have htail := actual_finite_row_column_sample_norm_tail hI F p c hc hcol t ht
  calc
    _ ≤ ((s : ℝ) + 1) * ((bernoulliColumnLaw s p)
        {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
          Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t}).toReal := hcond
    _ ≤ ((s : ℝ) + 1) * (2 * (Fintype.card I : ℝ) * Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

theorem actual_full_column_sample_norm_tail_zero {I : Type*} [Fintype I]
    [DecidableEq I] (s : ℕ) (F : Matrix I (Fin s) ℝ)
    (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t) :
    (uniformFixedColumnLaw s s le_rfl).real
      {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
        ‖F‖ + c * Real.sqrt t} = 0 := by
  rw [uniformFixedColumnLaw_real_apply]
  have hnone : (fixedCountSelectors s s).filter
      (fun ω => ω ∈ {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
        ‖F‖ + c * Real.sqrt t}) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hcard : (selectedColumns ω).card = s := (mem_filter.mp (mem_filter.mp hω).1).2
    have hsel : selectedColumns ω = univ := Finset.eq_of_subset_of_card_le (subset_univ _) (by
      simpa only [card_univ, Fintype.card_fin, hcard] using (le_rfl : s ≤ s))
    have hbad := (mem_filter.mp hω).2
    change ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥ ‖F‖ + c * Real.sqrt t at hbad
    rw [hsel, finiteRowColumnSample_univ_norm] at hbad
    have hpositive : 0 < c * Real.sqrt t := mul_pos hc (Real.sqrt_pos.mpr ht)
    linarith
  rw [hnone]
  simp

theorem actual_positive_fixed_column_sample_norm_tail {I : Type*} [Fintype I]
    [DecidableEq I] {s m : ℕ} (hI : 0 < Fintype.card I) (hs : 0 < s) (hm0 : 0 < m)
    (hm : m ≤ s) (F : Matrix I (Fin s) ℝ) (p : unitInterval)
    (hmean : (p : ℝ) * (s : ℝ) = (m : ℝ))
    (c : ℝ) (hc : 0 < c) (hcol : ∀ j, finiteRowColumnEnergy F j ≤ c ^ 2)
    (t : ℝ) (ht : 0 < t) :
    (uniformFixedColumnLaw s m hm).real
      {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
        Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t} ≤
      2 * (Fintype.card I : ℝ) * ((s : ℝ) + 1) * Real.exp (-t) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  by_cases hfull : m = s
  · have hpone : (p : ℝ) = 1 := by
      rw [hfull] at hmean
      have he : ((p : ℝ) - 1) * (s : ℝ) = 0 := by nlinarith only [hmean]
      have hz := (mul_eq_zero.mp he).resolve_right (ne_of_gt hsR)
      linarith
    subst m
    have hzero := actual_full_column_sample_norm_tail_zero s F c hc t ht
    simpa only [hpone, Real.sqrt_one, one_mul, hzero] using
      (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card I : ℝ) * ((s : ℝ) + 1) * Real.exp (-t))
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
    exact actual_fixed_column_sample_norm_tail hI F p hp hp1 hms hmean c hc hcol t ht

#print axioms actual_fixed_column_sample_norm_tail
#print axioms actual_full_column_sample_norm_tail_zero
#print axioms actual_positive_fixed_column_sample_norm_tail
#check @actual_positive_fixed_column_sample_norm_tail
end OpenMathReview.Sampling
