/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import UniformOperatorSample
import UniformDegree
import SampledColumnEnergy

/-! # Actual first-shore and neighbour-count events

These are explicit uniform-set probability bounds, not concentration
hypotheses for the two-shore theorem.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator Classical

theorem uniform_count_mismatch_zero (N m : ℕ) (hm : m ≤ N) :
    (uniformFixedColumnLaw N m hm).real {ω | (selectedColumns ω).card ≠ m} = 0 := by
  rw [uniformFixedColumnLaw_real_apply]
  have he : (fixedCountSelectors N m).filter (fun ω => (selectedColumns ω).card ≠ m) = ∅ := by
    ext ω
    simp [fixedCountSelectors]
  simp only [Set.mem_ofPred_eq]
  rw [he]
  simp

theorem uniform_all_column_degree_tail {N m : ℕ} (hN : 0 < N) (hm0 : 0 < m) (hm : m ≤ N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1) (hcol : ∀ j, ∑ i, W i j = d)
    (p : unitInterval) (hmean : (p : ℝ) * (N : ℝ) = (m : ℝ)) (hD : 0 < (p : ℝ) * d) :
    (uniformFixedColumnLaw N m hm).real
      {ω | ∃ j, sampledDegree W (selectedColumns ω) j ≥ 2 * ((p : ℝ) * d)} ≤
      2 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-((p : ℝ) * d) / 3) := by
  let E : Fin N → Set (Fin N → Bool) :=
    fun j => {ω | selectedDegree (fun i => W i j) ω ≥ 2 * ((p : ℝ) * d)}
  have hEach : ∀ j, (uniformFixedColumnLaw N m hm).real (E j) ≤
      2 * ((N : ℝ) + 1) * Real.exp (-((p : ℝ) * d) / 3) := by
    intro j
    have h := actual_uniform_selected_degree_tail hN hm0 hm (fun i => W i j)
      (fun i => hb i j) p hmean (by simpa only [hcol] using hD)
    simpa only [E, hcol] using h
  have he : {ω | ∃ j, sampledDegree W (selectedColumns ω) j ≥ 2 * ((p : ℝ) * d)} =
      ⋃ j, E j := by
    ext ω
    simp [E, sampledDegree, selectedDegree]
  rw [he]
  calc
    _ ≤ ∑ j, (uniformFixedColumnLaw N m hm).real (E j) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _j : Fin N, (2 * ((N : ℝ) + 1) * Real.exp (-((p : ℝ) * d) / 3)) :=
      sum_le_sum (fun j _ => hEach j)
    _ = _ := by simp; ring

theorem rowSample_transpose_column {N : ℕ} (F : Matrix (Fin N) (Fin N) ℝ) (U : Finset (Fin N)) :
    rowSample F U = (finiteRowColumnSample F.transpose U).transpose := by
  ext i j
  rfl

theorem uniform_row_sample_norm_tail {N m : ℕ} (hN : 0 < N) (hm0 : 0 < m) (hm : m ≤ N)
    (F : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 < d)
    (henergy : ∀ i, rowEnergy F i ≤ d) (p : unitInterval)
    (hmean : (p : ℝ) * (N : ℝ) = (m : ℝ)) (t : ℝ) (ht : 0 < t) :
    (uniformFixedColumnLaw N m hm).real
      {ω | ‖rowSample F (selectedColumns ω)‖ ≥
        Real.sqrt (p : ℝ) * ‖F‖ + Real.sqrt d * Real.sqrt t} ≤
      2 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := by
  have htrans : ∀ U, ‖rowSample F U‖ = ‖finiteRowColumnSample F.transpose U‖ := by
    intro U
    rw [rowSample_transpose_column]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (finiteRowColumnSample F.transpose U)
  have hFnorm : ‖F.transpose‖ = ‖F‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose F
  have henergy' : ∀ j, finiteRowColumnEnergy F.transpose j ≤ Real.sqrt d ^ 2 := by
    intro j
    rw [Real.sq_sqrt hd.le]
    simpa only [finiteRowColumnEnergy, rowEnergy, Matrix.transpose_apply] using henergy j
  have htail := actual_positive_fixed_column_sample_norm_tail
    (by simpa only [Fintype.card_fin] using hN) hN hm0 hm F.transpose p hmean
    (Real.sqrt d) (Real.sqrt_pos.mpr hd) henergy' t ht
  simpa only [← htrans, hFnorm, Fintype.card_fin] using htail

#print axioms uniform_count_mismatch_zero
#print axioms uniform_all_column_degree_tail
#print axioms uniform_row_sample_norm_tail
#check @uniform_row_sample_norm_tail
end OpenMathReview.Sampling
