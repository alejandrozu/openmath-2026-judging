/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import TwoShoreNorm
import RegularCentering
import SamplingNumerics

/-! # Independent uniform two-shore spectral subsampling (B2.2)

This statement uses the genuine second singular value and actual submatrix.
All concentration, variance, conditioning and centering conclusions are
proved in the imported modules. The density condition is the exact original
32(a+4)delta^(-2)log(2N) condition, multiplied by positive delta^2.
This theorem does not assert Hamiltonicity or resolve Erdos585.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator Classical

instance (N m : ℕ) (hm : m ≤ N) : IsProbabilityMeasure (twoShoreLaw N m hm) := by
  unfold twoShoreLaw
  infer_instance

theorem independent_uniform_bipartite_spectral_sampling {N m : ℕ}
    (hN : 1 < N) (hm0 : 0 < m) (hm : m ≤ N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 < d)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1)
    (hrow : ∀ i, ∑ j, W i j = d) (hcol : ∀ j, ∑ i, W i j = d)
    (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgap : secondSingularValue W ≤ (1 - δ) * d)
    (p : unitInterval) (hmean : (p : ℝ) * (N : ℝ) = (m : ℝ))
    (hsize : 32 * (a + 4) * Real.log (2 * (N : ℝ)) ≤ δ ^ 2 * ((p : ℝ) * d)) :
    (twoShoreLaw N m hm).real
      {ω | secondSingularValue (sampled W (selectedColumns ω.1) (selectedColumns ω.2)) >
        (1 - δ / 2) * ((p : ℝ) * d)} ≤ (2 * (N : ℝ)) ^ (-a) := by
  let t : ℝ := (a + 4) * Real.log (2 * (N : ℝ))
  let D : ℝ := (p : ℝ) * d
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (2 * (N : ℝ)) := Real.log_pos (by nlinarith)
  have ht : 0 < t := mul_pos (by linarith) hlog
  have hsize' : 32 * t ≤ δ ^ 2 * D := by
    dsimp [t, D]
    nlinarith only [hsize]
  have hD : 0 < D := by
    by_contra hD
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) (le_of_not_gt hD)
    linarith
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hDbound := mul_le_mul_of_nonneg_right hδsq hD.le
  have hDt : t ≤ D / 3 := by nlinarith
  have hstrict : secondSingularValue W < d := by nlinarith [mul_pos hδ hd]
  have hcenter := regular_centered_norm_eq_second hN W d hd hrow hcol hstrict
  have hnoise := two_shore_noise_le_half_loss hδ hD ht hsize'
  have hthreshold : (p : ℝ) * ‖centered W d‖ +
      (1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t ≤ (1 - δ / 2) * D := by
    rw [hcenter]
    have hscaled := mul_le_mul_of_nonneg_left hgap p.property.1
    dsimp [D] at hnoise ⊢
    nlinarith
  have hrank : ∀ ω : (Fin N → Bool) × (Fin N → Bool),
      secondSingularValue (sampled W (selectedColumns ω.1) (selectedColumns ω.2)) ≤
        ‖sampled (centered W d) (selectedColumns ω.1) (selectedColumns ω.2)‖ := by
    intro ω
    have h := secondSingularValue_constant_error_all
      (sampled W (selectedColumns ω.1) (selectedColumns ω.2)) (d / N)
    have he : sampled W (selectedColumns ω.1) (selectedColumns ω.2) -
        Matrix.of (fun _ _ => d / N) =
        sampled (centered W d) (selectedColumns ω.1) (selectedColumns ω.2) := by
      ext i j
      rfl
    rw [he] at h
    exact h
  have hsub : {ω : (Fin N → Bool) × (Fin N → Bool) |
      secondSingularValue (sampled W (selectedColumns ω.1) (selectedColumns ω.2)) >
      (1 - δ / 2) * D} ⊆
      {ω | ‖sampled (centered W d) (selectedColumns ω.1) (selectedColumns ω.2)‖ >
        (p : ℝ) * ‖centered W d‖ + (1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t} := by
    intro ω hω
    change (1 - δ / 2) * D <
      secondSingularValue (sampled W (selectedColumns ω.1) (selectedColumns ω.2)) at hω
    change _ < ‖sampled (centered W d) (selectedColumns ω.1) (selectedColumns ω.2)‖
    exact hthreshold.trans_lt (hω.trans_le (hrank ω))
  have htail := actual_two_shore_centered_norm_tail (by omega : 0 < N) hm0 hm
    W d hd hb hrow hcol p hmean hD t ht hDt
  calc
    _ ≤ (twoShoreLaw N m hm).real
        {ω | ‖sampled (centered W d) (selectedColumns ω.1) (selectedColumns ω.2)‖ >
          (p : ℝ) * ‖centered W d‖ + (1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t} :=
      measureReal_mono hsub
    _ ≤ 6 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := htail
    _ ≤ (2 * (N : ℝ)) ^ (-a) := two_shore_probability_budget N (by omega) a

#print axioms independent_uniform_bipartite_spectral_sampling
#check @independent_uniform_bipartite_spectral_sampling
end OpenMathReview.Sampling
