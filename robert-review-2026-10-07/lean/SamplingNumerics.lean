/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import UniformOperatorSample
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact deterministic noise and probability budgets for two-shore sampling

These inequalities contain no assumed matrix or concentration conclusion.
The constant 32 and the n^(-a) conversion use exact real arithmetic.
-/
noncomputable section
namespace OpenMathReview.Sampling

theorem two_shore_noise_le_half_loss {δ D t : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (ht : 0 < t) (hsize : 32 * t ≤ δ ^ 2 * D) :
    (1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t ≤ δ * D / 2 := by
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have h3le : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith
  have hDsq := Real.sq_sqrt hD.le
  have htsq := Real.sq_sqrt ht.le
  have hprod : 0 ≤ D * t := mul_nonneg hD.le ht.le
  have hleftsq : ((1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t) ^ 2 =
      (4 + 2 * Real.sqrt 3) * D * t := by
    simp only [mul_pow, add_sq, one_pow, one_mul, h3, hDsq, htsq]
    ring
  have hcoef : (4 + 2 * Real.sqrt 3) * (D * t) ≤ 8 * (D * t) :=
    mul_le_mul_of_nonneg_right (by linarith) hprod
  have hscaled := mul_le_mul_of_nonneg_right hsize hD.le
  have hsq : ((1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t) ^ 2 ≤ (δ * D / 2) ^ 2 := by
    rw [hleftsq]
    nlinarith
  have hleft0 : 0 ≤ (1 + Real.sqrt 3) * Real.sqrt D * Real.sqrt t := by positivity
  have hright0 : 0 ≤ δ * D / 2 := by positivity
  exact (sq_le_sq₀ hleft0 hright0).mp hsq

theorem two_shore_probability_budget (N : ℕ) (hN : 1 ≤ N) (a : ℝ) :
    6 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-((a + 4) * Real.log (2 * (N : ℝ)))) ≤
      (2 * (N : ℝ)) ^ (-a) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < 2 * (N : ℝ) := by positivity
  have hn0 : 2 * (N : ℝ) ≠ 0 := ne_of_gt hn
  have hcoeff : 6 * (N : ℝ) * ((N : ℝ) + 1) ≤ (2 * (N : ℝ)) ^ 4 := by
    have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hN4 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((N : ℝ) ^ 2 - 1)]
    nlinarith
  have hexp : Real.exp (-((a + 4) * Real.log (2 * (N : ℝ)))) =
      Real.exp (-a * Real.log (2 * (N : ℝ))) / (2 * (N : ℝ)) ^ 4 := by
    have hfour : Real.exp (4 * Real.log (2 * (N : ℝ))) = (2 * (N : ℝ)) ^ 4 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hn] using
        Real.exp_nat_mul (Real.log (2 * (N : ℝ))) 4
    rw [show -((a + 4) * Real.log (2 * (N : ℝ))) =
        -a * Real.log (2 * (N : ℝ)) - 4 * Real.log (2 * (N : ℝ)) by ring,
      Real.exp_sub, hfour]
  rw [hexp, Real.rpow_def_of_pos hn]
  rw [show Real.log (2 * (N : ℝ)) * (-a) = -a * Real.log (2 * (N : ℝ)) by ring,
    ← mul_div_assoc]
  have hden : 0 < (2 * (N : ℝ)) ^ 4 := pow_pos hn _
  have hepos : 0 ≤ Real.exp (-a * Real.log (2 * (N : ℝ))) := (Real.exp_pos _).le
  apply (div_le_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_right hcoeff hepos
  nlinarith only [hmul]

#print axioms two_shore_noise_le_half_loss
#print axioms two_shore_probability_budget
#check @two_shore_probability_budget
end OpenMathReview.Sampling
