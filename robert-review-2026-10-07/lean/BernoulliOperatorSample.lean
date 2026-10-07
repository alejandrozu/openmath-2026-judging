/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import MatrixVarianceBounds

/-! # Derived operator-norm tail for actual independently selected columns

This is a Bernoulli theorem, not a fixed-size uniform-subset theorem. The variance
bound and Gram representation are proved by the imported sampling modules.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

def columnSampleExcess (p c M t : ℝ) : ℝ :=
  2 * c * Real.sqrt p * M * Real.sqrt t + c ^ 2 * t

theorem columnSampleExcess_pos {p c M t : ℝ}
    (hp : 0 ≤ p) (hc : 0 < c) (hM : 0 ≤ M) (ht : 0 < t) :
    0 < columnSampleExcess p c M t := by
  unfold columnSampleExcess
  have hfirst : 0 ≤ 2 * c * Real.sqrt p * M * Real.sqrt t :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hM)
      (Real.sqrt_nonneg _)
  have hlast : 0 < c ^ 2 * t := mul_pos (sq_pos_of_pos hc) ht
  linarith

theorem columnSampleExcess_rate {p c M t v : ℝ}
    (hp : 0 ≤ p) (hc : 0 < c) (hM : 0 ≤ M) (ht : 0 < t)
    (hv : 0 ≤ v) (hvb : v ≤ p * c ^ 2 * M ^ 2) :
    t ≤ (columnSampleExcess p c M t ^ 2 / 2) /
      (v + c ^ 2 * columnSampleExcess p c M t / 3) := by
  have hu := columnSampleExcess_pos hp hc hM ht
  have hden : 0 < v + c ^ 2 * columnSampleExcess p c M t / 3 := by
    have : 0 < c ^ 2 * columnSampleExcess p c M t :=
      mul_pos (sq_pos_of_pos hc) hu
    positivity
  apply (le_div_iff₀ hden).mpr
  have hA0 : 0 ≤ c * Real.sqrt p * M * Real.sqrt t := by positivity
  have hA2 : (c * Real.sqrt p * M * Real.sqrt t) ^ 2 = p * c ^ 2 * M ^ 2 * t := by
    simp only [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt ht.le]
    ring
  have hvt := mul_le_mul_of_nonneg_right hvb ht.le
  have hcross : 0 ≤ (c * Real.sqrt p * M * Real.sqrt t) * (c ^ 2 * t) :=
    mul_nonneg hA0 (mul_nonneg (sq_nonneg _) ht.le)
  have hidentity : columnSampleExcess p c M t ^ 2 / 2 -
      t * (v + c ^ 2 * columnSampleExcess p c M t / 3) =
      2 * (p * c ^ 2 * M ^ 2 * t) - v * t +
      (4 / 3 : ℝ) * (c * Real.sqrt p * M * Real.sqrt t) * (c ^ 2 * t) +
      (1 / 6 : ℝ) * (c ^ 2 * t) ^ 2 := by
    unfold columnSampleExcess
    nlinarith [hA2]
  have hmain : 0 ≤ p * c ^ 2 * M ^ 2 * t := by positivity
  linarith [sq_nonneg (c ^ 2 * t)]

theorem matrixBernsteinTailBound_columnSampleExcess {p c M t v : ℝ} (r : ℕ)
    (hp : 0 ≤ p) (hc : 0 < c) (hM : 0 ≤ M) (ht : 0 < t)
    (hv : 0 ≤ v) (hvb : v ≤ p * c ^ 2 * M ^ 2) :
    RMT.matrixBernsteinTailBound r v (c ^ 2) (columnSampleExcess p c M t) ≤
      2 * (r : ℝ) * Real.exp (-t) := by
  unfold RMT.matrixBernsteinTailBound
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (columnSampleExcess_rate hp hc hM ht hv hvb)
  · positivity

theorem columnSample_gram_norm {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (U : Finset (Fin s)) :
    ‖columnSample F U * (columnSample F U).transpose‖ = ‖columnSample F U‖ ^ 2 := by
  have ht : ‖(columnSample F U).transpose‖ = ‖columnSample F U‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (columnSample F U)
  calc
    ‖columnSample F U * (columnSample F U).transpose‖ =
        ‖(columnSample F U).transpose.conjTranspose * (columnSample F U).transpose‖ := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    _ = ‖(columnSample F U).transpose‖ * ‖(columnSample F U).transpose‖ :=
      Matrix.l2_opNorm_conjTranspose_mul_self (columnSample F U).transpose
    _ = ‖columnSample F U‖ ^ 2 := by rw [ht, pow_two]

theorem columnSample_norm_bad_implies_gram_bad {r s : ℕ}
    (F : Matrix (Fin r) (Fin s) ℝ) (p : unitInterval) (c t : ℝ)
    (hc : 0 < c) (ht : 0 < t) (ω : Fin s → Bool)
    (hbad : Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t ≤
      ‖columnSample F (selectedColumns ω)‖) :
    columnSampleExcess p c ‖F‖ t ≤
      ‖actualSelectedGram F ω - (p : ℝ) • (F * F.transpose)‖ := by
  have hn : ‖actualSelectedGram F ω‖ ≤
      ‖actualSelectedGram F ω - (p : ℝ) • (F * F.transpose)‖ +
      ‖(p : ℝ) • (F * F.transpose)‖ := norm_le_norm_sub_add _ _
  have hmean : ‖(p : ℝ) • (F * F.transpose)‖ = (p : ℝ) * ‖F‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.property.1, real_gram_norm]
  have hgram : ‖actualSelectedGram F ω‖ = ‖columnSample F (selectedColumns ω)‖ ^ 2 :=
    columnSample_gram_norm F (selectedColumns ω)
  have hb0 : 0 ≤ Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t := by positivity
  have hbsq := pow_le_pow_left₀ hb0 hbad 2
  have hsquare : (Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t) ^ 2 =
      (p : ℝ) * ‖F‖ ^ 2 + columnSampleExcess p c ‖F‖ t := by
    unfold columnSampleExcess
    simp only [add_sq, mul_pow, Real.sq_sqrt p.property.1, Real.sq_sqrt ht.le]
    ring
  rw [hmean, hgram] at hn
  rw [hsquare] at hbsq
  linarith

theorem actual_column_sample_norm_tail {r s : ℕ} (hr : 0 < r)
    (F : Matrix (Fin r) (Fin s) ℝ) (p : unitInterval)
    (c : ℝ) (hc : 0 < c) (hcol : ∀ j, columnEnergy F j ≤ c ^ 2)
    (t : ℝ) (ht : 0 < t) :
    ((bernoulliColumnLaw s p)
      {ω | ‖columnSample F (selectedColumns ω)‖ ≥
        Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t}).toReal ≤
      2 * (r : ℝ) * Real.exp (-t) := by
  have hsub : {ω | ‖columnSample F (selectedColumns ω)‖ ≥
      Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t} ⊆
      {ω | ‖actualSelectedGram F ω - (p : ℝ) • (F * F.transpose)‖ ≥
        columnSampleExcess p c ‖F‖ t} := by
    intro ω hω
    exact columnSample_norm_bad_implies_gram_bad F p c t hc ht ω hω
  have hv := RMT.matrixBernsteinVarianceProxy_nonneg
    (bernoulliColumnLaw s p) (gramSummand F p)
  have hvb := bernoulli_variance_proxy_le F p c hcol
  have htail := bernoulli_gram_deviation hr F p c hcol
    (columnSampleExcess p c ‖F‖ t)
    (columnSampleExcess_pos p.property.1 hc (norm_nonneg _) ht).le
  calc
    _ ≤ ((bernoulliColumnLaw s p)
        {ω | ‖actualSelectedGram F ω - (p : ℝ) • (F * F.transpose)‖ ≥
          columnSampleExcess p c ‖F‖ t}).toReal := measureReal_mono hsub
    _ ≤ RMT.matrixBernsteinTailBound r
        (RMT.matrixBernsteinVarianceProxy (bernoulliColumnLaw s p) (gramSummand F p))
        (c ^ 2) (columnSampleExcess p c ‖F‖ t) := by
      simpa only [actualSelectedGram_centered_eq] using htail
    _ ≤ 2 * (r : ℝ) * Real.exp (-t) :=
      matrixBernsteinTailBound_columnSampleExcess r p.property.1 hc (norm_nonneg _) ht hv hvb

#print axioms columnSampleExcess_rate
#print axioms matrixBernsteinTailBound_columnSampleExcess
#print axioms columnSample_norm_bad_implies_gram_bad
#print axioms actual_column_sample_norm_tail
#check @actual_column_sample_norm_tail
end OpenMathReview.Sampling
