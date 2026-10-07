/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import MatrixVarianceBounds

/-! # Actual selected binary degree tail from the proved scalar Bernstein case

The scalar random variable counts selected neighbours. It is represented by
the one-dimensional actual compressed Gram, whose variance is derived.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

def scalarRow {s : ℕ} (x : Fin s → ℝ) : Matrix (Fin 1) (Fin s) ℝ :=
  Matrix.of (fun _ j => x j)

def selectedDegree {s : ℕ} (x : Fin s → ℝ) (ω : Fin s → Bool) : ℝ :=
  ∑ j ∈ selectedColumns ω, x j

theorem scalar_matrix_norm (a : ℝ) :
    ‖(Matrix.of (fun _ _ => a) : Matrix (Fin 1) (Fin 1) ℝ)‖ = |a| := by
  have he : (Matrix.of (fun _ _ => a) : Matrix (Fin 1) (Fin 1) ℝ) =
      a • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hi, hj]
  rw [he, norm_smul, norm_one, mul_one, Real.norm_eq_abs]

theorem scalar_binary_Gram {s : ℕ} (x : Fin s → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (j : Fin s) :
    columnGram (scalarRow x) j = Matrix.of (fun _ _ => x j) := by
  ext i k
  rcases hx j with h | h <;> simp [columnGram, scalarRow, h]

theorem scalar_binary_energy {s : ℕ} (x : Fin s → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (j : Fin s) :
    columnEnergy (scalarRow x) j = x j := by
  unfold columnEnergy
  have he : (scalarRow x 0 j) ^ 2 = x j := by
    rcases hx j with h | h <;> simp [scalarRow, h]
  simpa using he

theorem selectedDegree_Gram {s : ℕ} (x : Fin s → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (ω : Fin s → Bool) :
    actualSelectedGram (scalarRow x) ω = Matrix.of (fun _ _ => selectedDegree x ω) := by
  unfold actualSelectedGram
  rw [columnSample_gram_eq_sum]
  ext i k
  simp only [Matrix.sum_apply, scalar_binary_Gram x hx, Matrix.of_apply, selectedDegree]

theorem selectedDegree_variance {s : ℕ} (x : Fin s → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (p : unitInterval) :
    RMT.matrixBernsteinVarianceProxy (bernoulliColumnLaw s p) (gramSummand (scalarRow x) p) =
      (p : ℝ) * (1 - p) * ∑ j, x j := by
  have hx0 : ∀ j, 0 ≤ x j := by
    intro j
    rcases hx j with h | h <;> simp [h]
  have he : ∑ j, columnEnergy (scalarRow x) j • columnGram (scalarRow x) j =
      Matrix.of (fun _ _ => ∑ j, x j) := by
    ext i k
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      scalar_binary_energy x hx, scalar_binary_Gram x hx, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro j _
    rcases hx j with h | h <;> simp [h]
  unfold RMT.matrixBernsteinVarianceProxy
  rw [bernoulli_gram_variance_matrix, he]
  have hs : ((p : ℝ) * (1 - p)) •
      (Matrix.of (fun _ _ => ∑ j, x j) : Matrix (Fin 1) (Fin 1) ℝ) =
      Matrix.of (fun _ _ => ((p : ℝ) * (1 - p)) * ∑ j, x j) := by
    ext i j
    simp
  rw [hs, scalar_matrix_norm, abs_of_nonneg]
  exact mul_nonneg (mul_nonneg p.property.1 (sub_nonneg.mpr p.property.2))
    (sum_nonneg (fun j _ => hx0 j))

theorem Bernstein_scalar_degree_rate {D v : ℝ} (hD : 0 < D) (hv : 0 ≤ v) (hvb : v ≤ D) :
    D / 3 ≤ (D ^ 2 / 2) / (v + D / 3) := by
  have hden : 0 < v + D / 3 := by positivity
  apply (le_div_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left hvb hD.le
  nlinarith [sq_nonneg D]

theorem actual_selected_degree_tail {s : ℕ} (x : Fin s → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (p : unitInterval)
    (hD : 0 < (p : ℝ) * ∑ j, x j) :
    ((bernoulliColumnLaw s p)
      {ω | selectedDegree x ω ≥ 2 * ((p : ℝ) * ∑ j, x j)}).toReal ≤
      2 * Real.exp (-((p : ℝ) * ∑ j, x j) / 3) := by
  let D : ℝ := (p : ℝ) * ∑ j, x j
  have hx0 : ∀ j, 0 ≤ x j := by
    intro j
    rcases hx j with h | h <;> simp [h]
  have hcol : ∀ j, columnEnergy (scalarRow x) j ≤ (1 : ℝ) ^ 2 := by
    intro j
    rw [scalar_binary_energy x hx]
    rcases hx j with h | h <;> simp [h]
  have hwhole : scalarRow x * (scalarRow x).transpose = Matrix.of (fun _ _ => ∑ j, x j) := by
    rw [gram_eq_sum_columnGram]
    ext i k
    simp only [Matrix.sum_apply, scalar_binary_Gram x hx, Matrix.of_apply]
  have hnorm : ∀ ω,
      ‖actualSelectedGram (scalarRow x) ω - (p : ℝ) •
        (scalarRow x * (scalarRow x).transpose)‖ = |selectedDegree x ω - D| := by
    intro ω
    rw [selectedDegree_Gram x hx, hwhole]
    have he : Matrix.of (fun _ _ => selectedDegree x ω) -
        (p : ℝ) • Matrix.of (fun _ _ => ∑ j, x j) =
        (Matrix.of (fun _ _ => selectedDegree x ω - D) : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i k
      simp [D]
    rw [he, scalar_matrix_norm]
  have hsub : {ω | selectedDegree x ω ≥ 2 * D} ⊆
      {ω | ‖actualSelectedGram (scalarRow x) ω - (p : ℝ) •
        (scalarRow x * (scalarRow x).transpose)‖ ≥ D} := by
    intro ω hω
    change D ≤ ‖actualSelectedGram (scalarRow x) ω - (p : ℝ) •
      (scalarRow x * (scalarRow x).transpose)‖
    change 2 * D ≤ selectedDegree x ω at hω
    rw [hnorm]
    exact (by linarith : D ≤ selectedDegree x ω - D).trans (le_abs_self _)
  have ht := bernoulli_gram_deviation (by omega : 0 < 1) (scalarRow x) p 1 hcol D hD.le
  have hv := RMT.matrixBernsteinVarianceProxy_nonneg
    (bernoulliColumnLaw s p) (gramSummand (scalarRow x) p)
  have hvb : RMT.matrixBernsteinVarianceProxy
      (bernoulliColumnLaw s p) (gramSummand (scalarRow x) p) ≤ D := by
    rw [selectedDegree_variance x hx p]
    have hs0 : 0 ≤ ∑ j, x j := sum_nonneg (fun j _ => hx0 j)
    dsimp [D]
    nlinarith [mul_nonneg p.property.1 hs0,
      mul_nonneg (sq_nonneg (p : ℝ)) hs0]
  calc
    _ ≤ ((bernoulliColumnLaw s p)
        {ω | ‖actualSelectedGram (scalarRow x) ω - (p : ℝ) •
          (scalarRow x * (scalarRow x).transpose)‖ ≥ D}).toReal := measureReal_mono hsub
    _ ≤ RMT.matrixBernsteinTailBound 1
        (RMT.matrixBernsteinVarianceProxy (bernoulliColumnLaw s p) (gramSummand (scalarRow x) p))
        1 D := by simpa only [actualSelectedGram_centered_eq, one_pow] using ht
    _ ≤ 2 * Real.exp (-D / 3) := by
      unfold RMT.matrixBernsteinTailBound
      simp only [Nat.cast_one, one_mul, mul_one]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hr := Bernstein_scalar_degree_rate hD hv hvb
      simpa only [neg_div] using neg_le_neg hr

#print axioms selectedDegree_variance
#print axioms actual_selected_degree_tail
#check @actual_selected_degree_tail
end OpenMathReview.Sampling
