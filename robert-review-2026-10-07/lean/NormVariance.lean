/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import MatrixSampling

/-! # Real operator-norm and actual column-Gram interfaces

The real Rayleigh proof avoids applying a complex CStarAlgebra instance to
real matrices. These interfaces are deterministic ingredients, not an
assumed concentration or spectral-gap conclusion.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

theorem real_opNorm_mono_of_quadratic_forms
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) (hA : A.IsSymmetric)
    (hpos : ∀ x, 0 ≤ inner ℝ (A x) x)
    (hAB : ∀ x, inner ℝ (A x) x ≤ inner ℝ (B x) x) :
    ‖A‖ ≤ ‖B‖ := by
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro x
  have hqpos : 0 ≤ A.rayleighQuotient x := by
    change 0 ≤ inner ℝ (A x) x / ‖x‖ ^ 2
    exact div_nonneg (hpos x) (sq_nonneg _)
  have hqle : A.rayleighQuotient x ≤ B.rayleighQuotient x := by
    change inner ℝ (A x) x / ‖x‖ ^ 2 ≤ inner ℝ (B x) x / ‖x‖ ^ 2
    exact div_le_div_of_nonneg_right (hAB x) (sq_nonneg _)
  rw [abs_of_nonneg hqpos]
  exact hqle.trans ((le_abs_self _).trans (B.rayleighQuotient_le_norm x))

theorem columnGram_norm {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    ‖columnGram F j‖ = columnEnergy F j := by
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i => F i j)
  have hm : columnGram F j =
      Matrix.toEuclideanLin.symm (InnerProductSpace.rankOne ℝ v v) := by
    rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
    ext i k
    simp [columnGram, Matrix.vecMulVec_apply, v]
  rw [hm, Matrix.l2_opNorm_def, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change ‖InnerProductSpace.rankOne ℝ v v‖ = columnEnergy F j
  rw [InnerProductSpace.norm_rankOne]
  rw [← pow_two, EuclideanSpace.norm_sq_eq]
  simp [v, columnEnergy, Real.norm_eq_abs, sq_abs]

theorem columnGram_norm_le {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s)
    (c : ℝ) (hcol : columnEnergy F j ≤ c ^ 2) :
    ‖columnGram F j‖ ≤ c ^ 2 := by
  rwa [columnGram_norm]

theorem columnGram_square_norm {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    ‖(columnGram F j) ^ 2‖ = (columnEnergy F j) ^ 2 := by
  rw [columnGram_sq, norm_smul, columnGram_norm]
  have hpos : 0 ≤ columnEnergy F j := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hpos, pow_two]

#print axioms real_opNorm_mono_of_quadratic_forms
#print axioms columnGram_norm
#print axioms columnGram_norm_le
#print axioms columnGram_square_norm
end OpenMathReview.Sampling
