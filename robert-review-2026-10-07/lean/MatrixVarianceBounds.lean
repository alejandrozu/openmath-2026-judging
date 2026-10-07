/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import BernoulliColumnSample

/-! # Derived real matrix variance bounds for actual Bernoulli sampling

The variance comparison is obtained from positive-semidefinite column Gram
matrices and their actual energies. No variance or concentration conclusion
is supplied as a premise.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

theorem columnGram_posSemidef {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    (columnGram F j).PosSemidef := by
  have he : columnGram F j =
      Matrix.vecMulVec (fun i => F i j) (star (fun i => F i j)) := by
    ext i k
    simp [columnGram, Matrix.vecMulVec_apply]
  rw [he]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem real_matrix_quad_nonneg {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosSemidef) (x : EuclideanSpace ℝ (Fin r)) :
    0 ≤ inner ℝ (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ) A x) x := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  have hx := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2
    (fun i => x i)
  simpa using hx

theorem real_matrix_psd_norm_mono {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) : ‖A‖ ≤ ‖B‖ := by
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def]
  have hs : (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ) A).IsSymmetric := by
    change (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ) A :
      EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r)).IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  apply real_opNorm_mono_of_quadratic_forms _ _ hs (real_matrix_quad_nonneg A hA)
  intro x
  have hh := real_matrix_quad_nonneg (B - A) hBA x
  rw [map_sub] at hh
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hh
  linarith

theorem positive_weighted_columnGram {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (a : Fin s → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (∑ j, a j • columnGram F j).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun j _ => ((columnGram_posSemidef F j).smul (ha j)).nonneg)

theorem real_gram_norm {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) :
    ‖F * F.transpose‖ = ‖F‖ ^ 2 := by
  have ht : ‖F.transpose‖ = ‖F‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose F
  calc
    ‖F * F.transpose‖ = ‖F.transpose.conjTranspose * F.transpose‖ := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    _ = ‖F.transpose‖ * ‖F.transpose‖ := Matrix.l2_opNorm_conjTranspose_mul_self F.transpose
    _ = ‖F‖ ^ 2 := by rw [ht, pow_two]

theorem weighted_columnGram_norm_le {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (a : Fin s → ℝ) (b : ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j ≤ b) (hb : 0 ≤ b) :
    ‖∑ j, a j • columnGram F j‖ ≤ b * ‖F‖ ^ 2 := by
  have hd : (b • (∑ j, columnGram F j) - ∑ j, a j • columnGram F j).PosSemidef := by
    have he : b • (∑ j, columnGram F j) - ∑ j, a j • columnGram F j =
        ∑ j, (b - a j) • columnGram F j := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      simp only [sub_smul]
    rw [he]
    exact positive_weighted_columnGram F (fun j => b - a j)
      (fun j => sub_nonneg.mpr (hab j))
  calc
    ‖∑ j, a j • columnGram F j‖ ≤ ‖b • ∑ j, columnGram F j‖ :=
      real_matrix_psd_norm_mono _ _ (positive_weighted_columnGram F a ha) hd
    _ = b * ‖F‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb,
        ← gram_eq_sum_columnGram, real_gram_norm]

theorem bernoulli_variance_proxy_le {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (c : ℝ) (hcol : ∀ j, columnEnergy F j ≤ c ^ 2) :
    RMT.matrixBernsteinVarianceProxy (bernoulliColumnLaw s p) (gramSummand F p) ≤
      (p : ℝ) * c ^ 2 * ‖F‖ ^ 2 := by
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hp1 : (p : ℝ) ≤ 1 := p.property.2
  have he0 : ∀ j, 0 ≤ columnEnergy F j := fun j =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha : ∀ j, 0 ≤ ((p : ℝ) * (1 - p)) * columnEnergy F j := fun j =>
    mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) (he0 j)
  have hab : ∀ j, ((p : ℝ) * (1 - p)) * columnEnergy F j ≤ (p : ℝ) * c ^ 2 := by
    intro j
    calc
      ((p : ℝ) * (1 - p)) * columnEnergy F j =
          (p : ℝ) * ((1 - p) * columnEnergy F j) := by ring
      _ ≤ (p : ℝ) * columnEnergy F j := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (he0 j) (sub_le_self 1 hp0)) hp0
      _ ≤ (p : ℝ) * c ^ 2 := mul_le_mul_of_nonneg_left (hcol j) hp0
  unfold RMT.matrixBernsteinVarianceProxy
  rw [bernoulli_gram_variance_matrix, Finset.smul_sum]
  simp only [smul_smul]
  exact weighted_columnGram_norm_le F
    (fun j => ((p : ℝ) * (1 - p)) * columnEnergy F j) ((p : ℝ) * c ^ 2) ha hab
    (mul_nonneg hp0 (sq_nonneg c))

#print axioms columnGram_posSemidef
#print axioms real_matrix_psd_norm_mono
#print axioms real_gram_norm
#print axioms weighted_columnGram_norm_le
#print axioms bernoulli_variance_proxy_le
#check @bernoulli_variance_proxy_le
end OpenMathReview.Sampling
