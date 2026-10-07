/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import SpectralCentering

/-! # Genuine regular-matrix centering and its second singular value

Row and column sums give the uniform Gram eigenvector equation. The strict
second-singular-value gap identifies that direction as the top direction;
the centred norm is then proved, not assumed.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Module Matrix InnerProductSpace Finset
open scoped BigOperators Matrix.Norms.L2Operator

def onesVector (N : ℕ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun _ => 1)

theorem onesVector_norm_sq (N : ℕ) : ‖onesVector N‖ ^ 2 = (N : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [onesVector]

theorem onesVector_inner {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (onesVector N) x = ∑ j, x j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [onesVector, dotProduct]

theorem regular_uniform_eigenvector {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hrow : ∀ i, ∑ j, W i j = d) :
    Matrix.toEuclideanLin W (onesVector N) = d • onesVector N := by
  ext i
  change (∑ j, W i j * 1) = d * 1
  simp only [mul_one, hrow]

theorem regular_uniform_gram_eigenvector {N : ℕ}
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hrow : ∀ i, ∑ j, W i j = d) (hcol : ∀ j, ∑ i, W i j = d) :
    ((Matrix.toEuclideanLin W).adjoint.comp (Matrix.toEuclideanLin W)) (onesVector N) =
      d ^ 2 • onesVector N := by
  have ht : (Matrix.toEuclideanLin W).adjoint = Matrix.toEuclideanLin W.transpose := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint W).symm
  rw [LinearMap.comp_apply, regular_uniform_eigenvector W d hrow, map_smul, ht,
    regular_uniform_eigenvector W.transpose d (by simpa only [Matrix.transpose_apply] using hcol),
    smul_smul, pow_two]

theorem centering_operator_eq_projection {N : ℕ}
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hrow : ∀ i, ∑ j, W i j = d) :
    (Matrix.toEuclideanLin (centered W d)).toContinuousLinearMap =
      (Matrix.toEuclideanLin W).toContinuousLinearMap -
        (Matrix.toEuclideanLin W).toContinuousLinearMap.comp (ℝ ∙ onesVector N).starProjection := by
  ext x i
  have hP : (ℝ ∙ onesVector N).starProjection x =
      ((∑ j, x j) / (N : ℝ)) • onesVector N := by
    rw [Submodule.starProjection_singleton, onesVector_inner, onesVector_norm_sq]
    simp
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', hP, map_smul,
    regular_uniform_eigenvector W d hrow, smul_smul]
  change (∑ j, (W i j - d / N) * x j) =
    (∑ j, W i j * x j) - (((∑ j, x j) / (N : ℝ)) * d) * 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem regular_centered_norm_le_second {N : ℕ} (hN : 1 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 < d)
    (hrow : ∀ i, ∑ j, W i j = d) (hcol : ∀ j, ∑ i, W i j = d)
    (hgap : secondSingularValue W < d) :
    ‖centered W d‖ ≤ secondSingularValue W := by
  have hu0 : onesVector N ≠ 0 := by
    intro he
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin N) => x ⟨0, by omega⟩) he
    simp [onesVector] at hi
  have h := spectral_centered_operator_bound (Matrix.toEuclideanLin W)
    finrank_euclideanSpace_fin hN (onesVector N) hu0 d hd
    (regular_uniform_gram_eigenvector W d hrow hcol) hgap
  rw [← centering_operator_eq_projection W d hrow] at h
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply, secondSingularValue] using h

theorem regular_centered_norm_eq_second {N : ℕ} (hN : 1 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 < d)
    (hrow : ∀ i, ∑ j, W i j = d) (hcol : ∀ j, ∑ i, W i j = d)
    (hgap : secondSingularValue W < d) :
    ‖centered W d‖ = secondSingularValue W := by
  apply le_antisymm (regular_centered_norm_le_second hN W d hd hrow hcol hgap)
  have h := secondSingularValue_constant_perturbation W (d / N)
    (by simpa only [Fintype.card_fin] using hN)
  have he : W - Matrix.of (fun _ : Fin N => fun _ : Fin N => d / N) = centered W d := by
    ext i j
    rfl
  rw [he] at h
  exact h

#print axioms regular_uniform_gram_eigenvector
#print axioms centering_operator_eq_projection
#print axioms regular_centered_norm_eq_second
#check @regular_centered_norm_eq_second
end OpenMathReview.Sampling
