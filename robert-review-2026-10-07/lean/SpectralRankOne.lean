/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

The lower-bound proof below is adapted from the pinned SLT MatrixInfra/EYM.lean
commit d0f506f0a695018265dccb33bcb05e2f5ca1c876, lines 232-264.
The sampling interfaces are copyright 2026 Robert Huynh and
Alejandro Zarzuelo Urdiales, under the same Apache 2.0 license.
-/
import NormVariance
import SLT.MatrixInfra.CourantFischer
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # A genuine rank-one obstruction for the second singular value

The rank-one error bound is proved by the dimension-intersection argument.
It is a known Eckart-Young-Mirsky ingredient, not a new concentration premise.
The second singular value uses Mathlib's zero-based index 1.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Module Matrix
open scoped Matrix.Norms.L2Operator

theorem spectral_rank_error_lower
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T B : E →ₗ[ℝ] F) {n k : ℕ} (hn : finrank ℝ E = n) (hk : k < n)
    (hB : finrank ℝ B.range ≤ k) :
    T.singularValues k ≤ ‖(T - B).toContinuousLinearMap‖ := by
  let i : Fin n := ⟨k, hk⟩
  let L : Submodule ℝ E :=
    T.isSymmetric_adjoint_comp_self.leadingEigenSubspace hn (Nat.succ_le_of_lt i.2)
  have hLdim : finrank ℝ L = k + 1 := by
    simpa [L, i] using
      T.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace hn
        (Nat.succ_le_of_lt i.2)
  have hkerdim : finrank ℝ B.ker = n - finrank ℝ B.range := by
    have h := B.finrank_range_add_finrank_ker
    rw [hn] at h
    omega
  have hinter : finrank ℝ E < finrank ℝ L + finrank ℝ B.ker := by
    rw [hn, hLdim, hkerdim]
    omega
  obtain ⟨x, hxL, hxker, hx0⟩ :=
    Submodule.exists_ne_zero_mem_inf_of_finrank_lt_add_finrank L B.ker hinter
  have hsing_le : T.singularValues k ≤ LinearMap.singularQuotient T x := by
    simpa [i] using
      LinearMap.singularValues_le_singularQuotient_of_mem_gram_leadingEigenSubspace T hn i
        (by simpa [L] using hxL) hx0
  have hquot_le : LinearMap.singularQuotient T x ≤ ‖(T - B).toContinuousLinearMap‖ := by
    unfold LinearMap.singularQuotient
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hTx : T x = (T - B) x := by
      simp [LinearMap.sub_apply, LinearMap.mem_ker.mp hxker]
    rw [hTx]
    exact (div_le_iff₀ hxnorm).mpr ((T - B).toContinuousLinearMap.le_opNorm x)
  exact hsing_le.trans hquot_le

def secondSingularValue {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (F : Matrix I J ℝ) : ℝ :=
  (Matrix.toEuclideanLin F).singularValues 1

set_option backward.isDefEq.respectTransparency false in
theorem secondSingularValue_rank_one_perturbation {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (F R : Matrix I J ℝ) (hJ : 1 < Fintype.card J) (hR : R.rank ≤ 1) :
    secondSingularValue F ≤ ‖F - R‖ := by
  have hreq : R.rank = finrank ℝ (LinearMap.range (Matrix.toEuclideanLin R)) := by
    simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      Matrix.rank_eq_finrank_range_toLin R
        (EuclideanSpace.basisFun I ℝ).toBasis (EuclideanSpace.basisFun J ℝ).toBasis
  have hlinrank : finrank ℝ (LinearMap.range (Matrix.toEuclideanLin R)) ≤ 1 := by
    rw [← hreq]
    exact hR
  have h := spectral_rank_error_lower (Matrix.toEuclideanLin F) (Matrix.toEuclideanLin R)
    finrank_euclideanSpace hJ hlinrank
  simpa only [secondSingularValue, Matrix.l2_opNorm_def, LinearEquiv.trans_apply, map_sub] using h

theorem constantMatrix_rank_le_one {I J : Type*}
    [Fintype I] [Fintype J] (a : ℝ) :
    (Matrix.of (fun _ : I => fun _ : J => a)).rank ≤ 1 := by
  have he : Matrix.of (fun _ : I => fun _ : J => a) =
      Matrix.vecMulVec (fun _ : I => a) (fun _ : J => (1 : ℝ)) := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

theorem secondSingularValue_constant_perturbation {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (F : Matrix I J ℝ) (a : ℝ) (hJ : 1 < Fintype.card J) :
    secondSingularValue F ≤ ‖F - Matrix.of (fun _ : I => fun _ : J => a)‖ :=
  secondSingularValue_rank_one_perturbation F _ hJ (constantMatrix_rank_le_one a)

theorem secondSingularValue_constant_error_all {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (F : Matrix I J ℝ) (a : ℝ) :
    secondSingularValue F ≤ ‖F - Matrix.of (fun _ : I => fun _ : J => a)‖ := by
  by_cases hJ : 1 < Fintype.card J
  · exact secondSingularValue_constant_perturbation F a hJ
  · have hdim : finrank ℝ (EuclideanSpace ℝ J) ≤ 1 := by
      rw [finrank_euclideanSpace]
      omega
    have hz := (Matrix.toEuclideanLin F).singularValues_of_finrank_le hdim
    unfold secondSingularValue
    rw [hz]
    exact norm_nonneg _

#print axioms spectral_rank_error_lower
#print axioms secondSingularValue_rank_one_perturbation
#print axioms secondSingularValue_constant_perturbation
#check @secondSingularValue_constant_perturbation
end OpenMathReview.Sampling
