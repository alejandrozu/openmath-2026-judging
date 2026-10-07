/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

The trailing-subspace membership proof is adapted from SLT MatrixInfra/EYM.lean
commit d0f506f0a695018265dccb33bcb05e2f5ca1c876, lines 50-75.
The remaining interfaces are copyright 2026 Robert Huynh and
Alejandro Zarzuelo Urdiales, under the same Apache 2.0 license.
-/
import SpectralRankOne

/-! # Centering at a genuine top Gram eigenvector

The top direction is identified from a proved Gram-eigenvector equation and
a strict second-singular-value gap. No centred operator-norm conclusion is
supplied as a hypothesis.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Module InnerProductSpace
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem mem_gram_trailing_of_repr_zero (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (i : Fin n) {x : E}
    (hzero : ∀ j : Fin n, j.val < i.val →
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).repr x j = 0) :
    x ∈ T.isSymmetric_adjoint_comp_self.trailingEigenSubspace hn i := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  have hsupp : ↑(b.toBasis.repr x).support ⊆ {j : Fin n | i.val ≤ j.val} := by
    intro j hj
    by_contra hjlt
    have hzero' : b.toBasis.repr x j = 0 := by
      rw [b.coe_toBasis_repr_apply]
      exact hzero j (Nat.lt_of_not_ge hjlt)
    exact (Finsupp.mem_support_iff.mp hj) hzero'
  have hxspan : x ∈ Submodule.span ℝ (b '' {j : Fin n | i.val ≤ j.val}) :=
    (b.toBasis.mem_span_image (s := {j : Fin n | i.val ≤ j.val})).2 hsupp
  unfold LinearMap.IsSymmetric.trailingEigenSubspace
  refine (Submodule.span_mono ?_) hxspan
  rintro y ⟨j, hj, rfl⟩
  have hjrange : j ∈ Set.range (Fin.natAdd_castLEEmb (Nat.sub_le n i.val)) := by
    rw [Fin.range_natAdd_castLEEmb]
    change n - (n - i.val) ≤ j.val
    rw [Nat.sub_sub_self (Nat.le_of_lt i.2)]
    exact hj
  rcases hjrange with ⟨l, rfl⟩
  exact ⟨l, rfl⟩

theorem gram_top_eigenvector_span (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (hn2 : 1 < n) (u : E) (d : ℝ)
    (hd : 0 < d) (hu : (T.adjoint.comp T) u = d ^ 2 • u)
    (hgap : T.singularValues 1 < d) :
    u = ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).repr u
      ⟨0, Nat.zero_lt_of_lt hn2⟩) •
        T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn ⟨0, Nat.zero_lt_of_lt hn2⟩ := by
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis hn
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt hn2⟩
  let i1 : Fin n := ⟨1, hn2⟩
  have hEigOne : hS.eigenvalues hn i1 = T.singularValues 1 ^ 2 := by
    have h := T.singularValues_fin hn i1
    have hp := T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i1
    have hs := Real.sq_sqrt hp
    simpa [i1, hS, h] using hs.symm
  have hstrict : T.singularValues 1 ^ 2 < d ^ 2 := by
    nlinarith [T.singularValues_nonneg 1]
  have hzero : ∀ j : Fin n, j ≠ i0 → b.repr u j = 0 := by
    intro j hj
    have hge : i1 ≤ j := by
      change 1 ≤ j.val
      have hj0 : j.val ≠ 0 := by
        intro hval
        apply hj
        exact Fin.ext hval
      omega
    have hEigBase : hS.eigenvalues hn i1 < d ^ 2 := by rw [hEigOne]; exact hstrict
    have hEigLt : hS.eigenvalues hn j < d ^ 2 :=
      ((hS.eigenvalues_antitone hn) hge).trans_lt hEigBase
    have he := hS.eigenvectorBasis_apply_self_apply hn u j
    rw [hu] at he
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at he
    change d ^ 2 * b.repr u j = hS.eigenvalues hn j * b.repr u j at he
    exact (mul_eq_mul_right_iff.mp he).resolve_left (ne_of_gt hEigLt)
  calc
    u = ∑ j, b.repr u j • b j := (b.sum_repr u).symm
    _ = _ := Finset.sum_eq_single i0 (fun j _ hj => by rw [hzero j hj, zero_smul])
      (by simp)

theorem singular_norm_on_top_orthogonal (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (hn2 : 1 < n) (u : E) (hu0 : u ≠ 0) (d : ℝ)
    (hd : 0 < d) (hu : (T.adjoint.comp T) u = d ^ 2 • u)
    (hgap : T.singularValues 1 < d) (x : E) (hx : x ∈ (ℝ ∙ u)ᗮ) :
    ‖T x‖ ≤ T.singularValues 1 * ‖x‖ := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt hn2⟩
  let i1 : Fin n := ⟨1, hn2⟩
  have huvec : u = (b.repr u i0) • b i0 := gram_top_eigenvector_span T hn hn2 u d hd hu hgap
  have hc : b.repr u i0 ≠ 0 := by
    intro hc
    apply hu0
    rw [huvec, hc, zero_smul]
  have hinner : inner ℝ (b i0) x = 0 := by
    have hux := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hx
    rw [huvec, real_inner_smul_left] at hux
    exact (mul_eq_zero.mp hux).resolve_left hc
  have hxtrailing : x ∈ T.isSymmetric_adjoint_comp_self.trailingEigenSubspace hn i1 := by
    apply mem_gram_trailing_of_repr_zero T hn i1
    intro j hj
    have hj0 : j = i0 := by apply Fin.ext; change j.val = 0; change j.val < 1 at hj; omega
    rw [hj0, OrthonormalBasis.repr_apply_apply]
    exact hinner
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hquot := LinearMap.singularQuotient_le_singularValues_of_mem_gram_trailingEigenSubspace
      T hn i1 hxtrailing hx0
    unfold LinearMap.singularQuotient at hquot
    exact (div_le_iff₀ (norm_pos_iff.mpr hx0)).mp hquot

theorem spectral_centered_operator_bound (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (hn2 : 1 < n) (u : E) (hu0 : u ≠ 0) (d : ℝ)
    (hd : 0 < d) (hu : (T.adjoint.comp T) u = d ^ 2 • u)
    (hgap : T.singularValues 1 < d) :
    ‖T.toContinuousLinearMap - T.toContinuousLinearMap.comp (ℝ ∙ u).starProjection‖ ≤
      T.singularValues 1 := by
  let P : Submodule ℝ E := ℝ ∙ u
  apply ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg 1)
  intro x
  let y : E := Pᗮ.starProjection x
  have hy : y ∈ Pᗮ := Pᗮ.starProjection_apply_mem x
  have he : (T.toContinuousLinearMap - T.toContinuousLinearMap.comp P.starProjection) x = T y := by
    dsimp [y]
    rw [Submodule.starProjection_orthogonal_val]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    rfl
  rw [he]
  exact (singular_norm_on_top_orthogonal T hn hn2 u hu0 d hd hu hgap y hy).trans
    (mul_le_mul_of_nonneg_left (Pᗮ.norm_starProjection_apply_le x) (T.singularValues_nonneg 1))

#print axioms gram_top_eigenvector_span
#print axioms singular_norm_on_top_orthogonal
#print axioms spectral_centered_operator_bound
#check @spectral_centered_operator_bound
end OpenMathReview.Sampling
