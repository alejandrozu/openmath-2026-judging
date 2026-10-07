/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import BernoulliOperatorSample

/-! # Sampling arbitrary finite row shores without changing the operator norm

The row reindexing is an actual Euclidean linear isometry. This permits a
second column sampling after the first compressed row sample has a subtype
as its row index. No sampled norm bound is assumed.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator Classical

theorem l2_opNorm_row_equiv {I I' J : Type*}
    [Fintype I] [Fintype I'] [Fintype J] [DecidableEq I] [DecidableEq I']
    [DecidableEq J] (F : Matrix I J ℝ) (e : I' ≃ I) :
    ‖F.submatrix e id‖ = ‖F‖ := by
  let T : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ I :=
    (Matrix.toEuclideanLin F).toContinuousLinearMap
  let T' : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ I' :=
    (Matrix.toEuclideanLin (F.submatrix e id)).toContinuousLinearMap
  let L : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I' :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm
  have he : T' = (L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I').comp T := by
    ext x i
    rfl
  have heinv : T = (L.symm : EuclideanSpace ℝ I' →L[ℝ] EuclideanSpace ℝ I).comp T' := by
    rw [he]
    ext x
    simp
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  change ‖T'‖ = ‖T‖
  apply le_antisymm
  · apply T'.opNorm_le_bound (norm_nonneg _)
    intro x
    rw [he]
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
      LinearIsometryEquiv.norm_map] using T.le_opNorm x
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    rw [heinv]
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
      LinearIsometryEquiv.norm_map] using T'.le_opNorm x

def finiteRowColumnSample {I : Type*} [Fintype I] {s : ℕ}
    (F : Matrix I (Fin s) ℝ) (U : Finset (Fin s)) : Matrix I U ℝ :=
  F.submatrix id Subtype.val

def finiteRowColumnEnergy {I : Type*} [Fintype I] {s : ℕ}
    (F : Matrix I (Fin s) ℝ) (j : Fin s) : ℝ := ∑ i, F i j ^ 2

theorem finiteRowGram_norm {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (F : Matrix I J ℝ) :
    ‖F * F.transpose‖ = ‖F‖ ^ 2 := by
  have ht : ‖F.transpose‖ = ‖F‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose F
  calc
    ‖F * F.transpose‖ = ‖F.transpose.conjTranspose * F.transpose‖ := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    _ = ‖F.transpose‖ * ‖F.transpose‖ := Matrix.l2_opNorm_conjTranspose_mul_self F.transpose
    _ = ‖F‖ ^ 2 := by rw [ht, pow_two]

theorem finiteRowColumnSample_univ_norm {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℕ} (F : Matrix I (Fin s) ℝ) :
    ‖finiteRowColumnSample F univ‖ = ‖F‖ := by
  have hgram : finiteRowColumnSample F univ * (finiteRowColumnSample F univ).transpose =
      F * F.transpose := by
    ext i k
    simp only [finiteRowColumnSample, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq]
    simpa using Finset.sum_coe_sort (univ : Finset (Fin s)) (fun j => F i j * F k j)
  have hsquare : ‖finiteRowColumnSample F univ‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [← finiteRowGram_norm, hgram, finiteRowGram_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

theorem actual_finite_row_column_sample_norm_tail {I : Type*} [Fintype I]
    [DecidableEq I] {s : ℕ} (hI : 0 < Fintype.card I)
    (F : Matrix I (Fin s) ℝ) (p : unitInterval) (c : ℝ) (hc : 0 < c)
    (hcol : ∀ j, finiteRowColumnEnergy F j ≤ c ^ 2) (t : ℝ) (ht : 0 < t) :
    ((bernoulliColumnLaw s p)
      {ω | ‖finiteRowColumnSample F (selectedColumns ω)‖ ≥
        Real.sqrt (p : ℝ) * ‖F‖ + c * Real.sqrt t}).toReal ≤
      2 * (Fintype.card I : ℝ) * Real.exp (-t) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let F' : Matrix (Fin (Fintype.card I)) (Fin s) ℝ := F.submatrix e id
  have hF : ‖F'‖ = ‖F‖ := l2_opNorm_row_equiv F e
  have hsample : ∀ ω, ‖columnSample F' (selectedColumns ω)‖ =
      ‖finiteRowColumnSample F (selectedColumns ω)‖ := by
    intro ω
    exact l2_opNorm_row_equiv (finiteRowColumnSample F (selectedColumns ω)) e
  have henergy : ∀ j, columnEnergy F' j = finiteRowColumnEnergy F j := by
    intro j
    unfold columnEnergy finiteRowColumnEnergy
    change (∑ i, F (e i) j ^ 2) = ∑ i, F i j ^ 2
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have htail := actual_column_sample_norm_tail hI F' p c hc
    (fun j => (henergy j).trans_le (hcol j)) t ht
  simpa only [hF, hsample] using htail

#print axioms l2_opNorm_row_equiv
#print axioms finiteRowColumnSample_univ_norm
#print axioms actual_finite_row_column_sample_norm_tail
#check @actual_finite_row_column_sample_norm_tail
end OpenMathReview.Sampling
