/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import ReindexSampling
import BernoulliDegree

/-! # Actual column energies after selecting rows of a binary regular matrix

The good-neighbour-count condition is deterministic data. Its probability
will be derived from the separately proved selected-degree tail, rather than
assumed in the final two-shore theorem.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

def rowSample {N : ℕ} (F : Matrix (Fin N) (Fin N) ℝ) (U : Finset (Fin N)) :
    Matrix U (Fin N) ℝ := F.submatrix Subtype.val id

def sampledDegree {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (U : Finset (Fin N)) (j : Fin N) : ℝ := ∑ i ∈ U, W i j

theorem sum_sq_sub_const_finite {I : Type*} [Fintype I] (x : I → ℝ) (a : ℝ) :
    ∑ i, (x i - a) ^ 2 = (∑ i, x i ^ 2) - 2 * a * (∑ i, x i) +
      (Fintype.card I : ℝ) * a ^ 2 := by
  calc
    ∑ i, (x i - a) ^ 2 = ∑ i, (x i ^ 2 - (2 * a) * x i + a ^ 2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      simp

theorem actual_sampled_column_energy {N : ℕ}
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1) (U : Finset (Fin N)) (j : Fin N) :
    finiteRowColumnEnergy (rowSample (centered W d) U) j =
      sampledDegree W U j * (1 - 2 * (d / N)) + (U.card : ℝ) * (d / N) ^ 2 := by
  unfold finiteRowColumnEnergy rowSample centered
  change (∑ i : U, (W i j - d / N) ^ 2) = _
  rw [sum_sq_sub_const_finite]
  have hsq : (∑ i : U, W i j ^ 2) = ∑ i : U, W i j := by
    apply sum_congr rfl
    intro i _
    rcases hb i j with h | h <;> simp [h]
  rw [hsq]
  have hsum : (∑ i : U, W i j) = sampledDegree W U j :=
    Finset.sum_coe_sort U (fun i => W i j)
  rw [hsum, Fintype.card_coe]
  ring

theorem binary_regular_degree_le_order {N : ℕ} (hN : 0 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1) (hcol : ∀ j, ∑ i, W i j = d) : d ≤ N := by
  let j : Fin N := ⟨0, hN⟩
  calc
    d = ∑ i, W i j := (hcol j).symm
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
      apply sum_le_sum
      intro i _
      rcases hb i j with h | h <;> simp [h]
    _ = (N : ℝ) := by simp

theorem actual_sampled_column_energy_le {N : ℕ} (hN : 0 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 ≤ d) (hdN : d ≤ N)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1) (U : Finset (Fin N)) (D : ℝ)
    (hD : D = (U.card : ℝ) / (N : ℝ) * d)
    (hdegree : ∀ j, sampledDegree W U j ≤ 2 * D) (j : Fin N) :
    finiteRowColumnEnergy (rowSample (centered W d) U) j ≤ 3 * D := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 ≤ d / N := div_nonneg hd hNR.le
  have ha1 : d / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hdN
  have hg0 : 0 ≤ sampledDegree W U j := by
    unfold sampledDegree
    apply sum_nonneg
    intro i _
    rcases hb i j with h | h <;> simp [h]
  have hcard : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hsquare : (d / (N : ℝ)) ^ 2 ≤ d / N := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsquare hcard
  have hmean : (U.card : ℝ) * (d / (N : ℝ)) = D := by rw [hD]; ring
  rw [actual_sampled_column_energy W d hb U j]
  rw [hmean] at hm
  nlinarith [mul_nonneg ha0 hg0, hdegree j]

#print axioms actual_sampled_column_energy
#print axioms binary_regular_degree_le_order
#print axioms actual_sampled_column_energy_le
#check @actual_sampled_column_energy_le
end OpenMathReview.Sampling
