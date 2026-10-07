/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import SLT.RMT.MatBern

/-! # Actual row/column sampling and centred binary matrix identities

These algebraic identities supply data for a future concentration proof. They
do not assume or assert the fixed-size spectral sampling conclusion B2.2.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

def centered {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => W i j - d / N

def rowEnergy {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (i : Fin r) : ℝ :=
  ∑ j, (F i j) ^ 2

def columnEnergy {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) : ℝ :=
  ∑ i, (F i j) ^ 2

def sampled {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (U V : Finset (Fin N)) : Matrix U V ℝ :=
  W.submatrix Subtype.val Subtype.val

theorem sampled_centered_decomposition {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (d : ℝ) (U V : Finset (Fin N)) :
    sampled W U V = Matrix.of (fun _ _ => d / N) +
      sampled (centered W d) U V := by
  ext i j
  simp only [sampled, Matrix.submatrix_apply, centered, Matrix.add_apply, Matrix.of_apply]
  ring

theorem sum_sq_sub_const {N : ℕ} (x : Fin N → ℝ) (a : ℝ) :
    ∑ i, (x i - a) ^ 2 =
      (∑ i, (x i) ^ 2) - 2 * a * (∑ i, x i) + (N : ℝ) * a ^ 2 := by
  calc
    ∑ i, (x i - a) ^ 2 = ∑ i, ((x i) ^ 2 - (2 * a) * x i + a ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp

theorem centered_row_energy {N : ℕ} (hN : 0 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1)
    (hrow : ∀ i, ∑ j, W i j = d) (i : Fin N) :
    rowEnergy (centered W d) i = d - d ^ 2 / N := by
  have hs : ∑ j, (W i j) ^ 2 = d := by
    calc
      ∑ j, (W i j) ^ 2 = ∑ j, W i j := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hb i j with h | h <;> simp [h]
      _ = d := hrow i
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold rowEnergy centered
  rw [sum_sq_sub_const, hs, hrow]
  field_simp
  ring

theorem centered_column_energy {N : ℕ} (hN : 0 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1)
    (hcol : ∀ j, ∑ i, W i j = d) (j : Fin N) :
    columnEnergy (centered W d) j = d - d ^ 2 / N := by
  simpa [rowEnergy, columnEnergy, centered, Matrix.transpose_apply] using
    centered_row_energy hN W.transpose d (fun i j => hb j i) hcol j

theorem centered_row_energy_le {N : ℕ} (hN : 0 < N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1)
    (hrow : ∀ i, ∑ j, W i j = d) (i : Fin N) :
    rowEnergy (centered W d) i ≤ d := by
  rw [centered_row_energy hN W d hb hrow]
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact sub_le_self _ (div_nonneg (sq_nonneg d) hn)

def columnGram {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    Matrix (Fin r) (Fin r) ℝ := fun i k => F i j * F k j

def weightedColumns {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (b : Fin s → ℝ) :
    Matrix (Fin r) (Fin s) ℝ := fun i j => b j * F i j

theorem columnGram_isHermitian {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    (columnGram F j).IsHermitian := by
  change (columnGram F j).conjTranspose = columnGram F j
  ext i k
  simp [columnGram, Matrix.conjTranspose_apply, mul_comm]

theorem gram_eq_sum_columnGram {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) :
    F * F.transpose = ∑ j, columnGram F j := by
  ext i k
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, columnGram]

theorem weighted_gram_eq {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (b : Fin s → ℝ) :
    weightedColumns F b * (weightedColumns F b).transpose =
      ∑ j, (b j) ^ 2 • columnGram F j := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, weightedColumns,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, columnGram]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem columnGram_sq {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    (columnGram F j) ^ 2 = columnEnergy F j • columnGram F j := by
  ext i k
  simp only [pow_two, Matrix.mul_apply, columnGram, Matrix.smul_apply,
    smul_eq_mul, columnEnergy]
  calc
    ∑ a, F i j * F a j * (F a j * F k j) =
        ∑ a, (F a j) ^ 2 * (F i j * F k j) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by simp only [pow_two, Finset.sum_mul]

#print axioms sampled_centered_decomposition
#print axioms centered_row_energy
#print axioms centered_column_energy
#print axioms centered_row_energy_le
#print axioms columnGram_isHermitian
#print axioms gram_eq_sum_columnGram
#print axioms weighted_gram_eq
#print axioms columnGram_sq
end OpenMathReview.Sampling
