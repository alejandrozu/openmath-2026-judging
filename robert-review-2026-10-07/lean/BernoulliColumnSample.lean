/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import BernoulliGram

/-! # The actual compressed-column sample and its genuine Gram concentration

The selected matrix has exactly the columns whose canonical Boolean selectors
are true, rather than an abstract family merely named "sampling". Counts remain
Bernoulli; the fixed-count uniform law and B2.2 are not asserted here.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

def columnSample {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (U : Finset (Fin s)) :
    Matrix (Fin r) U ℝ := F.submatrix id Subtype.val

def selectedColumns {s : ℕ} (ω : Fin s → Bool) : Finset (Fin s) :=
  univ.filter fun j => ω j = true

def actualSelectedGram {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (ω : Fin s → Bool) :
    Matrix (Fin r) (Fin r) ℝ :=
  columnSample F (selectedColumns ω) * (columnSample F (selectedColumns ω)).transpose

theorem columnSample_gram_eq_sum {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (U : Finset (Fin s)) :
    columnSample F U * (columnSample F U).transpose = ∑ j ∈ U, columnGram F j := by
  ext i k
  simp only [columnSample, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.sum_apply, columnGram, id_eq]
  exact Finset.sum_coe_sort U (fun j => F i j * F k j)

theorem actualSelectedGram_eq_sum {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (ω : Fin s → Bool) :
    actualSelectedGram F ω = ∑ j, bit (ω j) • columnGram F j := by
  unfold actualSelectedGram
  rw [columnSample_gram_eq_sum]
  unfold selectedColumns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases h : ω j <;> simp [bit, h]

theorem actualSelectedGram_centered_eq {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (ω : Fin s → Bool) :
    actualSelectedGram F ω - (p : ℝ) • (F * F.transpose) =
      RMT.matrixBernsteinSum (gramSummand F p) ω := by
  rw [actualSelectedGram_eq_sum, gram_eq_sum_columnGram, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  unfold RMT.matrixBernsteinSum
  apply Finset.sum_congr rfl
  intro j _
  simp only [gramSummand, gramAtom, sub_smul]

theorem actual_column_sample_gram_deviation {r s : ℕ} (hr : 0 < r)
    (F : Matrix (Fin r) (Fin s) ℝ) (p : unitInterval)
    (c : ℝ) (hcol : ∀ j, columnEnergy F j ≤ c ^ 2) (t : ℝ) (ht : 0 ≤ t) :
    ((bernoulliColumnLaw s p)
      {ω | ‖actualSelectedGram F ω - (p : ℝ) • (F * F.transpose)‖ ≥ t}).toReal ≤
      RMT.matrixBernsteinTailBound r
        ‖((p : ℝ) * (1 - p)) • ∑ j, (columnEnergy F j) • columnGram F j‖
        (c ^ 2) t := by
  simpa only [actualSelectedGram_centered_eq, RMT.matrixBernsteinVarianceProxy,
    bernoulli_gram_variance_matrix] using
    bernoulli_gram_deviation hr F p c hcol t ht

#print axioms columnSample_gram_eq_sum
#print axioms actualSelectedGram_eq_sum
#print axioms actualSelectedGram_centered_eq
#print axioms actual_column_sample_gram_deviation
#check @actual_column_sample_gram_deviation
end OpenMathReview.Sampling
