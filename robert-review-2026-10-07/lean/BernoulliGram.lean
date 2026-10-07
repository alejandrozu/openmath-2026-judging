/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import NormVariance
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Pi

/-! # Genuine independent Bernoulli column-Gram sampling

The probability space is the explicit finite product of two-point Bernoulli
laws. Independence, mean zero, moments and integrability are conclusions.
No concentration, MGF or spectral conclusion is a premise.
This is not the fixed-cardinality sampling statement B2.2.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def bit (b : Bool) : ℝ := if b then 1 else 0

def bernoulliColumnLaw (s : ℕ) (p : unitInterval) : Measure (Fin s → Bool) :=
  Measure.pi (fun _ : Fin s => bernoulliMeasure true false p)

instance (s : ℕ) (p : unitInterval) : IsProbabilityMeasure (bernoulliColumnLaw s p) := by
  unfold bernoulliColumnLaw
  infer_instance

def gramAtom {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) (b : Bool) : Matrix (Fin r) (Fin r) ℝ :=
  (bit b - (p : ℝ)) • columnGram F j

def gramSummand {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) (ω : Fin s → Bool) : Matrix (Fin r) (Fin r) ℝ :=
  gramAtom F p j (ω j)

local instance {r : ℕ} : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := borel _
local instance {r : ℕ} : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := ⟨rfl⟩

theorem gramSummand_integrable {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) :
    Integrable (gramSummand F p j) (bernoulliColumnLaw s p) := by
  exact MeasureTheory.integrable_comp_eval
    (integrable_bernoulliMeasure true false p (gramAtom F p j))

theorem gramSummand_square_integrable {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) :
    Integrable (fun ω => (gramSummand F p j ω) ^ 2) (bernoulliColumnLaw s p) := by
  exact MeasureTheory.integrable_comp_eval
    (μ := fun _ : Fin s => bernoulliMeasure true false p) (i := j)
    (integrable_bernoulliMeasure true false p (fun b => (gramAtom F p j b) ^ 2))

theorem gramSummand_mean_zero {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) :
    ∫ ω, gramSummand F p j ω ∂bernoulliColumnLaw s p = 0 := by
  unfold gramSummand bernoulliColumnLaw
  rw [MeasureTheory.integral_comp_eval
    (integrable_bernoulliMeasure true false p (gramAtom F p j)).aestronglyMeasurable]
  rw [integral_bernoulliMeasure]
  simp only [gramAtom, bit, Bool.false_eq_true, if_true, if_false]
  rw [smul_smul, smul_smul, ← add_smul]
  have h : (p : ℝ) * (1 - p) + (1 - p) * (0 - p) = 0 := by ring
  rw [h, zero_smul]

theorem real_smul_square {r : ℕ} (a : ℝ) (G : Matrix (Fin r) (Fin r) ℝ) :
    (a • G) ^ 2 = a ^ 2 • G ^ 2 := by
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]

theorem gramSummand_second_moment {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) :
    ∫ ω, (gramSummand F p j ω) ^ 2 ∂bernoulliColumnLaw s p =
      ((p : ℝ) * (1 - p)) • (columnGram F j) ^ 2 := by
  unfold gramSummand bernoulliColumnLaw
  rw [MeasureTheory.integral_comp_eval
    (μ := fun _ : Fin s => bernoulliMeasure true false p) (i := j)
    (f := fun b : Bool => (gramAtom F p j b) ^ 2)
    (integrable_bernoulliMeasure true false p (fun b => (gramAtom F p j b) ^ 2)).aestronglyMeasurable]
  rw [integral_bernoulliMeasure]
  simp only [gramAtom, bit, Bool.false_eq_true, if_true, if_false, real_smul_square]
  rw [smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

theorem gramSummand_isHermitian {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) (ω : Fin s → Bool) :
    (gramSummand F p j ω).IsHermitian := by
  change (gramSummand F p j ω).conjTranspose = gramSummand F p j ω
  ext i k
  simp [gramSummand, gramAtom, Matrix.smul_apply, Matrix.conjTranspose_apply,
    columnGram, mul_comm]

theorem gramSummand_norm_bound {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) (j : Fin s) (c : ℝ) (hcol : columnEnergy F j ≤ c ^ 2)
    (ω : Fin s → Bool) : ‖gramSummand F p j ω‖ ≤ c ^ 2 := by
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hp1 : (p : ℝ) ≤ 1 := p.property.2
  have hbit : |bit (ω j) - p| ≤ 1 := by
    cases h : ω j
    · simp only [bit, h, Bool.false_eq_true, if_false, zero_sub, abs_neg, abs_of_nonneg hp0]
      exact hp1
    · simp only [bit, h, if_true]
      rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
      linarith
  unfold gramSummand gramAtom
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |bit (ω j) - p| * ‖columnGram F j‖ ≤ 1 * ‖columnGram F j‖ :=
      mul_le_mul_of_nonneg_right hbit (norm_nonneg _)
    _ ≤ c ^ 2 := by simpa using columnGram_norm_le F j c hcol

theorem gramSummand_independent {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) :
    RMT.MatrixBernsteinIndependent (gramSummand F p) (bernoulliColumnLaw s p) := by
  unfold RMT.MatrixBernsteinIndependent
  change iIndepFun (fun j ω => gramAtom F p j (ω j))
    (Measure.pi (fun _ : Fin s => bernoulliMeasure true false p))
  exact iIndepFun_pi (fun j =>
    (show Measurable (gramAtom F p j) from Measurable.of_discrete).aemeasurable)

theorem bernoulli_gram_variance_matrix {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ)
    (p : unitInterval) :
    RMT.matrixBernsteinVarianceMatrix (bernoulliColumnLaw s p) (gramSummand F p) =
      ((p : ℝ) * (1 - p)) • ∑ j, (columnEnergy F j) • columnGram F j := by
  unfold RMT.matrixBernsteinVarianceMatrix
  simp_rw [gramSummand_second_moment, columnGram_sq, smul_smul]
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem bernoulli_gram_deviation {r s : ℕ} (hr : 0 < r)
    (F : Matrix (Fin r) (Fin s) ℝ) (p : unitInterval)
    (c : ℝ) (hcol : ∀ j, columnEnergy F j ≤ c ^ 2) (t : ℝ) (ht : 0 ≤ t) :
    ((bernoulliColumnLaw s p) {ω | ‖RMT.matrixBernsteinSum (gramSummand F p) ω‖ ≥ t}).toReal ≤
      RMT.matrixBernsteinTailBound r
        (RMT.matrixBernsteinVarianceProxy (bernoulliColumnLaw s p) (gramSummand F p))
        (c ^ 2) t := by
  exact RMT.matrix_bernstein_inequality_hdp_all (gramSummand F p)
    (bernoulliColumnLaw s p) (c ^ 2) hr (gramSummand_independent F p)
    (gramSummand_integrable F p) (gramSummand_square_integrable F p)
    (gramSummand_mean_zero F p)
    (fun j => Filter.Eventually.of_forall (gramSummand_isHermitian F p j))
    (fun j => Filter.Eventually.of_forall (gramSummand_norm_bound F p j c (hcol j)))
    t ht

#print axioms gramSummand_mean_zero
#print axioms gramSummand_second_moment
#print axioms gramSummand_independent
#print axioms gramSummand_norm_bound
#print axioms bernoulli_gram_variance_matrix
#print axioms bernoulli_gram_deviation
#check @bernoulli_gram_deviation
end OpenMathReview.Sampling
