/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import BinomialMode
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Powerset

/-! # Actual Bernoulli selectors conditioned to a uniform fixed count

Every subset of the prescribed size has one Boolean selector and the same
Bernoulli probability. The polynomial conditioning loss is derived from the
proved central binomial mode bound. No tail or spectral premise is introduced.
-/
noncomputable section
namespace OpenMathReview.Sampling
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

def fixedCountSelectors (s m : ℕ) : Finset (Fin s → Bool) :=
  univ.filter fun ω => (selectedColumns ω).card = m

theorem selectedColumns_indicator {s : ℕ} (U : Finset (Fin s)) :
    selectedColumns (fun j => decide (j ∈ U)) = U := by
  ext j
  simp [selectedColumns]

theorem selectedColumns_injective (s : ℕ) : Function.Injective (@selectedColumns s) := by
  intro ω ω' he
  funext j
  have hj : (ω j = true) ↔ (ω' j = true) := by
    simpa only [selectedColumns, mem_filter, mem_univ, true_and] using (Finset.ext_iff.mp he j)
  cases h : ω j <;> cases h' : ω' j <;> simp_all

theorem fixedCountSelectors_card (s m : ℕ) :
    (fixedCountSelectors s m).card = s.choose m := by
  have hcard : (fixedCountSelectors s m).card =
      (univ.powersetCard m : Finset (Finset (Fin s))).card := by
    apply Finset.card_bij (fun ω _ => selectedColumns ω)
    · intro ω hω
      exact mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hω).2⟩
    · intro ω hω ω' hω' hsame
      exact selectedColumns_injective s hsame
    · intro U hU
      have hsize : U.card = m := (mem_powersetCard.mp hU).2
      refine ⟨fun j => decide (j ∈ U), ?_, selectedColumns_indicator U⟩
      simp [fixedCountSelectors, selectedColumns_indicator, hsize]
  simpa only [card_powersetCard, card_univ, Fintype.card_fin] using hcard

theorem fixedCountSelectors_nonempty (s m : ℕ) (hm : m ≤ s) :
    (fixedCountSelectors s m).Nonempty := by
  apply card_pos.mp
  rw [fixedCountSelectors_card]
  exact Nat.choose_pos hm

def uniformFixedColumnLaw (s m : ℕ) (hm : m ≤ s) : Measure (Fin s → Bool) :=
  (PMF.uniformOfFinset (fixedCountSelectors s m) (fixedCountSelectors_nonempty s m hm)).toMeasure

instance (s m : ℕ) (hm : m ≤ s) : IsProbabilityMeasure (uniformFixedColumnLaw s m hm) := by
  unfold uniformFixedColumnLaw
  infer_instance

theorem bernoulliColumnLaw_real_singleton (s : ℕ) (p : unitInterval) (ω : Fin s → Bool) :
    (bernoulliColumnLaw s p).real {ω} =
      (p : ℝ) ^ (selectedColumns ω).card *
      (1 - p : ℝ) ^ (s - (selectedColumns ω).card) := by
  change (Measure.pi (fun _ : Fin s => bernoulliMeasure true false p) {ω}).toReal = _
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  have hpoint : ∀ j : Fin s,
      (bernoulliMeasure true false p {ω j}).toReal =
        if ω j = true then (p : ℝ) else 1 - p := by
    intro j
    cases h : ω j <;>
      simp [← measureReal_def, bernoulliMeasure_real_apply, h, Bool.false_eq_true]
  simp_rw [hpoint]
  have hcomp : (univ.filter fun j : Fin s => ¬ ω j = true).card =
      s - (selectedColumns ω).card := by
    have h := card_filter_add_card_filter_not (s := univ) (fun j : Fin s => ω j = true)
    simp only [card_univ, Fintype.card_fin] at h
    unfold selectedColumns
    omega
  rw [Finset.prod_ite]
  simp only [prod_const, hcomp]
  rfl

theorem bernoulliColumnLaw_real_fixed_count (s m : ℕ) (p : unitInterval) :
    (bernoulliColumnLaw s p).real (fixedCountSelectors s m) = binomialWeight s p m := by
  rw [← sum_measureReal_singleton]
  have hmass : ∀ ω ∈ fixedCountSelectors s m,
      (bernoulliColumnLaw s p).real {ω} = (p : ℝ) ^ m * (1 - p : ℝ) ^ (s - m) := by
    intro ω hω
    rw [bernoulliColumnLaw_real_singleton, (mem_filter.mp hω).2]
  rw [sum_congr rfl hmass, sum_const, nsmul_eq_mul, fixedCountSelectors_card]
  unfold binomialWeight
  ring

theorem bernoulliColumnLaw_real_fixed_count_lower (s m : ℕ) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hm : m < s)
    (hmean : (p : ℝ) * (s : ℝ) = (m : ℝ)) :
    (1 : ℝ) / ((s : ℝ) + 1) ≤
      (bernoulliColumnLaw s p).real (fixedCountSelectors s m) := by
  rw [bernoulliColumnLaw_real_fixed_count]
  exact binomialWeight_mode_lower s m hp hp1 hm hmean

theorem uniformFixedColumnLaw_real_apply (s m : ℕ) (hm : m ≤ s)
    (E : Set (Fin s → Bool)) :
    (uniformFixedColumnLaw s m hm).real E =
      ((fixedCountSelectors s m).filter fun ω => ω ∈ E).card /
        ((fixedCountSelectors s m).card : ℝ) := by
  unfold uniformFixedColumnLaw
  rw [measureReal_def, PMF.toMeasure_uniformOfFinset_apply
    (fixedCountSelectors_nonempty s m hm) E (Set.toFinite E).measurableSet,
    ENNReal.toReal_div]
  simp

theorem uniformFixedColumnLaw_actual_subset_probability (s m : ℕ) (hm : m ≤ s)
    (U : Finset (Fin s)) (hU : U.card = m) :
    (uniformFixedColumnLaw s m hm).real {ω | selectedColumns ω = U} =
      (1 : ℝ) / (s.choose m : ℝ) := by
  have hset : (fixedCountSelectors s m).filter (fun ω => selectedColumns ω = U) =
      {fun j => decide (j ∈ U)} := by
    ext ω
    simp only [mem_filter, mem_singleton]
    constructor
    · intro hω
      exact selectedColumns_injective s (hω.2.trans (selectedColumns_indicator U).symm)
    · intro hω
      subst ω
      constructor
      · simp [fixedCountSelectors, selectedColumns_indicator, hU]
      · exact selectedColumns_indicator U
  rw [uniformFixedColumnLaw_real_apply]
  simp only [Set.mem_setOf_eq]
  rw [hset, card_singleton, fixedCountSelectors_card]
  simp

theorem uniformFixedColumnLaw_real_as_conditioning (s m : ℕ) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hm : m ≤ s)
    (E : Set (Fin s → Bool)) :
    (uniformFixedColumnLaw s m hm).real E =
      (bernoulliColumnLaw s p).real (E ∩ (fixedCountSelectors s m : Set _)) /
        (bernoulliColumnLaw s p).real (fixedCountSelectors s m) := by
  have hq : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hbase : 0 < (p : ℝ) ^ m * (1 - p : ℝ) ^ (s - m) := by positivity
  have hcard : 0 < ((fixedCountSelectors s m).card : ℝ) := by
    exact_mod_cast card_pos.mpr (fixedCountSelectors_nonempty s m hm)
  have hmass : (bernoulliColumnLaw s p).real
      (E ∩ (fixedCountSelectors s m : Set _)) =
      (((fixedCountSelectors s m).filter fun ω => ω ∈ E).card : ℝ) *
        ((p : ℝ) ^ m * (1 - p : ℝ) ^ (s - m)) := by
    have hset : E ∩ (fixedCountSelectors s m : Set _) =
        (((fixedCountSelectors s m).filter fun ω => ω ∈ E) : Set _) := by
      ext ω
      simp [and_comm]
    rw [hset, ← sum_measureReal_singleton]
    have he : ∀ ω ∈ (fixedCountSelectors s m).filter (fun ω => ω ∈ E),
        (bernoulliColumnLaw s p).real {ω} = (p : ℝ) ^ m * (1 - p : ℝ) ^ (s - m) := by
      intro ω hω
      rw [bernoulliColumnLaw_real_singleton, (mem_filter.mp (mem_filter.mp hω).1).2]
    rw [sum_congr rfl he, sum_const, nsmul_eq_mul]
  rw [uniformFixedColumnLaw_real_apply, hmass, bernoulliColumnLaw_real_fixed_count]
  unfold binomialWeight
  rw [← fixedCountSelectors_card]
  field_simp [ne_of_gt hbase, ne_of_gt hcard]

theorem uniformFixedColumnLaw_event_le (s m : ℕ) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hm : m < s)
    (hmean : (p : ℝ) * (s : ℝ) = (m : ℝ)) (E : Set (Fin s → Bool)) :
    (uniformFixedColumnLaw s m hm.le).real E ≤
      ((s : ℝ) + 1) * (bernoulliColumnLaw s p).real E := by
  rw [uniformFixedColumnLaw_real_as_conditioning s m p hp hp1 hm.le]
  have hmass := bernoulliColumnLaw_real_fixed_count_lower s m p hp hp1 hm hmean
  have hpos : 0 < (bernoulliColumnLaw s p).real (fixedCountSelectors s m) :=
    (by positivity : 0 < (1 : ℝ) / ((s : ℝ) + 1)).trans_le hmass
  have hsub : (bernoulliColumnLaw s p).real (E ∩ (fixedCountSelectors s m : Set _)) ≤
      (bernoulliColumnLaw s p).real E := measureReal_mono Set.inter_subset_left
  have hmultiply : 1 ≤ ((s : ℝ) + 1) *
      (bernoulliColumnLaw s p).real (fixedCountSelectors s m) := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < (s : ℝ) + 1)).mp hmass
  apply (div_le_iff₀ hpos).mpr
  have hepos : 0 ≤ (bernoulliColumnLaw s p).real E := measureReal_nonneg
  have hexpand := mul_le_mul_of_nonneg_left hmultiply hepos
  nlinarith

#print axioms fixedCountSelectors_card
#print axioms bernoulliColumnLaw_real_fixed_count_lower
#print axioms uniformFixedColumnLaw_actual_subset_probability
#print axioms uniformFixedColumnLaw_real_as_conditioning
#print axioms uniformFixedColumnLaw_event_le
#check @uniformFixedColumnLaw_event_le
end OpenMathReview.Sampling
