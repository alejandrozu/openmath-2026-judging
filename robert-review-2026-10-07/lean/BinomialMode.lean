/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import BernoulliColumnSample
import Mathlib.Data.Nat.Choose.Sum

/-! # A proved lower bound for the central binomial conditioning event

The mode calculation is elementary algebra. It will be used with p=m/N to
transfer a genuine Bernoulli tail to an exactly fixed-cardinality sample.
This file alone does not prove that law identification or B2.2.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Finset
open scoped BigOperators

def binomialWeight (N : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)

theorem binomialWeight_nonneg (N k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomialWeight N p k := by
  unfold binomialWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem binomialWeight_recurrence (N k : ℕ) (p : ℝ) (hk : k < N) :
    ((k : ℝ) + 1) * (1 - p) * binomialWeight N p (k + 1) =
      ((N - k : ℕ) : ℝ) * p * binomialWeight N p k := by
  have hchoose : (N.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (N.choose k : ℝ) * ((N - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq N k
  have hsub : N - k = (N - (k + 1)) + 1 := by omega
  have hpow : (1 - p) ^ (N - k) = (1 - p) ^ (N - (k + 1)) * (1 - p) := by
    rw [hsub, pow_succ]
  unfold binomialWeight
  calc
    ((k : ℝ) + 1) * (1 - p) *
        ((N.choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (N - (k + 1))) =
      ((N.choose (k + 1) : ℝ) * ((k : ℝ) + 1)) * p ^ (k + 1) *
        (1 - p) ^ (N - k) := by rw [hpow]; ring
    _ = ((N.choose k : ℝ) * ((N - k : ℕ) : ℝ)) * p ^ (k + 1) *
        (1 - p) ^ (N - k) := by rw [hchoose]
    _ = ((N - k : ℕ) : ℝ) * p *
        ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by rw [pow_succ]; ring

theorem binomialWeight_step_up (N m k : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hm : m < N) (hkm : k < m)
    (hmean : p * (N : ℝ) = (m : ℝ)) :
    binomialWeight N p k ≤ binomialWeight N p (k + 1) := by
  have hkN : k < N := hkm.trans hm
  have hrec := binomialWeight_recurrence N k p hkN
  have hsub : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) :=
    Nat.cast_sub hkN.le
  have hkmR : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hkm
  have hc : ((k : ℝ) + 1) * (1 - p) ≤ ((N - k : ℕ) : ℝ) * p := by
    rw [hsub]
    nlinarith
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hA : 0 < ((k : ℝ) + 1) * (1 - p) := by positivity
  have hw := binomialWeight_nonneg N k hp.le hp1.le
  have hmul : (((k : ℝ) + 1) * (1 - p)) * binomialWeight N p k ≤
      (((k : ℝ) + 1) * (1 - p)) * binomialWeight N p (k + 1) := by
    calc
      _ ≤ (((N - k : ℕ) : ℝ) * p) * binomialWeight N p k :=
        mul_le_mul_of_nonneg_right hc hw
      _ = _ := hrec.symm
  exact le_of_mul_le_mul_left hmul hA

theorem binomialWeight_step_down (N m k : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hm : m ≤ k) (hk : k < N)
    (hmean : p * (N : ℝ) = (m : ℝ)) :
    binomialWeight N p (k + 1) ≤ binomialWeight N p k := by
  have hrec := binomialWeight_recurrence N k p hk
  have hsub : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := Nat.cast_sub hk.le
  have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm
  have hc : ((N - k : ℕ) : ℝ) * p ≤ ((k : ℝ) + 1) * (1 - p) := by
    rw [hsub]
    nlinarith
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hA : 0 < ((k : ℝ) + 1) * (1 - p) := by positivity
  have hw := binomialWeight_nonneg N k hp.le hp1.le
  have hmul : (((k : ℝ) + 1) * (1 - p)) * binomialWeight N p (k + 1) ≤
      (((k : ℝ) + 1) * (1 - p)) * binomialWeight N p k := by
    calc
      _ = (((N - k : ℕ) : ℝ) * p) * binomialWeight N p k := hrec
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hw
  exact le_of_mul_le_mul_left hmul hA

theorem binomialWeight_le_mode (N m k : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hm : m < N) (hk : k ≤ N)
    (hmean : p * (N : ℝ) = (m : ℝ)) :
    binomialWeight N p k ≤ binomialWeight N p m := by
  by_cases hkm : k ≤ m
  · have hmon : Monotone (fun j : ℕ => binomialWeight N p (min j m)) := by
      apply monotone_nat_of_le_succ
      intro j
      by_cases hj : j < m
      · rw [min_eq_left hj.le, min_eq_left (Nat.succ_le_iff.mpr hj)]
        exact binomialWeight_step_up N m j hp hp1 hm hj hmean
      · have hjm : m ≤ j := Nat.le_of_not_gt hj
        rw [min_eq_right hjm, min_eq_right (hjm.trans (Nat.le_succ j))]
    simpa [min_eq_left hkm] using hmon hkm
  · have hmk : m ≤ k := by omega
    have hd : ∀ j, m ≤ j → j ≤ N → binomialWeight N p j ≤ binomialWeight N p m := by
      intro j
      induction j with
      | zero =>
          intro hj _
          have hm0 : m = 0 := by omega
          simp [hm0]
      | succ j ih =>
          intro hj hN
          by_cases hje : j + 1 = m
          · rw [hje]
          · have hjm : m ≤ j := by omega
            exact (binomialWeight_step_down N m j hp hp1 hjm (by omega) hmean).trans
              (ih hjm (by omega))
    exact hd k hmk hk

theorem binomialWeight_sum (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), binomialWeight N p k = 1 := by
  have h := add_pow p (1 - p) N
  have he : p + (1 - p) = 1 := by ring
  rw [he, one_pow] at h
  simpa [binomialWeight, mul_comm, mul_left_comm, mul_assoc] using h.symm

theorem binomialWeight_mode_lower (N m : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hm : m < N)
    (hmean : p * (N : ℝ) = (m : ℝ)) :
    (1 : ℝ) / ((N : ℝ) + 1) ≤ binomialWeight N p m := by
  have hsum : (1 : ℝ) ≤ ((N : ℝ) + 1) * binomialWeight N p m := by
    calc
      1 = ∑ k ∈ range (N + 1), binomialWeight N p k := (binomialWeight_sum N p).symm
      _ ≤ ∑ _k ∈ range (N + 1), binomialWeight N p m := by
        apply sum_le_sum
        intro k hk
        exact binomialWeight_le_mode N m k hp hp1 hm (by have := mem_range.mp hk; omega) hmean
      _ = ((N : ℝ) + 1) * binomialWeight N p m := by simp
  exact (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mpr (by nlinarith)

#print axioms binomialWeight_recurrence
#print axioms binomialWeight_le_mode
#print axioms binomialWeight_mode_lower
#check @binomialWeight_mode_lower
end OpenMathReview.Sampling
