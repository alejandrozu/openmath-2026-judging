/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import UniformShoreEvents
import FiniteProductProbability

/-! # Actual independent uniform two-shore norm sampling

The probability bounds in this proof come from the already derived uniform
norm and neighbour-count theorems. No concentration conclusion is a premise.
-/
noncomputable section
namespace OpenMathReview.Sampling
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator Classical

def twoShoreLaw (N m : ℕ) (hm : m ≤ N) : Measure ((Fin N → Bool) × (Fin N → Bool)) :=
  (uniformFixedColumnLaw N m hm).prod (uniformFixedColumnLaw N m hm)

theorem sampling_threshold_comp (p : unitInterval) (d t M R : ℝ)
    (hR : R ≤ Real.sqrt (p : ℝ) * M + Real.sqrt d * Real.sqrt t) :
    Real.sqrt (p : ℝ) * R + Real.sqrt (3 * ((p : ℝ) * d)) * Real.sqrt t ≤
      (p : ℝ) * M + (1 + Real.sqrt 3) * Real.sqrt ((p : ℝ) * d) * Real.sqrt t := by
  have hs : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt p.property.1
  have hsd : Real.sqrt (p : ℝ) * Real.sqrt d = Real.sqrt ((p : ℝ) * d) :=
    (Real.sqrt_mul p.property.1 d).symm
  have hs3 : Real.sqrt (3 * ((p : ℝ) * d)) = Real.sqrt 3 * Real.sqrt ((p : ℝ) * d) :=
    Real.sqrt_mul (by norm_num) _
  calc
    _ ≤ Real.sqrt (p : ℝ) * (Real.sqrt (p : ℝ) * M + Real.sqrt d * Real.sqrt t) +
        Real.sqrt (3 * ((p : ℝ) * d)) * Real.sqrt t := by
      exact _root_.add_le_add (mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)) le_rfl
    _ = (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) * M +
        (Real.sqrt (p : ℝ) * Real.sqrt d) * Real.sqrt t +
        Real.sqrt (3 * ((p : ℝ) * d)) * Real.sqrt t := by ring
    _ = _ := by rw [hs, hsd, hs3]; ring

theorem row_then_column_sample {N : ℕ} (F : Matrix (Fin N) (Fin N) ℝ)
    (U V : Finset (Fin N)) : finiteRowColumnSample (rowSample F U) V = sampled F U V := by
  ext i j
  rfl

theorem actual_two_shore_centered_norm_tail {N m : ℕ}
    (hN : 0 < N) (hm0 : 0 < m) (hm : m ≤ N)
    (W : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) (hd : 0 < d)
    (hb : ∀ i j, W i j = 0 ∨ W i j = 1)
    (hrow : ∀ i, ∑ j, W i j = d) (hcol : ∀ j, ∑ i, W i j = d)
    (p : unitInterval) (hmean : (p : ℝ) * (N : ℝ) = (m : ℝ))
    (hD : 0 < (p : ℝ) * d) (t : ℝ) (ht : 0 < t) (hDt : t ≤ ((p : ℝ) * d) / 3) :
    (twoShoreLaw N m hm).real
      {ω | ‖sampled (centered W d) (selectedColumns ω.1) (selectedColumns ω.2)‖ >
        (p : ℝ) * ‖centered W d‖ +
          (1 + Real.sqrt 3) * Real.sqrt ((p : ℝ) * d) * Real.sqrt t} ≤
      6 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := by
  let B := centered W d
  let μ := uniformFixedColumnLaw N m hm
  let R : Set (Fin N → Bool) := {ω | ‖rowSample B (selectedColumns ω)‖ ≥
    Real.sqrt (p : ℝ) * ‖B‖ + Real.sqrt d * Real.sqrt t}
  let G : Set (Fin N → Bool) := {ω | ∃ j, sampledDegree W (selectedColumns ω) j ≥ 2 * ((p : ℝ) * d)}
  let C : Set (Fin N → Bool) := {ω | (selectedColumns ω).card ≠ m}
  let A := (R ∪ G) ∪ C
  let E : Set ((Fin N → Bool) × (Fin N → Bool)) :=
    {ω | ‖sampled B (selectedColumns ω.1) (selectedColumns ω.2)‖ >
      (p : ℝ) * ‖B‖ + (1 + Real.sqrt 3) * Real.sqrt ((p : ℝ) * d) * Real.sqrt t}
  have hR : μ.real R ≤ 2 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := by
    exact uniform_row_sample_norm_tail hN hm0 hm B d hd
      (centered_row_energy_le hN W d hb hrow) p hmean t ht
  have hG : μ.real G ≤ 2 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := by
    have hg := uniform_all_column_degree_tail hN hm0 hm W d hb hcol p hmean hD
    have he : Real.exp (-((p : ℝ) * d) / 3) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      linarith
    exact hg.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hC : μ.real C = 0 := uniform_count_mismatch_zero N m hm
  have hA : μ.real A ≤ 4 * (N : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := by
    have hu := measureReal_union_le (μ := μ) (R ∪ G) C
    have hu' := measureReal_union_le (μ := μ) R G
    dsimp [A]
    linarith
  have hFibre : ∀ ω ∉ A, μ.real {η | (ω, η) ∈ E} ≤
      2 * (m : ℝ) * ((N : ℝ) + 1) * Real.exp (-t) := by
    intro ω hnot
    let U := selectedColumns ω
    have hc : U.card = m := by
      by_contra hneq
      exact hnot (Or.inr hneq)
    have hgoodR : ‖rowSample B U‖ ≤ Real.sqrt (p : ℝ) * ‖B‖ + Real.sqrt d * Real.sqrt t := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hbad
      exact hnot (Or.inl (Or.inl hbad))
    have hgoodG : ∀ j, sampledDegree W U j ≤ 2 * ((p : ℝ) * d) := by
      intro j
      apply le_of_lt
      apply lt_of_not_ge
      intro hbad
      exact hnot (Or.inl (Or.inr ⟨j, hbad⟩))
    have hmeanU : (p : ℝ) * d = (U.card : ℝ) / (N : ℝ) * d := by
      rw [hc, ← hmean]
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp
    have henergy : ∀ j, finiteRowColumnEnergy (rowSample B U) j ≤ Real.sqrt (3 * ((p : ℝ) * d)) ^ 2 := by
      intro j
      rw [Real.sq_sqrt (by positivity)]
      exact actual_sampled_column_energy_le hN W d hd.le
        (binary_regular_degree_le_order hN W d hb hcol) hb U ((p : ℝ) * d) hmeanU hgoodG j
    have hUI : 0 < Fintype.card U := by simpa only [Fintype.card_coe, hc] using hm0
    have htail := actual_positive_fixed_column_sample_norm_tail hUI hN hm0 hm (rowSample B U)
      p hmean (Real.sqrt (3 * ((p : ℝ) * d))) (Real.sqrt_pos.mpr (by positivity)) henergy t ht
    have hThreshold := sampling_threshold_comp p d t ‖B‖ ‖rowSample B U‖ hgoodR
    have hsub : {η | (ω, η) ∈ E} ⊆
        {η | ‖finiteRowColumnSample (rowSample B U) (selectedColumns η)‖ ≥
          Real.sqrt (p : ℝ) * ‖rowSample B U‖ + Real.sqrt (3 * ((p : ℝ) * d)) * Real.sqrt t} := by
      intro η hη
      change (p : ℝ) * ‖B‖ + (1 + Real.sqrt 3) * Real.sqrt ((p : ℝ) * d) * Real.sqrt t <
        ‖sampled B U (selectedColumns η)‖ at hη
      change _ ≤ ‖finiteRowColumnSample (rowSample B U) (selectedColumns η)‖
      rw [row_then_column_sample]
      exact hThreshold.trans hη.le
    have hh := (measureReal_mono (μ := μ) hsub).trans htail
    simpa only [Fintype.card_coe, hc] using hh
  have hprod := finite_product_bad_fiber_bound μ μ E A
    (2 * (m : ℝ) * ((N : ℝ) + 1) * Real.exp (-t)) (by positivity) hFibre
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hmscaled := mul_le_mul_of_nonneg_right hmR
    (by positivity : 0 ≤ 2 * ((N : ℝ) + 1) * Real.exp (-t))
  change (μ.prod μ).real E ≤ _
  nlinarith

#print axioms actual_two_shore_centered_norm_tail
#check @actual_two_shore_centered_norm_tail
end OpenMathReview.Sampling
