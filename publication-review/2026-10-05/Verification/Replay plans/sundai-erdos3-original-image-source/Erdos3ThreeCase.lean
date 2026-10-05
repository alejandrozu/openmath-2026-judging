import Erdos3CrossScale

/-!
# The three-term case of Erdős 3 from a Roth-number bound

This module does not prove the Kelley–Meka or Bloom–Sisask bounds. It proves
that either published bound implies Formal Conjectures' `erdos_3.variants.three`
(every set with divergent reciprocal sum contains a three-term progression).
The bound statements and the target are copied verbatim from
`FormalConjectures/ErdosProblems/3.lean`. What remains for an unconditional
proof is the bound itself.
-/

namespace Erdos3ThreeCase

open Asymptotics Filter

/-- Verbatim from Formal Conjectures: the largest `k`-AP-free subset of `{1, …, N}`. -/
noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/-- Verbatim statement of `erdos_3.variants.three`. -/
def ThreeCase : Prop := ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, S.IsAPOfLength 3

/-- Verbatim statement of `erdos_3.variants.kelley_meka`. -/
def KelleyMeka : Prop := ∃ β > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun N ↦ (r 3 N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β)

/-- The Bloom–Sisask (2020) form: `r₃(N) ≪ N / (log N)^(1+c)` for some `c > 0`. -/
def LogBarrier (k : ℕ) : Prop := ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) / Real.log N ^ (1 + c)

-- ## analysis

/-- Beating the logarithm by a power above one makes the dyadic extremal series converge. -/
theorem dyadic_of_logBarrier {k : ℕ} (h : LogBarrier k) :
    Summable fun j : ℕ ↦ (r k (2 ^ j) : ℝ) / 2 ^ j := by
  obtain ⟨c, hc, hO⟩ := h
  have ht : Tendsto (fun j : ℕ => 2 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have h1 := (hO.comp_tendsto ht).mul (isBigO_refl (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop)
  have hg : Summable (fun j : ℕ => (Real.log 2 ^ (1 + c))⁻¹ * ((j : ℝ) ^ (1 + c))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  apply summable_of_isBigO_nat hg
  refine (h1.congr_left ?_).congr_right ?_
  · intro j
    simp only [Function.comp_def, div_eq_mul_inv]
  · intro j
    simp only [Function.comp_def]
    push_cast
    have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
    rw [Real.log_pow, Real.mul_rpow (Nat.cast_nonneg j) (Real.log_nonneg one_le_two),
      div_eq_mul_inv, mul_comm, ← mul_assoc, inv_mul_cancel₀ h2, one_mul, mul_inv, mul_comm]

/-- A Kelley–Meka-shape bound implies the logarithmic-barrier form, for any length. -/
theorem logBarrier_of_quasipoly {k : ℕ} (h : ∃ β > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β)) :
    LogBarrier k := by
  obtain ⟨β, hβ, c, hc, hO⟩ := h
  refine ⟨1, one_pos, hO.trans ?_⟩
  have e1 : (fun y : ℝ => Real.exp (-c * y)) =O[atTop] fun y : ℝ => y ^ (-2 / β) :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-2 / β)).isBigO
  have e2 := e1.comp_tendsto (tendsto_rpow_atTop hβ)
  have e3 : (fun x : ℝ => Real.exp (-c * x ^ β)) =O[atTop] fun x : ℝ => 1 / x ^ ((1 : ℝ) + 1) := by
    refine e2.trans_eventuallyEq ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def]
    rw [← Real.rpow_mul hx, show β * (-2 / β) = -((1 : ℝ) + 1) by field_simp; ring,
      Real.rpow_neg hx, one_div]
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have e4 := (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop).mul (e3.comp_tendsto hlog)
  refine e4.congr_right ?_
  intro N
  simp only [Function.comp_def]
  rw [mul_one_div]

-- ## the three-term case

/-- Dyadic extremal summability for length three gives the three-term case. -/
theorem three_of_dyadic (h : Summable fun j : ℕ ↦ (r 3 (2 ^ j) : ℝ) / 2 ^ j) :
    ThreeCase := by
  intro A hdiv
  by_contra hno
  push_neg at hno
  have hAfree : A.IsAPOfLengthFree 3 := by
    intro t ht hAP
    exact absurd hAP (hno t ht)
  exact hdiv (Erdos3CrossScale.freeSummable_of_dyadic h A hAfree)

/-- The Bloom–Sisask (2020) bound would give `erdos_3.variants.three`. -/
theorem three_of_logBarrier (h : LogBarrier 3) : ThreeCase :=
  three_of_dyadic (dyadic_of_logBarrier h)

/-- Formal Conjectures' `kelley_meka` variant implies its `three` variant. -/
theorem three_of_kelleyMeka (h : KelleyMeka) : ThreeCase :=
  three_of_logBarrier (logBarrier_of_quasipoly h)

#print axioms dyadic_of_logBarrier
#print axioms logBarrier_of_quasipoly
#print axioms three_of_dyadic
#print axioms three_of_logBarrier
#print axioms three_of_kelleyMeka

end Erdos3ThreeCase
