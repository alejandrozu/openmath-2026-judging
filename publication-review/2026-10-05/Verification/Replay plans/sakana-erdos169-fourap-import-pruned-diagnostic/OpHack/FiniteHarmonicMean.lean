import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Optional reusable rational finite-Jensen bridge. No holes or extra axioms.
Compilation pending; the proof uses only positivity, square nonnegativity,
and rearrangement of finite sums, so no analytic convexity API is required. -/
namespace Erdos3Candidate

lemma pair_ratio_ge_two (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    2 ≤ x / y + y / x := by
  have hid : (x / y + y / x) * (x * y) = x*x + y*y := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    <;> ring
  have hxy : 0 < x * y := mul_pos hx hy
  have hle : 2 * (x * y) ≤ (x / y + y / x) * (x * y) := by
    rw [hid]
    nlinarith [sq_nonneg (x-y)]
  nlinarith

lemma finite_harmonic_cauchy {α : Type*} (s : Finset α) (f : α → ℚ)
    (hpos : ∀ i ∈ s, 0 < f i) :
    (s.card : ℚ)^2 ≤ (∑ i ∈ s, f i) * (∑ i ∈ s, 1 / f i) := by
  have hp := Finset.sum_le_sum (fun i hi =>
    Finset.sum_le_sum (fun j hj => pair_ratio_ge_two (f i) (f j) (hpos i hi) (hpos j hj)))
  have hl : (∑ i ∈ s, ∑ j ∈ s, (2 : ℚ)) = 2 * (s.card : ℚ)^2 := by
    simp
    <;> ring
  have hr : (∑ i ∈ s, ∑ j ∈ s, (f i / f j + f j / f i)) =
      2 * (∑ i ∈ s, f i) * (∑ i ∈ s, 1 / f i) := by
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, one_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hl, hr] at hp
  linarith

lemma finite_harmonic_mean_bound {α : Type*} (s : Finset α) (f : α → ℚ)
    (hs : s.Nonempty) (B : ℚ) (hB : 0 < B)
    (hpos : ∀ i ∈ s, 0 < f i)
    (hmean : (∑ i ∈ s, f i) ≤ (s.card : ℚ) * B) :
    (s.card : ℚ) / B ≤ ∑ i ∈ s, 1 / f i := by
  have hc := finite_harmonic_cauchy s f hpos
  have hn : (0 : ℚ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hr : (0 : ℚ) ≤ ∑ i ∈ s, 1 / f i :=
    Finset.sum_nonneg (fun i hi => le_of_lt (one_div_pos.mpr (hpos i hi)))
  have hm := mul_le_mul_of_nonneg_right hmean hr
  apply (div_le_iff₀ hB).2
  nlinarith

end Erdos3Candidate
