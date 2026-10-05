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

namespace Erdos3Candidate

/-- Downward integer division gives a kernel-checkable rational lower bound. -/
theorem floor_ratio_le (Q N D : ℕ) (hQ : 0 < Q) (hD : 0 < D) :
    (((N * Q / D : ℕ) : ℚ) / Q) ≤ (N : ℚ) / D := by
  have hNat : (N * Q / D) * D ≤ N * Q := Nat.div_mul_le_self (N * Q) D
  have hRat : (((N * Q / D : ℕ) : ℚ) * D) ≤ (N : ℚ) * Q := by
    exact_mod_cast hNat
  have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  exact (div_le_div_iff₀ hQ' hD').2 hRat

/-- Sum of any finite list of downward-rounded terms. -/
theorem floor_list_le (xs : List ℕ) (Q N : ℕ) (D : ℕ → ℕ)
    (hQ : 0 < Q) (hD : ∀ x ∈ xs, 0 < D x) :
    (((xs.map fun x => N * Q / D x).sum : ℕ) : ℚ) / Q ≤
      (xs.map fun x => (N : ℚ) / D x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hDx : 0 < D x := hD x (by simp)
      have hDxs : ∀ y ∈ xs, 0 < D y := by
        intro y hy
        exact hD y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
      exact add_le_add (floor_ratio_le Q N (D x) hQ hDx) (ih hDxs)

end Erdos3Candidate
