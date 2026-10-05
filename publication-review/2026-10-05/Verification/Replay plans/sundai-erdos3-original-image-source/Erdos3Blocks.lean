import FormalConjecturesUtil

/-!
Finite dyadic logarithm blocks and an upper bound for their reciprocal mass.
The block with index zero includes zero when zero belongs to A; its reciprocal
is zero under Lean's real division convention and is handled explicitly.
-/

namespace Erdos3Blocks

def logBlock (A : Set ℕ) (j : ℕ) : Set A :=
  {a | Nat.log 2 (a : ℕ) = j}

/-- Every member of block j is below the next power of two, including zero. -/
theorem logBlock_lt_upper (A : Set ℕ) (j : ℕ) {a : A}
    (ha : a ∈ logBlock A j) : (a : ℕ) < 2 ^ (j + 1) := by
  have hlog : Nat.log 2 (a : ℕ) = j := ha
  simpa only [hlog, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (a : ℕ))

/-- The logarithm blocks are finite subsets of the original subtype. -/
theorem logBlock_finite (A : Set ℕ) (j : ℕ) : (logBlock A j).Finite := by
  apply Set.Finite.of_injOn (f := fun a : A => (a : ℕ))
    (t := Set.Iio (2 ^ (j + 1)))
  · intro a ha
    exact logBlock_lt_upper A j ha
  · exact Subtype.val_injective.injOn
  · exact Set.finite_Iio _

/-- Each reciprocal in a block is at most the reciprocal of its lower scale. -/
theorem logBlock_reciprocal_le (A : Set ℕ) (j : ℕ) {a : A}
    (ha : a ∈ logBlock A j) : 1 / (a : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
  by_cases hzero : (a : ℕ) = 0
  · have hcast : (a : ℝ) = 0 := by exact_mod_cast hzero
    rw [hcast, div_zero]
    positivity
  · have hlog : Nat.log 2 (a : ℕ) = j := ha
    have hlower : 2 ^ j ≤ (a : ℕ) := by
      simpa only [hlog] using (Nat.pow_log_le_self 2 hzero)
    have hreal : (2 : ℝ) ^ j ≤ (a : ℝ) := by exact_mod_cast hlower
    exact one_div_le_one_div_of_le (by positivity) hreal

/-- Cardinality divided by the lower dyadic scale bounds the entire block mass. -/
theorem logBlock_mass_le (A : Set ℕ) (j : ℕ) :
    (∑' a : logBlock A j, 1 / ((a : A) : ℝ)) ≤
      ((logBlock A j).ncard : ℝ) / (2 : ℝ) ^ j := by
  classical
  let : Fintype (logBlock A j) := (logBlock_finite A j).fintype
  rw [tsum_fintype]
  calc
    (∑ a : logBlock A j, 1 / ((a : A) : ℝ)) ≤
        ∑ _a : logBlock A j, 1 / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro a _
      exact logBlock_reciprocal_le A j a.property
    _ = ((logBlock A j).ncard : ℝ) / (2 : ℝ) ^ j := by
      simp [div_eq_mul_inv]

#print axioms logBlock_lt_upper
#print axioms logBlock_finite
#print axioms logBlock_reciprocal_le
#print axioms logBlock_mass_le

end Erdos3Blocks
