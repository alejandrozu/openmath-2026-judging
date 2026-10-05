import Std

/-!+# Elementary, checked special cases related to Erdős Problem 3

This file proves known elementary results, not the open reciprocal-divergence
conjecture. It uses only Std. No infinite sums or Mathlib definitions are imported.

`ContainsAP A k` means there are a start a and positive step d such that all k
terms a+i*d, with i<k, belong to A. `ap_terms_strictly_increase` checks that a
positive step makes these terms distinct. For k=0 the condition is vacuous.
The positive-step convention is harmless for k=0 or k=1, and is necessary for
nontrivial progressions of length at least two.
-/

namespace Erdos3SpecialCases

def ContainsAP (A : Nat → Prop) (k : Nat) : Prop :=
  ∃ a d : Nat, 0 < d ∧ ∀ i : Nat, i < k → A (a + i * d)

def ArbitrarilyLongAPs (A : Nat → Prop) : Prop :=
  ∀ k : Nat, ContainsAP A k

theorem ap_terms_strictly_increase (a d i j : Nat)
    (hd : 0 < d) (hij : i < j) : a + i * d < a + j * d := by
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij hd) a

theorem containsAP_mono {A B : Nat → Prop} {k : Nat}
    (hAB : ∀ n, A n → B n) (hA : ContainsAP A k) : ContainsAP B k := by
  obtain ⟨a, d, hd, hterms⟩ := hA
  exact ⟨a, d, hd, fun i hi => hAB _ (hterms i hi)⟩

theorem containsAP_prefix {A : Nat → Prop} {k l : Nat}
    (hlk : l ≤ k) (hA : ContainsAP A k) : ContainsAP A l := by
  obtain ⟨a, d, hd, hterms⟩ := hA
  exact ⟨a, d, hd, fun i hi => hterms i (Nat.lt_of_lt_of_le hi hlk)⟩

/-- Unbounded available lengths suffice for every finite length. -/
theorem unbounded_lengths_iff_all_lengths (A : Nat → Prop) :
    (∀ n, ∃ k, n ≤ k ∧ ContainsAP A k) ↔ ArbitrarilyLongAPs A := by
  constructor
  · intro h n
    obtain ⟨k, hnk, hk⟩ := h n
    exact containsAP_prefix hnk hk
  · intro h n
    exact ⟨n, Nat.le_refl n, h n⟩

/-- Cofinite case: the interval starting at N supplies every finite length. -/
theorem cofinite_contains_all_lengths {A : Nat → Prop} (N : Nat)
    (hA : ∀ n, N ≤ n → A n) : ArbitrarilyLongAPs A := by
  intro k
  refine ⟨N, 1, by decide, ?_⟩
  intro i _
  apply hA
  omega

/-- Every tail of an infinite nonconstant arithmetic progression works. -/
theorem affine_tail_contains_all_lengths {A : Nat → Prop} (a d N : Nat)
    (hd : 0 < d) (hA : ∀ n, N ≤ n → A (a + n * d)) :
    ArbitrarilyLongAPs A := by
  intro k
  refine ⟨a + N * d, d, hd, ?_⟩
  intro i _
  have h := hA (N + i) (Nat.le_add_right N i)
  simpa [Nat.add_mul, Nat.add_assoc] using h

/-- A concrete family: all multiples of any positive d. -/
theorem multiples_contain_all_lengths (d : Nat) (hd : 0 < d) :
    ArbitrarilyLongAPs (fun n => ∃ m, n = m * d) := by
  intro k
  exact ⟨0, d, hd, fun i _ => ⟨i, by simp⟩⟩

/-- Unbounded sets contain a nonconstant progression of length two. -/
theorem unbounded_contains_two {A : Nat → Prop}
    (hA : ∀ N : Nat, ∃ n, N ≤ n ∧ A n) : ContainsAP A 2 := by
  obtain ⟨a, _, ha⟩ := hA 0
  obtain ⟨b, hb, hAb⟩ := hA (a + 1)
  refine ⟨a, b - a, by omega, ?_⟩
  intro i hi
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with hi0 | hi1
  · simpa [hi0] using ha
  · have hab : a + (b - a) = b := by omega
    simpa [hi1, hab] using hAb

/-- Progression properties pass to any superset. -/
theorem arbitrarilyLongAPs_mono {A B : Nat → Prop}
    (hAB : ∀ n, A n → B n) (hA : ArbitrarilyLongAPs A) :
    ArbitrarilyLongAPs B := by
  intro k
  exact containsAP_mono hAB (hA k)

/-- If the last power is beyond the middle one, it is at least twice as large.
Adding any positive power makes the midpoint identity impossible. -/
theorem powers_two_no_midpoint (i j k : Nat) (hjk : j < k) :
    2 ^ i + 2 ^ k ≠ 2 * 2 ^ j := by
  have hpos := Nat.two_pow_pos i
  have hlarge : 2 ^ (j + 1) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simp only [Nat.pow_succ] at hlarge
  omega

/-- Powers of two have no nonconstant three-term arithmetic progression. -/
theorem powers_two_no_three :
    ¬ ContainsAP (fun n => ∃ i : Nat, n = 2 ^ i) 3 := by
  rintro ⟨a, d, hd, hterms⟩
  obtain ⟨i, hi⟩ := hterms 0 (by decide)
  obtain ⟨j, hj⟩ := hterms 1 (by decide)
  obtain ⟨k, hk⟩ := hterms 2 (by decide)
  simp only [Nat.zero_mul, Nat.add_zero] at hi
  simp only [Nat.one_mul] at hj
  have hpow : 2 ^ j < 2 ^ k := by omega
  have hjk : j < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hneq := powers_two_no_midpoint i j k hjk
  apply hneq
  omega

theorem nat_lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [Nat.pow_succ]
    omega

/-- An explicit unbounded family to show why infinitude alone is insufficient. -/
theorem powers_two_unbounded :
    ∀ N : Nat, ∃ n, N ≤ n ∧ (∃ i : Nat, n = 2 ^ i) := by
  intro N
  exact ⟨2 ^ N, Nat.le_of_lt (nat_lt_two_pow N), N, rfl⟩

theorem unbounded_does_not_imply_all_lengths :
    ¬ (∀ A : Nat → Prop,
      (∀ N : Nat, ∃ n, N ≤ n ∧ A n) → ArbitrarilyLongAPs A) := by
  intro h
  exact powers_two_no_three (h _ powers_two_unbounded 3)

#print axioms ap_terms_strictly_increase
#print axioms containsAP_mono
#print axioms containsAP_prefix
#print axioms unbounded_lengths_iff_all_lengths
#print axioms cofinite_contains_all_lengths
#print axioms affine_tail_contains_all_lengths
#print axioms multiples_contain_all_lengths
#print axioms unbounded_contains_two
#print axioms arbitrarilyLongAPs_mono
#print axioms powers_two_no_midpoint
#print axioms powers_two_no_three
#print axioms nat_lt_two_pow
#print axioms powers_two_unbounded
#print axioms unbounded_does_not_imply_all_lengths

end Erdos3SpecialCases
