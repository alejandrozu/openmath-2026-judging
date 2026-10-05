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

/-!
Pure-kernel arithmetic certificate supporting an explicit four-progression-free
finite construction. These three closed arithmetic theorems do NOT, by themselves,
establish the construction or its harmonic bound. The necessary structural and
finite Cauchy/Jensen bridge is described in HARMONIC_BOUND.md.
No `sorry`, `native_decide`, or added axioms. Compilation pending.
-/
namespace Erdos3Candidate.HarmonicCertificate

def digits : List ℕ :=
  [0, 1, 2, 4, 5, 9, 10, 11, 14, 16, 17, 18, 21, 24, 30, 37, 39, 41, 42, 45, 47]

def prefixes : List ℕ := digits.flatMap (fun a => digits.map (fun b => 55 * a + b))
def leadingPrefix : List ℕ :=
  (digits.filter (fun a => a != 0)).flatMap (fun a => digits.map (fun b => 55 * a + b))

def prefixFloorSum : ℕ :=
  (prefixes.map (fun p => 10^12 / (p + 1))).sum

def tailFloorSum : ℕ :=
  (leadingPrefix.map (fun p => (1155 * 10^12) / (1155 * p + 454))).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem prefixFloorSum_value : prefixFloorSum = 3875802807082 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tailFloorSum_value : tailFloorSum = 913030252293 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact rational lower certificate clears the claimed threshold. -/
theorem lower_certificate_gt :
    (3875802807082 : ℚ) / 10^12 +
      ((913030252293 : ℚ) / 10^12) *
        (∑ j ∈ Finset.range 20, (21 / 55 : ℚ) ^ (j + 1)) +
      1 / 26738 > 443977 / 100000 := by
  norm_num [Finset.sum_range_succ]

end Erdos3Candidate.HarmonicCertificate
