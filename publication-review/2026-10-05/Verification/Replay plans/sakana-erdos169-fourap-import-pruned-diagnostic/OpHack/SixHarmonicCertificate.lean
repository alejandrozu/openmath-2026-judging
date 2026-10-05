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

/-! Closed exact arithmetic for the six-fibre > 111/25 candidate.
The structural and finite harmonic-mean bridges are separate obligations.
No holes, native_decide, or additional axioms. Compilation pending. -/
namespace Erdos3Candidate.SixHarmonicCertificate

def digits : List ℕ :=
  [0, 1, 2, 4, 5, 9, 10, 11, 14, 16, 17, 18, 21, 24, 30, 37, 39, 41, 42, 45, 47]
def lowExtensions : List ℕ := [26286, 26726, 26737]
def highExtensions : List ℕ := [120061, 120501, 120512]
def extensions : List ℕ := lowExtensions ++ highExtensions

def newPrefixFloor : ℕ :=
  (extensions.flatMap (fun u => digits.map
    (fun d => 10^15 / (166375*d+u+1)))).sum

def newTailFloor : ℕ :=
  (lowExtensions.flatMap (fun u => (digits.filter (fun d => d != 0)).map
    (fun d => (1134*10^15) / (166375*(1134*d+433))))).sum +
  (highExtensions.flatMap (fun u => (digits.filter (fun d => d != 0)).map
    (fun d => (1155*10^15) / (166375*(1155*d+433)+21*(u+1))))).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem newPrefixFloor_value : newPrefixFloor = 222203111618 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem newTailFloor_value : newTailFloor = 84819414442 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem six_lower_certificate_gt :
    ((3875802807082000 + 222203111618 : ℚ) / 10^15) +
      ((913030252293000 + 84819414442 : ℚ) / 10^15) *
        (∑ j ∈ Finset.range 20, (21 / 55 : ℚ)^(j+1)) > 111 / 25 := by
  norm_num [Finset.sum_range_succ]

end Erdos3Candidate.SixHarmonicCertificate
