import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast
import Lean.Linter.ConstructorAsVariable
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
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
Independent finite certificates for the base-55 singleton 26737.

UNCOMPILED CANDIDATE: no claim of kernel checking is made by this source.
Every proof is ordinary `decide`; no `native_decide`, axioms, or sorry.
The generic digit-lifting and reciprocal-sum theorems are separate obligations.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace ErdosSingletonIndependent

def D : Finset ℕ :=
  {0, 1, 2, 4, 5, 9, 10, 11, 14, 16, 17, 18, 21, 24,
   30, 37, 39, 41, 42, 45, 47}

def badBasePairs : Finset (ℕ × ℕ) :=
  ((Finset.range 55).product (Finset.Icc 1 54)).filter fun ad =>
    ad.1 ∈ D ∧ (ad.1 + ad.2) % 55 ∈ D ∧
      (ad.1 + 2 * ad.2) % 55 ∈ D ∧
      (ad.1 + 3 * ad.2) % 55 ∈ D

theorem base_modular_four_free : badBasePairs = ∅ := by decide

def endpointCandidates : Finset ℕ :=
  (Finset.range 55).filter fun t =>
    (7 + t) % 55 ∈ D ∧ (7 + 2 * t) % 55 ∈ D ∧
      (7 + 3 * t) % 55 ∈ D

theorem endpoint_exclusion : endpointCandidates = ∅ := by decide

/-- Each candidate t is below 55, so u+55-t implements u-t modulo 55
    without truncated-subtraction underflow, for all offsets used below. -/
def middleCandidates (u v w : ℕ) : Finset ℕ :=
  (Finset.range 55).filter fun t =>
    (u + 55 - t) % 55 ∈ D ∧ (v + t) % 55 ∈ D ∧
      (w + 2 * t) % 55 ∈ D

theorem units_candidates :
    middleCandidates 7 7 7 = {2, 7, 17, 32, 52} := by decide

theorem tens_for_units_2_or_7 :
    middleCandidates 46 46 46 = {9, 25} := by decide

theorem tens_for_units_17 :
    middleCandidates 45 46 46 = {27} := by decide

theorem tens_for_units_32 :
    middleCandidates 45 46 47 = ∅ := by decide

theorem tens_for_units_52 :
    middleCandidates 45 47 48 = {8, 24} := by decide

theorem third_digit_exclusion :
    middleCandidates 8 9 9 = ∅ := by decide

def lowerCandidates : Finset ℕ := {492, 497, 502, 1372, 1377, 1382, 1502}

theorem lower_candidates_arithmetic :
    ({2 + 55 * 9, 2 + 55 * 25, 7 + 55 * 9, 7 + 55 * 25,
      17 + 55 * 27, 52 + 55 * 8, 52 + 55 * 24} : Finset ℕ)
      = lowerCandidates := by decide

theorem third_digit_offsets :
    ∀ d ∈ lowerCandidates,
      (26737 - d) / 3025 = 8 ∧
      (26737 + d) / 3025 = 9 ∧
      (26737 + 2 * d) / 3025 = 9 := by decide

theorem tens_offsets :
    ((26737 - 2) / 55 % 55, (26737 + 2) / 55 % 55,
      (26737 + 2 * 2) / 55 % 55) = (46, 46, 46) ∧
    ((26737 - 7) / 55 % 55, (26737 + 7) / 55 % 55,
      (26737 + 2 * 7) / 55 % 55) = (46, 46, 46) ∧
    ((26737 - 17) / 55 % 55, (26737 + 17) / 55 % 55,
      (26737 + 2 * 17) / 55 % 55) = (45, 46, 46) ∧
    ((26737 - 32) / 55 % 55, (26737 + 32) / 55 % 55,
      (26737 + 2 * 32) / 55 % 55) = (45, 46, 47) ∧
    ((26737 - 52) / 55 % 55, (26737 + 52) / 55 % 55,
      (26737 + 2 * 52) / 55 % 55) = (45, 47, 48) := by decide

theorem new_point_digits :
    26737 % 55 = 7 ∧ 26737 / 55 % 55 = 46 ∧
      26737 / 3025 = 8 ∧ 26737 % 55 ∉ D := by decide

theorem base_size_and_sum : D.card = 21 ∧ ∑ d ∈ D, d = 433 := by decide

end ErdosSingletonIndependent
