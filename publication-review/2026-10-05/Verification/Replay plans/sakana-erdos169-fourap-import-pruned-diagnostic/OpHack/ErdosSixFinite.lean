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
Compact exact certificates for the six-residue extension modulo 55^3.

UNCOMPILED CANDIDATE. Standard kernel-reduced `decide` only; no native_decide,
axioms or sorry. This file supplies the exhaustive small arithmetic facts.
The ordinary complete assembly proof is SIX_FIBRE_REVIEW.md. Formal assembly
(digit carry completeness, modular inverses, and the old digit-descent theorem)
must still be completed before claiming the joint ModularAPFree theorem.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace ErdosSixIndependent

def D : Finset ℕ :=
  {0, 1, 2, 4, 5, 9, 10, 11, 14, 16, 17, 18, 21, 24,
   30, 37, 39, 41, 42, 45, 47}

def U : Finset ℕ := {26286, 26726, 26737, 120061, 120501, 120512}

abbrev M : ℕ := 166375

abbrev oldTwo (x : ℕ) : Prop := x % 55 ∈ D ∧ x / 55 % 55 ∈ D
abbrev oldThree (x : ℕ) : Prop := oldTwo x ∧ x / 3025 % 55 ∈ D
abbrev allowed (x : ℕ) : Prop := oldThree x ∨ x ∈ U

def unitsCandidates (x : ℕ) : List ℕ :=
  (List.range 55).filter fun t => decide
    ((x + 55 - t) % 55 ∈ D ∧ (x + t) % 55 ∈ D ∧
      (x + 2 * t) % 55 ∈ D)

def twoCandidates (x : ℕ) : List ℕ :=
  let lifted := (unitsCandidates (x % 55)).flatMap fun d =>
    (List.range 55).map fun t => d + 55 * t
  lifted.filter fun d => decide
    (oldTwo ((x + 3025 - d) % 3025) ∧
     oldTwo ((x + d) % 3025) ∧ oldTwo ((x + 2 * d) % 3025))

theorem units_7 : unitsCandidates 7 = [2, 7, 17, 32, 52] := by decide
theorem units_51 : unitsCandidates 51 = [4, 9, 14, 34, 49] := by decide

theorem two_candidates_2086 :
    twoCandidates 2086 = [1049, 1489, 1544, 1054, 1494, 1549,
      1059, 1499, 1554] := by decide

theorem two_candidates_2526 :
    twoCandidates 2526 = [1489, 1494, 1499] := by decide

theorem two_candidates_2537 :
    twoCandidates 2537 = [497, 1377, 502, 1382, 1502, 492, 1372] := by decide

def endpointCandidates (x : ℕ) : Finset ℕ :=
  (Finset.range 55).filter fun t =>
    (x + t) % 55 ∈ D ∧ (x + 2 * t) % 55 ∈ D ∧ (x + 3 * t) % 55 ∈ D

theorem endpoint_7 : endpointCandidates 7 = ∅ := by decide
theorem endpoint_51 : endpointCandidates 51 = ∅ := by decide

def thirdCandidates (z : ℕ) : Finset ℕ :=
  (Finset.range 55).filter fun t =>
    (z + 55 - t) % 55 ∈ D ∧ (z + 1 + t) % 55 ∈ D ∧
      (z + 1 + 2 * t) % 55 ∈ D

theorem third_8 : thirdCandidates 8 = ∅ := by decide
theorem third_39 : thirdCandidates 39 = ∅ := by decide

theorem new_residue_data :
    ∀ u ∈ U,
      u < M ∧ ¬oldThree u ∧
      (u % 55 = 7 ∨ u % 55 = 51) ∧
      (u % 3025 = 2086 ∨ u % 3025 = 2526 ∨ u % 3025 = 2537) ∧
      (u / 3025 = 8 ∨ u / 3025 = 39) := by decide

/-- Every surviving low-two-digit difference produces the same carry triple.
    The subtraction here is safe: every displayed d is less than every u. -/
theorem third_offsets :
    ∀ u ∈ U, ∀ d ∈ twoCandidates (u % 3025),
      d < u ∧
      (u - d) / 3025 = u / 3025 ∧
      (u + d) / 3025 = u / 3025 + 1 ∧
      (u + 2 * d) / 3025 = u / 3025 + 1 := by decide

def inverseGap : ℕ → ℕ
  | 1 => 1
  | 2 => 83188
  | 3 => 110917
  | _ => 0

theorem gap_inverses :
    (1 * inverseGap 1) % M = 1 ∧
    (2 * inverseGap 2) % M = 1 ∧
    (3 * inverseGap 3) % M = 1 := by decide

def pairDifference (u v i j : ℕ) : ℕ :=
  ((v + M - u) * inverseGap (j - i)) % M

def pairStart (u v i j : ℕ) : ℕ :=
  (u + 4 * M - i * pairDifference u v i j) % M

def pairTerm (u v i j k : ℕ) : ℕ :=
  (pairStart u v i j + k * pairDifference u v i j) % M

/-- Only 6*5*6=180 genuinely active cases. The other branches are trivial
    implications. All membership tests use the JOINT enlarged alphabet. -/
theorem two_new_exclusion :
    ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      ∀ i j : Fin 4, i < j →
        ¬ (∀ k : Fin 4, allowed (pairTerm u v i.val j.val k.val)) := by decide

theorem pair_data :
    ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      ∀ i j : Fin 4, i < j →
        0 < pairDifference u v i.val j.val ∧
        pairTerm u v i.val j.val i.val = u ∧
        pairTerm u v i.val j.val j.val = v := by decide

end ErdosSixIndependent
