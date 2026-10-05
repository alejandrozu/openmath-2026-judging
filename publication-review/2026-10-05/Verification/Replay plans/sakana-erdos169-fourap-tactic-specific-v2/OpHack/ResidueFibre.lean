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
Residue-fibre preservation for progression-free sets.

This is reusable infrastructure derived from the standard modular-digit argument,
not a claimed new resolution or competition-credit contribution.
Source context: A. Walker, arXiv:2203.06045, Theorem 1.2.
The variable-fibre generalization is proved here directly.

No `sorry`, additional axioms, native_decide, or computed-data imports.
Compiler status: not checked at the time this file was written.
-/

namespace Erdos3Candidate

/-- Nonconstant integer arithmetic progressions, of exactly `k` indexed terms. -/
def APFree (k : ℕ) (A : Set ℤ) : Prop :=
  ∀ a d : ℤ, d ≠ 0 → ¬ (∀ i : Fin k, a + (i : ℤ) * d ∈ A)

/-- Modular progression freeness includes repeated residues when the step has
small order modulo `b`. Only the step being zero modulo `b` is excluded. -/
def ModularAPFree (k : ℕ) (b : ℤ) (S : Set ℤ) : Prop :=
  ∀ a d : ℤ, ¬ b ∣ d → ¬ (∀ i : Fin k, (a + (i : ℤ) * d) % b ∈ S)

/-- Integer fibre above an arbitrary lift `s` of a residue class. -/
def fibre (b s : ℤ) (A : Set ℤ) : Set ℤ :=
  {t | s + b * t ∈ A}

/-- A modularly progression-free residue support and progression-free fibres
produce a progression-free integer set. Fibre offsets range over all integers,
so there are no hidden canonical-representative or division conventions. -/
theorem apFree_of_modular_support_and_fibres
    (k : ℕ) (b : ℤ) (S A : Set ℤ)
    (hS : ModularAPFree k b S)
    (hSupport : ∀ n ∈ A, n % b ∈ S)
    (hFibre : ∀ s : ℤ, APFree k (fibre b s A)) :
    APFree k A := by
  intro a d hd hAP
  have hdiv : b ∣ d := by
    by_contra hnot
    exact hS a d hnot (fun i => hSupport _ (hAP i))
  obtain ⟨e, he⟩ := hdiv
  have he0 : e ≠ 0 := by
    intro hz
    apply hd
    simpa [hz] using he
  apply hFibre a 0 e he0
  intro i
  change a + b * (0 + (i : ℤ) * e) ∈ A
  convert hAP i using 1 <;> rw [he] <;> ring

end Erdos3Candidate
