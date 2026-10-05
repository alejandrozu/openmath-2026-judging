import FormalConjecturesUtil

/-!
# A conditional route to the exact Erdős 3 hill

The hypothesis below is NOT proved here. It isolates the research obligation:
every set avoiding a fixed progression length at least three must have a
summable reciprocal series. A proof of that obligation would settle the hill.
This file only checks the logical reduction, including its filter formulation.
-/

namespace Erdos3Reduction

/-- Sufficient missing research statement; this definition is not an axiom. -/
def APFreeSummability : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ A : Set ℕ, A.IsAPOfLengthFree k →
    Summable (fun a : A ↦ 1 / (a : ℝ))

/-- Conditional reduction, not an unconditional solution. The hill's default
`answer(sorry)` elaborates to `True`, as checked separately in the image. -/
theorem hill_of_apFreeSummability (h : APFreeSummability) :
    True ↔ ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  constructor
  · intro _ A hdiv
    apply Filter.frequently_atTop.2
    intro n
    refine ⟨max n 3, le_max_left n 3, ?_⟩
    by_contra hNo
    apply hdiv
    apply h (max n 3) (le_max_right n 3) A
    intro S hSA hAP
    exact False.elim (hNo ⟨S, hSA, hAP⟩)
  · intro _
    trivial

#check hill_of_apFreeSummability
#print axioms hill_of_apFreeSummability

end Erdos3Reduction
