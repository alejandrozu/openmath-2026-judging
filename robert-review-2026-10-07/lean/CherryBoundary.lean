import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# A missing nonvacuity clause in the literal cherry lemma

The report's isolated Lemma Ch allows degree cap zero and empty shore sets.
Its hypotheses are then true even for a request for one cherry. The main BM
application has positive degree, so this boundary defect does not refute BM.
-/

namespace RobertPublishable.BM

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def HasCherry (G : SimpleGraph V) (P Q : Finset V) : Prop :=
  ∃ x y z, x ∈ P ∧ y ∈ Q ∧ z ∈ P ∧ x ≠ z ∧ G.Adj x y ∧ G.Adj y z

/-- A nonempty ambient graph with no edges is a counterexample to the isolated
lemma with d=0, theta=2, r=1 and both proposed shores empty. -/
theorem vacuous_zero_degree_cherry_counterexample :
    (∀ v : Fin 1, (⊥ : SimpleGraph (Fin 1)).degree v ≤ 0) ∧
    (∀ y ∈ (∅ : Finset (Fin 1)),
      2 ≤ ((∅ : Finset (Fin 1)).filter ((⊥ : SimpleGraph (Fin 1)).Adj y)).card) ∧
    (2 - 1) * (∅ : Finset (Fin 1)).card ≥ 3 * 1 * 0 ∧
    ¬ HasCherry (⊥ : SimpleGraph (Fin 1)) ∅ ∅ := by
  simp [HasCherry]

/-- With an actual centre and two distinct neighbours, there really is a
three-vertex path. The nonvacuity premise is visible in the conclusion's witness. -/
theorem hasCherry_of_two_neighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    (P Q : Finset V) (y : V) (hy : y ∈ Q)
    (htwo : 2 ≤ (P.filter (G.Adj y)).card) : HasCherry G P Q := by
  have hcard : 1 < (P.filter (G.Adj y)).card := by omega
  obtain ⟨x, hx, z, hz, hxz⟩ := one_lt_card.mp hcard
  obtain ⟨hxP, hxy⟩ := mem_filter.mp hx
  obtain ⟨hzP, hyz⟩ := mem_filter.mp hz
  exact ⟨x, y, z, hxP, hy, hzP, hxz, hxy.symm, hyz⟩

theorem hasCherry_of_nonempty_centres {G : SimpleGraph V} [DecidableRel G.Adj]
    (P Q : Finset V) (hQ : Q.Nonempty)
    (hneigh : ∀ y ∈ Q, 2 ≤ (P.filter (G.Adj y)).card) : HasCherry G P Q := by
  obtain ⟨y, hy⟩ := hQ
  exact hasCherry_of_two_neighbors P Q y hy (hneigh y hy)

#print axioms vacuous_zero_degree_cherry_counterexample
#print axioms hasCherry_of_two_neighbors
#print axioms hasCherry_of_nonempty_centres

end RobertPublishable.BM
