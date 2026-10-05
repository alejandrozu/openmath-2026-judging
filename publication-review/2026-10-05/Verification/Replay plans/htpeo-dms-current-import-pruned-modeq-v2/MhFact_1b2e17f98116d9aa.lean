-- Lean proof of fact 1b2e17f98116d9aa (RH2F.layer37a); added by fact_submit, do not edit
import MhFact_66a4a19c81528d5b
set_option backward.isDefEq.respectTransparency false

/-
  Layer 37a — ROOT-CS4 in Lean with the finite hypotheses BASE12, SIMPLE14, B14D and the leaf case (II_D) on at most
  14 vertices discharged (layers 32d and 35).
-/

namespace RH2F
open MGraph

/-- (II_D) restricted to hosts with at least 16 vertices -/
def IID16 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 16 ≤ vcount P → TwoCutReducedOn P → ∀ g, P g →
    (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) → (∀ S, TwoCut P S → ¬ Crosses P S g) →
    Colourable (leafSet P g) 6

/-- (II_D) from its part on at least 16 vertices -/
theorem iid_of_iid16 (h : IID16) : IID := by
  intro X P hG h6 h2 g hg hpar hcut
  by_cases h14 : vcount P ≤ 14
  · exact layer35.2.2 X P hG h6 h14 h2 g hg hpar hcut
  · have hev := vcount_even' hG
    exact h X P hG (by omega) h2 g hg hpar hcut

/-- **layer 37a** -/
theorem layer37a :
    BASE12 ∧ SIMPLE14 ∧ B14D ∧ (IID16 → IID) ∧
    (FEEXTD10 → FEEXISTD10 → POLE → TDTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD10 → WEXT → TDLTRI → IID16 → DMS) :=
  ⟨base12, simple14, b14d, iid_of_iid16,
   fun hext hex hpole htd hD =>
     layer28.2.1 base12 simple14 b14d hext hex hpole htd (iid_of_iid16 hD),
   fun hext hex hW htdl hD =>
     layer28.2.2 base12 simple14 b14d hext hex hW htdl (iid_of_iid16 hD)⟩

end RH2F
