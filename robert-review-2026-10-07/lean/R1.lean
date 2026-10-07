import Regularity

/-! # The complete original gadget substitution theorem R1

All graph conclusions are derived from the valid-simple construction data.
This statement retains the exact finite gadget hypotheses while allowing an
infinite, locally finite skeleton with finite labelled stars.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

theorem theorem_R1 {U E I O : Type*} [DecidableEq U] [DecidableEq E]
    [DecidableEq I] [DecidableEq O] [Fintype I] [Fintype O]
    {Γ : SimpleGraph (I ⊕ O)} {L : LooplessMultigraph U E} {d : ℕ}
    {G : SimpleGraph (U × (I ⊕ O))} (T : ValidSimpleSubstitution Γ L d G)
    (hΓgadget : Gadget Γ d) (hd : d ≤ 7)
    (hΓ : ¬ Erdos585.HasPairF Γ) (hL : ¬ L.HasPair) :
    ¬ Erdos585.HasPairF G ∧
      @SimpleGraph.IsRegularOfDegree _ G T.locallyFinite d ∧
      ((∃ c, ValidSimpleSubstitution.SkeletonBicoloring L c) → G.IsBipartite) := by
  refine ⟨T.pairfree hΓgadget hd hΓ hL,T.regular hΓgadget,?_⟩
  rintro ⟨c,hc⟩
  exact T.bipartite hΓgadget c hc

#check theorem_R1
#print axioms theorem_R1
end RobertPublishable.SUB
