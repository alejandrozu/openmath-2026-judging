import Main
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Faithful d-gadget and valid-simple substitution hypotheses

The two shores and port deficits are the hypotheses of the author's R1.
Neither a projected cycle nor pair-freeness of the substituted graph is assumed.
The ambient skeleton need not have a finite vertex type.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

variable {U E I O : Type*} [DecidableEq U] [DecidableEq E]
  [DecidableEq I] [DecidableEq O] [Fintype I] [Fintype O]

def outerShore : I ⊕ O → Bool := Sum.elim (fun _ => false) (fun _ => true)

/-- The complete finite d-gadget conditions, including the one-vertex surplus. -/
structure Gadget (Γ : SimpleGraph (I ⊕ O)) (d : ℕ) : Prop where
  bipartite : ∀ x y, Γ.Adj x y → outerShore x ≠ outerShore y
  inner_degree : ∀ i, Γ.degree (Sum.inl i) = d
  outer_degree : ∀ o, Γ.degree (Sum.inr o) ≤ d
  surplus : Fintype.card O = Fintype.card I + 1

/-- Individually labelled finite stars, so parallel skeleton edges are counted
separately and the ambient graph can be infinite. -/
structure RegularStars (L : LooplessMultigraph U E) (d : ℕ) where
  star : U → Finset E
  mem_star : ∀ u e, e ∈ star u ↔ u ∈ L.ends e
  card_star : ∀ u, (star u).card = d

/-- A genuine simple graph made of disjoint Γ copies and exactly the skeleton
links; the port-load condition retains the official valid-substitution scope. -/
structure ValidSimpleSubstitution (Γ : SimpleGraph (I ⊕ O))
    (L : LooplessMultigraph U E) (d : ℕ) (G : SimpleGraph (U × (I ⊕ O))) where
  projection : LinkProjection G L Prod.fst
  regularStars : RegularStars L d
  internal : ∀ u x y, G.Adj (u, x) (u, y) ↔ Γ.Adj x y
  links_outer : ∀ e v, v ∈ projection.link e → outerShore v.2 = true
  port_load : ∀ u o,
    ((regularStars.star u).filter fun e => (u, Sum.inr o) ∈ projection.link e).card =
      d - Γ.degree (Sum.inr o)

namespace ValidSimpleSubstitution
variable {Γ : SimpleGraph (I ⊕ O)} {L : LooplessMultigraph U E} {d : ℕ}
  {G : SimpleGraph (U × (I ⊕ O))} (T : ValidSimpleSubstitution Γ L d G)

include T

noncomputable def cut (u : U) : Finset (Sym2 (U × (I ⊕ O))) :=
  (T.regularStars.star u).image T.projection.link

lemma cut_exact (u : U) (z : Sym2 (U × (I ⊕ O))) (hz : z ∈ G.edgeSet) :
    z ∈ T.cut u ↔ Crosses Prod.fst u z := by
  classical
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := mem_image.mp h
    exact (T.projection.incident_iff_crosses u e).mp ((T.regularStars.mem_star u e).mp he)
  · intro h
    obtain ⟨e, he⟩ := T.projection.complete z hz (nonDiag_of_crosses _ u z h)
    refine mem_image.mpr ⟨e, ?_, he⟩
    apply (T.regularStars.mem_star u e).mpr
    apply (T.projection.incident_iff_crosses u e).mpr
    rwa [he]

lemma cut_card (u : U) : (T.cut u).card = d := by
  classical
  rw [cut, card_image_of_injective _ T.projection.injective, T.regularStars.card_star]

lemma internal_shores (hΓ : Gadget Γ d) :
    ∀ a b, G.Adj a b → a.1 = b.1 → outerShore a.2 ≠ outerShore b.2 := by
  rintro ⟨u, x⟩ ⟨v, y⟩ h hcopy
  dsimp at hcopy
  subst v
  exact hΓ.bipartite x y ((T.internal u x y).mp h)

lemma external_shores : ∀ a b, G.Adj a b → a.1 ≠ b.1 →
    outerShore a.2 = true ∧ outerShore b.2 = true := by
  intro a b hab hcopy
  obtain ⟨e, he⟩ := T.projection.complete s(a,b) (G.mem_edgeSet.mpr hab)
    (by simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using hcopy)
  constructor
  · apply T.links_outer e a
    rw [he]
    simp
  · apply T.links_outer e b
    rw [he]
    simp

lemma fibers_pairfree (hΓ : ¬ Erdos585.HasPairF Γ) :
    ∀ u, ¬ Erdos585.HasPairF (G.induce {v | v.1 = u}) := by
  intro u h
  let hom : G.induce {v | v.1 = u} →g Γ :=
    { toFun := fun x => x.1.2
      map_rel' := fun {x y} hxy => by
        have h := (T.internal u x.1.2 y.1.2).mp
        apply h
        have hx : x.1 = (u, x.1.2) := Prod.ext x.2 rfl
        have hy : y.1 = (u, y.1.2) := Prod.ext y.2 rfl
        rw [← hx, ← hy]
        exact hxy }
  apply hΓ (h.map hom ?_)
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact x.2.trans y.2.symm
  · exact hxy

/-- R1, d≤7: every valid simple substitution of a pair-free d-gadget into a
pair-free loopless d-regular multigraph is itself pair-free. The gadget's exact
degree/cardinality/port conditions are retained; all projection work is proved. -/
theorem pairfree (hΓgadget : Gadget Γ d) (hd : d ≤ 7)
    (hΓ : ¬ Erdos585.HasPairF Γ) (hL : ¬ L.HasPair) : ¬ Erdos585.HasPairF G := by
  apply pairfree_of_link_projection T.projection (fun v => outerShore v.2)
    (T.internal_shores hΓgadget) T.external_shores T.cut T.cut_exact
  · intro u
    rw [T.cut_card]
    exact hd
  · exact T.fibers_pairfree hΓ
  · exact hL

#print axioms pairfree

end ValidSimpleSubstitution
end RobertPublishable.SUB
