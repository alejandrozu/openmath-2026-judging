import SkeletonB
import DeletedGadget
import UnitPorts

/-! # Corollary B: prescribed-vertex equivalence at degree six

The explicit original L6b is proved pair-free, bipartite, and six-regular. The
unit-deficit port construction is proved simple. Thus the equivalence below
does not assume an avoiding skeleton or the desired graph conclusion.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

namespace DeletedGadget
variable {V : Type*} [DecidableEq V] [Fintype V]
  (B : SimpleGraph V) (c : V → Bool) (o : V)

noncomputable def ports : Finset (Outer c o) := univ.filter (fun y => B.Adj o y.1)

lemma ports_card (hc : ∀ a b, B.Adj a b → c a ≠ c b) (hreg : ∀ v, B.degree v = 6) :
    (ports B c o).card = 6 := by
  have he : (ports B c o).image Subtype.val = B.neighborFinset o := by
    ext v
    constructor
    · intro h
      obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      exact (B.mem_neighborFinset o y.1).mpr (mem_filter.mp hy).2
    · intro h
      have hv := (B.mem_neighborFinset o v).mp h
      refine mem_image.mpr ⟨⟨v,(hc o v hv).symm⟩,?_,rfl⟩
      exact mem_filter.mpr ⟨mem_univ _,hv⟩
  have hh := congrArg Finset.card he
  rw [card_image_of_injective _ Subtype.val_injective,B.card_neighborFinset_eq_degree,hreg] at hh
  exact hh

lemma port_degree (hreg : ∀ v, B.degree v = 6) (y : Outer c o) :
    (graph B c o).degree (Sum.inr y) = 6 - (if y ∈ ports B c o then 1 else 0) := by
  rw [graph_degree,hreg]
  have hm : y ∈ ports B c o ↔ B.Adj o y.1 := by simp [ports]
  by_cases h : B.Adj o y.1
  · have hp := hm.mpr h
    simp [kept,h,hp]
  · have hp : y ∉ ports B c o := fun hy => h (hm.mp hy)
    simp [kept,h,hp]

end DeletedGadget

theorem avoiding_graph_from_deleted_vertex {V : Type*} [DecidableEq V] [Fintype V]
    (B : SimpleGraph V) (c : V → Bool) (o : V)
    (hc : ∀ a b, B.Adj a b → c a ≠ c b) (hreg : ∀ v, B.degree v = 6)
    (hfree : ¬ Erdos585.HasPairF (B.induce {v | v ≠ o})) :
    ∃ G : SimpleGraph (BVertex × (DeletedGadget.Inner c o ⊕ DeletedGadget.Outer c o)),
      Nonempty (BVertex × (DeletedGadget.Inner c o ⊕ DeletedGadget.Outer c o)) ∧
      ¬ Erdos585.HasPairF G ∧ (∀ v, G.degree v = 6) ∧ G.IsBipartite := by
  let Γ := DeletedGadget.graph B c o
  let P := DeletedGadget.ports B c o
  have hcard : P.card = 6 := DeletedGadget.ports_card B c o hc hreg
  let T := UnitPorts.valid Γ skeletonB 6 skeletonB_stars P hcard (by decide)
    (DeletedGadget.port_degree B c o hreg)
  have hΓ := DeletedGadget.gadget B c o hc hreg
  have hΓfree := DeletedGadget.pairfree B c o hfree
  let G := UnitPorts.graph Γ skeletonB 6 skeletonB_stars P hcard (by decide)
  refine ⟨G,?_,T.pairfree hΓ (by decide) hΓfree skeletonB_pairfree,?_,?_⟩
  · obtain ⟨y,hy⟩ := card_pos.mp (by omega : 0 < P.card)
    exact ⟨((0,0),Sum.inr y)⟩
  · intro v
    calc
      G.degree v = @SimpleGraph.degree _ G v (T.locallyFinite v) := by
        exact congrArg (fun inst : Fintype (G.neighborSet v) => @SimpleGraph.degree _ G v inst)
          (Subsingleton.elim _ _)
      _ = 6 := T.regular hΓ v
  · exact T.bipartite hΓ skeletonB_bicolor skeletonB_bipartite

universe u
/-- The finite, nonempty degree-six bipartite statement. Empty regular graphs
are excluded, as required for a meaningful universal cycle-existence claim. -/
def EveryBipartiteSixHasPair : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V] (B : SimpleGraph V),
    (∀ v, B.degree v = 6) → B.IsBipartite → Erdos585.HasPairF B

/-- The stronger statement quantifies each prescribed vertex of the same finite
degree-six bipartite graphs and asks for a pair avoiding that vertex. -/
def EveryBipartiteSixHasPairAvoidingVertex : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V] (B : SimpleGraph V),
    (∀ v, B.degree v = 6) → B.IsBipartite → ∀ o : V,
      Erdos585.HasPairF (B.induce {v | v ≠ o})

theorem prescribed_vertex_equivalence : EveryBipartiteSixHasPair.{u} ↔
    EveryBipartiteSixHasPairAvoidingVertex.{u} := by
  classical
  constructor
  · intro h V _ _ _ B hreg hbip o
    by_contra hfree
    obtain ⟨b⟩ := hbip
    let color : B.Coloring Bool := B.recolorOfEquiv finTwoEquiv b
    obtain ⟨G,hne,hGfree,hGreg,hGbip⟩ := avoiding_graph_from_deleted_vertex B color o
      (fun a b hab => color.valid hab) hreg hfree
    letI := hne
    exact hGfree (h _ G hGreg hGbip)
  · intro h V _ _ _ B hreg hbip
    let o : V := Classical.choice inferInstance
    have hp := h V B hreg hbip o
    exact hp.map (Embedding.induce {v | v ≠ o}).toHom (Embedding.induce (G := B) _).injective

#check avoiding_graph_from_deleted_vertex
#check prescribed_vertex_equivalence
#print axioms avoiding_graph_from_deleted_vertex
#print axioms prescribed_vertex_equivalence
end RobertPublishable.SUB
