import Projection

/-! # Pair-freeness under valid simple gadget substitution

This proof contracts genuine cycle edges to the individually labelled skeleton.
The connected, two-regular skeleton cycles are conclusions, not hypotheses.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

variable {V U E : Type*} [DecidableEq V] [DecidableEq U] [DecidableEq E]
  {G : SimpleGraph V} {L : LooplessMultigraph U E} {copy : V → U}

lemma pair_in_fiber {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (u : U) (hps : ∀ x ∈ p.support, copy x = u) :
    Erdos585.HasPairF (G.induce {x | copy x = u}) := by
  have hps' : ∀ x ∈ p.support, x ∈ {x | copy x = u} := hps
  have hqs : ∀ x ∈ q.support, x ∈ {x | copy x = u} := by
    intro x hx
    apply hps
    rwa [← List.mem_toFinset, hS, List.mem_toFinset]
  have hpair := (Erdos585.pair_map_iff (Embedding.induce {x | copy x = u}).toHom
    (Embedding.induce (G := G) _).injective (p.induce _ hps') (q.induce _ hqs)).1
    (by rw [Walk.map_induce, Walk.map_induce]; exact ⟨hp, hq, hS, hE⟩)
  exact ⟨_, _, _, _, hpair⟩

/-- The main contraction argument, including genuine projected connectivity.
Every edge between copies is individually represented by the loopless skeleton;
the at-most-seven incident edges are a cut, not an assumed projected circuit. -/
theorem pairfree_of_link_projection (P : LinkProjection G L copy) (outer : V → Bool)
    (hinternal : ∀ a b, G.Adj a b → copy a = copy b → outer a ≠ outer b)
    (hexternal : ∀ a b, G.Adj a b → copy a ≠ copy b → outer a = true ∧ outer b = true)
    (cuts : U → Finset (Sym2 V))
    (hcuts : ∀ u e, e ∈ G.edgeSet → (e ∈ cuts u ↔ Crosses copy u e))
    (hsizes : ∀ u, (cuts u).card ≤ 7)
    (hfibers : ∀ u, ¬ Erdos585.HasPairF (G.induce {x | copy x = u}))
    (hskeleton : ¬ L.HasPair) : ¬ Erdos585.HasPairF G := by
  classical
  rintro ⟨a, b, p, q, hp, hq, hS, hE⟩
  have hpass : ∀ u ∈ p.support.toFinset.image copy,
      (p.edges.toFinset.filter (Crosses copy u)).card = 2 ∧
      (q.edges.toFinset.filter (Crosses copy u)).card = 2 := by
    intro u hu
    obtain ⟨x, hx, hxu⟩ := mem_image.mp hu
    have h := single_passage copy outer u hinternal hexternal (cuts u)
      (hcuts u) (hsizes u) hp hq hS hE ⟨x, List.mem_toFinset.mp hx, hxu⟩
    rcases h with hlocal | hpass
    · exact False.elim (hfibers u (pair_in_fiber hp hq hS hE u hlocal))
    · exact hpass
  have hpc := P.projected_cycle p hp (fun u hu => (hpass u hu).1)
  have hqc := P.projected_cycle q hq (fun u hu => (hpass u (by rwa [hS])).2)
  apply hskeleton
  refine ⟨p.support.toFinset.image copy, P.projectedEdges p, P.projectedEdges q,
    hpc, ?_, P.projected_disjoint p q hE⟩
  simpa [hS] using hqc

#print axioms pairfree_of_link_projection

end RobertPublishable.SUB
