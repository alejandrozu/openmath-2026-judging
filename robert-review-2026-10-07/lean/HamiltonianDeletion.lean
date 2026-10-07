import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# A graph-semantic bridge for the BM-2 argument

This file proves only the deterministic implication from an actual Hamilton cycle
and Hamiltonicity of its edge-deleted graph to two edge-disjoint Hamilton cycles.
It does not establish the spectral or expansion Hamiltonicity premise of BM.
The pair predicate below has exactly the walk, support and edge semantics of the
public Erdős 585 target; no conjecture declarations are imported.
-/

namespace RobertPublishable.BM

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual same-support, edge-disjoint cycle predicate, expressed with walks. -/
def HasPair (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u u) (q : G.Walk v v),
    p.IsCycle ∧ q.IsCycle ∧
    {w | w ∈ p.support} = {w | w ∈ q.support} ∧ List.Disjoint p.edges q.edges

/-- A pair whose two cycles each visit every vertex of the ambient graph. -/
def HasTwoHamiltonianCycles (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u u) (q : G.Walk v v),
    p.IsHamiltonianCycle ∧ q.IsHamiltonianCycle ∧ List.Disjoint p.edges q.edges

theorem hasPair_of_twoHamiltonianCycles {G : SimpleGraph V}
    (h : HasTwoHamiltonianCycles G) : HasPair G := by
  obtain ⟨u, v, p, q, hp, hq, hd⟩ := h
  refine ⟨u, v, p, q, hp.isCycle, hq.isCycle, ?_, hd⟩
  ext w
  exact ⟨fun _ => hq.mem_support w, fun _ => hp.mem_support w⟩

/-- The edge-deleted graph supplies a second cycle on exactly the same vertices.
The explicit remainder premise is essential and is not proved by this bridge. -/
theorem twoHamiltonianCycles_of_hamiltonian_remainder [Nontrivial V]
    {G : SimpleGraph V} {u : V} (p : G.Walk u u)
    (hp : p.IsHamiltonianCycle)
    (hrem : (G.deleteEdges {e | e ∈ p.edges}).IsHamiltonian) :
    HasTwoHamiltonianCycles G := by
  obtain ⟨v, q, hq⟩ := hrem Fintype.one_lt_card.ne'
  let qG : G.Walk v v := q.mapLe (G.deleteEdges_le {e | e ∈ p.edges})
  refine ⟨u, v, p, qG, hp, ?_, ?_⟩
  · exact hq.map Function.bijective_id
  · apply List.disjoint_left.mpr
    intro e hep heq
    have heq' : e ∈ q.edges := by
      simpa only [qG, SimpleGraph.Walk.edges_mapLe_eq_edges] using heq
    have hed := q.edges_subset_edgeSet heq'
    rw [SimpleGraph.edgeSet_deleteEdges] at hed
    exact hed.2 hep

/-- A property sufficient for one Hamilton cycle and preserved by deleting that
cycle is sufficient for two. All graph and Hamiltonicity premises are explicit. -/
theorem twoHamiltonianCycles_of_preserved_criterion [Nontrivial V]
    (criterion : SimpleGraph V → Prop)
    (forces : ∀ H, criterion H → H.IsHamiltonian)
    (preserved : ∀ (H : SimpleGraph V) (u : V) (p : H.Walk u u),
      criterion H → p.IsHamiltonianCycle → criterion (H.deleteEdges {e | e ∈ p.edges}))
    {G : SimpleGraph V} (hG : criterion G) : HasTwoHamiltonianCycles G := by
  obtain ⟨u, p, hp⟩ := forces G hG Fintype.one_lt_card.ne'
  exact twoHamiltonianCycles_of_hamiltonian_remainder p hp
    (forces _ (preserved G u p hG hp))

theorem hasPair_of_preserved_criterion [Nontrivial V]
    (criterion : SimpleGraph V → Prop)
    (forces : ∀ H, criterion H → H.IsHamiltonian)
    (preserved : ∀ (H : SimpleGraph V) (u : V) (p : H.Walk u u),
      criterion H → p.IsHamiltonianCycle → criterion (H.deleteEdges {e | e ∈ p.edges}))
    {G : SimpleGraph V} (hG : criterion G) : HasPair G :=
  hasPair_of_twoHamiltonianCycles
    (twoHamiltonianCycles_of_preserved_criterion criterion forces preserved hG)

#print axioms hasPair_of_twoHamiltonianCycles
#print axioms twoHamiltonianCycles_of_hamiltonian_remainder
#print axioms twoHamiltonianCycles_of_preserved_criterion
#print axioms hasPair_of_preserved_criterion

end RobertPublishable.BM
