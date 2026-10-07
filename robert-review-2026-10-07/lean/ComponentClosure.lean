import HaarInfinite
import Openmath.Proofs.SmallExact

/-!
# A pair exhausts its component in a locally finite four-regular graph

The common finite support is proved edge-closed from the actual two cycles.
No component-closure or Hamilton-decomposition assumption is introduced.
-/

noncomputable section

namespace RobertPublishable.HaarComponent

open SimpleGraph Erdos585

variable {W : Type*} [DecidableEq W] {G : SimpleGraph W}
  {u v : W} {p : G.Walk u u} {q : G.Walk v v}

theorem cycle_neighbors_disjoint (hE : Disjoint p.edges.toFinset q.edges.toFinset) (x : W) :
    Disjoint (p.toSubgraph.neighborSet x) (q.toSubgraph.neighborSet x) := by
  rw [Set.disjoint_left]
  intro y hyP hyQ
  have heP : s(x, y) ∈ p.edges := Walk.adj_toSubgraph_iff_mem_edges.mp hyP
  have heQ : s(x, y) ∈ q.edges := Walk.adj_toSubgraph_iff_mem_edges.mp hyQ
  exact Finset.disjoint_left.mp hE (List.mem_toFinset.mpr heP) (List.mem_toFinset.mpr heQ)

theorem cycle_neighbor_union_eq (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (x : W) (hx : x ∈ p.support) (hf : (G.neighborSet x).Finite)
    (hdegree : (G.neighborSet x).ncard = 4) :
    p.toSubgraph.neighborSet x ∪ q.toSubgraph.neighborSet x = G.neighborSet x := by
  have hxQ : x ∈ q.support := by
    rw [← List.mem_toFinset, ← hS, List.mem_toFinset]
    exact hx
  have hcard : (p.toSubgraph.neighborSet x ∪ q.toSubgraph.neighborSet x).ncard = 4 := by
    rw [Set.ncard_union_eq (cycle_neighbors_disjoint hE x)
      p.finite_neighborSet_toSubgraph q.finite_neighborSet_toSubgraph,
      hp.ncard_neighborSet_toSubgraph_eq_two hx,
      hq.ncard_neighborSet_toSubgraph_eq_two hxQ]
  apply Set.eq_of_subset_of_ncard_le _ (by rw [hdegree, hcard]) hf
  intro y hy
  rcases hy with hy | hy
  · exact p.toSubgraph.adj_sub hy
  · exact q.toSubgraph.adj_sub hy

theorem pair_support_edge_closed (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (hf : ∀ x, (G.neighborSet x).Finite) (hdegree : ∀ x, (G.neighborSet x).ncard = 4) :
    ∀ ⦃x y⦄, x ∈ p.support → G.Adj x y → y ∈ p.support := by
  intro x y hx hxy
  have hy : y ∈ p.toSubgraph.neighborSet x ∪ q.toSubgraph.neighborSet x := by
    rw [cycle_neighbor_union_eq hp hq hS hE x hx (hf x) (hdegree x)]
    exact hxy
  rcases hy with hy | hy
  · exact p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts x hy)
  · have hyQ : y ∈ q.support :=
      q.mem_verts_toSubgraph.mp (q.toSubgraph.neighborSet_subset_verts x hy)
    rw [← List.mem_toFinset, hS, List.mem_toFinset]
    exact hyQ

theorem pair_support_eq_component (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (hf : ∀ x, (G.neighborSet x).Finite) (hdegree : ∀ x, (G.neighborSet x).ncard = 4) :
    (p.support.toFinset : Set W) = (G.connectedComponentMk u).supp := by
  ext x
  constructor
  · intro hx
    have hxP : x ∈ p.support := List.mem_toFinset.mp hx
    exact ConnectedComponent.sound (p.takeUntil x hxP).reachable.symm
  · intro hx
    have hr : G.Reachable u x :=
      (G.connectedComponentMk u).reachable_of_mem_supp
        (ConnectedComponent.connectedComponentMk_mem (v := u)) hx
    rw [reachable_iff_reflTransGen] at hr
    clear hx
    have hxP : x ∈ p.support := by
      induction hr with
      | refl => exact p.start_mem_support
      | @tail y z _ hyz ih => exact pair_support_edge_closed hp hq hS hE hf hdegree ih hyz
    exact List.mem_toFinset.mpr hxP

theorem pair_edges_exhaust_component (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (hf : ∀ x, (G.neighborSet x).Finite) (hdegree : ∀ x, (G.neighborSet x).ncard = 4) :
    ∀ ⦃x y⦄, x ∈ (G.connectedComponentMk u).supp → G.Adj x y →
      s(x, y) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
  intro x y hx hxy
  have hxP : x ∈ p.support := by
    rw [← pair_support_eq_component hp hq hS hE hf hdegree] at hx
    exact List.mem_toFinset.mp hx
  have hy : y ∈ p.toSubgraph.neighborSet x ∪ q.toSubgraph.neighborSet x := by
    rw [cycle_neighbor_union_eq hp hq hS hE x hxP (hf x) (hdegree x)]
    exact hxy
  rcases hy with hy | hy
  · exact Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr
      (Walk.adj_toSubgraph_iff_mem_edges.mp hy)))
  · exact Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr
      (Walk.adj_toSubgraph_iff_mem_edges.mp hy)))

/-- A component decomposition consists of actual cycles with precisely the
component support, disjoint edge sets, and every incident component edge. -/
def HamiltonDecomposesComponent (G : SimpleGraph W) (C : G.ConnectedComponent) : Prop :=
  ∃ (u v : W) (p : G.Walk u u) (q : G.Walk v v),
    p.IsCycle ∧ q.IsCycle ∧ (p.support.toFinset : Set W) = C.supp ∧
    (q.support.toFinset : Set W) = C.supp ∧
    Disjoint p.edges.toFinset q.edges.toFinset ∧
    ∀ ⦃x y⦄, x ∈ C.supp → G.Adj x y → s(x, y) ∈ p.edges.toFinset ∪ q.edges.toFinset

#print axioms cycle_neighbors_disjoint
#print axioms cycle_neighbor_union_eq
#print axioms pair_support_edge_closed
#print axioms pair_support_eq_component
#print axioms pair_edges_exhaust_component
#check @HamiltonDecomposesComponent

end RobertPublishable.HaarComponent
