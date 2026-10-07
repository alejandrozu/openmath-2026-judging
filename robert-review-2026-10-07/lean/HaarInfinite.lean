/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
This additive review proof extends the finite converse in Robert Huynh's
HaarDegree.lean to arbitrary ambient additive groups. It does not assert
new historical priority for the elementary local-degree argument.
-/
import Openmath.Proofs.HaarGamma

noncomputable section
namespace OpenMathReview.HaarInfinite
open SimpleGraph Finset Erdos585

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

lemma neighborSet_false (S : Finset V) (x : V) :
    (Erdos585.Haar.graph S).neighborSet (x, false) =
      (fun s : V => (x + s, true)) '' (S : Set V) := by
  ext y
  obtain ⟨y, b⟩ := y
  cases b
  · simp [SimpleGraph.neighborSet, Erdos585.Haar.graph]
  · constructor
    · intro h
      have hm : y - x ∈ S := (Erdos585.Haar.graph_cross S x y).mp h
      exact ⟨y - x, hm, by simp⟩
    · rintro ⟨s, hs, h⟩
      have he := congrArg Prod.fst h
      change x + s = y at he
      subst y
      exact (Erdos585.Haar.graph_cross S x (x + s)).mpr (by simpa using hs)

lemma neighborSet_true (S : Finset V) (x : V) :
    (Erdos585.Haar.graph S).neighborSet (x, true) =
      (fun s : V => (x - s, false)) '' (S : Set V) := by
  ext y
  obtain ⟨y, b⟩ := y
  cases b
  · constructor
    · intro h
      have hm : x - y ∈ S := (Erdos585.Haar.graph_cross S y x).mp h.symm
      exact ⟨x - y, hm, by simp⟩
    · rintro ⟨s, hs, h⟩
      have he := congrArg Prod.fst h
      change x - s = y at he
      subst y
      exact ((Erdos585.Haar.graph_cross S (x - s) x).mpr (by simpa using hs)).symm
  · simp [SimpleGraph.neighborSet, Erdos585.Haar.graph]

theorem neighbor_finite (S : Finset V) (x : V × Bool) :
    ((Erdos585.Haar.graph S).neighborSet x).Finite := by
  obtain ⟨x, b⟩ := x
  cases b
  · rw [neighborSet_false]
    exact S.finite_toSet.image _
  · rw [neighborSet_true]
    exact S.finite_toSet.image _

theorem neighbor_ncard (S : Finset V) (x : V × Bool) :
    ((Erdos585.Haar.graph S).neighborSet x).ncard = S.card := by
  obtain ⟨x, b⟩ := x
  cases b
  · rw [neighborSet_false, Set.ncard_image_of_injective _ (fun a b h =>
      add_left_cancel (congrArg Prod.fst h)), Set.ncard_coe_finset]
  · rw [neighborSet_true, Set.ncard_image_of_injective _ (fun a b h =>
      sub_right_injective (congrArg Prod.fst h)), Set.ncard_coe_finset]

/-- Cycle rigidity needs finite cycle supports, not a finite ambient graph. -/
theorem pair_four_neighbors {W : Type*} [DecidableEq W] {G : SimpleGraph W}
    {u v : W} {p : G.Walk u u} {q : G.Walk v v}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (hf : (G.neighborSet u).Finite) : 4 ≤ (G.neighborSet u).ncard := by
  have hu : u ∈ q.support := by
    rw [← List.mem_toFinset, ← hS, List.mem_toFinset]
    exact p.start_mem_support
  have hd : Disjoint (p.toSubgraph.neighborSet u) (q.toSubgraph.neighborSet u) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have he₁ : s(u, x) ∈ p.edges := by
      rw [← Walk.mem_edges_toSubgraph]
      exact p.toSubgraph.mem_edgeSet.mpr hx
    have he₂ : s(u, x) ∈ q.edges := by
      rw [← Walk.mem_edges_toSubgraph]
      exact q.toSubgraph.mem_edgeSet.mpr hy
    exact Finset.disjoint_left.mp hE (List.mem_toFinset.mpr he₁)
      (List.mem_toFinset.mpr he₂)
  have hc : (p.toSubgraph.neighborSet u ∪ q.toSubgraph.neighborSet u).ncard = 4 := by
    rw [Set.ncard_union_eq hd (p.finite_neighborSet_toSubgraph)
      (q.finite_neighborSet_toSubgraph),
      hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support,
      hq.ncard_neighborSet_toSubgraph_eq_two hu]
  rw [← hc]
  exact Set.ncard_le_ncard (by
    intro x hx
    rcases hx with hx | hx
    · exact p.toSubgraph.adj_sub hx
    · exact q.toSubgraph.adj_sub hx) hf

/-- The converse for a finite palette holds even in an infinite ambient group. -/
theorem four_le_card_of_pair (S : Finset V)
    (h : HasTwoEdgeDisjointCyclesSameVertexSet (Erdos585.Haar.graph S)) :
    4 ≤ S.card := by
  obtain ⟨u, v, p, q, hp, hq, hS, hE⟩ := (Erdos585.hasPairF_iff _).mpr h
  have hc := pair_four_neighbors hp hq hS hE (neighbor_finite S u)
  simpa only [neighbor_ncard] using hc

/-- Full classification for every prime-field module, with no Fintype V. -/
theorem hasPair_iff {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] (S : Finset V) :
    HasTwoEdgeDisjointCyclesSameVertexSet (Erdos585.Haar.graph S) ↔ 4 ≤ S.card := by
  constructor
  · exact four_le_card_of_pair S
  · intro h
    exact (Erdos585.hasPairF_iff _).mp
      (Erdos585.HaarClassification.hasPair_of_four (p := p) S h)

#print axioms neighbor_finite
#print axioms neighbor_ncard
#print axioms pair_four_neighbors
#print axioms four_le_card_of_pair
#print axioms hasPair_iff
#check @hasPair_iff
end OpenMathReview.HaarInfinite
