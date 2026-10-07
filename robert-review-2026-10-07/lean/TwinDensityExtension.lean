/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.

An additive density corollary using the frozen actual twin-incidence interfaces.
The zero-sum selection and subdivided-double lifting are known ingredients.
This source is prepared for root review and has not been compiled by its editor.
-/
import Openmath.Proofs.TwinNoSingleton

/-! # The singleton-free twin criterion throughout the density range -/

noncomputable section
namespace OpenMathReview.TwinDensityExtension
open SimpleGraph Finset Erdos585
open Erdos585.TwinCoreForcing

section Grouped
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R]

/-- The inequality version still balances the two shores, without any sparsity premise. -/
theorem grouped_balance_dense (J : Finset (I × R)) (k : I → ℕ)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hdense : 3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R) ≤
      (groupedGraph J k).edgeFinset.card + 2) :
    (∑ i, k i) = Fintype.card R := by
  have hL := isBipartiteWith_sum_degrees_eq_card_edges (groupedGraph_bipartite J k)
  have hR := isBipartiteWith_sum_degrees_eq_card_edges' (groupedGraph_bipartite J k)
  simp only [sum_map] at hL hR
  change (∑ x : (Σ i, Fin (k i)), (groupedGraph J k).degree (.inl x)) = _ at hL
  change (∑ r : R, (groupedGraph J k).degree (.inr r)) = _ at hR
  have hL' := sum_le_sum (s := (univ : Finset (Σ i, Fin (k i))))
    (fun x _ => hmax (.inl x))
  have hR' := sum_le_sum (s := (univ : Finset R)) (fun r _ => hmax (.inr r))
  rw [hL] at hL'
  rw [hR] at hR'
  simp only [sum_const, card_univ, smul_eq_mul, Fintype.card_sigma, Fintype.card_fin]
    at hL' hR'
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at hdense
  omega

/-- Above the exact critical count, a singleton-free represented host is six-regular
on the left: its weighted degree deficit is at most one, but every group weighs at least two. -/
theorem grouped_full_degree_of_strict_dense (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hdense : 3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R) ≤
      (groupedGraph J k).edgeFinset.card + 2)
    (hnot : (groupedGraph J k).edgeFinset.card + 2 ≠
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    ∀ i, (univ.filter (fun r => (i, r) ∈ J)).card = 6 := by
  have hbal := grouped_balance_dense J k hmax hdense
  obtain ⟨hleft, _⟩ := groupedGraph_quotient_caps J k hk hmax
  have hl : ∀ i, (univ.filter (fun r => (i, r) ∈ J)).card ≤ 6 := by
    intro i
    simpa only [card_filter_fst] using hleft i
  let d : I → ℕ := fun i => 6 - (univ.filter (fun r => (i, r) ∈ J)).card
  have hs : (∑ i, k i * d i) + (groupedGraph J k).edgeFinset.card = 6 * ∑ i, k i := by
    rw [groupedGraph_edge_card, ← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    change k i * (6 - (univ.filter (fun r => (i, r) ∈ J)).card) +
      k i * (univ.filter (fun r => (i, r) ∈ J)).card = 6 * k i
    rw [← Nat.mul_add, Nat.sub_add_cancel (hl i), Nat.mul_comm]
  have hdle : (∑ i, k i * d i) ≤ 1 := by
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at hdense hnot
    rw [hbal] at hs hdense hnot
    omega
  intro i
  have hi : k i * d i ≤ 1 :=
    (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hdle
  have hi' : 2 * d i ≤ 1 := (Nat.mul_le_mul_right (d i) (hk i)).trans hi
  have hz : d i = 0 := by omega
  dsimp [d] at hz
  have hh := hl i
  omega

theorem incidence_budget_of_full_degree (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, k i ≤ 3) (hbal : (∑ i, k i) = Fintype.card R)
    (hfull : ∀ i, (univ.filter (fun r => (i, r) ∈ J)).card = 6) :
    3 * Fintype.card I + Fintype.card R ≤ J.card := by
  have hJ : J.card = 6 * Fintype.card I := by
    rw [← sum_left_card]
    simp [hfull, Nat.mul_comm]
  have hr : Fintype.card R ≤ 3 * Fintype.card I := by
    rw [← hbal]
    calc
      ∑ i, k i ≤ ∑ _i : I, 3 := sum_le_sum (fun i _ => hk i)
      _ = 3 * Fintype.card I := by simp [Nat.mul_comm]
  omega

/-- A nonempty actual represented host has a faithful pair throughout the density range.
No selected subgraph, factor or cycle witness is included in the premises. -/
theorem groupedGraph_hasPair_of_no_singletons_dense (J : Finset (I × R)) (k : I → ℕ)
    (hne : Nonempty ((Σ i, Fin (k i)) ⊕ R))
    (hk : ∀ i, 2 ≤ k i)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hdense : 3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R) ≤
      (groupedGraph J k).edgeFinset.card + 2) :
    HasTwoEdgeDisjointCyclesSameVertexSet (groupedGraph J k) := by
  by_cases heq : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)
  · exact groupedGraph_hasPair_of_no_singletons J k hk hmax heq
  · have hfull := grouped_full_degree_of_strict_dense J k hk hmax hdense heq
    by_cases hlarge : ∃ i, 4 ≤ k i
    · obtain ⟨i, hi⟩ := hlarge
      exact groupedGraph_hasPair_of_large_group J k i hi (by rw [hfull i]; omega)
    · have hsmall : ∀ i, k i ≤ 3 := by
        intro i
        have hn : ¬ 4 ≤ k i := fun h => hlarge ⟨i, h⟩
        omega
      have hbal := grouped_balance_dense J k hmax hdense
      have hrpos : 0 < Fintype.card R := by
        have hv := Fintype.card_pos_iff.mpr hne
        simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at hv
        rw [hbal] at hv
        omega
      letI : Nonempty R := Fintype.card_pos_iff.mp hrpos
      obtain ⟨hl, hr⟩ := groupedGraph_quotient_caps J k hk hmax
      exact hasPair_of_twin_incidence (groupedGraph J k) J hl hr
        (incidence_budget_of_full_degree J k hsmall hbal hfull)
        (twoCloneHostEmbedding k hk) (groupedGraph_twoClone_adj J k hk)
end Grouped

section Host
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R]
    (G : SimpleGraph (A ⊕ R)) [DecidableRel G.Adj]
open Erdos585.TwinNoSingleton

/-- Nonempty finite simple bipartite hosts with maximum degree six, repeated left
neighborhoods and at least 3v−2 edges force the original actual cycle pair. -/
theorem hasPair_of_no_singleton_twins_dense
    (hne : Nonempty (A ⊕ R))
    (hleft : ∀ a b : A, ¬ G.Adj (.inl a) (.inl b))
    (hright : ∀ r s : R, ¬ G.Adj (.inr r) (.inr s))
    (hmax : ∀ v, G.degree v ≤ 6)
    (hdense : 3 * Fintype.card (A ⊕ R) ≤ G.edgeFinset.card + 2)
    (htwins : ∀ a : A, ∃ b : A, b ≠ a ∧
      ∀ r : R, G.Adj (.inl a) (.inr r) ↔ G.Adj (.inl b) (.inr r)) :
    HasTwoEdgeDisjointCyclesSameVertexSet G := by
  classical
  let e := groupedIso G hleft hright
  have hgroupmax : ∀ v,
      (groupedGraph (incidences G) (classSize G)).degree v ≤ 6 := by
    intro v
    rw [← e.degree_eq v]
    exact hmax (e v)
  have hgroupdense :
      3 * Fintype.card ((Σ i : TwinClass G, Fin (classSize G i)) ⊕ R) ≤
        (groupedGraph (incidences G) (classSize G)).edgeFinset.card + 2 := by
    rw [e.card_edgeFinset_eq, Fintype.card_congr e.toEquiv]
    exact hdense
  have hgroupne : Nonempty ((Σ i : TwinClass G, Fin (classSize G i)) ⊕ R) := by
    obtain ⟨v⟩ := hne
    exact ⟨e.symm v⟩
  have hp := groupedGraph_hasPair_of_no_singletons_dense
    (incidences G) (classSize G) hgroupne (classSize_ge_two G htwins) hgroupmax hgroupdense
  exact faithfulPair_map hp e.toHom e.injective
end Host

#print axioms grouped_balance_dense
#print axioms grouped_full_degree_of_strict_dense
#print axioms groupedGraph_hasPair_of_no_singletons_dense
#print axioms hasPair_of_no_singleton_twins_dense
#check @hasPair_of_no_singleton_twins_dense
end OpenMathReview.TwinDensityExtension
