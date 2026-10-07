import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Actual same-vertex spanning edge loss across a cut

This is an edge-subgraph statement. No vertex-deletion estimate is substituted
for the actual difference of the two adjacency relations.
-/

noncomputable section

namespace RobertPublishable.Factor

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every undirected crossing edge is counted once, at its endpoint in S. -/
def cutCount (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact ∑ v ∈ S, (Sᶜ.filter (G.Adj v)).card

theorem cutCount_eq (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutCount G S = ∑ v ∈ S, (Sᶜ.filter (G.Adj v)).card := by
  unfold cutCount
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact Finset.filter_congr_decidable _ _ _

theorem neighbor_difference_card (F H : SimpleGraph V)
    [DecidableRel F.Adj] [DecidableRel H.Adj] (hFH : F ≤ H) (v : V) :
    (H.neighborFinset v \ F.neighborFinset v).card = H.degree v - F.degree v := by
  have hsub : F.neighborFinset v ⊆ H.neighborFinset v := by
    intro x hx
    exact (H.mem_neighborFinset v x).mpr (hFH ((F.mem_neighborFinset v x).mp hx))
  rw [Finset.card_sdiff_of_subset hsub, F.card_neighborFinset_eq_degree, H.card_neighborFinset_eq_degree]

theorem vertex_cut_card_le (F H : SimpleGraph V)
    [DecidableRel F.Adj] [DecidableRel H.Adj] (hFH : F ≤ H)
    (S : Finset V) (v : V) :
    (Sᶜ.filter (H.Adj v)).card ≤
      (Sᶜ.filter (F.Adj v)).card + (H.degree v - F.degree v) := by
  classical
  have hsub : Sᶜ.filter (H.Adj v) ⊆
      (Sᶜ.filter (F.Adj v)) ∪ (H.neighborFinset v \ F.neighborFinset v) := by
    intro x hx
    obtain ⟨hxS, hxH⟩ := Finset.mem_filter.mp hx
    by_cases hxF : F.Adj v x
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hxS, hxF⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr
        ⟨(H.mem_neighborFinset v x).mpr hxH,
          fun h => hxF ((F.mem_neighborFinset v x).mp h)⟩))
  calc
    (Sᶜ.filter (H.Adj v)).card ≤
        ((Sᶜ.filter (F.Adj v)) ∪ (H.neighborFinset v \ F.neighborFinset v)).card :=
      Finset.card_le_card hsub
    _ ≤ (Sᶜ.filter (F.Adj v)).card + (H.neighborFinset v \ F.neighborFinset v).card :=
      Finset.card_union_le _ _
    _ = (Sᶜ.filter (F.Adj v)).card + (H.degree v - F.degree v) := by
      rw [neighbor_difference_card F H hFH v]

/-- Losing at most t incident edges per vertex costs at most t|S| across
the actual cut, with both graphs on the same vertex type. -/
theorem cutCount_le_of_degree_loss (F H : SimpleGraph V)
    [DecidableRel F.Adj] [DecidableRel H.Adj] (hFH : F ≤ H)
    (t : ℕ) (hloss : ∀ v, H.degree v - F.degree v ≤ t) (S : Finset V) :
    cutCount H S ≤ cutCount F S + t * S.card := by
  classical
  classical
  have hsum : (∑ v ∈ S, (Sᶜ.filter (H.Adj v)).card) ≤
      (∑ v ∈ S, (Sᶜ.filter (F.Adj v)).card) + t * S.card := by
    calc
      ∑ v ∈ S, (Sᶜ.filter (H.Adj v)).card ≤
          ∑ v ∈ S, ((Sᶜ.filter (F.Adj v)).card + t) := by
        apply Finset.sum_le_sum
        intro v _
        exact (vertex_cut_card_le F H hFH S v).trans (Nat.add_le_add_left (hloss v) _)
      _ = (∑ v ∈ S, (Sᶜ.filter (F.Adj v)).card) + t * S.card := by
        rw [Finset.sum_add_distrib]
        simp [Nat.mul_comm]
  simpa only [cutCount_eq] using hsum

/-- Real degree budgets avoid an additional ceiling loss when the nominal
regularity parameter comes from sampling. The cuts still count actual edges. -/
theorem cutCount_real_le_of_degree_loss (F H : SimpleGraph V)
    [DecidableRel F.Adj] [DecidableRel H.Adj] (hFH : F ≤ H)
    (t : ℝ) (hloss : ∀ v, (H.degree v : ℝ) - (F.degree v : ℝ) ≤ t) (S : Finset V) :
    (cutCount H S : ℝ) ≤ (cutCount F S : ℝ) + t * (S.card : ℝ) := by
  classical
  have hv : ∀ v, ((Sᶜ.filter (H.Adj v)).card : ℝ) ≤
      ((Sᶜ.filter (F.Adj v)).card : ℝ) + t := by
    intro v
    have hD : F.degree v ≤ H.degree v :=
      SimpleGraph.degree_le_of_le (G := F) (v := v) hFH
    have hR : ((Sᶜ.filter (H.Adj v)).card : ℝ) ≤
        ((Sᶜ.filter (F.Adj v)).card : ℝ) + ((H.degree v - F.degree v : ℕ) : ℝ) := by
      exact_mod_cast vertex_cut_card_le F H hFH S v
    rw [Nat.cast_sub hD] at hR
    exact hR.trans (add_le_add_right (hloss v) _)
  have hsum : (∑ v ∈ S, ((Sᶜ.filter (H.Adj v)).card : ℝ)) ≤
      (∑ v ∈ S, ((Sᶜ.filter (F.Adj v)).card : ℝ)) + t * (S.card : ℝ) := by
    calc
      ∑ v ∈ S, ((Sᶜ.filter (H.Adj v)).card : ℝ) ≤
          ∑ v ∈ S, (((Sᶜ.filter (F.Adj v)).card : ℝ) + t) := by
        exact Finset.sum_le_sum (fun v _ => hv v)
      _ = (∑ v ∈ S, ((Sᶜ.filter (F.Adj v)).card : ℝ)) + t * (S.card : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]
  simpa only [cutCount_eq, Nat.cast_sum] using hsum

#print axioms neighbor_difference_card
#print axioms vertex_cut_card_le
#print axioms cutCount_le_of_degree_loss
#print axioms cutCount_real_le_of_degree_loss
#check @cutCount_le_of_degree_loss
#check @cutCount_real_le_of_degree_loss

end RobertPublishable.Factor
