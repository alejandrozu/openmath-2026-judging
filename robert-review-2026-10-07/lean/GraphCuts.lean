import EdgeCounts
import CrossingLoss
import Mathlib.Tactic.Tauto

/-! # Literal graph cut counts and the four bipartite cells

All counts below concern the actual simple adjacency graph, not a supplied
network-flow cut inequality. -/
open Finset SimpleGraph
open scoped Classical BigOperators
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]
  (r : P → Q → Prop)

lemma selected_cell (X : Finset P) (Y : Finset Q) (p : P) (q : Q) :
    selectedRel r (cellEdges r X Y) p q ↔ r p q ∧ p ∈ X ∧ q ∈ Y := by
  constructor
  · rintro ⟨e, he, hp, hq⟩
    obtain ⟨_, hx, hy⟩ := mem_filter.mp he
    exact ⟨by simpa only [hp,hq] using e.2, hp ▸ hx, hq ▸ hy⟩
  · rintro ⟨h, hx, hy⟩
    exact ⟨⟨(p,q),h⟩, by simp [cellEdges,hx,hy], rfl,rfl⟩

lemma cell_row_sum (X : Finset P) (Y : Finset Q) :
    cellCount r X Y = ∑ p ∈ X, (Y.filter (r p)).card := by
  have hm : (cellEdges r X Y : Set (Edge r)).MapsTo (fun e => e.1.1) X := by
    intro e he
    exact (mem_filter.mp he).2.1
  rw [cellCount,card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  intro p hp
  rw [← left_neighbour_card]
  congr 1
  ext q
  simp [selected_cell,hp]
  tauto

lemma cell_column_sum (X : Finset P) (Y : Finset Q) :
    cellCount r X Y = ∑ q ∈ Y, (X.filter (fun p => r p q)).card := by
  have hm : (cellEdges r X Y : Set (Edge r)).MapsTo (fun e => e.1.2) Y := by
    intro e he
    exact (mem_filter.mp he).2.2
  rw [cellCount,card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  intro q hq
  rw [← right_neighbour_card]
  congr 1
  ext p
  simp [selected_cell,hq]
  tauto

lemma cut_left_vertex (X : Finset P) (Y : Finset Q) (p : P) :
    (((X.disjSum Y)ᶜ).filter ((bipGraph r).Adj (Sum.inl p))).card =
      (Yᶜ.filter (r p)).card := by
  have he : ((X.disjSum Y)ᶜ).filter ((bipGraph r).Adj (Sum.inl p)) =
      (Yᶜ.filter (r p)).map Function.Embedding.inr := by
    ext w
    simp only [mem_filter]
    cases w <;> simp [bipGraph]
  rw [he,card_map]

lemma cut_right_vertex (X : Finset P) (Y : Finset Q) (q : Q) :
    (((X.disjSum Y)ᶜ).filter ((bipGraph r).Adj (Sum.inr q))).card =
      (Xᶜ.filter (fun p => r p q)).card := by
  have he : ((X.disjSum Y)ᶜ).filter ((bipGraph r).Adj (Sum.inr q)) =
      (Xᶜ.filter (fun p => r p q)).map Function.Embedding.inl := by
    ext w
    simp only [mem_filter]
    cases w <;> simp [bipGraph]
  rw [he,card_map]

theorem bipartite_cut_count (X : Finset P) (Y : Finset Q) :
    cutCount (bipGraph r) (X.disjSum Y) = cellCount r X Yᶜ + cellCount r Xᶜ Y := by
  unfold cutCount
  rw [sum_disjSum]
  simp_rw [cut_left_vertex,cut_right_vertex]
  rw [cell_row_sum,cell_column_sum]

lemma cell_mono_left (X X' : Finset P) (Y : Finset Q) (h : X ⊆ X') :
    cellCount r X Y ≤ cellCount r X' Y := by
  apply card_le_card
  intro e he
  obtain ⟨hu,hx,hy⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨hu,h hx,hy⟩

lemma cell_mono_right (X : Finset P) (Y Y' : Finset Q) (h : Y ⊆ Y') :
    cellCount r X Y ≤ cellCount r X Y' := by
  apply card_le_card
  intro e he
  obtain ⟨hu,hx,hy⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨hu,hx,h hy⟩

#print axioms bipartite_cut_count
end RobertPublishable.Factor
