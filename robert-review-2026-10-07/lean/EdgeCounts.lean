import BipartiteFactor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact incidence counts for the four cells of a bipartite cut -/
open Finset
open scoped Classical
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]
  (r : P → Q → Prop)

noncomputable def cellEdges (X : Finset P) (Y : Finset Q) : Finset (Edge r) :=
  univ.filter (fun e => e.1.1 ∈ X ∧ e.1.2 ∈ Y)
noncomputable def cellCount (X : Finset P) (Y : Finset Q) : ℕ := (cellEdges r X Y).card

lemma crossing_as_cell (X : Finset P) (Y : Finset Q) :
    crossing r X Y = cellEdges r X Yᶜ := by ext e; simp [crossing,cellEdges]

lemma row_split (X : Finset P) (Y : Finset Q) :
    cellCount r X univ = cellCount r X Y + cellCount r X Yᶜ := by
  have he : cellEdges r X univ = cellEdges r X Y ∪ cellEdges r X Yᶜ := by
    ext e
    simp only [cellEdges,mem_filter,mem_univ,true_and,mem_union,mem_compl]
    tauto
  have hd : Disjoint (cellEdges r X Y) (cellEdges r X Yᶜ) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (mem_compl.mp (mem_filter.mp hf).2.2) (mem_filter.mp he).2.2
  unfold cellCount
  rw [he,card_union_of_disjoint hd]

lemma column_split (X : Finset P) (Y : Finset Q) :
    cellCount r univ Y = cellCount r X Y + cellCount r Xᶜ Y := by
  have he : cellEdges r univ Y = cellEdges r X Y ∪ cellEdges r Xᶜ Y := by
    ext e
    simp only [cellEdges,mem_filter,mem_univ,true_and,mem_union,mem_compl]
    tauto
  have hd : Disjoint (cellEdges r X Y) (cellEdges r Xᶜ Y) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (mem_compl.mp (mem_filter.mp hf).2.1) (mem_filter.mp he).2.1
  unfold cellCount
  rw [he,card_union_of_disjoint hd]

lemma selected_univ (p : P) (q : Q) : selectedRel r univ p q ↔ r p q := by
  constructor
  · exact selectedRel_sub r univ
  · intro h
    exact ⟨⟨(p,q),h⟩,mem_univ _,rfl,rfl⟩

lemma all_left_incidence (p : P) :
    ((univ : Finset (Edge r)).filter (fun e => e.1.1 = p)).card =
      (univ.filter (r p)).card := by
  have h := left_neighbour_card r (univ : Finset (Edge r)) p
  simpa only [selected_univ] using h.symm

lemma all_right_incidence (q : Q) :
    ((univ : Finset (Edge r)).filter (fun e => e.1.2 = q)).card =
      (univ.filter (fun p => r p q)).card := by
  have h := right_neighbour_card r (univ : Finset (Edge r)) q
  simpa only [selected_univ] using h.symm

lemma row_sum (X : Finset P) :
    cellCount r X univ = ∑ p ∈ X, (univ.filter (r p)).card := by
  have hm : (cellEdges r X univ : Set (Edge r)).MapsTo (fun e => e.1.1) X := by
    intro e he
    exact (mem_filter.mp he).2.1
  rw [cellCount,card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  intro p hp
  have he : (cellEdges r X univ).filter (fun e => e.1.1 = p) =
      univ.filter (fun e : Edge r => e.1.1 = p) := by
    ext e
    simp only [cellEdges,mem_filter,mem_univ,true_and,and_true]
    aesop
  rw [he,all_left_incidence]

lemma column_sum (Y : Finset Q) :
    cellCount r univ Y = ∑ q ∈ Y, (univ.filter (fun p => r p q)).card := by
  have hm : (cellEdges r univ Y : Set (Edge r)).MapsTo (fun e => e.1.2) Y := by
    intro e he
    exact (mem_filter.mp he).2.2
  rw [cellCount,card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  intro q hq
  have he : (cellEdges r univ Y).filter (fun e => e.1.2 = q) =
      univ.filter (fun e : Edge r => e.1.2 = q) := by
    ext e
    simp only [cellEdges,mem_filter,mem_univ,true_and,and_true]
    aesop
  rw [he,all_right_incidence]

#print axioms row_sum
#print axioms column_sum
end RobertPublishable.Factor
