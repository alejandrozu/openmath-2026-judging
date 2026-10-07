import FactorExtraction
import Aesop

/-! # An actual spanning simple-graph factor

This graph has the original vertices, keeps only original adjacency edges,
and has exactly k actual neighbours at every vertex.
-/
open Finset SimpleGraph
open scoped Classical
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]

def bipGraph (r : P → Q → Prop) : SimpleGraph (P ⊕ Q) where
  Adj a b := match a,b with
    | Sum.inl p, Sum.inr q => r p q
    | Sum.inr q, Sum.inl p => r p q
    | Sum.inl _, Sum.inl _ => False
    | Sum.inr _, Sum.inr _ => False
  symm := by
    constructor
    intro a b h
    cases a <;> cases b <;> exact h
  loopless := by
    constructor
    intro a h
    cases a <;> exact h

lemma degree_left (r : P → Q → Prop) (p : P) :
    (bipGraph r).degree (Sum.inl p) = (univ.filter (r p)).card := by
  have hn : (bipGraph r).neighborFinset (Sum.inl p) =
      (univ.filter (r p)).map Function.Embedding.inr := by
    ext w
    rw [(bipGraph r).mem_neighborFinset (Sum.inl p) w]
    cases w <;> simp [bipGraph]
  rw [← card_neighborFinset_eq_degree,hn,card_map]

lemma degree_right (r : P → Q → Prop) (q : Q) :
    (bipGraph r).degree (Sum.inr q) = (univ.filter (fun p => r p q)).card := by
  have hn : (bipGraph r).neighborFinset (Sum.inr q) =
      (univ.filter (fun p => r p q)).map Function.Embedding.inl := by
    ext w
    rw [(bipGraph r).mem_neighborFinset (Sum.inr q) w]
    cases w <;> simp [bipGraph]
  rw [← card_neighborFinset_eq_degree,hn,card_map]

def selectedRel (r : P → Q → Prop) (C : Finset (Edge r)) (p : P) (q : Q) : Prop :=
  ∃ e ∈ C, e.1.1 = p ∧ e.1.2 = q

lemma selectedRel_sub (r : P → Q → Prop) (C : Finset (Edge r)) {p : P} {q : Q}
    (h : selectedRel r C p q) : r p q := by
  obtain ⟨e,he,hp,hq⟩ := h
  simpa only [hp,hq] using e.2

lemma left_neighbours_as_image (r : P → Q → Prop) (C : Finset (Edge r)) (p : P) :
    univ.filter (selectedRel r C p) = (C.filter (fun e => e.1.1 = p)).image (fun e => e.1.2) := by
  ext q
  simp only [mem_filter,mem_univ,true_and,selectedRel,mem_image]
  aesop

lemma right_neighbours_as_image (r : P → Q → Prop) (C : Finset (Edge r)) (q : Q) :
    univ.filter (fun p => selectedRel r C p q) = (C.filter (fun e => e.1.2 = q)).image (fun e => e.1.1) := by
  ext p
  simp only [mem_filter,mem_univ,true_and,selectedRel,mem_image]
  aesop

lemma left_neighbour_card (r : P → Q → Prop) (C : Finset (Edge r)) (p : P) :
    (univ.filter (selectedRel r C p)).card = (C.filter (fun e => e.1.1 = p)).card := by
  rw [left_neighbours_as_image,card_image_of_injOn]
  intro e he f hf hq
  apply Subtype.ext
  exact Prod.ext ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hq

lemma right_neighbour_card (r : P → Q → Prop) (C : Finset (Edge r)) (q : Q) :
    (univ.filter (fun p => selectedRel r C p q)).card = (C.filter (fun e => e.1.2 = q)).card := by
  rw [right_neighbours_as_image,card_image_of_injOn]
  intro e he f hf hp
  apply Subtype.ext
  exact Prod.ext hp ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm)

/-- The genuine capacity-one k-factor consequence of the complete cut criterion. -/
theorem exists_spanning_regular_factor (r : P → Q → Prop) (k : ℕ)
    (hbalance : Fintype.card P = Fintype.card Q) (hcut : CutCondition r k) :
    ∃ F : SimpleGraph (P ⊕ Q), F ≤ bipGraph r ∧ F.IsRegularOfDegree k := by
  obtain ⟨C,hP,hQ⟩ := exists_regular_edge_set r k hbalance hcut
  refine ⟨bipGraph (selectedRel r C),?_,?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp only [bipGraph] at * <;> try contradiction
    all_goals exact selectedRel_sub r C hab
  · intro v
    cases v with
    | inl p => rw [degree_left,left_neighbour_card,hP]
    | inr q => rw [degree_right,right_neighbour_card,hQ]

#print axioms exists_spanning_regular_factor
end RobertPublishable.Factor
