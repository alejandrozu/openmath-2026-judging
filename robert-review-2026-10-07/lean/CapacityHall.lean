import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-! # Capacity-one bipartite factor matching from the cut criterion

The two edge-capacity nodes prevent different vertex clones from choosing the
same original edge. Finite Hall supplies the matching; no flow existence or
factor conclusion is a hypothesis. The near-regular hypotheses will be shown
to imply the cut criterion in a separate module.
-/
open Finset
open scoped Classical
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]
  (r : P → Q → Prop) (k : ℕ)

abbrev Edge := {pq : P × Q // r pq.1 pq.2}
abbrev Left := (P × Fin k) ⊕ Edge r
abbrev Right := (Q × Fin k) ⊕ Edge r

def cloneRel : Left r k → Right r k → Prop
  | Sum.inl pi, Sum.inr e => e.1.1 = pi.1
  | Sum.inr e, Sum.inl qj => e.1.2 = qj.1
  | Sum.inr e, Sum.inr f => e = f
  | Sum.inl _, Sum.inl _ => False

noncomputable def neighbors (a : Left r k) : Finset (Right r k) :=
  univ.filter (cloneRel r k a)

noncomputable def crossing (X : Finset P) (Y : Finset Q) : Finset (Edge r) :=
  univ.filter (fun e => e.1.1 ∈ X ∧ e.1.2 ∉ Y)

def CutCondition : Prop := ∀ X : Finset P, ∀ Y : Finset Q,
  k * X.card ≤ k * Y.card + (crossing r X Y).card

theorem capacity_hall (hcut : CutCondition r k) (S : Finset (Left r k)) :
    S.card ≤ (S.biUnion (neighbors r k)).card := by
  classical
  let C := S.toLeft
  let D := S.toRight
  let X : Finset P := C.image Prod.fst
  let Y : Finset Q := D.image (fun e => e.1.2)
  let I : Finset (Edge r) := univ.filter (fun e => e.1.1 ∈ X)
  have hN : S.biUnion (neighbors r k) = (Y.product (univ : Finset (Fin k))).disjSum (I ∪ D) := by
    ext b
    cases b with
    | inl qj =>
      constructor
      · intro hb
        obtain ⟨a,ha,hr⟩ := mem_biUnion.mp hb
        have hr := (mem_filter.mp hr).2
        cases a with
        | inl pi => exact False.elim hr
        | inr e =>
          exact inl_mem_disjSum.mpr (mem_product.mpr
            ⟨mem_image.mpr ⟨e,mem_toRight.mpr ha,hr⟩,mem_univ _⟩)
      · intro hb
        obtain ⟨e,he,heq⟩ := mem_image.mp (mem_product.mp (inl_mem_disjSum.mp hb)).1
        exact mem_biUnion.mpr ⟨Sum.inr e,mem_toRight.mp he,
          mem_filter.mpr ⟨mem_univ _,heq⟩⟩
    | inr e =>
      constructor
      · intro hb
        obtain ⟨a,ha,hr⟩ := mem_biUnion.mp hb
        have hr := (mem_filter.mp hr).2
        apply inr_mem_disjSum.mpr
        cases a with
        | inl pi =>
          apply mem_union.mpr
          left
          apply mem_filter.mpr
          refine ⟨mem_univ _,?_⟩
          exact mem_image.mpr ⟨pi,mem_toLeft.mpr ha,hr.symm⟩
        | inr f =>
          change f = e at hr
          subst f
          exact mem_union.mpr (Or.inr (mem_toRight.mpr ha))
      · intro hb
        rcases mem_union.mp (inr_mem_disjSum.mp hb) with hi | hd
        · obtain ⟨pi,hpi,hfirst⟩ := mem_image.mp (mem_filter.mp hi).2
          exact mem_biUnion.mpr ⟨Sum.inl pi,mem_toLeft.mp hpi,
            mem_filter.mpr ⟨mem_univ _,hfirst.symm⟩⟩
        · exact mem_biUnion.mpr ⟨Sum.inr e,mem_toRight.mp hd,
            mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  have hC : C ⊆ X.product (univ : Finset (Fin k)) := by
    intro pi hpi
    exact mem_product.mpr ⟨mem_image.mpr ⟨pi,hpi,rfl⟩,mem_univ _⟩
  have hCcard : C.card ≤ k * X.card := by
    have hh := card_le_card hC
    simpa [Nat.mul_comm] using hh
  have hcross : crossing r X Y ⊆ I \ D := by
    intro e he
    obtain ⟨_,hx,hy⟩ := mem_filter.mp he
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,?_⟩
    intro hd
    exact hy (mem_image.mpr ⟨e,hd,rfl⟩)
  have hK : k * X.card ≤ k * Y.card + (I \ D).card :=
    (hcut X Y).trans (Nat.add_le_add_left (card_le_card hcross) _)
  have hU : (I \ D) ∪ D = I ∪ D := by ext; simp only [mem_union,mem_sdiff]; tauto
  have hprod : (Y.product (univ : Finset (Fin k))).card = Y.card*k := by
    simpa using Finset.card_product Y (univ : Finset (Fin k))
  rw [hN,card_disjSum,hprod,← hU,card_union_of_disjoint sdiff_disjoint]
  have hS : S.card = C.card + D.card := card_toLeft_add_card_toRight.symm
  rw [hS,Nat.mul_comm Y.card k]
  omega

/-- A bijective capacity matching, prior to extraction of the actual factor. -/
theorem capacity_matching (hbalance : Fintype.card P = Fintype.card Q)
    (hcut : CutCondition r k) :
    ∃ f : Left r k → Right r k, Function.Bijective f ∧ ∀ a, cloneRel r k a (f a) := by
  obtain ⟨f,hf,hrel⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' (neighbors r k)).mp
    (capacity_hall r k hcut)
  have hc : Fintype.card (Left r k) = Fintype.card (Right r k) := by
    simp [Fintype.card_sum,Fintype.card_prod,hbalance]
  refine ⟨f,⟨hf,?_⟩,fun a => (mem_filter.mp (hrel a)).2⟩
  exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hc)).mp hf

#print axioms capacity_hall
#print axioms capacity_matching
end RobertPublishable.Factor
