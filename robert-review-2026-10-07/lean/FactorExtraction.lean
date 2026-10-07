import CapacityHall
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Extracting distinct actual edges from the capacity matching

The selected finite edge set has exactly k incidences at every vertex on both
shores. Edges are subtypes of ordered endpoint pairs, so one incidence is one
original simple-graph edge. No regular-factor existence is an input.
-/
open Finset SimpleGraph
open scoped Classical
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]
  (r : P → Q → Prop) (k : ℕ) (f : Left r k → Right r k)
  (hf : Function.Bijective f) (hr : ∀ a, cloneRel r k a (f a))

include hr in
lemma left_exists (pi : P × Fin k) : ∃ e : Edge r,
    f (Sum.inl pi) = Sum.inr e ∧ e.1.1 = pi.1 := by
  have h := hr (Sum.inl pi)
  cases hval : f (Sum.inl pi) with
  | inl qj => simp [hval,cloneRel] at h
  | inr e => exact ⟨e,rfl,by simpa [hval,cloneRel] using h⟩

noncomputable def leftChoice (pi : P × Fin k) : Edge r :=
  Classical.choose (left_exists r k f hr pi)

lemma leftChoice_spec (pi : P × Fin k) :
    f (Sum.inl pi) = Sum.inr (leftChoice r k f hr pi) ∧
      (leftChoice r k f hr pi).1.1 = pi.1 := Classical.choose_spec (left_exists r k f hr pi)

noncomputable def selected : Finset (Edge r) :=
  univ.filter (fun e => ∃ pi : P × Fin k, f (Sum.inl pi) = Sum.inr e)

include hf hr in
lemma selected_iff_right (e : Edge r) : e ∈ selected r k f ↔
    ∃ qj : Q × Fin k, f (Sum.inr e) = Sum.inl qj := by
  classical
  constructor
  · intro he
    obtain ⟨pi,hpi⟩ := (mem_filter.mp he).2
    have hh := hr (Sum.inr e)
    cases hval : f (Sum.inr e) with
    | inl qj => exact ⟨qj,rfl⟩
    | inr e' =>
      have hee : e = e' := by simpa [cloneRel,hval] using hh
      subst e'
      have ha := hf.1 (hpi.trans hval.symm)
      cases ha
  · rintro ⟨qj,hqj⟩
    obtain ⟨a,ha⟩ := hf.2 (Sum.inr e)
    have hh := hr a
    cases a with
    | inl pi => exact mem_filter.mpr ⟨mem_univ _,⟨pi,ha⟩⟩
    | inr e' =>
      have hee : e' = e := by simpa [cloneRel,ha] using hh
      subst e'
      have hx : (Sum.inl qj : Right r k) = Sum.inr e := hqj.symm.trans ha
      cases hx

include hf hr in
lemma right_exists (qj : Q × Fin k) : ∃ e : Edge r,
    f (Sum.inr e) = Sum.inl qj ∧ e.1.2 = qj.1 := by
  obtain ⟨a,ha⟩ := hf.2 (Sum.inl qj)
  have hh := hr a
  cases a with
  | inl pi => simp [ha,cloneRel] at hh
  | inr e => exact ⟨e,ha,by simpa [ha,cloneRel] using hh⟩

noncomputable def rightChoice (qj : Q × Fin k) : Edge r :=
  Classical.choose (right_exists r k f hf hr qj)

lemma rightChoice_spec (qj : Q × Fin k) :
    f (Sum.inr (rightChoice r k f hf hr qj)) = Sum.inl qj ∧
      (rightChoice r k f hf hr qj).1.2 = qj.1 :=
  Classical.choose_spec (right_exists r k f hf hr qj)

include hf in
lemma leftChoice_injective : Function.Injective (leftChoice r k f hr) := by
  intro pi pj h
  have hh : f (Sum.inl pi) = f (Sum.inl pj) :=
    (leftChoice_spec r k f hr pi).1.trans
      ((congrArg Sum.inr h).trans (leftChoice_spec r k f hr pj).1.symm)
  exact Sum.inl.inj (hf.1 hh)

lemma rightChoice_injective : Function.Injective (rightChoice r k f hf hr) := by
  intro qi qj h
  have hh : (Sum.inl qi : Right r k) = Sum.inl qj :=
    (rightChoice_spec r k f hf hr qi).1.symm.trans
      ((congrArg (fun e => f (Sum.inr e)) h).trans (rightChoice_spec r k f hf hr qj).1)
  exact Sum.inl.inj hh

lemma selected_left_image (p : P) :
    (selected r k f).filter (fun e => e.1.1 = p) =
      (univ : Finset (Fin k)).image (fun i => leftChoice r k f hr (p,i)) := by
  ext e
  constructor
  · intro he
    obtain ⟨hs,hleft⟩ := mem_filter.mp he
    obtain ⟨pi,hpi⟩ := (mem_filter.mp hs).2
    have hsame : leftChoice r k f hr pi = e :=
      Sum.inr.inj ((leftChoice_spec r k f hr pi).1.symm.trans hpi)
    have hp : pi.1 = p := (leftChoice_spec r k f hr pi).2.symm.trans (hsame.symm ▸ hleft)
    have htuple : pi = (p,pi.2) := Prod.ext hp rfl
    exact mem_image.mpr ⟨pi.2,mem_univ _,htuple ▸ hsame⟩
  · intro he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,⟨(p,i),(leftChoice_spec r k f hr (p,i)).1⟩⟩,
      (leftChoice_spec r k f hr (p,i)).2⟩

lemma selected_right_image (q : Q) :
    (selected r k f).filter (fun e => e.1.2 = q) =
      (univ : Finset (Fin k)).image (fun j => rightChoice r k f hf hr (q,j)) := by
  ext e
  constructor
  · intro he
    obtain ⟨hs,hright⟩ := mem_filter.mp he
    obtain ⟨qj,hqj⟩ := (selected_iff_right r k f hf hr e).mp hs
    have hsame : rightChoice r k f hf hr qj = e :=
      Sum.inr.inj (hf.1 ((rightChoice_spec r k f hf hr qj).1.trans hqj.symm))
    have hq : qj.1 = q := (rightChoice_spec r k f hf hr qj).2.symm.trans (hsame.symm ▸ hright)
    have htuple : qj = (q,qj.2) := Prod.ext hq rfl
    exact mem_image.mpr ⟨qj.2,mem_univ _,htuple ▸ hsame⟩
  · intro he
    obtain ⟨j,hj,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨(selected_iff_right r k f hf hr _).mpr
      ⟨(q,j),(rightChoice_spec r k f hf hr (q,j)).1⟩,(rightChoice_spec r k f hf hr (q,j)).2⟩

include hf hr in
theorem selected_left_degree (p : P) : ((selected r k f).filter (fun e => e.1.1 = p)).card = k := by
  rw [selected_left_image r k f hr p,card_image_of_injective]
  · simp
  · intro i j h
    exact (Prod.mk.inj (leftChoice_injective r k f hf hr h)).2

include hf hr in
theorem selected_right_degree (q : Q) : ((selected r k f).filter (fun e => e.1.2 = q)).card = k := by
  rw [selected_right_image r k f hf hr q,card_image_of_injective]
  · simp
  · intro i j h
    exact (Prod.mk.inj (rightChoice_injective r k f hf hr h)).2

theorem exists_regular_edge_set (hbalance : Fintype.card P = Fintype.card Q)
    (hcut : CutCondition r k) : ∃ C : Finset (Edge r),
    (∀ p, (C.filter (fun e => e.1.1 = p)).card = k) ∧
    (∀ q, (C.filter (fun e => e.1.2 = q)).card = k) := by
  obtain ⟨f,hf,hr⟩ := capacity_matching r k hbalance hcut
  exact ⟨selected r k f,selected_left_degree r k f hf hr,selected_right_degree r k f hf hr⟩

#print axioms selected_left_degree
#print axioms selected_right_degree
#print axioms exists_regular_edge_set
end RobertPublishable.Factor
