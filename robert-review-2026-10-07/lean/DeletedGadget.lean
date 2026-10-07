import Regularity

/-! # A deleted vertex of a finite bipartite regular graph gives a gadget

The side surplus, exact deleted-neighbour degrees, and distinct unit-deficit
ports are conclusions. This is the graph-theoretic input to Corollary B.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB
namespace DeletedGadget
variable {V : Type*} [DecidableEq V] [Fintype V]
  (B : SimpleGraph V) (c : V → Bool) (o : V)

abbrev Inner := {v : V // c v = c o ∧ v ≠ o}
abbrev Outer := {v : V // c v ≠ c o}
abbrev Kept := {v : V // v ≠ o}

def kept : Inner c o ⊕ Outer c o → V
  | Sum.inl v => v.1
  | Sum.inr v => v.1

lemma kept_ne (x : Inner c o ⊕ Outer c o) : kept c o x ≠ o := by
  cases x with
  | inl x => exact x.2.2
  | inr x => exact fun h => x.2 (congrArg c h)

lemma kept_injective : Function.Injective (kept c o) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext h)
    | inr y => exact False.elim (y.2 ((congrArg c h).symm.trans x.2.1))
  | inr x =>
    cases y with
    | inl y => exact False.elim (x.2 ((congrArg c h).trans y.2.1))
    | inr y => exact congrArg Sum.inr (Subtype.ext h)

noncomputable def keptEquiv : Inner c o ⊕ Outer c o ≃ Kept o :=
  Equiv.ofBijective (fun x => ⟨kept c o x,kept_ne c o x⟩)
    ⟨fun x y h => kept_injective c o (congrArg Subtype.val h), by
      intro v
      by_cases hc : c v.1 = c o
      · exact ⟨Sum.inl ⟨v.1,hc,v.2⟩,rfl⟩
      · exact ⟨Sum.inr ⟨v.1,hc⟩,rfl⟩⟩

def graph : SimpleGraph (Inner c o ⊕ Outer c o) := B.comap (kept c o)

noncomputable def deletedIso : graph B c o ≃g B.induce {v | v ≠ o} :=
  { toEquiv := keptEquiv c o
    map_rel_iff' := by intro x y; rfl }

lemma induced_degree (v : Kept o) :
    (B.induce {v | v ≠ o}).degree v = B.degree v.1 - (if B.Adj o v.1 then 1 else 0) := by
  classical
  have he : ((B.induce {v | v ≠ o}).neighborFinset v).map (.subtype (· ∈ {v | v ≠ o})) =
      (B.neighborFinset v.1).erase o := by
    rw [B.map_neighborFinset_induce]
    ext w
    simp [and_comm]
  rw [← card_neighborFinset_eq_degree,← card_map (f := Function.Embedding.subtype (· ∈ {v | v ≠ o})),he]
  by_cases h : B.Adj o v.1
  · have ho : o ∈ B.neighborFinset v.1 := (B.mem_neighborFinset v.1 o).mpr h.symm
    rw [card_erase_of_mem ho,B.card_neighborFinset_eq_degree]
    simp [h]
  · have ho : o ∉ B.neighborFinset v.1 := by simpa [adj_comm] using h
    rw [erase_eq_of_notMem ho,B.card_neighborFinset_eq_degree]
    simp [h]

lemma graph_degree (x : Inner c o ⊕ Outer c o) :
    (graph B c o).degree x = B.degree (kept c o x) -
      (if B.Adj o (kept c o x) then 1 else 0) := by
  rw [← (deletedIso B c o).degree_eq x,induced_degree]
  rfl

lemma color_outer (x : Inner c o ⊕ Outer c o) :
    outerShore x = true ↔ c (kept c o x) ≠ c o := by
  cases x with
  | inl x => simp [outerShore,kept,x.2.1]
  | inr x => simp [outerShore,kept,x.2]

lemma bipartite (hc : ∀ a b, B.Adj a b → c a ≠ c b) :
    ∀ x y, (graph B c o).Adj x y → outerShore x ≠ outerShore y := by
  intro x y h
  have hcol := hc (kept c o x) (kept c o y) h
  have hx := color_outer c o x
  have hy := color_outer c o y
  cases ha : outerShore x <;> cases hb : outerShore y <;>
    cases hu : c (kept c o x) <;> cases hv : c (kept c o y) <;> cases ho : c o <;> simp_all

lemma side_card_eq (hc : ∀ a b, B.Adj a b → c a ≠ c b)
    (hreg : ∀ v, B.degree v = 6) :
    (univ.filter fun v => c v = c o).card = (univ.filter fun v => c v ≠ c o).card := by
  classical
  let X : Finset V := univ.filter (fun v => c v = c o)
  let Y : Finset V := univ.filter (fun v => c v ≠ c o)
  have hb : B.IsBipartiteWith (↑X) (↑Y) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro v hx hy
      exact (mem_filter.mp hy).2 (mem_filter.mp hx).2
    · intro v w hvw
      have hh := hc v w hvw
      by_cases hv : c v = c o
      · exact Or.inl ⟨mem_filter.mpr ⟨mem_univ _,hv⟩,
          mem_filter.mpr ⟨mem_univ _,fun hw => hh (hv.trans hw.symm)⟩⟩
      · have hw : c w = c o := by cases cv : c v <;> cases cw : c w <;> cases co : c o <;> simp_all
        exact Or.inr ⟨mem_filter.mpr ⟨mem_univ _,hv⟩,mem_filter.mpr ⟨mem_univ _,hw⟩⟩
  have he := B.isBipartiteWith_sum_degrees_eq hb
  simp_rw [hreg] at he
  simp [hreg] at he
  change X.card = Y.card
  omega

lemma surplus (hc : ∀ a b, B.Adj a b → c a ≠ c b)
    (hreg : ∀ v, B.degree v = 6) : Fintype.card (Outer c o) = Fintype.card (Inner c o) + 1 := by
  classical
  have hcard := side_card_eq B c o hc hreg
  have he : univ.filter (fun v => c v = c o ∧ v ≠ o) =
      (univ.filter fun v => c v = c o).erase o := by ext; simp [and_comm]
  have ho : o ∈ univ.filter (fun v => c v = c o) := by simp
  simp only [Outer,Inner,Fintype.card_subtype]
  rw [he,card_erase_of_mem ho,← hcard]
  have hp := card_pos.mpr ⟨o,ho⟩
  omega

theorem gadget (hc : ∀ a b, B.Adj a b → c a ≠ c b) (hreg : ∀ v, B.degree v = 6) :
    Gadget (graph B c o) 6 := by
  refine ⟨bipartite B c o hc,?_,?_,surplus B c o hc hreg⟩
  · intro i
    rw [graph_degree,hreg]
    have hn : ¬ B.Adj o i.1 := by
      intro h
      exact hc o i.1 h i.2.1.symm
    simp [kept,hn]
  · intro y
    rw [graph_degree,hreg]
    omega

theorem pairfree (h : ¬ Erdos585.HasPairF (B.induce {v | v ≠ o})) :
    ¬ Erdos585.HasPairF (graph B c o) := by
  intro hp
  exact h (hp.map (deletedIso B c o).toHom (deletedIso B c o).injective)

#print axioms gadget
#print axioms pairfree
end DeletedGadget
end RobertPublishable.SUB
