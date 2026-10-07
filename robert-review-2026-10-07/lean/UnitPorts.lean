import Regularity

/-! # Existence of a valid simple substitution with distinct unit-deficit ports

Each individually labelled incident skeleton edge gets a different deficient
port. This proves that parallel skeleton edges still give distinct simple-graph
links. Port assignments and the substituted graph are constructed here.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB
namespace UnitPorts
variable {U E I O : Type*} [DecidableEq U] [DecidableEq E]
  [DecidableEq I] [DecidableEq O] [Fintype I] [Fintype O]
  (Γ : SimpleGraph (I ⊕ O)) (L : LooplessMultigraph U E) (d : ℕ)
  (stars : RegularStars L d) (ports : Finset O)
  (hcard : ports.card = d) (hpos : 0 < d)

noncomputable def assignment (u : U) : ↥(stars.star u) ≃ ↥ports :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_coe,stars.card_star,hcard])

noncomputable def defaultPort : ↥ports :=
  Classical.choice (Finset.card_pos.mp (hcard.symm ▸ hpos)).to_subtype

noncomputable def portAt (u : U) (e : E) : O :=
  if he : e ∈ stars.star u then (assignment L d stars ports hcard u ⟨e,he⟩).1
    else (defaultPort d ports hcard hpos).1

lemma portAt_mem (u : U) (e : E) : portAt L d stars ports hcard hpos u e ∈ ports := by
  unfold portAt
  split
  · exact (assignment L d stars ports hcard u _).2
  · exact (defaultPort d ports hcard hpos).2

lemma portAt_injective (u : U) {e f : E} (he : e ∈ stars.star u) (hf : f ∈ stars.star u)
    (hp : portAt L d stars ports hcard hpos u e = portAt L d stars ports hcard hpos u f) : e = f := by
  simp only [portAt,dif_pos he,dif_pos hf] at hp
  exact congrArg Subtype.val ((assignment L d stars ports hcard u).injective (Subtype.ext hp))

noncomputable def link (e : E) : Sym2 (U × (I ⊕ O)) :=
  Sym2.map (fun u => (u,Sum.inr (portAt L d stars ports hcard hpos u e))) (L.ends e)

lemma link_ends (e : E) : Sym2.map Prod.fst (link (I := I) L d stars ports hcard hpos e) = L.ends e := by
  simp [link,Sym2.map_map,Function.comp_def]

lemma link_member {e : E} {v : U × (I ⊕ O)}
    (hv : v ∈ link (I := I) L d stars ports hcard hpos e) :
    v.1 ∈ L.ends e ∧ v.2 = Sum.inr (portAt L d stars ports hcard hpos v.1 e) := by
  obtain ⟨u,hu,hv⟩ := Sym2.mem_map.mp hv
  subst v
  exact ⟨hu,rfl⟩

lemma link_injective : Function.Injective (link (I := I) L d stars ports hcard hpos) := by
  intro e f heq
  have hn : ∃ u, u ∈ L.ends e := by
    generalize hz : L.ends e = z
    induction z using Sym2.inductionOn with | _ a b => exact ⟨a,by simp⟩
  obtain ⟨u,hu⟩ := hn
  let v : U × (I ⊕ O) := (u,Sum.inr (portAt L d stars ports hcard hpos u e))
  have hve : v ∈ link (I := I) L d stars ports hcard hpos e := Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  have hvf : v ∈ link (I := I) L d stars ports hcard hpos f := heq ▸ hve
  have hf := link_member L d stars ports hcard hpos hvf
  apply portAt_injective L d stars ports hcard hpos u
    ((stars.mem_star u e).mpr hu) ((stars.mem_star u f).mpr hf.1)
  exact Sum.inr.inj hf.2

noncomputable def graph : SimpleGraph (U × (I ⊕ O)) where
  Adj a b := (a.1 = b.1 ∧ Γ.Adj a.2 b.2) ∨ ∃ e, link (I := I) L d stars ports hcard hpos e = s(a,b)
  symm := by
    constructor
    intro a b h
    rcases h with ⟨hc,hi⟩ | ⟨e,he⟩
    · exact Or.inl ⟨hc.symm,hi.symm⟩
    · exact Or.inr ⟨e,he.trans Sym2.eq_swap⟩
  loopless := by
    constructor
    intro a h
    rcases h with ⟨_,hi⟩ | ⟨e,he⟩
    · exact Γ.irrefl hi
    · have hh := congrArg (Sym2.map Prod.fst) he
      rw [link_ends,Sym2.map_mk] at hh
      exact L.loopless e (hh.symm ▸ (by simp))

lemma internal (u : U) (x y : I ⊕ O) :
    (graph Γ L d stars ports hcard hpos).Adj (u,x) (u,y) ↔ Γ.Adj x y := by
  constructor
  · rintro (⟨_,h⟩ | ⟨e,he⟩)
    · exact h
    · have hh := congrArg (Sym2.map Prod.fst) he
      rw [link_ends,Sym2.map_mk] at hh
      exact False.elim (L.loopless e (hh.symm ▸ (by simp)))
  · exact fun h => Or.inl ⟨rfl,h⟩

noncomputable def projection : LinkProjection (graph Γ L d stars ports hcard hpos) L Prod.fst where
  link := link (I := I) L d stars ports hcard hpos
  injective := link_injective L d stars ports hcard hpos
  link_edge := by
    intro e
    generalize hz : link (I := I) L d stars ports hcard hpos e = z
    induction z using Sym2.inductionOn with | _ a b => ?_
    exact (graph Γ L d stars ports hcard hpos).mem_edgeSet.mpr (Or.inr ⟨e,hz⟩)
  ends_eq := fun e => (link_ends L d stars ports hcard hpos e).symm
  complete := by
    intro z hz hn
    induction z using Sym2.inductionOn with | _ a b => ?_
    have ha := (graph Γ L d stars ports hcard hpos).mem_edgeSet.mp hz
    rcases ha with ⟨hc,hi⟩ | he
    · exact False.elim (hn (by simp [Sym2.map_mk,Sym2.mk_isDiag_iff,hc]))
    · exact he

lemma port_incidence (u : U) (o : O) (e : E) (he : e ∈ stars.star u) :
    (u,Sum.inr o) ∈ link (I := I) L d stars ports hcard hpos e ↔ portAt L d stars ports hcard hpos u e = o := by
  constructor
  · intro h
    exact (Sum.inr.inj (link_member L d stars ports hcard hpos h).2).symm
  · intro h
    apply Sym2.mem_map.mpr
    exact ⟨u,(stars.mem_star u e).mp he,by simp [h]⟩

lemma port_count (u : U) (o : O) :
    ((stars.star u).filter fun e => (u,Sum.inr o) ∈ link (I := I) L d stars ports hcard hpos e).card =
      if o ∈ ports then 1 else 0 := by
  classical
  by_cases ho : o ∈ ports
  · let e : ↥(stars.star u) := (assignment L d stars ports hcard u).symm ⟨o,ho⟩
    have hp : portAt L d stars ports hcard hpos u e.1 = o := by
      simp [portAt,e]
    have hf : (stars.star u).filter (fun f => (u,Sum.inr o) ∈ link (I := I) L d stars ports hcard hpos f) = {e.1} := by
      ext f
      constructor
      · intro h
        have hstar := (mem_filter.mp h).1
        have hport := (port_incidence L d stars ports hcard hpos u o f hstar).mp (mem_filter.mp h).2
        exact mem_singleton.mpr (portAt_injective L d stars ports hcard hpos u hstar e.2 (hport.trans hp.symm))
      · intro h
        have hfe : f = e.1 := mem_singleton.mp h
        subst f
        exact mem_filter.mpr ⟨e.2,(port_incidence L d stars ports hcard hpos u o e.1 e.2).mpr hp⟩
    simp [hf,ho]
  · have hf : (stars.star u).filter (fun e => (u,Sum.inr o) ∈ link (I := I) L d stars ports hcard hpos e) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have hp := (port_incidence L d stars ports hcard hpos u o e (mem_filter.mp he).1).mp (mem_filter.mp he).2
      exact ho (hp ▸ portAt_mem L d stars ports hcard hpos u e)
    simp [hf,ho]

noncomputable def valid (hdegree : ∀ o, Γ.degree (Sum.inr o) = d - (if o ∈ ports then 1 else 0)) :
    ValidSimpleSubstitution Γ L d (graph Γ L d stars ports hcard hpos) where
  projection := projection Γ L d stars ports hcard hpos
  regularStars := stars
  internal := internal Γ L d stars ports hcard hpos
  links_outer := by
    intro e v hv
    have h := (link_member L d stars ports hcard hpos hv).2
    rw [h]
    rfl
  port_load := by
    intro u o
    change ((stars.star u).filter fun e => (u,Sum.inr o) ∈
      link (I := I) L d stars ports hcard hpos e).card = d - Γ.degree (Sum.inr o)
    rw [port_count,hdegree]
    split <;> omega

#print axioms valid
end UnitPorts
end RobertPublishable.SUB
