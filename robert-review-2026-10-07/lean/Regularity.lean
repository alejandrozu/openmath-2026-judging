import Substitution
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # Regularity and bipartiteness of the actual substituted graph

The incidence decomposition also proves local finiteness when the skeleton has
infinitely many vertices. Regularity and bipartiteness are derived, not fields
of ValidSimpleSubstitution.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB
namespace ValidSimpleSubstitution
variable {U E I O : Type*} [DecidableEq U] [DecidableEq E]
  [DecidableEq I] [DecidableEq O] [Fintype I] [Fintype O]
  {Γ : SimpleGraph (I ⊕ O)} {L : LooplessMultigraph U E} {d : ℕ}
  {G : SimpleGraph (U × (I ⊕ O))} (T : ValidSimpleSubstitution Γ L d G)
include T

noncomputable def portEdges (v : U × (I ⊕ O)) : Finset E :=
  (T.regularStars.star v.1).filter (fun e => v ∈ T.projection.link e)

lemma internal_edge (u : U) (z : Sym2 (I ⊕ O)) (hz : z ∈ Γ.edgeSet) :
    Sym2.map (fun x => (u,x)) z ∈ G.edgeSet := by
  induction z using Sym2.inductionOn with | _ x y => ?_
  exact G.mem_edgeSet.mpr ((T.internal u x y).mpr (Γ.mem_edgeSet.mp hz))

lemma internal_diag (u : U) (z : Sym2 (I ⊕ O)) :
    (Sym2.map Prod.fst (Sym2.map (fun x => (u,x)) z)).IsDiag := by
  induction z using Sym2.inductionOn with | _ x y => ?_
  simp

noncomputable def incidenceMap (v : U × (I ⊕ O)) :
    Γ.incidenceSet v.2 ⊕ ↥(T.portEdges v) → G.incidenceSet v
  | Sum.inl z => ⟨Sym2.map (fun x => (v.1,x)) z.1, T.internal_edge v.1 z.1 z.2.1,
      Sym2.mem_map.mpr ⟨v.2,z.2.2,Prod.eta v⟩⟩
  | Sum.inr e => ⟨T.projection.link e.1, T.projection.link_edge e.1,
      (mem_filter.mp e.2).2⟩

lemma incidenceMap_injective (v : U × (I ⊕ O)) :
    Function.Injective (T.incidenceMap v) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      apply Subtype.ext
      exact Sym2.map.injective (fun x y h => congrArg Prod.snd h) (congrArg Subtype.val hab)
    | inr b =>
      have hd := T.internal_diag v.1 a.1
      have he : Sym2.map (fun x => (v.1,x)) a.1 = T.projection.link b.1 :=
        congrArg Subtype.val hab
      rw [he, ← T.projection.ends_eq] at hd
      exact False.elim (L.loopless b.1 hd)
  | inr a =>
    cases b with
    | inl b =>
      have hd := T.internal_diag v.1 b.1
      have he : Sym2.map (fun x => (v.1,x)) b.1 = T.projection.link a.1 :=
        (congrArg Subtype.val hab).symm
      rw [he, ← T.projection.ends_eq] at hd
      exact False.elim (L.loopless a.1 hd)
    | inr b =>
      congr 1
      exact Subtype.ext (T.projection.injective (congrArg Subtype.val hab))

lemma incidenceMap_surjective (v : U × (I ⊕ O)) :
    Function.Surjective (T.incidenceMap v) := by
  intro z
  let w := Sym2.Mem.other z.2.2
  have hw : s(v,w) = z.1 := Sym2.other_spec z.2.2
  have hadj : G.Adj v w := G.mem_edgeSet.mp (hw.symm ▸ z.2.1)
  by_cases hc : w.1 = v.1
  · have hΓ : Γ.Adj v.2 w.2 := (T.internal v.1 v.2 w.2).mp (by
      have hv : v = (v.1,v.2) := Prod.eta v
      have hw' : w = (v.1,w.2) := Prod.ext hc rfl
      rw [← hv, ← hw']; exact hadj)
    refine ⟨Sum.inl ⟨s(v.2,w.2), Γ.mem_incidenceSet v.2 w.2 |>.mpr hΓ⟩, ?_⟩
    apply Subtype.ext
    change s((v.1,v.2),(v.1,w.2)) = z.1
    have hv' : v = (v.1,v.2) := Prod.eta v
    have hw' : w = (v.1,w.2) := Prod.ext hc rfl
    rw [← hv', ← hw']
    exact hw
  · obtain ⟨e,he⟩ := T.projection.complete z.1 z.2.1 (by
      rw [← hw, Sym2.map_mk, Sym2.mk_isDiag_iff]
      exact Ne.symm hc)
    have hv : v ∈ T.projection.link e := he.symm ▸ z.2.2
    have hstar : e ∈ T.regularStars.star v.1 := by
      apply (T.regularStars.mem_star v.1 e).mpr
      rw [T.projection.ends_eq]
      exact Sym2.mem_map.mpr ⟨v,hv,rfl⟩
    refine ⟨Sum.inr ⟨e,mem_filter.mpr ⟨hstar,hv⟩⟩, ?_⟩
    exact Subtype.ext he

noncomputable def incidenceEquiv (v : U × (I ⊕ O)) :
    Γ.incidenceSet v.2 ⊕ ↥(T.portEdges v) ≃ G.incidenceSet v :=
  Equiv.ofBijective (T.incidenceMap v)
    ⟨T.incidenceMap_injective v, T.incidenceMap_surjective v⟩

noncomputable def locallyFinite : G.LocallyFinite := fun v =>
  Fintype.ofEquiv (Γ.incidenceSet v.2 ⊕ ↥(T.portEdges v))
    ((T.incidenceEquiv v).trans (G.incidenceSetEquivNeighborSet v))

lemma degree_eq (v : U × (I ⊕ O)) :
    @SimpleGraph.degree _ G v (T.locallyFinite v) = Γ.degree v.2 + (T.portEdges v).card := by
  letI := T.locallyFinite
  rw [← G.card_incidenceSet_eq_degree,
    ← Fintype.card_congr (T.incidenceEquiv v), Fintype.card_sum,
    Γ.card_incidenceSet_eq_degree, Fintype.card_coe]

theorem regular (hΓ : Gadget Γ d) :
    @SimpleGraph.IsRegularOfDegree _ G T.locallyFinite d := by
  intro v
  rw [T.degree_eq]
  rcases v with ⟨u, i | o⟩
  · rw [hΓ.inner_degree]
    have he : T.portEdges (u,Sum.inl i) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have h := T.links_outer e (u,Sum.inl i) (mem_filter.mp he).2
      simp [outerShore] at h
    simp [he]
  · rw [portEdges, T.port_load]
    exact Nat.add_sub_of_le (hΓ.outer_degree o)

def SkeletonBicoloring (L : LooplessMultigraph U E) (c : U → Bool) : Prop :=
  ∀ e u v, L.ends e = s(u,v) → c u ≠ c v

theorem bicoloring (hΓ : Gadget Γ d) (c : U → Bool) (hc : SkeletonBicoloring L c) :
    ∃ f : U × (I ⊕ O) → Bool, ∀ a b, G.Adj a b → f a ≠ f b := by
  refine ⟨fun v => xor (c v.1) (outerShore v.2), ?_⟩
  intro a b hab
  by_cases hcopy : a.1 = b.1
  · have ho := T.internal_shores hΓ a b hab hcopy
    cases ha : c a.1 <;> cases hb : c b.1 <;>
      cases hα : outerShore a.2 <;> cases hβ : outerShore b.2 <;> simp_all
  · have ho := T.external_shores a b hab hcopy
    obtain ⟨e,he⟩ := T.projection.complete s(a,b) (G.mem_edgeSet.mpr hab)
      (by simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using hcopy)
    have hc' : c a.1 ≠ c b.1 := hc e a.1 b.1 (by rw [T.projection.ends_eq, he]; rfl)
    simp only [ho.1,ho.2]
    cases ha : c a.1 <;> cases hb : c b.1 <;> simp_all

#print axioms regular
#print axioms bicoloring

theorem bipartite (hΓ : Gadget Γ d) (c : U → Bool) (hc : SkeletonBicoloring L c) :
    G.IsBipartite := by
  obtain ⟨f,hf⟩ := T.bicoloring hΓ c hc
  have h := (SimpleGraph.Coloring.mk f (fun {a b} hab => hf a b hab)).colorable
  simpa using h

#print axioms bipartite
end ValidSimpleSubstitution
end RobertPublishable.SUB
