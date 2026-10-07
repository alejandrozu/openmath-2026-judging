import Piece
import SkeletonK
import Substitution

/-! # Explicit bipartite six-regular pair-free skeleton L6b

The orientation and all 48 labelled edges are the original PROOF-R1 data.
Small cuts of two and then three edges confine a hypothetical pair to one
piece. The resulting actual connected two-regular piece cycles contradict the
proved local piece lemma. No enumeration of cycle pairs is assumed.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

def arcSource (e : Fin 8) : Fin 4 :=
  if e.val < 2 then 0 else if e.val < 3 then 3 else if e.val < 5 then 1
  else if e.val < 7 then 2 else 3
def arcTarget (e : Fin 8) : Fin 4 :=
  if e.val < 2 then 3 else if e.val < 3 then 0 else if e.val < 5 then 2
  else if e.val < 6 then 1 else if e.val < 7 then 0 else 1

abbrev BVertex := Fin 4 × Fin 4
abbrev BEdge := (Fin 4 × Fin 10) ⊕ Fin 8

def bEnds : BEdge → Sym2 BVertex
  | Sum.inl (u,k) => Sym2.map (fun i => (u,i)) (piece.ends k)
  | Sum.inr e => s((arcSource e,3),(arcTarget e,0))

def skeletonB : LooplessMultigraph BVertex BEdge where
  ends := bEnds
  loopless := by
    intro e
    cases e with
    | inl p =>
      rcases p with ⟨u,k⟩
      have hn := piece.loopless k
      change ¬ (Sym2.map (fun i => (u,i)) (piece.ends k)).IsDiag
      generalize hz : piece.ends k = z at *
      induction z using Sym2.inductionOn with | _ a b => ?_
      simpa [bEnds,Sym2.mk_isDiag_iff,Sym2.map_mk] using hn
    | inr e => simp [bEnds,Sym2.mk_isDiag_iff]

lemma arcs_match_K (e : Fin 8) : skeletonK.ends e = s(arcSource e,arcTarget e) := by
  revert e
  decide
lemma arcs_distinct (e : Fin 8) : arcSource e ≠ arcTarget e := by revert e; decide

def bColor (v : BVertex) : Bool := kColor v.1
def copyColor (u : Fin 4) (v : BVertex) : Bool := decide (v.1 = u)
def outerCut : Finset BEdge := kCut.image Sum.inr
def localCut (u : Fin 4) : Finset BEdge := (kBundle (kColor u)).image Sum.inr

lemma outerCut_size : outerCut.card ≤ 3 := by decide
lemma localCut_size (u : Fin 4) : (localCut u).card ≤ 3 := by
  rw [localCut,card_image_of_injective _ Sum.inr_injective,k_bundle_card]

lemma no_internal_cross (color : Fin 4 → Bool) (u : Fin 4) (k : Fin 10) :
    ¬ Crosses (fun v : BVertex => color v.1) true (skeletonB.ends (Sum.inl (u,k))) := by
  change ¬ Crosses _ true (Sym2.map (fun i => (u,i)) (piece.ends k))
  generalize hz : piece.ends k = z
  induction z using Sym2.inductionOn with | _ a b => ?_
  simp

lemma outerCut_exact (e : BEdge) : Crosses bColor true (skeletonB.ends e) → e ∈ outerCut := by
  cases e with
  | inl p =>
    exact fun h => False.elim (no_internal_cross kColor p.1 p.2 h)
  | inr e =>
    intro h
    have hx : Crosses kColor true (skeletonK.ends e) := by
      simpa only [arcs_match_K,bColor,skeletonB,bEnds,crosses_mk] using h
    exact mem_image.mpr ⟨e,k_cut_contains e hx,rfl⟩

lemma cycles_constant_copy (S : Finset BVertex) (F H : Finset BEdge)
    (hF : skeletonB.IsCycleOn S F) (hH : skeletonB.IsCycleOn S H) (hd : Disjoint F H)
    (u : BVertex) (hu : u ∈ S) : ∀ v ∈ S, v.1 = u.1 := by
  classical
  have hh : ∀ v ∈ S, bColor v = bColor u := by
    intro v hv
    exact (skeletonB.pair_constant_of_small_cut S F H hF hH hd bColor outerCut
      outerCut_exact outerCut_size hu hv).symm
  have hinc (e : BEdge) (he : e ∈ F ∪ H) (v : BVertex) (hv : v ∈ skeletonB.ends e) : v ∈ S := by
    rcases mem_union.mp he with he | he
    · exact LooplessMultigraph.IsCycleOn.mem_support_of_incident skeletonB hF he hv
    · exact LooplessMultigraph.IsCycleOn.mem_support_of_incident skeletonB hH he hv
  have hcut : ∀ e ∈ F ∪ H, Crosses (copyColor u.1) true (skeletonB.ends e) → e ∈ localCut u.1 := by
    intro e he hc
    cases e with
    | inl p => exact False.elim (no_internal_cross (fun w => decide (w = u.1)) p.1 p.2 hc)
    | inr e =>
      have hs : kColor (arcSource e) = kColor u.1 :=
        hh (arcSource e,3) (hinc _ he (arcSource e,3) (by simp [skeletonB,bEnds]))
      have ht : kColor (arcTarget e) = kColor u.1 :=
        hh (arcTarget e,0) (hinc _ he (arcTarget e,0) (by simp [skeletonB,bEnds]))
      have heB : e ∈ kBundle (kColor u.1) := by
        apply k_bundle_of_constant
        intro w hw
        rw [arcs_match_K,Sym2.mem_iff] at hw
        rcases hw with rfl | rfl <;> assumption
      exact mem_image.mpr ⟨e,heB,rfl⟩
  intro v hv
  have hc := (skeletonB.pair_constant_of_small_cut_on S F H hF hH hd
    (copyColor u.1) (localCut u.1) hcut (localCut_size u.1) hu hv).symm
  simpa [copyColor] using hc

def embedPiece (u : Fin 4) (k : Fin 10) : BEdge := Sum.inl (u,k)
lemma embedPiece_injective (u : Fin 4) : Function.Injective (embedPiece u) := by
  intro x y h
  exact (Prod.mk.inj (Sum.inl.inj h)).2

lemma local_edges (S : Finset BVertex) (F : Finset BEdge)
    (hF : skeletonB.IsCycleOn S F) (u : Fin 4) (hc : ∀ v ∈ S, v.1 = u)
    (e : BEdge) (he : e ∈ F) : ∃ k, embedPiece u k = e := by
  cases e with
  | inl p =>
    rcases p with ⟨w,k⟩
    have hn : ∃ i, i ∈ piece.ends k := by
      generalize hz : piece.ends k = z
      induction z using Sym2.inductionOn with | _ a b => exact ⟨a,by simp⟩
    obtain ⟨i,hi⟩ := hn
    have hs : (w,i) ∈ S := LooplessMultigraph.IsCycleOn.mem_support_of_incident
      skeletonB hF he (Sym2.mem_map.mpr ⟨i,hi,rfl⟩)
    have hw : w = u := hc (w,i) hs
    subst w
    exact ⟨k,rfl⟩
  | inr e =>
    have hs := hc (arcSource e,3) (LooplessMultigraph.IsCycleOn.mem_support_of_incident
      skeletonB hF he (by simp [skeletonB,bEnds]))
    have ht := hc (arcTarget e,0) (LooplessMultigraph.IsCycleOn.mem_support_of_incident
      skeletonB hF he (by simp [skeletonB,bEnds]))
    exact False.elim (arcs_distinct e (hs.trans ht.symm))

noncomputable def localEdges (F : Finset BEdge) (u : Fin 4) : Finset (Fin 10) :=
  F.preimage (embedPiece u) (embedPiece_injective u).injOn

lemma mem_localEdges (F : Finset BEdge) (u : Fin 4) (k : Fin 10) :
    k ∈ localEdges F u ↔ embedPiece u k ∈ F := by simp [localEdges]

lemma local_incidence (u : Fin 4) (i : Fin 4) (k : Fin 10) :
    (u,i) ∈ skeletonB.ends (embedPiece u k) ↔ i ∈ piece.ends k := by
  simp [skeletonB,bEnds,embedPiece,Sym2.mem_map]

lemma local_cycle (S : Finset BVertex) (F : Finset BEdge)
    (hF : skeletonB.IsCycleOn S F) (u : Fin 4) (hc : ∀ v ∈ S, v.1 = u) :
    piece.IsCycleOn (S.image Prod.snd) (localEdges F u) := by
  classical
  have hlocal := local_edges S F hF u hc
  have hmem (i : Fin 4) : (u,i) ∈ S ↔ i ∈ S.image Prod.snd := by
    constructor
    · intro hi; exact mem_image.mpr ⟨(u,i),hi,rfl⟩
    · intro hi
      obtain ⟨v,hv,hvi⟩ := mem_image.mp hi
      have hv' : v = (u,i) := Prod.ext (hc v hv) hvi
      exact hv' ▸ hv
  have hdeg (i : Fin 4) : piece.degree (localEdges F u) i = skeletonB.degree F (u,i) := by
    have heq : ((localEdges F u).filter (fun k => i ∈ piece.ends k)).image (embedPiece u) =
        F.filter (fun e => (u,i) ∈ skeletonB.ends e) := by
      ext e
      constructor
      · intro he
        obtain ⟨k,hk,rfl⟩ := mem_image.mp he
        exact mem_filter.mpr ⟨(mem_localEdges F u k).mp (mem_filter.mp hk).1,
          (local_incidence u i k).mpr (mem_filter.mp hk).2⟩
      · intro he
        obtain ⟨k,hk⟩ := hlocal e (mem_filter.mp he).1
        refine mem_image.mpr ⟨k,mem_filter.mpr ⟨?_,?_⟩,hk⟩
        · exact (mem_localEdges F u k).mpr (hk.symm ▸ (mem_filter.mp he).1)
        · exact (local_incidence u i k).mp (hk.symm ▸ (mem_filter.mp he).2)
    unfold LooplessMultigraph.degree
    rw [← heq,card_image_of_injective _ (embedPiece_injective u)]
  let hom : skeletonB.supportGraph F →g piece.supportGraph (localEdges F u) :=
    { toFun := Prod.snd
      map_rel' := fun {a b} hab => by
        obtain ⟨e,heF,he⟩ := mem_image.mp hab.1
        obtain ⟨k,hk⟩ := hlocal e heF
        have haS : a ∈ S := LooplessMultigraph.IsCycleOn.mem_support_of_incident
          skeletonB hF heF (he.symm ▸ (by simp : a ∈ s(a,b)))
        have hbS : b ∈ S := LooplessMultigraph.IsCycleOn.mem_support_of_incident
          skeletonB hF heF (he.symm ▸ (by simp : b ∈ s(a,b)))
        change s(a.2,b.2) ∈ (↑((localEdges F u).image piece.ends) : Set (Sym2 (Fin 4))) ∧ a.2 ≠ b.2
        refine ⟨mem_image.mpr ⟨k,(mem_localEdges F u k).mpr (hk.symm ▸ heF),?_⟩,?_⟩
        · have hh := congrArg (Sym2.map Prod.snd) (hk.symm ▸ he)
          simpa [skeletonB,bEnds,embedPiece,Sym2.map_mk,Sym2.map_map,Function.comp_def] using hh
        · intro h
          exact hab.2 (Prod.ext ((hc a haS).trans (hc b hbS).symm) h) }
  refine ⟨hF.nonempty.image Prod.snd,?_,?_⟩
  · intro i
    rw [hdeg,hF.degree_eq]
    simp only [hmem]
  · intro i hi j hj
    exact SimpleGraph.Reachable.map hom
      (hF.connected (u,i) ((hmem i).mpr hi) (u,j) ((hmem j).mpr hj))

theorem skeletonB_pairfree : ¬ skeletonB.HasPair := by
  classical
  rintro ⟨S,F,H,hF,hH,hd⟩
  obtain ⟨u,hu⟩ := hF.nonempty
  have hc := cycles_constant_copy S F H hF hH hd u hu
  apply piece_pairfree
  refine ⟨S.image Prod.snd,localEdges F u.1,localEdges H u.1,
    local_cycle S F hF u.1 hc,local_cycle S H hH u.1 hc,?_⟩
  apply Finset.disjoint_left.mpr
  intro k hk hh
  exact Finset.disjoint_left.mp hd ((mem_localEdges F u.1 k).mp hk)
    ((mem_localEdges H u.1 k).mp hh)

def skeletonB_stars : RegularStars skeletonB 6 where
  star v := univ.filter (fun e => v ∈ skeletonB.ends e)
  mem_star := by intro v e; simp
  card_star := by
    intro v
    rcases v with ⟨u,i⟩
    fin_cases u <;> fin_cases i <;> decide

def skeletonB_bicolor (v : BVertex) : Bool := decide (v.2 = 1 ∨ v.2 = 3)
theorem skeletonB_bipartite : ∀ e u v, skeletonB.ends e = s(u,v) →
    skeletonB_bicolor u ≠ skeletonB_bicolor v := by decide

#print axioms skeletonB_pairfree
#print axioms skeletonB_bipartite
end RobertPublishable.SUB
