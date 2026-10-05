-- Lean proof of fact 974f7197c1be8069 (DmsIILean.dms_of_I_II); added by fact_submit, do not edit
/-
  DmsII.lean — the reduction "(I) and (II) imply DMS" in Lean, by the minimal-counterexample argument of the
  HOLE⇒DMS module of fact 5c1eb3f583cf643f with HOLE replaced by
  * DMS_I : every connected, bridgeless, loopless cubic edge set not isomorphic to K₃,₃ is star 6-colourable, and
  * DMS_II : every suppression configuration (SuppData: T(G0,g) or G0 with g subdivided, G0 = supp …
    connected, bridgeless, cubic, not K₃,₃) is star 6-colourable.
  Main theorem: `DmsIILean.dms_of_I_II`.
-/
import MhFact_5c1eb3f583cf643f

namespace DmsIILean
open MGraph

/-- statement (I) (for connected edge sets not isomorphic to K₃,₃) -/
def DMS_I : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → ConnectedOn P → BridgelessOn P → CubicOn P →
    ¬ IsoTo k33 P → Colourable P 6

/-- statement (II), in the suppression form used by the reduction -/
def DMS_II : Prop :=
  ∀ (G : MGraph) (Q : Fin G.m → Prop) (S : SuppData Q), Subcubic G → Loopless G → S.u ≠ S.w →
    ConnectedOn (supp Q S.y S.u S.w) → BridgelessOn (supp Q S.y S.u S.w) → CubicOn (supp Q S.y S.u S.w) →
    ¬ IsoTo k33 (supp Q S.y S.u S.w) → Colourable Q 6

variable {G : MGraph}

theorem minimal_impossible' (hI : DMS_I) (hII : DMS_II) (hsub : Subcubic G) (hloop : Loopless G) {Q : Fin G.m → Prop}
    (hmin : MinimalCounterexample Q 6) : False := by
  classical
  have hconn : ConnectedOn Q := minimal_connected hmin
  have hcoreconn : ConnectedOn (Core Q) := minimal_core_connected hmin
  have hcut : ∀ f, Core Q f → G.CutOn Q f → False := fun f hf B => core_no_cut hsub Q hmin hf B
  -- the far end of the edge at a vertex of degree one meets the core
  have hleaf : ∀ l p y, QDeg1 Q l → Q p → G.Joins p l y → ∃ f, Core Q f ∧ G.Inc f y := by
    intro l p y hl hp hj
    have hpp : Pendant Q p := pendant_of_deg1 hl hp (joins_inc_left hj)
    obtain ⟨l', y', hj', hleaf', f, g, hf, hg, hfp, hgp, hfg, hfy, hgy⟩ := pendant_attach hsub hmin hpp
    rcases joins_unique hj' hj with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact ⟨f, hf, h2 ▸ hfy⟩
    · exfalso
      obtain ⟨a, _, _, ha⟩ := hl
      exact hfp ((ha f hf.1 (h2 ▸ hfy)).trans (ha p hp (joins_inc_left hj)).symm)
  have hdeg2 : ∀ x, QDeg2 Q x → ∃ f, Core Q f ∧ G.Inc f x := by
    intro x hx
    obtain ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩ := id hx
    by_cases hac : Core Q a
    · exact ⟨a, hac, hax⟩
    · have hpa : Pendant Q a := Classical.byContradiction fun hp => hac ⟨hQa, hp⟩
      obtain ⟨z, haz, hz1⟩ := deg1_of_pendant hpa
      have hzx : z ≠ x := fun h => qdeg1_not2 (h ▸ hz1) hx
      exact hleaf z a x hz1 hQa (joins_of_inc_ne haz hax hzx)
  -- `Q` has an edge
  obtain ⟨e0, he0⟩ : ∃ f, Q f := by
    apply Classical.byContradiction
    intro h
    apply hmin.1
    exact ⟨fun _ => 0, fun a _ _ ha _ => absurd ⟨a, ha⟩ h, fun w h1 _ _ _ => absurd ⟨w.e1, h1⟩ h⟩
  -- the core edges are the edges of `Q` whose ends both have degree three
  have core_of_deg3 : ∀ f, Q f → (∀ x, G.Inc f x → QDeg3 Q x) → Core Q f := by
    intro f hf h3
    refine ⟨hf, fun hp => ?_⟩
    obtain ⟨x, hfx, hx1⟩ := deg1_of_pendant hp
    exact qdeg1_not3 hx1 (h3 x hfx)
  by_cases hR0 : ∃ r, QDeg1 Q r ∨ QDeg2 Q r
  · by_cases hR2 : ∃ r1 r2, r1 ≠ r2 ∧ (QDeg1 Q r1 ∨ QDeg2 Q r1) ∧ (QDeg1 Q r2 ∨ QDeg2 Q r2)
    · -- two vertices of degree ≤ 2: double `Q`
      obtain ⟨r1, r2, hr, hr1, hr2⟩ := hR2
      have hL := dbl.loopless hloop
      have hC := dblP_connected hconn hr1
      have hB := dblP_bridgeless hcoreconn hcut hleaf hdeg2 hr hr1 hr2
      have hK := dblP_cubic hsub Q
      obtain ⟨c, hc⟩ : Colourable (dblP Q) 6 := by
        by_cases hiso : IsoTo k33 (dblP Q)
        · exact k33_colourable hiso
        · exact hI (dbl G) (dblP Q) hL hC hB hK hiso
      apply hmin.1
      exact ⟨_, starOn_embed (G := G) (H := dbl G) (Q := Q) (P := dblP Q) dbl.vo dbl.eo
        (fun _ _ _ _ _ _ _ _ h => dbl.vo_inj h) (fun _ _ _ _ h => dbl.eo_inj h) (fun _ ha => dblP_eo.2 ha)
        (fun a _ => dbl.joins_eo (joins_ends a)) hc⟩
    · -- exactly one vertex `r` of degree ≤ 2: suppress it
      obtain ⟨r, hr⟩ := hR0
      have huniq : ∀ r', (QDeg1 Q r' ∨ QDeg2 Q r') → r' = r := fun r' hr' =>
        Classical.byContradiction fun hne => hR2 ⟨r', r, hne, hr', hr⟩
      have deg3_of : ∀ x, x ≠ r → (∃ f, Q f ∧ G.Inc f x) → QDeg3 Q x := by
        intro x hxr hx
        rcases qdeg_cases hsub Q hx with h1 | h2 | h3
        · exact absurd (huniq x (Or.inl h1)) hxr
        · exact absurd (huniq x (Or.inr h2)) hxr
        · exact h3
      have hS : Nonempty (SuppData Q) := by
        rcases hr with h1 | h2
        · -- `r` is a leaf `l` with pendant edge `p = l y`
          obtain ⟨p, hp, hpl, hpall⟩ := id h1
          obtain ⟨y, hjy⟩ := exists_joins_of_inc hpl
          have hjp : G.Joins p r y := joins_symm hjy
          have hyr : y ≠ r := Ne.symm (ne_of_joins hloop hjp)
          have hy3 : QDeg3 Q y := deg3_of y hyr ⟨p, hp, joins_inc_right hjp⟩
          obtain ⟨x1, x2, hQx1, hQx2, hx1y, hx2y, hx12, hx1p, hx2p, hally⟩ :=
            three_minus_one hy3 hp (joins_inc_right hjp)
          obtain ⟨u, hju⟩ := exists_joins_of_inc hx1y
          obtain ⟨w, hjw⟩ := exists_joins_of_inc hx2y
          have hru : r ≠ u := fun h => hx1p (hpall x1 hQx1 (h ▸ joins_inc_left hju))
          have hrw : r ≠ w := fun h => hx2p (hpall x2 hQx2 (h ▸ joins_inc_left hjw))
          exact ⟨
            { y := y, u := u, w := w, l := r, f1 := x1, f2 := x2
              hf1 := joins_symm hju, hf2 := joins_symm hjw, hQ1 := hQx1, hQ2 := hQx2, hf12 := hx12
              hy := fun d hd hdy => by
                rcases hally d hd hdy with h | h | h
                · exact Or.inr (Or.inr (h ▸ joins_symm hjp))
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
              hl := fun d d' hd hjd hd' hd'l =>
                (hpall d' hd' hd'l).trans (hpall d hd (joins_inc_right hjd)).symm
              hlu := hru, hlw := hrw
              hlleaf := Or.inr fun d hd hdl => (hpall d hd hdl) ▸ joins_symm hjp
              hrest := fun x hxy hxl hx => deg3_of x hxl hx }⟩
        · -- `r` is a vertex `y` of degree two
          obtain ⟨a, b, hQa, hQb, hay, hby, hab, habd⟩ := id h2
          obtain ⟨u, hju⟩ := exists_joins_of_inc hay
          obtain ⟨w, hjw⟩ := exists_joins_of_inc hby
          exact ⟨
            { y := r, u := u, w := w, l := r, f1 := a, f2 := b
              hf1 := joins_symm hju, hf2 := joins_symm hjw, hQ1 := hQa, hQ2 := hQb, hf12 := hab
              hy := fun d hd hdy => by
                rcases habd d hd hdy with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
              hl := fun d _ _ hjd _ _ => absurd rfl (ne_of_joins hloop hjd)
              hlu := ne_of_joins hloop (joins_symm hju)
              hlw := ne_of_joins hloop (joins_symm hjw)
              hlleaf := Or.inl rfl
              hrest := fun x hxy _ hx => deg3_of x hxy hx }⟩
      obtain ⟨S⟩ := hS
      have hyl3 : ∀ x, x ≠ S.y → x ≠ S.l → (∃ f, Q f ∧ G.Inc f x) → QDeg3 Q x := S.hrest
      -- edges of `Q` avoiding `y` are core edges
      have coreNotY : ∀ f, Q f → ¬ G.Inc f S.y → Core Q f := by
        intro f hf hfy
        apply core_of_deg3 f hf
        intro x hfx
        have := S.not_l_of_not_y hf hfy hfx
        exact hyl3 x this.1 this.2 ⟨f, hf, hfx⟩
      have hcutQ' : ∀ f, Q f → ¬ G.Inc f S.y → G.CutOn Q f → False :=
        fun f hf hfy B => hcut f (coreNotY f hf hfy) B
      have huw : S.u ≠ S.w := S.u_ne_w hloop hcutQ'
      have hyw := S.y_ne_w hloop
      have hf2core : Core Q S.f2 := by
        have hw3 : QDeg3 Q S.w := hyl3 S.w (Ne.symm hyw) (Ne.symm S.hlw) ⟨S.f2, S.hQ2, joins_inc_right S.hf2⟩
        obtain ⟨x1, _, hQx1, _, hx1w, _, _, hx1f, _, _⟩ := three_minus_one hw3 S.hQ2 (joins_inc_right S.hf2)
        exact ⟨S.hQ2, not_pendant_of_two S.hf2 S.hQ1 S.hf12 (joins_inc_left S.hf1) hQx1 hx1f hx1w⟩
      have hcutQ'' : ∀ f, Q f → (f = S.f2 ∨ ¬ G.Inc f S.y) → G.CutOn Q f → False := by
        intro f hf hcase B
        rcases hcase with rfl | hfy
        · exact hcut _ hf2core B
        · exact hcut f (coreNotY f hf hfy) B
      have hL := addEdge_loopless hloop huw
      have hC := S.supp_connected hloop hconn
      have hB := S.supp_bridgeless hloop hcutQ''
      have hK := S.supp_cubic hloop huw
      apply hmin.1
      by_cases hiso : IsoTo k33 (supp Q S.y S.u S.w)
      · exact k33_supp_colourable hloop S hiso
      · exact hII G Q S hsub hloop huw hC hB hK hiso
  · -- no vertex of degree ≤ 2: `Q` itself is cubic
    have hK : CubicOn Q := by
      intro x hx
      rcases qdeg_cases hsub Q hx with h1 | h2 | h3
      · exact absurd ⟨x, Or.inl h1⟩ hR0
      · exact absurd ⟨x, Or.inr h2⟩ hR0
      · exact h3
    have hB : BridgelessOn Q := by
      intro f hf B
      by_cases hfc : Core Q f
      · exact hcut f hfc B
      · obtain ⟨x, _, hx1⟩ := deg1_of_pendant (Classical.byContradiction fun hp => hfc ⟨hf, hp⟩)
        exact hR0 ⟨x, Or.inl hx1⟩
    apply hmin.1
    by_cases hiso : IsoTo k33 Q
    · exact k33_colourable hiso
    · exact hI G Q hloop hconn hB hK hiso


/-- **(I) and (II) imply DMS**: every loopless subcubic multigraph is star 6-edge-colourable. -/
theorem dms_of_I_II (hI : DMS_I) (hII : DMS_II) :
    ∀ (G : MGraph), Subcubic G → Loopless G → ∀ P : Fin G.m → Prop, Colourable P 6 := by
  intro G hsub hloop P
  apply Classical.byContradiction
  intro hP
  obtain ⟨Q, -, hmin⟩ := exists_minimal 6 P hP
  exact minimal_impossible' hI hII hsub hloop hmin

end DmsIILean
