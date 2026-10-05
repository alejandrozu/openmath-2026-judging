-- Lean proof of fact bde9371a01dd2855 (RH2F.layer23); added by fact_submit, do not edit
import MhFact_33aabc50b1cec1ba
set_option backward.isDefEq.respectTransparency false


/-
  TD1.lean — **Lemma TRI-BRICK-TD** (fact 7d38a456e3fbe169) for a triangle-with-digon piece `T` on the true side of
  a 3-edge-cut `K`: (a) if the pole `Q(X′, z)` is dominant and the restricted EX1 property (TD) holds, `P` is EX1-good;
  (b) (T1′) for `(X′, z, w_i)` implies (TD). Perfect matchings of `X′ = K.cont` through `z w_i` and perfect matchings
  of `P` through `e_i`, `a = y_j u`, `b = v y_k` correspond.
-/

namespace RH2F
open MGraph
open Classical

section td
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)

/-- the restricted EX1 property (TD) of fact 7d38a456e3fbe169: for every edge `g` inside the far side and every status
    `t` realized by a perfect matching through `e_i`, `a`, `b`, an MC colouring with `e_i`, `a`, `b` in colour class `6`
    (Lean colour `5`) and `[c(g) = 6] = t` -/
def TD : Prop :=
  ∀ g, K.flip.inA g → ∀ t : Bool,
    (∃ N, PMOn P N ∧ N (K.e i) ∧ N T.a ∧ N T.b ∧ (N g ↔ t = true)) →
    ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 ∧ (c g = 5 ↔ t = true)

include T

/-- **lifting a perfect matching** of `X′` through `z w_i` to `P` -/
theorem pm_lift (hG : InG X P) {N' : Fin (addHub X K.w).m → Prop} (hN' : PMOn K.cont N') (hNi : N' (hNew K.w i)) :
    ∃ N, PMOn P N ∧ N (K.e i) ∧ N T.a ∧ N T.b ∧ ∀ g, K.flip.inA g → (N g ↔ N' (K.toCont g)) := by
  let N : Fin X.m → Prop := fun f => (K.flip.inA f ∧ N' (K.toCont f)) ∨ f = K.e i ∨ f = T.a ∨ f = T.b
  have hNP : ∀ f, N f → P f := by
    rintro f (⟨hf, _⟩ | rfl | rfl | rfl)
    · exact hf.1
    · exact K.hP i
    · exact T.pa
    · exact T.pb
  have nIn : ∀ f, K.inA f → f ≠ T.a → f ≠ T.b → ¬ N f := by
    rintro f hf ha hb (⟨hf', _⟩ | h | h | h)
    · exact K.not_flip_of_inA hf hf'
    · exact K.not_inA_of_cut ⟨i, h⟩ hf
    · exact ha h
    · exact hb h
  have nCut : ∀ t, t ≠ i → ¬ N (K.e t) := by
    rintro t ht (⟨hf', _⟩ | h | h | h)
    · exact K.flip.not_inA_of_cut ⟨t, rfl⟩ hf'
    · exact ht (K.einj _ _ h)
    · exact T.e_ne_inner T.ja (K.sy j) T.su h
    · exact T.e_ne_inner T.jb T.sv (K.sy k) h
  have hhub : ∀ t, N' (hNew K.w t) → t = i := by
    intro t ht
    obtain ⟨a, _, _, hu⟩ := hN'.2 (hub K.w) ⟨hNew K.w i, Or.inr ⟨i, rfl⟩, hub_inc_new_hub _ i⟩
    exact hNew_inj _ ((hu _ ht (hub_inc_new_hub _ t)).trans (hu _ hNi (hub_inc_new_hub _ i)).symm)
  refine ⟨N, ⟨hNP, fun x hx => ?_⟩, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
    Or.inr (Or.inr (Or.inr rfl)), fun g hg => ⟨?_, fun h => Or.inl ⟨hg, h⟩⟩⟩
  rotate_left
  · rintro (⟨_, h⟩ | rfl | rfl | rfl)
    · exact h
    · exact absurd hg (K.flip.not_inA_of_cut ⟨i, rfl⟩)
    · exact absurd hg (K.not_flip_of_inA T.inA_a)
    · exact absurd hg (K.not_flip_of_inA T.inA_b)
  cases hs : K.S x
  · -- a vertex of the far side
    have hm : meets K.cont (hv K.w x) := (K.meets_cont_hv x).2 ⟨hx, hs⟩
    obtain ⟨e, he, hex, heu⟩ := hN'.2 _ hm
    obtain ⟨f, hfp, hfx, rfl⟩ := K.cont_at (hN'.1 e he) hex
    have hback : ∀ d, K.flip.pole d → X.Inc d x → (addHub X K.w).Inc (K.toCont d) (hv K.w x) := by
      intro d hd hdx
      have hj := K.toCont_joins hd
      rw [← K.toV_B hs]
      rcases hdx with h | h <;> rw [← h]
      · exact joins_inc_left hj
      · exact joins_inc_right hj
    rcases hfp with hf | ⟨t, rfl⟩
    · refine ⟨f, Or.inl ⟨hf, he⟩, hfx, fun d hd hdx => ?_⟩
      rcases hd with ⟨hd', hdN⟩ | rfl | rfl | rfl
      · exact K.toCont_inj (heu _ hdN (hback d (Or.inl hd') hdx))
      · -- `x = w_i`, and the hub edge at `i` is the matching edge at `x`
        have hxw : x = K.w i := by
          rcases inc_of_joins (K.hj i) hdx with h | h
          · rw [h, K.sy i] at hs; exact absurd hs (by decide)
          · exact h
        have := heu _ hNi (by rw [hxw]; exact (hub_inc_new _).2 rfl)
        rw [K.toCont_flip_inA hf] at this
        exact (hOld_ne_hNew _ _ _ this.symm).elim
      · exfalso; have := T.su; rcases inc_of_joins T.ja hdx with h | h <;> rw [h] at hs <;> simp_all [K.sy]
      · exfalso; have := T.sv; rcases inc_of_joins T.jb hdx with h | h <;> rw [h] at hs <;> simp_all [K.sy]
    · have e2 : K.toCont (K.flip.e t) = hNew K.w t := K.toCont_e t
      rw [e2] at he
      have hti := hhub t he
      subst hti
      refine ⟨K.e t, Or.inr (Or.inl rfl), hfx, fun d hd hdx => ?_⟩
      rcases hd with ⟨hd', hdN⟩ | rfl | rfl | rfl
      · have := heu _ hdN (hback d (Or.inl hd') hdx)
        rw [e2, K.toCont_flip_inA hd'] at this
        exact (hOld_ne_hNew _ _ _ this).elim
      · rfl
      · exfalso; have := T.su; rcases inc_of_joins T.ja hdx with h | h <;> rw [h] at hs <;> simp_all [K.sy]
      · exfalso; have := T.sv; rcases inc_of_joins T.jb hdx with h | h <;> rw [h] at hs <;> simp_all [K.sy]
  · -- a vertex of the piece
    rcases T.side x hs hx with rfl | rfl | rfl | rfl | rfl
    · refine ⟨K.e i, Or.inr (Or.inl rfl), joins_inc_left (K.hj i), fun d hd hdx => ?_⟩
      rcases T.at_yi hG d (hNP d hd) hdx with h | h | h
      · exact h
      · exact absurd (h ▸ hd) (nIn _ T.inA_t12 T.n12_a T.n12_b)
      · exact absurd (h ▸ hd) (nIn _ T.inA_t13 T.n13_a T.n13_b)
    · refine ⟨T.a, Or.inr (Or.inr (Or.inl rfl)), joins_inc_left T.ja, fun d hd hdx => ?_⟩
      rcases T.at_yj hG d (hNP d hd) hdx with h | h | h
      · exact absurd (h ▸ hd) (nCut j (Ne.symm T.hij))
      · exact absurd (h ▸ hd) (nIn _ T.inA_t12 T.n12_a T.n12_b)
      · exact h
    · refine ⟨T.b, Or.inr (Or.inr (Or.inr rfl)), joins_inc_right T.jb, fun d hd hdx => ?_⟩
      rcases T.at_yk hG d (hNP d hd) hdx with h | h | h
      · exact absurd (h ▸ hd) (nCut k (Ne.symm T.hik))
      · exact absurd (h ▸ hd) (nIn _ T.inA_t13 T.n13_a T.n13_b)
      · exact h
    · refine ⟨T.a, Or.inr (Or.inr (Or.inl rfl)), joins_inc_right T.ja, fun d hd hdx => ?_⟩
      rcases T.at_u hG d (hNP d hd) hdx with h | h | h
      · exact h
      · exact absurd (h ▸ hd) (nIn _ T.inA_d1 (Ne.symm T.na_d1) (Ne.symm T.nb_d1))
      · exact absurd (h ▸ hd) (nIn _ T.inA_d2 (Ne.symm T.na_d2) (Ne.symm T.nb_d2))
    · refine ⟨T.b, Or.inr (Or.inr (Or.inr rfl)), joins_inc_left T.jb, fun d hd hdx => ?_⟩
      rcases T.at_v hG d (hNP d hd) hdx with h | h | h
      · exact absurd (h ▸ hd) (nIn _ T.inA_d1 (Ne.symm T.na_d1) (Ne.symm T.nb_d1))
      · exact absurd (h ▸ hd) (nIn _ T.inA_d2 (Ne.symm T.na_d2) (Ne.symm T.nb_d2))
      · exact h


/-- **restricting a perfect matching** of `P` through `e_i`, `a`, `b` to `X′` -/
theorem pm_restrict (hG : InG X P) {N : Fin X.m → Prop} (hN : PMOn P N) (hi : N (K.e i)) (ha : N T.a)
    (hb : N T.b) :
    ∃ N', PMOn K.cont N' ∧ N' (hNew K.w i) ∧ ∀ g, K.flip.inA g → (N' (K.toCont g) ↔ N g) := by
  let N' : Fin (addHub X K.w).m → Prop := fun e => K.cont e ∧ ∃ f, K.flip.pole f ∧ e = K.toCont f ∧ N f
  have uniq : ∀ x d d', N d → N d' → X.Inc d x → X.Inc d' x → d = d' := by
    intro x d d' hd hd' hdx hd'x
    obtain ⟨a', _, _, hu⟩ := hN.2 x ⟨d, hN.1 d hd, hdx⟩
    exact (hu d hd hdx).trans (hu d' hd' hd'x).symm
  have cutN : ∀ t, N (K.e t) → t = i := by
    intro t ht
    rcases fin3_cases i j k t T.hij T.hik T.hjk with h | h | h
    · exact h
    · subst h
      exact absurd (uniq _ _ _ ht ha (joins_inc_left (K.hj t)) (joins_inc_left T.ja)) (T.e_ne_inner T.ja (K.sy t) T.su)
    · subst h
      exact absurd (uniq _ _ _ ht hb (joins_inc_left (K.hj t)) (joins_inc_right T.jb)) (T.e_ne_inner T.jb T.sv (K.sy t))
  refine ⟨N', ⟨fun e he => he.1, fun x hx => ?_⟩, ⟨Or.inr ⟨i, rfl⟩, K.e i, Or.inr ⟨i, rfl⟩, (K.toCont_e i).symm, hi⟩,
    fun g hg => ⟨fun ⟨_, f, _, hfe, hf⟩ => by rw [K.toCont_inj hfe]; exact hf,
      fun h => ⟨K.toCont_mem (Or.inl hg), g, Or.inl hg, rfl, h⟩⟩⟩
  obtain ⟨e0, he0, hx0⟩ := hx
  rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl
  · have hxv : (Fin.castSucc y : Fin (addHub X K.w).n) = hv K.w y := rfl
    have hmy := (K.meets_cont_hv y).1 ⟨e0, he0, hx0⟩
    obtain ⟨a', ha', hay, hau⟩ := hN.2 y hmy.1
    have hsy : K.flip.S y = true := by rw [Cut3.flip_S, hmy.2]; rfl
    have hap : K.flip.pole a' := K.flip.pole_of_inc (hN.1 a' ha') hay hsy
    have hinc : ∀ f, K.flip.pole f → X.Inc f y → (addHub X K.w).Inc (K.toCont f) (hv K.w y) := by
      intro f hf hfy
      have hj := K.toCont_joins hf
      rw [← K.toV_B hmy.2]
      rcases hfy with h | h <;> rw [← h]
      · exact joins_inc_left hj
      · exact joins_inc_right hj
    refine ⟨K.toCont a', ⟨K.toCont_mem hap, a', hap, rfl, ha'⟩, hinc a' hap hay, fun e he hex => ?_⟩
    obtain ⟨_, f, hf, rfl, hfN⟩ := he
    have hfy : X.Inc f y := by
      rcases Cut3.inc_of_joins' (K.toCont_joins hf) hex with h | h
      · have := K.toV_eq_hv h.symm; rw [← this.1]; exact Or.inl rfl
      · have := K.toV_eq_hv h.symm; rw [← this.1]; exact Or.inr rfl
    rw [hau f hfN hfy]
  · refine ⟨hNew K.w i, ⟨Or.inr ⟨i, rfl⟩, K.e i, Or.inr ⟨i, rfl⟩, (K.toCont_e i).symm, hi⟩,
      hub_inc_new_hub K.w i, fun e he hex => ?_⟩
    obtain ⟨_, f, hf, rfl, hfN⟩ := he
    rcases hf with hf | ⟨t, rfl⟩
    · rw [K.toCont_flip_inA hf] at hex; exact absurd hex (hub_not_inc_old _)
    · have ht := cutN t hfN
      subst ht
      exact K.toCont_e _

/-- **Lemma TRI-BRICK-TD (b)**: (T1′) for `(X′, z, w_i)` implies (TD) -/
theorem td_of_t1 (hG : InG X P) (hT1 : T1p K i) : T.TD := by
  intro g hg t ⟨N, hN, hi, ha, hb, hst⟩
  obtain ⟨N', hN', hNi, hNg⟩ := T.pm_restrict hG hN hi ha hb
  have hgc : K.cont (K.toCont g) := K.toCont_mem (Or.inl hg)
  have hgv : ¬ (addHub X K.w).Inc (K.toCont g) (hub K.w) := by
    rw [K.toCont_flip_inA hg]; exact hub_not_inc_old _
  obtain ⟨c1, hc1, hci, hst1, hpat⟩ := hT1 _ hgc hgv t ⟨N', hN', hNi, (hNg g hg).trans hst⟩
  obtain ⟨c, hc, hcψ, h1, h2, h3⟩ := T.m6b_lift hG c1 hc1 hci hpat
  exact ⟨c, hc, h1, h2, h3, by rw [hcψ g (Or.inl hg)]; exact hst1⟩

/-- **Lemma TRI-BRICK-TD (a)** -/
theorem tri_brick_td (hG : InG X P) (hdom : Dominant K.flip.hubPorts) (hTD : T.TD) : EX1On P := by
  have hw : ∀ t, CubicAt P (K.flip.w t) := fun t =>
    hG.2.2.2 (K.flip.w t) ⟨K.e t, K.hP t, joins_inc_left (K.hj t)⟩
  have hwK : ∀ t, CubicAt P (K.w t) := fun t =>
    hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩
  -- the lift through (TD)
  have viaTD : ∀ g, K.flip.inA g → ∀ t : Bool,
      (∃ N', PMOn K.cont N' ∧ N' (hNew K.w i) ∧ (N' (K.toCont g) ↔ t = true)) →
      ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 ∧ (c g = 5 ↔ t = true) := by
    intro g hg t ⟨N', hN', hNi, hst⟩
    obtain ⟨N, hN, hi, ha, hb, hNg⟩ := T.pm_lift hG hN' hNi
    exact hTD g hg t ⟨N, hN, hi, ha, hb, (hNg g hg).trans hst⟩
  -- Case 1.2: the pairs forcing the matching `B`
  have bad : ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 := by
    obtain ⟨N0, hN0, hN0i⟩ := RH2P.pstat _ K.cont (K.cont_inG hG) (hNew K.w i) (Or.inr ⟨i, rfl⟩) true
    obtain ⟨f0, _, _, hf0, _, _, _, _⟩ := K.pairB (hwK i)
    obtain ⟨c, hc, h1, h2, h3, _⟩ := viaTD f0 hf0 (decide (N0 (K.toCont f0))) ⟨N0, hN0, hN0i.2 rfl, by simp⟩
    exact ⟨c, hc, h1, h2, h3⟩
  -- gluing an MC colouring of `X_P` from the list `cl` at its colour-`6` port `s` with (D1)
  have key : ∀ (cl : List Nat), MCol (fun _ : Fin H6.m => True) (colL H6.m cl) → ∀ (s : Fin 3) (ts : Fin H6.m),
      T.es6 ts = hNew K.flip.w s → colL H6.m cl ts = 5 → ∀ (idx : Fin H6.m) (t : Bool),
      (colL H6.m cl idx = 5 ↔ t = true) → ∃ c, MCol P c ∧ (c (T.es9 idx) = 5 ↔ t = true) := by
    intro cl hmc s ts hts h5 idx t hst
    obtain ⟨c, hc, hcs, hcv⟩ := T.glue_XP hG hdom cl hmc hts h5
    obtain ⟨d, hd, hcomp⟩ := hdom.1 s _ _ _ (K.flip.dat_admissible hG.1 hw c hc hcs)
    obtain ⟨c'', hc'', _, hψ⟩ := K.flip.glue_track c hc hd hcomp
    have hp : K.flip.flip.pole (T.es9 idx) := by
      rw [Cut3.flip_flip_pole]
      fin_cases idx
      · exact Or.inr ⟨i, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
      · exact Or.inr ⟨k, rfl⟩
      · exact Or.inl T.inA_t12
      · exact Or.inl T.inA_t13
      · exact Or.inl T.inA_a
      · exact Or.inl T.inA_d1
      · exact Or.inl T.inA_d2
      · exact Or.inl T.inA_b
    refine ⟨c'', hc'', ?_⟩
    rw [hψ (T.es9 idx) hp, T.toCont_es9, hcv]
    exact hst
  have k2d := key c2d h6_c2d j ⟨1, by decide⟩ rfl rfl
  have k2d' := key c2d' h6_c2d' j ⟨1, by decide⟩ rfl rfl
  have k3d := key c3d h6_c3d k ⟨2, by decide⟩ rfl rfl
  apply ex1_of_mcol
  intro g hg t
  rcases K.flip.cases_P hg with hU | hPc | hcut
  · -- Case 2: `g` inside the far side, (D2)
    have hgc : K.flip.flip.cont (K.flip.flip.toCont g) := by
      rw [K.flip.flipToCont_inA hU]
      exact Or.inl ⟨g, rfl, by simp only [Cut3.flip_flip_inA]; exact hU⟩
    have hgv : ¬ (addHub X K.flip.flip.w).Inc (K.flip.flip.toCont g) (hub K.flip.flip.w) := by
      rw [K.flip.flipToCont_inA hU]; exact hub_not_inc_old _
    obtain ⟨s, hs⟩ := hdom.2 _ hgc hgv t
    rcases fin3_cases i j k s T.hij T.hik T.hjk with hsi | hsj | hsk
    · -- port `i`: the datum of Step 5, the matching of Step 6, then (T1′) and M6B-LIFT
      rw [hsi] at hs
      obtain ⟨d, hd, hcomp, hst⟩ := hs _ _ _ (step5_adm T.hij T.hik T.hjk)
      obtain ⟨N, hN, hNi, hNg⟩ := T.step6 hG hd hcomp (s5A_i T.hij T.hik T.hjk)
        (step5_adm T.hij T.hik T.hjk).1
      obtain ⟨c, hc, _, _, _, hst1⟩ := viaTD g hU t ⟨N, hN, hNi, (hNg g hU).trans hst⟩
      exact ⟨c, hc, hst1⟩
    · rw [hsj] at hs
      obtain ⟨c, hc, hcj, _⟩ := T.glue_XP hG hdom c2d h6_c2d (s := j) (ts := ⟨1, by decide⟩) rfl rfl
      obtain ⟨d, hd, hcomp, hst⟩ := hs _ _ _ (K.flip.dat_admissible hG.1 hw c hc hcj)
      obtain ⟨c'', hc'', hφ, _⟩ := K.flip.glue_track c hc hd hcomp
      exact ⟨c'', hc'', by rw [hφ g (Or.inl hU)]; exact hst⟩
    · rw [hsk] at hs
      obtain ⟨c, hc, hck, _⟩ := T.glue_XP hG hdom c3d h6_c3d (s := k) (ts := ⟨2, by decide⟩) rfl rfl
      obtain ⟨d, hd, hcomp, hst⟩ := hs _ _ _ (K.flip.dat_admissible hG.1 hw c hc hck)
      obtain ⟨c'', hc'', hφ, _⟩ := K.flip.glue_track c hc hd hcomp
      exact ⟨c'', hc'', by rw [hφ g (Or.inl hU)]; exact hst⟩
  all_goals
    -- Case 1: `g` in the piece or a cut edge
    have hgp : K.pole g := by
      first
        | exact Or.inl ((Cut3.flip_flip_inA K).1 ‹_›)
        | exact Or.inr ‹K.flip.isCut g›
    obtain ⟨idx, rfl⟩ := T.pole9 hG g hgp
    fin_cases idx <;> cases t
    all_goals
      first
        | exact k2d _ _ (by decide)
        | exact k2d' _ _ (by decide)
        | exact k3d _ _ (by decide)
        | (obtain ⟨c, hc, h1, h2, h3⟩ := bad
           first
             | exact ⟨c, hc, fun _ => rfl, fun _ => h1⟩
             | exact ⟨c, hc, fun _ => rfl, fun _ => h2⟩
             | exact ⟨c, hc, fun _ => rfl, fun _ => h3⟩)

end TriPiece

end td

end RH2F


/-
  TD2.lean — (TD-TRI), H-RED14 (c) (fact 71dbf09ece78f77e) and Theorem ROOT-CS4 (fact 6010cb59aaf31d7a) in Lean,
  from the finite facts; (T1′-TRI) implies (TD-TRI).
-/

namespace RH2F
open MGraph
open Classical

/-- (TD-TRI) (facts 71dbf09ece78f77e, 6010cb59aaf31d7a): at a triangle side `S` of a non-c4c member of 𝒮 carrying
    exactly one edge `δ` of `D`, inside `S`, the restricted EX1 property (TD) of fact 7d38a456e3fbe169 holds for
    `X = Q^D`: `e1 = (Cut3.dig C).e i` joins the apex `y1 = C.y i` to `w1`, `y2u = eO δ`, `vy3 = eN δ 2`, and `g`
    ranges over the edges of `X` inside `V_T` -/
def TDTRI : Prop :=
  ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → ¬ C4C Y Q → ∀ (C : Cut3 Q), CycSide Q C.S → scount Q C.S true = 3 →
    ∀ (D : Fin Y.m → Prop), 16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) →
    ∀ (i : Fin 3) (δ : Fin Y.m), Q δ → D δ → C.S (Y.ends δ).1 = true → C.S (Y.ends δ).2 = true →
      ¬ Y.Inc δ (C.y i) → (∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = δ) →
      ∀ g, (Cut3.dig (D := D) C).flip.inA g → ∀ t : Bool,
        (∃ N, PMOn (digSet Q D) N ∧ N ((Cut3.dig (D := D) C).e i) ∧ N (eO δ) ∧ N (eN δ 2) ∧ (N g ↔ t = true)) →
        ∃ c, MCol (digSet Q D) c ∧ c ((Cut3.dig (D := D) C).e i) = 5 ∧ c (eO δ) = 5 ∧ c (eN δ 2) = 5 ∧
          (c g = 5 ↔ t = true)

/-- H-RED14 (c) (fact 71dbf09ece78f77e), as a statement -/
def HRED14c : Prop := KD16_10 → POLE → TDTRI → Hyp

section qpiece
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

theorem triPiece_of {Y : MGraph} {Q : Fin Y.m → Prop} (hQ : InS Y Q) (C : Cut3 Q) (h3 : scount Q C.S true = 3)
    (D : Fin Y.m → Prop) (i : Fin 3) (δ : Fin Y.m) (hQδ : Q δ) (hDδ : D δ) (hδ1 : C.S (Y.ends δ).1 = true)
    (hδ2 : C.S (Y.ends δ).2 = true) (hδi : ¬ Y.Inc δ (C.y i))
    (huniq : ∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = δ) :
    ∃ (j k : Fin 3) (T : TriPiece (Cut3.dig (D := D) C) i j k), T.a = eO δ ∧ T.b = eN δ 2 := by
  have hloop : Loopless Y := hQ.1.1
  -- the side `S` consists of the three ends `C.y t`
  have hmem : ∀ x, meets Q x → C.S x = true → ∃ a, x = C.y a := by
    intro x hx hsx
    exact C.flip.sideB3 (by rw [Cut3.scount_flip3]; exact h3) hx (by simp [Cut3.flip_S, hsx])
  obtain ⟨j, hj⟩ := hmem _ (ends_meets1 hQδ) hδ1
  obtain ⟨k, hk⟩ := hmem _ (ends_meets2 hQδ) hδ2
  have hij : i ≠ j := by rintro rfl; exact hδi (Or.inl hj)
  have hik : i ≠ k := by rintro rfl; exact hδi (Or.inr hk)
  have hjk : j ≠ k := by rintro rfl; exact hloop δ (by rw [hj, hk])
  -- no cut edge carries a digon
  have hcutD : ∀ t, ¬ D (C.e t) := by
    intro t hD
    have hQe := C.hP t
    have hin : C.S (Y.ends (C.e t)).1 = true ∨ C.S (Y.ends (C.e t)).2 = true := by
      rcases C.hj t with h | h <;> rw [h] <;> simp [C.sy t]
    have := huniq _ hQe hD hin
    rw [← this] at hδ1 hδ2
    rcases C.hj t with h | h <;> rw [h] at hδ1 hδ2
    · rw [C.sw t] at hδ2; exact absurd hδ2 (by decide)
    · rw [C.sw t] at hδ1; exact absurd hδ1 (by decide)
  set K := Cut3.dig (D := D) C with hK
  have hKy : ∀ t, K.y t = dO (C.y t) := by
    intro t
    show cutY (D := D) C.S (C.e t) (C.y t) = dO (C.y t)
    unfold cutY; rw [if_neg (hcutD t)]
  -- the triangle edges at `y_i`
  have hS3 : ∀ x, meets Q x → C.S x = true → x = C.y i ∨ x = C.y j ∨ x = C.y k := by
    intro x hx hsx
    obtain ⟨a, rfl⟩ := hmem x hx hsx
    rcases fin3_cases i j k a hij hik hjk with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ :=
    hQ.1.2.2.2 (C.y i) ⟨C.e i, C.hP i, joins_inc_left (C.hj i)⟩
  -- the two edges at `y_i` other than `e_i`
  have inner : ∀ f, Q f → Y.Inc f (C.y i) → f ≠ C.e i →
      (Y.Joins f (C.y i) (C.y j) ∨ Y.Joins f (C.y i) (C.y k)) := by
    intro f hf hfi hne
    have hnc : ¬ C.isCut f := by
      rintro ⟨t, rfl⟩
      exact hne (by rw [C.cut_at_y hfi])
    have hin := C.inA_of_notcut hf hnc hfi (C.sy i)
    have hother : ∀ z, Y.Joins f (C.y i) z → z = C.y j ∨ z = C.y k := by
      intro z hz
      have hzS : C.S z = true := by
        rcases hz with h | h
        · have := hin.2.2; rw [h] at this; exact this
        · have := hin.2.1; rw [h] at this; exact this
      rcases hS3 z ⟨f, hf, joins_inc_right hz⟩ hzS with h | h | h
      · exact absurd (h ▸ hz) (fun hz' => by
          rcases hz' with h' | h' <;> exact hloop f (by rw [h']))
      · exact Or.inl h
      · exact Or.inr h
    rcases hfi with h | h
    · rcases hother (Y.ends f).2 (Or.inl (by rw [← h])) with e | e
      · exact Or.inl (Or.inl (by rw [← h, ← e]))
      · exact Or.inr (Or.inl (by rw [← h, ← e]))
    · rcases hother (Y.ends f).1 (Or.inr (by rw [← h])) with e | e
      · exact Or.inl (Or.inr (by rw [← h, ← e]))
      · exact Or.inr (Or.inr (by rw [← h, ← e]))
  -- two distinct edges at `y_i` other than `e_i`
  obtain ⟨f1, f2, hf1, hf2, if1, if2, n1, n2, n12⟩ : ∃ f1 f2, Q f1 ∧ Q f2 ∧ Y.Inc f1 (C.y i) ∧ Y.Inc f2 (C.y i) ∧
      f1 ≠ C.e i ∧ f2 ≠ C.e i ∧ f1 ≠ f2 := by
    rcases hall (C.e i) (C.hP i) (joins_inc_left (C.hj i)) with h | h | h
    · exact ⟨q, r, hq, hr, iq, ir, fun e => dpq (e.trans h).symm, fun e => dpr (e.trans h).symm, dqr⟩
    · exact ⟨p, r, hp, hr, ip, ir, fun e => dpq (e.trans h), fun e => dqr (e.trans h).symm, dpr⟩
    · exact ⟨p, q, hp, hq, ip, iq, fun e => dpr (e.trans h), fun e => dqr (e.trans h), dpq⟩
  obtain ⟨t12, t13, h12, h13, j12, j13⟩ : ∃ t12 t13, Q t12 ∧ Q t13 ∧ Y.Joins t12 (C.y i) (C.y j) ∧
      Y.Joins t13 (C.y i) (C.y k) := by
    rcases inner f1 hf1 if1 n1 with a1 | a1 <;> rcases inner f2 hf2 if2 n2 with a2 | a2
    · exact absurd (hQ.2.1 f1 f2 _ _ hf1 hf2 a1 a2) n12
    · exact ⟨f1, f2, hf1, hf2, a1, a2⟩
    · exact ⟨f2, f1, hf2, hf1, a2, a1⟩
    · exact absurd (hQ.2.1 f1 f2 _ _ hf1 hf2 a1 a2) n12
  -- they carry no digon
  have hn12 : t12 ≠ δ := ne_of_joins j12 (Or.inl (Prod.ext hj hk : Y.ends δ = (C.y j, C.y k))) (by
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hij (C.yinj _ _ h)
    · exact hik (C.yinj _ _ h))
  have hn13 : t13 ≠ δ := ne_of_joins j13 (Or.inl (Prod.ext hj hk : Y.ends δ = (C.y j, C.y k))) (by
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hij (C.yinj _ _ h)
    · exact hik (C.yinj _ _ h))
  have hD12 : ¬ D t12 := fun hD => hn12 (huniq _ h12 hD (by rcases j12 with h | h <;> rw [h] <;> simp [C.sy i]))
  have hD13 : ¬ D t13 := fun hD => hn13 (huniq _ h13 hD (by rcases j13 with h | h <;> rw [h] <;> simp [C.sy i]))
  -- the piece
  have joinsO : ∀ {f : Fin Y.m} {x y : Fin Y.n}, ¬ D f → Y.Joins f x y →
      (digG Y D).Joins (eO f) (dO x) (dO y) := by
    intro f x y hD hjf
    rcases hjf with h | h
    · exact Or.inl (by rw [ends_eO_nD hD, h])
    · exact Or.inr (by rw [ends_eO_nD hD, h])
  have hsu : K.S (dU δ) = true := by
    show indS (D := D) C.S (dU δ) = true
    rw [indS_dU, hδ1]; rfl
  have hsv : K.S (dV δ) = true := by
    show indS (D := D) C.S (dV δ) = true
    rw [indS_dV, hδ1]; rfl
  let T : TriPiece K i j k :=
    { hij := hij, hik := hik, hjk := hjk
      u := dU δ, v := dV δ
      t12 := eO t12, t13 := eO t13, a := eO δ, d1 := eN δ 0, d2 := eN δ 1, b := eN δ 2
      p12 := (set_eO Q t12).2 h12, p13 := (set_eO Q t13).2 h13, pa := (set_eO Q δ).2 hQδ
      pd1 := (set_eN Q δ 0).2 ⟨hQδ, hDδ⟩, pd2 := (set_eN Q δ 1).2 ⟨hQδ, hDδ⟩, pb := (set_eN Q δ 2).2 ⟨hQδ, hDδ⟩
      j12 := by rw [hKy, hKy]; exact joinsO hD12 j12
      j13 := by rw [hKy, hKy]; exact joinsO hD13 j13
      ja := by rw [hKy, ← hj]; exact Or.inl (ends_eO_D hDδ)
      jd1 := Or.inl (ends_eN01 δ 0 (by decide))
      jd2 := Or.inl (ends_eN01 δ 1 (by decide))
      jb := by rw [hKy, ← hk]; exact Or.inl (ends_eN2 δ)
      dd := fun h => absurd (eN_inj h).2 (by decide)
      su := hsu, sv := hsv
      uy := fun t => by rw [hKy]; exact fun h => dO_ne_dU _ _ h.symm
      vy := fun t => by rw [hKy]; exact fun h => dO_ne_dV _ _ h.symm
      uv := dU_ne_dV _ _
      side := fun x hx hxm => by
        rcases vert_cases x with ⟨z, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
        · have hzs : C.S z = true := by
            have : indS (D := D) C.S (dO z) = true := hx
            rwa [indS_dO] at this
          have hzm : meets Q z := (meets_dig_dO hloop z).1 hxm
          rcases hS3 z hzm hzs with rfl | rfl | rfl
          · exact Or.inl (hKy i).symm
          · exact Or.inr (Or.inl (hKy j).symm)
          · exact Or.inr (Or.inr (Or.inl (hKy k).symm))
        · have hdm := (meets_dig_dU d).1 hxm
          have hdS : (C.S (Y.ends d).1 || C.S (Y.ends d).2) = true := by
            have : indS (D := D) C.S (dU d) = true := hx
            rwa [indS_dU] at this
          have hd : d = δ := huniq d hdm.1 hdm.2 (by
            cases h : C.S (Y.ends d).1
            · rw [h] at hdS; exact Or.inr (by simpa using hdS)
            · exact Or.inl rfl)
          subst hd
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · have hdm := (meets_dig_dV d).1 hxm
          have hdS : (C.S (Y.ends d).1 || C.S (Y.ends d).2) = true := by
            have : indS (D := D) C.S (dV d) = true := hx
            rwa [indS_dV] at this
          have hd : d = δ := huniq d hdm.1 hdm.2 (by
            cases h : C.S (Y.ends d).1
            · rw [h] at hdS; exact Or.inr (by simpa using hdS)
            · exact Or.inl rfl)
          subst hd
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl))) }
  exact ⟨j, k, T, rfl, rfl⟩

end qpiece

section main14
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

/-- **the induction step**: `Q ∈ 𝒮`, `Q^D` with at least 16 vertices, all smaller 2-cut-reduced members of 𝒢 with at
    least 10 vertices EX1-good -/
theorem hred14_step (hKD : KD16_10) (hpole : POLE) (hTD : TDTRI) (hSH : SMALLHOSTD) (hPD : SMALLPD)
    (hQ : InS Y Q) (h16 : 16 ≤ vcount (digSet Q D))
    (ih : ∀ (X' : MGraph) (P' : Fin X'.m → Prop), InG X' P' → 10 ≤ vcount P' → TwoCutReducedOn P' →
      vcount P' < vcount (digSet Q D) → EX1On P') : EX1On (digSet Q D) := by
  obtain ⟨hGd, h2d, hvd⟩ := dig_class hQ.1 hQ.2.2 D
  have hn16 : 16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) := by rw [← hvd]; exact h16
  by_cases hc4 : C4C Y Q
  · by_cases hQ10 : 10 ≤ vcount Q
    · exact hKD Y Q D ⟨hc4, hQ.2.1, hQ10, hn16⟩
    · have hevQ := vcount_even' hQ.1
      exact hSH Y Q D hc4 hQ.2.1 (by omega) hn16
  obtain ⟨S, hS⟩ : ∃ S, CycSide Q S := by
    rcases Classical.em (∃ S, CycSide Q S) with hex | hex
    · exact hex
    · exact absurd ((c4c_iff_noCyc hQ.1 hQ.2.2).2 hex) hc4
  obtain ⟨C, hCS⟩ := cycCut hQ.1 hQ.2.2 hS
  subst hCS
  -- T1 and TRI-BRICK-EX at a triangle side `S'` of a cut `C'` carrying exactly one digon, inside `S'`
  have tri : ∀ (C' : Cut3 Q), CycSide Q C'.S → scount Q C'.S true = 3 → ∀ δ, Q δ → D δ →
      C'.S (Y.ends δ).1 = true → C'.S (Y.ends δ).2 = true →
      (∀ d, Q d → D d → (C'.S (Y.ends d).1 = true ∨ C'.S (Y.ends d).2 = true) → d = δ) →
      EX1On (digSet Q D) := by
    intro C' hcyc h3 δ hQδ hDδ h1 h2 huniq
    -- the side `V_S'` has 5 vertices
    have hc := scount_indS (D := D) hQ.1.1 (Q := Q) C'.S true
    have hcnt : cntF Y.m (fun d => Q d ∧ D d ∧ (C'.S (Y.ends d).1 || C'.S (Y.ends d).2) = true) = 1 := by
      apply le_antisymm
      · rw [← cntF_single Y.m δ]
        apply cntF_mono
        intro d ⟨hd, hDd, hSd⟩
        apply huniq d hd hDd
        cases h : C'.S (Y.ends d).1
        · rw [h] at hSd; exact Or.inr (by simpa using hSd)
        · exact Or.inl rfl
      · exact cntF_le_of_mem _ _ ⟨hQδ, hDδ, by simp [h1]⟩
    rw [h3, hcnt] at hc
    have hsp := vcount_split (digSet Q D) (Cut3.dig (D := D) C').S
    have hv5 : scount (digSet Q D) (Cut3.dig (D := D) C').S true = 5 := hc
    have hdom : ∀ E : Ports (Cut3.dig (D := D) C').cont (hub (Cut3.dig (D := D) C').w), Dominant E :=
      fun E => hpole _ _ ((Cut3.dig (D := D) C').cont_inG hGd) (by rw [Cut3.vcount_cont]; omega)
        ((Cut3.dig (D := D) C').cont_2cr h2d) _ E
    -- the apex `y_i`
    have hmem : ∀ x, meets Q x → C'.S x = true → ∃ a, x = C'.y a := by
      intro x hx hsx
      exact C'.flip.sideB3 (by rw [Cut3.scount_flip3]; exact h3) hx (by simp [Cut3.flip_S, hsx])
    obtain ⟨i, hi⟩ := exists_apex hQ.1.1 C'.y C'.yinj
      (let ⟨a, ha⟩ := hmem _ (ends_meets1 hQδ) h1; ⟨a, ha⟩) (let ⟨a, ha⟩ := hmem _ (ends_meets2 hQδ) h2; ⟨a, ha⟩)
    obtain ⟨j', k', T, hTa, hTb⟩ := triPiece_of hQ C' h3 D i δ hQδ hDδ h1 h2 hi huniq
    have hTD' : T.TD := by
      unfold TriPiece.TD; rw [hTa, hTb]
      exact hTD Y Q hQ hc4 C' hcyc h3 D hn16 i δ hQδ hDδ h1 h2 hi huniq
    have hdom' : Dominant (Cut3.dig (D := D) C').flip.hubPorts :=
      hpole _ _ ((Cut3.dig (D := D) C').flip.flip.cont_inG hGd) (by rw [vcount_flipflip_cont]; omega)
        ((Cut3.dig (D := D) C').flip.flip.cont_2cr h2d) _ _
    exact T.tri_brick_td hGd hdom' hTD'
  set K := Cut3.dig (D := D) C with hK
  have hsplit := vcount_split (digSet Q D) K.S
  have hodd := cut3_odd hGd K
  by_cases ha : 9 ≤ scount (digSet Q D) K.S true
  · by_cases hb : 9 ≤ scount (digSet Q D) K.S false
    · -- both sides have at least 9 vertices: (POLE) on `V_S`, induction on `V_T`
      have hdom : Dominant K.hubPorts :=
        hpole _ K.flip.cont (K.flip.cont_inG hGd) (by rw [vcount_flip_cont]; omega) (K.flip.cont_2cr h2d) _ K.hubPorts
      have hW : EX1On K.cont := ih _ K.cont (K.cont_inG hGd) (by rw [Cut3.vcount_cont]; omega) (K.cont_2cr h2d)
        (by rw [Cut3.vcount_cont]; omega)
      exact K.brick hGd hdom hW
    · -- the side `V_T` is small
      have hb7 : scount (digSet Q D) K.S false ≤ 7 := by have := hodd false; omega
      rcases small_side3 hpole hPD ih hGd h2d h16 K.flip (by rw [Cut3.scount_flip3]; exact hb7) with h | hA
      · exact h
      · obtain ⟨hT3, δ, hQδ, hDδ, hδ1, hδ2, huniq⟩ := apexT hQ C hA
        have h5 : scount (digSet Q D) K.S false = 5 := by
          have := (apex_digon hQ.2.1 _ hA).1; rw [Cut3.scount_flip3] at this; exact this
        by_cases hk : ∃ j, D (C.e j)
        · -- a cut edge carries a digon: shift it to the side `V_T`
          obtain ⟨j, hj⟩ := hk
          obtain ⟨K3, hK3⟩ := exists_shift hQ C j hj
          have h7 : scount (digSet Q D) K3.flip.S true = 7 := by
            rw [Cut3.scount_flip3]; show scount (digSet Q D) K3.S false = 7
            rw [hK3]; show scount (digSet Q D) K.S false + 2 = 7; omega
          rcases small_side3 hpole hPD ih hGd h2d h16 K3.flip (by omega) with h | hA3
          · exact h
          · exfalso; have := (apex_digon hQ.2.1 _ hA3).1; omega
        · -- no cut edge carries a digon: the triangle `T` with its digon, seen from `C.flip`
          apply tri C.flip (cycSide_flip hS) (by rw [Cut3.scount_flip3]; exact hT3) δ hQδ hDδ
            (by simp [Cut3.flip_S, hδ1]) (by simp [Cut3.flip_S, hδ2])
          intro d hd hDd hSd
          simp only [Cut3.flip_S, Bool.not_eq_true'] at hSd
          by_cases hb1 : C.S (Y.ends d).1 = false
          · by_cases hb2 : C.S (Y.ends d).2 = false
            · exact huniq d hd hDd hb1 hb2
            · exfalso
              obtain ⟨j, rfl⟩ := C.cut d hd (by rw [hb1]; simpa using hb2)
              exact hk ⟨j, hDd⟩
          · have hb2 : C.S (Y.ends d).2 = false := hSd.resolve_left hb1
            exfalso
            obtain ⟨j, rfl⟩ := C.cut d hd (by rw [hb2]; simpa using hb1)
            exact hk ⟨j, hDd⟩
  · -- the side `V_S` is small
    have ha7 : scount (digSet Q D) K.S true ≤ 7 := by have := hodd true; omega
    rcases small_side3 hpole hPD ih hGd h2d h16 K ha7 with h | hA
    · exact h
    · obtain ⟨hS3, δ, hQδ, hDδ, hδ1, hδ2, huniq⟩ := apexS hQ C hA
      exact tri C hS hS3 δ hQδ hDδ hδ1 hδ2 huniq

end main14

/-- **H-RED14 (c)** (fact 71dbf09ece78f77e) from the finite facts -/
theorem hred14c_of (hB12 : BASE12) (hS14 : SIMPLE14) (hB14 : B14D) (hSH : SMALLHOSTD) (hPD : SMALLPD) :
    HRED14c := by
  intro hKD hpole hTD X P
  generalize hn : vcount P = n
  induction n using Nat.strong_induction_on generalizing X P with
  | _ n ih =>
    intro hG h10 h2
    have hev := vcount_even' hG
    by_cases h14 : n ≤ 14
    · rcases (by omega : n = 10 ∨ n = 12 ∨ n = 14) with h | h | h
      · exact hB12 X P hG h2 (Or.inl (hn.trans h))
      · exact hB12 X P hG h2 (Or.inr (hn.trans h))
      · by_cases hs : SimpleP P
        · exact hS14 X P (inS_of_simple hG h2 hs) (hn.trans h)
        · exact hB14 X P hG h2 (hn.trans h) hs
    · obtain ⟨Y, Q, D, hQ, _, hvP, _, htr⟩ := hasm_converse hG h2 (by rw [hn]; exact h10)
      apply htr
      have hvd := vcount_dig hQ.1.1 (P := Q) (D := D)
      exact hred14_step hKD hpole hTD hSH hPD hQ (by omega)
        (fun X' P' hG' h10' h2' hlt => ih _ (by omega) X' P' rfl hG' h10' h2')


/-- **H-RED14 (d)**, first part: (T1′-TRI) implies (TD-TRI) -/
theorem tdtri_of_t1tri (hT1 : T1TRI) : TDTRI := by
  intro Y Q hQ hc4 C hcyc h3 D hn16 i δ hQδ hDδ hδ1 hδ2 hδi huniq
  obtain ⟨hGd, _, _⟩ := dig_class hQ.1 hQ.2.2 D
  obtain ⟨j, k, T, hTa, hTb⟩ := triPiece_of hQ C h3 D i δ hQδ hDδ hδ1 hδ2 hδi huniq
  have h := T.td_of_t1 hGd (hT1 Y Q hQ hc4 C hcyc h3 D hn16 i δ hQδ hDδ hδ1 hδ2 hδi huniq)
  unfold TriPiece.TD at h; rw [hTa, hTb] at h
  exact h

/-- **Theorem ROOT-CS4** (fact 6010cb59aaf31d7a) from the finite facts -/
theorem rootcs4 (hB12 : BASE12) (hS14 : SIMPLE14) (hB14 : B14D) (hSH : SMALLHOSTD) (hPD : SMALLPD)
    (hext : FEEXTD10) (hex : FEEXISTD10) (hpole : POLE) (htd : TDTRI) (hD : IID) : DMS :=
  dms_of_H_IID (hred14c_of hB12 hS14 hB14 hSH hPD (hred8_2 hext hex) hpole htd) hD

/-- **layer 23**: Lemma TRI-BRICK-TD, H-RED14 (c), ROOT-CS4, and (T1′-TRI) ⇒ (TD-TRI) -/
theorem layer23 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (K : Cut3 P) (i j k : Fin 3) (T : TriPiece K i j k), InG X P →
      Dominant K.flip.hubPorts → T.TD → EX1On P) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (K : Cut3 P) (i j k : Fin 3) (T : TriPiece K i j k), InG X P →
      T1p K i → T.TD) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD → HRED14c) ∧
    (T1TRI → TDTRI) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD →
      FEEXTD10 → FEEXISTD10 → POLE → TDTRI → IID → DMS) :=
  ⟨fun _ _ _ _ _ _ T hG hdom hTD => T.tri_brick_td hG hdom hTD,
   fun _ _ _ _ _ _ T hG hT1 => T.td_of_t1 hG hT1, hred14c_of, tdtri_of_t1tri, rootcs4⟩

end RH2F
