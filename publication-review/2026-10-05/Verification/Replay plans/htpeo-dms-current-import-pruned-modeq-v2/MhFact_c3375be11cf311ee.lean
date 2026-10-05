-- Lean proof of fact c3375be11cf311ee (RH2F.layer17); added by fact_submit, do not edit
import MhFact_81c52cea8147de67
import MhFact_6c78409a046a3fe7
set_option backward.isDefEq.respectTransparency false

/-
  IV4.lean — back from H^D to H: if `Q^D` is connected, bridgeless, resp. 2-cut-reduced (with no digon on old
  vertices), then `Q` is connected, bridgeless, resp. has no 2-edge-cut (the L(T) argument of H-ASM (a)).
-/

namespace RH2F
open MGraph
open Classical

section back
variable {Y : MGraph} {D : Fin Y.m → Prop}

/-- a vertex 2-colouring of `Y` extended to `digG Y D`: both new vertices of `d` get the value of the first end of `d` -/
noncomputable def liftD (U : Fin Y.n → Bool) (w : Fin (digG Y D).n) : Bool :=
  if h : w.val < Y.n then U ⟨w.val, h⟩
  else U (Y.ends ⟨(w.val - Y.n) / 2, by have := w.isLt; change w.val < Y.n + 2 * Y.m at this; omega⟩).1

theorem liftD_dO (U : Fin Y.n → Bool) (x : Fin Y.n) : liftD (D := D) U (dO x) = U x := by
  simp [liftD, dO, x.isLt]

theorem liftD_dU (U : Fin Y.n → Bool) (d : Fin Y.m) : liftD (D := D) U (dU d) = U (Y.ends d).1 := by
  have h : ¬ (dU d : Fin (Y.n + 2 * Y.m)).val < Y.n := by simp only [dU]; omega
  have hd : (⟨((dU d : Fin (Y.n + 2 * Y.m)).val - Y.n) / 2, by have := d.isLt; simp only [dU]; omega⟩ : Fin Y.m) = d :=
    Fin.ext (by simp only [dU]; omega)
  simp only [liftD, dif_neg h]
  rw [hd]

theorem liftD_dV (U : Fin Y.n → Bool) (d : Fin Y.m) : liftD (D := D) U (dV d) = U (Y.ends d).1 := by
  have h : ¬ (dV d : Fin (Y.n + 2 * Y.m)).val < Y.n := by simp only [dV]; omega
  have hd : (⟨((dV d : Fin (Y.n + 2 * Y.m)).val - Y.n) / 2, by have := d.isLt; simp only [dV]; omega⟩ : Fin Y.m) = d :=
    Fin.ext (by simp only [dV]; omega)
  simp only [liftD, dif_neg h]
  rw [hd]

/-- the lifted colouring is constant on the digSet edges of `d` except possibly the edge that carries the change
    between the two ends of `d`: `eO d` if `¬ D d`, `eN d 2` if `D d` -/
theorem liftD_const {Q : Fin Y.m → Prop} (U : Fin Y.n → Bool) (e : Fin (digG Y D).m) (he : digSet Q D e) :
    liftD U ((digG Y D).ends e).1 = liftD U ((digG Y D).ends e).2 ∨
      ∃ d, Q d ∧ (e = (if D d then eN d 2 else eO d)) ∧ liftD (D := D) U ((digG Y D).ends e).1 = U (Y.ends d).1 ∧
        liftD (D := D) U ((digG Y D).ends e).2 = U (Y.ends d).2 := by
  rcases dig_cases e with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
  · have hd := (set_eO Q d).1 he
    by_cases hD : D d
    · left; rw [ends_eO_D hD]; simp only; rw [liftD_dO, liftD_dU]
    · right; refine ⟨d, hd, by rw [if_neg hD], ?_, ?_⟩ <;> rw [ends_eO_nD hD] <;> simp only [liftD_dO]
  · obtain ⟨hd, hD⟩ := (set_eN Q d k).1 he
    rcases k_cases k with rfl | hk
    · right; refine ⟨d, hd, by rw [if_pos hD], ?_, ?_⟩ <;> rw [ends_eN2] <;> simp only [liftD_dO, liftD_dV]
    · left; rw [ends_eN01 d k hk]; simp only; rw [liftD_dU, liftD_dV]

/-- the change-carrying edge of `d` has ends with the values of the two ends of `d` -/
theorem carrier_ends {Q : Fin Y.m → Prop} (U : Fin Y.n → Bool) (d : Fin Y.m) :
    liftD (D := D) U ((digG Y D).ends (if D d then eN d 2 else eO d)).1 = U (Y.ends d).1 ∧
      liftD (D := D) U ((digG Y D).ends (if D d then eN d 2 else eO d)).2 = U (Y.ends d).2 := by
  by_cases hD : D d
  · rw [if_pos hD, ends_eN2]; simp only [liftD_dV, liftD_dO, and_self]
  · rw [if_neg hD, ends_eO_nD hD]; simp only [liftD_dO, and_self]

theorem carrier_set {Q : Fin Y.m → Prop} {d : Fin Y.m} (hd : Q d) : digSet Q D (if D d then eN d 2 else eO d) := by
  by_cases hD : D d
  · rw [if_pos hD]; exact (set_eN Q d 2).2 ⟨hd, hD⟩
  · rw [if_neg hD]; exact (set_eO Q d).2 hd

theorem carrier_inj {d d' : Fin Y.m}
    (h : (if D d then eN d 2 else eO d : Fin (digG Y D).m) = if D d' then eN d' 2 else eO d') : d = d' := by
  split_ifs at h
  · exact (eN_inj h).1
  · exact absurd h (eO_ne_eN _ _ _).symm
  · exact absurd h (eO_ne_eN _ _ _)
  · exact eO_inj h

/-- **connected** -/
theorem back_connected {Q : Fin Y.m → Prop} (h : ConnectedOn (digSet Q D)) : ConnectedOn Q := by
  intro U hU f g hf hg
  have hc := h (liftD U) (fun e he => by
    rcases liftD_const U e he with h1 | ⟨d, hd, _, h1, h2⟩
    · exact h1
    · rw [h1, h2]; exact hU d hd)
  have := hc (eO f) (eO g) ((set_eO Q f).2 hf) ((set_eO Q g).2 hg)
  rw [ends_eO, ends_eO] at this
  split_ifs at this <;> simpa [liftD_dO] using this

/-- **bridgeless** -/
theorem back_bridgeless {Q : Fin Y.m → Prop} (h : BridgelessOn (digSet Q D)) : BridgelessOn Q := by
  intro e he B
  apply h _ (carrier_set (D := D) he)
  have hc := carrier_ends (D := D) (Q := Q) B.U e
  exact { U := liftD B.U
          hu := by rw [hc.1]; exact B.hu
          hv := by rw [hc.2]; exact B.hv
          sep := fun e' he' hne => by
            rcases liftD_const B.U e' he' with h1 | ⟨d, hd, rfl, h1, h2⟩
            · exact h1
            · rw [h1, h2]
              exact B.sep d hd (fun hde => hne (by rw [hde])) }

/-- side counts of the lifted colouring -/
theorem scount_dig (hloop : Loopless Y) {Q : Fin Y.m → Prop} (S : Fin Y.n → Bool) (b : Bool) :
    scount (digSet Q D) (liftD S) b = scount Q S b + 2 * cntF Y.m (fun d => (Q d ∧ D d) ∧ S (Y.ends d).1 = b) := by
  unfold scount
  let A : Finset (Fin Y.m) := Finset.univ.filter (fun d => (Q d ∧ D d) ∧ S (Y.ends d).1 = b)
  have hA : cntF Y.m (fun d => (Q d ∧ D d) ∧ S (Y.ends d).1 = b) = A.card := by rw [cntF_eq_card]; convert rfl
  rw [cntF_eq_card, cntF_eq_card, hA]
  have hset : ∀ w, (meets (digSet Q D) w ∧ liftD S w = b) ↔
      w ∈ (Finset.univ.filter (fun x => meets Q x ∧ S x = b)).image dO ∪ (A.image dU ∪ A.image dV) := by
    intro w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, A]
    rcases vert_cases w with ⟨x, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
    · rw [meets_dig_dO hloop, liftD_dO]
      constructor
      · intro h; exact Or.inl ⟨x, h, rfl⟩
      · rintro (⟨y, hy, h⟩ | ⟨y, _, h⟩ | ⟨y, _, h⟩)
        · rw [dO_inj h] at hy; exact hy
        · exact absurd h.symm (dO_ne_dU _ _)
        · exact absurd h.symm (dO_ne_dV _ _)
    · rw [meets_dig_dU, liftD_dU]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨d, h, rfl⟩)
      · rintro (⟨y, _, h⟩ | ⟨y, hy, h⟩ | ⟨y, _, h⟩)
        · exact absurd h (dO_ne_dU _ _)
        · rw [← dU_inj h]; exact hy
        · exact absurd h (dU_ne_dV _ _).symm
    · rw [meets_dig_dV, liftD_dV]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨d, h, rfl⟩)
      · rintro (⟨y, _, h⟩ | ⟨y, _, h⟩ | ⟨y, hy, h⟩)
        · exact absurd h (dO_ne_dV _ _)
        · exact absurd h (dU_ne_dV _ _)
        · rw [← dV_inj h]; exact hy
  have hbig : ((Finset.univ.filter (fun x => meets Q x ∧ S x = b)).image dO ∪ (A.image dU ∪ A.image dV)).card =
      (Finset.univ.filter (fun x => meets Q x ∧ S x = b)).card + 2 * A.card := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ (fun a b h => dO_inj h), Finset.card_image_of_injective _ (fun a b h => dU_inj h),
      Finset.card_image_of_injective _ (fun a b h => dV_inj h)]
    · omega
    · rw [Finset.disjoint_left]
      intro w hw hw'
      simp only [Finset.mem_image] at hw hw'
      obtain ⟨a, _, rfl⟩ := hw
      obtain ⟨b', _, h⟩ := hw'
      exact dU_ne_dV _ _ h.symm
    · rw [Finset.disjoint_left]
      intro w hw hw'
      simp only [Finset.mem_union, Finset.mem_image] at hw hw'
      obtain ⟨a, _, rfl⟩ := hw
      rcases hw' with ⟨b', _, h⟩ | ⟨b', _, h⟩
      · exact dO_ne_dU _ _ h.symm
      · exact dO_ne_dV _ _ h.symm
  refine Eq.trans (congrArg Finset.card (Finset.ext fun w => ?_)) (hbig.trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hset w
  · first
      | rfl
      | (congr 2; first | rfl | (ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]))

/-- **no 2-edge-cut**: if `Q^D` is 2-cut-reduced and has no two parallel old edges, then `Q` has no 2-edge-cut -/
theorem back_no2cut (hloop : Loopless Y) {Q : Fin Y.m → Prop} (hcub : CubicOn Q) (h2 : TwoCutReducedOn (digSet Q D))
    (hpar : ∀ f g, Q f → Q g → ¬ D f → ¬ D g → f ≠ g → ¬ Y.Joins g (Y.ends f).1 (Y.ends f).2) :
    ∀ S, ¬ TwoCut Q S := by
  rintro S ⟨e1, e2, hne, c1, c2, hall⟩
  let car : Fin Y.m → Fin (digG Y D).m := fun d => if D d then eN d 2 else eO d
  have crossCar : ∀ d, Q d → (RH2F.Crosses (digSet Q D) (liftD S) (car d) ↔ RH2F.Crosses Q S d) := by
    intro d hd
    have hc := carrier_ends (D := D) (Q := Q) S d
    unfold RH2F.Crosses
    rw [hc.1, hc.2]
    exact ⟨fun h => ⟨hd, h.2⟩, fun h => ⟨carrier_set hd, h.2⟩⟩
  have htc : TwoCut (digSet Q D) (liftD S) := by
    refine ⟨car e1, car e2, fun h => hne (carrier_inj h), (crossCar e1 c1.1).2 c1, (crossCar e2 c2.1).2 c2, ?_⟩
    intro e' he'
    rcases liftD_const S e' he'.1 with h1 | ⟨d, hd, rfl, h1, h2'⟩
    · exact absurd h1 he'.2
    · have hdc : RH2F.Crosses Q S d := ⟨hd, by rw [← h1, ← h2']; exact he'.2⟩
      rcases hall d hdc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  have key : ∀ b, scount (digSet Q D) (liftD S) b = 2 → False := by
    intro b hb
    rw [scount_dig hloop] at hb
    have h1 := side_nonempty c1 b
    have hk : cntF Y.m (fun d => (Q d ∧ D d) ∧ S (Y.ends d).1 = b) = 0 := by omega
    have hs2 : scount Q S b = 2 := by omega
    -- two edges inside side `b`
    have hh := side_handshake hloop hcub S b
    have hcr : cntF Y.m (RH2F.Crosses Q S) = 2 := by
      rw [← cntF_pair Y.m hne]; apply cntF_congr; intro f
      constructor
      · exact hall f
      · rintro (rfl | rfl)
        · exact c1
        · exact c2
    have hin : cntF Y.m (inner Q S b) = 2 := by omega
    rw [cntF_eq_card] at hin
    obtain ⟨f, g, hfg, hfgset⟩ := Finset.card_eq_two.1 hin
    have hf : inner Q S b f := by
      have h' := congrArg (f ∈ ·) hfgset
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        eq_iff_iff] at h'
      exact h'.2 (by simp)
    have hg : inner Q S b g := by
      have h' := congrArg (g ∈ ·) hfgset
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        eq_iff_iff] at h'
      exact h'.2 (by simp)
    -- the two vertices of side `b`
    unfold scount at hs2
    rw [cntF_eq_card] at hs2
    obtain ⟨x, y, hxy, hxyset⟩ := Finset.card_eq_two.1 hs2
    have onside : ∀ w, meets Q w → S w = b → w = x ∨ w = y := by
      intro w hw hs
      have h' := congrArg (w ∈ ·) hxyset
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        eq_iff_iff] at h'
      exact h'.1 ⟨hw, hs⟩
    have endsxy : ∀ h, inner Q S b h → (Y.ends h = (x, y) ∨ Y.ends h = (y, x)) := by
      intro h ⟨hQ, h1', h2'⟩
      have hl := hloop h
      rcases onside _ ⟨h, hQ, Or.inl rfl⟩ h1' with ha | ha <;>
        rcases onside _ ⟨h, hQ, Or.inr rfl⟩ h2' with hb' | hb'
      · exact absurd (ha.trans hb'.symm) hl
      · left; exact Prod.ext ha hb'
      · right; exact Prod.ext ha hb'
      · exact absurd (ha.trans hb'.symm) hl
    have nD : ∀ h, inner Q S b h → ¬ D h := by
      intro h hh' hD
      have : 0 < cntF Y.m (fun d => (Q d ∧ D d) ∧ S (Y.ends d).1 = b) :=
        cntF_le_of_mem Y.m _ (i := h) ⟨⟨hh'.1, hD⟩, hh'.2.1⟩
      omega
    apply hpar f g hf.1 hg.1 (nD f hf) (nD g hg) hfg
    rcases endsxy f hf with hf' | hf' <;> rcases endsxy g hg with hg' | hg' <;> rw [hf'] <;> simp only
    · exact Or.inl hg'
    · exact Or.inr hg'
    · exact Or.inr hg'
    · exact Or.inl hg'
  rcases h2 _ htc with h | h
  · exact key true h
  · exact key false h

/-- the number of crossing edges: at most two crossing edges are none, one, or exactly two distinct ones -/
theorem cross_cases {X : MGraph} {P : Fin X.m → Prop} (S : Fin X.n → Bool) (h : cntF X.m (RH2F.Crosses P S) ≤ 2) :
    (∀ e, ¬ RH2F.Crosses P S e) ∨ (∃ a, RH2F.Crosses P S a ∧ ∀ e, RH2F.Crosses P S e → e = a) ∨ TwoCut P S := by
  by_cases h0 : ∃ a, RH2F.Crosses P S a
  · obtain ⟨a, ha⟩ := h0
    by_cases h1 : ∃ b, RH2F.Crosses P S b ∧ b ≠ a
    · obtain ⟨b, hb, hba⟩ := h1
      right; right
      refine ⟨a, b, fun h => hba h.symm, ha, hb, fun e he => ?_⟩
      by_contra hne
      push_neg at hne
      have h3 := cntF_triple X.m (Ne.symm hba) hne.1.symm hne.2.symm
      have : cntF X.m (fun k => k = a ∨ k = b ∨ k = e) ≤ cntF X.m (RH2F.Crosses P S) := by
        apply cntF_mono; rintro k (rfl | rfl | rfl)
        · exact ha
        · exact hb
        · exact he
      rw [h3] at this
      omega
    · push_neg at h1
      exact Or.inr (Or.inl ⟨a, ha, h1⟩)
  · push_neg at h0
    exact Or.inl h0

/-- **simplicity**: a member of 𝒢 without 2-edge-cuts on at least 4 vertices is simple -/
theorem simple_of_no2cut {X : MGraph} {P : Fin X.m → Prop} (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S)
    (h4 : 4 ≤ vcount P) : SimpleP P := by
  intro f g x y hf hg jf jg
  by_contra hfg
  let S : Fin X.n → Bool := fun w => decide (w = x ∨ w = y)
  have hxy : x ≠ y := ne_of_joins hG.1 jf
  have hin : 2 ≤ cntF X.m (inner P S true) := by
    rw [← cntF_pair X.m hfg]
    apply cntF_mono
    have ins : ∀ h, P h → X.Joins h x y → inner P S true h := by
      intro h hh jh
      refine ⟨hh, ?_, ?_⟩ <;> rcases jh with jh | jh <;> rw [jh] <;> simp [S]
    rintro k (rfl | rfl)
    · exact ins k hf jf
    · exact ins k hg jg
  have hs : scount P S true = 2 := by
    unfold scount
    rw [← cntF_pair X.n hxy]
    apply cntF_congr
    intro w
    simp only [S, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro (rfl | rfl)
      · exact ⟨⟨f, hf, joins_inc_left jf⟩, Or.inl rfl⟩
      · exact ⟨⟨f, hf, joins_inc_right jf⟩, Or.inr rfl⟩
  have hh := side_handshake hG.1 hG.2.2.2 S true
  have hc : cntF X.m (RH2F.Crosses P S) ≤ 2 := by omega
  rcases cross_cases S hc with h0 | ⟨a, ha, hu⟩ | htc
  · -- no crossing edge: a vertex outside `{x, y}` contradicts connectivity
    have hsplit := vcount_split P S
    have : 2 ≤ scount P S false := by omega
    obtain ⟨z, ⟨⟨h, hh', hz⟩, hzs⟩⟩ := cntF_pos X.n _ (by omega : 0 < scount P S false)
    have hc' := hG.2.1 S (fun e he => by by_contra h'; exact h0 e ⟨he, h'⟩) f h hf hh'
    have e1 : S (X.ends f).1 = true := by rcases jf with jf | jf <;> rw [jf] <;> simp [S]
    have e2 : S (X.ends h).1 = false := by
      rcases hz with hz | hz
      · rw [hz]; exact hzs
      · have : S (X.ends h).1 = S (X.ends h).2 := by by_contra h'; exact h0 h ⟨hh', h'⟩
        rw [this, hz]; exact hzs
    rw [e1, e2] at hc'; exact Bool.noConfusion hc'
  · apply hG.2.2.1 a ha.1
    exact { U := fun v => decide (S v = S (X.ends a).1)
            hu := by simp
            hv := by simp only [decide_eq_false_iff_not]; exact fun h => ha.2 h.symm
            sep := fun g' hg' hne => by
              have : S (X.ends g').1 = S (X.ends g').2 := by
                by_contra h'; exact hne (hu g' ⟨hg', h'⟩)
              simp only [this] }
  · exact h3 S htc

end back

end RH2F


/-
  IV5.lean — EX1-goodness transfers along the correspondence `Rep` of fact 6c78409a046a3fe7 (plain multigraph ↔ edge
  set of an MGraph), hence between two edge sets with a common plain reading.
-/

namespace RH2Fid
open MGraph
open Classical

namespace Rep
variable {V E : Type} {en : E → Sym2 V} {X : MGraph} {P : Fin X.m → Prop} (R : Rep en X P)

include R in
/-- **EX1 corresponds** -/
theorem ex1_iff (hV : ∀ v, ∃ e, v ∈ en e) : RH2F.EX1On P ↔ EX1GoodP en := by
  constructor
  · intro hex g t ht ⟨N', hpm', hind'⟩
    have hN : ∀ f, R.liftN N' f → P f := R.liftN_P N'
    have hfun : (fun e => R.liftN N' (R.ψ e)) = N' := funext fun e => propext (R.liftN_ψ N' e)
    have hpm : RH2F.PMOn P (R.liftN N') := by
      rw [R.pmOn_iff hV _ hN, hfun]; exact hpm'
    have hst : R.liftN N' (R.ψ g) ↔ decide (t = 1) = true := by
      rw [R.liftN_ψ]; exact (ind_iff N' g t ht).1 hind'
    obtain ⟨N2, hpm2, hst2, c, hc2, hcl⟩ := hex (R.ψ g) (R.ψP g) (decide (t = 1)) ⟨_, hpm, hst⟩
    refine ⟨fun e => N2 (R.ψ e), (R.pmOn_iff hV N2 hpm2.1).1 hpm2,
      (ind_iff _ g t ht).2 hst2, toN (fun e => c (R.ψ e)), toN_range _, ?_, (R.classOn_iff N2 c).1 hcl⟩
    exact (starP_congr en _ _ (fun e f => by simp only [toN, Fin.ext_iff]; omega)).1 ((R.starOn_iff c).1 hc2)
  · intro hex g hg t ⟨N, hpm, hst⟩
    obtain ⟨g', rfl⟩ := R.ψsurj g hg
    have hpm' := (R.pmOn_iff hV N hpm.1).1 hpm
    have hind : ind (fun e => N (R.ψ e)) g' = (if t then 1 else 0) := (ind_bool _ g' t).1 hst
    obtain ⟨N'', hpm'', hind'', c, hr, hsc, hcl⟩ :=
      hex g' (if t then 1 else 0) (by cases t <;> simp) ⟨_, hpm', hind⟩
    have hfun : (fun e => R.liftN N'' (R.ψ e)) = N'' := funext fun e => propext (R.liftN_ψ N'' e)
    refine ⟨R.liftN N'', (R.pmOn_iff hV _ (R.liftN_P N'')).2 (by rw [hfun]; exact hpm''), ?_,
      R.liftC 0 (ofN c), ?_, ?_⟩
    · have := (ind_bool N'' g' t).2 hind''
      rw [R.liftN_ψ]; exact this
    · rw [R.starOn_iff]
      have : (fun e => R.liftC 0 (ofN c) (R.ψ e)) = ofN c := funext fun e => R.liftC_ψ _ _ e
      rw [this]
      exact (starP_congr _ c (ofN c) (fun e f => by
        have := hr e; have := hr f; unfold ofN; rw [Fin.ext_iff]; simp only; omega)).1 hsc
    · rw [R.classOn_iff]
      have h1 : (fun e => R.liftC 0 (ofN c) (R.ψ e)) = ofN c := funext fun e => R.liftC_ψ _ _ e
      have h2 : toN (ofN c) = c := funext fun e => by
        have := hr e; unfold toN ofN; simp only; omega
      rw [h1, h2, hfun]; exact hcl

end Rep

/-- EX1 between two edge sets with a common plain reading `subEn X P` -/
theorem ex1_of_rep {X Y : MGraph} {P : Fin X.m → Prop} {Q : Fin Y.m → Prop} (R : Rep (subEn X P) Y Q)
    (h : RH2F.EX1On Q) : RH2F.EX1On P :=
  ((subRep X P).ex1_iff (sub_hV X P)).2 ((R.ex1_iff (sub_hV X P)).1 h)

end RH2Fid


/-
  IV6.lean — H-ASM (fact fdd83999b9ec10e2) (a), converse: every 2-cut-reduced member of 𝒢 on at least 10 vertices is
  a digon insertion H^D of a simple 3-edge-connected cubic multigraph H. Part 1: digons.
-/

namespace RH2F
open MGraph
open Classical

section digons
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `f` has a parallel mate in `P` -/
def IsPar (P : Fin X.m → Prop) (f : Fin X.m) : Prop :=
  P f ∧ ∃ g, P g ∧ g ≠ f ∧ X.Joins g (X.ends f).1 (X.ends f).2

/-- `f` is the edge of lower index of a digon of `P` -/
def FirstD (P : Fin X.m → Prop) (f : Fin X.m) : Prop :=
  P f ∧ ∃ g, P g ∧ f.val < g.val ∧ X.Joins g (X.ends f).1 (X.ends f).2

/-- `x` lies in a digon of `P` -/
def InDig (P : Fin X.m → Prop) (x : Fin X.n) : Prop := ∃ f, IsPar P f ∧ X.Inc f x

namespace DigData
variable (D : DigData P)

/-- the edges of `P` joining `u` and `v` are `d1` and `d2` -/
theorem par_of {h : Fin X.m} (hh : P h) (hj : X.Joins h D.u D.v) : h = D.d1 ∨ h = D.d2 := by
  rcases D.covu h hh (joins_inc_left hj) with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · subst h1
    rcases joins_unique hj D.ju with ⟨_, h2⟩ | ⟨h2, _⟩
    · exact absurd h2.symm D.hxv
    · exact absurd h2.symm D.hxu

theorem inc_d1_u : X.Inc D.d1 D.u := joins_inc_left D.j1
theorem inc_d2_u : X.Inc D.d2 D.u := joins_inc_left D.j2
theorem inc_d1_v : X.Inc D.d1 D.v := joins_inc_right D.j1
theorem inc_d2_v : X.Inc D.d2 D.v := joins_inc_right D.j2

theorem gu_ne_d1 : D.gu ≠ D.d1 := by
  intro h; have := D.j1; rw [← h] at this
  rcases joins_unique this D.ju with ⟨_, h2⟩ | ⟨h2, _⟩
  · exact D.hxv h2.symm
  · exact D.hxu h2.symm
theorem gu_ne_d2 : D.gu ≠ D.d2 := by
  intro h; have := D.j2; rw [← h] at this
  rcases joins_unique this D.ju with ⟨_, h2⟩ | ⟨h2, _⟩
  · exact D.hxv h2.symm
  · exact D.hxu h2.symm
theorem gv_ne_d1 : D.gv ≠ D.d1 := by
  intro h; have := D.j1; rw [← h] at this
  rcases joins_unique this D.jv with ⟨h2, _⟩ | ⟨h2, _⟩
  · exact D.huv h2
  · exact D.hyu h2.symm
theorem gv_ne_d2 : D.gv ≠ D.d2 := by
  intro h; have := D.j2; rw [← h] at this
  rcases joins_unique this D.jv with ⟨h2, _⟩ | ⟨h2, _⟩
  · exact D.huv h2
  · exact D.hyu h2.symm

/-- the same digon seen from `v` -/
def swap : DigData P where
  u := D.v
  v := D.u
  x := D.y
  y := D.x
  d1 := D.d1
  d2 := D.d2
  gu := D.gv
  gv := D.gu
  hd1 := D.hd1
  hd2 := D.hd2
  hgu := D.hgv
  hgv := D.hgu
  j1 := Or.symm D.j1
  j2 := Or.symm D.j2
  ju := D.jv
  jv := D.ju
  d12 := D.d12
  covu := D.covv
  covv := D.covu
  huv := fun h => D.huv h.symm
  hxu := D.hyv
  hxv := D.hyu
  hyu := D.hxv
  hyv := D.hxu
  hxy := fun h => D.hxy h.symm

/-- **the outer neighbour `x` lies in no digon** (Step 3 of H-ASM (a)) -/
theorem x_not_dig (hG : InG X P) (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) : ¬ InDig P D.x := by
  rintro ⟨h, ⟨hh, h', hh', hne', hj'⟩, hhx⟩
  obtain ⟨x', jh⟩ := joins_of_inc hhx
  have jh' : X.Joins h' D.x x' := by
    rcases jh with jh | jh <;> rw [jh] at hj' <;> simp only at hj'
    · exact hj'
    · exact Or.symm hj'
  have hx'x : x' ≠ D.x := fun e => ne_of_joins hG.1 jh e.symm
  have hgu_h : D.gu ≠ h := by
    intro e; subst e
    rcases joins_unique jh D.ju with ⟨e2, _⟩ | ⟨_, e2⟩
    · exact D.hxu e2
    · subst e2
      rcases D.covu h' hh' (joins_inc_right jh') with e3 | e3 | e3
      · rcases joins_unique jh' (e3 ▸ D.j1) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact D.hxu e4
        · exact D.hxv e4
      · rcases joins_unique jh' (e3 ▸ D.j2) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact D.hxu e4
        · exact D.hxv e4
      · exact hne' e3
  have hgu_h' : D.gu ≠ h' := by
    intro e; subst e
    rcases joins_unique jh' D.ju with ⟨e2, _⟩ | ⟨_, e2⟩
    · exact D.hxu e2
    · subst e2
      rcases D.covu h hh (joins_inc_right jh) with e3 | e3 | e3
      · rcases joins_unique jh (e3 ▸ D.j1) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact D.hxu e4
        · exact D.hxv e4
      · rcases joins_unique jh (e3 ▸ D.j2) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact D.hxu e4
        · exact D.hxv e4
      · exact hne' e3.symm
  -- `x'` is none of `u`, `v`
  have hx'u : x' ≠ D.u := by
    intro e; subst e
    rcases D.covu h hh (joins_inc_right jh) with e3 | e3 | e3
    · rcases joins_unique jh (e3 ▸ D.j1) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact D.hxu e4
      · exact D.hxv e4
    · rcases joins_unique jh (e3 ▸ D.j2) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact D.hxu e4
      · exact D.hxv e4
    · exact hgu_h e3.symm
  have hx'v : x' ≠ D.v := by
    intro e; subst e
    rcases D.covv h hh (joins_inc_right jh) with e3 | e3 | e3
    · rcases joins_unique jh (e3 ▸ D.j1) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact D.hxu e4
      · exact D.hxv e4
    · rcases joins_unique jh (e3 ▸ D.j2) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact D.hxu e4
      · exact D.hxv e4
    · rcases joins_unique jh (e3 ▸ D.jv) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact D.hxv e4
      · exact D.hxy e4
  -- the edges at `x` are `gu`, `h`, `h'`
  obtain ⟨c, hc, ic, chx, chx', covx⟩ := third_edge hG.2.2.2 hh hh' hhx (joins_inc_left jh') (Ne.symm hne')
  have covx' : ∀ d, P d → X.Inc d D.x → d = h ∨ d = h' ∨ d = D.gu := by
    intro d hd hdx
    rcases covx D.gu D.hgu (joins_inc_right D.ju) with e | e | e
    · exact absurd e hgu_h
    · exact absurd e hgu_h'
    · subst e; exact covx d hd hdx
  -- the third edge `k` at `x'`
  obtain ⟨k, hk, ik, khx, khx', covk⟩ :=
    third_edge hG.2.2.2 hh hh' (joins_inc_right jh) (joins_inc_right jh') (Ne.symm hne')
  obtain ⟨z, jk⟩ := joins_of_inc ik
  have hzx' : z ≠ x' := fun e => ne_of_joins hG.1 jk e.symm
  have hzx : z ≠ D.x := by
    intro e; subst e
    rcases covx' k hk (joins_inc_right jk) with e | e | e
    · exact khx e
    · exact khx' e
    · subst e
      rcases joins_unique jk D.ju with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact hx'u e4
      · exact hx'x e4
  have hzu : z ≠ D.u := by
    intro e; subst e
    rcases D.covu k hk (joins_inc_right jk) with e3 | e3 | e3
    · rcases joins_unique jk (e3 ▸ D.j1) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact hx'u e4
      · exact hx'v e4
    · rcases joins_unique jk (e3 ▸ D.j2) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact hx'u e4
      · exact hx'v e4
    · rcases joins_unique jk (e3 ▸ D.ju) with ⟨e4, _⟩ | ⟨e4, _⟩
      · exact hx'u e4
      · exact hx'x e4
  -- the 2-colouring of `{u, v, x, x'}`
  let U : Fin X.n → Bool := fun w => decide (w = D.u ∨ w = D.v ∨ w = D.x ∨ w = x')
  have Uin : ∀ w, (w = D.u ∨ w = D.v ∨ w = D.x ∨ w = x') → U w = true := fun w hw => by simp [U, hw]
  have Uout : ∀ w, w ≠ D.u → w ≠ D.v → w ≠ D.x → w ≠ x' → U w = false := fun w h1 h2 h3 h4 => by
    simp [U, h1, h2, h3, h4]
  have inside : ∀ d a b, X.Joins d a b → (a = D.u ∨ a = D.v ∨ a = D.x ∨ a = x') →
      (b = D.u ∨ b = D.v ∨ b = D.x ∨ b = x') → U (X.ends d).1 = U (X.ends d).2 := by
    intro d a b hj ha hb
    rcases hj with e | e <;> rw [e] <;> simp only [Uin a ha, Uin b hb]
  -- the only edges leaving the four vertices are `gv` and `k`
  have sep : ∀ d, P d → d ≠ D.gv → d ≠ k → U (X.ends d).1 = U (X.ends d).2 := by
    intro d hd hdv hdk
    by_cases hdu : X.Inc d D.u
    · rcases D.covu d hd hdu with rfl | rfl | rfl
      · exact inside _ _ _ D.j1 (Or.inl rfl) (Or.inr (Or.inl rfl))
      · exact inside _ _ _ D.j2 (Or.inl rfl) (Or.inr (Or.inl rfl))
      · exact inside _ _ _ D.ju (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    by_cases hdvv : X.Inc d D.v
    · rcases D.covv d hd hdvv with rfl | rfl | rfl
      · exact inside _ _ _ D.j1 (Or.inl rfl) (Or.inr (Or.inl rfl))
      · exact inside _ _ _ D.j2 (Or.inl rfl) (Or.inr (Or.inl rfl))
      · exact absurd rfl hdv
    by_cases hdx : X.Inc d D.x
    · rcases covx' d hd hdx with rfl | rfl | rfl
      · exact inside _ _ _ jh (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
      · exact inside _ _ _ jh' (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
      · exact absurd (joins_inc_left D.ju) hdu
    by_cases hdx' : X.Inc d x'
    · rcases covk d hd hdx' with rfl | rfl | rfl
      · exact absurd (joins_inc_left jh) hdx
      · exact absurd (joins_inc_left jh') hdx
      · exact absurd rfl hdk
    · have n1 : (X.ends d).1 ≠ D.u ∧ (X.ends d).1 ≠ D.v ∧ (X.ends d).1 ≠ D.x ∧ (X.ends d).1 ≠ x' :=
        ⟨fun e => hdu (Or.inl e), fun e => hdvv (Or.inl e), fun e => hdx (Or.inl e), fun e => hdx' (Or.inl e)⟩
      have n2 : (X.ends d).2 ≠ D.u ∧ (X.ends d).2 ≠ D.v ∧ (X.ends d).2 ≠ D.x ∧ (X.ends d).2 ≠ x' :=
        ⟨fun e => hdu (Or.inr e), fun e => hdvv (Or.inr e), fun e => hdx (Or.inr e), fun e => hdx' (Or.inr e)⟩
      rw [Uout _ n1.1 n1.2.1 n1.2.2.1 n1.2.2.2, Uout _ n2.1 n2.2.1 n2.2.2.1 n2.2.2.2]
  -- the four vertices meet `P`, the rest has at least six vertices
  have hS4 : scount P U true = 4 := by
    unfold scount
    have e4 : cntF X.n (fun w => meets P w ∧ U w = true) = cntF X.n (fun w => w = D.u ∨ w = D.v ∨ w = D.x ∨ w = x') := by
      apply cntF_congr; intro w
      constructor
      · rintro ⟨_, hw⟩; simpa [U] using hw
      · intro hw
        refine ⟨?_, Uin w hw⟩
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨D.d1, D.hd1, D.inc_d1_u⟩
        · exact ⟨D.d1, D.hd1, D.inc_d1_v⟩
        · exact ⟨D.gu, D.hgu, joins_inc_right D.ju⟩
        · exact ⟨h, hh, joins_inc_right jh⟩
    rw [e4, cntF_split X.n _ (fun w => w = x')]
    have e1 : cntF X.n (fun w => (w = D.u ∨ w = D.v ∨ w = D.x ∨ w = x') ∧ w = x') = 1 := by
      rw [← cntF_single X.n x']; apply cntF_congr; intro w
      constructor
      · rintro ⟨_, e⟩; exact e
      · rintro rfl; exact ⟨Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    have e3 : cntF X.n (fun w => (w = D.u ∨ w = D.v ∨ w = D.x ∨ w = x') ∧ ¬ w = x') = 3 := by
      rw [← cntF_triple X.n D.huv (Ne.symm D.hxu) (Ne.symm D.hxv)]; apply cntF_congr; intro w
      constructor
      · rintro ⟨e | e | e | e, e'⟩
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)
        · exact absurd e e'
      · rintro (rfl | rfl | rfl)
        · exact ⟨Or.inl rfl, fun e => hx'u e.symm⟩
        · exact ⟨Or.inr (Or.inl rfl), fun e => hx'v e.symm⟩
        · exact ⟨Or.inr (Or.inr (Or.inl rfl)), fun e => hx'x e.symm⟩
    omega
  have hsplit := vcount_split P U
  by_cases hyx' : D.y = x'
  · -- then nothing leaves the four vertices: `P` is disconnected
    have sep' : ∀ d, P d → U (X.ends d).1 = U (X.ends d).2 := by
      intro d hd
      by_cases hdv : d = D.gv
      · subst hdv; exact inside _ _ _ D.jv (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr hyx')))
      by_cases hdk : d = k
      · subst hdk
        -- `k` is the third edge at `x' = y`, i.e. `gv`
        rcases covk D.gv D.hgv (hyx' ▸ joins_inc_right D.jv) with e | e | e
        · exfalso
          have jv' := D.jv; rw [e] at jv'
          rcases joins_unique jv' jh with ⟨e4, _⟩ | ⟨e4, _⟩
          · exact D.hxv e4.symm
          · exact hx'v e4.symm
        · exfalso
          have jv' := D.jv; rw [e] at jv'
          rcases joins_unique jv' jh' with ⟨e4, _⟩ | ⟨e4, _⟩
          · exact D.hxv e4.symm
          · exact hx'v e4.symm
        · exact absurd e.symm hdv
      exact sep d hd hdv hdk
    have hc := hG.2.1 U sep'
    obtain ⟨w, ⟨⟨fw, hfw, ifw⟩, hwU⟩⟩ := cntF_pos X.n _ (by omega : 0 < scount P U false)
    have e1 := hc D.d1 fw D.hd1 hfw
    have ea : U (X.ends D.d1).1 = true := by
      rcases D.j1 with e | e <;> rw [e] <;> simp [U]
    have eb : U (X.ends fw).1 = false := by
      rcases ifw with e | e
      · rw [e]; exact hwU
      · rw [sep' fw hfw, e]; exact hwU
    rw [ea, eb] at e1; exact Bool.noConfusion e1
  · -- two crossing edges `gv` and `k`: a 2-edge-cut with sides of 4 and at least 6 vertices
    have hzv : z ≠ D.v := by
      intro e; subst e
      rcases D.covv k hk (joins_inc_right jk) with e3 | e3 | e3
      · rcases joins_unique jk (e3 ▸ D.j1) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact hx'u e4
        · exact hx'v e4
      · rcases joins_unique jk (e3 ▸ D.j2) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact hx'u e4
        · exact hx'v e4
      · rcases joins_unique jk (e3 ▸ D.jv) with ⟨e4, _⟩ | ⟨e4, _⟩
        · exact hx'v e4
        · exact hyx' e4.symm
    have hkgv : k ≠ D.gv := by
      intro e; subst e
      rcases D.gv_at (joins_inc_left jk) with e | e
      · exact hx'v e
      · exact hyx' e.symm
    have cgv : RH2F.Crosses P U D.gv := ⟨D.hgv, by
      rcases D.jv with e | e <;> rw [e] <;>
        simp only [Uin D.v (Or.inr (Or.inl rfl)), Uout D.y D.hyu D.hyv (Ne.symm D.hxy) hyx'] <;> decide⟩
    have ck : RH2F.Crosses P U k := ⟨hk, by
      rcases jk with e | e <;> rw [e] <;>
        simp only [Uin x' (Or.inr (Or.inr (Or.inr rfl))), Uout z hzu hzv hzx hzx'] <;> decide⟩
    have htc : TwoCut P U := ⟨D.gv, k, Ne.symm hkgv, cgv, ck, fun d hd => by
      by_contra hne; push_neg at hne; exact hd.2 (sep d hd.1 hne.1 hne.2)⟩
    rcases h2 U htc with e | e <;> omega

theorem y_not_dig (hG : InG X P) (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) : ¬ InDig P D.y :=
  D.swap.x_not_dig hG h2 h10

end DigData

/-! ### one `DigData` per digon, indexed by its edge of lower index -/

theorem firstD_isPar {f : Fin X.m} (hf : FirstD P f) : IsPar P f := by
  obtain ⟨hPf, g, hg, hlt, hj⟩ := hf
  exact ⟨hPf, g, hg, fun e => by rw [e] at hlt; exact Nat.lt_irrefl _ hlt, hj⟩

/-- the digon data of the digon with lower edge `f` (`u`, `v` the ends of `f`) -/
noncomputable def dg (hG : InG X P) (h4 : 4 ≤ vcount P) (f : Fin X.m) (hf : FirstD P f) : DigData P :=
  Classical.choose (digData_of hG h4 hf.1 (Classical.choose_spec hf.2).1 (joins_ends f)
    (Classical.choose_spec hf.2).2.2 (fun e => by
      have := (Classical.choose_spec hf.2).2.1; rw [← e] at this; exact Nat.lt_irrefl _ this))

theorem dg_u (hG : InG X P) (h4 : 4 ≤ vcount P) (f : Fin X.m) (hf : FirstD P f) :
    (dg hG h4 f hf).u = (X.ends f).1 :=
  (Classical.choose_spec (digData_of hG h4 hf.1 (Classical.choose_spec hf.2).1 (joins_ends f)
    (Classical.choose_spec hf.2).2.2 (fun e => by
      have := (Classical.choose_spec hf.2).2.1; rw [← e] at this; exact Nat.lt_irrefl _ this))).1

theorem dg_v (hG : InG X P) (h4 : 4 ≤ vcount P) (f : Fin X.m) (hf : FirstD P f) :
    (dg hG h4 f hf).v = (X.ends f).2 :=
  (Classical.choose_spec (digData_of hG h4 hf.1 (Classical.choose_spec hf.2).1 (joins_ends f)
    (Classical.choose_spec hf.2).2.2 (fun e => by
      have := (Classical.choose_spec hf.2).2.1; rw [← e] at this; exact Nat.lt_irrefl _ this))).2

theorem dg_joins (hG : InG X P) (h4 : 4 ≤ vcount P) (f : Fin X.m) (hf : FirstD P f) :
    X.Joins f (dg hG h4 f hf).u (dg hG h4 f hf).v := by
  rw [dg_u, dg_v]; exact joins_ends f

/-- an edge of `P` at a digon vertex `w` of `D` that joins `w` to a vertex outside the digon is the third edge at `w` -/
theorem DigData.third_not_par (D : DigData P) {g h : Fin X.m} (hg : P g) (hh : P h) (hgh : g ≠ h)
    (hgu : g = D.gu) (hj : X.Joins h (X.ends g).1 (X.ends g).2) : False := by
  subst hgu
  have jh : X.Joins h D.u D.x := by
    rcases D.ju with e | e <;> rw [e] at hj
    · exact hj
    · exact Or.symm hj
  rcases D.covu h hh (joins_inc_left jh) with e | e | e
  · rcases joins_unique jh (e ▸ D.j1) with ⟨_, e4⟩ | ⟨e4, _⟩
    · exact D.hxv e4
    · exact D.huv e4
  · rcases joins_unique jh (e ▸ D.j2) with ⟨_, e4⟩ | ⟨e4, _⟩
    · exact D.hxv e4
    · exact D.huv e4
  · exact hgh e.symm

theorem three_in_two {α : Type} {a b x y z : α} (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) (hz : z = a ∨ z = b)
    (hxy : x ≠ y) (hzx : z ≠ x) : z = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp_all

/-- **digons are determined by any of their vertices** -/
theorem first_unique (hG : InG X P) (h4 : 4 ≤ vcount P) {f f' : Fin X.m} (hf : FirstD P f) (hf' : FirstD P f')
    {w : Fin X.n} (hw : X.Inc f w) (hw' : X.Inc f' w) : f = f' := by
  let D := dg hG h4 f hf
  have jf : X.Joins f D.u D.v := dg_joins hG h4 f hf
  -- `f'` is `d1` or `d2` of `D`
  have inD : ∀ (E : DigData P), X.Joins f E.u E.v → X.Inc f' E.u → f' = E.d1 ∨ f' = E.d2 := by
    intro E jE hu
    rcases E.covu f' hf'.1 hu with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso
      obtain ⟨g'', hg'', hlt, hj''⟩ := hf'.2
      exact E.third_not_par hf'.1 hg'' (fun e' => by rw [e'] at hlt; exact Nat.lt_irrefl _ hlt) e hj''
  have hmem : f' = D.d1 ∨ f' = D.d2 := by
    rcases inc_of_joins jf hw with e | e
    · exact inD D jf (e ▸ hw')
    · have jf' : X.Joins f D.swap.u D.swap.v := Or.symm jf
      have hv' : X.Inc f' D.swap.u := by show X.Inc f' D.v; exact e ▸ hw'
      exact inD D.swap jf' hv'
  have hfmem : f = D.d1 ∨ f = D.d2 := D.par_of hf.1 jf
  -- the mate of `f` is the other one, and it has larger index; symmetrically for `f'`
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨g, hg, hlt, hj⟩ := hf.2
  obtain ⟨g', hg', hlt', hj'⟩ := hf'.2
  have jg : X.Joins g D.u D.v := by rw [dg_u, dg_v]; exact hj
  have jf'' : X.Joins f' D.u D.v := by
    rcases hmem with e | e <;> rw [e]
    · exact D.j1
    · exact D.j2
  have jg' : X.Joins g' D.u D.v := by
    rcases joins_unique jf'' (joins_ends f') with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hj'
    · rw [e1, e2]; exact Or.symm hj'
  have gmem := D.par_of hg jg
  have g'mem := D.par_of hg' jg'
  have hgf : g ≠ f := fun e => by rw [e] at hlt; exact Nat.lt_irrefl _ hlt
  have hg'f' : g' ≠ f' := fun e => by rw [e] at hlt'; exact Nat.lt_irrefl _ hlt'
  -- all four lie in `{d1, d2}`, so `g = f'` and `g' = f`
  have e1 : g = f' := three_in_two hfmem hmem gmem hne hgf
  have e2 : g' = f := three_in_two hmem hfmem g'mem (Ne.symm hne) hg'f'
  rw [e1] at hlt; rw [e2] at hlt'; omega

/-- a parallel edge joins the ends of the lower edge of its digon -/
theorem isPar_first {h : Fin X.m} (hh : IsPar P h) : ∃ f, FirstD P f ∧ X.Joins h (X.ends f).1 (X.ends f).2 := by
  obtain ⟨hPh, h', hh', hne, hj⟩ := hh
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · -- `h'` is the lower edge
    refine ⟨h', ⟨hh', h, hPh, hlt, ?_⟩, ?_⟩
    · rcases hj with e | e <;> rw [e]
      · exact joins_ends h
      · exact Or.symm (joins_ends h)
    · rcases hj with e | e <;> rw [e]
      · exact joins_ends h
      · exact Or.symm (joins_ends h)
  · exact ⟨h, ⟨hPh, h', hh', hlt, hj⟩, joins_ends h⟩

theorem inDig_iff {x : Fin X.n} : InDig P x ↔ ∃ f, FirstD P f ∧ X.Inc f x := by
  constructor
  · rintro ⟨h, hh, hx⟩
    obtain ⟨f, hf, hj⟩ := isPar_first hh
    refine ⟨f, hf, ?_⟩
    rcases inc_of_joins hj hx with e | e
    · exact Or.inl e.symm
    · exact Or.inr e.symm
  · rintro ⟨f, hf, hx⟩
    exact ⟨f, firstD_isPar hf, hx⟩

/-! ### the suppressed multigraph H -/

section supp
variable (hG : InG X P) (h4 : 4 ≤ vcount P)

/-- the ambient of `H`: the old edges, and for every edge `f` a new edge joining the outer neighbours of the digon of
    `f` if `f` is the lower edge of a digon (otherwise a copy of `f`, not used) -/
noncomputable def supY : MGraph where
  n := X.n
  m := X.m + X.m
  ends := fun e => if h : e.val < X.m then X.ends ⟨e.val, h⟩ else
    if hf : FirstD P ⟨e.val - X.m, by have := e.isLt; omega⟩ then
      ((dg hG h4 _ hf).x, (dg hG h4 _ hf).y) else X.ends ⟨e.val - X.m, by have := e.isLt; omega⟩

/-- the old edge `f` of `supY` -/
def yO (f : Fin X.m) : Fin (X.m + X.m) := Fin.castAdd X.m f
/-- the new edge of the digon with lower edge `f` -/
def yN (f : Fin X.m) : Fin (X.m + X.m) := Fin.natAdd X.m f

/-- the edges of `H`: old edges of `P` away from the digons, and the new edges of the digons -/
def supQ : Fin (supY hG h4).m → Prop := fun e =>
  if h : e.val < X.m then P ⟨e.val, h⟩ ∧ ¬ InDig P (X.ends ⟨e.val, h⟩).1 ∧ ¬ InDig P (X.ends ⟨e.val, h⟩).2
  else FirstD P ⟨e.val - X.m, by have := e.isLt; change e.val < X.m + X.m at this; omega⟩

/-- the digon set: the new edges -/
def supD : Fin (supY hG h4).m → Prop := fun e => X.m ≤ e.val

variable {hG h4}

theorem supY_ends_yO (f : Fin X.m) : (supY hG h4).ends (yO f) = X.ends f := by
  simp [supY, yO, f.isLt]

theorem supY_ends_yN {f : Fin X.m} (hf : FirstD P f) :
    (supY hG h4).ends (yN f) = ((dg hG h4 f hf).x, (dg hG h4 f hf).y) := by
  have hlt : ¬ (yN f : Fin (X.m + X.m)).val < X.m := by simp [yN]
  have hf' : (⟨(yN f : Fin (X.m + X.m)).val - X.m, by simp [yN]⟩ : Fin X.m) = f := Fin.ext (by simp [yN])
  simp only [supY, dif_neg hlt]
  have key : ∀ (g : Fin X.m) (hg : g = f), (if hfg : FirstD P g then ((dg hG h4 g hfg).x, (dg hG h4 g hfg).y)
      else X.ends g) = ((dg hG h4 f hf).x, (dg hG h4 f hf).y) := by
    intro g hg; subst hg; rw [dif_pos hf]
  exact key _ hf'

theorem supQ_yO (f : Fin X.m) : supQ hG h4 (yO f) ↔ P f ∧ ¬ InDig P (X.ends f).1 ∧ ¬ InDig P (X.ends f).2 := by
  simp [supQ, yO, f.isLt]

theorem supQ_yN (f : Fin X.m) : supQ hG h4 (yN f) ↔ FirstD P f := by
  have hlt : ¬ (yN f : Fin (X.m + X.m)).val < X.m := by simp [yN]
  have hf' : (⟨(yN f : Fin (X.m + X.m)).val - X.m, by simp [yN]⟩ : Fin X.m) = f := Fin.ext (by simp [yN])
  simp only [supQ, dif_neg hlt]
  rw [hf']

theorem supD_yO (f : Fin X.m) : ¬ supD hG h4 (yO f) := by simp [supD, yO, f.isLt]
theorem supD_yN (f : Fin X.m) : supD hG h4 (yN f) := by simp [supD, yN]

theorem sup_cases (e : Fin (supY hG h4).m) : (∃ f, e = yO f) ∨ ∃ f, e = yN f := by
  by_cases h : e.val < X.m
  · exact Or.inl ⟨⟨e.val, h⟩, Fin.ext rfl⟩
  · have := e.isLt
    change e.val < X.m + X.m at this
    exact Or.inr ⟨⟨e.val - X.m, by omega⟩, Fin.ext (by simp [yN]; omega)⟩

theorem yO_inj {f g : Fin X.m} (h : (yO f : Fin (X.m + X.m)) = yO g) : f = g := by
  simp only [yO] at h; exact Fin.ext (by simpa using congrArg Fin.val h)
theorem yN_inj {f g : Fin X.m} (h : (yN f : Fin (X.m + X.m)) = yN g) : f = g := by
  simp only [yN] at h; exact Fin.ext (by simpa using congrArg Fin.val h)
theorem yO_ne_yN (f g : Fin X.m) : (yO f : Fin (X.m + X.m)) ≠ yN g := by
  intro h; have := congrArg Fin.val h; simp [yO, yN] at this; have := f.isLt; omega

theorem supY_loopless : Loopless (supY hG h4) := by
  intro e
  rcases sup_cases e with ⟨f, rfl⟩ | ⟨f, rfl⟩
  · rw [supY_ends_yO]; exact hG.1 f
  · by_cases hf : FirstD P f
    · rw [supY_ends_yN hf]; exact (dg hG h4 f hf).hxy
    · have hlt : ¬ (yN f : Fin (X.m + X.m)).val < X.m := by simp [yN]
      have hf' : (⟨(yN f : Fin (X.m + X.m)).val - X.m, by simp [yN]⟩ : Fin X.m) = f := Fin.ext (by simp [yN])
      show ((supY hG h4).ends (yN f)).1 ≠ ((supY hG h4).ends (yN f)).2
      simp only [supY, dif_neg hlt]
      have key : ∀ (g : Fin X.m) (hg : g = f), (if hfg : FirstD P g then ((dg hG h4 g hfg).x, (dg hG h4 g hfg).y)
          else X.ends g) = X.ends f := by
        intro g hg; subst hg; rw [dif_neg hf]
      rw [key _ hf']
      exact hG.1 f

/-! #### the third edges of a digon -/

theorem DigData.d1_par (D : DigData P) : IsPar P D.d1 :=
  ⟨D.hd1, D.d2, D.hd2, Ne.symm D.d12, by
    rcases D.j1 with e | e <;> rw [e]
    · exact D.j2
    · exact Or.symm D.j2⟩
theorem DigData.d2_par (D : DigData P) : IsPar P D.d2 :=
  ⟨D.hd2, D.d1, D.hd1, D.d12, by
    rcases D.j2 with e | e <;> rw [e]
    · exact D.j1
    · exact Or.symm D.j1⟩

theorem DigData.at_u_notpar (D : DigData P) {h : Fin X.m} (hh : P h) (hu : X.Inc h D.u) (hp : ¬ IsPar P h) :
    h = D.gu := by
  rcases D.covu h hh hu with e | e | e
  · exact absurd (e ▸ D.d1_par) hp
  · exact absurd (e ▸ D.d2_par) hp
  · exact e

theorem DigData.at_v_notpar (D : DigData P) {h : Fin X.m} (hh : P h) (hv : X.Inc h D.v) (hp : ¬ IsPar P h) :
    h = D.gv := by
  rcases D.covv h hh hv with e | e | e
  · exact absurd (e ▸ D.d1_par) hp
  · exact absurd (e ▸ D.d2_par) hp
  · exact e

theorem isPar_inc_dig {h : Fin X.m} {w : Fin X.n} (hp : IsPar P h) (hw : X.Inc h w) : InDig P w := ⟨h, hp, hw⟩

/-- the chosen lower edge of the digon at a digon vertex -/
noncomputable def digOf {z : Fin X.n} (hz : InDig P z) : Fin X.m := Classical.choose (inDig_iff.1 hz)
theorem digOf_spec {z : Fin X.n} (hz : InDig P z) : FirstD P (digOf hz) ∧ X.Inc (digOf hz) z :=
  Classical.choose_spec (inDig_iff.1 hz)

/-- an edge of `P` from a vertex `w` outside the digons to a digon vertex `z` is `gu` (then `w = x`) or `gv` (then
    `w = y`) of the digon at `z` -/
theorem third_cases (hG : InG X P) (h4 : 4 ≤ vcount P) {h : Fin X.m} {w z : Fin X.n} (hh : P h)
    (hj : X.Joins h w z) (hw : ¬ InDig P w) (hz : InDig P z) :
    (h = (dg hG h4 _ (digOf_spec hz).1).gu ∧ z = (dg hG h4 _ (digOf_spec hz).1).u ∧
      w = (dg hG h4 _ (digOf_spec hz).1).x) ∨
    (h = (dg hG h4 _ (digOf_spec hz).1).gv ∧ z = (dg hG h4 _ (digOf_spec hz).1).v ∧
      w = (dg hG h4 _ (digOf_spec hz).1).y) := by
  set f := digOf hz
  set D := dg hG h4 f (digOf_spec hz).1
  have hp : ¬ IsPar P h := fun hp => hw (isPar_inc_dig hp (joins_inc_left hj))
  have hwz : w ≠ z := ne_of_joins hG.1 hj
  rcases inc_of_joins (dg_joins hG h4 f (digOf_spec hz).1) (digOf_spec hz).2 with ez | ez
  · have e := D.at_u_notpar hh (ez ▸ joins_inc_right hj) hp
    refine Or.inl ⟨e, ez, ?_⟩
    rcases joins_unique hj (e ▸ D.ju) with ⟨e1, _⟩ | ⟨e2, _⟩
    · exact absurd (e1.trans ez.symm) hwz
    · exact e2
  · have e := D.at_v_notpar hh (ez ▸ joins_inc_right hj) hp
    refine Or.inr ⟨e, ez, ?_⟩
    rcases joins_unique hj (e ▸ D.jv) with ⟨e1, _⟩ | ⟨e2, _⟩
    · exact absurd (e1.trans ez.symm) hwz
    · exact e2

/-- the third edges of the digon `f` at a vertex `w` outside the digons -/
theorem third_cases' (hG : InG X P) (h4 : 4 ≤ vcount P) {f : Fin X.m} (hf : FirstD P f) {h : Fin X.m} {w z : Fin X.n}
    (hh : P h) (hj : X.Joins h w z) (hw : ¬ InDig P w) (hzf : X.Inc f z) :
    (h = (dg hG h4 f hf).gu ∧ w = (dg hG h4 f hf).x) ∨ (h = (dg hG h4 f hf).gv ∧ w = (dg hG h4 f hf).y) := by
  set D := dg hG h4 f hf
  have hp : ¬ IsPar P h := fun hp => hw (isPar_inc_dig hp (joins_inc_left hj))
  have hwz : w ≠ z := ne_of_joins hG.1 hj
  rcases inc_of_joins (dg_joins hG h4 f hf) hzf with ez | ez
  · have e := D.at_u_notpar hh (ez ▸ joins_inc_right hj) hp
    refine Or.inl ⟨e, ?_⟩
    rcases joins_unique hj (e ▸ D.ju) with ⟨e1, _⟩ | ⟨e2, _⟩
    · exact absurd (e1.trans ez.symm) hwz
    · exact e2
  · have e := D.at_v_notpar hh (ez ▸ joins_inc_right hj) hp
    refine Or.inr ⟨e, ?_⟩
    rcases joins_unique hj (e ▸ D.jv) with ⟨e1, _⟩ | ⟨e2, _⟩
    · exact absurd (e1.trans ez.symm) hwz
    · exact e2

section cubic
variable {hG : InG X P} {h4 : 4 ≤ vcount P}

/-- the edge of `H` at `w` corresponding to the edge `h` of `P` at `w` -/
noncomputable def imgE (hG : InG X P) (h4 : 4 ≤ vcount P) (w : Fin X.n) (h : Fin X.m) : Fin (supY hG h4).m :=
  if hz : InDig P (other h w) then yN (digOf hz) else yO h

theorem supQ_vertex (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {w : Fin X.n} {e : Fin (supY hG h4).m}
    (he : supQ hG h4 e) (hw : (supY hG h4).Inc e w) : ¬ InDig P w ∧ meets P w := by
  rcases sup_cases e with ⟨f, rfl⟩ | ⟨f, rfl⟩
  · obtain ⟨hf, h1, h2'⟩ := (supQ_yO f).1 he
    have hw' : X.Inc f w := by unfold Inc at hw ⊢; rw [supY_ends_yO] at hw; exact hw
    refine ⟨?_, ⟨f, hf, hw'⟩⟩
    rcases hw' with e | e
    · rw [← e]; exact h1
    · rw [← e]; exact h2'
  · have hf := (supQ_yN f).1 he
    set D := dg hG h4 f hf
    have hw' : w = D.x ∨ w = D.y := by
      unfold Inc at hw; rw [supY_ends_yN hf] at hw
      rcases hw with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm
    rcases hw' with rfl | rfl
    · exact ⟨D.x_not_dig hG h2 h10, ⟨D.gu, D.hgu, joins_inc_right D.ju⟩⟩
    · exact ⟨D.y_not_dig hG h2 h10, ⟨D.gv, D.hgv, joins_inc_right D.jv⟩⟩

theorem imgE_spec (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {w : Fin X.n} (hw : ¬ InDig P w) {h : Fin X.m}
    (hh : P h) (hhw : X.Inc h w) : supQ hG h4 (imgE hG h4 w h) ∧ (supY hG h4).Inc (imgE hG h4 w h) w := by
  have hj := joins_other hhw
  unfold imgE
  by_cases hz : InDig P (other h w)
  · rw [dif_pos hz]
    have hf := (digOf_spec hz).1
    refine ⟨(supQ_yN _).2 hf, ?_⟩
    unfold Inc; rw [supY_ends_yN hf]
    rcases third_cases' hG h4 hf hh hj hw (digOf_spec hz).2 with ⟨_, e⟩ | ⟨_, e⟩
    · exact Or.inl e.symm
    · exact Or.inr e.symm
  · rw [dif_neg hz]
    refine ⟨(supQ_yO h).2 ⟨hh, ?_, ?_⟩, ?_⟩
    · rcases hj with e | e <;> rw [e]
      · exact hw
      · exact hz
    · rcases hj with e | e <;> rw [e]
      · exact hz
      · exact hw
    · unfold Inc; rw [supY_ends_yO]; exact hhw

theorem imgE_inj {w : Fin X.n} (hw : ¬ InDig P w) {h h' : Fin X.m} (hh : P h) (hh' : P h') (hhw : X.Inc h w)
    (hh'w : X.Inc h' w) (heq : imgE hG h4 w h = imgE hG h4 w h') : h = h' := by
  have hj := joins_other hhw
  have hj' := joins_other hh'w
  unfold imgE at heq
  by_cases hz : InDig P (other h w) <;> by_cases hz' : InDig P (other h' w)
  · rw [dif_pos hz, dif_pos hz'] at heq
    have ef := yN_inj heq
    have hf := (digOf_spec hz).1
    have hz'f : X.Inc (digOf hz) (other h' w) := ef ▸ (digOf_spec hz').2
    rcases third_cases' hG h4 hf hh hj hw (digOf_spec hz).2 with ⟨e1, x1⟩ | ⟨e1, y1⟩ <;>
      rcases third_cases' hG h4 hf hh' hj' hw hz'f with ⟨e2, x2⟩ | ⟨e2, y2⟩
    · exact e1.trans e2.symm
    · exact absurd (x1.symm.trans y2) (dg hG h4 _ hf).hxy
    · exact absurd (x2.symm.trans y1) (dg hG h4 _ hf).hxy
    · exact e1.trans e2.symm
  · rw [dif_pos hz, dif_neg hz'] at heq; exact absurd heq.symm (yO_ne_yN _ _)
  · rw [dif_neg hz, dif_pos hz'] at heq; exact absurd heq (yO_ne_yN _ _)
  · rw [dif_neg hz, dif_neg hz'] at heq; exact yO_inj heq

theorem imgE_surj {w : Fin X.n} (hw : ¬ InDig P w) {e : Fin (supY hG h4).m} (he : supQ hG h4 e)
    (hew : (supY hG h4).Inc e w) : ∃ h, P h ∧ X.Inc h w ∧ e = imgE hG h4 w h := by
  rcases sup_cases e with ⟨h, rfl⟩ | ⟨f, rfl⟩
  · obtain ⟨hh, h1, h2'⟩ := (supQ_yO h).1 he
    have hhw : X.Inc h w := by unfold Inc at hew ⊢; rw [supY_ends_yO] at hew; exact hew
    refine ⟨h, hh, hhw, ?_⟩
    unfold imgE
    have hz : ¬ InDig P (other h w) := by
      rcases inc_of_joins (joins_ends h) (joins_inc_right (joins_other hhw)) with e | e <;> rw [e]
      · exact h1
      · exact h2'
    rw [dif_neg hz]
  · have hf := (supQ_yN f).1 he
    set D := dg hG h4 f hf
    have hw' : w = D.x ∨ w = D.y := by
      unfold Inc at hew; rw [supY_ends_yN hf] at hew
      rcases hew with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm
    -- the third edge at the digon vertex next to `w`
    have key : ∀ (g : Fin X.m) (z : Fin X.n), P g → X.Joins g z w → X.Inc f z →
        yN f = imgE hG h4 w g := by
      intro g z hg jg hzf
      have hzw : other g w = z := by
        rcases joins_unique (joins_other (joins_inc_right jg)) (Or.symm jg) with ⟨_, e⟩ | ⟨e1, _⟩
        · exact e
        · exact absurd e1.symm (ne_of_joins hG.1 jg)
      have hzd : InDig P (other g w) := hzw ▸ ⟨f, firstD_isPar hf, hzf⟩
      unfold imgE
      rw [dif_pos hzd]
      congr 1
      exact first_unique hG h4 hf (digOf_spec hzd).1 (hzw ▸ hzf) (digOf_spec hzd).2
    rcases hw' with rfl | rfl
    · refine ⟨D.gu, D.hgu, joins_inc_right D.ju, key D.gu D.u D.hgu D.ju ?_⟩
      rw [show D.u = (X.ends f).1 from dg_u hG h4 f hf]; exact Or.inl rfl
    · refine ⟨D.gv, D.hgv, joins_inc_right D.jv, key D.gv D.v D.hgv D.jv ?_⟩
      rw [show D.v = (X.ends f).2 from dg_v hG h4 f hf]; exact Or.inr rfl

theorem supQ_cubic (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) : CubicOn (supQ hG h4) := by
  rintro w ⟨e0, he0, hw0⟩
  obtain ⟨hw, hmw⟩ := supQ_vertex h2 h10 he0 hw0
  obtain ⟨a, b, c, ha, hb, hc, ia, ib, ic, dab, dac, dbc, hall⟩ := hG.2.2.2 w hmw
  have sa := imgE_spec (hG := hG) (h4 := h4) h2 h10 hw ha ia
  have sb := imgE_spec (hG := hG) (h4 := h4) h2 h10 hw hb ib
  have sc := imgE_spec (hG := hG) (h4 := h4) h2 h10 hw hc ic
  refine ⟨_, _, _, sa.1, sb.1, sc.1, sa.2, sb.2, sc.2, fun h => dab (imgE_inj hw ha hb ia ib h),
    fun h => dac (imgE_inj hw ha hc ia ic h), fun h => dbc (imgE_inj hw hb hc ib ic h), ?_⟩
  intro e he hew
  obtain ⟨h, hh, hhw, rfl⟩ := imgE_surj hw he hew
  rcases hall h hh hhw with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end cubic

/-! #### the isomorphism `P ≅ H^D` -/

theorem dg_congr (hG : InG X P) (h4 : 4 ≤ vcount P) {f f' : Fin X.m} (hf : FirstD P f) (hf' : FirstD P f')
    (e : f = f') : dg hG h4 f hf = dg hG h4 f' hf' := by
  subst e; rfl

section iso
variable (hG : InG X P) (h4 : 4 ≤ vcount P)

/-- the vertex map: vertices outside the digons are old vertices; the ends `u`, `v` of the lower edge `f` of a digon
    go to the new vertices `dU (yN f)`, `dV (yN f)` -/
noncomputable def phiH (w : RH2Fid.SubV X P) : Fin (digG (supY hG h4) (supD hG h4)).n :=
  if hw : InDig P w.1 then
    (if w.1 = (X.ends (digOf hw)).1 then dU (X := supY hG h4) (yN (digOf hw)) else dV (X := supY hG h4) (yN (digOf hw)))
  else dO (X := supY hG h4) w.1

/-- the edge map: old edges away from the digons stay; the two parallel edges of the digon `f` go to `eN (yN f) 0`
    (`f` itself) and `eN (yN f) 1`; the third edge at `u` goes to `eO (yN f)` and the third edge at `v` to
    `eN (yN f) 2` -/
noncomputable def psiH (h : RH2Fid.SubE X P) : Fin (digG (supY hG h4) (supD hG h4)).m :=
  if hp : IsPar P h.1 then
    (if h.1 = Classical.choose (isPar_first hp) then eN (X := supY hG h4) (yN (Classical.choose (isPar_first hp))) 0
      else eN (X := supY hG h4) (yN (Classical.choose (isPar_first hp))) 1)
  else if hu : InDig P (X.ends h.1).1 then
    (if (X.ends h.1).1 = (X.ends (digOf hu)).1 then eO (X := supY hG h4) (yN (digOf hu))
      else eN (X := supY hG h4) (yN (digOf hu)) 2)
  else if hv : InDig P (X.ends h.1).2 then
    (if (X.ends h.1).2 = (X.ends (digOf hv)).1 then eO (X := supY hG h4) (yN (digOf hv))
      else eN (X := supY hG h4) (yN (digOf hv)) 2)
  else eO (X := supY hG h4) (yO h.1)

variable {hG h4}

theorem phiH_out {w : RH2Fid.SubV X P} (hw : ¬ InDig P w.1) : phiH hG h4 w = dO (X := supY hG h4) w.1 := by
  unfold phiH; rw [dif_neg hw]

theorem phiH_u {f : Fin X.m} (hf : FirstD P f) {w : RH2Fid.SubV X P} (hw : w.1 = (X.ends f).1) :
    phiH hG h4 w = dU (X := supY hG h4) (yN f) := by
  have hd : InDig P w.1 := ⟨f, firstD_isPar hf, Or.inl hw.symm⟩
  have e := first_unique hG h4 (digOf_spec hd).1 hf (digOf_spec hd).2 (Or.inl hw.symm)
  unfold phiH
  rw [dif_pos hd]
  have : w.1 = (X.ends (digOf hd)).1 := by rw [e]; exact hw
  rw [if_pos this, e]

theorem phiH_v {f : Fin X.m} (hf : FirstD P f) {w : RH2Fid.SubV X P} (hw : w.1 = (X.ends f).2) :
    phiH hG h4 w = dV (X := supY hG h4) (yN f) := by
  have hd : InDig P w.1 := ⟨f, firstD_isPar hf, Or.inr hw.symm⟩
  have e := first_unique hG h4 (digOf_spec hd).1 hf (digOf_spec hd).2 (Or.inr hw.symm)
  unfold phiH
  rw [dif_pos hd]
  have : ¬ w.1 = (X.ends (digOf hd)).1 := by rw [e, hw]; exact fun h => hG.1 f h.symm
  rw [if_neg this, e]

theorem psiH_old {h : RH2Fid.SubE X P} (hp : ¬ IsPar P h.1) (h1 : ¬ InDig P (X.ends h.1).1)
    (h2' : ¬ InDig P (X.ends h.1).2) : psiH hG h4 h = eO (X := supY hG h4) (yO h.1) := by
  unfold psiH; rw [dif_neg hp, dif_neg h1, dif_neg h2']

theorem psiH_par {h : RH2Fid.SubE X P} (hp : IsPar P h.1) {f : Fin X.m} (hf : FirstD P f)
    (hj : X.Joins h.1 (X.ends f).1 (X.ends f).2) :
    psiH hG h4 h = if h.1 = f then eN (X := supY hG h4) (yN f) 0 else eN (X := supY hG h4) (yN f) 1 := by
  have hc := Classical.choose_spec (isPar_first hp)
  have e : Classical.choose (isPar_first hp) = f :=
    first_unique hG h4 hc.1 hf (by
      rcases inc_of_joins hc.2 (Or.inl rfl : X.Inc h.1 (X.ends h.1).1) with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm) (by
      rcases inc_of_joins hj (Or.inl rfl : X.Inc h.1 (X.ends h.1).1) with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
  unfold psiH; rw [dif_pos hp, e]

include hG h4 in
/-- a non-parallel edge at a digon vertex `z`: its other end lies outside the digons -/
theorem notpar_other (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {h : Fin X.m} (hh : P h) (hp : ¬ IsPar P h)
    {f : Fin X.m} (hf : FirstD P f) {z w : Fin X.n} (hj : X.Joins h z w) (hz : X.Inc f z) : ¬ InDig P w := by
  set D := dg hG h4 f hf
  rcases inc_of_joins (dg_joins hG h4 f hf) hz with ez | ez
  · have e := D.at_u_notpar hh (ez ▸ joins_inc_left hj) hp
    rcases joins_unique hj (e ▸ D.ju) with ⟨_, e2⟩ | ⟨e1, _⟩
    · rw [e2]; exact D.x_not_dig hG h2 h10
    · exact absurd (ez.symm.trans e1) (Ne.symm D.hxu)
  · have e := D.at_v_notpar hh (ez ▸ joins_inc_left hj) hp
    rcases joins_unique hj (e ▸ D.jv) with ⟨_, e2⟩ | ⟨e1, _⟩
    · rw [e2]; exact D.y_not_dig hG h2 h10
    · exact absurd (ez.symm.trans e1) (Ne.symm D.hyv)

theorem psiH_thU (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {h : RH2Fid.SubE X P} (hp : ¬ IsPar P h.1)
    {f : Fin X.m} (hf : FirstD P f) (hu : X.Inc h.1 (X.ends f).1) : psiH hG h4 h = eO (X := supY hG h4) (yN f) := by
  unfold psiH
  rw [dif_neg hp]
  rcases hu with e | e
  · have hd : InDig P (X.ends h.1).1 := ⟨f, firstD_isPar hf, Or.inl e.symm⟩
    have ef := first_unique hG h4 (digOf_spec hd).1 hf (digOf_spec hd).2 (Or.inl e.symm)
    rw [dif_pos hd, ef, if_pos e]
  · have hn : ¬ InDig P (X.ends h.1).1 :=
      notpar_other (hG := hG) (h4 := h4) h2 h10 h.2 hp hf (Or.symm (joins_ends h.1) : X.Joins h.1 (X.ends h.1).2 (X.ends h.1).1)
        (Or.inl e.symm)
    have hd : InDig P (X.ends h.1).2 := ⟨f, firstD_isPar hf, Or.inl e.symm⟩
    have ef := first_unique hG h4 (digOf_spec hd).1 hf (digOf_spec hd).2 (Or.inl e.symm)
    rw [dif_neg hn, dif_pos hd, ef, if_pos e]

theorem psiH_thV (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {h : RH2Fid.SubE X P} (hp : ¬ IsPar P h.1)
    {f : Fin X.m} (hf : FirstD P f) (hv : X.Inc h.1 (X.ends f).2) : psiH hG h4 h = eN (X := supY hG h4) (yN f) 2 := by
  unfold psiH
  rw [dif_neg hp]
  have huv : (X.ends f).2 ≠ (X.ends f).1 := fun e => hG.1 f e.symm
  rcases hv with e | e
  · have hd : InDig P (X.ends h.1).1 := ⟨f, firstD_isPar hf, Or.inr e.symm⟩
    have ef := first_unique hG h4 (digOf_spec hd).1 hf (digOf_spec hd).2 (Or.inr e.symm)
    rw [dif_pos hd, ef, if_neg (by rw [e]; exact huv)]
  · have hn : ¬ InDig P (X.ends h.1).1 :=
      notpar_other (hG := hG) (h4 := h4) h2 h10 h.2 hp hf (Or.symm (joins_ends h.1) : X.Joins h.1 (X.ends h.1).2 (X.ends h.1).1)
        (Or.inr e.symm)
    have hd : InDig P (X.ends h.1).2 := ⟨f, firstD_isPar hf, Or.inr e.symm⟩
    have ef := first_unique hG h4 (digOf_spec hd).1 hf (digOf_spec hd).2 (Or.inr e.symm)
    rw [dif_neg hn, dif_pos hd, ef, if_neg (by rw [e]; exact huv)]

/-- the three kinds of edges of `P` -/
theorem edge_kinds (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) (h : RH2Fid.SubE X P) :
    (∃ f, FirstD P f ∧ IsPar P h.1 ∧ X.Joins h.1 (X.ends f).1 (X.ends f).2) ∨
    (∃ f, ∃ hf : FirstD P f, ¬ IsPar P h.1 ∧ h.1 = (dg hG h4 f hf).gu) ∨
    (∃ f, ∃ hf : FirstD P f, ¬ IsPar P h.1 ∧ h.1 = (dg hG h4 f hf).gv) ∨
    (¬ IsPar P h.1 ∧ ¬ InDig P (X.ends h.1).1 ∧ ¬ InDig P (X.ends h.1).2) := by
  by_cases hp : IsPar P h.1
  · obtain ⟨f, hf, hj⟩ := isPar_first hp
    exact Or.inl ⟨f, hf, hp, hj⟩
  -- a non-parallel edge at a digon vertex is a third edge of that digon
  have third : ∀ z, X.Inc h.1 z → InDig P z →
      (∃ f, ∃ hf : FirstD P f, ¬ IsPar P h.1 ∧ h.1 = (dg hG h4 f hf).gu) ∨
      (∃ f, ∃ hf : FirstD P f, ¬ IsPar P h.1 ∧ h.1 = (dg hG h4 f hf).gv) := by
    intro z hz hzd
    have hf := (digOf_spec hzd).1
    set D := dg hG h4 _ hf
    rcases inc_of_joins (dg_joins hG h4 _ hf) (digOf_spec hzd).2 with ez | ez
    · exact Or.inl ⟨_, hf, hp, D.at_u_notpar h.2 (ez ▸ hz) hp⟩
    · exact Or.inr ⟨_, hf, hp, D.at_v_notpar h.2 (ez ▸ hz) hp⟩
  by_cases h1 : InDig P (X.ends h.1).1
  · rcases third _ (Or.inl rfl) h1 with t | t
    · exact Or.inr (Or.inl t)
    · exact Or.inr (Or.inr (Or.inl t))
  by_cases h2' : InDig P (X.ends h.1).2
  · rcases third _ (Or.inr rfl) h2' with t | t
    · exact Or.inr (Or.inl t)
    · exact Or.inr (Or.inr (Or.inl t))
  exact Or.inr (Or.inr (Or.inr ⟨hp, h1, h2'⟩))

/-- **the edge map respects ends** -/
theorem psiH_joins (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) (h : RH2Fid.SubE X P) :
    (digG (supY hG h4) (supD hG h4)).Joins (psiH hG h4 h)
      (phiH hG h4 ⟨(X.ends h.1).1, h.1, h.2, Or.inl rfl⟩) (phiH hG h4 ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩) := by
  rcases edge_kinds (hG := hG) (h4 := h4) h2 h10 h with ⟨f, hf, hp, hj⟩ | ⟨f, hf, hp, hgu⟩ | ⟨f, hf, hp, hgv⟩ |
    ⟨hp, h1, h2'⟩
  · -- a parallel edge: `eN (yN f) 0/1` joins `dU (yN f)` and `dV (yN f)`
    have hk : ∀ k : Fin 3, k ≠ 2 → (digG (supY hG h4) (supD hG h4)).Joins (eN (X := supY hG h4) (yN f) k)
        (phiH hG h4 ⟨(X.ends h.1).1, h.1, h.2, Or.inl rfl⟩) (phiH hG h4 ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩) := by
      intro k hk
      rcases hj with e | e
      · have e1 : (X.ends h.1).1 = (X.ends f).1 := by rw [e]
        have e2 : (X.ends h.1).2 = (X.ends f).2 := by rw [e]
        rw [phiH_u hf e1, phiH_v hf e2]
        exact Or.inl (ends_eN01 _ k hk)
      · have e1 : (X.ends h.1).1 = (X.ends f).2 := by rw [e]
        have e2 : (X.ends h.1).2 = (X.ends f).1 := by rw [e]
        rw [phiH_v hf e1, phiH_u hf e2]
        exact Or.inr (ends_eN01 _ k hk)
    rw [psiH_par hp hf hj]
    split_ifs
    · exact hk 0 (by decide)
    · exact hk 1 (by decide)
  · -- the third edge at `u`: `eO (yN f)` joins `dO x` and `dU (yN f)`
    set D := dg hG h4 f hf
    have hju : X.Joins h.1 D.u D.x := hgu ▸ D.ju
    have hu : X.Inc h.1 (X.ends f).1 := by rw [← dg_u hG h4 f hf]; exact joins_inc_left hju
    rw [psiH_thU h2 h10 hp hf hu]
    have hx : ¬ InDig P D.x := D.x_not_dig hG h2 h10
    have hE : (digG (supY hG h4) (supD hG h4)).ends (eO (X := supY hG h4) (yN f)) = (dO (X := supY hG h4) D.x, dU (X := supY hG h4) (yN f)) := by
      rw [ends_eO_D (supD_yN f), supY_ends_yN hf]
    rcases joins_unique (joins_ends h.1) hju with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [phiH_u hf (e1.trans (dg_u hG h4 f hf)), phiH_out (w := ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩)
        (by show ¬ InDig P (X.ends h.1).2; rw [e2]; exact hx)]
      simp only [e2]
      exact Or.inr hE
    · rw [phiH_u (w := ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩) hf (e2.trans (dg_u hG h4 f hf)),
        phiH_out (w := ⟨(X.ends h.1).1, h.1, h.2, Or.inl rfl⟩)
        (by show ¬ InDig P (X.ends h.1).1; rw [e1]; exact hx)]
      simp only [e1]
      exact Or.inl hE
  · -- the third edge at `v`: `eN (yN f) 2` joins `dV (yN f)` and `dO y`
    set D := dg hG h4 f hf
    have hjv : X.Joins h.1 D.v D.y := hgv ▸ D.jv
    have hv : X.Inc h.1 (X.ends f).2 := by rw [← dg_v hG h4 f hf]; exact joins_inc_left hjv
    rw [psiH_thV h2 h10 hp hf hv]
    have hy : ¬ InDig P D.y := D.y_not_dig hG h2 h10
    have hE : (digG (supY hG h4) (supD hG h4)).ends (eN (X := supY hG h4) (yN f) 2) = (dV (X := supY hG h4) (yN f), dO (X := supY hG h4) D.y) := by
      rw [ends_eN2, supY_ends_yN hf]
    rcases joins_unique (joins_ends h.1) hjv with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [phiH_v hf (e1.trans (dg_v hG h4 f hf)), phiH_out (w := ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩)
        (by show ¬ InDig P (X.ends h.1).2; rw [e2]; exact hy)]
      simp only [e2]
      exact Or.inl hE
    · rw [phiH_v (w := ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩) hf (e2.trans (dg_v hG h4 f hf)),
        phiH_out (w := ⟨(X.ends h.1).1, h.1, h.2, Or.inl rfl⟩)
        (by show ¬ InDig P (X.ends h.1).1; rw [e1]; exact hy)]
      simp only [e1]
      exact Or.inr hE
  · -- an old edge
    rw [psiH_old hp h1 h2', phiH_out (w := ⟨(X.ends h.1).1, h.1, h.2, Or.inl rfl⟩) h1,
      phiH_out (w := ⟨(X.ends h.1).2, h.1, h.2, Or.inr rfl⟩) h2']
    left
    rw [ends_eO_nD (supD_yO h.1), supY_ends_yO]

theorem DigData.gu_notpar (D : DigData P) : ¬ IsPar P D.gu := by
  rintro ⟨_, h, hh, hne, hj⟩
  exact D.third_not_par D.hgu hh (Ne.symm hne) rfl hj

theorem DigData.gv_notpar (D : DigData P) : ¬ IsPar P D.gv := D.swap.gu_notpar

theorem psiH_mem (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) (h : RH2Fid.SubE X P) :
    digSet (supQ hG h4) (supD hG h4) (psiH hG h4 h) := by
  rcases edge_kinds (hG := hG) (h4 := h4) h2 h10 h with ⟨f, hf, hp, hj⟩ | ⟨f, hf, hp, hgu⟩ | ⟨f, hf, hp, hgv⟩ |
    ⟨hp, h1, h2'⟩
  · rw [psiH_par hp hf hj]
    split_ifs <;> exact (set_eN _ _ _).2 ⟨(supQ_yN f).2 hf, supD_yN f⟩
  · have hu : X.Inc h.1 (X.ends f).1 := by
      rw [← dg_u hG h4 f hf, hgu]; exact joins_inc_left (dg hG h4 f hf).ju
    rw [psiH_thU h2 h10 hp hf hu]; exact (set_eO _ _).2 ((supQ_yN f).2 hf)
  · have hv : X.Inc h.1 (X.ends f).2 := by
      rw [← dg_v hG h4 f hf, hgv]; exact joins_inc_left (dg hG h4 f hf).jv
    rw [psiH_thV h2 h10 hp hf hv]; exact (set_eN _ _ _).2 ⟨(supQ_yN f).2 hf, supD_yN f⟩
  · rw [psiH_old hp h1 h2']; exact (set_eO _ _).2 ((supQ_yO h.1).2 ⟨h.2, h1, h2'⟩)

/-- the value of the edge map, by kind -/
theorem psiH_val (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) (h : RH2Fid.SubE X P) :
    (∃ f, FirstD P f ∧ X.Joins h.1 (X.ends f).1 (X.ends f).2 ∧
      ((h.1 = f ∧ psiH hG h4 h = eN (X := supY hG h4) (yN f) 0) ∨
       (h.1 ≠ f ∧ psiH hG h4 h = eN (X := supY hG h4) (yN f) 1))) ∨
    (∃ f, ∃ hf : FirstD P f, h.1 = (dg hG h4 f hf).gu ∧ psiH hG h4 h = eO (X := supY hG h4) (yN f)) ∨
    (∃ f, ∃ hf : FirstD P f, h.1 = (dg hG h4 f hf).gv ∧ psiH hG h4 h = eN (X := supY hG h4) (yN f) 2) ∨
    (psiH hG h4 h = eO (X := supY hG h4) (yO h.1)) := by
  rcases edge_kinds (hG := hG) (h4 := h4) h2 h10 h with ⟨f, hf, hp, hj⟩ | ⟨f, hf, hp, hgu⟩ | ⟨f, hf, hp, hgv⟩ |
    ⟨hp, h1, h2'⟩
  · refine Or.inl ⟨f, hf, hj, ?_⟩
    rw [psiH_par hp hf hj]
    by_cases e : h.1 = f
    · exact Or.inl ⟨e, by rw [if_pos e]⟩
    · exact Or.inr ⟨e, by rw [if_neg e]⟩
  · have hu : X.Inc h.1 (X.ends f).1 := by
      rw [← dg_u hG h4 f hf, hgu]; exact joins_inc_left (dg hG h4 f hf).ju
    exact Or.inr (Or.inl ⟨f, hf, hgu, psiH_thU h2 h10 hp hf hu⟩)
  · have hv : X.Inc h.1 (X.ends f).2 := by
      rw [← dg_v hG h4 f hf, hgv]; exact joins_inc_left (dg hG h4 f hf).jv
    exact Or.inr (Or.inr (Or.inl ⟨f, hf, hgv, psiH_thV h2 h10 hp hf hv⟩))
  · exact Or.inr (Or.inr (Or.inr (psiH_old hp h1 h2')))

theorem eN_ne2 {f f' : Fin X.m} {k : Fin 3} (hk : k ≠ 2) :
    (eN (X := supY hG h4) (yN f) k : Fin (digG (supY hG h4) (supD hG h4)).m) ≠ eN (X := supY hG h4) (yN f') 2 :=
  fun e => hk (eN_inj e).2

theorem psiH_inj (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {h h' : RH2Fid.SubE X P}
    (heq : psiH hG h4 h = psiH hG h4 h') : h = h' := by
  apply Subtype.ext
  rcases psiH_val (hG := hG) (h4 := h4) h2 h10 h with ⟨f, hf, hj, ⟨e1, v1⟩ | ⟨e1, v1⟩⟩ | ⟨f, hf, e1, v1⟩ |
    ⟨f, hf, e1, v1⟩ | v1 <;>
  rcases psiH_val (hG := hG) (h4 := h4) h2 h10 h' with ⟨f', hf', hj', ⟨e2, v2⟩ | ⟨e2, v2⟩⟩ | ⟨f', hf', e2, v2⟩ |
    ⟨f', hf', e2, v2⟩ | v2 <;>
  rw [v1, v2] at heq
  all_goals first
    | exact absurd heq (eO_ne_eN _ _ _)
    | exact absurd heq.symm (eO_ne_eN _ _ _)
    | exact absurd (eN_inj heq).2 (by decide)
    | exact absurd (eO_inj heq) (yO_ne_yN _ _)
    | exact absurd (eO_inj heq).symm (yO_ne_yN _ _)
    | exact yO_inj (eO_inj heq)
    | (rw [e1, e2]; exact yN_inj (eN_inj heq).1)
    | (have ef := yN_inj (eO_inj heq); subst ef; rw [e1, e2])
    | (have ef := yN_inj (eN_inj heq).1; subst ef; rw [e1, e2])
    | (have ef := yN_inj (eN_inj heq).1
       subst ef
       exact three_in_two ((dg hG h4 _ hf).par_of hf.1 (dg_joins hG h4 _ hf))
         ((dg hG h4 _ hf).par_of h'.2 (by rw [dg_u, dg_v]; exact hj'))
         ((dg hG h4 _ hf).par_of h.2 (by rw [dg_u, dg_v]; exact hj)) (Ne.symm e2) e1)

theorem psiH_surj (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) {e : Fin (digG (supY hG h4) (supD hG h4)).m}
    (he : digSet (supQ hG h4) (supD hG h4) e) : ∃ h, psiH hG h4 h = e := by
  rcases dig_cases e with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
  · have hq := (set_eO _ d).1 he
    rcases sup_cases d with ⟨g, rfl⟩ | ⟨f, rfl⟩
    · obtain ⟨hg, h1, h2'⟩ := (supQ_yO g).1 hq
      have hp : ¬ IsPar P g := fun hp => h1 (isPar_inc_dig hp (Or.inl rfl))
      exact ⟨⟨g, hg⟩, psiH_old hp h1 h2'⟩
    · have hf := (supQ_yN f).1 hq
      set D := dg hG h4 f hf
      have hu : X.Inc D.gu (X.ends f).1 := by rw [← dg_u hG h4 f hf]; exact joins_inc_left D.ju
      exact ⟨⟨D.gu, D.hgu⟩, psiH_thU h2 h10 D.gu_notpar hf hu⟩
  · obtain ⟨hq, hD⟩ := (set_eN _ d k).1 he
    rcases sup_cases d with ⟨g, rfl⟩ | ⟨f, rfl⟩
    · exact absurd hD (supD_yO g)
    · have hf := (supQ_yN f).1 hq
      set D := dg hG h4 f hf
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by
        rcases k with ⟨k, hk3⟩; simp only [Fin.ext_iff]; omega
      rcases hk with rfl | rfl | rfl
      · refine ⟨⟨f, hf.1⟩, ?_⟩
        rw [psiH_par (firstD_isPar hf) hf (joins_ends f), if_pos rfl]
      · obtain ⟨g, hg, hlt, hj⟩ := hf.2
        have hgf : g ≠ f := fun e => by rw [e] at hlt; exact Nat.lt_irrefl _ hlt
        have hp : IsPar P g := ⟨hg, f, hf.1, Ne.symm hgf, by
          rcases hj with e | e <;> rw [e]
          · exact joins_ends f
          · exact Or.symm (joins_ends f)⟩
        refine ⟨⟨g, hg⟩, ?_⟩
        rw [psiH_par hp hf hj, if_neg hgf]
      · have hv : X.Inc D.gv (X.ends f).2 := by rw [← dg_v hG h4 f hf]; exact joins_inc_left D.jv
        exact ⟨⟨D.gv, D.hgv⟩, psiH_thV h2 h10 D.gv_notpar hf hv⟩

theorem phiH_inj {w w' : RH2Fid.SubV X P} (heq : phiH hG h4 w = phiH hG h4 w') : w = w' := by
  apply Subtype.ext
  -- the value of the vertex map
  have val : ∀ w : RH2Fid.SubV X P, (¬ InDig P w.1 ∧ phiH hG h4 w = dO (X := supY hG h4) w.1) ∨
      (∃ f, FirstD P f ∧ w.1 = (X.ends f).1 ∧ phiH hG h4 w = dU (X := supY hG h4) (yN f)) ∨
      (∃ f, FirstD P f ∧ w.1 = (X.ends f).2 ∧ phiH hG h4 w = dV (X := supY hG h4) (yN f)) := by
    intro w
    by_cases hw : InDig P w.1
    · have hf := (digOf_spec hw).1
      rcases inc_of_joins (joins_ends (digOf hw)) (digOf_spec hw).2 with e | e
      · exact Or.inr (Or.inl ⟨_, hf, e, phiH_u hf e⟩)
      · exact Or.inr (Or.inr ⟨_, hf, e, phiH_v hf e⟩)
    · exact Or.inl ⟨hw, phiH_out hw⟩
  rcases val w with ⟨_, v1⟩ | ⟨f, _, e1, v1⟩ | ⟨f, _, e1, v1⟩ <;>
    rcases val w' with ⟨_, v2⟩ | ⟨f', _, e2, v2⟩ | ⟨f', _, e2, v2⟩ <;> rw [v1, v2] at heq
  · exact dO_inj (X := supY hG h4) heq
  · exact absurd heq (dO_ne_dU (X := supY hG h4) _ _)
  · exact absurd heq (dO_ne_dV (X := supY hG h4) _ _)
  · exact absurd heq.symm (dO_ne_dU (X := supY hG h4) _ _)
  · rw [e1, e2, yN_inj (dU_inj (X := supY hG h4) heq)]
  · exact absurd heq (dU_ne_dV (X := supY hG h4) _ _)
  · exact absurd heq.symm (dO_ne_dV (X := supY hG h4) _ _)
  · exact absurd heq.symm (dU_ne_dV (X := supY hG h4) _ _)
  · rw [e1, e2, yN_inj (dV_inj (X := supY hG h4) heq)]

/-- **the isomorphism**: the plain reading of `P` is the edge set of `H^D` -/
noncomputable def repH (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) :
    RH2Fid.Rep (RH2Fid.subEn X P) (digG (supY hG h4) (supD hG h4)) (digSet (supQ hG h4) (supD hG h4)) where
  φ := phiH hG h4
  ψ := psiH hG h4
  φinj := fun _ _ h => phiH_inj h
  ψinj := fun _ _ h => psiH_inj h2 h10 h
  ψP := psiH_mem h2 h10
  ψsurj := fun _ he => psiH_surj h2 h10 he
  φsurj := by
    intro x e he hx
    obtain ⟨h, rfl⟩ := psiH_surj h2 h10 he
    rcases inc_of_joins (psiH_joins h2 h10 h) hx with e | e
    · exact ⟨_, e.symm⟩
    · exact ⟨_, e.symm⟩
  hend := by
    intro h
    have hj := psiH_joins (hG := hG) (h4 := h4) h2 h10 h
    rw [RH2Fid.joins_iff_sym2] at hj
    rw [hj]
    rfl

end iso

end supp







end digons

section converse
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the handshake count for a loopless cubic edge set -/
theorem total_handshake {Y : MGraph} {Q : Fin Y.m → Prop} (hloop : Loopless Y) (hcub : CubicOn Q) :
    3 * vcount Q = 2 * cntF Y.m Q := by
  have hh := side_handshake hloop hcub (fun _ => true) true
  have e1 : scount Q (fun _ => true) true = vcount Q := by
    unfold scount vcount; apply cntF_congr; intro w; simp
  have e2 : cntF Y.m (inner Q (fun _ => true) true) = cntF Y.m Q := by
    apply cntF_congr; intro f; simp [inner]
  have e3 : cntF Y.m (RH2F.Crosses Q (fun _ => true)) = 0 := by
    apply cntF_eq_zero; intro f h; exact h.2 rfl
  omega

/-- **H-ASM (a), converse**: every 2-cut-reduced member `P` of 𝒢 on at least 10 vertices is isomorphic to a digon
    insertion `Q^D` of a simple 3-edge-connected cubic multigraph `Q` on at least 4 vertices, with
    `|V(P)| = |V(Q)| + 2 |Q ∩ D|`; in particular EX1-goodness of `Q^D` gives EX1-goodness of `P` -/
theorem hasm_converse (hG : InG X P) (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) :
    ∃ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q ∧ 4 ≤ vcount Q ∧
      vcount P = vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) ∧
      Nonempty (RH2Fid.Rep (RH2Fid.subEn X P) (digG Y D) (digSet Q D)) ∧ (EX1On (digSet Q D) → EX1On P) := by
  have h4 : 4 ≤ vcount P := by omega
  let R := repH (hG := hG) (h4 := h4) h2 h10
  let S0 := RH2Fid.subRep X P
  have hV := RH2Fid.sub_hV X P
  -- the plain reading of `P`
  have pC : RH2Fid.ConnectedP (RH2Fid.subEn X P) := S0.connectedP_of hV hG.2.1
  have pB : RH2Fid.BridgelessP (RH2Fid.subEn X P) := S0.bridgeless_iff.1 hG.2.2.1
  have pK : RH2Fid.CubicP (RH2Fid.subEn X P) := S0.cubicP_of hV hG.2.2.2
  have pT : RH2Fid.TwoCutReducedP (RH2Fid.subEn X P) := (S0.twoCutReduced_iff hV).1 h2
  -- the digon insertion `Q^D`
  have dC : ConnectedOn (digSet (supQ hG h4) (supD hG h4)) := R.connectedOn_of pC
  have dB : BridgelessOn (digSet (supQ hG h4) (supD hG h4)) := R.bridgeless_iff.2 pB
  have dT : TwoCutReducedOn (digSet (supQ hG h4) (supD hG h4)) := (R.twoCutReduced_iff hV).2 pT
  -- back to `Q`
  have hloop : Loopless (supY hG h4) := supY_loopless
  have hcub : CubicOn (supQ hG h4) := supQ_cubic h2 h10
  have hGQ : InG (supY hG h4) (supQ hG h4) := ⟨hloop, back_connected dC, back_bridgeless dB, hcub⟩
  have hpar : ∀ f g, supQ hG h4 f → supQ hG h4 g → ¬ supD hG h4 f → ¬ supD hG h4 g → f ≠ g →
      ¬ (supY hG h4).Joins g ((supY hG h4).ends f).1 ((supY hG h4).ends f).2 := by
    intro f g hf hg hDf hDg hfg hj
    rcases sup_cases f with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases sup_cases g with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · obtain ⟨ha, h1, _⟩ := (supQ_yO a).1 hf
        obtain ⟨hb, _, _⟩ := (supQ_yO b).1 hg
        rw [supY_ends_yO] at hj
        have hj' : X.Joins b (X.ends a).1 (X.ends a).2 := by
          unfold Joins at hj ⊢; rw [supY_ends_yO] at hj; exact hj
        exact h1 ⟨a, ⟨ha, b, hb, fun e => hfg (by rw [e]), hj'⟩, Or.inl rfl⟩
      · exact hDg (supD_yN b)
    · exact hDf (supD_yN a)
  have hno2 := back_no2cut hloop hcub dT hpar
  -- counting
  have hvd : vcount (digSet (supQ hG h4) (supD hG h4)) = vcount P := by
    rw [R.vcount_eq hV, S0.vcount_eq hV]
  have hcnt := vcount_dig (D := supD hG h4) hloop (P := supQ hG h4)
  have hhs := total_handshake hloop hcub
  have hle : cntF (supY hG h4).m (fun d => supQ hG h4 d ∧ supD hG h4 d) ≤ cntF (supY hG h4).m (supQ hG h4) :=
    cntF_mono _ _ _ (fun d h => h.1)
  have hQ4 : 4 ≤ vcount (supQ hG h4) := by omega
  refine ⟨supY hG h4, supQ hG h4, supD hG h4, ⟨hGQ, simple_of_no2cut hGQ hno2 hQ4, hno2⟩, hQ4, by omega, ⟨R⟩,
    fun h => RH2Fid.ex1_of_rep R h⟩

end converse

end RH2F

namespace RH2F
open MGraph

/-- **Layer 17 of the Lean formalization** (digon layer): H-ASM (fact fdd83999b9ec10e2) (a), converse — every
    2-cut-reduced member of 𝒢 on at least 10 vertices is isomorphic to a digon insertion `Q^D` of a member `Q` of 𝒮 on at
    least 4 vertices; the transfer of connectivity, bridgelessness and 3-edge-connectivity from `Q^D` back to `Q`;
    simplicity of 3-edge-connected cubic members of 𝒢; EX1-goodness along the correspondence `Rep`. -/
theorem layer17 :
    (∀ (Y : MGraph) (Q D : Fin Y.m → Prop), ConnectedOn (digSet Q D) → ConnectedOn Q) ∧
    (∀ (Y : MGraph) (Q D : Fin Y.m → Prop), BridgelessOn (digSet Q D) → BridgelessOn Q) ∧
    (∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Loopless Y → CubicOn Q → TwoCutReducedOn (digSet Q D) →
      (∀ f g, Q f → Q g → ¬ D f → ¬ D g → f ≠ g → ¬ Y.Joins g (Y.ends f).1 (Y.ends f).2) → ∀ S, ¬ TwoCut Q S) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → (∀ S, ¬ TwoCut P S) → 4 ≤ vcount P → SimpleP P) ∧
    (∀ (X Y : MGraph) (P : Fin X.m → Prop) (Q : Fin Y.m → Prop), RH2Fid.Rep (RH2Fid.subEn X P) Y Q →
      EX1On Q → EX1On P) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 10 ≤ vcount P →
      ∃ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q ∧ 4 ≤ vcount Q ∧
        vcount P = vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) ∧
        Nonempty (RH2Fid.Rep (RH2Fid.subEn X P) (digG Y D) (digSet Q D)) ∧ (EX1On (digSet Q D) → EX1On P)) :=
  ⟨fun _ _ _ h => back_connected h, fun _ _ _ h => back_bridgeless h,
   fun _ _ _ hl hc h2 hp => back_no2cut hl hc h2 hp, fun _ _ hG h3 h4 => simple_of_no2cut hG h3 h4,
   fun _ _ _ _ R h => RH2Fid.ex1_of_rep R h, fun _ _ hG h2 h10 => hasm_converse hG h2 h10⟩

end RH2F
