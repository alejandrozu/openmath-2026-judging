-- Lean proof of fact 345a55d7429fd4b1 (RH2F.layer18); added by fact_submit, do not edit
import MhFact_c3375be11cf311ee
set_option backward.isDefEq.respectTransparency false

/-
  IV7.lean — cyclic 3-edge-cuts of members of 𝒮 (H-ASM (fact fdd83999b9ec10e2) (b) and Lemma L1): a 3-edge-connected
  cubic edge set has at least three edges across every nontrivial cut; a cyclic 3-edge-cut side gives a `Cut3` (the
  ends of the cut edges are distinct); both contractions are again in 𝒮; cyclic sides have odd size at least 3; and a
  member of 𝒮 is c4c iff it has no cyclic 3-edge-cut side.
-/

namespace RH2F
open MGraph
open Classical

section cyc
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `S` is a cyclic 3-edge-cut side: exactly three edges of `P` cross, and both sides contain a cycle of `P` -/
def CycSide (P : Fin X.m → Prop) (S : Fin X.n → Bool) : Prop :=
  ThreeCut P S ∧ HasCycle (inner P S true) ∧ HasCycle (inner P S false)

/-- **three crossing edges**: in a 3-edge-connected cubic edge set, a cut with vertices of `P` on both sides is crossed
    by at least three edges -/
theorem three_cross (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (S : Fin X.n → Bool) {u v : Fin X.n}
    (hu : meets P u) (hSu : S u = true) (hv : meets P v) (hSv : S v = false) :
    3 ≤ cntF X.m (RH2F.Crosses P S) := by
  by_contra hlt
  push_neg at hlt
  rcases cross_cases (P := P) S (by omega) with h0 | ⟨a, ha, hall⟩ | htc
  · obtain ⟨f, hf, hfu⟩ := hu
    obtain ⟨g, hg, hgv⟩ := hv
    have hc := hG.2.1 S (fun e he => by by_contra h'; exact h0 e ⟨he, h'⟩) f g hf hg
    have e1 : S (X.ends f).1 = true := by
      rcases hfu with h | h
      · rw [h]; exact hSu
      · have : S (X.ends f).1 = S (X.ends f).2 := by by_contra h'; exact h0 f ⟨hf, h'⟩
        rw [this, h]; exact hSu
    have e2 : S (X.ends g).1 = false := by
      rcases hgv with h | h
      · rw [h]; exact hSv
      · have : S (X.ends g).1 = S (X.ends g).2 := by by_contra h'; exact h0 g ⟨hg, h'⟩
        rw [this, h]; exact hSv
    rw [e1, e2] at hc; exact Bool.noConfusion hc
  · apply hG.2.2.1 a ha.1
    exact { U := fun w => decide (S w = S (X.ends a).1)
            hu := by simp
            hv := by simp only [decide_eq_false_iff_not]; exact fun h => ha.2 h.symm
            sep := fun g hg hne => by
              have : S (X.ends g).1 = S (X.ends g).2 := by
                by_contra h'; exact hne (hall g ⟨hg, h'⟩)
              simp only [this] }
  · exact h3 S htc

/-- in a cubic edge set, the side of a 3-edge-cut has odd size -/
theorem three_side_odd (hloop : Loopless X) (hcub : CubicOn P) {S : Fin X.n → Bool} (hS : ThreeCut P S) (b : Bool) :
    scount P S b % 2 = 1 := by
  obtain ⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hall⟩ := hS
  have hc : cntF X.m (RH2F.Crosses P S) = 3 := by
    rw [← cntF_triple X.m d12 d13 d23]; apply cntF_congr; intro f
    constructor
    · exact hall f
    · rintro (rfl | rfl | rfl)
      · exact c1
      · exact c2
      · exact c3
  have hh := side_handshake hloop hcub S b
  omega

/-- a 3-edge-cut of a 3-edge-connected cubic edge set is cyclic iff both sides have at least two vertices; then both
    have at least three -/
theorem cycSide_iff (hG : InG X P) {S : Fin X.n → Bool} (hS : ThreeCut P S) :
    CycSide P S ↔ (2 ≤ scount P S true ∧ 2 ≤ scount P S false) := by
  constructor
  · rintro ⟨_, cT, cF⟩
    exact ⟨two_le_side (fun f hf => hf) cT, two_le_side (fun f hf => hf) cF⟩
  · rintro ⟨hT, hF⟩
    have oT := three_side_odd hG.1 hG.2.2.2 hS true
    have oF := three_side_odd hG.1 hG.2.2.2 hS false
    obtain ⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hall⟩ := hS
    have hc : cntF X.m (RH2F.Crosses P S) = 3 := by
      rw [← cntF_triple X.m d12 d13 d23]; apply cntF_congr; intro f
      constructor
      · exact hall f
      · rintro (rfl | rfl | rfl)
        · exact c1
        · exact c2
        · exact c3
    have hn : ∀ b, 3 ≤ scount P S b := by
      intro b; cases b
      · omega
      · omega
    exact ⟨⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hall⟩, both_cyc hG.1 hG.2.2.2 S 3 hc (by decide) hn true,
      both_cyc hG.1 hG.2.2.2 S 3 hc (by decide) hn false⟩

theorem cycSide_three (hG : InG X P) {S : Fin X.n → Bool} (hS : CycSide P S) (b : Bool) : 3 ≤ scount P S b := by
  have h := (cycSide_iff hG hS.1).1 hS
  have hodd := three_side_odd hG.1 hG.2.2.2 hS.1 b
  cases b
  · have := h.2; omega
  · have := h.1; omega

/-- **Lemma L1**: a member of 𝒮 (more generally a 3-edge-connected member of 𝒢) is c4c iff it has no cyclic
    3-edge-cut side -/
theorem c4c_iff_noCyc (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) : C4C X P ↔ ¬ ∃ S, CycSide P S := by
  constructor
  · rintro ⟨_, _, htriv⟩ ⟨S, hS⟩
    have h := (cycSide_iff hG hS.1).1 hS
    rcases htriv S hS.1 with e | e <;> omega
  · intro hno
    refine ⟨hG, h3, fun S hS => ?_⟩
    by_contra hne
    push_neg at hne
    apply hno ⟨S, (cycSide_iff hG hS).2 ⟨?_, ?_⟩⟩
    · obtain ⟨e1, _, _, _, _, _, c1, _⟩ := hS
      have := side_nonempty c1 true; omega
    · obtain ⟨e1, _, _, _, _, _, c1, _⟩ := hS
      have := side_nonempty c1 false; omega

theorem cntF_le_two (n : Nat) (a b : Fin n) : cntF n (fun k => k = a ∨ k = b) ≤ 2 := by
  by_cases hab : a = b
  · subst hab
    have : cntF n (fun k => k = a ∨ k = a) = cntF n (fun k => k = a) := cntF_congr _ _ _ (fun k => ⟨fun h => h.elim id id, Or.inl⟩)
    rw [this, cntF_single]; omega
  · rw [cntF_pair n hab]

/-- **distinct ends**: two distinct edges crossing a cyclic 3-edge-cut side of a 3-edge-connected cubic edge set have
    no common end -/
theorem cut_ends_distinct (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) {S : Fin X.n → Bool} (hS : CycSide P S)
    {e f : Fin X.m} (he : RH2F.Crosses P S e) (hf : RH2F.Crosses P S f) (hef : e ≠ f) {y : Fin X.n}
    (hye : X.Inc e y) (hyf : X.Inc f y) : False := by
  obtain ⟨g, hg, hgy, hge, hgf, hall⟩ := third_edge hG.2.2.2 he.1 hf.1 hye hyf hef
  obtain ⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hcr⟩ := hS.1
  -- the third crossing edge `l`
  obtain ⟨l, hl⟩ : ∃ l, ∀ d, RH2F.Crosses P S d → d = e ∨ d = f ∨ d = l := by
    have hE := hcr e he; have hF := hcr f hf
    rcases hE with rfl | rfl | rfl <;> rcases hF with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hef
      | exact ⟨e3, fun d hd => by rcases hcr d hd with h | h | h <;> simp_all⟩
      | exact ⟨e2, fun d hd => by rcases hcr d hd with h | h | h <;> simp_all⟩
      | exact ⟨e1, fun d hd => by rcases hcr d hd with h | h | h <;> simp_all⟩
  -- the side of `y` without `y`
  let T : Fin X.n → Bool := fun v => decide (S v = S y ∧ v ≠ y)
  have hT : ∀ v, T v = true ↔ (S v = S y ∧ v ≠ y) := fun v => by simp [T]
  -- its crossing edges are among `g` and `l`
  have hcross : ∀ d, RH2F.Crosses P T d → d = g ∨ d = l := by
    rintro d ⟨hd, hne⟩
    by_cases hS' : S (X.ends d).1 = S (X.ends d).2
    · -- both ends on one side of `S`: then `d` is at `y`
      have hy : X.Inc d y := by
        by_contra hny
        apply hne
        have n1 : (X.ends d).1 ≠ y := fun h => hny (Or.inl h)
        have n2 : (X.ends d).2 ≠ y := fun h => hny (Or.inr h)
        simp only [T, hS', n1, n2, ne_eq, not_false_eq_true, and_true]
      rcases hall d hd hy with rfl | rfl | rfl
      · exact absurd hS' he.2
      · exact absurd hS' hf.2
      · exact Or.inl rfl
    · rcases hl d ⟨hd, hS'⟩ with rfl | rfl | rfl
      · -- `e` has ends `y` and one on the other side: it does not cross `T`
        exfalso; apply hne
        obtain ⟨z, hj⟩ := joins_of_inc hye
        have hz : S z ≠ S y := by
          intro h; apply he.2
          rcases hj with h' | h' <;> rw [h'] <;> simp [h]
        have tz : T z = false := by simp [T, hz]
        have ty : T y = false := by simp [T]
        rcases hj with h' | h' <;> rw [h'] <;> simp only [tz, ty]
      · exfalso; apply hne
        obtain ⟨z, hj⟩ := joins_of_inc hyf
        have hz : S z ≠ S y := by
          intro h; apply hf.2
          rcases hj with h' | h' <;> rw [h'] <;> simp [h]
        have tz : T z = false := by simp [T, hz]
        have ty : T y = false := by simp [T]
        rcases hj with h' | h' <;> rw [h'] <;> simp only [tz, ty]
      · exact Or.inr rfl
  have hle : cntF X.m (RH2F.Crosses P T) ≤ 2 :=
    le_trans (cntF_mono _ _ _ hcross) (cntF_le_two X.m g l)
  -- a vertex of `T`, and `y ∉ T`
  obtain ⟨u, ⟨hu, hSu⟩, hne1, _⟩ := cntF_other (cycSide_three hG hS (S y)) y y
  have h3' := three_cross hG h3 T (u := u) (v := y) hu ((hT u).2 ⟨hSu, hne1⟩) ⟨e, he.1, hye⟩ (by simp [T])
  omega

/-- choose among three -/
def sel3 {α : Type} (a b c : α) (i : Fin 3) : α := if i = 0 then a else if i = 1 then b else c

theorem sel3_inj {α : Type} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {i j : Fin 3}
    (h : sel3 a b c i = sel3 a b c j) : i = j := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by rcases i with ⟨i, hi⟩; simp only [Fin.ext_iff]; omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by rcases j with ⟨j, hj⟩; simp only [Fin.ext_iff]; omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp_all [sel3]

/-- **a cyclic 3-edge-cut side of a 3-edge-connected cubic edge set is a `Cut3`** (H-ASM (b), distinctness) -/
theorem cycCut (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) {S : Fin X.n → Bool} (hS : CycSide P S) :
    ∃ C : Cut3 P, C.S = S := by
  obtain ⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hcr⟩ := hS.1
  let e : Fin 3 → Fin X.m := sel3 e1 e2 e3
  have hce : ∀ i, RH2F.Crosses P S (e i) := by
    intro i; simp only [e, sel3]; split_ifs
    · exact c1
    · exact c2
    · exact c3
  have einj : ∀ i j, e i = e j → i = j := fun i j h => sel3_inj d12 d13 d23 h
  refine ⟨{ S := S
            e := e
            y := fun i => endT S (e i)
            w := fun i => endF S (e i)
            hP := fun i => (hce i).1
            hj := fun i => (endTF (hce i)).1
            sy := fun i => (endTF (hce i)).2.1
            sw := fun i => (endTF (hce i)).2.2
            einj := einj
            yinj := fun i j h => by
              by_contra hne
              exact cut_ends_distinct hG h3 hS (hce i) (hce j) (fun h' => hne (einj _ _ h'))
                (joins_inc_left (endTF (hce i)).1) (h ▸ joins_inc_left (endTF (hce j)).1)
            winj := fun i j h => by
              by_contra hne
              exact cut_ends_distinct hG h3 hS (hce i) (hce j) (fun h' => hne (einj _ _ h'))
                (joins_inc_right (endTF (hce i)).1) (h ▸ joins_inc_right (endTF (hce j)).1)
            cut := fun f hf hne => by
              rcases hcr f ⟨hf, hne⟩ with rfl | rfl | rfl
              · exact ⟨0, rfl⟩
              · exact ⟨1, rfl⟩
              · exact ⟨2, rfl⟩ }, rfl⟩

/-- **both contractions are in 𝒮** (H-ASM (b)) -/
theorem cont_inS (hS : InS X P) (C : Cut3 P) : InS (addHub X C.w) C.cont := by
  refine ⟨C.cont_inG hS.1, ?_, fun S hTC => hS.2.2 _ (C.twoCut_lift S hTC)⟩
  intro f g x y hf hg jf jg
  have hn : ∀ a : Fin X.n, (hv C.w a : Fin (addHub X C.w).n) ≠ hub C.w := fun a => hv_ne_hub _ _
  rcases hf with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩ <;> rcases hg with ⟨d', rfl, hd'⟩ | ⟨t', rfl⟩
  · congr 1
    have jd := hub_joins_old (q := C.w) (joins_ends d)
    have jd' := hub_joins_old (q := C.w) (joins_ends d')
    rcases joins_unique jf jd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jg jd' with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hS.2.1 d d' _ _ hd.1 hd'.1 (joins_ends d) (by
        rw [hv_inj _ (e1.symm.trans e3), hv_inj _ (e2.symm.trans e4)]; exact joins_ends d')
    · exact hS.2.1 d d' _ _ hd.1 hd'.1 (joins_ends d) (by
        rw [hv_inj _ (e1.symm.trans e3), hv_inj _ (e2.symm.trans e4)]; exact Or.symm (joins_ends d'))
    · exact hS.2.1 d d' _ _ hd.1 hd'.1 (Or.symm (joins_ends d)) (by
        rw [hv_inj _ (e1.symm.trans e3), hv_inj _ (e2.symm.trans e4)]; exact joins_ends d')
    · exact hS.2.1 d d' _ _ hd.1 hd'.1 (Or.symm (joins_ends d)) (by
        rw [hv_inj _ (e1.symm.trans e3), hv_inj _ (e2.symm.trans e4)]; exact Or.symm (joins_ends d'))
  · exfalso
    have jd := hub_joins_old (q := C.w) (joins_ends d)
    have jt : (addHub X C.w).Joins (hNew C.w t') (hub C.w) (hv C.w (C.w t')) := Or.inl (hub_ends_new C.w t')
    rcases joins_unique jf jd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jg jt with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
  · exfalso
    have jd := hub_joins_old (q := C.w) (joins_ends d')
    have jt : (addHub X C.w).Joins (hNew C.w t) (hub C.w) (hv C.w (C.w t)) := Or.inl (hub_ends_new C.w t)
    rcases joins_unique jg jd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jf jt with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
  · have jt : (addHub X C.w).Joins (hNew C.w t) (hub C.w) (hv C.w (C.w t)) := Or.inl (hub_ends_new C.w t)
    have jt' : (addHub X C.w).Joins (hNew C.w t') (hub C.w) (hv C.w (C.w t')) := Or.inl (hub_ends_new C.w t')
    congr 1
    apply C.winj
    rcases joins_unique jf jt with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jg jt' with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hv_inj _ (e2.symm.trans e4)
    · exact absurd (e3.symm.trans e1) (hn _)
    · exact absurd (e1.symm.trans e3) (hn _)
    · exact hv_inj _ (e1.symm.trans e3)

end cyc


end RH2F


/-
  IV8.lean — Lemma B (1), (3), (4) of H-RED6 (fact 898eb5ab55d140fe): a 3-edge-cut of `Q` with distinct ends (in
  particular a cyclic 3-edge-cut side of a member of 𝒮) induces a 3-edge-cut with distinct ends of `Q^D`: the side `V_S`
  consists of `S` and the new vertices of the edges of `D` with an end in `S`.
-/

namespace RH2F
open MGraph
open Classical

section lemmaB
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

/-- the induced side `V_S` in `digG Y D`: old vertices by `S`, the new vertices of `d` on side `true` iff an end of `d`
    is on side `true` -/
noncomputable def indS (S : Fin Y.n → Bool) (w : Fin (digG Y D).n) : Bool :=
  if h : w.val < Y.n then S ⟨w.val, h⟩
  else (S (Y.ends ⟨(w.val - Y.n) / 2, by have := w.isLt; change w.val < Y.n + 2 * Y.m at this; omega⟩).1 ||
        S (Y.ends ⟨(w.val - Y.n) / 2, by have := w.isLt; change w.val < Y.n + 2 * Y.m at this; omega⟩).2)

theorem indS_dO (S : Fin Y.n → Bool) (x : Fin Y.n) : indS (D := D) S (dO x) = S x := by
  simp [indS, dO, x.isLt]

theorem indS_dU (S : Fin Y.n → Bool) (d : Fin Y.m) : indS (D := D) S (dU d) = (S (Y.ends d).1 || S (Y.ends d).2) := by
  have h : ¬ (dU d : Fin (Y.n + 2 * Y.m)).val < Y.n := by simp only [dU]; omega
  have hd : (⟨((dU d : Fin (Y.n + 2 * Y.m)).val - Y.n) / 2, by have := d.isLt; simp only [dU]; omega⟩ : Fin Y.m) = d :=
    Fin.ext (by simp only [dU]; omega)
  simp only [indS, dif_neg h]
  rw [hd]

theorem indS_dV (S : Fin Y.n → Bool) (d : Fin Y.m) : indS (D := D) S (dV d) = (S (Y.ends d).1 || S (Y.ends d).2) := by
  have h : ¬ (dV d : Fin (Y.n + 2 * Y.m)).val < Y.n := by simp only [dV]; omega
  have hd : (⟨((dV d : Fin (Y.n + 2 * Y.m)).val - Y.n) / 2, by have := d.isLt; simp only [dV]; omega⟩ : Fin Y.m) = d :=
    Fin.ext (by simp only [dV]; omega)
  simp only [indS, dif_neg h]
  rw [hd]

/-- the edge of the path of the cut edge `f` that crosses `V_S` -/
noncomputable def cutE (S : Fin Y.n → Bool) (f : Fin Y.m) : Fin (digG Y D).m :=
  if D f then (if S (Y.ends f).1 = true then eN f 2 else eO f) else eO f

/-- its end in `V_S` -/
noncomputable def cutY (S : Fin Y.n → Bool) (f : Fin Y.m) (y : Fin Y.n) : Fin (digG Y D).n :=
  if D f then (if S (Y.ends f).1 = true then dV f else dU f) else dO y

theorem cutE_joins (S : Fin Y.n → Bool) {f : Fin Y.m} {y w : Fin Y.n} (hj : Y.Joins f y w) (hy : S y = true)
    (hw : S w = false) : (digG Y D).Joins (cutE S f) (cutY S f y) (dO w) := by
  unfold cutE cutY
  by_cases hD : D f
  · rw [if_pos hD, if_pos hD]
    rcases hj with e | e
    · rw [e]; simp only [hy, if_true]
      exact Or.inl (by rw [ends_eN2, e])
    · rw [e]; simp only [hw, Bool.false_eq_true, if_false]
      exact Or.inr (by rw [ends_eO_D hD, e])
  · rw [if_neg hD, if_neg hD]
    rcases hj with e | e
    · exact Or.inl (by rw [ends_eO_nD hD, e])
    · exact Or.inr (by rw [ends_eO_nD hD, e])

theorem cutY_side (S : Fin Y.n → Bool) {f : Fin Y.m} {y w : Fin Y.n} (hj : Y.Joins f y w) (hy : S y = true) :
    indS (D := D) S (cutY S f y) = true := by
  unfold cutY
  by_cases hD : D f
  · rw [if_pos hD]
    have : (S (Y.ends f).1 || S (Y.ends f).2) = true := by
      rcases hj with e | e <;> rw [e] <;> simp [hy]
    split_ifs
    · rw [indS_dV]; exact this
    · rw [indS_dU]; exact this
  · rw [if_neg hD, indS_dO]; exact hy

theorem cutE_set (S : Fin Y.n → Bool) {f : Fin Y.m} (hf : Q f) : digSet Q D (cutE S f) := by
  unfold cutE
  split_ifs with h1 h2
  · exact (set_eN Q f 2).2 ⟨hf, h1⟩
  · exact (set_eO Q f).2 hf
  · exact (set_eO Q f).2 hf

/-- the crossing edges of `V_S` are exactly the crossing edges of the paths of the cut edges -/
theorem indS_cross (S : Fin Y.n → Bool) {e : Fin (digG Y D).m} (he : digSet Q D e)
    (hc : indS S ((digG Y D).ends e).1 ≠ indS S ((digG Y D).ends e).2) :
    ∃ f, Q f ∧ S (Y.ends f).1 ≠ S (Y.ends f).2 ∧ e = cutE S f := by
  rcases dig_cases e with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
  · have hd := (set_eO Q d).1 he
    by_cases hD : D d
    · rw [ends_eO_D hD, indS_dO, indS_dU] at hc
      refine ⟨d, hd, ?_, ?_⟩
      · intro h; apply hc; rw [h]; simp
      · unfold cutE; rw [if_pos hD, if_neg]
        intro h; apply hc; simp [h]
    · rw [ends_eO_nD hD, indS_dO, indS_dO] at hc
      exact ⟨d, hd, hc, by unfold cutE; rw [if_neg hD]⟩
  · obtain ⟨hd, hD⟩ := (set_eN Q d k).1 he
    rcases k_cases k with rfl | hk
    · rw [ends_eN2, indS_dV, indS_dO] at hc
      refine ⟨d, hd, ?_, ?_⟩
      · intro h; apply hc; rw [h]; simp
      · unfold cutE; rw [if_pos hD, if_pos]
        by_contra h
        apply hc
        simp only [Bool.not_eq_true] at h
        simp [h]
    · rw [ends_eN01 d k hk, indS_dU, indS_dV] at hc
      exact absurd rfl hc

/-- **Lemma B (1)**: a 3-edge-cut of `Q` with distinct ends induces one of `Q^D` -/
noncomputable def Cut3.dig (C : Cut3 Q) : Cut3 (digSet Q D) where
  S := indS C.S
  e := fun i => cutE C.S (C.e i)
  y := fun i => cutY C.S (C.e i) (C.y i)
  w := fun i => dO (C.w i)
  hP := fun i => cutE_set C.S (C.hP i)
  hj := fun i => cutE_joins C.S (C.hj i) (C.sy i) (C.sw i)
  sy := fun i => cutY_side C.S (C.hj i) (C.sy i)
  sw := fun i => by rw [indS_dO]; exact C.sw i
  einj := fun i j h => by
    apply C.einj
    unfold cutE at h
    split_ifs at h <;> first
      | exact (eN_inj h).1
      | exact eO_inj h
      | exact absurd h (eO_ne_eN _ _ _)
      | exact absurd h.symm (eO_ne_eN _ _ _)
  yinj := fun i j h => by
    apply C.einj
    unfold cutY at h
    split_ifs at h <;> first
      | exact dV_inj h
      | exact dU_inj h
      | exact absurd h (dU_ne_dV _ _)
      | exact absurd h.symm (dU_ne_dV _ _)
      | exact absurd h.symm (dO_ne_dU _ _)
      | exact absurd h (dO_ne_dU _ _)
      | exact absurd h.symm (dO_ne_dV _ _)
      | exact absurd h (dO_ne_dV _ _)
      | (exact congrArg C.e (C.yinj _ _ (dO_inj h)))
  winj := fun i j h => C.winj _ _ (dO_inj h)
  cut := fun e he hc => by
    obtain ⟨f, hf, hfc, rfl⟩ := indS_cross C.S he hc
    obtain ⟨i, rfl⟩ := C.cut f hf hfc
    exact ⟨i, rfl⟩

end lemmaB

end RH2F


/-
  IV9.lean — the Lean statement of the closing set CS2′ of the root (ROOT-CS2 f8958e836f66d686 with (II_D) of II-RED2
  52408ddd08d61ae6 in place of (II)): the far-exchange engine hypotheses (FE-EXT-D)₁₀ and (FE-EXIST-D)₁₀ on digon
  insertions of c4c hosts, (POLE), the existential T1 property (T1′-TRI) at triangles carrying one digon, and (II_D);
  Corollary H-RED8 (2) (fact d2f6b988c49c84f6); and the composition, with H-RED13 (c) (fact da66a84c773b73b3) as a named
  hypothesis.
-/

namespace RH2F
open MGraph
open Classical

section cs2
variable {X : MGraph}

/-- two edges meet: they share an endpoint (parallel edges meet) -/
def Meet (a b : Fin X.m) : Prop := ∃ x, X.Inc a x ∧ X.Inc b x

/-- the distance of the edges `p`, `p'` of `P` is at least 3: no path with at most two edges of `P` joins an endpoint of
    `p` to an endpoint of `p'` -/
def Dist3 (P : Fin X.m → Prop) (p p' : Fin X.m) : Prop :=
  ∀ a b, X.Inc p a → X.Inc p' b → a ≠ b ∧ (¬ ∃ e, P e ∧ X.Joins e a b) ∧
    ¬ ∃ e1 e2 z, P e1 ∧ P e2 ∧ X.Joins e1 a z ∧ X.Joins e2 z b

/-- `C` is a far-exchange set for the perfect matching `M` of `P` (conditions (a), (b′), (c) of fact
    898eb5ab55d140fe) -/
def FarEx (P M C : Fin X.m → Prop) : Prop :=
  (∀ f, C f → P f ∧ ¬ M f) ∧
  -- (a) every edge of `M` meets at most one edge of `C`
  (∀ p c1 c2, M p → C c1 → C c2 → Meet p c1 → Meet p c2 → c1 = c2) ∧
  -- (b′) no edge of `P ∖ (M ∪ C)` parallel to no edge of `C` has both endpoints on edges of `C`
  (∀ e, P e → ¬ M e → ¬ C e → (¬ ∃ c, C c ∧ X.Joins c (X.ends e).1 (X.ends e).2) →
    ¬ ((∃ c, C c ∧ X.Inc c (X.ends e).1) ∧ ∃ c, C c ∧ X.Inc c (X.ends e).2)) ∧
  -- (c) two distinct edges of `M` meeting no edge of `C` are at distance at least 3
  (∀ p p', M p → M p' → p ≠ p' → (∀ c, C c → ¬ Meet p c) → (∀ c, C c → ¬ Meet p' c) → Dist3 P p p')

/-- the c4c simple cubic host `Q` has at least 10 vertices and `|V(Q)| + 2|D| ≥ 16` -/
def Host10 (Y : MGraph) (Q D : Fin Y.m → Prop) : Prop :=
  C4C Y Q ∧ SimpleP Q ∧ 10 ≤ vcount Q ∧ 16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d)

/-- (KD≥16)₁₀: `Q^D` is EX1-good for every such host -/
def KD16_10 : Prop := ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Host10 Y Q D → EX1On (digSet Q D)

/-- (FE-EXT-D)₁₀: every far-exchange structure on `X := Q^D` extends to a star 6-colouring with colour classes `6 = M`
    and `5 = C` (colours `5`, `4` here) -/
def FEEXTD10 : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Host10 Y Q D → ∀ M C, PMOn (digSet Q D) M → FarEx (digSet Q D) M C →
    ∃ c, StarOn (digSet Q D) 6 c ∧ ∀ f, digSet Q D f → ((M f ↔ c f = 5) ∧ (C f ↔ c f = 4))

/-- (FE-EXIST-D)₁₀: every edge and status is attained by a perfect matching with a far-exchange set -/
def FEEXISTD10 : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Host10 Y Q D → ∀ g, digSet Q D g → ∀ t : Bool,
    ∃ M, PMOn (digSet Q D) M ∧ (M g ↔ t = true) ∧ ∃ C, FarEx (digSet Q D) M C

/-- **Corollary H-RED8 (2)**: (FE-EXT-D)₁₀ ∧ (FE-EXIST-D)₁₀ implies (KD≥16)₁₀ -/
theorem hred8_2 (hext : FEEXTD10) (hex : FEEXISTD10) : KD16_10 := by
  intro Y Q D hH g hg t _
  obtain ⟨M, hM, hst, C, hC⟩ := hex Y Q D hH g hg t
  obtain ⟨c, hc, hcl⟩ := hext Y Q D hH M C hM hC
  exact ⟨M, hM, hst, c, hc, ⟨5, fun f hf => (hcl f hf).1⟩⟩

/-- (T1′) for the contraction `C.cont` of side `A` of a 3-edge-cut `C` of `R`, at its hub and port `i`: for every edge
    `g` not at the hub and every status `t` attained by a perfect matching containing the hub edge `z w_i`, some MC
    colouring `c` has `c(z w_i) = 6`, `[c(g) = 6] = t`, and not `t_j = t_k = ζ`. Here `j, k` are the other two ports,
    `t_j` is the colour of the edge at `w_j` other than `z w_j` not of colour 6, and `ζ` is the colour outside
    `{a_j, a_k} ∪ Π` (`a = c(z w)`, `Π` the colours of the other two edges at `w_i`) other than 6 -/
def T1p {R : Fin X.m → Prop} (C : Cut3 R) (i : Fin 3) : Prop :=
  ∀ g, C.cont g → ¬ (addHub X C.w).Inc g (hub C.w) → ∀ t : Bool,
    (∃ N, PMOn C.cont N ∧ N (hNew C.w i) ∧ (N g ↔ t = true)) →
    ∃ c, MCol C.cont c ∧ c (hNew C.w i) = 5 ∧ (c g = 5 ↔ t = true) ∧
      ¬ ∃ (j k : Fin 3) (h2 h3 : Fin (addHub X C.w).m), j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
        C.cont h2 ∧ (addHub X C.w).Inc h2 (hv C.w (C.w j)) ∧ h2 ≠ hNew C.w j ∧ c h2 ≠ 5 ∧
        C.cont h3 ∧ (addHub X C.w).Inc h3 (hv C.w (C.w k)) ∧ h3 ≠ hNew C.w k ∧ c h3 ≠ 5 ∧
        c h2 = c h3 ∧ c h2 ≠ c (hNew C.w j) ∧ c h2 ≠ c (hNew C.w k) ∧
        ∀ h1, C.cont h1 → (addHub X C.w).Inc h1 (hv C.w (C.w i)) → h1 ≠ hNew C.w i → c h1 ≠ c h2

/-- (T1′-TRI): for every `Q ∈ 𝒮` that is not c4c, every cyclic 3-edge-cut side `S` of `Q` with 3 vertices (a Cut3 `C`
    with side `A = S`), every `D` with `|V(Q)| + 2|D| ≥ 16` whose only edge incident with `S` is one edge `δ` inside `S`
    not at `y_i`, (T1′) holds for `X_T := (Q^D)/V_S` at port `i` -/
def T1TRI : Prop :=
  ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → ¬ C4C Y Q → ∀ (C : Cut3 Q), CycSide Q C.S → scount Q C.S true = 3 →
    ∀ (D : Fin Y.m → Prop), 16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) →
    ∀ (i : Fin 3) (δ : Fin Y.m), Q δ → D δ → C.S (Y.ends δ).1 = true → C.S (Y.ends δ).2 = true →
      ¬ Y.Inc δ (C.y i) → (∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = δ) →
      T1p (Cut3.dig (D := D) C) i

/-- H-RED13 (c) (fact da66a84c773b73b3), as a named statement -/
def HRED13c : Prop := KD16_10 → POLE → T1TRI → Hyp

/-- **the closing set CS2′**: under H-RED13 (c), (FE-EXT-D)₁₀ ∧ (FE-EXIST-D)₁₀ ∧ (POLE) ∧ (T1′-TRI) ∧ (II_D) imply DMS -/
theorem cs2p (h13 : HRED13c) (hext : FEEXTD10) (hex : FEEXISTD10) (hpole : POLE) (ht1 : T1TRI) (hD : IID) : DMS :=
  dms_of_H_IID (h13 (hred8_2 hext hex) hpole ht1) hD

end cs2

end RH2F

namespace RH2F
open MGraph

/-- **Layer 18 of the Lean formalization**: cyclic 3-edge-cuts of 3-edge-connected cubic multigraphs (H-ASM (b), first
    part, and Lemma L1 of fact fdd83999b9ec10e2); Lemma B (1) of fact 898eb5ab55d140fe (a 3-edge-cut with distinct ends
    of `Q` induces one of `Q^D`); Corollary H-RED8 (2) of fact d2f6b988c49c84f6; and the closing set CS2′ of the root
    with H-RED13 (c) of fact da66a84c773b73b3 as a named hypothesis. -/
theorem layer18 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (S : Fin X.n → Bool), InG X P → (∀ S, ¬ TwoCut P S) → CycSide P S →
      ∃ C : Cut3 P, C.S = S) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (S : Fin X.n → Bool) (b : Bool), InG X P → CycSide P S →
      3 ≤ scount P S b ∧ scount P S b % 2 = 1) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → (∀ S, ¬ TwoCut P S) → (C4C X P ↔ ¬ ∃ S, CycSide P S)) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P), InS X P → InS (addHub X C.w) C.cont) ∧
    (∀ (Y : MGraph) (Q D : Fin Y.m → Prop) (C : Cut3 Q), ∃ C' : Cut3 (digSet Q D), C'.S = indS C.S ∧
      ∀ i, C'.w i = dO (C.w i)) ∧
    (FEEXTD10 → FEEXISTD10 → KD16_10) ∧
    (HRED13c → FEEXTD10 → FEEXISTD10 → POLE → T1TRI → IID → DMS) :=
  ⟨fun _ _ _ hG h3 hS => cycCut hG h3 hS,
   fun _ _ _ b hG hS => ⟨cycSide_three hG hS b, three_side_odd hG.1 hG.2.2.2 hS.1 b⟩,
   fun _ _ hG h3 => c4c_iff_noCyc hG h3, fun _ _ C hS => cont_inS hS C,
   fun _ _ D C => ⟨Cut3.dig (D := D) C, rfl, fun _ => rfl⟩, hred8_2, cs2p⟩

end RH2F
