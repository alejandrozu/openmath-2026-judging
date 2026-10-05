-- Lean proof of fact 90b4662cdeba097d (RH2F.layer12); added by fact_submit, do not edit
import MhFact_a030b9ec722eb795
set_option backward.isDefEq.respectTransparency false

-- ===== from II4.lean (part 2) =====
namespace RH2F
open MGraph
open Classical

section ii4
variable {X : MGraph} {P : Fin X.m → Prop}

/-- every side with at least 4 vertices is 2-sided, under (H) -/
theorem Cut2.twoSided_all (hH : Hyp) (C : Cut2 P) (hG : InG X P) (h4 : 4 ≤ scount P C.S true) :
    C.TwoSided := by
  by_cases h8 : scount P C.S true ≤ 8
  · exact C.small2sided hG h4 h8
  · have hev := C.side_even RH2P.pstat hG
    have h10 : 10 ≤ vcount C.clo := by rw [C.vcount_clo]; omega
    have hex := ex1red RH2P.pstat smallFacts hH _ _ (C.clo_inG hG) h10
    exact C.twoSided_of_ex1 RH2P.pstat hG (C.flip.m1 hG (by rw [scount_flip]; exact h4)) hex

/-- hypothesis (II_D) of II-RED2: the leaf case for 2-cut-reduced hosts on at least 6 vertices, with `g` in no digon
    and in no 2-edge-cut -/
def IID : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 6 ≤ vcount P → TwoCutReducedOn P → ∀ g, P g →
    (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) → (∀ S, TwoCut P S → ¬ Crosses P S g) →
    Colourable (leafSet P g) 6

/-- (II) for connected hosts -/
def IIc : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → ∀ g, P g → Colourable (leafSet P g) 6

/-- a second edge parallel to `g` gives the 2-edge-cut side `V ∖ {s, t}` -/
theorem digon_cut (hG : InG X P) (h4 : 4 ≤ vcount P) {g h : Fin X.m} (hg : P g) (hh : P h) (hne : h ≠ g)
    (hj : X.Joins h (X.ends g).1 (X.ends g).2) :
    ∃ S, TwoCut P S ∧ S (X.ends g).1 = false ∧ scount P S true + 2 = vcount P := by
  obtain ⟨D, hu, hv⟩ := digData_of hG h4 hg hh (joins_ends g) hj (Ne.symm hne)
  let S : Fin X.n → Bool := fun w => !(decide (w = D.u) || decide (w = D.v))
  have Su : S D.u = false := by simp [S]
  have Sv : S D.v = false := by simp [S]
  have Sx : S D.x = true := by simp [S, D.hxu, D.hxv]
  have Sy : S D.y = true := by simp [S, D.hyu, D.hyv]
  have Sw : ∀ w, S w = false ↔ (w = D.u ∨ w = D.v) := fun w => by
    simp only [S, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq]
  -- the crossing edges are `gu` and `gv`
  have cr : ∀ e, Crosses P S e → e = D.gu ∨ e = D.gv := by
    rintro e ⟨he, hS⟩
    by_cases h1 : S (X.ends e).1 = false
    · rcases (Sw _).1 h1 with h' | h'
      · rcases D.covu e he (Or.inl h') with rfl | rfl | rfl
        · exfalso; apply hS; rcases D.j1 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exfalso; apply hS; rcases D.j2 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exact Or.inl rfl
      · rcases D.covv e he (Or.inl h') with rfl | rfl | rfl
        · exfalso; apply hS; rcases D.j1 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exfalso; apply hS; rcases D.j2 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exact Or.inr rfl
    · have h2 : S (X.ends e).2 = false := by
        cases h' : S (X.ends e).2
        · rfl
        · exfalso; apply hS; rw [h']; cases h'' : S (X.ends e).1 <;> simp_all
      rcases (Sw _).1 h2 with h' | h'
      · rcases D.covu e he (Or.inr h') with rfl | rfl | rfl
        · exfalso; apply hS; rcases D.j1 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exfalso; apply hS; rcases D.j2 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exact Or.inl rfl
      · rcases D.covv e he (Or.inr h') with rfl | rfl | rfl
        · exfalso; apply hS; rcases D.j1 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exfalso; apply hS; rcases D.j2 with h'' | h'' <;> rw [h''] <;> simp [Su, Sv]
        · exact Or.inr rfl
  have cgu : Crosses P S D.gu := ⟨D.hgu, by rcases D.ju with h' | h' <;> rw [h'] <;> simp [Su, Sx]⟩
  have cgv : Crosses P S D.gv := ⟨D.hgv, by rcases D.jv with h' | h' <;> rw [h'] <;> simp [Sv, Sy]⟩
  have gne : D.gu ≠ D.gv := by
    intro h'
    have hgu := D.ju
    rw [h'] at hgu
    rcases joins_unique hgu D.jv with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact D.huv h1
    · exact D.hyu h1.symm
  refine ⟨S, ⟨D.gu, D.gv, gne, cgu, cgv, cr⟩, by rw [← hu]; exact Su, ?_⟩
  have hsplit := vcount_split P S
  have hm : ∀ w, (meets P w ∧ S w = false) ↔ (w = D.u ∨ w = D.v) := fun w =>
    ⟨fun h' => (Sw w).1 h'.2, fun h' => ⟨by
      rcases h' with rfl | rfl
      · exact ⟨D.d1, D.hd1, joins_inc_left D.j1⟩
      · exact ⟨D.d1, D.hd1, joins_inc_right D.j1⟩, (Sw w).2 h'⟩⟩
  have hfalse : scount P S false = 2 := by
    unfold scount
    rw [cntF_congr X.n _ _ hm]
    exact cntF_pair X.n D.huv
  omega

/-- **Theorem II-RED2** (fact 52408ddd08d61ae6), for connected hosts: (H) and (II_D) imply (II) for every connected
    bridgeless loopless cubic multigraph -/
theorem iic_of (hH : Hyp) (hD : IID) : IIc := by
  suffices h : ∀ n, ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P = n → ∀ g, P g →
      Colourable (leafSet P g) 6 from fun X P hG g hg => h _ X P hG rfl g hg
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro X P hG hn g hg
  have hpos : 0 < vcount P := cntF_le_of_mem _ _ (i := (X.ends g).1) ⟨g, hg, Or.inl rfl⟩
  by_cases hsmall : n ≤ 4
  · exact step2 hG hpos (by omega) hg
  have hev := vcount_even RH2P.pstat hG
  -- Step 3: a reducible 2-edge-cut
  by_cases hred : ∃ S, TwoCut P S ∧ ¬ (S (X.ends g).1 = true ∧ S (X.ends g).2 = true) ∧ 4 ≤ scount P S true
  · obtain ⟨S, hS, hgS, h4⟩ := hred
    obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS
    have hts := C.twoSided_all hH hG h4
    have hsplit := vcount_split P C.S
    have hvB : vcount C.flip.clo < n := by rw [C.flip.vcount_clo, scount_flip]; simp; omega
    rcases C.cases_P hg with hA | hB | hcut
    · exact absurd ⟨hA.2.1, hA.2.2⟩ hgS
    · exact C.leaf_glue_B hG.1 hG.2.2.2 hB hts
        (ih _ hvB _ _ (C.flip.clo_inG hG) rfl _ (Or.inr ⟨g, rfl, hB⟩))
    · rcases hcut with rfl | rfl
      · exact C.leaf_glue_E hG.1 hG.2.2.2 hts (ih _ hvB _ _ (C.flip.clo_inG hG) rfl _ (Or.inl rfl))
      · have hvB' : vcount C.swap12.flip.clo < n := by
          rw [C.swap12.flip.vcount_clo, scount_flip]; simp; exact (by rw [C.flip.vcount_clo, scount_flip] at hvB; first | simpa using hvB | exact hvB | (simp at hvB; exact hvB))
        exact C.swap12.leaf_glue_E hG.1 hG.2.2.2 (C.swap12_twoSided hts)
          (ih _ hvB' _ _ (C.swap12.flip.clo_inG hG) rfl _ (Or.inl rfl))
  -- Step 4: every 2-edge-cut side not containing `g` has 2 vertices
  have hnot : ∀ S, TwoCut P S → ¬ (S (X.ends g).1 = true ∧ S (X.ends g).2 = true) → scount P S true = 2 := by
    intro S hS hgS
    have h1 : scount P S true < 4 := by
      apply Classical.byContradiction; intro h; exact hred ⟨S, hS, hgS, by omega⟩
    have := twoCut_even RH2P.pstat hG hS
    have := twoCut_pos hG hS true
    omega
  have hn6 : 6 ≤ vcount P := by omega
  apply hD X P hG hn6
  · -- (a) 2-cut-reduced
    intro S hS
    by_cases hin : S (X.ends g).1 = true ∧ S (X.ends g).2 = true
    · obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS
      have h2 := hnot C.flip.S C.flip.twoCut_self (by rw [Cut2.flip_S, Cut2.flip_S, hin.1, hin.2]; simp)
      rw [scount_flip] at h2
      exact Or.inr h2
    · exact Or.inl (hnot S hS hin)
  · exact hg
  · -- (b) no edge parallel to `g`
    intro h hh hne hj
    obtain ⟨S, hS, hSs, hcount⟩ := digon_cut hG (by omega) hg hh hne hj
    have := hnot S hS (fun h' => by rw [hSs] at h'; exact absurd h'.1 (by decide))
    omega
  · -- (c) `g` in no 2-edge-cut
    intro S hS hcr
    obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS
    have hd := hcr.2
    have h1 := hnot C.S hS (fun h' => hd (h'.1.trans h'.2.symm))
    have h2 := hnot C.flip.S C.flip.twoCut_self (fun h' => by
      rw [Cut2.flip_S, Cut2.flip_S] at h'
      exact hd (by cases h1' : C.S (X.ends g).1 <;> cases h2' : C.S (X.ends g).2 <;> simp_all))
    rw [scount_flip] at h2
    have := vcount_split P C.S
    simp at h2
    omega

/-- (II) for connected hosts gives the suppression form `DMS_II` (as `iiToDMSII`, fact 341b6e5e1be16205) -/
theorem iiToDMSII_c (hII : IIc) : DmsIILean.DMS_II := by
  intro G Q S _ hloop huw hC hB hK _
  have hXl : Loopless (addEdge G S.u S.w) := by
    intro f
    by_cases h : f.val < G.m
    · have := hloop ⟨f.val, h⟩
      simpa [addEdge, h] using this
    · simp [addEdge, h]; exact huw
  obtain ⟨c', hc'⟩ := hII (addEdge G S.u S.w) (supp Q S.y S.u S.w) ⟨hXl, hC, hB, hK⟩ (Fin.last G.m) (Or.inl rfl)
  exact ⟨fun a => c' (psiT S a), starOn_embed (phiT S) (psiT S)
    (fun x y _ _ _ _ _ _ h => phiT_inj S x y h) (fun a b ha hb h => psiT_inj S a b ha hb h)
    (fun a ha => psiT_set S a ha) (fun a ha => psiT_joins S hloop a ha) hc'⟩

/-- **(H) and (II_D) imply DMS** (II-RED2 with RH2): every loopless multigraph of maximum degree at most 3 is star
    6-edge-colourable -/
theorem dms_of_H_IID (hH : Hyp) (hD : IID) : DMS :=
  DmsIILean.dms_of_I_II (dmsI_of_parts RH2P.pstat smallFacts b8s hH) (iiToDMSII_c (iic_of hH hD))

end ii4

end RH2F

-- ===== from II5.lean =====
/-
  II5.lean — Step 1 of Theorem II-RED2 (fact 52408ddd08d61ae6): components.  The connected component of a vertex,
  (I) for all bridgeless loopless cubic multigraphs, and (H) ∧ (II_D) ⟹ (II) in full.
-/

namespace RH2F
open MGraph
open Classical

section ii5
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `v` lies in the component of `s`: every vertex set containing `s` and closed along the edges of `P` contains `v` -/
def Reach (P : Fin X.m → Prop) (s v : Fin X.n) : Prop :=
  ∀ T : Fin X.n → Prop, T s → (∀ f, P f → (T (X.ends f).1 ↔ T (X.ends f).2)) → T v

theorem reach_self (s : Fin X.n) : Reach P s s := fun _ h _ => h

theorem reach_edge {s : Fin X.n} {f : Fin X.m} (hf : P f) : Reach P s (X.ends f).1 ↔ Reach P s (X.ends f).2 :=
  ⟨fun h T hs hc => (hc f hf).1 (h T hs hc), fun h T hs hc => (hc f hf).2 (h T hs hc)⟩

theorem reach_inc {s : Fin X.n} {f : Fin X.m} (hf : P f) {x : Fin X.n} (hx : X.Inc f x) :
    Reach P s x ↔ Reach P s (X.ends f).1 := by
  rcases hx with rfl | rfl
  · exact Iff.rfl
  · exact (reach_edge hf).symm

/-- the edges of the component of `s` -/
def compK (P : Fin X.m → Prop) (s : Fin X.n) : Fin X.m → Prop := fun f => P f ∧ Reach P s (X.ends f).1
/-- the edges outside the component of `s` -/
def compR (P : Fin X.m → Prop) (s : Fin X.n) : Fin X.m → Prop := fun f => P f ∧ ¬ Reach P s (X.ends f).1

theorem compK_connected (s : Fin X.n) : ConnectedOn (compK P s) := by
  intro U hU f g hf hg
  have key : ∀ v, Reach P s v → U v = U s := by
    intro v hv
    refine hv (fun w => Reach P s w → U w = U s) (fun _ => rfl) ?_ hv
    intro e he
    by_cases hr : Reach P s (X.ends e).1
    · have hr2 := (reach_edge he).1 hr
      have hUe := hU e ⟨he, hr⟩
      constructor
      · intro h1 _; rw [← hUe]; exact h1 hr
      · intro h2 _; rw [hUe]; exact h2 hr2
    · have hr2 : ¬ Reach P s (X.ends e).2 := fun h => hr ((reach_edge he).2 h)
      exact ⟨fun _ h => absurd h hr2, fun _ h => absurd h hr⟩
  rw [key _ hf.2, key _ hg.2]

/-- a cut of the component (or of the rest) is a cut of `P` -/
theorem cut_of_part (hB : BridgelessOn P) (s : Fin X.n) (b : Prop) {Q : Fin X.m → Prop}
    (hQ : ∀ f, Q f ↔ P f ∧ (Reach P s (X.ends f).1 ↔ b)) : BridgelessOn Q := by
  intro e he B
  have heP := ((hQ e).1 he).1
  have heb := ((hQ e).1 he).2
  apply hB e heP
  refine ⟨fun v => if (Reach P s v ↔ b) then B.U v else B.U (X.ends e).2, ?_, ?_, ?_⟩
  · simp only [if_pos heb]; exact B.hu
  · have : (Reach P s (X.ends e).2 ↔ b) := ((reach_edge heP).symm.trans heb)
    simp only [if_pos this]; exact B.hv
  · intro f hf hfe
    have h12 := reach_edge (s := s) hf
    by_cases hb : (Reach P s (X.ends f).1 ↔ b)
    · have hb2 : (Reach P s (X.ends f).2 ↔ b) := h12.symm.trans hb
      simp only [if_pos hb, if_pos hb2]
      exact B.sep f ((hQ f).2 ⟨hf, hb⟩) hfe
    · have hb2 : ¬ (Reach P s (X.ends f).2 ↔ b) := fun h => hb (h12.trans h)
      simp only [if_neg hb, if_neg hb2]

theorem cubic_of_part (hK : CubicOn P) (s : Fin X.n) (b : Prop) {Q : Fin X.m → Prop}
    (hQ : ∀ f, Q f ↔ P f ∧ (Reach P s (X.ends f).1 ↔ b)) : CubicOn Q := by
  rintro x ⟨f0, hf0, hx0⟩
  have hP0 := ((hQ f0).1 hf0).1
  have hbx : (Reach P s x ↔ b) := (reach_inc hP0 hx0).trans ((hQ f0).1 hf0).2
  obtain ⟨a, b', c, ha, hb, hc, ia, ib, ic, dab, dac, dbc, hall⟩ := hK x ⟨f0, hP0, hx0⟩
  have inQ : ∀ d, P d → X.Inc d x → Q d := fun d hd hdx =>
    (hQ d).2 ⟨hd, (reach_inc hd hdx).symm.trans hbx⟩
  exact ⟨a, b', c, inQ a ha ia, inQ b' hb ib, inQ c hc ic, ia, ib, ic, dab, dac, dbc,
    fun d hd hdx => hall d ((hQ d).1 hd).1 hdx⟩

theorem compK_iff (s : Fin X.n) (f : Fin X.m) : compK P s f ↔ P f ∧ (Reach P s (X.ends f).1 ↔ True) := by
  simp [compK]
theorem compR_iff (s : Fin X.n) (f : Fin X.m) : compR P s f ↔ P f ∧ (Reach P s (X.ends f).1 ↔ False) := by
  simp [compR]

/-- the rest has fewer vertices -/
theorem vcount_compR (s : Fin X.n) (hs : meets P s) : vcount (compR P s) < vcount P := by
  unfold vcount
  have hsplit := cntF_split X.n (meets P) (fun v => Reach P s v)
  have h1 : 1 ≤ cntF X.n (fun v => meets P v ∧ Reach P s v) := cntF_le_of_mem _ _ ⟨hs, reach_self s⟩
  have h2 : cntF X.n (meets (compR P s)) = cntF X.n (fun v => meets P v ∧ ¬ Reach P s v) := by
    apply cntF_congr
    intro v
    constructor
    · rintro ⟨f, ⟨hf, hr⟩, hfv⟩
      exact ⟨⟨f, hf, hfv⟩, fun h => hr ((reach_inc hf hfv).1 h)⟩
    · rintro ⟨⟨f, hf, hfv⟩, hr⟩
      exact ⟨f, ⟨hf, fun h => hr ((reach_inc hf hfv).2 h)⟩, hfv⟩
  omega

theorem edge_side {s : Fin X.n} {a b : Fin X.m} {x : Fin X.n} (ha : P a) (hb : P b) (hax : X.Inc a x)
    (hbx : X.Inc b x) : decide (Reach P s (X.ends a).1) = decide (Reach P s (X.ends b).1) := by
  rw [decide_eq_decide]
  exact (reach_inc ha hax).symm.trans (reach_inc hb hbx)

theorem colourable_congr {Q Q' : Fin X.m → Prop} (h : ∀ f, Q f ↔ Q' f) (hc : Colourable Q 6) :
    Colourable Q' 6 := by
  have : Q = Q' := funext fun f => propext (h f)
  rw [← this]; exact hc

/-- **(I) for all bridgeless loopless cubic multigraphs**, under (H) -/
theorem dmsI_all (hH : Hyp) : ∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → BridgelessOn P → CubicOn P →
    Colourable P 6 := by
  suffices h : ∀ n, ∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → BridgelessOn P → CubicOn P → vcount P = n →
      Colourable P 6 from fun X P hL hB hK => h _ X P hL hB hK rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro X P hL hB hK hn
  by_cases hne : ∃ g, P g
  · obtain ⟨g, hg⟩ := hne
    let s := (X.ends g).1
    have hs : meets P s := ⟨g, hg, Or.inl rfl⟩
    -- the component of `s`
    have hGK : InG X (compK P s) := ⟨hL, compK_connected s, cut_of_part hB s True (compK_iff s),
      cubic_of_part hK s True (compK_iff s)⟩
    have hcK : Colourable (compK P s) 6 := by
      by_cases h10 : 10 ≤ vcount (compK P s)
      · have hex := ex1red RH2P.pstat smallFacts hH _ _ hGK h10
        have hgK : compK P s g := ⟨hg, reach_self s⟩
        obtain ⟨_, _, _, c, hc, _⟩ := hex g hgK true (RH2P.pstat _ _ hGK g hgK true)
        exact ⟨c, hc⟩
      · have := vcount_even RH2P.pstat hGK
        exact b8s _ _ hGK (by omega)
    have hcR : Colourable (compR P s) 6 :=
      ih _ (by rw [← hn]; exact vcount_compR s hs) X _ hL (cut_of_part hB s False (compR_iff s))
        (cubic_of_part hK s False (compR_iff s)) rfl
    apply colourable_of_sides (fun f => decide (Reach P s (X.ends f).1))
      (fun a b x ha hb _ hax hbx => edge_side ha hb hax hbx)
    · exact colourable_congr (fun f => by simp [compK]) hcK
    · exact colourable_congr (fun f => by simp [compR]) hcR
  · exact ⟨fun _ => 0, fun a _ _ ha _ => absurd ⟨a, ha⟩ hne, fun w h1 _ _ _ => absurd ⟨w.e1, h1⟩ hne⟩


/-- **Theorem II-RED2** (fact 52408ddd08d61ae6): (H) and (II_D) imply (II) -/
theorem ii_of (hH : Hyp) (hD : IID) : II := by
  intro X P hL hB hK g hg
  let s := (X.ends g).1
  have hgK : compK P s g := ⟨hg, reach_self s⟩
  have hGK : InG X (compK P s) := ⟨hL, compK_connected s, cut_of_part hB s True (compK_iff s),
    cubic_of_part hK s True (compK_iff s)⟩
  have hcK : Colourable (leafSet (compK P s) g) 6 := iic_of hH hD X _ hGK g hgK
  have hcR : Colourable (compR P s) 6 :=
    dmsI_all hH X _ hL (cut_of_part hB s False (compR_iff s)) (cubic_of_part hK s False (compR_iff s))
  have hst : Reach P s (X.ends g).2 := (reach_edge hg).1 (reach_self s)
  let sd : Fin (leafG X g).m → Bool := fun f =>
    if h : f.val < X.m then decide (Reach P s (X.ends ⟨f.val, h⟩).1) else true
  have sd_old : ∀ d, sd (oldE g d) = decide (Reach P s (X.ends d).1) := fun d => by
    simp only [sd, oldE, d.isLt, dif_pos]
  have sd_new : ∀ i (hi : i < 3), sd (newE g i hi) = true := fun i hi => by
    simp only [sd, newE]; simp
  -- the side of an edge is read off at any of its ends
  let vs : Fin (leafG X g).n → Bool := fun v => if h : v.val < X.n then decide (Reach P s ⟨v.val, h⟩) else true
  have vs_lv : ∀ w, vs (lv w) = decide (Reach P s w) := fun w => by
    simp only [vs, lv_val, w.isLt, dif_pos]; try rfl
  have vs_vx : vs (vx X) = true := by simp only [vs, vx_val]; simp
  have vs_vl : vs (vl X) = true := by simp only [vs, vl_val]; simp
  have claim : ∀ c x, leafSet P g c → (leafG X g).Inc c x → sd c = vs x := by
    intro c x hc hcx
    rcases leaf_cases g c with ⟨d, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨w, rfl, hw⟩ := inc_old_lv hcx
      rw [sd_old, vs_lv, decide_eq_decide]
      exact (reach_inc ((set_old P g d).1 hc).1 hw).symm
    · unfold Inc at hcx; rw [ends_new0] at hcx
      rw [sd_new]
      rcases hcx with h | h <;> rw [← h]
      · show true = vs (lv (X.ends g).1); rw [vs_lv]; exact (decide_eq_true (reach_self s)).symm
      · exact vs_vx.symm
    · unfold Inc at hcx; rw [ends_new1] at hcx
      rw [sd_new]
      rcases hcx with h | h <;> rw [← h]
      · exact vs_vx.symm
      · show true = vs (lv (X.ends g).2); rw [vs_lv]; exact (decide_eq_true hst).symm
    · unfold Inc at hcx; rw [ends_new2] at hcx
      rw [sd_new]
      rcases hcx with h | h <;> rw [← h]
      · exact vs_vx.symm
      · exact vs_vl.symm
  apply colourable_of_sides sd
  · intro a b x ha hb _ hax hbx
    rw [claim a x ha hax, claim b x hb hbx]
  · refine colourable_congr (fun f => ?_) hcK
    rcases leaf_cases g f with ⟨d, rfl⟩ | rfl | rfl | rfl
    · rw [set_old, set_old, sd_old]; simp [compK]; tauto
    all_goals simp [set_new, sd_new]
  · refine colourable_emb (X := X) (P := compR P s) (Y := leafG X g) (rhoL s) (muL g) ?_ ?_ ?_ ?_ hcR
    · rintro x y ⟨a, ⟨ha, hsa⟩, hax⟩ ⟨b, ⟨hb, hsb⟩, hby⟩ h
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl <;> try simp [sd_new] at hsa
      rcases leaf_cases g b with ⟨d', rfl⟩ | rfl | rfl | rfl <;> try simp [sd_new] at hsb
      obtain ⟨u, rfl, _⟩ := inc_old_lv hax
      obtain ⟨u', rfl, _⟩ := inc_old_lv hby
      rw [rhoL_lv, rhoL_lv] at h; rw [h]
    · rintro a b ⟨ha, hsa⟩ ⟨hb, hsb⟩ h
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl <;> try simp [sd_new] at hsa
      rcases leaf_cases g b with ⟨d', rfl⟩ | rfl | rfl | rfl <;> try simp [sd_new] at hsb
      rw [muL_old, muL_old] at h; rw [h]
    · rintro a ⟨ha, hsa⟩
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl <;> try simp [sd_new] at hsa
      rw [muL_old, sd_old] at *
      exact ⟨((set_old P g d).1 ha).1, by simpa using hsa⟩
    · rintro a ⟨ha, hsa⟩
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl <;> try simp [sd_new] at hsa
      rw [ends_old, muL_old]; simp only [rhoL_lv]; exact joins_ends d

end ii5

end RH2F

namespace RH2F
open MGraph

/-- **Layer 12 of the Lean formalization** (II-RED2 route): Theorem II-RED2 (fact 52408ddd08d61ae6), (I) for all
    bridgeless loopless cubic multigraphs under (H), and DMS from (H) and (II_D). -/
theorem layer12 :
    (Hyp → IID → II) ∧ (Hyp → IID → DMS) ∧
    (Hyp → ∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → BridgelessOn P → CubicOn P → Colourable P 6) :=
  ⟨ii_of, dms_of_H_IID, dmsI_all⟩

end RH2F
