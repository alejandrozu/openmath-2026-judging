-- Lean proof of fact 413193082c4b8758 (RH2F.layer15); added by fact_submit, do not edit
import MhFact_9e7dda3374e6b172
set_option backward.isDefEq.respectTransparency false

/-
  IV1.lean — the 3-cut brick (fact 87fba73118e1699c (a)): Lemma CC (the contraction X/V_A of a 3-edge-cut with distinct
  ends of a connected bridgeless loopless cubic multigraph is again one), dominance of a pole ((D1) and (D2)), and the
  brick: a dominant pole of side A and an EX1-good contraction of side A give EX1-goodness.
-/

namespace RH2F
open MGraph
open Classical

section brick
variable {X : MGraph} {P : Fin X.m → Prop}

namespace Cut3
variable (C : Cut3 P)

/-! ### Lemma CC -/

theorem addHub_loopless (hloop : Loopless X) (q : Fin 3 → Fin X.n) : Loopless (addHub X q) := by
  intro e
  rcases hub_cases q e with ⟨d, rfl⟩ | ⟨t, rfl⟩
  · rw [hub_ends_old]; exact fun h => hloop d (hv_inj _ h)
  · rw [hub_ends_new]; exact fun h => hv_ne_hub _ _ h.symm

/-- the vertex 2-colouring of `X` induced by one of `addHub X C.w`: side `A` gets the value of the hub -/
def liftU (U : Fin (addHub X C.w).n → Bool) : Fin X.n → Bool := fun v => if C.S v = true then U (hub C.w) else U (hv C.w v)

theorem liftU_A (U : Fin (addHub X C.w).n → Bool) {v : Fin X.n} (h : C.S v = true) : C.liftU U v = U (hub C.w) := by
  simp [liftU, h]
theorem liftU_B (U : Fin (addHub X C.w).n → Bool) {v : Fin X.n} (h : C.S v = false) : C.liftU U v = U (hv C.w v) := by
  simp [liftU, h]

theorem liftU_toV (U : Fin (addHub X C.w).n → Bool) (v : Fin X.n) : C.liftU U v = U (C.toV v) := by
  cases h : C.S v
  · rw [C.liftU_B U h, C.toV_B h]
  · rw [C.liftU_A U h, C.toV_A h]

/-- a 2-colouring of the contraction that is constant on the ends of the contraction edges other than `a0` (if any)
    lifts to one constant on the ends of the `P`-edges `f` with `C.toCont f ≠ a0` -/
theorem liftU_const (U : Fin (addHub X C.w).n → Bool) (F : Fin (addHub X C.w).m → Prop)
    (hU : ∀ a, C.cont a → F a → U ((addHub X C.w).ends a).1 = U ((addHub X C.w).ends a).2)
    {f : Fin X.m} (hf : P f) (hF : C.inA f ∨ F (C.toCont f)) :
    C.liftU U (X.ends f).1 = C.liftU U (X.ends f).2 := by
  rcases C.cases_P hf with h | h | h
  · rw [C.liftU_A U h.2.1, C.liftU_A U h.2.2]
  · have hF' : F (C.toCont f) := hF.resolve_left (C.not_flip_of_inA · h)
    have hj := C.toCont_joins (Or.inl h)
    have := hU _ (C.toCont_mem (Or.inl h)) hF'
    rw [C.liftU_toV, C.liftU_toV]
    rcases hj with hj | hj <;> rw [hj] at this
    · exact this
    · exact this.symm
  · have hF' : F (C.toCont f) := hF.resolve_left (C.not_inA_of_cut h)
    have hj := C.toCont_joins (Or.inr h)
    have := hU _ (C.toCont_mem (Or.inr h)) hF'
    rw [C.liftU_toV, C.liftU_toV]
    rcases hj with hj | hj <;> rw [hj] at this
    · exact this
    · exact this.symm

theorem cont_connected (hconn : ConnectedOn P) : ConnectedOn C.cont := by
  intro U hU a b ha hb
  have hP := hconn (C.liftU U) (fun f hf => C.liftU_const U (fun _ => True) (fun a ha _ => hU a ha) hf
    (Or.inr trivial))
  -- the first end of a contraction edge has the lifted value of the first end of a `P`-edge
  have key : ∀ a, C.cont a → ∃ f, P f ∧ U ((addHub X C.w).ends a).1 = C.liftU U (X.ends f).1 := by
    intro a ha
    rcases ha with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩
    · refine ⟨d, hd.1, ?_⟩
      have s1 : C.S (X.ends d).1 = false := by have := hd.2.1; rw [flip_S] at this; simpa using this
      rw [hub_ends_old, C.liftU_B U s1]
    · refine ⟨C.e t, C.hP t, ?_⟩
      rw [hub_ends_new]
      have hw : U (hub C.w) = U (hv C.w (C.w t)) := by
        have := hU (hNew C.w t) (Or.inr ⟨t, rfl⟩); rw [hub_ends_new] at this; exact this
      rcases C.hj t with h | h <;> rw [h]
      · rw [C.liftU_A U (C.sy t)]
      · rw [C.liftU_B U (C.sw t)]; exact hw
  obtain ⟨f, hf, hfa⟩ := key a ha
  obtain ⟨g, hg, hgb⟩ := key b hb
  rw [hfa, hgb]
  exact hP f g hf hg

theorem cont_bridgeless (hbr : BridgelessOn P) : BridgelessOn C.cont := by
  intro a ha B
  have hsep : ∀ f, P f → C.toCont f ≠ a → C.liftU B.U (X.ends f).1 = C.liftU B.U (X.ends f).2 := fun f hf hne =>
    C.liftU_const B.U (fun a' => a' ≠ a) (fun a' ha' hne' => B.sep a' ha' hne') hf
      (by by_cases h : C.inA f
          · exact Or.inl h
          · exact Or.inr hne)
  rcases ha with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩
  · -- an old edge inside `B`
    have s1 : C.S (X.ends d).1 = false := by have := hd.2.1; rw [flip_S] at this; simpa using this
    have s2 : C.S (X.ends d).2 = false := by have := hd.2.2; rw [flip_S] at this; simpa using this
    have hu := B.hu; have hv' := B.hv
    rw [hub_ends_old] at hu hv'
    apply hbr d hd.1
    exact { U := C.liftU B.U
            hu := by rw [C.liftU_B _ s1]; exact hu
            hv := by rw [C.liftU_B _ s2]; exact hv'
            sep := fun f hf hne => hsep f hf (fun h => hne (by
              rw [← C.toCont_flip_inA hd] at h; exact C.toCont_inj h)) }
  · -- a hub edge `z w_t`, i.e. the cut edge `e t`
    have hu := B.hu; have hv' := B.hv
    rw [hub_ends_new] at hu hv'
    have hne : ∀ f, P f → f ≠ C.e t → C.toCont f ≠ hNew C.w t := fun f _ h h' => h (by
      rw [← C.toCont_e t] at h'; exact C.toCont_inj h')
    rcases C.hj t with h | h
    · apply hbr (C.e t) (C.hP t)
      exact { U := C.liftU B.U
              hu := by rw [h, C.liftU_A _ (C.sy t)]; exact hu
              hv := by rw [h, C.liftU_B _ (C.sw t)]; exact hv'
              sep := fun f hf hne' => hsep f hf (hne f hf hne') }
    · apply hbr (C.e t) (C.hP t)
      exact { U := fun v => !C.liftU B.U v
              hu := by simp only [h, C.liftU_B _ (C.sw t), hv', Bool.not_false]
              hv := by simp only [h, C.liftU_A _ (C.sy t), hu, Bool.not_true]
              sep := fun f hf hne' => by simp only [hsep f hf (hne f hf hne')] }

theorem toV_eq_hv {v x : Fin X.n} (h : C.toV v = hv C.w x) : v = x ∧ C.S v = false := by
  cases hs : C.S v
  · rw [C.toV_B hs] at h; exact ⟨hv_inj _ h, rfl⟩
  · rw [C.toV_A hs] at h; exact absurd h.symm (hv_ne_hub _ _)

theorem inc_of_joins' {G : MGraph} {f : Fin G.m} {a b x : Fin G.n} (hj : G.Joins f a b) (hx : G.Inc f x) :
    x = a ∨ x = b := by
  rcases hj with h | h <;> rcases hx with hx | hx <;> rw [h] at hx <;> simp at hx
  · exact Or.inl hx.symm
  · exact Or.inr hx.symm
  · exact Or.inr hx.symm
  · exact Or.inl hx.symm

/-- an old vertex meeting the contraction lies on side `B` -/
theorem cont_at_B {a : Fin (addHub X C.w).m} {x : Fin X.n} (ha : C.cont a) (hax : (addHub X C.w).Inc a (hv C.w x)) :
    C.S x = false := by
  obtain ⟨f, hf, _, rfl⟩ := C.cont_at ha hax
  rcases inc_of_joins' (C.toCont_joins hf) hax with h | h
  · have := C.toV_eq_hv h.symm; rw [← this.1]; exact this.2
  · have := C.toV_eq_hv h.symm; rw [← this.1]; exact this.2

theorem toCont_inc {f : Fin X.m} {x : Fin X.n} (hf : C.flip.pole f) (hx : X.Inc f x) (hs : C.S x = false) :
    (addHub X C.w).Inc (C.toCont f) (hv C.w x) := by
  have hj := C.toCont_joins hf
  rw [← C.toV_B hs]
  rcases hx with h | h <;> rw [← h]
  · exact joins_inc_left hj
  · exact joins_inc_right hj

theorem cont_cubic (hcub : CubicOn P) : CubicOn C.cont := by
  rintro u ⟨a0, ha0, hau⟩
  rcases Fin.eq_castSucc_or_eq_last u with ⟨x, rfl⟩ | rfl
  · -- an old vertex, on side `B`
    have hu' : (addHub X C.w).Inc a0 (hv C.w x) := hau
    have hsx : C.S x = false := C.cont_at_B ha0 hu'
    have hsx' : C.flip.S x = true := by rw [flip_S, hsx]; rfl
    obtain ⟨f0, hf0, hf0x, rfl⟩ := C.cont_at ha0 hu'
    obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub x ⟨f0, C.flip.pole_P hf0, hf0x⟩
    have pp := C.flip.pole_of_inc hp ip hsx'
    have pq := C.flip.pole_of_inc hq iq hsx'
    have pr := C.flip.pole_of_inc hr ir hsx'
    refine ⟨C.toCont p, C.toCont q, C.toCont r, C.toCont_mem pp, C.toCont_mem pq, C.toCont_mem pr,
      C.toCont_inc pp ip hsx, C.toCont_inc pq iq hsx, C.toCont_inc pr ir hsx,
      fun h => dpq (C.toCont_inj h), fun h => dpr (C.toCont_inj h), fun h => dqr (C.toCont_inj h), ?_⟩
    intro b hb hbx
    obtain ⟨f, hf, hfx, rfl⟩ := C.cont_at hb hbx
    rcases hall f (C.flip.pole_P hf) hfx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · -- the hub
    refine ⟨hNew C.w 0, hNew C.w 1, hNew C.w 2, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩, Or.inr ⟨2, rfl⟩,
      hub_inc_new_hub _ 0, hub_inc_new_hub _ 1, hub_inc_new_hub _ 2, fun h => by have := hNew_inj _ h; simp [Fin.ext_iff] at this,
      fun h => by have := hNew_inj _ h; simp [Fin.ext_iff] at this, fun h => by have := hNew_inj _ h; simp [Fin.ext_iff] at this, ?_⟩
    intro b hb hbx
    rcases hb with ⟨d, rfl, _⟩ | ⟨t, rfl⟩
    · exact absurd hbx (hub_not_inc_old _)
    · have : t = 0 ∨ t = 1 ∨ t = 2 := by
        rcases t with ⟨t, ht⟩
        simp only [Fin.ext_iff]; omega
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- **Lemma CC**: the contraction of side `A` of a member of 𝒢 is a member of 𝒢 -/
theorem cont_inG (hG : InG X P) : InG (addHub X C.w) C.cont :=
  ⟨addHub_loopless hG.1 C.w, C.cont_connected hG.2.1, C.cont_bridgeless hG.2.2.1, C.cont_cubic hG.2.2.2⟩

/-! ### dominance of a pole -/

end Cut3

section dom
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n}

/-- condition (D2) of a pole `Q(Y, v)`: for every edge `g` of `Y − v` and every status `s` there is a port `i` such
    that every admissible outside datum at M-port `i` has a compatible MC pole colouring `d` with `[d g = 5] = s` -/
def D2 (D : Ports Q v) : Prop :=
  ∀ g, Q g → ¬ Y.Inc g v → ∀ s : Bool, ∃ i, ∀ a O B, Admissible i a O B →
    ∃ d, MCPole D d ∧ Compat D d a O B ∧ (d g = 5 ↔ s = true)

/-- the pole `Q(Y, v)` is dominant: (D1) at every port and (D2) -/
def Dominant (D : Ports Q v) : Prop := (∀ i, D1 D i) ∧ D2 D

end dom

/-! ### MC colourings and perfect matchings -/

section mcpm
variable {Y : MGraph} {Q : Fin Y.m → Prop}

theorem mcol_of_mc5 {N : Fin Y.m → Prop} {c : Fin Y.m → Fin 6} (hN : PMOn Q N) (hc : MC5 Q N c) : MCol Q c := by
  refine ⟨hc.1, fun x hx => ?_⟩
  obtain ⟨a, ha, hax, hu⟩ := hN.2 x hx
  refine ⟨a, hN.1 a ha, hax, (hc.2 a (hN.1 a ha)).1 ha, fun b hb hbx hb5 => hu b ((hc.2 b hb).2 hb5) hbx⟩

/-- the colour class `5` of an MC colouring is a perfect matching and a colour class -/
theorem pm_of_mcol {c : Fin Y.m → Fin 6} (hc : MCol Q c) :
    PMOn Q (fun f => Q f ∧ c f = 5) ∧ ClassOn Q (fun f => Q f ∧ c f = 5) c := by
  refine ⟨⟨fun f hf => hf.1, fun x hx => ?_⟩, ⟨5, fun f hf => ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩⟩⟩
  obtain ⟨a, ha, hax, ha5, hu⟩ := hc.2 x hx
  exact ⟨a, ⟨ha, ha5⟩, hax, fun d hd hdx => hu d hd.1 hdx hd.2⟩

/-- EX1-goodness from MC colourings with every status -/
theorem ex1_of_mcol (h : ∀ g, Q g → ∀ t : Bool, ∃ c, MCol Q c ∧ (c g = 5 ↔ t = true)) : EX1On Q := by
  intro g hg t _
  obtain ⟨c, hc, hst⟩ := h g hg t
  obtain ⟨hpm, hcl⟩ := pm_of_mcol hc
  exact ⟨_, hpm, ⟨fun hN => hst.1 hN.2, fun ht => ⟨hg, hst.2 ht⟩⟩, c, hc.1, hcl⟩

/-- an MC colouring with a prescribed status from EX1-goodness (with (P)) -/
theorem mcol_of_ex1 (hG : InG Y Q) (hE : EX1On Q) {h : Fin Y.m} (hh : Q h) (t : Bool) :
    ∃ c, MCol Q c ∧ (c h = 5 ↔ t = true) := by
  obtain ⟨N, c, hN, hst, hc⟩ := ex1_full RH2P.pstat hG hE hh t
  exact ⟨c, mcol_of_mc5 hN hc, ((hc.2 h hh).symm.trans hst)⟩

end mcpm

namespace Cut3
variable (C : Cut3 P)

/-- **MC gluing across a 3-edge-cut, with the glued colouring** (3CUT-MULTI (MC-M), direction ⇐) -/
theorem mc_glue' (c : Fin (addHub X C.w).m → Fin 6) (hc : MCol C.cont c) (φ : Fin X.m → Fin 6)
    (hφ : StarOn C.pole 6 φ) (hφA : ∀ x, C.S x = true → meets P x →
      ∃ a, C.pole a ∧ X.Inc a x ∧ φ a = 5 ∧ ∀ b, C.pole b → X.Inc b x → φ b = 5 → b = a)
    (hφe : ∀ t, φ (C.e t) = C.datA c t)
    (hcomp : ∀ t κ, C.Col φ t κ → C.datO c t κ → (C.Blk φ t κ ∨ C.datB c t κ) → False) :
    ∃ c', MCol P c' ∧ (∀ f, C.pole f → c' f = φ f) ∧ (∀ f, C.flip.pole f → c' f = c (C.toCont f)) := by
  let ψ : Fin X.m → Fin 6 := fun f => c (C.toCont f)
  have hψ : StarOn C.flip.pole 6 ψ := C.pole_of_cont c hc.1
  let c' : Fin X.m → Fin 6 := fun f => if C.inA f then φ f else ψ f
  have hcφ : ∀ f, C.pole f → c' f = φ f := by
    intro f hf
    by_cases h : C.inA f
    · simp only [c', if_pos h]
    · simp only [c', if_neg h]
      obtain ⟨t, rfl⟩ := hf.resolve_left h
      show c (C.toCont (C.e t)) = φ (C.e t)
      rw [hφe, C.toCont_e]; rfl
  have hcψ : ∀ f, C.flip.pole f → c' f = ψ f := by
    intro f hf
    have : ¬ C.inA f := by
      rcases hf with h | ⟨t, ht⟩
      · exact fun h' => C.not_flip_of_inA h' h
      · exact C.not_inA_of_cut ⟨t, ht⟩
    simp only [c', if_neg this]
  have hstar : StarOn P 6 c' := C.glue3 φ ψ c' hφ hψ hcφ hcψ (fun t κ h1 h2 h3 => hcomp t κ h1 h2 h3)
  refine ⟨c', ⟨hstar, fun x hx => ?_⟩, hcφ, hcψ⟩
  obtain ⟨f0, hf0, hf0x⟩ := hx
  cases hs : C.S x
  · -- side `B`: read off the contraction
    have hs' : C.flip.S x = true := by rw [flip_S, hs]; rfl
    obtain ⟨a, ha, hax, ha5, hauniq⟩ := hc.2 (hv C.w x) ⟨C.toCont f0, C.toCont_mem (C.flip.pole_of_inc hf0 hf0x hs'),
      by have := C.toCont_joins (C.flip.pole_of_inc hf0 hf0x hs'); rw [← C.toV_B hs]
         rcases hf0x with h | h <;> rw [← h]
         · exact joins_inc_left this
         · exact joins_inc_right this⟩
    obtain ⟨f, hfp, hfx, rfl⟩ := C.cont_at ha hax
    refine ⟨f, C.flip.pole_P hfp, hfx, by rw [hcψ f hfp]; exact ha5, fun b hb hbx hb5 => ?_⟩
    have hbp := C.flip.pole_of_inc hb hbx hs'
    apply C.toCont_inj
    apply hauniq _ (C.toCont_mem hbp)
    · have := C.toCont_joins hbp; rw [← C.toV_B hs]
      rcases hbx with h | h <;> rw [← h]
      · exact joins_inc_left this
      · exact joins_inc_right this
    · calc c (C.toCont b) = c' b := (hcψ b hbp).symm
        _ = 5 := hb5
  · obtain ⟨a, ha, hax, ha5, hauniq⟩ := hφA x hs ⟨f0, hf0, hf0x⟩
    refine ⟨a, C.pole_P ha, hax, by rw [hcφ a ha]; exact ha5, fun b hb hbx hb5 => ?_⟩
    have hbp := C.pole_of_inc hb hbx hs
    exact hauniq b hbp hbx (by rw [← hcφ b hbp]; exact hb5)


/-- the glued colouring from (D1)-type data at port `i`, tracking the colours -/
theorem glue_track (c : Fin (addHub X C.w).m → Fin 6)
    (hc : MCol C.cont c) {d : Fin (addHub X C.flip.w).m → Fin 6}
    (hd : MCPole C.hubPorts d) (hcomp : Compat C.hubPorts d (C.datA c) (C.datO c) (C.datB c)) :
    ∃ c', MCol P c' ∧ (∀ f, C.pole f → c' f = d (C.flip.toCont f)) ∧
      (∀ f, C.flip.pole f → c' f = c (C.toCont f)) := by
  obtain ⟨hs, hA, he, hcp⟩ := C.pole_of_D1 hd hcomp
  exact C.mc_glue' c hc _ hs hA he hcp

/-- **the 3-cut brick** (fact 87fba73118e1699c (a)): if the pole of side `A` (the pole of the contraction of side `B`
    at its hub) is dominant and the contraction of side `A` is EX1-good, then `P` is EX1-good -/
theorem brick (hG : InG X P) (hdom : Dominant C.hubPorts) (hE : EX1On C.cont) : EX1On P := by
  have hGc := C.cont_inG hG
  have hw : ∀ t, CubicAt P (C.w t) := fun t => hG.2.2.2 (C.w t) ⟨C.e t, C.hP t, joins_inc_right (C.hj t)⟩
  apply ex1_of_mcol
  intro g hg t
  rcases C.cases_P hg with hA | hgp
  · -- `g` inside side `A`: (D2) at `g`
    have hgc : C.flip.cont (C.flip.toCont g) := by
      rw [C.flipToCont_inA hA]
      exact Or.inl ⟨g, rfl, by simp only [flip_flip_inA]; exact hA⟩
    have hgv : ¬ (addHub X C.flip.w).Inc (C.flip.toCont g) (hub C.flip.w) := by
      rw [C.flipToCont_inA hA]; exact hub_not_inc_old _
    obtain ⟨i, hi⟩ := hdom.2 _ hgc hgv t
    obtain ⟨c, hc, hc5⟩ := mcol_of_ex1 hGc hE (h := hNew C.w i) (Or.inr ⟨i, rfl⟩) true
    have hci : c (hNew C.w i) = 5 := hc5.2 rfl
    obtain ⟨d, hd, hcomp, hst⟩ := hi _ _ _ (C.dat_admissible hG.1 hw c hc hci)
    obtain ⟨c', hc', hφ, _⟩ := C.glue_track c hc hd hcomp
    exact ⟨c', hc', by rw [hφ g (Or.inl hA)]; exact hst⟩
  · -- `g` inside side `B` or a cut edge: the status from the contraction, (D1) at the colour-5 port
    obtain ⟨c, hc, hst⟩ := mcol_of_ex1 hGc hE (C.toCont_mem hgp) t
    obtain ⟨i, hci⟩ := C.hub_port c hc
    obtain ⟨d, hd, hcomp⟩ := hdom.1 i _ _ _ (C.dat_admissible hG.1 hw c hc hci)
    obtain ⟨c', hc', _, hψ⟩ := C.glue_track c hc hd hcomp
    exact ⟨c', hc', by rw [hψ g hgp]; exact hst⟩

/-! ### counting on the contraction, and Lemma DR -/

theorem cont_cases {a : Fin (addHub X C.w).m} (ha : C.cont a) : ∃ f, C.flip.pole f ∧ a = C.toCont f := by
  rcases ha with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩
  · exact ⟨d, Or.inl hd, (C.toCont_flip_inA hd).symm⟩
  · exact ⟨C.e t, Or.inr ⟨t, rfl⟩, (C.toCont_e t).symm⟩

theorem meets_cont_hv (v : Fin X.n) : meets C.cont (hv C.w v) ↔ meets P v ∧ C.S v = false := by
  constructor
  · rintro ⟨a, ha, hav⟩
    obtain ⟨f, hf, hfv, _⟩ := C.cont_at ha hav
    exact ⟨⟨f, C.flip.pole_P hf, hfv⟩, C.cont_at_B ha hav⟩
  · rintro ⟨⟨f, hf, hfv⟩, hs⟩
    have hs' : C.flip.S v = true := by rw [flip_S, hs]; rfl
    have hfp := C.flip.pole_of_inc hf hfv hs'
    exact ⟨C.toCont f, C.toCont_mem hfp, C.toCont_inc hfp hfv hs⟩

theorem meets_cont_hub : meets C.cont (hub C.w) := ⟨hNew C.w 0, Or.inr ⟨0, rfl⟩, hub_inc_new_hub _ 0⟩

theorem vcount_cont : vcount C.cont = scount P C.S false + 1 := by
  unfold vcount scount
  show cntF (X.n + 1) (meets C.cont) = _
  have hh : meets C.cont (Fin.last X.n) := C.meets_cont_hub
  rw [cntF_succ, if_pos hh]
  congr 1
  exact cntF_congr _ _ _ (fun v => C.meets_cont_hv v)

theorem scount_flip3 (b : Bool) : scount P C.flip.S b = scount P C.S (!b) := by
  unfold scount
  apply cntF_congr
  intro v
  rw [flip_S]
  cases C.S v <;> cases b <;> simp

/-- each side has at least three vertices (the three ends of the cut edges) -/
theorem three_le_A : 3 ≤ scount P C.S true := by
  unfold scount
  rw [cntF_eq_card]
  apply Finset.two_lt_card_iff.2
  refine ⟨C.y 0, C.y 1, C.y 2, ?_, ?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨C.e 0, C.hP 0, joins_inc_left (C.hj 0)⟩, C.sy 0⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨C.e 1, C.hP 1, joins_inc_left (C.hj 1)⟩, C.sy 1⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨C.e 2, C.hP 2, joins_inc_left (C.hj 2)⟩, C.sy 2⟩
  · have := C.yinj _ _ h; simp [Fin.ext_iff] at this
  · have := C.yinj _ _ h; simp [Fin.ext_iff] at this
  · have := C.yinj _ _ h; simp [Fin.ext_iff] at this

theorem three_le_B : 3 ≤ scount P C.S false := by
  have := C.flip.three_le_A
  rw [C.scount_flip3] at this
  exact this

/-- crossing a lifted 2-colouring -/
theorem crosses_lift (S : Fin (addHub X C.w).n → Bool) {f : Fin X.m} (hf : C.flip.pole f) :
    RH2F.Crosses P (C.liftU S) f ↔ RH2F.Crosses C.cont S (C.toCont f) := by
  unfold RH2F.Crosses
  rw [C.liftU_toV, C.liftU_toV]
  have hj := C.toCont_joins hf
  constructor
  · rintro ⟨_, h⟩
    refine ⟨C.toCont_mem hf, ?_⟩
    rcases hj with hj | hj <;> rw [hj]
    · exact h
    · exact fun h' => h h'.symm
  · rintro ⟨_, h⟩
    refine ⟨C.flip.pole_P hf, ?_⟩
    rcases hj with hj | hj <;> rw [hj] at h
    · exact h
    · exact fun h' => h h'.symm

theorem not_crosses_inA (S : Fin (addHub X C.w).n → Bool) {f : Fin X.m} (hf : C.inA f) :
    ¬ RH2F.Crosses P (C.liftU S) f := by
  rintro ⟨_, h⟩
  rw [C.liftU_A S hf.2.1, C.liftU_A S hf.2.2] at h
  exact h rfl

theorem twoCut_lift (S : Fin (addHub X C.w).n → Bool) (hS : RH2F.TwoCut C.cont S) :
    RH2F.TwoCut P (C.liftU S) := by
  obtain ⟨a1, a2, hne, c1, c2, hall⟩ := hS
  obtain ⟨f1, hf1, rfl⟩ := C.cont_cases c1.1
  obtain ⟨f2, hf2, rfl⟩ := C.cont_cases c2.1
  refine ⟨f1, f2, fun h => hne (by rw [h]), (C.crosses_lift S hf1).2 c1, (C.crosses_lift S hf2).2 c2, ?_⟩
  intro d hd
  rcases C.cases_P hd.1 with hA | hdp
  · exact absurd hd (C.not_crosses_inA S hA)
  · rcases hall _ ((C.crosses_lift S hdp).1 hd) with h | h
    · exact Or.inl (C.toCont_inj h)
    · exact Or.inr (C.toCont_inj h)

/-- the side counts of a lifted 2-colouring -/
theorem scount_lift (S : Fin (addHub X C.w).n → Bool) (b : Bool) :
    scount P (C.liftU S) b = (if S (hub C.w) = b then scount P C.S true else 0) +
      cntF X.n (fun v => (meets P v ∧ C.S v = false) ∧ S (hv C.w v) = b) := by
  unfold scount
  rw [cntF_split X.n _ (fun v => C.S v = true)]
  congr 1
  · by_cases hb : S (hub C.w) = b
    · rw [if_pos hb]
      apply cntF_congr
      intro v
      constructor
      · rintro ⟨⟨hm, _⟩, hs⟩; exact ⟨hm, hs⟩
      · rintro ⟨hm, hs⟩; exact ⟨⟨hm, by rw [C.liftU_A S hs]; exact hb⟩, hs⟩
    · rw [if_neg hb]
      apply cntF_eq_zero
      rintro v ⟨⟨_, h⟩, hs⟩
      rw [C.liftU_A S hs] at h
      exact hb h
  · apply cntF_congr
    intro v
    constructor
    · rintro ⟨⟨hm, h⟩, hs⟩
      have hs' : C.S v = false := by simpa using hs
      exact ⟨⟨hm, hs'⟩, by rw [C.liftU_B S hs'] at h; exact h⟩
    · rintro ⟨⟨hm, hs⟩, h⟩
      exact ⟨⟨hm, by rw [C.liftU_B S hs]; exact h⟩, by simp [hs]⟩

theorem scount_cont (S : Fin (addHub X C.w).n → Bool) (b : Bool) :
    scount C.cont S b = cntF X.n (fun v => (meets P v ∧ C.S v = false) ∧ S (hv C.w v) = b) +
      (if S (hub C.w) = b then 1 else 0) := by
  unfold scount
  show cntF (X.n + 1) _ = _
  rw [cntF_succ]
  congr 1
  · apply cntF_congr
    intro v
    show meets C.cont (hv C.w v) ∧ S (hv C.w v) = b ↔ _
    rw [C.meets_cont_hv]
  · by_cases hb : S (hub C.w) = b
    · rw [if_pos ⟨C.meets_cont_hub, hb⟩, if_pos hb]
    · rw [if_neg (fun h => hb h.2), if_neg hb]

/-- **Lemma DR**: the contraction of side `A` of a 2-cut-reduced edge set is 2-cut-reduced -/
theorem cont_2cr (h2 : TwoCutReducedOn P) : TwoCutReducedOn C.cont := by
  intro S hS
  have hA3 := C.three_le_A
  have key : ∀ b, scount P (C.liftU S) b = 2 → scount C.cont S b = 2 := by
    intro b hb
    rw [C.scount_lift] at hb
    rw [C.scount_cont]
    by_cases hh : S (hub C.w) = b
    · rw [if_pos hh] at hb; omega
    · rw [if_neg hh] at hb; rw [if_neg hh]; omega
  rcases h2 _ (C.twoCut_lift S hS) with h | h
  · exact Or.inl (key true h)
  · exact Or.inr (key false h)

end Cut3

/-! ### the 3-cut layer (fact 87fba73118e1699c (b)) -/

/-- (POLE): every pole of a 2-cut-reduced member of 𝒢 on at least 10 vertices is dominant -/
def POLE : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P →
    ∀ (v : Fin X.n) (D : Ports P v), Dominant D

/-- a reducible 3-edge-cut: `|V1| ≥ 9`, and `|V2| ≥ 9`, or `G/V1` EX1-good, or `|V2| ≤ 7` and the pole `Q(G/V1, z2)`
    dominant -/
def Cut3.Reducible (C : Cut3 P) : Prop :=
  9 ≤ scount P C.S true ∧
    (9 ≤ scount P C.S false ∨ EX1On C.cont ∨ (scount P C.S false ≤ 7 ∧ Dominant C.flip.hubPorts))

/-- **the 3-cut layer** (fact 87fba73118e1699c (b)): under (POLE), if every 2-cut-reduced member of 𝒢 on at least 10
    vertices without a reducible 3-edge-cut is EX1-good, then every 2-cut-reduced member of 𝒢 on at least 10 vertices
    is EX1-good -/
theorem layer_3cut (hpole : POLE)
    (hcore : ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P →
      (∀ C : Cut3 P, ¬ C.Reducible) → EX1On P) :
    ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P → EX1On P := by
  intro X P
  generalize hn : vcount P = n
  induction n using Nat.strong_induction_on generalizing X P with
  | _ n ih =>
  intro hG h10 h2
  by_cases hr : ∃ C : Cut3 P, C.Reducible
  · obtain ⟨C, hA9, hr'⟩ := hr
    have hsplit := vcount_split P C.S
    have hA3 := C.three_le_A
    have hB3 := C.three_le_B
    have hsum : scount P C.S true + scount P C.S false = n := by rw [← hn, hsplit]
    -- the pole of side `A` is dominant, by (POLE) applied to the contraction of side `B`
    have hdomA : Dominant C.hubPorts := by
      apply hpole _ _ (C.flip.cont_inG hG)
      · rw [C.flip.vcount_cont, C.scount_flip3]; simp only [Bool.not_false]; omega
      · exact C.flip.cont_2cr h2
    rcases hr' with h9 | hE | ⟨_, hdomB⟩
    · apply C.brick hG hdomA
      apply ih (scount P C.S false + 1) (by omega) _ _ C.vcount_cont (C.cont_inG hG)
      · omega
      · exact C.cont_2cr h2
    · exact C.brick hG hdomA hE
    · apply C.flip.brick hG hdomB
      apply ih (scount P C.S true + 1) (by omega) _ _ (by rw [C.flip.vcount_cont, C.scount_flip3]; rfl)
        (C.flip.cont_inG hG)
      · omega
      · exact C.flip.cont_2cr h2
  · exact hcore X P hG (by rw [hn]; exact h10) h2 (fun C hC => hr ⟨C, hC⟩)




end brick

end RH2F

namespace RH2F
open MGraph

/-- **Layer 15 of the Lean formalization** (3-edge-cut layer): the 3-cut brick and the 3-cut layer of fact
    87fba73118e1699c ((a) and (b)), with Lemma CC and Lemma DR (the contraction of a side of a 3-edge-cut with distinct
    ends of a (2-cut-reduced) member of 𝒢 is again one). -/
theorem layer15 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P), InG X P → InG (addHub X C.w) C.cont) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P), TwoCutReducedOn P → TwoCutReducedOn C.cont) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P), vcount C.cont = scount P C.S false + 1) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P), InG X P → Dominant C.hubPorts → EX1On C.cont → EX1On P) ∧
    (POLE → (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P →
        (∀ C : Cut3 P, ¬ C.Reducible) → EX1On P) →
      ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P → EX1On P) :=
  ⟨fun _ _ C hG => C.cont_inG hG, fun _ _ C h2 => C.cont_2cr h2, fun _ _ C => C.vcount_cont,
   fun _ _ C hG hd hE => C.brick hG hd hE, fun hp hc => layer_3cut hp hc⟩

end RH2F
