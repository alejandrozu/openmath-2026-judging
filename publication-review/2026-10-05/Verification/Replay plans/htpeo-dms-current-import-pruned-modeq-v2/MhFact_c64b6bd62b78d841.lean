-- Lean proof of fact c64b6bd62b78d841 (RH2F.layer2); added by fact_submit, do not edit
import MhFact_7d291f6ca774e1da



-- ===== from RH2Pole.lean =====
/-
  RH2Pole.lean — the 2-poles of a 2-edge-cut and the gluing of their star colourings (the "if" parts of Lemma 2P,
  fact 8f2b69f6533dd766, parts (2) and (3), together with Lemma 2P-END, fact 216c7379).

  The 2-pole `A⁺` (side `A` with pendant edges `p_i = a_i ℓ_i`) is represented inside the same ambient multigraph as
  the edge set `C.pole = E(G[A]) ∪ {e1, e2}`: the pendant vertex `ℓ_i` is `b_i` and the pendant edge `p_i` is `e_i`
  (Lemma 2P, (B3)).  So a colouring of `A⁺` is a map `Fin X.m → Fin 6`, and `φ ⊕ ψ` is any `c` agreeing with `φ` on
  `C.pole` and with `ψ` on `C.flip.pole`.  A walk meeting the cut only in end edges is then literally a walk of one
  pole (Lemma 2P-END).
-/

namespace RH2F
open MGraph

section pole
variable {X : MGraph} {P M : Fin X.m → Prop}

/-- the 2-pole `A⁺` as an edge set: the edges inside `A` and the two cut edges -/
def Cut2.pole (C : Cut2 P) (f : Fin X.m) : Prop := C.inA f ∨ C.isCut f

theorem Cut2.pole_P (C : Cut2 P) {f : Fin X.m} (h : C.pole f) : P f := by
  rcases h with h | h
  · exact h.1
  · rcases h with rfl | rfl
    · exact C.P1
    · exact C.P2

/-- every edge of `P` at a vertex of `A` lies in the pole `A⁺` -/
theorem Cut2.pole_of_inc (C : Cut2 P) {f : Fin X.m} {x : Fin X.n} (hf : P f) (hx : X.Inc f x)
    (hs : C.S x = true) : C.pole f := by
  by_cases hc : C.isCut f
  · exact Or.inr hc
  · exact Or.inl (C.inA_of_notcut hf hc hx hs)

theorem Cut2.flip_true {C : Cut2 P} {x : Fin X.n} (h : C.S x = false) : C.flip.S x = true := by
  rw [Cut2.flip_S, h]; rfl

theorem Cut2.flip_flip_S (C : Cut2 P) (x : Fin X.n) : C.flip.flip.S x = C.S x := by
  simp [Cut2.flip_S]

/-- properness of a glued colouring -/
theorem glue_prop (C : Cut2 P) (φ ψ c : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f) :
    ∀ a b, X.Adj a b → P a → P b → c a ≠ c b := by
  intro a b hab ha hb
  obtain ⟨hne, x, hax, hbx⟩ := hab
  cases hs : C.S x
  · have hs' := Cut2.flip_true hs
    have pa := C.flip.pole_of_inc ha hax hs'
    have pb := C.flip.pole_of_inc hb hbx hs'
    rw [hcψ a pa, hcψ b pb]
    exact hψ.1 a b ⟨hne, x, hax, hbx⟩ pa pb
  · have pa := C.pole_of_inc ha hax hs
    have pb := C.pole_of_inc hb hbx hs
    rw [hcφ a pa, hcφ b pb]
    exact hφ.1 a b ⟨hne, x, hax, hbx⟩ pa pb

/-- a walk whose two middle edges are not cut edges lies in one pole (Lemma 2P-END) -/
theorem glue_mid (C : Cut2 P) (φ ψ c : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f) (w : X.Walk4)
    (h1 : P w.e1) (h2 : P w.e2) (h3 : P w.e3) (h4 : P w.e4) (c2 : ¬ C.isCut w.e2) (c3 : ¬ C.isCut w.e3) :
    ¬ Bicol c w := by
  intro hb
  have s12 : C.S w.v1 = C.S w.v2 := C.same_side h2 c2 w.h2
  have s23 : C.S w.v2 = C.S w.v3 := C.same_side h3 c3 w.h3
  cases hs : C.S w.v1
  · have t1 := Cut2.flip_true hs
    have t2 := Cut2.flip_true (s12 ▸ hs)
    have t3 := Cut2.flip_true (s23 ▸ s12 ▸ hs)
    have p1 := C.flip.pole_of_inc h1 w.inc_e1_v1 t1
    have p2 := C.flip.pole_of_inc h2 w.inc_e2_v1 t1
    have p3 := C.flip.pole_of_inc h3 w.inc_e3_v2 t2
    have p4 := C.flip.pole_of_inc h4 w.inc_e4_v3 t3
    exact hψ.2 w p1 p2 p3 p4 ⟨by rw [← hcψ _ p1, ← hcψ _ p3]; exact hb.1, by rw [← hcψ _ p2, ← hcψ _ p4]; exact hb.2⟩
  · have p1 := C.pole_of_inc h1 w.inc_e1_v1 hs
    have p2 := C.pole_of_inc h2 w.inc_e2_v1 hs
    have p3 := C.pole_of_inc h3 w.inc_e3_v2 (s12 ▸ hs)
    have p4 := C.pole_of_inc h4 w.inc_e4_v3 (s23 ▸ s12 ▸ hs)
    exact hφ.2 w p1 p2 p3 p4 ⟨by rw [← hcφ _ p1, ← hcφ _ p3]; exact hb.1, by rw [← hcφ _ p2, ← hcφ _ p4]; exact hb.2⟩

/-- **Gluing across an M-type cut** (Lemma 2P(2), "if").  Cut edges in `M`; `c` agrees with a star colouring `φ`
    of `A⁺` and `ψ` of `B⁺`; the colour class `5` of `c` is `M`; and at each cut edge `e_i` an F-edge at `a_i` and an
    F-edge at `b_i` get different colours (`P_φ(a_i) ∩ P_ψ(b_i) = ∅`).  Then `c` is a star colouring of `P`. -/
theorem glue_M (hM : PMOn P M) (C : Cut2 P) (hM1 : M C.e1) (hM2 : M C.e2) (φ ψ c : Fin X.m → Fin 6)
    (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f)
    (hdisj : ∀ e f f' u u', C.isCut e → X.Joins e u u' → P f → ¬ M f → X.Inc f u → P f' → ¬ M f' →
      X.Inc f' u' → c f ≠ c f') :
    StarOn P 6 c := by
  refine ⟨glue_prop C φ ψ c hφ hψ hcφ hcψ, ?_⟩
  intro w h1 h2 h3 h4 hb
  have mcut : ∀ e, C.isCut e → M e := fun e he => he.elim (fun h => h ▸ hM1) (fun h => h ▸ hM2)
  by_cases c2 : C.isCut w.e2
  · have n1 : ¬ M w.e1 := fun h => w.e1_ne_e2 (pm_unique hM h (mcut _ c2) w.inc_e1_v1 w.inc_e2_v1)
    have n3 : ¬ M w.e3 := fun h => w.e2_ne_e3 (pm_unique hM (mcut _ c2) h w.inc_e2_v2 w.inc_e3_v2)
    exact hdisj _ _ _ _ _ c2 w.h2 h1 n1 w.inc_e1_v1 h3 n3 w.inc_e3_v2 hb.1
  by_cases c3 : C.isCut w.e3
  · have n2 : ¬ M w.e2 := fun h => w.e2_ne_e3 (pm_unique hM h (mcut _ c3) w.inc_e2_v2 w.inc_e3_v2)
    have n4 : ¬ M w.e4 := fun h => w.e3_ne_e4 (pm_unique hM (mcut _ c3) h w.inc_e3_v3 w.inc_e4_v3)
    exact hdisj _ _ _ _ _ c3 w.h3 h2 n2 w.inc_e2_v2 h4 n4 w.inc_e4_v3 hb.2
  exact glue_mid C φ ψ c hφ hψ hcφ hcψ w h1 h2 h3 h4 c2 c3 hb

/-- the key case of the F-type gluing: `w2` is a cut edge whose end `v1` lies in `A` -/
theorem glue_F_key (hloop : Loopless X) (hM : PMOn P M) (C : Cut2 P) (hF1 : ¬ M C.e1) (hF2 : ¬ M C.e2)
    (ψ c : Fin X.m → Fin 6) (hψ : StarOn C.flip.pole 6 ψ)
    (hcψ : ∀ f, C.flip.pole f → c f = ψ f) (hcl : ∀ f, P f → (M f ↔ c f = 5))
    (hF1' : ∀ r, M r → X.Joins r C.b1 C.b2 → c C.e1 ≠ c C.e2)
    (hF2' : ∀ e f f' u u', C.isCut e → X.Joins e u u' → C.S u = true → f ≠ e → f' ≠ e → P f → ¬ M f →
      X.Inc f u → P f' → ¬ M f' → X.Inc f' u' → c f ≠ c f')
    (w : X.Walk4) (h1 : P w.e1) (h3 : P w.e3) (h4 : P w.e4) (c2 : C.isCut w.e2)
    (hv1 : C.S w.v1 = true) : ¬ Bicol c w := by
  intro hb
  have fcut : ∀ e, C.isCut e → ¬ M e := fun e he h => he.elim (fun h' => hF1 (h' ▸ h)) (fun h' => hF2 (h' ▸ h))
  -- the ends of the cut edge `w2`
  have hv2 : C.S w.v2 = false := by
    rcases C.cut_sides c2 w.h2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · rw [hv1] at h; exact absurd h (by decide)
  by_cases m1 : M w.e1
  · -- `w1`, `w3` are matching edges; `w4` has the colour of the cut edge `w2`
    have m3 : M w.e3 := (hcl _ h3).2 (hb.1 ▸ (hcl _ h1).1 m1)
    have c3 : ¬ C.isCut w.e3 := fun h => fcut _ h m3
    have t2 := Cut2.flip_true hv2
    have i3 : C.flip.inA w.e3 := C.flip.inA_of_notcut h3 c3 w.inc_e3_v2 t2
    have t3 : C.flip.S w.v3 = true := C.flip.side_of_inA i3 w.inc_e3_v3
    have hv3 : C.S w.v3 = false := by rw [Cut2.flip_S] at t3; simpa using t3
    by_cases c4 : C.isCut w.e4
    · -- `w3 ∈ M` joins `b1` and `b2`
      exfalso
      have hne24 : w.e2 ≠ w.e4 := w.e2_ne_e4
      rcases c2 with h2e | h2e <;> rcases c4 with h4e | h4e
      · exact hne24 (h2e.trans h4e.symm)
      · -- w2 = e1, w4 = e2: v2 = b1, v3 = b2
        have ev2 : w.v2 = C.b1 := by
          rcases C.inc_e1 (h2e ▸ w.inc_e2_v2) with h | h
          · rw [h, C.sa1] at hv2; exact absurd hv2 (by decide)
          · exact h
        have ev3 : w.v3 = C.b2 := by
          rcases C.inc_e2 (h4e ▸ w.inc_e4_v3) with h | h
          · rw [h, C.sa2] at hv3; exact absurd hv3 (by decide)
          · exact h
        have hj : X.Joins w.e3 C.b1 C.b2 := ev2 ▸ ev3 ▸ w.h3
        exact hF1' _ m3 hj (by rw [← h2e, ← h4e]; exact hb.2)
      · -- w2 = e2, w4 = e1: v2 = b2, v3 = b1
        have ev2 : w.v2 = C.b2 := by
          rcases C.inc_e2 (h2e ▸ w.inc_e2_v2) with h | h
          · rw [h, C.sa2] at hv2; exact absurd hv2 (by decide)
          · exact h
        have ev3 : w.v3 = C.b1 := by
          rcases C.inc_e1 (h4e ▸ w.inc_e4_v3) with h | h
          · rw [h, C.sa1] at hv3; exact absurd hv3 (by decide)
          · exact h
        have hj : X.Joins w.e3 C.b1 C.b2 := Or.symm (ev2 ▸ ev3 ▸ w.h3)
        exact hF1' _ m3 hj (by rw [← h4e, ← h2e]; exact hb.2.symm)
      · exact hne24 (h2e.trans h4e.symm)
    · -- `w4` inside `B`: the walk `w2, w3, w4, m(v4)` of the pole `B⁺` is bicoloured
      have i4 : C.flip.inA w.e4 := C.flip.inA_of_notcut h4 c4 w.inc_e4_v3 t3
      have t4 : C.flip.S w.v4 = true := C.flip.side_of_inA i4 w.inc_e4_v4
      obtain ⟨m, hm, hmv4, _⟩ := hM.2 w.v4 ⟨w.e4, h4, w.inc_e4_v4⟩
      obtain ⟨z, hz⟩ := joins_of_inc hmv4
      have cm : ¬ C.isCut m := fun h => fcut _ h hm
      have im : C.flip.inA m := C.flip.inA_of_notcut (hM.1 m hm) cm hmv4 t4
      have pw2 : C.flip.pole w.e2 := Or.inr c2
      have pw3 : C.flip.pole w.e3 := Or.inl i3
      have pw4 : C.flip.pole w.e4 := Or.inl i4
      have pm : C.flip.pole m := Or.inl im
      -- distinctness
      have hv2v4 : w.v2 ≠ w.v4 := w.d24
      have hv3v4 : w.v3 ≠ w.v4 := w.d34
      have hv1v3 : w.v1 ≠ w.v3 := w.d13
      have hv1v4 : w.v1 ≠ w.v4 := by
        intro h
        rw [Cut2.flip_S, ← h, hv1] at t4
        exact absurd t4 (by decide)
      have hv4z : w.v4 ≠ z := ne_of_joins hloop hz
      have hv2z : w.v2 ≠ z := by
        intro h
        have := pm_unique hM hm m3 (h ▸ joins_inc_right hz) w.inc_e3_v2
        subst this
        rcases inc_of_joins w.h3 hmv4 with h' | h'
        · exact hv2v4 h'.symm
        · exact hv3v4 h'.symm
      have hv3z : w.v3 ≠ z := by
        intro h
        have := pm_unique hM hm m3 (h ▸ joins_inc_right hz) w.inc_e3_v3
        subst this
        rcases inc_of_joins w.h3 hmv4 with h' | h'
        · exact hv2v4 h'.symm
        · exact hv3v4 h'.symm
      let W : X.Walk4 :=
        { v0 := w.v1, v1 := w.v2, v2 := w.v3, v3 := w.v4, v4 := z
          e1 := w.e2, e2 := w.e3, e3 := w.e4, e4 := m
          h1 := w.h2, h2 := w.h3, h3 := w.h4, h4 := hz
          d01 := w.d12, d02 := hv1v3, d03 := hv1v4, d12 := w.d23, d13 := hv2v4, d14 := hv2z
          d23 := hv3v4, d24 := hv3z, d34 := hv4z }
      apply hψ.2 W pw2 pw3 pw4 pm
      constructor
      · show ψ w.e2 = ψ w.e4
        rw [← hcψ _ pw2, ← hcψ _ pw4]; exact hb.2
      · show ψ w.e3 = ψ m
        rw [← hcψ _ pw3, ← hcψ _ pm, (hcl _ h3).1 m3, (hcl _ (hM.1 m hm)).1 hm]
  · -- `w1`, `w3` are F-edges at the two ends of the cut edge `w2`
    have m3 : ¬ M w.e3 := fun h => m1 ((hcl _ h1).2 (hb.1.symm ▸ (hcl _ h3).1 h))
    exact hF2' _ _ _ _ _ c2 w.h2 hv1 w.e1_ne_e2 w.e2_ne_e3.symm h1 m1 w.inc_e1_v1 h3 m3 w.inc_e3_v2 hb.1

theorem Cut2.flip_flip_inA_iff (C : Cut2 P) {f : Fin X.m} : C.flip.flip.inA f ↔ C.inA f := by
  unfold Cut2.inA; rw [Cut2.flip_flip_S, Cut2.flip_flip_S]

theorem Cut2.flip_flip_pole (C : Cut2 P) {f : Fin X.m} : C.flip.flip.pole f ↔ C.pole f := by
  unfold Cut2.pole; rw [C.flip_flip_inA_iff]; exact Iff.rfl

theorem starOn_congr {Q Q' : Fin X.m → Prop} {k : Nat} {c : Fin X.m → Fin k} (h : ∀ f, Q f ↔ Q' f)
    (hc : StarOn Q k c) : StarOn Q' k c :=
  ⟨fun a b hab ha hb => hc.1 a b hab ((h a).2 ha) ((h b).2 hb),
   fun w h1 h2 h3 h4 => hc.2 w ((h _).2 h1) ((h _).2 h2) ((h _).2 h3) ((h _).2 h4)⟩

/-- **Gluing across an F-type cut** (Lemma 2P(3), "if", with (F2) in the stronger form used by Lemma 2P(4b),(4c)).
    Cut edges not in `M`; `c` agrees with a star colouring `φ` of `A⁺` and `ψ` of `B⁺`; the colour class `5` of `c`
    is `M`; (F1) if an edge of `M` joins `a1, a2` or `b1, b2` then the cut edges get different colours; (F2′) at each
    cut edge an F-edge at one end and an F-edge at the other end get different colours.  Then `c` is a star colouring
    of `P`. -/
theorem glue_F (hloop : Loopless X) (hM : PMOn P M) (C : Cut2 P) (hF1 : ¬ M C.e1) (hF2 : ¬ M C.e2)
    (φ ψ c : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f)
    (hcl : ∀ f, P f → (M f ↔ c f = 5))
    (hF1' : ∀ r, M r → (X.Joins r C.a1 C.a2 ∨ X.Joins r C.b1 C.b2) → c C.e1 ≠ c C.e2)
    (hF2' : ∀ e f f' u u', C.isCut e → X.Joins e u u' → f ≠ e → f' ≠ e → P f → ¬ M f → X.Inc f u → P f' →
      ¬ M f' → X.Inc f' u' → c f ≠ c f') :
    StarOn P 6 c := by
  refine ⟨glue_prop C φ ψ c hφ hψ hcφ hcψ, ?_⟩
  have hφ' : StarOn C.flip.flip.pole 6 φ := starOn_congr (fun f => (C.flip_flip_pole).symm) hφ
  have hcφ' : ∀ f, C.flip.flip.pole f → c f = φ f := fun f h => hcφ f ((C.flip_flip_pole).1 h)
  -- a cut edge in the second position, in either orientation
  have key : ∀ w : X.Walk4, P w.e1 → P w.e3 → P w.e4 → C.isCut w.e2 → ¬ Bicol c w := by
    intro w h1 h3 h4 c2
    cases hs : C.S w.v1
    · exact glue_F_key hloop hM C.flip hF1 hF2 φ c hφ' hcφ' hcl
        (fun r hr hj => hF1' r hr (Or.inl hj))
        (fun e f f' u u' he hj _ => hF2' e f f' u u' he hj) w h1 h3 h4 c2 (Cut2.flip_true hs)
    · exact glue_F_key hloop hM C hF1 hF2 ψ c hψ hcψ hcl
        (fun r hr hj => hF1' r hr (Or.inr hj))
        (fun e f f' u u' he hj _ => hF2' e f f' u u' he hj) w h1 h3 h4 c2 hs
  intro w h1 h2 h3 h4 hb
  by_cases c2 : C.isCut w.e2
  · exact key w h1 h3 h4 c2 hb
  by_cases c3 : C.isCut w.e3
  · exact key w.reverse h4 h2 h1 c3 (bicol_rev w hb)
  exact glue_mid C φ ψ c hφ hψ hcφ hcψ w h1 h2 h3 h4 c2 c3 hb

end pole

end RH2F

-- ===== from RH2CL0.lean =====
/-
  RH2CL0.lean — Lemma CL (fact ecc9734f558cf885), part (0), in Lean 4.20 core: the edge closure `G_A` and the digon
  closure `G_A^D` of a side of a 2-edge-cut of a connected bridgeless cubic `P` are loopless, connected, bridgeless
  and cubic.

  The digon closure of side `A` is encoded in the ambient `C.XD = addEdge (addEdge X b1 b2) b1 b2`: its edges are the
  pole `A⁺ = E(G[A]) ∪ {e1, e2}` (old edges) and the two new parallel edges `δ = C.dl1`, `δ′ = C.dl2` joining
  `b1, b2`; the digon vertices `d1, d2` of the prose are `b1, b2`.
-/

namespace RH2F
open MGraph

section cl0
variable {X : MGraph} {P : Fin X.m → Prop}

/-! ### the edge closure -/

theorem Cut2.clo_side (C : Cut2 P) {i : Fin (addEdge X C.a1 C.a2).m} (hi : C.clo i) {x : Fin X.n}
    (hx : (addEdge X C.a1 C.a2).Inc i x) : C.S x = true := by
  rcases hi with rfl | ⟨d, rfl, hd⟩
  · rcases (C.inc_new_iff).1 hx with rfl | rfl
    · exact C.sa1
    · exact C.sa2
  · exact C.side_of_inA hd (addEdge_inc_old.1 hx)

theorem Cut2.e1_vals (C : Cut2 P) (V : Fin X.n → Bool) :
    (V (X.ends C.e1).1 = V C.a1 ∧ V (X.ends C.e1).2 = V C.b1) ∨
    (V (X.ends C.e1).1 = V C.b1 ∧ V (X.ends C.e1).2 = V C.a1) := by
  rcases C.j1 with h | h <;> rw [h]
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem Cut2.e2_vals (C : Cut2 P) (V : Fin X.n → Bool) :
    (V (X.ends C.e2).1 = V C.a2 ∧ V (X.ends C.e2).2 = V C.b2) ∨
    (V (X.ends C.e2).1 = V C.b2 ∧ V (X.ends C.e2).2 = V C.a2) := by
  rcases C.j2 with h | h <;> rw [h]
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- the labelling of `X` that agrees with `U` on side `A` and is `κ` on side `B` -/
def Cut2.lift (C : Cut2 P) (U : Fin X.n → Bool) (κ : Bool) : Fin X.n → Bool :=
  fun v => if C.S v = true then U v else κ

theorem Cut2.lift_A (C : Cut2 P) (U : Fin X.n → Bool) (κ : Bool) {v : Fin X.n} (h : C.S v = true) :
    C.lift U κ v = U v := by simp [Cut2.lift, h]

theorem Cut2.lift_B (C : Cut2 P) (U : Fin X.n → Bool) (κ : Bool) {v : Fin X.n} (h : C.S v = false) :
    C.lift U κ v = κ := by simp [Cut2.lift, h]

theorem Cut2.lift_inA (C : Cut2 P) (U : Fin X.n → Bool) (κ : Bool) {f : Fin X.m} (hf : C.inA f) :
    C.lift U κ (X.ends f).1 = U (X.ends f).1 ∧ C.lift U κ (X.ends f).2 = U (X.ends f).2 :=
  ⟨C.lift_A U κ hf.2.1, C.lift_A U κ hf.2.2⟩

theorem Cut2.lift_flip (C : Cut2 P) (U : Fin X.n → Bool) (κ : Bool) {f : Fin X.m} (hf : C.flip.inA f) :
    C.lift U κ (X.ends f).1 = C.lift U κ (X.ends f).2 := by
  have h1 : C.S (X.ends f).1 = false := by have := hf.2.1; rw [Cut2.flip_S] at this; simpa using this
  have h2 : C.S (X.ends f).2 = false := by have := hf.2.2; rw [Cut2.flip_S] at this; simpa using this
  rw [C.lift_B U κ h1, C.lift_B U κ h2]

/-- the edge closure is connected -/
theorem Cut2.clo_connected (C : Cut2 P) (hcon : ConnectedOn P) : ConnectedOn C.clo := by
  intro U hU f g hf hg
  have h12 : U C.a1 = U C.a2 := by
    have := hU _ C.clo_last; rwa [addEdge_ends_new] at this
  let V := C.lift U (U C.a1)
  have hV : ∀ f, P f → V (X.ends f).1 = V (X.ends f).2 := by
    intro f hf
    show C.lift U (U C.a1) (X.ends f).1 = C.lift U (U C.a1) (X.ends f).2
    rcases C.cases_P hf with h | h | h
    · rw [(C.lift_inA U _ h).1, (C.lift_inA U _ h).2]
      have := hU _ (C.clo_old h); rwa [addEdge_ends_old] at this
    · exact C.lift_flip U _ h
    · rcases h with rfl | rfl
      · rcases C.e1_vals (C.lift U (U C.a1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
          simp [C.lift_A U _ C.sa1, C.lift_B U _ C.sb1]
      · rcases C.e2_vals (C.lift U (U C.a1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
          simp [C.lift_A U _ C.sa2, C.lift_B U _ C.sb2, h12]
  have hVe1 : V (X.ends C.e1).1 = U C.a1 := by
    show C.lift U (U C.a1) (X.ends C.e1).1 = U C.a1
    rcases C.e1_vals (C.lift U (U C.a1)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact C.lift_A U _ C.sa1
    · exact C.lift_B U _ C.sb1
  have key : ∀ i, C.clo i → U ((addEdge X C.a1 C.a2).ends i).1 = U C.a1 := by
    intro i hi
    rcases hi with rfl | ⟨d, rfl, hd⟩
    · rw [addEdge_ends_new]
    · rw [addEdge_ends_old, ← (C.lift_inA U (U C.a1) hd).1]
      exact (hcon V hV d C.e1 hd.1 C.P1).trans hVe1
  rw [key f hf, key g hg]

/-- the edge closure is bridgeless -/
theorem Cut2.clo_bridgeless (C : Cut2 P) (hbr : BridgelessOn P) : BridgelessOn C.clo := by
  intro e he B
  have sep := B.sep
  have hu := B.hu
  have hv := B.hv
  rcases he with rfl | ⟨d, rfl, hd⟩
  · rw [addEdge_ends_new] at hu hv
    let V := C.lift B.U true
    apply bridgeless_sep hbr C.P2 V
    · show C.lift B.U true (X.ends C.e2).1 ≠ C.lift B.U true (X.ends C.e2).2
      rcases C.e2_vals (C.lift B.U true) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        simp [C.lift_A B.U _ C.sa2, C.lift_B B.U _ C.sb2, hv]
    · intro f hf hfe
      show C.lift B.U true (X.ends f).1 = C.lift B.U true (X.ends f).2
      rcases C.cases_P hf with h | h | h
      · rw [(C.lift_inA B.U _ h).1, (C.lift_inA B.U _ h).2]
        have := sep (Fin.castSucc f) (C.clo_old h) (castSucc_ne_last f)
        rwa [addEdge_ends_old] at this
      · exact C.lift_flip B.U _ h
      · rcases h with rfl | rfl
        · rcases C.e1_vals (C.lift B.U true) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
            simp [C.lift_A B.U _ C.sa1, C.lift_B B.U _ C.sb1, hu]
        · exact absurd rfl hfe
  · have hl := sep (Fin.last X.m) C.clo_last (fun h => castSucc_ne_last d h.symm)
    rw [addEdge_ends_new] at hl
    rw [addEdge_ends_old] at hu hv
    have hdA := hd
    let V := C.lift B.U (B.U C.a1)
    apply bridgeless_sep hbr hdA.1 V
    · show C.lift B.U (B.U C.a1) (X.ends d).1 ≠ C.lift B.U (B.U C.a1) (X.ends d).2
      rw [(C.lift_inA B.U _ hdA).1, (C.lift_inA B.U _ hdA).2, hu, hv]; decide
    · intro f hf hfd
      show C.lift B.U (B.U C.a1) (X.ends f).1 = C.lift B.U (B.U C.a1) (X.ends f).2
      rcases C.cases_P hf with h | h | h
      · rw [(C.lift_inA B.U _ h).1, (C.lift_inA B.U _ h).2]
        have := sep (Fin.castSucc f) (C.clo_old h) (fun h' => hfd (castSucc_inj' h'))
        rwa [addEdge_ends_old] at this
      · exact C.lift_flip B.U _ h
      · rcases h with rfl | rfl
        · rcases C.e1_vals (C.lift B.U (B.U C.a1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
            simp [C.lift_A B.U _ C.sa1, C.lift_B B.U _ C.sb1]
        · rcases C.e2_vals (C.lift B.U (B.U C.a1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
            simp [C.lift_A B.U _ C.sa2, C.lift_B B.U _ C.sb2, hl]

open Classical in
/-- the map sending a cut edge to the new edge and every other edge to itself -/
noncomputable def Cut2.toClo (C : Cut2 P) (f : Fin X.m) : Fin (addEdge X C.a1 C.a2).m :=
  if C.isCut f then Fin.last X.m else Fin.castSucc f

theorem Cut2.toClo_cut (C : Cut2 P) {f : Fin X.m} (h : C.isCut f) : C.toClo f = Fin.last X.m := by
  simp [Cut2.toClo, h]
  rfl

theorem Cut2.toClo_old (C : Cut2 P) {f : Fin X.m} (h : ¬ C.isCut f) : C.toClo f = Fin.castSucc f := by
  simp [Cut2.toClo, h]
  rfl

/-- the edges of `P` at a vertex `x` of `A` correspond to the edges of the closure at `x` -/
theorem Cut2.toClo_props (C : Cut2 P) {f : Fin X.m} {x : Fin X.n} (hf : P f) (hx : X.Inc f x)
    (hs : C.S x = true) : C.clo (C.toClo f) ∧ (addEdge X C.a1 C.a2).Inc (C.toClo f) x := by
  by_cases hc : C.isCut f
  · rw [C.toClo_cut hc]
    exact ⟨C.clo_last, C.inc_last_of_cut hc hx hs⟩
  · rw [C.toClo_old hc]
    exact ⟨C.clo_old (C.inA_of_notcut hf hc hx hs), addEdge_inc_old.2 hx⟩

theorem Cut2.toClo_inj (C : Cut2 P) {f f' : Fin X.m} {x : Fin X.n} (hx : X.Inc f x) (hx' : X.Inc f' x)
    (h : C.toClo f = C.toClo f') : f = f' := by
  by_cases hc : C.isCut f <;> by_cases hc' : C.isCut f'
  · apply Classical.byContradiction; intro hne; exact C.cut_disj hc hc' hne hx hx'
  · rw [C.toClo_cut hc, C.toClo_old hc'] at h; exact absurd h.symm (castSucc_ne_last f')
  · rw [C.toClo_old hc, C.toClo_cut hc'] at h; exact absurd h (castSucc_ne_last f)
  · rw [C.toClo_old hc, C.toClo_old hc'] at h; exact castSucc_inj' h

/-- the edge closure is cubic -/
theorem Cut2.clo_cubic (C : Cut2 P) (hcub : CubicOn P) : CubicOn C.clo := by
  intro x ⟨i, hi, hix⟩
  have hs : C.S x = true := C.clo_side hi hix
  have hxP : ∃ f, P f ∧ X.Inc f x := by
    rcases hi with rfl | ⟨d, rfl, hd⟩
    · rcases (C.inc_new_iff).1 hix with rfl | rfl
      · exact ⟨C.e1, C.P1, joins_inc_left C.j1⟩
      · exact ⟨C.e2, C.P2, joins_inc_left C.j2⟩
    · exact ⟨d, hd.1, addEdge_inc_old.1 hix⟩
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub x hxP
  obtain ⟨cp, jp⟩ := C.toClo_props hp ip hs
  obtain ⟨cq, jq⟩ := C.toClo_props hq iq hs
  obtain ⟨cr, jr⟩ := C.toClo_props hr ir hs
  refine ⟨C.toClo p, C.toClo q, C.toClo r, cp, cq, cr, jp, jq, jr,
    fun h => dpq (C.toClo_inj ip iq h), fun h => dpr (C.toClo_inj ip ir h), fun h => dqr (C.toClo_inj iq ir h), ?_⟩
  intro j hj hjx
  have cover : ∀ f, P f → X.Inc f x → C.toClo f = C.toClo p ∨ C.toClo f = C.toClo q ∨ C.toClo f = C.toClo r := by
    intro f hf hfx
    rcases hall f hf hfx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hj with rfl | ⟨d, rfl, hd⟩
  · rcases (C.inc_new_iff).1 hjx with rfl | rfl
    · rw [← C.toClo_cut (Or.inl rfl)]; exact cover _ C.P1 (joins_inc_left C.j1)
    · rw [← C.toClo_cut (Or.inr rfl)]; exact cover _ C.P2 (joins_inc_left C.j2)
  · rw [← C.toClo_old (C.not_inA_of_cut · hd)]
    exact cover d hd.1 (addEdge_inc_old.1 hjx)

theorem Cut2.clo_loopless (C : Cut2 P) (hloop : Loopless X) : Loopless (addEdge X C.a1 C.a2) :=
  addEdge_loopless hloop C.ha

/-! ### the digon closure -/

/-- the ambient multigraph of the digon closure of side `A`: two new edges joining `b1` and `b2` -/
def Cut2.XD (C : Cut2 P) : MGraph := addEdge (addEdge X C.b1 C.b2) C.b1 C.b2

/-- an old edge in the digon ambient -/
def Cut2.oD (C : Cut2 P) (d : Fin X.m) : Fin C.XD.m := Fin.castSucc (Fin.castSucc d)
/-- the two new parallel edges `δ`, `δ′` -/
def Cut2.dl1 (C : Cut2 P) : Fin C.XD.m := Fin.castSucc (Fin.last X.m)
def Cut2.dl2 (C : Cut2 P) : Fin C.XD.m := Fin.last (addEdge X C.b1 C.b2).m

/-- the digon closure `G_A^D` as an edge set of `C.XD` -/
def Cut2.cloD (C : Cut2 P) : Fin C.XD.m → Prop :=
  fun i => i = C.dl1 ∨ i = C.dl2 ∨ ∃ d, i = C.oD d ∧ C.pole d

theorem Cut2.XD_ends_old (C : Cut2 P) (d : Fin X.m) : C.XD.ends (C.oD d) = X.ends d := by
  exact (addEdge_ends_old (G := addEdge X C.b1 C.b2) (Fin.castSucc d)).trans (addEdge_ends_old d)

theorem Cut2.XD_ends_dl1 (C : Cut2 P) : C.XD.ends C.dl1 = (C.b1, C.b2) := by
  exact (addEdge_ends_old (G := addEdge X C.b1 C.b2) (Fin.last X.m)).trans addEdge_ends_new

theorem Cut2.XD_ends_dl2 (C : Cut2 P) : C.XD.ends C.dl2 = (C.b1, C.b2) := addEdge_ends_new

theorem Cut2.XD_cases (C : Cut2 P) (i : Fin C.XD.m) : i = C.dl2 ∨ i = C.dl1 ∨ ∃ d, i = C.oD d := by
  rcases addEdge_cases (G := addEdge X C.b1 C.b2) (u := C.b1) (w := C.b2) i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · rcases addEdge_cases (G := X) (u := C.b1) (w := C.b2) j with h | ⟨d, rfl⟩
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr ⟨d, rfl⟩)

theorem Cut2.oD_inj (C : Cut2 P) {d d' : Fin X.m} (h : C.oD d = C.oD d') : d = d' :=
  castSucc_inj' (castSucc_inj' h)
theorem Cut2.oD_ne_dl1 (C : Cut2 P) (d : Fin X.m) : C.oD d ≠ C.dl1 :=
  fun h => castSucc_ne_last d (castSucc_inj' h)
theorem Cut2.oD_ne_dl2 (C : Cut2 P) (d : Fin X.m) : C.oD d ≠ C.dl2 :=
  castSucc_ne_last _
theorem Cut2.dl1_ne_dl2 (C : Cut2 P) : C.dl1 ≠ C.dl2 := castSucc_ne_last _

theorem Cut2.XD_joins_old (C : Cut2 P) {d : Fin X.m} {x y : Fin X.n} :
    C.XD.Joins (C.oD d) x y ↔ X.Joins d x y := by
  unfold Joins; rw [C.XD_ends_old]; exact Iff.rfl
theorem Cut2.XD_inc_old (C : Cut2 P) {d : Fin X.m} {x : Fin X.n} : C.XD.Inc (C.oD d) x ↔ X.Inc d x := by
  unfold Inc; rw [C.XD_ends_old]; exact Iff.rfl
theorem Cut2.XD_inc_dl1 (C : Cut2 P) {x : Fin X.n} : C.XD.Inc C.dl1 x ↔ x = C.b1 ∨ x = C.b2 := by
  unfold Inc; rw [C.XD_ends_dl1]
  exact ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
theorem Cut2.XD_inc_dl2 (C : Cut2 P) {x : Fin X.n} : C.XD.Inc C.dl2 x ↔ x = C.b1 ∨ x = C.b2 := by
  unfold Inc; rw [C.XD_ends_dl2]
  exact ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
theorem Cut2.XD_joins_dl1 (C : Cut2 P) : C.XD.Joins C.dl1 C.b1 C.b2 := Or.inl C.XD_ends_dl1
theorem Cut2.XD_joins_dl2 (C : Cut2 P) : C.XD.Joins C.dl2 C.b1 C.b2 := Or.inl C.XD_ends_dl2

theorem Cut2.XD_loopless (C : Cut2 P) (hloop : Loopless X) : Loopless C.XD :=
  addEdge_loopless (addEdge_loopless hloop C.hb) C.hb

theorem Cut2.cloD_old_iff (C : Cut2 P) {d : Fin X.m} : C.cloD (C.oD d) ↔ C.pole d := by
  constructor
  · rintro (h | h | ⟨d', h, hd'⟩)
    · exact absurd h (C.oD_ne_dl1 d)
    · exact absurd h (C.oD_ne_dl2 d)
    · rw [C.oD_inj h]; exact hd'
  · exact fun h => Or.inr (Or.inr ⟨d, rfl, h⟩)

/-- the digon closure is connected -/
theorem Cut2.cloD_connected (C : Cut2 P) (hcon : ConnectedOn P) : ConnectedOn C.cloD := by
  intro U hU f g hf hg
  have hbb : U C.b1 = U C.b2 := by have := hU _ (Or.inl rfl); rwa [C.XD_ends_dl1] at this
  have he1 : U (X.ends C.e1).1 = U (X.ends C.e1).2 := by
    have := hU _ ((C.cloD_old_iff).2 (Or.inr (Or.inl rfl))); rwa [C.XD_ends_old] at this
  have he2 : U (X.ends C.e2).1 = U (X.ends C.e2).2 := by
    have := hU _ ((C.cloD_old_iff).2 (Or.inr (Or.inr rfl))); rwa [C.XD_ends_old] at this
  have ha1 : U C.a1 = U C.b1 := by
    rcases C.e1_vals U with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at he1
    · exact he1
    · exact he1.symm
  have ha2 : U C.a2 = U C.b2 := by
    rcases C.e2_vals U with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at he2
    · exact he2
    · exact he2.symm
  let V := C.lift U (U C.b1)
  have hV : ∀ f, P f → V (X.ends f).1 = V (X.ends f).2 := by
    intro f hf
    show C.lift U (U C.b1) (X.ends f).1 = C.lift U (U C.b1) (X.ends f).2
    rcases C.cases_P hf with h | h | h
    · rw [(C.lift_inA U _ h).1, (C.lift_inA U _ h).2]
      have := hU _ ((C.cloD_old_iff).2 (Or.inl h)); rwa [C.XD_ends_old] at this
    · exact C.lift_flip U _ h
    · rcases h with rfl | rfl
      · rcases C.e1_vals (C.lift U (U C.b1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
          simp [C.lift_A U _ C.sa1, C.lift_B U _ C.sb1, ha1]
      · rcases C.e2_vals (C.lift U (U C.b1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
          simp [C.lift_A U _ C.sa2, C.lift_B U _ C.sb2, ha2, hbb]
  have hVe1 : V (X.ends C.e1).1 = U C.b1 := by
    show C.lift U (U C.b1) (X.ends C.e1).1 = U C.b1
    rcases C.e1_vals (C.lift U (U C.b1)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · rw [C.lift_A U _ C.sa1, ha1]
    · exact C.lift_B U _ C.sb1
  have key : ∀ i, C.cloD i → U (C.XD.ends i).1 = U C.b1 := by
    intro i hi
    rcases hi with rfl | rfl | ⟨d, rfl, hd⟩
    · rw [C.XD_ends_dl1]
    · rw [C.XD_ends_dl2]
    · rw [C.XD_ends_old]
      rcases hd with hd | hd
      · rw [← (C.lift_inA U (U C.b1) hd).1]
        exact (hcon V hV d C.e1 hd.1 C.P1).trans hVe1
      · rcases hd with rfl | rfl
        · rcases C.e1_vals U with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
          exact ha1
        · rcases C.e2_vals U with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
          · rw [ha2, hbb]
          · exact hbb.symm
  rw [key f hf, key g hg]

/-- the digon closure is bridgeless -/
theorem Cut2.cloD_bridgeless (C : Cut2 P) (hbr : BridgelessOn P) : BridgelessOn C.cloD := by
  intro e he B
  have sep := B.sep
  have hu := B.hu
  have hv := B.hv
  rcases he with rfl | rfl | ⟨d, rfl, hd⟩
  · have := sep _ (Or.inr (Or.inl rfl)) (Ne.symm C.dl1_ne_dl2)
    rw [C.XD_ends_dl2] at this
    rw [C.XD_ends_dl1] at hu hv
    rw [hu, hv] at this; exact absurd this (by decide)
  · have := sep _ (Or.inl rfl) C.dl1_ne_dl2
    rw [C.XD_ends_dl1] at this
    rw [C.XD_ends_dl2] at hu hv
    rw [hu, hv] at this; exact absurd this (by decide)
  · rw [C.XD_ends_old] at hu hv
    have hbb : B.U C.b1 = B.U C.b2 := by
      have := sep _ (Or.inl rfl) (C.oD_ne_dl1 d).symm; rwa [C.XD_ends_dl1] at this
    -- the lifted labelling agrees with `B.U` on the ends of every pole edge
    let V := C.lift B.U (B.U C.b1)
    have agree : ∀ f, C.pole f → V (X.ends f).1 = B.U (X.ends f).1 ∧ V (X.ends f).2 = B.U (X.ends f).2 := by
      have hVa : ∀ v, C.S v = true → V v = B.U v := fun v hv => C.lift_A B.U _ hv
      have hVb1 : V C.b1 = B.U C.b1 := C.lift_B B.U _ C.sb1
      have hVb2 : V C.b2 = B.U C.b2 := (C.lift_B B.U _ C.sb2).trans hbb
      intro f hf
      rcases hf with h | h
      · exact C.lift_inA B.U _ h
      · rcases h with rfl | rfl
        · rcases C.j1 with h | h <;> rw [h]
          · exact ⟨hVa _ C.sa1, hVb1⟩
          · exact ⟨hVb1, hVa _ C.sa1⟩
        · rcases C.j2 with h | h <;> rw [h]
          · exact ⟨hVa _ C.sa2, hVb2⟩
          · exact ⟨hVb2, hVa _ C.sa2⟩
    apply bridgeless_sep hbr (C.pole_P hd) V
    · rw [(agree d hd).1, (agree d hd).2, hu, hv]; decide
    · intro f hf hfd
      by_cases hp : C.pole f
      · rw [(agree f hp).1, (agree f hp).2]
        have := sep _ ((C.cloD_old_iff).2 hp) (fun h => hfd (C.oD_inj h))
        rwa [C.XD_ends_old] at this
      · rcases C.cases_P hf with h | h | h
        · exact absurd (Or.inl h) hp
        · exact C.lift_flip B.U _ h
        · exact absurd (Or.inr h) hp

/-- the vertices of the digon closure are those of `A` and `b1, b2` -/
theorem Cut2.cloD_vertex (C : Cut2 P) {i : Fin C.XD.m} (hi : C.cloD i) {x : Fin X.n} (hx : C.XD.Inc i x) :
    C.S x = true ∨ x = C.b1 ∨ x = C.b2 := by
  rcases hi with rfl | rfl | ⟨d, rfl, hd⟩
  · exact Or.inr ((C.XD_inc_dl1).1 hx)
  · exact Or.inr ((C.XD_inc_dl2).1 hx)
  · have hx' := (C.XD_inc_old).1 hx
    rcases hd with hd | hd
    · exact Or.inl (C.side_of_inA hd hx')
    · rcases hd with rfl | rfl
      · rcases C.inc_e1 hx' with rfl | rfl
        · exact Or.inl C.sa1
        · exact Or.inr (Or.inl rfl)
      · rcases C.inc_e2 hx' with rfl | rfl
        · exact Or.inl C.sa2
        · exact Or.inr (Or.inr rfl)

/-- the digon closure is cubic -/
theorem Cut2.cloD_cubic (C : Cut2 P) (hcub : CubicOn P) : CubicOn C.cloD := by
  intro x ⟨i, hi, hix⟩
  -- at a digon vertex `b`: the edges are the cut edge `e` at `b`, `δ` and `δ′`
  have atb : ∀ (e : Fin X.m) (b : Fin X.n), C.isCut e → X.Inc e b → C.S b = false → (b = C.b1 ∨ b = C.b2) →
      ∃ a b' c, C.cloD a ∧ C.cloD b' ∧ C.cloD c ∧ C.XD.Inc a b ∧ C.XD.Inc b' b ∧ C.XD.Inc c b ∧
        a ≠ b' ∧ a ≠ c ∧ b' ≠ c ∧ ∀ d, C.cloD d → C.XD.Inc d b → d = a ∨ d = b' ∨ d = c := by
    intro e b he heb hb hb12
    refine ⟨C.oD e, C.dl1, C.dl2, (C.cloD_old_iff).2 (Or.inr he), Or.inl rfl, Or.inr (Or.inl rfl),
      (C.XD_inc_old).2 heb, (C.XD_inc_dl1).2 hb12, (C.XD_inc_dl2).2 hb12, C.oD_ne_dl1 e, C.oD_ne_dl2 e,
      C.dl1_ne_dl2, ?_⟩
    intro j hj hjb
    rcases hj with rfl | rfl | ⟨d, rfl, hd⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · have hdb := (C.XD_inc_old).1 hjb
      rcases hd with hd | hd
      · have := C.side_of_inA hd hdb; rw [hb] at this; exact absurd this (by decide)
      · by_cases hde : d = e
        · exact Or.inl (by rw [hde])
        · exact absurd (C.cut_disj hd he hde hdb heb) id
  rcases C.cloD_vertex hi hix with hs | rfl | rfl
  · have hxP : ∃ f, P f ∧ X.Inc f x := by
      rcases hi with rfl | rfl | ⟨d, rfl, hd⟩
      · rcases (C.XD_inc_dl1).1 hix with rfl | rfl
        · rw [C.sb1] at hs; exact absurd hs (by decide)
        · rw [C.sb2] at hs; exact absurd hs (by decide)
      · rcases (C.XD_inc_dl2).1 hix with rfl | rfl
        · rw [C.sb1] at hs; exact absurd hs (by decide)
        · rw [C.sb2] at hs; exact absurd hs (by decide)
      · exact ⟨d, C.pole_P hd, (C.XD_inc_old).1 hix⟩
    obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub x hxP
    refine ⟨C.oD p, C.oD q, C.oD r, (C.cloD_old_iff).2 (C.pole_of_inc hp ip hs),
      (C.cloD_old_iff).2 (C.pole_of_inc hq iq hs), (C.cloD_old_iff).2 (C.pole_of_inc hr ir hs),
      (C.XD_inc_old).2 ip, (C.XD_inc_old).2 iq, (C.XD_inc_old).2 ir,
      fun h => dpq (C.oD_inj h), fun h => dpr (C.oD_inj h), fun h => dqr (C.oD_inj h), ?_⟩
    intro j hj hjx
    rcases hj with rfl | rfl | ⟨d, rfl, hd⟩
    · rcases (C.XD_inc_dl1).1 hjx with rfl | rfl
      · rw [C.sb1] at hs; exact absurd hs (by decide)
      · rw [C.sb2] at hs; exact absurd hs (by decide)
    · rcases (C.XD_inc_dl2).1 hjx with rfl | rfl
      · rw [C.sb1] at hs; exact absurd hs (by decide)
      · rw [C.sb2] at hs; exact absurd hs (by decide)
    · rcases hall d (C.pole_P hd) ((C.XD_inc_old).1 hjx) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · exact atb C.e1 C.b1 (Or.inl rfl) (joins_inc_right C.j1) C.sb1 (Or.inl rfl)
  · exact atb C.e2 C.b2 (Or.inr rfl) (joins_inc_right C.j2) C.sb2 (Or.inr rfl)

end cl0

end RH2F

-- ===== from RH2CL.lean =====
/-
  RH2CL.lean — Lemma CL (fact ecc9734f558cf885), parts (CL1)–(CL4), in Lean 4.20 core, in the pole encoding:
  star colourings of the edge closure `G_A` or of the digon closure `G_A^D` restrict to star colourings of the
  2-pole `A⁺ = E(G[A]) ∪ {e1, e2}`.
  * `pole_of_clo`  : (CL1), (CL2) — a cut edge gets the colour of the new edge `g_A` (`c ∘ C.toClo`).
  * `pole_of_cloD` : (CL3), (CL4) — the pole is a sub-edge-set of the digon closure (`c ∘ C.oD`).
  * `cl4_pend`     : (CL4) — if `δ ∈ N` then the cut edges are not in `N` and get different colours.
  * `cl3_both`, `cl3_meet` : (CL3) — if `e1 ∈ N` then `e2 ∈ N`, and the F-colour pairs at `a1`, `a2` intersect.
-/

namespace RH2F
open MGraph

section cl
variable {X : MGraph} {P : Fin X.m → Prop}

/-- a pole edge at a vertex of `B` is a cut edge -/
theorem Cut2.pole_cut_of_B (C : Cut2 P) {f : Fin X.m} (hf : C.pole f) {x : Fin X.n} (hx : X.Inc f x)
    (hs : C.S x = false) : C.isCut f := by
  rcases hf with h | h
  · have := C.side_of_inA h hx; rw [hs] at this; exact absurd this (by decide)
  · exact h

/-- a cut edge and a different pole edge meet only at the `A`-end -/
theorem Cut2.pole_meet_A (C : Cut2 P) {e f : Fin X.m} (he : C.isCut e) (hf : C.pole f) (hne : e ≠ f)
    {v : Fin X.n} (hev : X.Inc e v) (hfv : X.Inc f v) : C.S v = true := by
  cases hs : C.S v
  · exact absurd (C.cut_disj he (C.pole_cut_of_B hf hfv hs) hne hev hfv) id
  · rfl

/-- the walk case "first edge is a cut edge" of `pole_of_clo` -/
theorem Cut2.pole_clo_first (C : Cut2 P) {k : Nat} (c : Fin (addEdge X C.a1 C.a2).m → Fin k)
    (hc : StarOn C.clo k c) (w : X.Walk4) (c1 : C.isCut w.e1) (i2 : C.inA w.e2) (i3 : C.inA w.e3)
    (h4 : C.pole w.e4) (hb : Bicol (fun f => c (C.toClo f)) w) : False := by
  have hv1 : C.S w.v1 = true := C.side_of_inA i2 w.inc_e2_v1
  have hv3 : C.S w.v3 = true := C.side_of_inA i3 w.inc_e3_v3
  have nc3 : ¬ C.isCut w.e3 := fun h => C.not_inA_of_cut h i3
  have hb1 : c (Fin.last X.m) = c (Fin.castSucc w.e3) := by
    have := hb.1; simp only [C.toClo_cut c1, C.toClo_old nc3] at this; exact this
  -- the other `A`-end `u` of a cut edge
  have key : ∃ u, u ≠ w.v1 ∧ (addEdge X C.a1 C.a2).Joins (Fin.last X.m) u w.v1 ∧
      ∀ e, C.isCut e → e ≠ w.e1 → X.Inc e w.v3 → w.v3 = u := by
    rcases C.cutA c1 w.inc_e1_v1 hv1 with ⟨he, hv⟩ | ⟨he, hv⟩
    · refine ⟨C.a2, by rw [hv]; exact Ne.symm C.ha, by rw [hv]; exact Or.symm addEdge_joins_new, ?_⟩
      intro e hce hne hev3
      rcases C.cutA hce hev3 hv3 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd (h.trans he.symm) hne
      · exact h
    · refine ⟨C.a1, by rw [hv]; exact C.ha, by rw [hv]; exact addEdge_joins_new, ?_⟩
      intro e hce hne hev3
      rcases C.cutA hce hev3 hv3 with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd (h.trans he.symm) hne
  obtain ⟨u, huv1, hj, hcut4⟩ := key
  have hlu : (addEdge X C.a1 C.a2).Inc (Fin.last X.m) u := joins_inc_left hj
  have near : ∀ v, X.Inc w.e3 v → v ≠ u := by
    intro v hv hvu
    apply hc.1 (Fin.last X.m) (Fin.castSucc w.e3)
      ⟨fun h => castSucc_ne_last w.e3 h.symm, u, hlu, addEdge_inc_old.2 (hvu ▸ hv)⟩ C.clo_last (C.clo_old i3) hb1
  have hu2 : u ≠ w.v2 := fun h => near w.v2 w.inc_e3_v2 h.symm
  have hu3 : u ≠ w.v3 := fun h => near w.v3 w.inc_e3_v3 h.symm
  have nc4 : ¬ C.isCut w.e4 := fun h => hu3 (hcut4 _ h (fun h' => w.e1_ne_e4 h'.symm) w.inc_e4_v3).symm
  have i4 : C.inA w.e4 := h4.resolve_right nc4
  have nc2 : ¬ C.isCut w.e2 := fun h => C.not_inA_of_cut h i2
  let W : (addEdge X C.a1 C.a2).Walk4 :=
    { v0 := u, v1 := w.v1, v2 := w.v2, v3 := w.v3, v4 := w.v4
      e1 := Fin.last X.m, e2 := Fin.castSucc w.e2, e3 := Fin.castSucc w.e3, e4 := Fin.castSucc w.e4
      h1 := hj, h2 := addEdge_joins_old.2 w.h2, h3 := addEdge_joins_old.2 w.h3, h4 := addEdge_joins_old.2 w.h4
      d01 := huv1, d02 := hu2, d03 := hu3, d12 := w.d12, d13 := w.d13, d14 := w.d14, d23 := w.d23
      d24 := w.d24, d34 := w.d34 }
  apply hc.2 W C.clo_last (C.clo_old i2) (C.clo_old i3) (C.clo_old i4)
  refine ⟨hb1, ?_⟩
  have := hb.2; simp only [C.toClo_old nc2, C.toClo_old nc4] at this; exact this

/-- **(CL1), (CL2)**: a star colouring `c` of the edge closure gives the star colouring `c ∘ toClo` of the pole
    (the cut edges get the colour of the new edge `g_A`) -/
theorem Cut2.pole_of_clo (C : Cut2 P) {k : Nat} (c : Fin (addEdge X C.a1 C.a2).m → Fin k)
    (hc : StarOn C.clo k c) : StarOn C.pole k (fun f => c (C.toClo f)) := by
  constructor
  · intro a b hab ha hb heq
    obtain ⟨hne, x, hax, hbx⟩ := hab
    cases hs : C.S x
    · exact C.cut_disj (C.pole_cut_of_B ha hax hs) (C.pole_cut_of_B hb hbx hs) hne hax hbx
    · obtain ⟨ca, ia⟩ := C.toClo_props (C.pole_P ha) hax hs
      obtain ⟨cb, ib⟩ := C.toClo_props (C.pole_P hb) hbx hs
      exact hc.1 _ _ ⟨fun h => hne (C.toClo_inj hax hbx h), x, ia, ib⟩ ca cb heq
  · intro w h1 h2 h3 h4 hb
    -- the two middle edges are not cut edges
    have nc2 : ¬ C.isCut w.e2 := by
      intro hc2
      have s1 := C.pole_meet_A hc2 h1 w.e1_ne_e2.symm w.inc_e2_v1 w.inc_e1_v1
      have s2 := C.pole_meet_A hc2 h3 w.e2_ne_e3 w.inc_e2_v2 w.inc_e3_v2
      rcases C.cut_sides hc2 w.h2 with ⟨_, h⟩ | ⟨h, _⟩
      · rw [s2] at h; exact absurd h (by decide)
      · rw [s1] at h; exact absurd h (by decide)
    have nc3 : ¬ C.isCut w.e3 := by
      intro hc3
      have s2 := C.pole_meet_A hc3 h2 w.e2_ne_e3.symm w.inc_e3_v2 w.inc_e2_v2
      have s3 := C.pole_meet_A hc3 h4 w.e3_ne_e4 w.inc_e3_v3 w.inc_e4_v3
      rcases C.cut_sides hc3 w.h3 with ⟨_, h⟩ | ⟨h, _⟩
      · rw [s3] at h; exact absurd h (by decide)
      · rw [s2] at h; exact absurd h (by decide)
    have i2 : C.inA w.e2 := h2.resolve_right nc2
    have i3 : C.inA w.e3 := h3.resolve_right nc3
    by_cases c1 : C.isCut w.e1
    · exact C.pole_clo_first c hc w c1 i2 i3 h4 hb
    by_cases c4 : C.isCut w.e4
    · exact C.pole_clo_first c hc w.reverse c4 i3 i2 h1 (bicol_rev w hb)
    have i1 : C.inA w.e1 := h1.resolve_right c1
    have i4 : C.inA w.e4 := h4.resolve_right c4
    let W : (addEdge X C.a1 C.a2).Walk4 :=
      { v0 := w.v0, v1 := w.v1, v2 := w.v2, v3 := w.v3, v4 := w.v4
        e1 := Fin.castSucc w.e1, e2 := Fin.castSucc w.e2, e3 := Fin.castSucc w.e3, e4 := Fin.castSucc w.e4
        h1 := addEdge_joins_old.2 w.h1, h2 := addEdge_joins_old.2 w.h2, h3 := addEdge_joins_old.2 w.h3
        h4 := addEdge_joins_old.2 w.h4
        d01 := w.d01, d02 := w.d02, d03 := w.d03, d12 := w.d12, d13 := w.d13, d14 := w.d14, d23 := w.d23
        d24 := w.d24, d34 := w.d34 }
    apply hc.2 W (C.clo_old i1) (C.clo_old i2) (C.clo_old i3) (C.clo_old i4)
    refine ⟨?_, ?_⟩
    · show c (Fin.castSucc w.e1) = c (Fin.castSucc w.e3)
      have := hb.1; simp only [C.toClo_old c1, C.toClo_old nc3] at this; exact this
    · show c (Fin.castSucc w.e2) = c (Fin.castSucc w.e4)
      have := hb.2; simp only [C.toClo_old nc2, C.toClo_old c4] at this; exact this

/-- **(CL3), (CL4)**: the pole is a sub-edge-set of the digon closure -/
theorem Cut2.pole_of_cloD (C : Cut2 P) {k : Nat} (c : Fin C.XD.m → Fin k) (hc : StarOn C.cloD k c) :
    StarOn C.pole k (fun f => c (C.oD f)) :=
  starOn_embed (G := X) (H := C.XD) (fun x => x) C.oD (fun _ _ _ _ _ _ _ _ h => h)
    (fun _ _ _ _ h => C.oD_inj h) (fun _ ha => (C.cloD_old_iff).2 ha)
    (fun a _ => (C.XD_joins_old).2 (joins_ends a)) hc

theorem Cut2.dl_ne_A (C : Cut2 P) {x : Fin X.n} (hx : C.S x = true) : ¬ (x = C.b1 ∨ x = C.b2) := by
  rintro (rfl | rfl)
  · rw [C.sb1] at hx; exact absurd hx (by decide)
  · rw [C.sb2] at hx; exact absurd hx (by decide)

/-- the matching edge at a vertex `y ∈ A` of the digon closure is an old edge `oD d` of the pole -/
theorem Cut2.cloD_N_at_A (C : Cut2 P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N) {y : Fin X.n}
    (hy : C.S y = true) (hyP : ∃ f, C.pole f ∧ X.Inc f y) :
    ∃ d, N (C.oD d) ∧ C.pole d ∧ X.Inc d y ∧ ∀ j, N j → C.XD.Inc j y → j = C.oD d := by
  obtain ⟨f, hf, hfy⟩ := hyP
  obtain ⟨a, ha, hay, hu⟩ := hN.2 y ⟨C.oD f, (C.cloD_old_iff).2 hf, (C.XD_inc_old).2 hfy⟩
  rcases C.XD_cases a with rfl | rfl | ⟨d, rfl⟩
  · exact absurd ((C.XD_inc_dl2).1 hay) (C.dl_ne_A hy)
  · exact absurd ((C.XD_inc_dl1).1 hay) (C.dl_ne_A hy)
  · exact ⟨d, ha, (C.cloD_old_iff).1 (hN.1 _ ha), (C.XD_inc_old).1 hay, hu⟩

/-- **(CL4)**: if `δ ∈ N`, the cut edges are not in `N` and have different colours -/
theorem Cut2.cl4_pend (C : Cut2 P) (hloop : Loopless X) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N)
    (hδ : N C.dl1) (c : Fin C.XD.m → Fin 6) (hc : MC5 C.cloD N c) :
    ¬ N (C.oD C.e1) ∧ ¬ N (C.oD C.e2) ∧ c (C.oD C.e1) ≠ c (C.oD C.e2) := by
  have n1 : ¬ N (C.oD C.e1) := fun h =>
    C.oD_ne_dl1 _ (pm_unique hN h hδ ((C.XD_inc_old).2 (joins_inc_right C.j1)) ((C.XD_inc_dl1).2 (Or.inl rfl)))
  have n2 : ¬ N (C.oD C.e2) := fun h =>
    C.oD_ne_dl1 _ (pm_unique hN h hδ ((C.XD_inc_old).2 (joins_inc_right C.j2)) ((C.XD_inc_dl1).2 (Or.inr rfl)))
  refine ⟨n1, n2, fun heq => ?_⟩
  obtain ⟨d, hdN, hdp, hda2, _⟩ := C.cloD_N_at_A hN C.sa2 ⟨C.e2, Or.inr (Or.inr rfl), joins_inc_left C.j2⟩
  have hde2 : d ≠ C.e2 := fun h => n2 (h ▸ hdN)
  have hdcut : ¬ C.isCut d := by
    rintro (rfl | rfl)
    · rcases C.inc_e1 hda2 with h | h
      · exact C.ha h.symm
      · exact C.a2_ne_b1 h
    · exact hde2 rfl
  have hdA : C.inA d := hdp.resolve_right hdcut
  obtain ⟨z, hz⟩ := joins_of_inc hda2
  have hzA : C.S z = true := C.side_of_inA hdA (joins_inc_right hz)
  have ne_b : ∀ v, C.S v = true → v ≠ C.b1 ∧ v ≠ C.b2 := fun v hv =>
    ⟨fun h => by rw [h, C.sb1] at hv; exact absurd hv (by decide),
     fun h => by rw [h, C.sb2] at hv; exact absurd hv (by decide)⟩
  let W : C.XD.Walk4 :=
    { v0 := C.a1, v1 := C.b1, v2 := C.b2, v3 := C.a2, v4 := z
      e1 := C.oD C.e1, e2 := C.dl1, e3 := C.oD C.e2, e4 := C.oD d
      h1 := (C.XD_joins_old).2 C.j1, h2 := C.XD_joins_dl1, h3 := (C.XD_joins_old).2 (Or.symm C.j2)
      h4 := (C.XD_joins_old).2 hz
      d01 := C.a1_ne_b1, d02 := C.a1_ne_b2, d03 := C.ha, d12 := C.hb, d13 := fun h => C.a2_ne_b1 h.symm
      d14 := fun h => (ne_b z hzA).1 h.symm, d23 := fun h => C.a2_ne_b2 h.symm
      d24 := fun h => (ne_b z hzA).2 h.symm, d34 := ne_of_joins hloop hz }
  apply hc.1.2 W ((C.cloD_old_iff).2 (Or.inr (Or.inl rfl))) (Or.inl rfl) ((C.cloD_old_iff).2 (Or.inr (Or.inr rfl)))
    ((C.cloD_old_iff).2 hdp)
  exact ⟨heq, ((hc.2 _ (Or.inl rfl)).1 hδ).trans ((hc.2 _ (hN.1 _ hdN)).1 hdN).symm⟩

end cl

end RH2F

-- ===== from RH2EX1.lean =====
/-
  RH2EX1.lean — EX1-goodness and gluing of perfect matchings across a 2-edge-cut (Lean 4.20 core).

  * `EX1On P` (EX1-good, fact 0e90cbc9a9e79513), `InG X P` (connected bridgeless loopless cubic), `PStat` (part (P) of
    fact f6e8c173bef4cfa1: in such a `P` every edge has both statuses realized by perfect matchings).
  * `ex1_full` : under `PStat`, an EX1-good member of 𝒢 has, for every edge and status, a perfect matching with that
    status which is the colour class `5` of a star 6-colouring.
  * `CoverA`, `pm_glue` : perfect matchings of the two sides glue to a perfect matching of `P`.
  * `clo_inG`, `cloD_inG` : the closures lie in 𝒢 (Lemma CL(0)).
-/

namespace RH2F
open MGraph

section ex1
variable {X : MGraph}

/-- EX1-good: for every edge `g` of `P` and every status `t` realised by some perfect matching, some perfect matching
    with that status is a colour class of a star 6-colouring of `P` -/
def EX1On (P : Fin X.m → Prop) : Prop :=
  ∀ g, P g → ∀ t : Bool, (∃ N, PMOn P N ∧ (N g ↔ t = true)) →
    ∃ N, PMOn P N ∧ (N g ↔ t = true) ∧ ∃ c, StarOn P 6 c ∧ ClassOn P N c

end ex1

/-- membership in 𝒢: a connected bridgeless cubic edge set of a loopless multigraph -/
def InG (X : MGraph) (P : Fin X.m → Prop) : Prop :=
  Loopless X ∧ ConnectedOn P ∧ BridgelessOn P ∧ CubicOn P

/-- part (P) of fact f6e8c173bef4cfa1: in a member of 𝒢 both statuses of every edge are realised -/
def PStat : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → ∀ h, P h → ∀ t : Bool, ∃ N, PMOn P N ∧ (N h ↔ t = true)

section glue
variable {X : MGraph} {P : Fin X.m → Prop}

theorem ex1_full (hPS : PStat) {Y : MGraph} {Q : Fin Y.m → Prop} (hG : InG Y Q) (hE : EX1On Q)
    {h : Fin Y.m} (hh : Q h) (t : Bool) :
    ∃ N c, PMOn Q N ∧ (N h ↔ t = true) ∧ MC5 Q N c := by
  obtain ⟨N, hN, hst, c, hc, hcl⟩ := hE h hh t (hPS Y Q hG h hh t)
  obtain ⟨c', hc'⟩ := mc5_of_class hc hcl
  exact ⟨N, c', hN, hst, hc'⟩

theorem mc5_congr {Y : MGraph} {Q N N' : Fin Y.m → Prop} {c : Fin Y.m → Fin 6} (h : MC5 Q N c)
    (hNN : ∀ f, Q f → (N f ↔ N' f)) : MC5 Q N' c :=
  ⟨h.1, fun f hf => (hNN f hf).symm.trans (h.2 f hf)⟩

theorem Cut2.clo_inG (C : Cut2 P) (hG : InG X P) : InG (addEdge X C.a1 C.a2) C.clo :=
  ⟨C.clo_loopless hG.1, C.clo_connected hG.2.1, C.clo_bridgeless hG.2.2.1, C.clo_cubic hG.2.2.2⟩

theorem Cut2.cloD_inG (C : Cut2 P) (hG : InG X P) : InG C.XD C.cloD :=
  ⟨C.XD_loopless hG.1, C.cloD_connected hG.2.1, C.cloD_bridgeless hG.2.2.1, C.cloD_cubic hG.2.2.2⟩

/-- `NA` (a set of edges inside `A`) covers every vertex of `A` exactly once, except that for `s` it covers neither
    `a1` nor `a2` -/
def Cut2.CoverA (C : Cut2 P) (NA : Fin X.m → Prop) (s : Prop) : Prop :=
  ∀ x, C.S x = true → (∃ f, P f ∧ X.Inc f x) →
    ((s ∧ (x = C.a1 ∨ x = C.a2)) → ∀ d, C.inA d → NA d → ¬ X.Inc d x) ∧
    (¬ (s ∧ (x = C.a1 ∨ x = C.a2)) → ∃ d, C.inA d ∧ NA d ∧ X.Inc d x ∧
      ∀ d', C.inA d' → NA d' → X.Inc d' x → d' = d)

/-- the glued matching: `NA` inside `A`, `NB` inside `B`, and the cut edges iff `s` -/
def Cut2.glueN (C : Cut2 P) (NA NB : Fin X.m → Prop) (s : Prop) (f : Fin X.m) : Prop :=
  (C.inA f ∧ NA f) ∨ (C.flip.inA f ∧ NB f) ∨ (C.isCut f ∧ s)

theorem Cut2.glueN_A (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} {f : Fin X.m} (hf : C.inA f) :
    C.glueN NA NB s f ↔ NA f := by
  constructor
  · rintro (h | h | h)
    · exact h.2
    · exact absurd h.1 (C.not_flip_of_inA hf)
    · exact absurd hf (C.not_inA_of_cut h.1)
  · exact fun h => Or.inl ⟨hf, h⟩

theorem Cut2.glueN_B (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} {f : Fin X.m} (hf : C.flip.inA f) :
    C.glueN NA NB s f ↔ NB f := by
  constructor
  · rintro (h | h | h)
    · exact absurd hf (C.not_flip_of_inA h.1)
    · exact h.2
    · exact absurd hf (C.flip.not_inA_of_cut h.1)
  · exact fun h => Or.inr (Or.inl ⟨hf, h⟩)

theorem Cut2.glueN_cut (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} {f : Fin X.m} (hf : C.isCut f) :
    C.glueN NA NB s f ↔ s := by
  constructor
  · rintro (h | h | h)
    · exact absurd h.1 (C.not_inA_of_cut hf)
    · exact absurd h.1 (C.flip.not_inA_of_cut hf)
    · exact h.2
  · exact fun h => Or.inr (Or.inr ⟨hf, h⟩)

theorem Cut2.glueN_symm (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} (f : Fin X.m) :
    C.flip.glueN NB NA s f ↔ C.glueN NA NB s f := by
  unfold Cut2.glueN
  rw [show C.flip.flip.inA f ↔ C.inA f from C.flip_flip_inA_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- one side of `pm_glue`: every vertex of `A` meets exactly one glued matching edge -/
theorem Cut2.pm_glue_side (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} (hA : C.CoverA NA s)
    {x : Fin X.n} (hs : C.S x = true) (hx : ∃ f, P f ∧ X.Inc f x) :
    ∃ a, C.glueN NA NB s a ∧ X.Inc a x ∧ ∀ d, C.glueN NA NB s d → X.Inc d x → d = a := by
  classical
  by_cases hsx : s ∧ (x = C.a1 ∨ x = C.a2)
  · have hno := (hA x hs hx).1 hsx
    -- the cut edge at `x`
    have hcut : ∃ e, C.isCut e ∧ X.Inc e x := by
      rcases hsx.2 with rfl | rfl
      · exact ⟨C.e1, Or.inl rfl, joins_inc_left C.j1⟩
      · exact ⟨C.e2, Or.inr rfl, joins_inc_left C.j2⟩
    obtain ⟨e, he, hex⟩ := hcut
    refine ⟨e, Or.inr (Or.inr ⟨he, hsx.1⟩), hex, ?_⟩
    rintro d (hd | hd | hd) hdx
    · exact absurd hdx (hno d hd.1 hd.2)
    · have := C.flip.side_of_inA hd.1 hdx; rw [Cut2.flip_S, hs] at this; exact absurd this (by decide)
    · apply Classical.byContradiction; intro hne; exact C.cut_disj hd.1 he hne hdx hex
  · obtain ⟨d0, hd0, hNd0, hd0x, hu⟩ := (hA x hs hx).2 hsx
    refine ⟨d0, Or.inl ⟨hd0, hNd0⟩, hd0x, ?_⟩
    rintro d (hd | hd | hd) hdx
    · exact hu d hd.1 hd.2 hdx
    · have := C.flip.side_of_inA hd.1 hdx; rw [Cut2.flip_S, hs] at this; exact absurd this (by decide)
    · exfalso
      apply hsx
      refine ⟨hd.2, ?_⟩
      rcases C.cutA hd.1 hdx hs with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h

/-- **gluing perfect matchings**: covers of the two sides with the same cut status give a perfect matching -/
theorem Cut2.pm_glue (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} (hA : C.CoverA NA s)
    (hB : C.flip.CoverA NB s) : PMOn P (C.glueN NA NB s) := by
  constructor
  · rintro f (h | h | h)
    · exact h.1.1
    · exact h.1.1
    · rcases h.1 with rfl | rfl
      · exact C.P1
      · exact C.P2
  · intro x hx
    cases hs : C.S x
    · obtain ⟨a, ha, hax, hu⟩ := C.flip.pm_glue_side (NB := NA) hB (Cut2.flip_true hs) hx
      refine ⟨a, (C.glueN_symm a).1 ha, hax, fun d hd hdx => hu d ((C.glueN_symm d).2 hd) hdx⟩
    · exact C.pm_glue_side hA hs hx

/-- a perfect matching of the edge closure with status `s` at the new edge covers side `A` -/
theorem Cut2.coverA_of_clo (C : Cut2 P) {N : Fin (addEdge X C.a1 C.a2).m → Prop} (hN : PMOn C.clo N)
    {s : Prop} (hs : N (Fin.last X.m) ↔ s) : C.CoverA (fun d => N (Fin.castSucc d)) s := by
  intro x hxA hx
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨cf, icf⟩ := C.toClo_props hf hfx hxA
  obtain ⟨a, ha, hax, hu⟩ := hN.2 x ⟨_, cf, icf⟩
  constructor
  · rintro ⟨hs', hx12⟩ d hd hNd hdx
    have hlast : N (Fin.last X.m) := hs.2 hs'
    have := hu _ hlast ((C.inc_new_iff).2 hx12)
    have := (hu _ hNd (addEdge_inc_old.2 hdx)).trans this.symm
    exact castSucc_ne_last d this
  · intro hns
    rcases addEdge_cases a with rfl | ⟨d, rfl⟩
    · exact absurd ⟨hs.1 ha, (C.inc_new_iff).1 hax⟩ hns
    · refine ⟨d, (C.clo_old_iff).1 (hN.1 _ ha), ha, addEdge_inc_old.1 hax, ?_⟩
      intro d' _ hNd' hd'x
      exact castSucc_inj' (hu _ hNd' (addEdge_inc_old.2 hd'x))

/-- a perfect matching of the digon closure containing `δ` covers side `A` inside `A` -/
theorem Cut2.coverA_of_cloD (C : Cut2 P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N) (hδ : N C.dl1) :
    C.CoverA (fun d => N (C.oD d)) False := by
  have n1 : ¬ N (C.oD C.e1) := fun h =>
    C.oD_ne_dl1 _ (pm_unique hN h hδ ((C.XD_inc_old).2 (joins_inc_right C.j1)) ((C.XD_inc_dl1).2 (Or.inl rfl)))
  have n2 : ¬ N (C.oD C.e2) := fun h =>
    C.oD_ne_dl1 _ (pm_unique hN h hδ ((C.XD_inc_old).2 (joins_inc_right C.j2)) ((C.XD_inc_dl1).2 (Or.inr rfl)))
  intro x hxA hx
  refine ⟨fun h => h.1.elim, fun _ => ?_⟩
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨d, hNd, hdp, hdx, hu⟩ := C.cloD_N_at_A hN hxA ⟨f, C.pole_of_inc hf hfx hxA, hfx⟩
  have hdA : C.inA d := by
    rcases hdp with h | h
    · exact h
    · rcases h with rfl | rfl
      · exact absurd hNd n1
      · exact absurd hNd n2
  exact ⟨d, hdA, hNd, hdx, fun d' _ hNd' hd'x => C.oD_inj (hu _ hNd' ((C.XD_inc_old).2 hd'x))⟩

/-- the closure matching of the glued matching is the given closure matching -/
theorem Cut2.cloN_glue (C : Cut2 P) {N : Fin (addEdge X C.a1 C.a2).m → Prop} {NB : Fin X.m → Prop} {s : Prop}
    (hs : N (Fin.last X.m) ↔ s) :
    ∀ i, C.clo i → (N i ↔ C.cloN (C.glueN (fun d => N (Fin.castSucc d)) NB s) s i) := by
  intro i hi
  rcases hi with rfl | ⟨d, rfl, hd⟩
  · rw [C.cloN_last_iff]; exact hs
  · rw [C.cloN_old_iff, C.glueN_A hd]
    exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩

end glue

end RH2F

-- ===== from RH2EX2C.lean =====
/-
  RH2EX2C.lean — Lemma EX1-2C″ (fact 081a6e8977aebf8f) in Lean 4.20 core, with its Step 5 (the case of a matching
  rung joining `b1, b2`) as the named statement `Cut2.Step5`, discharged in RH2Step5.lean.
-/

namespace RH2F
open MGraph

section ex2c
variable {X : MGraph} {P : Fin X.m → Prop}

theorem ex1On_congr {Y : MGraph} {Q Q' : Fin Y.m → Prop} (h : ∀ i, Q i ↔ Q' i) (hE : EX1On Q) : EX1On Q' := by
  have pm : ∀ N, PMOn Q N → PMOn Q' N := fun N hN =>
    ⟨fun f hf => (h f).1 (hN.1 f hf), fun x ⟨f, hf, hfx⟩ => hN.2 x ⟨f, (h f).2 hf, hfx⟩⟩
  have pm' : ∀ N, PMOn Q' N → PMOn Q N := fun N hN =>
    ⟨fun f hf => (h f).2 (hN.1 f hf), fun x ⟨f, hf, hfx⟩ => hN.2 x ⟨f, (h f).1 hf, hfx⟩⟩
  intro g hg t ⟨N0, hN0, hst0⟩
  obtain ⟨N, hN, hst, c, hc, μ, hμ⟩ := hE g ((h g).2 hg) t ⟨N0, pm' N0 hN0, hst0⟩
  exact ⟨N, pm N hN, hst, c, starOn_congr h hc, μ, fun f hf => hμ f ((h f).2 hf)⟩

theorem Cut2.flip_flip_clo (C : Cut2 P) (i : Fin (addEdge X C.a1 C.a2).m) : C.flip.flip.clo i ↔ C.clo i := by
  unfold Cut2.clo
  constructor
  · rintro (h | ⟨d, h, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, h, (C.flip_flip_inA_iff).1 hd⟩
  · rintro (h | ⟨d, h, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, h, (C.flip_flip_inA_iff).2 hd⟩

theorem Cut2.cloN_congr (C : Cut2 P) {N N' : Fin X.m → Prop} {g : Prop} (h : ∀ d, C.inA d → (N d ↔ N' d))
    (i : Fin (addEdge X C.a1 C.a2).m) : C.cloN N g i ↔ C.cloN N' g i := by
  unfold Cut2.cloN
  constructor
  · rintro (h1 | ⟨d, h1, hd, hn⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨d, h1, hd, (h d hd).1 hn⟩
  · rintro (h1 | ⟨d, h1, hd, hn⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨d, h1, hd, (h d hd).2 hn⟩

/-- at the `A`-end `u` of a cut edge `e` there are two distinct edges inside `A` -/
theorem Cut2.two_inA (C : Cut2 P) (hcub : CubicOn P) {e : Fin X.m} {u : Fin X.n} (he : C.isCut e)
    (heu : X.Inc e u) (hu : C.S u = true) (hPe : P e) :
    ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ X.Inc f u ∧ X.Inc f' u := by
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub u ⟨e, hPe, heu⟩
  have nc : ∀ g, P g → X.Inc g u → e ≠ g → C.inA g := fun g hg hgu hne =>
    C.inA_of_notcut hg (fun h => C.cut_disj he h hne heu hgu) hgu hu
  rcases hall e hPe heu with rfl | rfl | rfl
  · exact ⟨q, r, dqr, nc q hq iq dpq, nc r hr ir dpr, iq, ir⟩
  · exact ⟨p, r, dpr, nc p hp ip (Ne.symm dpq), nc r hr ir dqr, ip, ir⟩
  · exact ⟨p, q, dpq, nc p hp ip (Ne.symm dpr), nc q hq iq (Ne.symm dqr), ip, iq⟩

/-- an edge inside `A` at `a1` that does not join `a1` and `a2` (at most one edge joins them) -/
theorem Cut2.nonrung (C : Cut2 P) (hcub : CubicOn P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f') :
    ∃ f, C.inA f ∧ X.Inc f C.a1 ∧ ¬ X.Joins f C.a1 C.a2 := by
  obtain ⟨f, f', hne, hf, hf', i, i'⟩ := C.two_inA hcub (Or.inl rfl) (joins_inc_left C.j1) C.sa1 C.P1
  by_cases hj : X.Joins f C.a1 C.a2
  · by_cases hj' : X.Joins f' C.a1 C.a2
    · exact absurd (hpa f f' hf.1 hf'.1 hj hj') hne
    · exact ⟨f', hf', i', hj'⟩
  · exact ⟨f, hf, i, hj⟩

/-- **Step 5 of EX1-2C″**: from a perfect matching of `G_B` avoiding `g_B` and containing a rung joining `b1, b2`,
    with an MC-colouring, the side `A` supplies a cover and the glued matching is MC-colourable -/
def Cut2.Step5 (C : Cut2 P) : Prop :=
  ∀ (NB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Prop) (cB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6),
    PMOn C.flip.clo NB → ¬ NB (Fin.last X.m) → MC5 C.flip.clo NB cB →
    (∃ r, P r ∧ X.Joins r C.b1 C.b2 ∧ NB (Fin.castSucc r)) →
    ∃ NA c, C.CoverA NA False ∧ MC5 P (C.glueN NA (fun d => NB (Fin.castSucc d)) False) c

/-- the part of EX1-2C″ for an edge `g` inside `B` or a cut edge -/
theorem Cut2.side (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    (hpb : ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f')
    (hA : EX1On C.clo) (hB : EX1On C.flip.clo) (h5 : (∃ r, P r ∧ X.Joins r C.b1 C.b2) → C.Step5)
    {g : Fin X.m} (hg : C.flip.inA g ∨ C.isCut g) (t : Bool) :
    ∃ M c, PMOn P M ∧ (M g ↔ t = true) ∧ MC5 P M c := by
  classical
  have GA := C.clo_inG hG
  have GB := C.flip.clo_inG hG
  -- the edge of `G_B` carrying the prescription
  have hg' : C.flip.clo (C.flip.toClo g) := by
    rcases hg with h | h
    · rw [C.flip.toClo_old (fun h' => C.flip.not_inA_of_cut h' h)]; exact C.flip.clo_old h
    · rw [C.flip.toClo_cut h]; exact C.flip.clo_last
  obtain ⟨NB, cB, hNB, hstB, hcB⟩ := ex1_full hPS GB hB hg' t
  -- the status of the glued matching at `g`
  have status : ∀ (NA : Fin X.m → Prop) (s : Prop), (NB (Fin.last X.m) ↔ s) →
      (C.glueN NA (fun d => NB (Fin.castSucc d)) s g ↔ t = true) := by
    intro NA s hs
    rcases hg with h | h
    · rw [C.glueN_B h, ← hstB, C.flip.toClo_old (fun h' => C.flip.not_inA_of_cut h' h)]
    · rw [C.glueN_cut h, ← hs, ← hstB, C.flip.toClo_cut h]
  have coverB : ∀ s, (NB (Fin.last X.m) ↔ s) → C.flip.CoverA (fun d => NB (Fin.castSucc d)) s :=
    fun s hs => C.flip.coverA_of_clo hNB hs
  have mcB : ∀ (NA : Fin X.m → Prop) (s : Prop), (NB (Fin.last X.m) ↔ s) →
      MC5 C.flip.clo (C.flip.cloN (C.glueN NA (fun d => NB (Fin.castSucc d)) s) s) cB := by
    intro NA s hs
    refine mc5_congr hcB (fun i hi => ?_)
    rw [C.flip.cloN_glue (NB := NA) hs i hi]
    exact C.flip.cloN_congr (fun d _ => C.glueN_symm d) i
  by_cases hl : NB (Fin.last X.m)
  · -- (1) matching type: `g_B ∈ N_B`
    obtain ⟨NA, cA, hNA, hstA, hcA⟩ := ex1_full hPS GA hA C.clo_last true
    have hsA : NA (Fin.last X.m) ↔ True := ⟨fun _ => trivial, fun _ => hstA.2 rfl⟩
    have hsB : NB (Fin.last X.m) ↔ True := ⟨fun _ => trivial, fun _ => hl⟩
    let M := C.glueN (fun d => NA (Fin.castSucc d)) (fun d => NB (Fin.castSucc d)) True
    have hM : PMOn P M := C.pm_glue (C.coverA_of_clo hNA hsA) (coverB True hsB)
    obtain ⟨c, hc⟩ := g2m hG.1 hG.2.2.2 hM C ((C.glueN_cut (Or.inl rfl)).2 trivial)
      ((C.glueN_cut (Or.inr rfl)).2 trivial) hpa hpb cA
      (mc5_congr hcA (C.cloN_glue hsA)) cB (mcB _ True hsB)
    exact ⟨M, c, hM, status _ True hsB, hc⟩
  · have hsB : NB (Fin.last X.m) ↔ False := ⟨hl, False.elim⟩
    by_cases hr : ∃ r, P r ∧ X.Joins r C.b1 C.b2 ∧ NB (Fin.castSucc r)
    · -- (3) a matching rung on side `B`: Step 5
      obtain ⟨r, hrP, hrj, _⟩ := id hr
      obtain ⟨NA, c, hcov, hc⟩ := h5 ⟨r, hrP, hrj⟩ NB cB hNB hl hcB hr
      exact ⟨_, c, C.pm_glue hcov (coverB False hsB), status NA False hsB, hc⟩
    · -- (2) F-type without matching rungs: G2F
      obtain ⟨f, hf, hfa, hfj⟩ := C.nonrung hG.2.2.2 hpa
      obtain ⟨NA, cA, hNA, hstA, hcA⟩ := ex1_full hPS GA hA (C.clo_old hf) true
      have hNf : NA (Fin.castSucc f) := hstA.2 rfl
      have hfa' : (addEdge X C.a1 C.a2).Inc (Fin.castSucc f) C.a1 := addEdge_inc_old.2 hfa
      have hla : (addEdge X C.a1 C.a2).Inc (Fin.last X.m) C.a1 := (C.inc_new_iff).2 (Or.inl rfl)
      have hnl : ¬ NA (Fin.last X.m) := fun h => castSucc_ne_last f (pm_unique hNA hNf h hfa' hla)
      have hsA : NA (Fin.last X.m) ↔ False := ⟨hnl, False.elim⟩
      let M := C.glueN (fun d => NA (Fin.castSucc d)) (fun d => NB (Fin.castSucc d)) False
      have hM : PMOn P M := C.pm_glue (C.coverA_of_clo hNA hsA) (coverB False hsB)
      have hMa : ∀ e, M e → ¬ X.Joins e C.a1 C.a2 := by
        rintro e (⟨he, hn⟩ | ⟨he, _⟩ | ⟨_, hfalse⟩) hj
        · have := pm_unique hNA hn hNf (addEdge_inc_old.2 (joins_inc_left hj)) hfa'
          exact hfj (castSucc_inj' this ▸ hj)
        · have := C.flip.side_of_inA he (joins_inc_left hj); rw [Cut2.flip_S, C.sa1] at this
          exact absurd this (by decide)
        · exact hfalse
      have hMb : ∀ e, M e → ¬ X.Joins e C.b1 C.b2 := by
        rintro e (⟨he, _⟩ | ⟨he, hn⟩ | ⟨_, hfalse⟩) hj
        · have := C.side_of_inA he (joins_inc_left hj); rw [C.sb1] at this; exact absurd this (by decide)
        · exact hr ⟨e, he.1, hj, hn⟩
        · exact hfalse
      obtain ⟨c, hc⟩ := g2f hG.1 hG.2.2.2 hM C ((C.glueN_cut (Or.inl rfl)).1) ((C.glueN_cut (Or.inr rfl)).1)
        hMa hMb cA (mc5_congr hcA (C.cloN_glue hsA)) cB (mcB _ False hsB)
      exact ⟨M, c, hM, status _ False hsB, hc⟩

/-- **Lemma EX1-2C″** (fact 081a6e8977aebf8f), with (P) (fact f6e8c173bef4cfa1) and Step 5 as hypotheses. -/
theorem ex1_2c (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    (hpb : ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f')
    (hA : EX1On C.clo) (hB : EX1On C.flip.clo)
    (h5 : (∃ r, P r ∧ X.Joins r C.b1 C.b2) → C.Step5)
    (h5' : (∃ r, P r ∧ X.Joins r C.a1 C.a2) → C.flip.Step5) :
    EX1On P := by
  intro g hg t _
  have main : ∃ M c, PMOn P M ∧ (M g ↔ t = true) ∧ MC5 P M c := by
    rcases C.cases_P hg with h | h | h
    · exact C.flip.side hPS hG hpb hpa hB (ex1On_congr (fun i => (C.flip_flip_clo i).symm) hA) h5'
        (Or.inl ((C.flip_flip_inA_iff).2 h)) t
    · exact C.side hPS hG hpa hpb hA hB h5 (Or.inl h) t
    · exact C.side hPS hG hpa hpb hA hB h5 (Or.inr h) t
  obtain ⟨M, c, hM, hst, hc⟩ := main
  exact ⟨M, hM, hst, c, hc.1, 5, hc.2⟩

end ex2c

end RH2F

-- ===== from RH2CL5.lean =====
/-
  RH2CL5.lean — Lemma CL (fact ecc9734f558cf885), part (CL5), in Lean 4.20 core, in the pole encoding.
  If exactly one edge `r` of `P` joins `a1, a2` and `r ∈ N` for a perfect matching `N` of the edge closure `G_A`
  avoiding `g_A`, then the pole colouring `c ∘ toClo` of `A⁺` can be changed at `e2` to a colour `γ′` different from
  `γ = c(g_A)`, from the colour of the F-edge at `a1` inside `A`, and from 5.
-/

namespace RH2F
open MGraph

section cl5
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the third edge at a vertex of a cubic edge set -/
theorem third_edge (hcub : CubicOn P) {x : Fin X.n} {a b : Fin X.m} (ha : P a) (hb : P b) (hax : X.Inc a x)
    (hbx : X.Inc b x) (hab : a ≠ b) :
    ∃ c, P c ∧ X.Inc c x ∧ c ≠ a ∧ c ≠ b ∧ ∀ d, P d → X.Inc d x → d = a ∨ d = b ∨ d = c := by
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub x ⟨a, ha, hax⟩
  rcases hall a ha hax with rfl | rfl | rfl <;> rcases hall b hb hbx with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact ⟨r, hr, ir, Ne.symm dpr, Ne.symm dqr, fun d hd hdx => hall d hd hdx⟩
  · refine ⟨q, hq, iq, Ne.symm dpq, dqr, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · refine ⟨r, hr, ir, Ne.symm dqr, Ne.symm dpr, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact absurd rfl hab
  · refine ⟨p, hp, ip, dpq, dpr, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine ⟨q, hq, iq, dqr, Ne.symm dpq, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · refine ⟨p, hp, ip, dpr, dpq, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact absurd rfl hab

def okc (a b c d x : Fin 6) : Bool := x != a && x != b && x != c && x != d && x != 5

def pick5 (a b c d : Fin 6) : Fin 6 :=
  if okc a b c d 0 then 0 else if okc a b c d 1 then 1 else if okc a b c d 2 then 2 else
  if okc a b c d 3 then 3 else 4

theorem pick5_chk : all6 (fun a => all6 fun b => all6 fun c => all6 fun d => okc a b c d (pick5 a b c d)) = true := by
  decide +kernel

/-- a colour different from four given colours and from 5 -/
theorem avoid5 (a b c d : Fin 6) : ∃ x : Fin 6, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d ∧ x ≠ 5 := by
  refine ⟨pick5 a b c d, ?_⟩
  have h := all6_sound (all6_sound (all6_sound (all6_sound pick5_chk a) b) c) d
  simp only [okc, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem Cut2.joins_inA (C : Cut2 P) {r : Fin X.m} (hrP : P r) (hrj : X.Joins r C.a1 C.a2) : C.inA r := by
  rcases hrj with h | h <;> refine ⟨hrP, ?_, ?_⟩ <;> rw [h]
  · exact C.sa1
  · exact C.sa2
  · exact C.sa2
  · exact C.sa1

/-- in the pole, the cut edge `e2` is never a middle edge of a walk -/
theorem Cut2.pole_mid_not_cut (C : Cut2 P) {e f f' : Fin X.m} (he : C.isCut e) (hf : C.pole f) (hf' : C.pole f')
    (hfe : f ≠ e) (hf'e : f' ≠ e) {u u' : Fin X.n} (hj : X.Joins e u u') (hfu : X.Inc f u) (hf'u' : X.Inc f' u') :
    False := by
  have s1 := C.pole_meet_A he hf (Ne.symm hfe) (joins_inc_left hj) hfu
  have s2 := C.pole_meet_A he hf' (Ne.symm hf'e) (joins_inc_right hj) hf'u'
  rcases C.cut_sides he hj with ⟨_, h⟩ | ⟨h, _⟩
  · rw [s2] at h; exact absurd h (by decide)
  · rw [s1] at h; exact absurd h (by decide)

/-- **(CL5)** (fact ecc9734f558cf885) in the pole encoding. -/
theorem Cut2.cl5 (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    {N : Fin (addEdge X C.a1 C.a2).m → Prop} (hN : PMOn C.clo N) (_hnl : ¬ N (Fin.last X.m))
    {c : Fin (addEdge X C.a1 C.a2).m → Fin 6} (hc : MC5 C.clo N c)
    {r : Fin X.m} (hrP : P r) (hrj : X.Joins r C.a1 C.a2) (hrN : N (Fin.castSucc r)) :
    ∃ ψ' : Fin X.m → Fin 6, StarOn C.pole 6 ψ' ∧ (∀ f, C.inA f → ψ' f = c (Fin.castSucc f)) ∧
      ψ' C.e1 = c (Fin.last X.m) ∧ ψ' C.e2 ≠ c (Fin.last X.m) ∧ ψ' C.e2 ≠ 5 ∧
      (∀ f, C.inA f → ¬ N (Fin.castSucc f) → X.Inc f C.a1 → ψ' f ≠ ψ' C.e2) := by
  classical
  have hloop := hG.1
  have hcub := hG.2.2.2
  have hrA := C.joins_inA hrP hrj
  have hre1 : r ≠ C.e1 := fun h => C.not_inA_of_cut (Or.inl h) hrA
  have hre2 : r ≠ C.e2 := fun h => C.not_inA_of_cut (Or.inr h) hrA
  have ia1 : X.Inc r C.a1 := joins_inc_left hrj
  have ia2 : X.Inc r C.a2 := joins_inc_right hrj
  obtain ⟨f1, hf1, if1, f1e1, f1r, cov1⟩ := third_edge hcub C.P1 hrP (joins_inc_left C.j1) ia1 (Ne.symm hre1)
  obtain ⟨f2, hf2, if2, f2e2, f2r, cov2⟩ := third_edge hcub C.P2 hrP (joins_inc_left C.j2) ia2 (Ne.symm hre2)
  have nc1 : ¬ C.isCut f1 := by
    rintro (h | h)
    · exact f1e1 h
    · exact C.e12_disj (joins_inc_left C.j1) (h ▸ if1)
  have nc2 : ¬ C.isCut f2 := by
    rintro (h | h)
    · exact C.e12_disj (h ▸ if2) (joins_inc_left C.j2)
    · exact f2e2 h
  have i1A : C.inA f1 := C.inA_of_notcut hf1 nc1 if1 C.sa1
  have i2A : C.inA f2 := C.inA_of_notcut hf2 nc2 if2 C.sa2
  obtain ⟨y, hy⟩ := joins_of_inc if2
  have hya2 : y ≠ C.a2 := fun h => ne_of_joins hloop hy h.symm
  have hya1 : y ≠ C.a1 := by
    intro h
    exact f2r (hpa f2 r hf2 hrP (Or.symm (h ▸ hy)) hrj)
  have hyA : C.S y = true := C.side_of_inA i2A (joins_inc_right hy)
  -- the matching edge at `y`
  have hla : ∀ z, (addEdge X C.a1 C.a2).Inc (Fin.last X.m) z → z = C.a1 ∨ z = C.a2 := fun z h => (C.inc_new_iff).1 h
  obtain ⟨am, ham, hamy, _⟩ := hN.2 y ⟨Fin.castSucc f2, C.clo_old i2A, addEdge_inc_old.2 (joins_inc_right hy)⟩
  obtain ⟨m, rfl⟩ : ∃ m, am = Fin.castSucc m := by
    rcases addEdge_cases am with rfl | ⟨m, rfl⟩
    · rcases hla y hamy with h | h
      · exact absurd h hya1
      · exact absurd h hya2
    · exact ⟨m, rfl⟩
  have hmA : C.inA m := (C.clo_old_iff).1 (hN.1 _ ham)
  have hmy : X.Inc m y := addEdge_inc_old.1 hamy
  have nN2 : ¬ N (Fin.castSucc f2) := fun h =>
    f2r (castSucc_inj' (pm_unique hN h hrN (addEdge_inc_old.2 if2) (addEdge_inc_old.2 ia2)))
  have hmf2 : m ≠ f2 := fun h => nN2 (h ▸ ham)
  obtain ⟨h, hh, ihy, hhf2, hhm, covy⟩ :=
    third_edge hcub hf2 hmA.1 (joins_inc_right hy) hmy (Ne.symm hmf2)
  have nch : ¬ C.isCut h := by
    intro hch
    rcases C.cutA hch ihy hyA with ⟨_, h'⟩ | ⟨_, h'⟩
    · exact hya1 h'
    · exact hya2 h'
  have ihA : C.inA h := C.inA_of_notcut hh nch ihy hyA
  -- the new colour
  obtain ⟨γ', g1, g2, g3, g4, g5⟩ :=
    avoid5 (c (Fin.last X.m)) (c (Fin.castSucc f1)) (c (Fin.castSucc f2)) (c (Fin.castSucc h))
  let ψ : Fin X.m → Fin 6 := fun f => c (C.toClo f)
  have hψ : StarOn C.pole 6 ψ := C.pole_of_clo c hc.1
  let ψ' : Fin X.m → Fin 6 := fun f => if f = C.e2 then γ' else ψ f
  have ψ'e2 : ψ' C.e2 = γ' := by simp [ψ']
  have ψ'ne : ∀ f, f ≠ C.e2 → ψ' f = ψ f := fun f hf => by simp [ψ', hf]
  have ψold : ∀ f, ¬ C.isCut f → ψ f = c (Fin.castSucc f) := fun f hf => by simp [ψ, C.toClo_old hf]
  have ψ'e1 : ψ' C.e1 = c (Fin.last X.m) := by
    rw [ψ'ne _ C.ne12]; simp [ψ, C.toClo_cut (Or.inl rfl)]
  have c5 : ∀ g, C.inA g → N (Fin.castSucc g) → c (Fin.castSucc g) = 5 :=
    fun g hg hn => (hc.2 _ (C.clo_old hg)).1 hn
  -- the edges next to `e2` at `a2`
  have at_a2 : ∀ b, P b → X.Inc b C.a2 → b ≠ C.e2 → ψ' b ≠ γ' := by
    intro b hb hba hbe
    rcases cov2 b hb hba with h' | h' | h'
    · exact absurd h' hbe
    · rw [h', ψ'ne _ hre2, ψold _ (fun h'' => C.not_inA_of_cut h'' hrA), c5 r hrA hrN]; exact Ne.symm g5
    · rw [h', ψ'ne _ f2e2, ψold _ nc2]; exact Ne.symm g3
  -- a walk starting with `e2` is not bicoloured
  have first : ∀ w : X.Walk4, C.pole w.e1 → C.pole w.e2 → C.pole w.e3 → C.pole w.e4 → w.e1 = C.e2 →
      ¬ Bicol ψ' w := by
    intro w p1 p2 p3 p4 he hb
    have hv1 : C.S w.v1 = true := C.pole_meet_A (Or.inr he) p2 (he ▸ w.e1_ne_e2) (he ▸ w.inc_e1_v1) w.inc_e2_v1
    have hv1a : w.v1 = C.a2 := by
      rcases C.cutA (Or.inr he) w.inc_e1_v1 hv1 with ⟨h', _⟩ | ⟨_, h'⟩
      · exact absurd (h'.symm.trans he) C.ne12
      · exact h'
    have hw1 : ψ' w.e1 = γ' := by rw [he, ψ'e2]
    have hb1 : ψ' w.e3 = γ' := hb.1.symm.trans hw1
    have hw2e : w.e2 ≠ C.e2 := fun h' => w.e1_ne_e2 (he.trans h'.symm)
    have hw3e : w.e3 ≠ C.e2 := fun h' => w.e1_ne_e3 (he.trans h'.symm)
    rcases cov2 w.e2 (C.pole_P p2) (hv1a ▸ w.inc_e2_v1) with h' | h' | h'
    · exact hw2e h'
    · -- `w2 = r`: then `v2 = a1` and `w3 ∈ {e1, f1}`
      have hv2 : w.v2 = C.a1 := by
        rcases joins_unique (h' ▸ w.h2) hrj with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd (hv1a.symm.trans h1) (Ne.symm C.ha)
        · exact h2
      rcases cov1 w.e3 (C.pole_P p3) (hv2 ▸ w.inc_e3_v2) with h'' | h'' | h''
      · rw [h'', ψ'e1] at hb1; exact g1 hb1.symm
      · exact w.e2_ne_e3 (h'.trans h''.symm)
      · rw [h'', ψ'ne _ (fun h3 => nc1 (Or.inr h3)), ψold _ nc1] at hb1; exact g2 hb1.symm
    · -- `w2 = f2`: then `v2 = y` and `w3 ∈ {m, h}`
      have hv2 : w.v2 = y := by
        rcases joins_unique (h' ▸ w.h2) hy with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2
        · exact absurd (hv1a.symm.trans h1) (Ne.symm hya2)
      rcases covy w.e3 (C.pole_P p3) (hv2 ▸ w.inc_e3_v2) with h'' | h'' | h''
      · exact w.e2_ne_e3 (h'.trans h''.symm)
      · rw [h'', ψ'ne _ (fun h3 => C.not_inA_of_cut (Or.inr h3) hmA),
          ψold _ (fun h3 => C.not_inA_of_cut h3 hmA), c5 m hmA ham] at hb1
        exact g5 hb1.symm
      · rw [h'', ψ'ne _ (fun h3 => nch (Or.inr h3)), ψold _ nch] at hb1; exact g4 hb1.symm
  refine ⟨ψ', ⟨?_, ?_⟩, ?_, ψ'e1, ?_, ?_, ?_⟩
  · intro a b hab ha hb heq
    by_cases hae : a = C.e2 <;> by_cases hbe : b = C.e2
    · exact hab.1 (hae.trans hbe.symm)
    · obtain ⟨_, x, hax, hbx⟩ := hab
      subst hae
      have hs := C.pole_meet_A (Or.inr rfl) hb (Ne.symm hbe) hax hbx
      have hxa : x = C.a2 := by
        rcases C.cutA (Or.inr rfl) hax hs with ⟨h', _⟩ | ⟨_, h'⟩
        · exact absurd h'.symm C.ne12
        · exact h'
      exact at_a2 b (C.pole_P hb) (hxa ▸ hbx) hbe (heq.symm.trans ψ'e2)
    · obtain ⟨_, x, hax, hbx⟩ := hab
      subst hbe
      have hs := C.pole_meet_A (Or.inr rfl) ha (Ne.symm hae) hbx hax
      have hxa : x = C.a2 := by
        rcases C.cutA (Or.inr rfl) hbx hs with ⟨h', _⟩ | ⟨_, h'⟩
        · exact absurd h'.symm C.ne12
        · exact h'
      exact at_a2 a (C.pole_P ha) (hxa ▸ hax) hae (heq.trans ψ'e2)
    · rw [ψ'ne a hae, ψ'ne b hbe] at heq
      exact hψ.1 a b hab ha hb heq
  · intro w p1 p2 p3 p4 hb
    by_cases e1 : w.e1 = C.e2
    · exact first w p1 p2 p3 p4 e1 hb
    by_cases e4 : w.e4 = C.e2
    · exact first w.reverse p4 p3 p2 p1 e4 (bicol_rev w hb)
    by_cases e2 : w.e2 = C.e2
    · exact C.pole_mid_not_cut (Or.inr e2) p1 p3 w.e1_ne_e2 w.e2_ne_e3.symm w.h2 w.inc_e1_v1 w.inc_e3_v2
    by_cases e3 : w.e3 = C.e2
    · exact C.pole_mid_not_cut (Or.inr e3) p2 p4 w.e2_ne_e3 w.e3_ne_e4.symm w.h3 w.inc_e2_v2 w.inc_e4_v3
    apply hψ.2 w p1 p2 p3 p4
    exact ⟨by rw [← ψ'ne _ e1, ← ψ'ne _ e3]; exact hb.1, by rw [← ψ'ne _ e2, ← ψ'ne _ e4]; exact hb.2⟩
  · intro f hf
    rw [ψ'ne f (fun h' => C.not_inA_of_cut (Or.inr h') hf), ψold f (fun h' => C.not_inA_of_cut h' hf)]
  · rw [ψ'e2]; exact g1
  · rw [ψ'e2]; exact g5
  · intro f hf hnf hfa
    rw [ψ'e2]
    rcases cov1 f hf.1 hfa with h' | h' | h'
    · exact absurd (Or.inl h') (fun h'' => C.not_inA_of_cut h'' hf)
    · exact absurd (h' ▸ hrN) hnf
    · rw [h', ψ'ne _ (fun h3 => nc1 (Or.inr h3)), ψold _ nc1]; exact Ne.symm g2

end cl5

end RH2F

-- ===== from RH2Step5.lean =====
/-
  RH2Step5.lean — Step 5 of Lemma EX1-2C″ (fact 081a6e8977aebf8f) in Lean 4.20 core, and the complete lemma
  `ex1_2c''` with only (P) (fact f6e8c173bef4cfa1) as a hypothesis.
  Step 5: side `B` has a matching rung `r_B` (joining `b1, b2`); CL5 recolours the pendant `q2`; the digon closure
  `G_A^D` with `δ ∈ N` gives a colouring of `A⁺` with distinct pendant colours (CL4); after colour permutations
  (Lemma 2P(4c)) the F-type gluing (Lemma 2P(3)) applies.
-/

namespace RH2F
open MGraph

/-! ## Colour permutations for Lemma 2P(4c) -/

def p3L : List (List Nat) := [[0,1,2,3,4],[0,1,2,4,3],[0,1,3,2,4],[0,1,3,4,2],[0,1,4,2,3],[0,1,4,3,2]]

def p3Chk : Bool := p3L.all fun l =>
  ap5 l 0 == 0 && ap5 l 1 == 1 && ap5 l 5 == 5 && all6 fun x => all6 fun y => !(ap5 l x == ap5 l y) || x == y

theorem p3Chk_ok : p3Chk = true := by decide +kernel

theorem p3_props {l : List Nat} (hl : l ∈ p3L) :
    ap5 l 0 = 0 ∧ ap5 l 1 = 1 ∧ ap5 l 5 = 5 ∧ ∀ x y, ap5 l x = ap5 l y → x = y := by
  have h := List.all_eq_true.1 p3Chk_ok l hl
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h5⟩, hi⟩ := h
  refine ⟨h0, h1, h5, fun x y hxy => ?_⟩
  have := all6_sound (all6_sound hi x) y
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd hxy h
  · exact h

def all234 (p : Fin 6 → Bool) : Bool := p 2 && p 3 && p 4

theorem all234_sound {p : Fin 6 → Bool} (h : all234 p = true) : ∀ x, x ≠ 0 → x ≠ 1 → x ≠ 5 → p x = true := by
  simp only [all234, Bool.and_eq_true] at h
  obtain ⟨⟨h2, h3⟩, h4⟩ := h
  intro x h0 h1 h5
  rcases fin6_cases x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · exact absurd rfl h1
  all_goals first | assumption | exact absurd rfl h5

def c4Chk : Bool := all6 fun a1 => all6 fun a2 => all234 fun b1 => all234 fun b2 =>
  p3L.any fun l => ap5 l b1 != a1 && ap5 l b2 != a2

theorem c4Chk_ok : c4Chk = true := by decide +kernel

/-- **Lemma 2P(4c) permutation**: fix `γ ≠ γ′` (and 5) and move `β1, β2 ∉ {γ, γ′, 5}` off `α1`, `α2` -/
theorem perm_4c (γ γ' α1 α2 β1 β2 : Fin 6) (hγγ' : γ ≠ γ') (hγ5 : γ ≠ 5) (hγ'5 : γ' ≠ 5)
    (hb1 : β1 ≠ γ ∧ β1 ≠ γ' ∧ β1 ≠ 5) (hb2 : β2 ≠ γ ∧ β2 ≠ γ' ∧ β2 ≠ 5) :
    ∃ τ : Fin 6 → Fin 6, (∀ x y, τ x = τ y → x = y) ∧ τ 5 = 5 ∧ τ γ = γ ∧ τ γ' = γ' ∧ τ β1 ≠ α1 ∧ τ β2 ≠ α2 := by
  obtain ⟨κ, κ', hκκ, hκ'κ, hκ5, hκγ, hκγ'⟩ := norm_perm hγ5 hγ'5 hγγ'
  have κi := inj_of_linv hκκ
  have κ'i : ∀ x y, κ' x = κ' y → x = y := fun x y h => by rw [← hκ'κ x, h, hκ'κ y]
  have nb : ∀ β, β ≠ γ ∧ β ≠ γ' ∧ β ≠ 5 → κ β ≠ 0 ∧ κ β ≠ 1 ∧ κ β ≠ 5 := fun β hb =>
    ⟨fun h => hb.1 (κi _ _ (h.trans hκγ.symm)), fun h => hb.2.1 (κi _ _ (h.trans hκγ'.symm)),
     fun h => hb.2.2 (κi _ _ (h.trans hκ5.symm))⟩
  obtain ⟨n10, n11, n15⟩ := nb β1 hb1
  obtain ⟨n20, n21, n25⟩ := nb β2 hb2
  have h := all234_sound (all234_sound (all6_sound (all6_sound c4Chk_ok (κ α1)) (κ α2)) _ n10 n11 n15) _ n20 n21 n25
  obtain ⟨l, hl, hg⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
  obtain ⟨g1, g2⟩ := hg
  obtain ⟨l0, l1, l5, linj⟩ := p3_props hl
  have hκ'5 : κ' 5 = 5 := by have := hκκ 5; rw [hκ5] at this; exact this
  have hκ'0 : κ' 0 = γ := by have := hκκ γ; rw [hκγ] at this; exact this
  have hκ'1 : κ' 1 = γ' := by have := hκκ γ'; rw [hκγ'] at this; exact this
  refine ⟨fun x => κ' (ap5 l (κ x)), fun x y hxy => κi _ _ (linj _ _ (κ'i _ _ hxy)), ?_, ?_, ?_, ?_, ?_⟩
  · show κ' (ap5 l (κ 5)) = 5; rw [hκ5, l5, hκ'5]
  · show κ' (ap5 l (κ γ)) = γ; rw [hκγ, l0, hκ'0]
  · show κ' (ap5 l (κ γ')) = γ'; rw [hκγ', l1, hκ'1]
  · intro h; apply g1; rw [← h, hκ'κ]
  · intro h; apply g2; rw [← h, hκ'κ]

/-- a colour permutation fixing 5 with `x ↦ γ`, `y ↦ γ′` -/
theorem perm_two {x y γ γ' : Fin 6} (hx : x ≠ 5) (hy : y ≠ 5) (hxy : x ≠ y) (hγ : γ ≠ 5) (hγ' : γ' ≠ 5)
    (hγγ' : γ ≠ γ') : ∃ ρ : Fin 6 → Fin 6, (∀ a b, ρ a = ρ b → a = b) ∧ ρ 5 = 5 ∧ ρ x = γ ∧ ρ y = γ' := by
  obtain ⟨α, α', hαα, _, hα5, hαx, hαy⟩ := norm_perm hx hy hxy
  obtain ⟨β, β', hββ, hβ'β, hβ5, hβγ, hβγ'⟩ := norm_perm hγ hγ' hγγ'
  have αi := inj_of_linv hαα
  have β'i : ∀ a b, β' a = β' b → a = b := fun a b h => by rw [← hβ'β a, h, hβ'β b]
  refine ⟨fun a => β' (α a), fun a b h => αi _ _ (β'i _ _ h), ?_, ?_, ?_⟩
  · show β' (α 5) = 5; rw [hα5]; have := hββ 5; rw [hβ5] at this; exact this
  · show β' (α x) = γ; rw [hαx]; have := hββ γ; rw [hβγ] at this; exact this
  · show β' (α y) = γ'; rw [hαy]; have := hββ γ'; rw [hβγ'] at this; exact this

section step5
variable {X : MGraph} {P : Fin X.m → Prop}

/-- at a vertex of a cubic `P`, edges different from two given distinct edges are equal -/
theorem uniq3 (hcub : CubicOn P) {x : Fin X.n} {e0 d0 f f' : Fin X.m} (he0 : P e0) (hd0 : P d0) (hf : P f)
    (hf' : P f') (ie0 : X.Inc e0 x) (id0 : X.Inc d0 x) (if_ : X.Inc f x) (if' : X.Inc f' x) (hed : e0 ≠ d0)
    (hfe : f ≠ e0) (hfd : f ≠ d0) (hf'e : f' ≠ e0) (hf'd : f' ≠ d0) : f = f' := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨p, q, r, _, _, _, _, _, _, _, _, _, hall⟩ := hcub x ⟨e0, he0, ie0⟩
  rcases hall e0 he0 ie0 with a1 | a1 | a1 <;> rcases hall d0 hd0 id0 with a2 | a2 | a2 <;>
    rcases hall f hf if_ with a3 | a3 | a3 <;> rcases hall f' hf' if' with a4 | a4 | a4 <;>
    first
    | exact hed (a1.trans a2.symm) | exact hfe (a3.trans a1.symm) | exact hfd (a3.trans a2.symm)
    | exact hf'e (a4.trans a1.symm) | exact hf'd (a4.trans a2.symm) | exact hne (a3.trans a4.symm)

/-- a value attached to all edges with a property that are pairwise equal, with a default avoiding three colours -/
theorem uniq_val {ι : Type} (Q : ι → Prop) (v : ι → Fin 6) (huniq : ∀ i j, Q i → Q j → i = j)
    (a b : Fin 6) (hgood : ∀ i, Q i → v i ≠ a ∧ v i ≠ b ∧ v i ≠ 5) :
    ∃ β, (β ≠ a ∧ β ≠ b ∧ β ≠ 5) ∧ ∀ i, Q i → v i = β := by
  classical
  by_cases hex : ∃ i, Q i
  · obtain ⟨i, hi⟩ := hex
    exact ⟨v i, hgood i hi, fun j hj => by rw [huniq j i hj hi]⟩
  · obtain ⟨β, h1, h2, _, _, h5⟩ := avoid5 a b 5 5
    exact ⟨β, ⟨h1, h2, h5⟩, fun i hi => absurd ⟨i, hi⟩ hex⟩

/-- **Step 5 of EX1-2C″**, discharged. -/
theorem Cut2.step5 (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hpb : ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f')
    (hAD : EX1On C.cloD) : C.Step5 := by
  classical
  intro NB cB hNB hnl hcB hr
  obtain ⟨r, hrP, hrj, hrN⟩ := hr
  have hcub := hG.2.2.2
  -- (CL5) on side `B`
  obtain ⟨ψ', hψ', hψ'in, hψ'e1, hψ'γ, hψ'5, hβ1⟩ := C.flip.cl5 hG hpb hNB hnl hcB hrP hrj hrN
  have hγ5 : cB (Fin.last X.m) ≠ 5 := fun h => hnl ((hcB.2 _ C.flip.clo_last).2 h)
  -- (CL4) on side `A`
  obtain ⟨ND, cD, hND, hstD, hcD⟩ := ex1_full hPS (C.cloD_inG hG) hAD (Or.inl rfl : C.cloD C.dl1) true
  have hδ : ND C.dl1 := hstD.2 rfl
  obtain ⟨n1, n2, hφne⟩ := C.cl4_pend hG.1 hND hδ cD hcD
  have hφ : StarOn C.pole 6 (fun f => cD (C.oD f)) := C.pole_of_cloD cD hcD.1
  have φ5 : ∀ f, C.pole f → (cD (C.oD f) = 5 ↔ ND (C.oD f)) :=
    fun f hf => (hcD.2 _ ((C.cloD_old_iff).2 hf)).symm
  have hφ1 : cD (C.oD C.e1) ≠ 5 := fun h => n1 ((φ5 _ (Or.inr (Or.inl rfl))).1 h)
  have hφ2 : cD (C.oD C.e2) ≠ 5 := fun h => n2 ((φ5 _ (Or.inr (Or.inr rfl))).1 h)
  -- `ρ` sends the pendant colours of `A⁺` to `γ`, `γ′`
  obtain ⟨ρ, ρi, ρ5, ρ1, ρ2⟩ := perm_two hφ1 hφ2 hφne hγ5 hψ'5 (Ne.symm hψ'γ)
  have hρ5 : ∀ a, ρ a = 5 ↔ a = 5 := fun a => ⟨fun h => ρi _ _ (h.trans ρ5.symm), fun h => h ▸ ρ5⟩
  -- the glued matching
  let NA : Fin X.m → Prop := fun d => ND (C.oD d)
  let NB' : Fin X.m → Prop := fun d => NB (Fin.castSucc d)
  let M := C.glueN NA NB' False
  have hcovA : C.CoverA NA False := C.coverA_of_cloD hND hδ
  have hcovB : C.flip.CoverA NB' False := C.flip.coverA_of_clo hNB ⟨hnl, False.elim⟩
  have hM : PMOn P M := C.pm_glue hcovA hcovB
  have nMcut : ∀ e, C.isCut e → ¬ M e := fun e he h => (C.glueN_cut he).1 h
  have cutP : ∀ e, C.isCut e → P e := fun e he => C.pole_P (Or.inr he)
  -- the F-edge at an end of a cut edge (other than the cut edge) is unique
  have Funiq : ∀ e u f f', C.isCut e → X.Inc e u → f ≠ e → f' ≠ e → P f → ¬ M f → X.Inc f u → P f' → ¬ M f' →
      X.Inc f' u → f = f' := by
    intro e u f f' he heu hfe hf'e hf nf hfu hf' nf' hf'u
    apply Classical.byContradiction; intro hne
    exact fdeg2 hcub hM (cutP e he) hf hf' (nMcut e he) nf nf' heu hfu hf'u (Ne.symm hfe) (Ne.symm hf'e) hne
  -- an edge of `P` at a vertex of `A`, other than the cut edges, is inside `A`; likewise for `B`
  have atA : ∀ f u, P f → X.Inc f u → C.S u = true → ¬ C.isCut f → C.inA f :=
    fun f u hf hfu hu hnc => C.inA_of_notcut hf hnc hfu hu
  have notcut_at : ∀ e u f, C.isCut e → X.Inc e u → X.Inc f u → f ≠ e → ¬ C.isCut f :=
    fun e u f he heu hfu hfe hcf => C.cut_disj he hcf (Ne.symm hfe) heu hfu
  -- the values `α_i`
  have exα : ∀ (e : Fin X.m) (u : Fin X.n), C.isCut e → X.Inc e u →
      ∃ α : Fin 6, ∀ f, P f → ¬ M f → X.Inc f u → f ≠ e → ρ (cD (C.oD f)) = α := by
    intro e u he heu
    by_cases hex : ∃ f, P f ∧ ¬ M f ∧ X.Inc f u ∧ f ≠ e
    · obtain ⟨f0, h0, n0, i0, e0⟩ := hex
      exact ⟨ρ (cD (C.oD f0)), fun f hf nf hfu hfe => by rw [Funiq e u f f0 he heu hfe e0 hf nf hfu h0 n0 i0]⟩
    · exact ⟨0, fun f hf nf hfu hfe => absurd ⟨f, hf, nf, hfu, hfe⟩ hex⟩
  obtain ⟨α1, hα1⟩ := exα C.e1 C.a1 (Or.inl rfl) (joins_inc_left C.j1)
  obtain ⟨α2, hα2⟩ := exα C.e2 C.a2 (Or.inr rfl) (joins_inc_left C.j2)
  -- the values `β_i`
  have fB : ∀ f u e, C.isCut e → X.Inc e u → C.S u = false → P f → X.Inc f u → f ≠ e → C.flip.inA f :=
    fun f u e he heu hu hf hfu hfe => C.flip.inA_of_notcut hf (notcut_at e u f he heu hfu hfe) hfu (Cut2.flip_true hu)
  have nNB : ∀ f, C.flip.inA f → ¬ M f → ¬ NB (Fin.castSucc f) := fun f hf nf h => nf ((C.glueN_B hf).2 h)
  have c5B : ∀ f, C.flip.inA f → ¬ NB (Fin.castSucc f) → cB (Fin.castSucc f) ≠ 5 :=
    fun f hf hn h => hn ((hcB.2 _ (C.flip.clo_old hf)).2 h)
  have propB : ∀ f u, C.flip.inA f → X.Inc f u → (u = C.b1 ∨ u = C.b2) →
      cB (Fin.castSucc f) ≠ cB (Fin.last X.m) := fun f u hf hfu hu =>
    hcB.1.1 _ _ ⟨castSucc_ne_last f, u, addEdge_inc_old.2 hfu, (C.flip.inc_new_iff).2 hu⟩ (C.flip.clo_old hf)
      C.flip.clo_last
  obtain ⟨β1, hβ1g, hβ1v⟩ := uniq_val (fun f => P f ∧ ¬ M f ∧ X.Inc f C.b1 ∧ f ≠ C.e1) ψ'
    (fun i j hi hj => Funiq C.e1 C.b1 i j (Or.inl rfl) (joins_inc_right C.j1) hi.2.2.2 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1
      hj.1 hj.2.1 hj.2.2.1)
    (cB (Fin.last X.m)) (ψ' C.e2)
    (fun f ⟨hf, nf, hfu, hfe⟩ => by
      have hfB := fB f C.b1 C.e1 (Or.inl rfl) (joins_inc_right C.j1) C.sb1 hf hfu hfe
      refine ⟨?_, hβ1 f hfB (nNB f hfB nf) hfu, ?_⟩
      · rw [hψ'in f hfB]; exact propB f C.b1 hfB hfu (Or.inl rfl)
      · rw [hψ'in f hfB]; exact c5B f hfB (nNB f hfB nf))
  obtain ⟨β2, hβ2g, hβ2v⟩ := uniq_val (fun f => P f ∧ ¬ M f ∧ X.Inc f C.b2 ∧ f ≠ C.e2) ψ'
    (fun i j hi hj => Funiq C.e2 C.b2 i j (Or.inr rfl) (joins_inc_right C.j2) hi.2.2.2 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1
      hj.1 hj.2.1 hj.2.2.1)
    (cB (Fin.last X.m)) (ψ' C.e2)
    (fun f ⟨hf, nf, hfu, hfe⟩ => by
      have hfB := fB f C.b2 C.e2 (Or.inr rfl) (joins_inc_right C.j2) C.sb2 hf hfu hfe
      refine ⟨?_, ?_, ?_⟩
      · rw [hψ'in f hfB]; exact propB f C.b2 hfB hfu (Or.inr rfl)
      · exact hψ'.1 f C.e2 ⟨hfe, C.b2, hfu, joins_inc_right C.j2⟩ (Or.inl hfB) (Or.inr (Or.inr rfl))
      · rw [hψ'in f hfB]; exact c5B f hfB (nNB f hfB nf))
  obtain ⟨τ, τi, τ5, τγ, τγ', τ1, τ2⟩ :=
    perm_4c (cB (Fin.last X.m)) (ψ' C.e2) α1 α2 β1 β2 (Ne.symm hψ'γ) hγ5 hψ'5 hβ1g hβ2g
  -- the glued colouring
  let c : Fin X.m → Fin 6 := fun f => if C.flip.inA f then τ (ψ' f) else ρ (cD (C.oD f))
  have hcA' : ∀ f, ¬ C.flip.inA f → c f = ρ (cD (C.oD f)) := fun f hf => by simp only [c, if_neg hf]
  have hcB' : ∀ f, C.flip.inA f → c f = τ (ψ' f) := fun f hf => by simp only [c, if_pos hf]
  have hc1 : c C.e1 = cB (Fin.last X.m) := by rw [hcA' C.e1 (C.flip.not_inA_of_cut (Or.inl rfl))]; exact ρ1
  have hc2 : c C.e2 = ψ' C.e2 := by rw [hcA' C.e2 (C.flip.not_inA_of_cut (Or.inr rfl))]; exact ρ2
  have hcφ : ∀ f, C.pole f → c f = ρ (cD (C.oD f)) := by
    intro f hf
    apply hcA'
    rcases hf with h | h
    · exact C.not_flip_of_inA h
    · exact C.flip.not_inA_of_cut h
  have hcψ : ∀ f, C.flip.pole f → c f = τ (ψ' f) := by
    intro f hf
    rcases hf with h | h
    · exact hcB' f h
    · rcases h with h | h
      · rw [h]; show c C.e1 = τ (ψ' C.e1); rw [hc1, show ψ' C.e1 = cB (Fin.last X.m) from hψ'e1, τγ]
      · rw [h]; show c C.e2 = τ (ψ' C.e2); rw [hc2, τγ']
  have hcl : ∀ f, P f → (M f ↔ c f = 5) := by
    intro f hf
    show C.glueN NA NB' False f ↔ c f = 5
    rcases C.cases_P hf with h | h | h
    · rw [C.glueN_A h, hcA' f (C.not_flip_of_inA h), hρ5]; exact (φ5 f (Or.inl h)).symm
    · rw [C.glueN_B h, hcB' f h, hψ'in f h]
      constructor
      · intro hn; rw [(hcB.2 _ (C.flip.clo_old h)).1 hn, τ5]
      · intro h5; exact (hcB.2 _ (C.flip.clo_old h)).2 (τi _ _ (h5.trans τ5.symm))
    · rw [C.glueN_cut h]
      constructor
      · intro hfalse; exact hfalse.elim
      · intro h5
        rcases h with rfl | rfl
        · rw [hc1] at h5; exact hγ5 h5
        · rw [hc2] at h5; exact hψ'5 h5
  have hF1' : ∀ r, M r → (X.Joins r C.a1 C.a2 ∨ X.Joins r C.b1 C.b2) → c C.e1 ≠ c C.e2 :=
    fun _ _ _ => by rw [hc1, hc2]; exact Ne.symm hψ'γ
  -- across a cut edge: the F-edge at `a_i` against the F-edge at `b_i`
  have cross : ∀ f f', ((P f ∧ ¬ M f ∧ f ≠ C.e1 ∧ X.Inc f C.a1 ∧ P f' ∧ ¬ M f' ∧ f' ≠ C.e1 ∧ X.Inc f' C.b1) ∨
      (P f ∧ ¬ M f ∧ f ≠ C.e2 ∧ X.Inc f C.a2 ∧ P f' ∧ ¬ M f' ∧ f' ≠ C.e2 ∧ X.Inc f' C.b2)) → c f ≠ c f' := by
    rintro f f' (⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u⟩ | ⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u⟩)
    · have hfA := atA f C.a1 hf hfu C.sa1 (notcut_at C.e1 C.a1 f (Or.inl rfl) (joins_inc_left C.j1) hfu hfe)
      have hf'B := fB f' C.b1 C.e1 (Or.inl rfl) (joins_inc_right C.j1) C.sb1 hf' hf'u hf'e
      rw [hcA' f (C.not_flip_of_inA hfA), hα1 f hf nf hfu hfe, hcB' f' hf'B, hβ1v f' ⟨hf', nf', hf'u, hf'e⟩]
      exact Ne.symm τ1
    · have hfA := atA f C.a2 hf hfu C.sa2 (notcut_at C.e2 C.a2 f (Or.inr rfl) (joins_inc_left C.j2) hfu hfe)
      have hf'B := fB f' C.b2 C.e2 (Or.inr rfl) (joins_inc_right C.j2) C.sb2 hf' hf'u hf'e
      rw [hcA' f (C.not_flip_of_inA hfA), hα2 f hf nf hfu hfe, hcB' f' hf'B, hβ2v f' ⟨hf', nf', hf'u, hf'e⟩]
      exact Ne.symm τ2
  have hF2' : ∀ e f f' u u', C.isCut e → X.Joins e u u' → f ≠ e → f' ≠ e → P f → ¬ M f → X.Inc f u → P f' →
      ¬ M f' → X.Inc f' u' → c f ≠ c f' := by
    intro e f f' u u' he hj hfe hf'e hf nf hfu hf' nf' hf'u'
    rcases C.cut_sides he hj with ⟨hu, _⟩ | ⟨_, hu'⟩
    · rcases C.cutA he (joins_inc_left hj) hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : u' = C.b1 := by
          rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h C.a1_ne_b1
        subst this
        exact cross f f' (Or.inl ⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u'⟩)
      · have : u' = C.b2 := by
          rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h C.a2_ne_b2
        subst this
        exact cross f f' (Or.inr ⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u'⟩)
    · rcases C.cutA he (joins_inc_right hj) hu' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : u = C.b1 := by
          rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h C.a1_ne_b1
          · exact h
        subst this
        exact Ne.symm (cross f' f (Or.inl ⟨hf', nf', hf'e, hf'u', hf, nf, hfe, hfu⟩))
      · have : u = C.b2 := by
          rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h C.a2_ne_b2
          · exact h
        subst this
        exact Ne.symm (cross f' f (Or.inr ⟨hf', nf', hf'e, hf'u', hf, nf, hfe, hfu⟩))
  have hstar : StarOn P 6 c :=
    glue_F hG.1 hM C (nMcut _ (Or.inl rfl)) (nMcut _ (Or.inr rfl)) (fun f => ρ (cD (C.oD f)))
      (fun f => τ (ψ' f)) c (starOn_map ρ ρi hφ) (starOn_map τ τi hψ') hcφ hcψ hcl hF1' hF2'
  exact ⟨NA, c, hcovA, hstar, hcl⟩

end step5

/-- **Lemma EX1-2C″** (fact 081a6e8977aebf8f), with only (P) (fact f6e8c173bef4cfa1) as a hypothesis.  For a
    connected bridgeless loopless cubic `P` with a 2-edge-cut `C` (ends `a1 ≠ a2`, `b1 ≠ b2`) such that at most one
    edge joins `a1, a2` and at most one joins `b1, b2`: if the edge closures `G_A`, `G_B` are EX1-good, `G_A^D` is
    EX1-good in case an edge joins `b1, b2`, and `G_B^D` is EX1-good in case an edge joins `a1, a2`, then `P` is
    EX1-good. -/
theorem ex1_2c'' {X : MGraph} {P : Fin X.m → Prop} (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    (hpb : ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f')
    (hA : EX1On C.clo) (hB : EX1On C.flip.clo)
    (hAD : (∃ r, P r ∧ X.Joins r C.b1 C.b2) → EX1On C.cloD)
    (hBD : (∃ r, P r ∧ X.Joins r C.a1 C.a2) → EX1On C.flip.cloD) :
    EX1On P :=
  ex1_2c hPS C hG hpa hpb hA hB (fun h => C.step5 hPS hG hpb (hAD h)) (fun h => C.flip.step5 hPS hG hpa (hBD h))


end RH2F

namespace RH2F
open MGraph

/-- **Layer 2 of the Lean formalization of RH2**: Lemma CL (fact ecc9734f558cf885) part (0) and the restriction parts
    of (CL1)–(CL4), the gluing ("if") parts of Lemma 2P (fact 8f2b69f6533dd766) (2) and (3) with Lemma 2P-END
    (fact 216c7379f3c57884), and Lemma EX1-2C″ (fact 081a6e8977aebf8f) from part (P) of fact f6e8c173bef4cfa1. -/
theorem layer2 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → InG (addEdge X C.a1 C.a2) C.clo) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → InG C.XD C.cloD) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P) (k : Nat) (c : Fin (addEdge X C.a1 C.a2).m → Fin k),
      StarOn C.clo k c → StarOn C.pole k (fun f => c (C.toClo f))) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P) (k : Nat) (c : Fin C.XD.m → Fin k),
      StarOn C.cloD k c → StarOn C.pole k (fun f => c (C.oD f))) ∧
    (∀ (X : MGraph) (P M : Fin X.m → Prop), PMOn P M → ∀ C : Cut2 P, M C.e1 → M C.e2 →
      ∀ φ ψ c : Fin X.m → Fin 6, StarOn C.pole 6 φ → StarOn C.flip.pole 6 ψ →
      (∀ f, C.pole f → c f = φ f) → (∀ f, C.flip.pole f → c f = ψ f) →
      (∀ e f f' u u', C.isCut e → X.Joins e u u' → P f → ¬ M f → X.Inc f u → P f' → ¬ M f' →
        X.Inc f' u' → c f ≠ c f') →
      StarOn P 6 c) ∧
    (∀ (X : MGraph) (P M : Fin X.m → Prop), Loopless X → PMOn P M → ∀ C : Cut2 P, ¬ M C.e1 → ¬ M C.e2 →
      ∀ φ ψ c : Fin X.m → Fin 6, StarOn C.pole 6 φ → StarOn C.flip.pole 6 ψ →
      (∀ f, C.pole f → c f = φ f) → (∀ f, C.flip.pole f → c f = ψ f) →
      (∀ f, P f → (M f ↔ c f = 5)) →
      (∀ r, M r → (X.Joins r C.a1 C.a2 ∨ X.Joins r C.b1 C.b2) → c C.e1 ≠ c C.e2) →
      (∀ e f f' u u', C.isCut e → X.Joins e u u' → f ≠ e → f' ≠ e → P f → ¬ M f → X.Inc f u → P f' →
        ¬ M f' → X.Inc f' u' → c f ≠ c f') →
      StarOn P 6 c) ∧
    (PStat → ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P →
      (∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f') →
      (∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f') →
      EX1On C.clo → EX1On C.flip.clo →
      ((∃ r, P r ∧ X.Joins r C.b1 C.b2) → EX1On C.cloD) →
      ((∃ r, P r ∧ X.Joins r C.a1 C.a2) → EX1On C.flip.cloD) →
      EX1On P) :=
  ⟨fun _ _ C hG => C.clo_inG hG,
   fun _ _ C hG => C.cloD_inG hG,
   fun _ _ C _ c hc => C.pole_of_clo c hc,
   fun _ _ C _ c hc => C.pole_of_cloD c hc,
   fun _ _ _ hM C h1 h2 φ ψ c hφ hψ hcφ hcψ hd => glue_M hM C h1 h2 φ ψ c hφ hψ hcφ hcψ hd,
   fun _ _ _ hl hM C h1 h2 φ ψ c hφ hψ hcφ hcψ hcl hF1 hF2 =>
     glue_F hl hM C h1 h2 φ ψ c hφ hψ hcφ hcψ hcl hF1 hF2,
   fun hPS _ _ C hG hpa hpb hA hB hAD hBD => ex1_2c'' hPS C hG hpa hpb hA hB hAD hBD⟩

end RH2F
