-- Lean proof of fact 75fc19c47ee38b89 (RH2F.layer10); added by fact_submit, do not edit
import MhFact_3e79907cfcc0085b
set_option backward.isDefEq.respectTransparency false

-- ===== from II1.lean =====
/-
  II1.lean — Lemma II-2CUT (fact f32e854e8647f5e9), parts (A), (B), (C), in the pole form of the RH2 layers:
  gluing two pole colourings across a 2-edge-cut without any perfect matching, with the colour permutation of
  Step 1 (= `perm_4a`, Lemma 2P(4a)); and the 2-sidedness of an EX1-good closure.
-/

namespace RH2F
open MGraph
open Classical

section ii1
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `P` has exactly three edges at `x` -/
def CubicAt (P : Fin X.m → Prop) (x : Fin X.n) : Prop :=
  ∃ a b c, P a ∧ P b ∧ P c ∧ X.Inc a x ∧ X.Inc b x ∧ X.Inc c x ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ d, P d → X.Inc d x → d = a ∨ d = b ∨ d = c

theorem cubicAt_of_cubic (h : CubicOn P) {x : Fin X.n} (hx : meets P x) : CubicAt P x := h x hx

/-- at the `A`-end `u` of a cut edge, with three edges at `u`, there are exactly two edges inside `A` -/
theorem Cut2.pairAt (C : Cut2 P) {e : Fin X.m} {u : Fin X.n} (hu3 : CubicAt P u) (he : C.isCut e)
    (heu : X.Inc e u) (hu : C.S u = true) :
    ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ X.Inc f u ∧ X.Inc f' u ∧ ∀ g, C.inA g → X.Inc g u → g = f ∨ g = f' := by
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hu3
  have hPe : P e := C.pole_P (Or.inr he)
  have nc : ∀ g, P g → X.Inc g u → g ≠ e → C.inA g := fun g hg hgu hne => C.F_at_A he heu hu hg hgu hne
  have ncut : ∀ g, C.inA g → g ≠ e := fun g hg h => C.not_inA_of_cut (h ▸ he) hg
  rcases hall e hPe heu with rfl | rfl | rfl
  · refine ⟨q, r, dqr, nc q hq iq (Ne.symm dpq), nc r hr ir (Ne.symm dpr), iq, ir, fun g hg hgu => ?_⟩
    rcases hall g hg.1 hgu with h | h | h
    · exact absurd h (ncut g hg)
    · exact Or.inl h
    · exact Or.inr h
  · refine ⟨p, r, dpr, nc p hp ip dpq, nc r hr ir (Ne.symm dqr), ip, ir, fun g hg hgu => ?_⟩
    rcases hall g hg.1 hgu with h | h | h
    · exact Or.inl h
    · exact absurd h (ncut g hg)
    · exact Or.inr h
  · refine ⟨p, q, dpq, nc p hp ip dpr, nc q hq iq dqr, ip, iq, fun g hg hgu => ?_⟩
    rcases hall g hg.1 hgu with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (ncut g hg)

/-- the colour set at the `A`-end of a cut edge, as a pair -/
theorem Cut2.psetPair (C : Cut2 P) (χ : Fin X.m → Fin 6) {e : Fin X.m} {u : Fin X.n} (hu3 : CubicAt P u)
    (he : C.isCut e) (heu : X.Inc e u) (hu : C.S u = true) :
    ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ X.Inc f u ∧ X.Inc f' u ∧
      (∀ κ, C.Pset χ u κ ↔ κ = χ f ∨ κ = χ f') ∧ ∀ g, C.inA g → X.Inc g u → g = f ∨ g = f' := by
  obtain ⟨f, f', hne, hf, hf', i, i', hall⟩ := C.pairAt hu3 he heu hu
  refine ⟨f, f', hne, hf, hf', i, i', fun κ => ⟨?_, ?_⟩, hall⟩
  · rintro ⟨g, hg, hgu, rfl⟩
    rcases hall g hg hgu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨f, hf, i, rfl⟩
    · exact ⟨f', hf', i', rfl⟩

/-- **Gluing of pole colourings without a matching** (II-2CUT, Step 2, in pole form).  `c` agrees with a star
    colouring `φ` of `A⁺` and `ψ` of `B⁺`, and at each cut edge the other edges at its two ends get different
    colours.  Then `c` is a star colouring of `P`. -/
theorem glue_nM (C : Cut2 P) (φ ψ c : Fin X.m → Fin 6)
    (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f)
    (hdisj : ∀ e f f' u u', C.isCut e → X.Joins e u u' → P f → f ≠ e → X.Inc f u → P f' → f' ≠ e →
      X.Inc f' u' → c f ≠ c f') :
    StarOn P 6 c := by
  refine ⟨glue_prop C φ ψ c hφ hψ hcφ hcψ, ?_⟩
  intro w h1 h2 h3 h4 hb
  by_cases c2 : C.isCut w.e2
  · exact hdisj _ _ _ _ _ c2 w.h2 h1 w.e1_ne_e2 w.inc_e1_v1 h3 (Ne.symm w.e2_ne_e3) w.inc_e3_v2 hb.1
  by_cases c3 : C.isCut w.e3
  · exact hdisj _ _ _ _ _ c3 w.h3 h2 w.e2_ne_e3 w.inc_e2_v2 h4 (Ne.symm w.e3_ne_e4) w.inc_e4_v3 hb.2
  exact glue_mid C φ ψ c hφ hψ hcφ hcψ w h1 h2 h3 h4 c2 c3 hb

/-- colour sets under a colour swap -/
theorem Cut2.pset_swap (C : Cut2 P) (φ : Fin X.m → Fin 6) (a b : Fin 6) (v : Fin X.n) (κ : Fin 6) :
    C.Pset (fun f => swapc a b (φ f)) v (swapc a b κ) ↔ C.Pset φ v κ := by
  constructor
  · rintro ⟨f, hf, hfv, h⟩
    exact ⟨f, hf, hfv, swapc_inj a b _ _ h⟩
  · rintro ⟨f, hf, hfv, rfl⟩
    exact ⟨f, hf, hfv, rfl⟩

theorem Cut2.tsmall_swap (C : Cut2 P) (φ : Fin X.m → Fin 6) (a b : Fin 6) (h : C.TSmall φ) :
    C.TSmall (fun f => swapc a b (φ f)) := by
  intro h'
  apply h
  intro κ
  rw [← C.pset_swap φ a b C.a1 κ, ← C.pset_swap φ a b C.a2 κ]
  exact h' _

theorem Cut2.tmeet_swap (C : Cut2 P) (φ : Fin X.m → Fin 6) (a b : Fin 6) (h : C.TMeet φ) :
    C.TMeet (fun f => swapc a b (φ f)) := by
  obtain ⟨κ, h1, h2⟩ := h
  exact ⟨swapc a b κ, (C.pset_swap φ a b C.a1 κ).2 h1, (C.pset_swap φ a b C.a2 κ).2 h2⟩

/-- the cut edges get colour `5` after the swap -/
theorem Cut2.swap_cut (C : Cut2 P) (φ : Fin X.m → Fin 6) (hφe : φ C.e1 = φ C.e2) {f : Fin X.m} (hf : C.isCut f) :
    swapc (φ C.e1) 5 (φ f) = 5 := by
  rcases hf with rfl | rfl
  · exact swapc_left _ _
  · rw [← hφe]; exact swapc_left _ _

/-- the two colours at a cut end, avoiding the cut colour `5` -/
theorem Cut2.side_pair (C : Cut2 P) (χ : Fin X.m → Fin 6) (hχ : StarOn C.pole 6 χ)
    (h5 : ∀ f, C.isCut f → χ f = 5) {e : Fin X.m} {u : Fin X.n} (hu3 : CubicAt P u) (he : C.isCut e)
    (heu : X.Inc e u) (hu : C.S u = true) :
    ∃ f f', χ f ≠ 5 ∧ χ f' ≠ 5 ∧ χ f ≠ χ f' ∧ (∀ κ, C.Pset χ u κ ↔ κ = χ f ∨ κ = χ f') ∧
      ∀ g, C.inA g → X.Inc g u → χ g = χ f ∨ χ g = χ f' := by
  obtain ⟨f, f', hne, hf, hf', i, i', hset, hall⟩ := C.psetPair χ hu3 he heu hu
  have n5 : ∀ g, C.inA g → X.Inc g u → χ g ≠ 5 := by
    intro g hg hgu h
    have hge : g ≠ e := fun h' => C.not_inA_of_cut (h' ▸ he) hg
    exact hχ.1 g e ⟨hge, u, hgu, heu⟩ (Or.inl hg) (Or.inr he) (h.trans (h5 e he).symm)
  refine ⟨f, f', n5 f hf i, n5 f' hf' i', hχ.1 f f' ⟨hne, u, i, i'⟩ (Or.inl hf) (Or.inl hf'), hset, ?_⟩
  intro g hg hgu
  rcases hall g hg hgu with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **II-2CUT (A), pole form.**  Three edges at each of `a1, a2, b1, b2`; star colourings `φ` of `A⁺` and `ψ` of
    `B⁺`, each giving both cut edges one colour; and the overlap condition `{t_A, t_B} ≠ {0, 2}` in the form
    `(t_A ≤ 1 or t_B ≥ 1) and (t_A ≥ 1 or t_B ≤ 1)`.  Then `P` is star 6-colourable. -/
theorem Cut2.glue_ts (C : Cut2 P) (ha1 : CubicAt P C.a1) (ha2 : CubicAt P C.a2) (hb1 : CubicAt P C.b1)
    (hb2 : CubicAt P C.b2) (φ ψ : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hφe : φ C.e1 = φ C.e2)
    (hψ : StarOn C.flip.pole 6 ψ) (hψe : ψ C.e1 = ψ C.e2)
    (hcond : (C.TSmall φ ∨ C.flip.TMeet ψ) ∧ (C.TMeet φ ∨ C.flip.TSmall ψ)) :
    Colourable P 6 := by
  -- normalise: the cut colour becomes 5 on both sides
  let φ' : Fin X.m → Fin 6 := fun f => swapc (φ C.e1) 5 (φ f)
  let ψ' : Fin X.m → Fin 6 := fun f => swapc (ψ C.e1) 5 (ψ f)
  have hφ' : StarOn C.pole 6 φ' := starOn_map _ (swapc_inj _ _) hφ
  have hψ' : StarOn C.flip.pole 6 ψ' := starOn_map _ (swapc_inj _ _) hψ
  have φ5 : ∀ f, C.isCut f → φ' f = 5 := fun f hf => C.swap_cut φ hφe hf
  have ψ5 : ∀ f, C.flip.isCut f → ψ' f = 5 := fun f hf => C.flip.swap_cut ψ hψe hf
  have hcond' : (C.TSmall φ' ∨ C.flip.TMeet ψ') ∧ (C.TMeet φ' ∨ C.flip.TSmall ψ') := by
    refine ⟨hcond.1.imp (C.tsmall_swap φ _ _) (C.flip.tmeet_swap ψ _ _),
      hcond.2.imp (C.tmeet_swap φ _ _) (C.flip.tsmall_swap ψ _ _)⟩
  obtain ⟨f1, f1', s1n, s1n', s1d, hS1, cS1⟩ :=
    C.side_pair φ' hφ' φ5 ha1 (Or.inl rfl) (joins_inc_left C.j1) C.sa1
  obtain ⟨f2, f2', s2n, s2n', s2d, hS2, cS2⟩ :=
    C.side_pair φ' hφ' φ5 ha2 (Or.inr rfl) (joins_inc_left C.j2) C.sa2
  obtain ⟨g1, g1', t1n, t1n', t1d, hT1, cT1⟩ :=
    C.flip.side_pair ψ' hψ' ψ5 hb1 (Or.inl rfl) (joins_inc_right C.j1) C.flip.sa1
  obtain ⟨g2, g2', t2n, t2n', t2d, hT2, cT2⟩ :=
    C.flip.side_pair ψ' hψ' ψ5 hb2 (Or.inr rfl) (joins_inc_right C.j2) C.flip.sa2
  have disj_of : ∀ {D : Cut2 P} {χ : Fin X.m → Fin 6} {u v : Fin X.n} {x x' y y' : Fin 6},
      (∀ κ, D.Pset χ u κ ↔ κ = x ∨ κ = x') → (∀ κ, D.Pset χ v κ ↔ κ = y ∨ κ = y') → SDisj x x' y y' →
      ¬ ∃ κ, D.Pset χ u κ ∧ D.Pset χ v κ := by
    rintro D χ u v x x' y y' hu hv hd ⟨κ, h1, h2⟩
    rcases (hu κ).1 h1 with rfl | rfl <;> rcases (hv _).1 h2 with h | h
    · exact hd.1 h
    · exact hd.2.1 h
    · exact hd.2.2.1 h
    · exact hd.2.2.2 h
  have eq_of : ∀ {D : Cut2 P} {χ : Fin X.m → Fin 6} {u v : Fin X.n} {x x' y y' : Fin 6},
      (∀ κ, D.Pset χ u κ ↔ κ = x ∨ κ = x') → (∀ κ, D.Pset χ v κ ↔ κ = y ∨ κ = y') → SEq x x' y y' →
      ∀ κ, D.Pset χ u κ ↔ D.Pset χ v κ := by
    intro D χ u v x x' y y' hu hv he κ
    rw [hu κ, hv κ]
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact ⟨fun h => h.symm, fun h => h.symm⟩
  obtain ⟨σ, σi, σ5, x1, x2, x3, x4, x5, x6, x7, x8⟩ :=
    perm_4a (φ' f1) (φ' f1') (φ' f2) (φ' f2') (ψ' g1) (ψ' g1') (ψ' g2) (ψ' g2') s1n s1n' s2n s2n' t1n t1n' t2n
      t2n' s1d s2d t1d t2d
      ⟨fun h => by
        rcases hcond'.2 with h' | h'
        · exact disj_of hS1 hS2 h.1 h'
        · exact h' (eq_of hT1 hT2 h.2),
       fun h => by
        rcases hcond'.1 with h' | h'
        · exact h' (eq_of hS1 hS2 h.1)
        · exact disj_of hT1 hT2 h.2 h'⟩
  -- the glued colouring
  let c : Fin X.m → Fin 6 := fun f => if C.flip.inA f then σ (ψ' f) else φ' f
  have hcA' : ∀ f, ¬ C.flip.inA f → c f = φ' f := fun f hf => by simp only [c, if_neg hf]
  have hcB' : ∀ f, C.flip.inA f → c f = σ (ψ' f) := fun f hf => by simp only [c, if_pos hf]
  have hcφ : ∀ f, C.pole f → c f = φ' f := by
    intro f hf
    apply hcA'
    rcases hf with h | h
    · exact C.not_flip_of_inA h
    · exact C.flip.not_inA_of_cut h
  have hcψ : ∀ f, C.flip.pole f → c f = σ (ψ' f) := by
    intro f hf
    rcases hf with h | h
    · exact hcB' f h
    · rw [hcA' f (C.flip.not_inA_of_cut h), φ5 f h, ψ5 f h, σ5]
  have cross : ∀ f f', ((C.inA f ∧ X.Inc f C.a1 ∧ C.flip.inA f' ∧ X.Inc f' C.b1) ∨
      (C.inA f ∧ X.Inc f C.a2 ∧ C.flip.inA f' ∧ X.Inc f' C.b2)) → c f ≠ c f' := by
    rintro f f' (⟨hfA, hfu, hf'B, hf'u⟩ | ⟨hfA, hfu, hf'B, hf'u⟩)
    · rw [hcA' f (C.not_flip_of_inA hfA), hcB' f' hf'B]
      rcases cS1 f hfA hfu with h | h <;> rcases cT1 f' hf'B hf'u with h' | h' <;> rw [h, h'] <;>
        first | exact Ne.symm x1 | exact Ne.symm x2 | exact Ne.symm x3 | exact Ne.symm x4
    · rw [hcA' f (C.not_flip_of_inA hfA), hcB' f' hf'B]
      rcases cS2 f hfA hfu with h | h <;> rcases cT2 f' hf'B hf'u with h' | h' <;> rw [h, h'] <;>
        first | exact Ne.symm x5 | exact Ne.symm x6 | exact Ne.symm x7 | exact Ne.symm x8
  have hdisj : ∀ e f f' u u', C.isCut e → X.Joins e u u' → P f → f ≠ e → X.Inc f u → P f' → f' ≠ e →
      X.Inc f' u' → c f ≠ c f' := by
    -- the ends of a cut edge are `a_i` (side `A`) and `b_i` (side `B`)
    have ends : ∀ e u u', C.isCut e → X.Joins e u u' → C.S u = true →
        (u = C.a1 ∧ u' = C.b1 ∧ e = C.e1) ∨ (u = C.a2 ∧ u' = C.b2 ∧ e = C.e2) := by
      intro e u u' he hj hu
      rcases C.cutA he (joins_inc_left hj) hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine Or.inl ⟨rfl, ?_, rfl⟩
        rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h C.a1_ne_b1
      · refine Or.inr ⟨rfl, ?_, rfl⟩
        rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h C.a2_ne_b2
    have atA : ∀ e u f, C.isCut e → X.Inc e u → C.S u = true → P f → f ≠ e → X.Inc f u → C.inA f :=
      fun e u f he heu hu hf hfe hfu => C.F_at_A he heu hu hf hfu hfe
    have atB : ∀ e u f, C.isCut e → X.Inc e u → C.S u = false → P f → f ≠ e → X.Inc f u → C.flip.inA f :=
      fun e u f he heu hu hf hfe hfu => C.flip.F_at_A he heu (Cut2.flip_true hu) hf hfu hfe
    intro e f f' u u' he hj hf hfe hfu hf' hf'e hf'u
    rcases C.cut_sides he hj with ⟨hu, hu'⟩ | ⟨hu, hu'⟩
    · have hfA := atA e u f he (joins_inc_left hj) hu hf hfe hfu
      have hf'B := atB e u' f' he (joins_inc_right hj) hu' hf' hf'e hf'u
      rcases ends e u u' he hj hu with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact cross f f' (Or.inl ⟨hfA, hfu, hf'B, hf'u⟩)
      · exact cross f f' (Or.inr ⟨hfA, hfu, hf'B, hf'u⟩)
    · have hf'A := atA e u' f' he (joins_inc_right hj) hu' hf' hf'e hf'u
      have hfB := atB e u f he (joins_inc_left hj) hu hf hfe hfu
      rcases ends e u' u he (Or.symm hj) hu' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Ne.symm (cross f' f (Or.inl ⟨hf'A, hf'u, hfB, hfu⟩))
      · exact Ne.symm (cross f' f (Or.inr ⟨hf'A, hf'u, hfB, hfu⟩))
  exact ⟨c, glue_nM C φ' (fun f => σ (ψ' f)) c hφ' (starOn_map σ σi hψ') hcφ hcψ hdisj⟩

/-- `G_A` is 2-sided at `g_A`, in pole form: pole colourings (both cut edges one colour) with `t ≤ 1` and with
    `t ≥ 1` -/
def Cut2.TwoSided (C : Cut2 P) : Prop :=
  (∃ φ : Fin X.m → Fin 6, StarOn C.pole 6 φ ∧ φ C.e1 = φ C.e2 ∧ C.TSmall φ) ∧
    (∃ φ : Fin X.m → Fin 6, StarOn C.pole 6 φ ∧ φ C.e1 = φ C.e2 ∧ C.TMeet φ)

/-- a star colouring of the closure gives a pole colouring with equal cut colours -/
theorem Cut2.pole_eq_of_clo (C : Cut2 P) (c : Fin (addEdge X C.a1 C.a2).m → Fin 6) :
    (fun f => c (C.toClo f)) C.e1 = (fun f => c (C.toClo f)) C.e2 := by
  show c (C.toClo C.e1) = c (C.toClo C.e2)
  rw [C.toClo_cut (Or.inl rfl), C.toClo_cut (Or.inr rfl)]

/-- **II-2CUT (A)**: a star 6-colouring of the closure `G_B` and a 2-sided side `A` give a star 6-colouring of
    `P` (three edges at `a1, a2, b1, b2`) -/
theorem Cut2.glue_two (C : Cut2 P) (ha1 : CubicAt P C.a1) (ha2 : CubicAt P C.a2) (hb1 : CubicAt P C.b1)
    (hb2 : CubicAt P C.b2) (hts : C.TwoSided) (hB : Colourable C.flip.clo 6) : Colourable P 6 := by
  obtain ⟨d, hd⟩ := hB
  let ψ : Fin X.m → Fin 6 := fun f => d (C.flip.toClo f)
  have hψ : StarOn C.flip.pole 6 ψ := C.flip.pole_of_clo d hd
  have hψe : ψ C.e1 = ψ C.e2 := C.flip.pole_eq_of_clo d
  -- the colour sets at `b1`, `b2` are nonempty
  have ψ5 : ∀ f, C.flip.isCut f → swapc (ψ C.e1) 5 (ψ f) = 5 := fun f hf => C.flip.swap_cut ψ hψe hf
  obtain ⟨g1, _, _, _, _, hT1, _⟩ :=
    C.flip.side_pair _ (starOn_map _ (swapc_inj _ _) hψ) ψ5 hb1 (Or.inl rfl) (joins_inc_right C.j1) C.flip.sa1
  have ne1 : C.flip.Pset ψ C.b1 (swapc (ψ C.e1) 5 (swapc (ψ C.e1) 5 (ψ g1))) := by
    rw [← C.flip.pset_swap ψ (ψ C.e1) 5 C.b1]
    exact (hT1 _).2 (Or.inl (by rw [swapc_invol]))
  by_cases hm : C.flip.TMeet ψ
  · by_cases hs : C.flip.TSmall ψ
    · obtain ⟨φ, hφ, hφe, hφs⟩ := hts.1
      exact C.glue_ts ha1 ha2 hb1 hb2 φ ψ hφ hφe hψ hψe ⟨Or.inl hφs, Or.inr hs⟩
    · obtain ⟨φ, hφ, hφe, hφm⟩ := hts.2
      exact C.glue_ts ha1 ha2 hb1 hb2 φ ψ hφ hφe hψ hψe ⟨Or.inr hm, Or.inl hφm⟩
  · by_cases hs : C.flip.TSmall ψ
    · obtain ⟨φ, hφ, hφe, hφs⟩ := hts.1
      exact C.glue_ts ha1 ha2 hb1 hb2 φ ψ hφ hφe hψ hψe ⟨Or.inl hφs, Or.inr hs⟩
    · -- equal and disjoint nonempty sets: impossible
      exfalso
      apply hm
      have heq : ∀ κ, C.flip.Pset ψ C.flip.a1 κ ↔ C.flip.Pset ψ C.flip.a2 κ :=
        fun κ => Classical.byContradiction fun h => hs fun h' => h (h' κ)
      exact ⟨_, ne1, (heq _).1 ne1⟩

/-- **II-2CUT (B), (C)**: an EX1-good closure `G_A` (at most one edge of `P` joining `a1, a2`) is 2-sided -/
theorem Cut2.twoSided_of_ex1 (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f') (hex : EX1On C.clo) :
    C.TwoSided := by
  have hGA := C.clo_inG hG
  have hlast : C.clo (Fin.last X.m) := Or.inl rfl
  constructor
  · obtain ⟨N0, hN0, hl0⟩ := hPS _ _ hGA _ hlast true
    obtain ⟨N, hN, hl, c0, hc0, hcl⟩ := hex _ hlast true ⟨N0, hN0, hl0⟩
    obtain ⟨c, hc⟩ := mc5_of_class hc0 hcl
    have hlN : N (Fin.last X.m) := hl.2 rfl
    exact ⟨_, C.pole_of_clo c hc.1, C.pole_eq_of_clo c, C.cl1_small hG hpa hN hc hlN⟩
  · obtain ⟨N0, hN0, hl0⟩ := hPS _ _ hGA _ hlast false
    obtain ⟨N, hN, hl, c0, hc0, hcl⟩ := hex _ hlast false ⟨N0, hN0, hl0⟩
    obtain ⟨c, hc⟩ := mc5_of_class hc0 hcl
    have hlN : ¬ N (Fin.last X.m) := fun h => by simpa using hl.1 h
    refine ⟨_, C.pole_of_clo c hc.1, C.pole_eq_of_clo c, 5, ?_, ?_⟩
    · have hcov := C.coverA_of_clo hN (s := False) ⟨fun h => hlN h, False.elim⟩
      obtain ⟨d, hdA, hdN, hdx, _⟩ := (hcov C.a1 C.sa1 ⟨C.e1, C.P1, joins_inc_left C.j1⟩).2 (fun h => h.1)
      exact ⟨d, hdA, hdx, (C.cl2_class hc d hdA).2 hdN⟩
    · have hcov := C.coverA_of_clo hN (s := False) ⟨fun h => hlN h, False.elim⟩
      obtain ⟨d, hdA, hdN, hdx, _⟩ := (hcov C.a2 C.sa2 ⟨C.e2, C.P2, joins_inc_left C.j2⟩).2 (fun h => h.1)
      exact ⟨d, hdA, hdx, (C.cl2_class hc d hdA).2 hdN⟩

end ii1

end RH2F

-- ===== from II2.lean =====
/-
  II2.lean — Lemma II-2CUT (fact f32e854e8647f5e9), part (D): the 2-edge-cut of the leaf graph T(G0, g) when `g` is
  not inside side `A`, and the transfer of the colourings of `G_A` (2-sidedness) and of T(G_B, ·) to it.
-/

namespace RH2F
open MGraph
open Classical

section ii2
variable {X : MGraph} {P : Fin X.m → Prop}

/-- star colourability pulls back along an embedding -/
theorem colourable_emb {Y : MGraph} {Q : Fin Y.m → Prop} (ρ : Fin Y.n → Fin X.n) (μ : Fin Y.m → Fin X.m)
    (hρ : ∀ x y, meets Q x → meets Q y → ρ x = ρ y → x = y)
    (hμ : ∀ a b, Q a → Q b → μ a = μ b → a = b) (hP : ∀ a, Q a → P (μ a))
    (hj : ∀ a, Q a → X.Joins (μ a) (ρ (Y.ends a).1) (ρ (Y.ends a).2)) (hc : Colourable P 6) :
    Colourable Q 6 := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨_, starOn_embed ρ μ (fun x y a b ha hb hax hby h => hρ x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h) hμ hP hj hc⟩

/-- incidence along a map respecting `Joins` -/
theorem inc_map {Y : MGraph} {ρ : Fin Y.n → Fin X.n} {a : Fin Y.m} {f : Fin X.m}
    (hj : X.Joins f (ρ (Y.ends a).1) (ρ (Y.ends a).2)) {v : Fin Y.n} (hv : Y.Inc a v) : X.Inc f (ρ v) := by
  rcases hv with h | h
  · rw [← h]; exact joins_inc_left hj
  · rw [← h]; exact joins_inc_right hj

/-- **transfer of 2-sidedness** along an embedding of poles -/
theorem Cut2.twoSided_emb {Y : MGraph} {P' : Fin Y.m → Prop} (C : Cut2 P) (C' : Cut2 P')
    (ρ : Fin Y.n → Fin X.n) (μ : Fin Y.m → Fin X.m)
    (hρ : ∀ x y, meets C'.pole x → meets C'.pole y → ρ x = ρ y → x = y)
    (hμ : ∀ a b, C'.pole a → C'.pole b → μ a = μ b → a = b)
    (hj : ∀ a, C'.pole a → X.Joins (μ a) (ρ (Y.ends a).1) (ρ (Y.ends a).2))
    (hcut : ∀ a, C'.isCut a → C.isCut (μ a)) (hinA : ∀ a, C'.inA a → C.inA (μ a))
    (hsec : ∀ d, C.inA d → ∃ a, C'.inA a ∧ μ a = d)
    (ha1 : ρ C'.a1 = C.a1) (ha2 : ρ C'.a2 = C.a2) (hts : C.TwoSided) : C'.TwoSided := by
  have hpole : ∀ a, C'.pole a → C.pole (μ a) := fun a h =>
    h.elim (fun h => Or.inl (hinA a h)) (fun h => Or.inr (hcut a h))
  have star : ∀ φ : Fin X.m → Fin 6, StarOn C.pole 6 φ → StarOn C'.pole 6 (fun a => φ (μ a)) := fun φ hφ =>
    starOn_embed ρ μ (fun x y a b ha hb hax hby h => hρ x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h) hμ hpole hj hφ
  have eqc : ∀ φ : Fin X.m → Fin 6, φ C.e1 = φ C.e2 → φ (μ C'.e1) = φ (μ C'.e2) := by
    intro φ hφ
    rcases hcut C'.e1 (Or.inl rfl) with h1 | h1 <;> rcases hcut C'.e2 (Or.inr rfl) with h2 | h2 <;>
      rw [h1, h2] <;> first | rfl | exact hφ | exact hφ.symm
  have mA1 : meets C'.pole C'.a1 := ⟨C'.e1, Or.inr (Or.inl rfl), joins_inc_left C'.j1⟩
  have mA2 : meets C'.pole C'.a2 := ⟨C'.e2, Or.inr (Or.inr rfl), joins_inc_left C'.j2⟩
  have pset : ∀ (φ : Fin X.m → Fin 6) (v : Fin Y.n), meets C'.pole v → ∀ κ,
      C'.Pset (fun a => φ (μ a)) v κ ↔ C.Pset φ (ρ v) κ := by
    intro φ v hv κ
    constructor
    · rintro ⟨a, ha, hav, hκ⟩
      exact ⟨μ a, hinA a ha, inc_map (hj a (Or.inl ha)) hav, hκ⟩
    · rintro ⟨d, hd, hdv, hκ⟩
      obtain ⟨a, ha, rfl⟩ := hsec d hd
      refine ⟨a, ha, ?_, hκ⟩
      rcases inc_of_joins (hj a (Or.inl ha)) hdv with h | h
      · have := hρ v _ hv ⟨a, Or.inl ha, Or.inl rfl⟩ h
        rw [this]; exact Or.inl rfl
      · have := hρ v _ hv ⟨a, Or.inl ha, Or.inr rfl⟩ h
        rw [this]; exact Or.inr rfl
  obtain ⟨⟨φ, hφ, hφe, hφs⟩, ⟨φ', hφ', hφe', hφm⟩⟩ := hts
  refine ⟨⟨_, star φ hφ, eqc φ hφe, ?_⟩, ⟨_, star φ' hφ', eqc φ' hφe', ?_⟩⟩
  · intro h
    apply hφs
    intro κ
    rw [← ha1, ← ha2, ← pset φ _ mA1, ← pset φ _ mA2]
    exact h κ
  · obtain ⟨κ, h1, h2⟩ := hφm
    exact ⟨κ, (pset φ' _ mA1 κ).2 (ha1 ▸ h1), (pset φ' _ mA2 κ).2 (ha2 ▸ h2)⟩

/-- the cut with the indices `1`, `2` exchanged -/
def Cut2.swap12 (C : Cut2 P) : Cut2 P where
  S := C.S
  e1 := C.e2
  e2 := C.e1
  a1 := C.a2
  a2 := C.a1
  b1 := C.b2
  b2 := C.b1
  P1 := C.P2
  P2 := C.P1
  j1 := C.j2
  j2 := C.j1
  sa1 := C.sa2
  sa2 := C.sa1
  sb1 := C.sb2
  sb2 := C.sb1
  ne12 := Ne.symm C.ne12
  ha := Ne.symm C.ha
  hb := Ne.symm C.hb
  cut := fun f hf h => (C.cut f hf h).symm

theorem Cut2.swap12_twoSided (C : Cut2 P) (h : C.TwoSided) : C.swap12.TwoSided := by
  have hp : ∀ f, C.swap12.pole f ↔ C.pole f := fun f => by
    unfold Cut2.pole Cut2.isCut Cut2.inA
    show (P f ∧ C.S _ = true ∧ C.S _ = true) ∨ (f = C.e2 ∨ f = C.e1) ↔ _
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  have hs : ∀ φ : Fin X.m → Fin 6, StarOn C.pole 6 φ → StarOn C.swap12.pole 6 φ := fun φ hφ =>
    ⟨fun a b hab ha hb => hφ.1 a b hab ((hp a).1 ha) ((hp b).1 hb),
     fun w h1 h2 h3 h4 => hφ.2 w ((hp _).1 h1) ((hp _).1 h2) ((hp _).1 h3) ((hp _).1 h4)⟩
  have hps : ∀ (φ : Fin X.m → Fin 6) v κ, C.swap12.Pset φ v κ ↔ C.Pset φ v κ := fun _ _ _ => Iff.rfl
  obtain ⟨⟨φ, hφ, hφe, hφs⟩, ⟨φ', hφ', hφe', hφm⟩⟩ := h
  refine ⟨⟨φ, hs φ hφ, hφe.symm, fun h' => hφs fun κ => ?_⟩, ⟨φ', hs φ' hφ', hφe'.symm, ?_⟩⟩
  · exact ((hps φ _ κ).symm.trans ((h' κ).symm.trans (hps φ _ κ)))
  · obtain ⟨κ, h1, h2⟩ := hφm
    exact ⟨κ, h2, h1⟩

/-! ### the leaf graph -/

/-- a side map of `X` extended to the leaf graph, with `x`, `ℓ` on side `false` -/
def liftS (S : Fin X.n → Bool) : Fin (X.n + 2) → Bool := fun v => if h : v.val < X.n then S ⟨v.val, h⟩ else false

theorem liftS_lv (S : Fin X.n → Bool) (v : Fin X.n) : liftS S (lv v) = S v := by
  simp [liftS, lv, v.isLt]
theorem liftS_vx (S : Fin X.n → Bool) : liftS S (vx X) = false := by simp [liftS, vx]
theorem liftS_vl (S : Fin X.n → Bool) : liftS S (vl X) = false := by simp [liftS, vl]

theorem leaf_cases (g : Fin X.m) (f : Fin (leafG X g).m) :
    (∃ d, f = oldE g d) ∨ f = newE g 0 (by decide) ∨ f = newE g 1 (by decide) ∨ f = newE g 2 (by decide) := by
  have hf : f.val < X.m + 3 := f.isLt
  by_cases h : f.val < X.m
  · exact Or.inl ⟨⟨f.val, h⟩, Fin.ext rfl⟩
  · right
    by_cases h0 : f.val = X.m
    · exact Or.inl (Fin.ext (by simp [newE, h0]))
    by_cases h1 : f.val = X.m + 1
    · exact Or.inr (Or.inl (Fin.ext (by simp [newE, h1])))
    · exact Or.inr (Or.inr (Fin.ext (by simp [newE]; omega)))

theorem oldE_inj {g d d' : Fin X.m} (h : oldE g d = oldE g d') : d = d' := by
  have := congrArg Fin.val h; simp [oldE] at this; exact Fin.ext this
theorem oldE_ne_new {g d : Fin X.m} (i : Nat) (hi : i < 3) : oldE g d ≠ newE g i hi := by
  intro h; have := congrArg Fin.val h; simp [oldE, newE] at this; have := d.isLt; omega
theorem new_ne {g : Fin X.m} {i j : Nat} (hi : i < 3) (hj : j < 3) (h : i ≠ j) : newE g i hi ≠ newE g j hj := by
  intro h'; have := congrArg Fin.val h'; simp [newE] at this; omega

theorem leaf_inc_old {g d : Fin X.m} {v : Fin X.n} : (leafG X g).Inc (oldE g d) (lv v) ↔ X.Inc d v := by
  unfold Inc; rw [ends_old]
  constructor
  · rintro (h | h)
    · exact Or.inl (lv_inj h)
    · exact Or.inr (lv_inj h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
theorem leaf_inc_old_vx {g d : Fin X.m} : ¬ (leafG X g).Inc (oldE g d) (vx X) := by
  unfold Inc; rw [ends_old]
  rintro (h | h)
  · exact lv_ne_vx _ h
  · exact lv_ne_vx _ h
theorem leaf_inc_old_vl {g d : Fin X.m} : ¬ (leafG X g).Inc (oldE g d) (vl X) := by
  unfold Inc; rw [ends_old]
  rintro (h | h)
  · exact lv_ne_vl _ h
  · exact lv_ne_vl _ h
theorem leaf_inc_new0 {g : Fin X.m} {v : Fin X.n} :
    (leafG X g).Inc (newE g 0 (by decide)) (lv v) ↔ (X.ends g).1 = v := by
  unfold Inc; rw [ends_new0]
  constructor
  · rintro (h | h)
    · exact lv_inj h
    · exact absurd h.symm (lv_ne_vx v)
  · intro h; exact Or.inl (by rw [h])
theorem leaf_inc_new1 {g : Fin X.m} {v : Fin X.n} :
    (leafG X g).Inc (newE g 1 (by decide)) (lv v) ↔ (X.ends g).2 = v := by
  unfold Inc; rw [ends_new1]
  constructor
  · rintro (h | h)
    · exact absurd h.symm (lv_ne_vx v)
    · exact lv_inj h
  · intro h; exact Or.inr (by rw [h])
theorem leaf_inc_new2 {g : Fin X.m} {v : Fin X.n} : ¬ (leafG X g).Inc (newE g 2 (by decide)) (lv v) := by
  unfold Inc; rw [ends_new2]
  rintro (h | h)
  · exact lv_ne_vx v h.symm
  · exact lv_ne_vl v h.symm
theorem leaf_joins_old {g d : Fin X.m} : (leafG X g).Joins (oldE g d) (lv (X.ends d).1) (lv (X.ends d).2) :=
  Or.inl (ends_old g d)

/-- three edges at an old vertex of the leaf graph -/
theorem cubicAt_leaf (hloop : Loopless X) (hcub : CubicOn P) {g : Fin X.m} (hg : P g) {v : Fin X.n}
    (hv : meets P v) : CubicAt (leafSet P g) (lv v) := by
  obtain ⟨a, b, c, ha, hb, hc, ia, ib, ic, dab, dac, dbc, hall⟩ := hcub v hv
  -- the edge replacing `d` at `v`
  let r : Fin X.m → Fin (leafG X g).m := fun d =>
    if d = g then (if (X.ends g).1 = v then newE g 0 (by decide) else newE g 1 (by decide)) else oldE g d
  have rset : ∀ d, P d → leafSet P g (r d) := by
    intro d hd
    by_cases h : d = g
    · simp only [r, if_pos h]; split
      · exact set_new P g 0 (by decide)
      · exact set_new P g 1 (by decide)
    · simp only [r, if_neg h]; exact (set_old P g d).2 ⟨hd, h⟩
  have rinc : ∀ d, X.Inc d v → (leafG X g).Inc (r d) (lv v) := by
    intro d hd
    by_cases h : d = g
    · subst h
      simp only [r, if_pos rfl]
      by_cases h1 : (X.ends d).1 = v
      · rw [if_pos h1]; exact leaf_inc_new0.2 h1
      · rw [if_neg h1]; exact leaf_inc_new1.2 (hd.resolve_left h1)
    · simp only [r, if_neg h]; exact leaf_inc_old.2 hd
  have rinj : ∀ d d', r d = r d' → d = d' := by
    intro d d' h
    by_cases h1 : d = g <;> by_cases h2 : d' = g
    · rw [h1, h2]
    · simp only [r, if_pos h1, if_neg h2] at h; split at h
      · exact absurd h.symm (oldE_ne_new 0 _)
      · exact absurd h.symm (oldE_ne_new 1 _)
    · simp only [r, if_neg h1, if_pos h2] at h; split at h
      · exact absurd h (oldE_ne_new 0 _)
      · exact absurd h (oldE_ne_new 1 _)
    · simp only [r, if_neg h1, if_neg h2] at h; exact oldE_inj h
  refine ⟨r a, r b, r c, rset a ha, rset b hb, rset c hc, rinc a ia, rinc b ib, rinc c ic,
    fun h => dab (rinj _ _ h), fun h => dac (rinj _ _ h), fun h => dbc (rinj _ _ h), ?_⟩
  intro d hd hdv
  have back : ∀ d0, P d0 → X.Inc d0 v → r d0 = d → d = r a ∨ d = r b ∨ d = r c := by
    intro d0 hd0 i0 hr
    rcases hall d0 hd0 i0 with rfl | rfl | rfl
    · exact Or.inl hr.symm
    · exact Or.inr (Or.inl hr.symm)
    · exact Or.inr (Or.inr hr.symm)
  rcases leaf_cases g d with ⟨d0, rfl⟩ | rfl | rfl | rfl
  · obtain ⟨hd0, hne⟩ := (set_old P g d0).1 hd
    exact back d0 hd0 (leaf_inc_old.1 hdv) (by simp only [r, if_neg hne])
  · have h1 := leaf_inc_new0.1 hdv
    exact back g hg (Or.inl h1) (by simp only [r, if_pos rfl, if_pos h1])
  · have h2 := leaf_inc_new1.1 hdv
    have h1 : (X.ends g).1 ≠ v := fun h => hloop g (h.trans h2.symm)
    exact back g hg (Or.inr h2) (by simp only [r, if_pos rfl, if_neg h1])
  · exact absurd hdv leaf_inc_new2

/-- three edges at the new vertex `x` -/
theorem cubicAt_leaf_vx {g : Fin X.m} : CubicAt (leafSet P g) (vx X) := by
  refine ⟨newE g 0 (by decide), newE g 1 (by decide), newE g 2 (by decide), set_new P g 0 _, set_new P g 1 _,
    set_new P g 2 _, ?_, ?_, ?_, new_ne _ _ (by decide), new_ne _ _ (by decide), new_ne _ _ (by decide), ?_⟩
  · unfold Inc; rw [ends_new0]; exact Or.inr rfl
  · unfold Inc; rw [ends_new1]; exact Or.inl rfl
  · unfold Inc; rw [ends_new2]; exact Or.inl rfl
  · intro d _ hdv
    rcases leaf_cases g d with ⟨d0, rfl⟩ | rfl | rfl | rfl
    · exact absurd hdv leaf_inc_old_vx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)


theorem leaf_joins_of {g d : Fin X.m} {x y : Fin X.n} (h : X.Joins d x y) :
    (leafG X g).Joins (oldE g d) (lv x) (lv y) := by
  rcases h with h | h
  · left; rw [ends_old, h]
  · right; rw [ends_old, h]

theorem Cut2.e1_ends (C : Cut2 P) :
    ((X.ends C.e1).1 = C.a1 ∧ (X.ends C.e1).2 = C.b1) ∨ ((X.ends C.e1).1 = C.b1 ∧ (X.ends C.e1).2 = C.a1) := by
  rcases C.j1 with h | h
  · left; rw [h]; exact ⟨rfl, rfl⟩
  · right; rw [h]; exact ⟨rfl, rfl⟩

theorem Cut2.flip_inA_S (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g) :
    C.S (X.ends g).1 = false ∧ C.S (X.ends g).2 = false := by
  have h1 := hg.2.1; have h2 := hg.2.2
  rw [Cut2.flip_S] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- (D)(i): `g` inside side `B`; the same cut in T(P, g), with `x`, `ℓ` on side `B` -/
def Cut2.leafB (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g) : Cut2 (leafSet P g) where
  S := liftS C.S
  e1 := oldE g C.e1
  e2 := oldE g C.e2
  a1 := lv C.a1
  a2 := lv C.a2
  b1 := lv C.b1
  b2 := lv C.b2
  P1 := (set_old P g C.e1).2 ⟨C.P1, fun h => C.flip.not_inA_of_cut (f := C.e1) (Or.inl rfl) (by rw [h]; exact hg)⟩
  P2 := (set_old P g C.e2).2 ⟨C.P2, fun h => C.flip.not_inA_of_cut (f := C.e2) (Or.inr rfl) (by rw [h]; exact hg)⟩
  j1 := leaf_joins_of C.j1
  j2 := leaf_joins_of C.j2
  sa1 := by rw [liftS_lv]; exact C.sa1
  sa2 := by rw [liftS_lv]; exact C.sa2
  sb1 := by rw [liftS_lv]; exact C.sb1
  sb2 := by rw [liftS_lv]; exact C.sb2
  ne12 := fun h => C.ne12 (oldE_inj h)
  ha := fun h => C.ha (lv_inj h)
  hb := fun h => C.hb (lv_inj h)
  cut := by
    intro f hf hS
    obtain ⟨s1, s2⟩ := C.flip_inA_S hg
    rcases leaf_cases g f with ⟨d, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨hd, _⟩ := (set_old P g d).1 hf
      rw [ends_old, liftS_lv, liftS_lv] at hS
      rcases C.cut d hd hS with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · exfalso; apply hS; rw [ends_new0, liftS_lv, liftS_vx, s1]
    · exfalso; apply hS; rw [ends_new1, liftS_lv, liftS_vx, s2]
    · exfalso; apply hS; rw [ends_new2, liftS_vx, liftS_vl]

/-- (D)(ii): `g = e1`; the cut of T(P, e1) with cut edges `a1x` and `e2`, `x` playing the role of `b1` -/
def Cut2.leafE (C : Cut2 P) : Cut2 (leafSet P C.e1) where
  S := liftS C.S
  e1 := if (X.ends C.e1).1 = C.a1 then newE C.e1 0 (by decide) else newE C.e1 1 (by decide)
  e2 := oldE C.e1 C.e2
  a1 := lv C.a1
  a2 := lv C.a2
  b1 := vx X
  b2 := lv C.b2
  P1 := by split <;> exact set_new _ _ _ _
  P2 := (set_old P C.e1 C.e2).2 ⟨C.P2, Ne.symm C.ne12⟩
  j1 := by
    split
    · next h => left; rw [ends_new0, h]
    · next h =>
      right; rw [ends_new1]
      rcases C.e1_ends with h' | h'
      · exact absurd h'.1 h
      · rw [h'.2]
  j2 := leaf_joins_of C.j2
  sa1 := by rw [liftS_lv]; exact C.sa1
  sa2 := by rw [liftS_lv]; exact C.sa2
  sb1 := liftS_vx C.S
  sb2 := by rw [liftS_lv]; exact C.sb2
  ne12 := by split <;> exact fun h => oldE_ne_new _ _ h.symm
  ha := fun h => C.ha (lv_inj h)
  hb := fun h => lv_ne_vx C.b2 h.symm
  cut := by
    intro f hf hS
    rcases leaf_cases C.e1 f with ⟨d, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨hd, hne⟩ := (set_old P C.e1 d).1 hf
      rw [ends_old, liftS_lv, liftS_lv] at hS
      rcases C.cut d hd hS with h | h
      · exact absurd h hne
      · exact Or.inr (by rw [h])
    · left
      rw [ends_new0, liftS_lv, liftS_vx] at hS
      rcases C.e1_ends with h' | h'
      · rw [if_pos h'.1]
      · exfalso; apply hS; rw [h'.1, C.sb1]
    · left
      rw [ends_new1, liftS_lv, liftS_vx] at hS
      rcases C.e1_ends with h' | h'
      · exfalso; apply hS; rw [h'.2, C.sb1]
      · rw [if_neg (fun h => C.a1_ne_b1 (h.symm.trans h'.1))]
    · exfalso; apply hS; rw [ends_new2, liftS_vx, liftS_vl]


/-! ### maps from the leaf graph back to `X` (the pole side) -/

/-- vertices: old vertices to themselves, `x` and `ℓ` to `b` -/
def rhoL (b : Fin X.n) : Fin (X.n + 2) → Fin X.n := fun v => if h : v.val < X.n then ⟨v.val, h⟩ else b
/-- edges: old edges to themselves, new edges to `e` -/
def muL {g : Fin X.m} (e : Fin X.m) : Fin (leafG X g).m → Fin X.m := fun i => if h : i.val < X.m then ⟨i.val, h⟩ else e

theorem rhoL_lv (b v : Fin X.n) : rhoL b (lv v) = v := by
  apply Fin.ext; simp [rhoL, lv, v.isLt]
theorem rhoL_vx (b : Fin X.n) : rhoL b (vx X) = b := by simp [rhoL, vx]
theorem muL_old {g : Fin X.m} (e d : Fin X.m) : muL (g := g) e (oldE g d) = d := by
  apply Fin.ext; simp [muL, oldE, d.isLt]
theorem muL_new {g : Fin X.m} (e : Fin X.m) (i : Nat) (hi : i < 3) : muL (g := g) e (newE g i hi) = e := by
  simp [muL, newE]

theorem inc_old_lv {g d : Fin X.m} {x : Fin (leafG X g).n} (h : (leafG X g).Inc (oldE g d) x) :
    ∃ w, x = lv w ∧ X.Inc d w := by
  unfold Inc at h; rw [ends_old] at h
  rcases h with h | h
  · exact ⟨_, h.symm, Or.inl rfl⟩
  · exact ⟨_, h.symm, Or.inr rfl⟩

/-- the edges of the `A`-pole of `leafB` are old -/
theorem Cut2.leafB_pole (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g) {a : Fin (leafG X g).m}
    (ha : (C.leafB hg).pole a) : ∃ d, a = oldE g d ∧ C.pole d := by
  rcases ha with h | h | h
  · rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨hd, _⟩ := (set_old P g d).1 h.1
      have s1 := h.2.1; have s2 := h.2.2
      rw [ends_old] at s1 s2
      exact ⟨d, rfl, Or.inl ⟨hd, by simpa [Cut2.leafB, liftS_lv] using s1, by simpa [Cut2.leafB, liftS_lv] using s2⟩⟩
    · have s2 := h.2.2; rw [ends_new0] at s2; simp [Cut2.leafB, liftS_vx] at s2
    · have s1 := h.2.1; rw [ends_new1] at s1; simp [Cut2.leafB, liftS_vx] at s1
    · have s1 := h.2.1; rw [ends_new2] at s1; simp [Cut2.leafB, liftS_vx] at s1
  · exact ⟨C.e1, h, Or.inr (Or.inl rfl)⟩
  · exact ⟨C.e2, h, Or.inr (Or.inr rfl)⟩

theorem Cut2.leafB_inA (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g) {d : Fin X.m} :
    (C.leafB hg).inA (oldE g d) ↔ C.inA d := by
  unfold Cut2.inA
  rw [ends_old, set_old]
  show (P d ∧ d ≠ g) ∧ liftS C.S (lv _) = true ∧ liftS C.S (lv _) = true ↔ _
  rw [liftS_lv, liftS_lv]
  constructor
  · rintro ⟨⟨hd, _⟩, h1, h2⟩; exact ⟨hd, h1, h2⟩
  · rintro ⟨hd, h1, h2⟩
    refine ⟨⟨hd, fun h => ?_⟩, h1, h2⟩
    rw [h] at h1; rw [(C.flip_inA_S hg).1] at h1; exact absurd h1 (by decide)

/-- 2-sidedness passes from `C` to `leafB` -/
theorem Cut2.leafB_twoSided (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g) (hts : C.TwoSided) :
    (C.leafB hg).TwoSided := by
  have vtx : ∀ x, meets (C.leafB hg).pole x → ∃ w, x = lv w := by
    rintro x ⟨a, ha, hax⟩
    obtain ⟨d, rfl, _⟩ := C.leafB_pole hg ha
    obtain ⟨w, rfl, _⟩ := inc_old_lv hax
    exact ⟨w, rfl⟩
  apply C.twoSided_emb (C.leafB hg) (rhoL C.b1) (muL C.e1)
  · intro x y hx hy h
    obtain ⟨w, rfl⟩ := vtx x hx
    obtain ⟨w', rfl⟩ := vtx y hy
    rw [rhoL_lv, rhoL_lv] at h; rw [h]
  · intro a b ha hb h
    obtain ⟨d, rfl, _⟩ := C.leafB_pole hg ha
    obtain ⟨d', rfl, _⟩ := C.leafB_pole hg hb
    rw [muL_old, muL_old] at h; rw [h]
  · intro a ha
    obtain ⟨d, rfl, _⟩ := C.leafB_pole hg ha
    rw [ends_old, muL_old]; simp only [rhoL_lv]; exact joins_ends d
  · rintro a (rfl | rfl)
    · show C.isCut (muL C.e1 (oldE g C.e1)); rw [muL_old]; exact Or.inl rfl
    · show C.isCut (muL C.e1 (oldE g C.e2)); rw [muL_old]; exact Or.inr rfl
  · intro a ha
    obtain ⟨d, rfl, _⟩ := C.leafB_pole hg (Or.inl ha)
    rw [muL_old]; exact (C.leafB_inA hg).1 ha
  · intro d hd
    exact ⟨oldE g d, (C.leafB_inA hg).2 hd, muL_old _ _⟩
  · exact rhoL_lv _ _
  · exact rhoL_lv _ _
  · exact hts


theorem Cut2.leafE_e1 (C : Cut2 P) :
    C.leafE.e1 = newE C.e1 0 (by decide) ∨ C.leafE.e1 = newE C.e1 1 (by decide) := by
  by_cases h : (X.ends C.e1).1 = C.a1
  · left; show (if (X.ends C.e1).1 = C.a1 then newE C.e1 0 (by decide) else newE C.e1 1 (by decide)) = _
    rw [if_pos h]
  · right; show (if (X.ends C.e1).1 = C.a1 then newE C.e1 0 (by decide) else newE C.e1 1 (by decide)) = _
    rw [if_neg h]

theorem Cut2.leafE_inA (C : Cut2 P) {d : Fin X.m} : C.leafE.inA (oldE C.e1 d) ↔ C.inA d := by
  unfold Cut2.inA
  rw [ends_old, set_old]
  show (P d ∧ d ≠ C.e1) ∧ liftS C.S (lv _) = true ∧ liftS C.S (lv _) = true ↔ _
  rw [liftS_lv, liftS_lv]
  constructor
  · rintro ⟨⟨hd, _⟩, h1, h2⟩; exact ⟨hd, h1, h2⟩
  · rintro ⟨hd, h1, h2⟩
    exact ⟨⟨hd, fun h => C.not_inA_of_cut (Or.inl h) ⟨hd, h1, h2⟩⟩, h1, h2⟩

/-- the edges of the `A`-pole of `leafE`: old pole edges other than `e1`, and the new cut edge -/
theorem Cut2.leafE_pole (C : Cut2 P) {a : Fin (leafG X C.e1).m} (ha : C.leafE.pole a) :
    (∃ d, a = oldE C.e1 d ∧ (C.inA d ∨ d = C.e2)) ∨ a = C.leafE.e1 := by
  rcases ha with h | h | h
  · left
    rcases leaf_cases C.e1 a with ⟨d, rfl⟩ | rfl | rfl | rfl
    · exact ⟨d, rfl, Or.inl (C.leafE_inA.1 h)⟩
    · have s2 := h.2.2; rw [ends_new0] at s2; simp [Cut2.leafE, liftS_vx] at s2
    · have s1 := h.2.1; rw [ends_new1] at s1; simp [Cut2.leafE, liftS_vx] at s1
    · have s1 := h.2.1; rw [ends_new2] at s1; simp [Cut2.leafE, liftS_vx] at s1
  · exact Or.inr h
  · exact Or.inl ⟨C.e2, h, Or.inr rfl⟩

theorem Cut2.leafE_twoSided (C : Cut2 P) (hts : C.TwoSided) : C.leafE.TwoSided := by
  -- the vertices of the pole: old vertices other than `b1`, and `x`
  have vtx : ∀ x, meets C.leafE.pole x → (∃ w, x = lv w ∧ w ≠ C.b1) ∨ x = vx X := by
    rintro x ⟨a, ha, hax⟩
    rcases C.leafE_pole ha with ⟨d, rfl, hd⟩ | rfl
    · obtain ⟨w, rfl, hw⟩ := inc_old_lv hax
      refine Or.inl ⟨w, rfl, fun h => ?_⟩
      subst h
      rcases hd with hd | rfl
      · have := C.side_of_inA hd hw; rw [C.sb1] at this; exact absurd this (by decide)
      · rcases inc_of_joins C.j2 hw with h | h
        · exact C.a2_ne_b1 h.symm
        · exact C.hb h
    · rcases inc_of_joins C.leafE.j1 hax with h | h
      · exact Or.inl ⟨C.a1, h, C.a1_ne_b1⟩
      · exact Or.inr h
  have mu1 : muL (g := C.e1) C.e1 C.leafE.e1 = C.e1 := by
    rcases C.leafE_e1 with h | h <;> rw [h, muL_new]
  have old_ne : ∀ d, (C.inA d ∨ d = C.e2) → d ≠ C.e1 := by
    rintro d (hd | rfl) h
    · exact C.not_inA_of_cut (Or.inl h) hd
    · exact C.ne12 h.symm
  apply C.twoSided_emb C.leafE (rhoL C.b1) (muL C.e1)
  · intro x y hx hy h
    rcases vtx x hx with ⟨w, rfl, hw⟩ | rfl <;> rcases vtx y hy with ⟨w', rfl, hw'⟩ | rfl
    · rw [rhoL_lv, rhoL_lv] at h; rw [h]
    · rw [rhoL_lv, rhoL_vx] at h; exact absurd h hw
    · rw [rhoL_lv, rhoL_vx] at h; exact absurd h.symm hw'
    · rfl
  · intro a b ha hb h
    rcases C.leafE_pole ha with ⟨d, rfl, hd⟩ | rfl <;> rcases C.leafE_pole hb with ⟨d', rfl, hd'⟩ | rfl
    · rw [muL_old, muL_old] at h; rw [h]
    · rw [muL_old, mu1] at h; exact absurd h (old_ne d hd)
    · rw [muL_old, mu1] at h; exact absurd h.symm (old_ne d' hd')
    · rfl
  · intro a ha
    rcases C.leafE_pole ha with ⟨d, rfl, _⟩ | rfl
    · rw [ends_old, muL_old]; simp only [rhoL_lv]; exact joins_ends d
    · rw [mu1]
      rcases C.leafE.j1 with h | h <;> rw [h]
      · show X.Joins C.e1 (rhoL C.b1 (lv C.a1)) (rhoL C.b1 (vx X))
        rw [rhoL_lv, rhoL_vx]; exact C.j1
      · show X.Joins C.e1 (rhoL C.b1 (vx X)) (rhoL C.b1 (lv C.a1))
        rw [rhoL_lv, rhoL_vx]; exact Or.symm C.j1
  · rintro a (rfl | rfl)
    · rw [mu1]; exact Or.inl rfl
    · show C.isCut (muL C.e1 (oldE C.e1 C.e2)); rw [muL_old]; exact Or.inr rfl
  · intro a ha
    rcases C.leafE_pole (Or.inl ha) with ⟨d, rfl, _⟩ | rfl
    · rw [muL_old]; exact C.leafE_inA.1 ha
    · exact absurd ha (C.leafE.not_inA_of_cut (Or.inl rfl))
  · intro d hd
    exact ⟨oldE C.e1 d, C.leafE_inA.2 hd, muL_old _ _⟩
  · exact rhoL_lv _ _
  · exact rhoL_lv _ _
  · exact hts


/-! ### the `B′`-closure of the leaf cut and the leaf graph of `G_B` -/

theorem leafG_m (g : Fin X.m) : (leafG X g).m = X.m + 3 := rfl
theorem addEdge_m' (G : MGraph) (u w : Fin G.n) : (addEdge G u w).m = G.m + 1 := rfl

section clos
variable (g : Fin X.m) (u w : Fin X.n)

/-- (D)(i): edges of `(T(P, g))_{B′}` (in `addEdge (leafG X g) (lv u) (lv w)`) to edges of T(G_B, g) -/
def muB : Fin (addEdge (leafG X g) (lv u) (lv w)).m → Fin (leafG (addEdge X u w) (Fin.castSucc g)).m :=
  fun i => ⟨if i.val < X.m then i.val else if i.val = X.m + 3 then X.m else i.val + 1, by
    have hi : i.val < X.m + 3 + 1 := i.isLt
    show _ < X.m + 1 + 3
    split_ifs <;> omega⟩

theorem muB_last : muB g u w (Fin.last _) = oldE (Fin.castSucc g) (Fin.last X.m) := by
  apply Fin.ext; simp [muB, oldE, leafG_m]
theorem muB_old (d : Fin X.m) : muB g u w (Fin.castSucc (oldE g d)) = oldE (Fin.castSucc g) (Fin.castSucc d) := by
  apply Fin.ext; simp [muB, oldE, d.isLt]
theorem muB_new (i : Nat) (hi : i < 3) : muB g u w (Fin.castSucc (newE g i hi)) = newE (Fin.castSucc g) i hi := by
  apply Fin.ext; simp only [muB, newE, Fin.coe_castSucc, addEdge_m']; split_ifs <;> omega

theorem muB_inj (a b : Fin (addEdge (leafG X g) (lv u) (lv w)).m) (h : muB g u w a = muB g u w b) : a = b := by
  have ha : a.val < X.m + 3 + 1 := a.isLt
  have hb : b.val < X.m + 3 + 1 := b.isLt
  have := congrArg Fin.val h
  simp only [muB] at this
  apply Fin.ext
  split_ifs at this <;> omega

theorem muB_ends (a : Fin (addEdge (leafG X g) (lv u) (lv w)).m) :
    (leafG (addEdge X u w) (Fin.castSucc g)).ends (muB g u w a) = (addEdge (leafG X g) (lv u) (lv w)).ends a := by
  rcases addEdge_cases a with rfl | ⟨d, rfl⟩
  · rw [muB_last, ends_old, addEdge_ends_new, addEdge_ends_new]; rfl
  · rw [addEdge_ends_old]
    rcases leaf_cases g d with ⟨d0, rfl⟩ | rfl | rfl | rfl
    · rw [muB_old, ends_old, ends_old, addEdge_ends_old]; rfl
    · rw [muB_new, ends_new0, ends_new0, addEdge_ends_old]; rfl
    · rw [muB_new, ends_new1, ends_new1, addEdge_ends_old]; rfl
    · rw [muB_new, ends_new2, ends_new2]; rfl

/-- (D)(ii): edges of `(T(P, e1))_{B′}` (in `addEdge (leafG X e1) x (lv w)`) to edges of T(G_B, g_B) -/
def muE : Fin (addEdge (leafG X g) (vx X) (lv w)).m → Fin (leafG (addEdge X u w) (Fin.last X.m)).m :=
  fun i => ⟨if i.val < X.m then i.val else if i.val = X.m + 2 then X.m + 3 else
    if i.val = X.m + 3 then X.m + 2 else X.m + 1, by
    show _ < X.m + 1 + 3
    split_ifs <;> omega⟩

theorem muE_last : muE g u w (Fin.last _) = newE (Fin.last X.m) 1 (by decide) := by
  apply Fin.ext; simp only [muE, newE, Fin.val_last, leafG_m, addEdge_m']; split_ifs <;> omega
theorem muE_old (d : Fin X.m) : muE g u w (Fin.castSucc (oldE g d)) = oldE (Fin.last X.m) (Fin.castSucc d) := by
  apply Fin.ext; simp [muE, oldE, d.isLt]
theorem muE_new0 : muE g u w (Fin.castSucc (newE g 0 (by decide))) = newE (Fin.last X.m) 0 (by decide) := by
  apply Fin.ext; simp only [muE, newE, Fin.coe_castSucc, addEdge_m']; split_ifs <;> omega
theorem muE_new1 : muE g u w (Fin.castSucc (newE g 1 (by decide))) = newE (Fin.last X.m) 0 (by decide) := by
  apply Fin.ext; simp only [muE, newE, Fin.coe_castSucc, addEdge_m']; split_ifs <;> omega
theorem muE_new2 : muE g u w (Fin.castSucc (newE g 2 (by decide))) = newE (Fin.last X.m) 2 (by decide) := by
  apply Fin.ext; simp only [muE, newE, Fin.coe_castSucc, addEdge_m']; split_ifs <;> omega

theorem muE_eq (a b : Fin (addEdge (leafG X g) (vx X) (lv w)).m) (h : muE g u w a = muE g u w b) :
    a = b ∨ (a.val = X.m ∧ b.val = X.m + 1) ∨ (a.val = X.m + 1 ∧ b.val = X.m) := by
  have ha : a.val < X.m + 3 + 1 := a.isLt
  have hb : b.val < X.m + 3 + 1 := b.isLt
  have := congrArg Fin.val h
  simp only [muE] at this
  by_cases hab : a.val = b.val
  · exact Or.inl (Fin.ext hab)
  · right; split_ifs at this <;> omega

end clos

/-- (D)(i): a star colouring of T(G_B, g) gives one of the `B′`-closure of `leafB` -/
theorem Cut2.leafB_closure (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g)
    (hB : Colourable (leafSet C.flip.clo (Fin.castSucc g : Fin (addEdge X C.b1 C.b2).m)) 6) :
    Colourable (C.leafB hg).flip.clo 6 := by
  refine colourable_emb (X := leafG (addEdge X C.b1 C.b2) (Fin.castSucc g))
    (P := leafSet C.flip.clo (Fin.castSucc g : Fin (addEdge X C.b1 C.b2).m))
    (Y := addEdge (leafG X g) (lv C.b1) (lv C.b2)) (Q := (C.leafB hg).flip.clo)
    (fun v => v) (muB g C.b1 C.b2)
    (fun x y _ _ h => h) (fun a b _ _ h => muB_inj g C.b1 C.b2 a b h) ?_
    (fun a _ => Or.inl (muB_ends g C.b1 C.b2 a)) hB
  rintro a (rfl | ⟨d, rfl, hd⟩)
  · rw [muB_last, set_old]
    exact ⟨Or.inl rfl, fun h => by have := congrArg Fin.val h; simp at this; have := g.isLt; omega⟩
  · rcases leaf_cases g d with ⟨d0, rfl⟩ | rfl | rfl | rfl
    · rw [muB_old, set_old]
      obtain ⟨hd0, h1, h2⟩ := hd
      obtain ⟨hd0, hne⟩ := (set_old P g d0).1 hd0
      rw [ends_old] at h1 h2
      have s1 : C.S (X.ends d0).1 = false := by
        simp only [Cut2.flip_S] at h1; simpa [Cut2.leafB, liftS_lv] using h1
      have s2 : C.S (X.ends d0).2 = false := by
        simp only [Cut2.flip_S] at h2; simpa [Cut2.leafB, liftS_lv] using h2
      refine ⟨Or.inr ⟨d0, rfl, hd0, by rw [Cut2.flip_S, s1]; rfl, by rw [Cut2.flip_S, s2]; rfl⟩, fun h => hne ?_⟩
      exact Fin.castSucc_injective _ h
    · rw [muB_new]; exact set_new _ _ _ _
    · rw [muB_new]; exact set_new _ _ _ _
    · rw [muB_new]; exact set_new _ _ _ _

/-- (D)(ii): a star colouring of T(G_B, g_B) gives one of the `B′`-closure of `leafE` -/
theorem Cut2.leafE_closure (C : Cut2 P) (hloop : Loopless X)
    (hB : Colourable (leafSet C.flip.clo (Fin.last X.m : Fin (addEdge X C.b1 C.b2).m)) 6) :
    Colourable C.leafE.flip.clo 6 := by
  -- membership of the new edges `sx`, `xt` in the closure forces their old end to be `b1`
  have n0 : C.leafE.flip.inA (newE C.e1 0 (by decide)) → (X.ends C.e1).1 = C.b1 := by
    rintro ⟨_, h1, _⟩
    rw [ends_new0] at h1
    have : C.S (X.ends C.e1).1 = false := by
      simp only [Cut2.flip_S] at h1; simpa [Cut2.leafE, liftS_lv] using h1
    rcases C.e1_ends with h | h
    · rw [h.1, C.sa1] at this; exact absurd this (by decide)
    · exact h.1
  have n1 : C.leafE.flip.inA (newE C.e1 1 (by decide)) → (X.ends C.e1).2 = C.b1 := by
    rintro ⟨_, _, h2⟩
    rw [ends_new1] at h2
    have : C.S (X.ends C.e1).2 = false := by
      simp only [Cut2.flip_S] at h2; simpa [Cut2.leafE, liftS_lv] using h2
    rcases C.e1_ends with h | h
    · exact h.2
    · rw [h.2, C.sa1] at this; exact absurd this (by decide)
  have not01 : C.leafE.flip.inA (newE C.e1 0 (by decide)) → C.leafE.flip.inA (newE C.e1 1 (by decide)) → False :=
    fun h0 h1 => hloop C.e1 ((n0 h0).trans (n1 h1).symm)
  -- the closure edges with value `X.m` and `X.m + 1`
  have v0 : ∀ a, C.leafE.flip.clo a → a.val = X.m → C.leafE.flip.inA (newE C.e1 0 (by decide)) := by
    rintro a (rfl | ⟨d, rfl, hd⟩) h
    · simp [leafG_m] at h
    · have : d = newE C.e1 0 (by decide) := Fin.ext (by simp only [newE]; simpa using h)
      rw [← this]; exact hd
  have v1 : ∀ a, C.leafE.flip.clo a → a.val = X.m + 1 → C.leafE.flip.inA (newE C.e1 1 (by decide)) := by
    rintro a (rfl | ⟨d, rfl, hd⟩) h
    · simp [leafG_m] at h
    · have : d = newE C.e1 1 (by decide) := Fin.ext (by simp only [newE]; simpa using h)
      rw [← this]; exact hd
  refine colourable_emb (X := leafG (addEdge X C.b1 C.b2) (Fin.last X.m))
    (P := leafSet C.flip.clo (Fin.last X.m : Fin (addEdge X C.b1 C.b2).m))
    (Y := addEdge (leafG X C.e1) (vx X) (lv C.b2)) (Q := C.leafE.flip.clo)
    (fun v => v) (muE C.e1 C.b1 C.b2) (fun x y _ _ h => h) ?_ ?_ ?_ hB
  · intro a b ha hb h
    rcases muE_eq C.e1 C.b1 C.b2 a b h with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h'
    · exact absurd (v1 b hb h2) (fun h => not01 (v0 a ha h1) h)
    · exact absurd (v1 a ha h1) (fun h => not01 (v0 b hb h2) h)
  · rintro a (rfl | ⟨d, rfl, hd⟩)
    · rw [muE_last]; exact set_new _ _ _ _
    · rcases leaf_cases C.e1 d with ⟨d0, rfl⟩ | rfl | rfl | rfl
      · rw [muE_old, set_old]
        obtain ⟨hd0, h1, h2⟩ := hd
        obtain ⟨hd0, hne⟩ := (set_old P C.e1 d0).1 hd0
        rw [ends_old] at h1 h2
        have s1 : C.S (X.ends d0).1 = false := by
          simp only [Cut2.flip_S] at h1; simpa [Cut2.leafE, liftS_lv] using h1
        have s2 : C.S (X.ends d0).2 = false := by
          simp only [Cut2.flip_S] at h2; simpa [Cut2.leafE, liftS_lv] using h2
        exact ⟨Or.inr ⟨d0, rfl, hd0, by rw [Cut2.flip_S, s1]; rfl, by rw [Cut2.flip_S, s2]; rfl⟩,
          Fin.castSucc_ne_last d0⟩
      · rw [muE_new0]; exact set_new _ _ _ _
      · rw [muE_new1]; exact set_new _ _ _ _
      · rw [muE_new2]; exact set_new _ _ _ _
  · rintro a (rfl | ⟨d, rfl, hd⟩)
    · left; rw [muE_last, ends_new1, addEdge_ends_new, addEdge_ends_new]; rfl
    · rcases leaf_cases C.e1 d with ⟨d0, rfl⟩ | rfl | rfl | rfl
      · left; rw [muE_old, ends_old, addEdge_ends_old, addEdge_ends_old, ends_old]; rfl
      · left; rw [muE_new0, ends_new0, addEdge_ends_new, addEdge_ends_old, ends_new0, n0 hd]; rfl
      · right; rw [muE_new1, ends_new0, addEdge_ends_new, addEdge_ends_old, ends_new1, n1 hd]; rfl
      · left; rw [muE_new2, ends_new2, addEdge_ends_old, ends_new2]; rfl


/-- **II-2CUT (D)(i)**: `g` inside side `B`, `G_A` 2-sided, T(G_B, g) star 6-colourable ⟹ T(P, g) star
    6-colourable -/
theorem Cut2.leaf_glue_B (hloop : Loopless X) (hcub : CubicOn P) (C : Cut2 P) {g : Fin X.m} (hg : C.flip.inA g)
    (hts : C.TwoSided) (hB : Colourable (leafSet C.flip.clo (Fin.castSucc g : Fin (addEdge X C.b1 C.b2).m)) 6) :
    Colourable (leafSet P g) 6 :=
  (C.leafB hg).glue_two (cubicAt_leaf hloop hcub hg.1 ⟨C.e1, C.P1, joins_inc_left C.j1⟩)
    (cubicAt_leaf hloop hcub hg.1 ⟨C.e2, C.P2, joins_inc_left C.j2⟩)
    (cubicAt_leaf hloop hcub hg.1 ⟨C.e1, C.P1, joins_inc_right C.j1⟩)
    (cubicAt_leaf hloop hcub hg.1 ⟨C.e2, C.P2, joins_inc_right C.j2⟩)
    (C.leafB_twoSided hg hts) (C.leafB_closure hg hB)

/-- **II-2CUT (D)(ii)**: `g = e1`, `G_A` 2-sided, T(G_B, g_B) star 6-colourable ⟹ T(P, e1) star 6-colourable -/
theorem Cut2.leaf_glue_E (hloop : Loopless X) (hcub : CubicOn P) (C : Cut2 P) (hts : C.TwoSided)
    (hB : Colourable (leafSet C.flip.clo (Fin.last X.m : Fin (addEdge X C.b1 C.b2).m)) 6) :
    Colourable (leafSet P C.e1) 6 :=
  C.leafE.glue_two (cubicAt_leaf hloop hcub C.P1 ⟨C.e1, C.P1, joins_inc_left C.j1⟩)
    (cubicAt_leaf hloop hcub C.P1 ⟨C.e2, C.P2, joins_inc_left C.j2⟩) cubicAt_leaf_vx
    (cubicAt_leaf hloop hcub C.P1 ⟨C.e2, C.P2, joins_inc_right C.j2⟩)
    (C.leafE_twoSided hts) (C.leafE_closure hloop hB)

end ii2

end RH2F

namespace RH2F
open MGraph

/-- **Layer 10 of the Lean formalization** (II-RED2 route): Lemma II-2CUT (fact f32e854e8647f5e9), parts (A),
    (B)+(C) and (D), in the pole form of the RH2 layers. -/
theorem layer10 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), CubicAt P C.a1 → CubicAt P C.a2 → CubicAt P C.b1 →
      CubicAt P C.b2 → C.TwoSided → Colourable C.flip.clo 6 → Colourable P 6) ∧
    (PStat → ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P →
      (∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f') → EX1On C.clo → C.TwoSided) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P) (g : Fin X.m), Loopless X → CubicOn P → C.flip.inA g →
      C.TwoSided → Colourable (leafSet C.flip.clo (Fin.castSucc g : Fin (addEdge X C.b1 C.b2).m)) 6 →
      Colourable (leafSet P g) 6) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), Loopless X → CubicOn P → C.TwoSided →
      Colourable (leafSet C.flip.clo (Fin.last X.m : Fin (addEdge X C.b1 C.b2).m)) 6 →
      Colourable (leafSet P C.e1) 6) :=
  ⟨fun _ _ C => C.glue_two, fun hPS _ _ C => Cut2.twoSided_of_ex1 hPS C,
   fun _ _ C _ hl hc hg => C.leaf_glue_B hl hc hg, fun _ _ C hl hc => C.leaf_glue_E hl hc⟩

end RH2F
