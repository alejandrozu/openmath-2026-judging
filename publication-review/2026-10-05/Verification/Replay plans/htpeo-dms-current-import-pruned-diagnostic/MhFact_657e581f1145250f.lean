-- Lean proof of fact 657e581f1145250f (RH2F.layer3); added by fact_submit, do not edit
import MhFact_c64b6bd62b78d841



-- ===== from RH2Glue.lean =====
/-
  RH2Glue.lean — gluing lemmas for pole colourings (Lemma 2P, fact 8f2b69f6533dd766, parts (2)–(4)), in the form
  used by Lemma SR (fact 5a68c9cb62d7148d), steps (G2), (G3)/(G4):
  * `Cut2.glue_nc` : F-type, side `B` "without cross ends" (pendant colours `γ ≠ γ′`, the F-edge at `b1` avoids `γ′`,
                     the one at `b2` avoids `γ`), side `A` with distinct pendant colours  — steps (G3), (G4), Step 5.
  * `Cut2.glue_eq` : F-type, equal pendant colours on both sides, no matching rung joining `a1, a2` or `b1, b2`
                     — step (G2), Lemma 2P(4b).
-/

namespace RH2F
open MGraph

section glue2
variable {X : MGraph} {P : Fin X.m → Prop}

/-- facts about the glued matching of two F-type covers -/
theorem Cut2.glueF_facts (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} (hcovA : C.CoverA NA False)
    (hcovB : C.flip.CoverA NB False) :
    PMOn P (C.glueN NA NB False) ∧ (∀ e, C.isCut e → ¬ C.glueN NA NB False e) ∧
    (∀ e u f f', C.isCut e → X.Inc e u → f ≠ e → f' ≠ e → P f → ¬ C.glueN NA NB False f → X.Inc f u → P f' →
      ¬ C.glueN NA NB False f' → X.Inc f' u → f = f') := by
  have hM := C.pm_glue hcovA hcovB
  have nMcut : ∀ e, C.isCut e → ¬ C.glueN NA NB False e := fun e he h => (C.glueN_cut he).1 h
  refine ⟨hM, nMcut, ?_⟩
  intro e u f f' he heu hfe hf'e hf nf hfu hf' nf' hf'u
  apply Classical.byContradiction; intro hne
  exact fdeg2 hG.2.2.2 hM (C.pole_P (Or.inr he)) hf hf' (nMcut e he) nf nf' heu hfu hf'u (Ne.symm hfe)
    (Ne.symm hf'e) hne

/-- the F-edge (other than the cut edge) at an end `u ∈ A` of a cut edge lies inside `A` -/
theorem Cut2.F_at_A (C : Cut2 P) {e f : Fin X.m} {u : Fin X.n} (he : C.isCut e) (heu : X.Inc e u)
    (hu : C.S u = true) (hf : P f) (hfu : X.Inc f u) (hfe : f ≠ e) : C.inA f :=
  C.inA_of_notcut hf (fun hcf => C.cut_disj he hcf (Ne.symm hfe) heu hfu) hfu hu

/-- **(G3), (G4), Step 5**: gluing an `A⁺` colouring with distinct pendant colours to a `B⁺` colouring without
    cross ends. -/
theorem Cut2.glue_nc (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} (hcovA : C.CoverA NA False)
    (hcovB : C.flip.CoverA NB False) (φ ψ : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ)
    (hψ : StarOn C.flip.pole 6 ψ)
    (hφcl : ∀ f, C.inA f → (φ f = 5 ↔ NA f)) (hφ1 : φ C.e1 ≠ 5) (hφ2 : φ C.e2 ≠ 5) (hφne : φ C.e1 ≠ φ C.e2)
    (hψcl : ∀ f, C.flip.inA f → (ψ f = 5 ↔ NB f)) (hψ1 : ψ C.e1 ≠ 5) (hψ2 : ψ C.e2 ≠ 5) (hψne : ψ C.e1 ≠ ψ C.e2)
    (hβ1 : ∀ f, C.flip.inA f → ¬ NB f → X.Inc f C.b1 → ψ f ≠ ψ C.e2)
    (hβ2 : ∀ f, C.flip.inA f → ¬ NB f → X.Inc f C.b2 → ψ f ≠ ψ C.e1) :
    ∃ c, MC5 P (C.glueN NA NB False) c := by
  classical
  obtain ⟨hM, nMcut, Funiq⟩ := C.glueF_facts hG hcovA hcovB
  let M := C.glueN NA NB False
  obtain ⟨ρ, ρi, ρ5, ρ1, ρ2⟩ := perm_two hφ1 hφ2 hφne hψ1 hψ2 hψne
  have hρ5 : ∀ a, ρ a = 5 ↔ a = 5 := fun a => ⟨fun h => ρi _ _ (h.trans ρ5.symm), fun h => h ▸ ρ5⟩
  -- `α_i`
  have exα : ∀ (e : Fin X.m) (u : Fin X.n), C.isCut e → X.Inc e u →
      ∃ α : Fin 6, ∀ f, P f → ¬ M f → X.Inc f u → f ≠ e → ρ (φ f) = α := by
    intro e u he heu
    by_cases hex : ∃ f, P f ∧ ¬ M f ∧ X.Inc f u ∧ f ≠ e
    · obtain ⟨f0, h0, n0, i0, e0⟩ := hex
      exact ⟨ρ (φ f0), fun f hf nf hfu hfe => by rw [Funiq e u f f0 he heu hfe e0 hf nf hfu h0 n0 i0]⟩
    · exact ⟨0, fun f hf nf hfu hfe => absurd ⟨f, hf, nf, hfu, hfe⟩ hex⟩
  obtain ⟨α1, hα1⟩ := exα C.e1 C.a1 (Or.inl rfl) (joins_inc_left C.j1)
  obtain ⟨α2, hα2⟩ := exα C.e2 C.a2 (Or.inr rfl) (joins_inc_left C.j2)
  -- `β_i`
  have nNB : ∀ f, C.flip.inA f → ¬ M f → ¬ NB f := fun f hf nf h => nf ((C.glueN_B hf).2 h)
  have ψ5 : ∀ f, C.flip.inA f → ¬ NB f → ψ f ≠ 5 := fun f hf hn h => hn ((hψcl f hf).1 h)
  have propψ : ∀ f e u, C.flip.inA f → C.isCut e → X.Inc e u → X.Inc f u → ψ f ≠ ψ e := fun f e u hf he heu hfu =>
    hψ.1 f e ⟨fun h => C.flip.not_inA_of_cut (h ▸ he) hf, u, hfu, heu⟩ (Or.inl hf) (Or.inr he)
  obtain ⟨β1, hβ1g, hβ1v⟩ := uniq_val (fun f => P f ∧ ¬ M f ∧ X.Inc f C.b1 ∧ f ≠ C.e1) ψ
    (fun i j hi hj => Funiq C.e1 C.b1 i j (Or.inl rfl) (joins_inc_right C.j1) hi.2.2.2 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1
      hj.1 hj.2.1 hj.2.2.1)
    (ψ C.e1) (ψ C.e2)
    (fun f ⟨hf, nf, hfu, hfe⟩ => by
      have hfB := C.flip.F_at_A (Or.inl rfl) (joins_inc_right C.j1) C.flip.sa1 hf hfu hfe
      exact ⟨propψ f C.e1 C.b1 hfB (Or.inl rfl) (joins_inc_right C.j1) hfu, hβ1 f hfB (nNB f hfB nf) hfu,
        ψ5 f hfB (nNB f hfB nf)⟩)
  obtain ⟨β2, hβ2g, hβ2v⟩ := uniq_val (fun f => P f ∧ ¬ M f ∧ X.Inc f C.b2 ∧ f ≠ C.e2) ψ
    (fun i j hi hj => Funiq C.e2 C.b2 i j (Or.inr rfl) (joins_inc_right C.j2) hi.2.2.2 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1
      hj.1 hj.2.1 hj.2.2.1)
    (ψ C.e1) (ψ C.e2)
    (fun f ⟨hf, nf, hfu, hfe⟩ => by
      have hfB := C.flip.F_at_A (Or.inr rfl) (joins_inc_right C.j2) C.flip.sa2 hf hfu hfe
      exact ⟨hβ2 f hfB (nNB f hfB nf) hfu, propψ f C.e2 C.b2 hfB (Or.inr rfl) (joins_inc_right C.j2) hfu,
        ψ5 f hfB (nNB f hfB nf)⟩)
  obtain ⟨τ, τi, τ5, τγ, τγ', τ1, τ2⟩ := perm_4c (ψ C.e1) (ψ C.e2) α1 α2 β1 β2 hψne hψ1 hψ2 hβ1g hβ2g
  let c : Fin X.m → Fin 6 := fun f => if C.flip.inA f then τ (ψ f) else ρ (φ f)
  have hcA' : ∀ f, ¬ C.flip.inA f → c f = ρ (φ f) := fun f hf => by simp only [c, if_neg hf]
  have hcB' : ∀ f, C.flip.inA f → c f = τ (ψ f) := fun f hf => by simp only [c, if_pos hf]
  have hc1 : c C.e1 = ψ C.e1 := by rw [hcA' C.e1 (C.flip.not_inA_of_cut (Or.inl rfl))]; exact ρ1
  have hc2 : c C.e2 = ψ C.e2 := by rw [hcA' C.e2 (C.flip.not_inA_of_cut (Or.inr rfl))]; exact ρ2
  have hcφ : ∀ f, C.pole f → c f = ρ (φ f) := by
    intro f hf
    apply hcA'
    rcases hf with h | h
    · exact C.not_flip_of_inA h
    · exact C.flip.not_inA_of_cut h
  have hcψ : ∀ f, C.flip.pole f → c f = τ (ψ f) := by
    intro f hf
    rcases hf with h | h
    · exact hcB' f h
    · rcases h with h | h
      · rw [h]; show c C.e1 = τ (ψ C.e1); rw [hc1, τγ]
      · rw [h]; show c C.e2 = τ (ψ C.e2); rw [hc2, τγ']
  have hcl : ∀ f, P f → (M f ↔ c f = 5) := by
    intro f hf
    show C.glueN NA NB False f ↔ c f = 5
    rcases C.cases_P hf with h | h | h
    · rw [C.glueN_A h, hcA' f (C.not_flip_of_inA h), hρ5]; exact (hφcl f h).symm
    · rw [C.glueN_B h, hcB' f h]
      constructor
      · intro hn; rw [(hψcl f h).2 hn, τ5]
      · intro h5; exact (hψcl f h).1 (τi _ _ (h5.trans τ5.symm))
    · rw [C.glueN_cut h]
      constructor
      · intro hfalse; exact hfalse.elim
      · intro h5
        rcases h with rfl | rfl
        · rw [hc1] at h5; exact hψ1 h5
        · rw [hc2] at h5; exact hψ2 h5
  have hF1' : ∀ r, M r → (X.Joins r C.a1 C.a2 ∨ X.Joins r C.b1 C.b2) → c C.e1 ≠ c C.e2 :=
    fun _ _ _ => by rw [hc1, hc2]; exact hψne
  have cross : ∀ f f', ((P f ∧ ¬ M f ∧ f ≠ C.e1 ∧ X.Inc f C.a1 ∧ P f' ∧ ¬ M f' ∧ f' ≠ C.e1 ∧ X.Inc f' C.b1) ∨
      (P f ∧ ¬ M f ∧ f ≠ C.e2 ∧ X.Inc f C.a2 ∧ P f' ∧ ¬ M f' ∧ f' ≠ C.e2 ∧ X.Inc f' C.b2)) → c f ≠ c f' := by
    rintro f f' (⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u⟩ | ⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u⟩)
    · have hfA := C.F_at_A (Or.inl rfl) (joins_inc_left C.j1) C.sa1 hf hfu hfe
      have hf'B := C.flip.F_at_A (Or.inl rfl) (joins_inc_right C.j1) C.flip.sa1 hf' hf'u hf'e
      rw [hcA' f (C.not_flip_of_inA hfA), hα1 f hf nf hfu hfe, hcB' f' hf'B, hβ1v f' ⟨hf', nf', hf'u, hf'e⟩]
      exact Ne.symm τ1
    · have hfA := C.F_at_A (Or.inr rfl) (joins_inc_left C.j2) C.sa2 hf hfu hfe
      have hf'B := C.flip.F_at_A (Or.inr rfl) (joins_inc_right C.j2) C.flip.sa2 hf' hf'u hf'e
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
  exact ⟨c, glue_F hG.1 hM C (nMcut _ (Or.inl rfl)) (nMcut _ (Or.inr rfl)) (fun f => ρ (φ f)) (fun f => τ (ψ f)) c
    (starOn_map ρ ρi hφ) (starOn_map τ τi hψ) hcφ hcψ hcl hF1' hF2', hcl⟩

/-- **(G2), Lemma 2P(4b)**: gluing two F-type pole colourings with equal pendant colours, no matching rung. -/
theorem Cut2.glue_eq (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} (hcovA : C.CoverA NA False)
    (hcovB : C.flip.CoverA NB False) (φ ψ : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ)
    (hψ : StarOn C.flip.pole 6 ψ)
    (hφcl : ∀ f, C.inA f → (φ f = 5 ↔ NA f)) (hφ1 : φ C.e1 ≠ 5) (hφeq : φ C.e1 = φ C.e2)
    (hψcl : ∀ f, C.flip.inA f → (ψ f = 5 ↔ NB f)) (hψ1 : ψ C.e1 ≠ 5) (hψeq : ψ C.e1 = ψ C.e2)
    (hnoA : ∀ r, C.inA r → NA r → ¬ X.Joins r C.a1 C.a2)
    (hnoB : ∀ r, C.flip.inA r → NB r → ¬ X.Joins r C.b1 C.b2) :
    ∃ c, MC5 P (C.glueN NA NB False) c := by
  classical
  obtain ⟨hM, nMcut, Funiq⟩ := C.glueF_facts hG hcovA hcovB
  let M := C.glueN NA NB False
  let γ := ψ C.e1
  let ρ : Fin 6 → Fin 6 := swapc (φ C.e1) γ
  have ρi : ∀ a b, ρ a = ρ b → a = b := swapc_inj _ _
  have ρ5 : ρ 5 = 5 := swapc_other _ _ 5 (Ne.symm hφ1) (Ne.symm hψ1)
  have ρ1 : ρ (φ C.e1) = γ := swapc_left _ _
  have ρ2 : ρ (φ C.e2) = γ := by rw [← hφeq]; exact ρ1
  have hρ5 : ∀ a, ρ a = 5 ↔ a = 5 := fun a => ⟨fun h => ρi _ _ (h.trans ρ5.symm), fun h => h ▸ ρ5⟩
  have hφ' : StarOn C.pole 6 (fun f => ρ (φ f)) := starOn_map ρ ρi hφ
  have nNA : ∀ f, C.inA f → ¬ M f → ¬ NA f := fun f hf nf h => nf ((C.glueN_A hf).2 h)
  have nNB : ∀ f, C.flip.inA f → ¬ M f → ¬ NB f := fun f hf nf h => nf ((C.glueN_B hf).2 h)
  -- `α_i`: F-colours at `a_i` inside `A` (after `ρ`), different from `γ` and 5
  have exα : ∀ (e : Fin X.m) (u : Fin X.n), C.isCut e → X.Inc e u → C.S u = true →
      ∃ α, (α ≠ γ ∧ α ≠ γ ∧ α ≠ 5) ∧ ∀ f, P f ∧ ¬ M f ∧ X.Inc f u ∧ f ≠ e → ρ (φ f) = α := by
    intro e u he heu hu
    refine uniq_val (fun f => P f ∧ ¬ M f ∧ X.Inc f u ∧ f ≠ e) (fun f => ρ (φ f))
      (fun i j hi hj => Funiq e u i j he heu hi.2.2.2 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1 hj.1 hj.2.1 hj.2.2.1) γ γ ?_
    rintro f ⟨hf, nf, hfu, hfe⟩
    have hfA := C.F_at_A he heu hu hf hfu hfe
    have hne : ρ (φ f) ≠ γ := by
      have hγe : γ = ρ (φ e) := by rcases he with rfl | rfl; exact ρ1.symm; exact ρ2.symm
      rw [hγe]
      exact hφ'.1 f e ⟨fun h => C.not_inA_of_cut (h ▸ he) hfA, u, hfu, heu⟩ (Or.inl hfA) (Or.inr he)
    exact ⟨hne, hne, fun h => nNA f hfA nf ((hφcl f hfA).1 ((hρ5 _).1 h))⟩
  obtain ⟨α1, hα1g, hα1⟩ := exα C.e1 C.a1 (Or.inl rfl) (joins_inc_left C.j1) C.sa1
  obtain ⟨α2, hα2g, hα2⟩ := exα C.e2 C.a2 (Or.inr rfl) (joins_inc_left C.j2) C.sa2
  -- `β_i`: F-colours at `b_i` inside `B`
  have exβ : ∀ (e : Fin X.m) (u : Fin X.n), C.isCut e → X.Inc e u → C.S u = false →
      ∃ β, (β ≠ γ ∧ β ≠ γ ∧ β ≠ 5) ∧ ∀ f, P f ∧ ¬ M f ∧ X.Inc f u ∧ f ≠ e → ψ f = β := by
    intro e u he heu hu
    refine uniq_val (fun f => P f ∧ ¬ M f ∧ X.Inc f u ∧ f ≠ e) ψ
      (fun i j hi hj => Funiq e u i j he heu hi.2.2.2 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1 hj.1 hj.2.1 hj.2.2.1) γ γ ?_
    rintro f ⟨hf, nf, hfu, hfe⟩
    have hfB := C.flip.F_at_A he heu (Cut2.flip_true hu) hf hfu hfe
    have hne : ψ f ≠ γ := by
      have hγe : γ = ψ e := by rcases he with rfl | rfl; rfl; exact hψeq
      rw [hγe]
      exact hψ.1 f e ⟨fun h => C.flip.not_inA_of_cut (h ▸ he) hfB, u, hfu, heu⟩ (Or.inl hfB) (Or.inr he)
    exact ⟨hne, hne, fun h => nNB f hfB nf ((hψcl f hfB).1 h)⟩
  obtain ⟨β1, hβ1g, hβ1⟩ := exβ C.e1 C.b1 (Or.inl rfl) (joins_inc_right C.j1) C.sb1
  obtain ⟨β2, hβ2g, hβ2⟩ := exβ C.e2 C.b2 (Or.inr rfl) (joins_inc_right C.j2) C.sb2
  obtain ⟨σ, σi, σ5, σγ, s11, s12, s21, s22⟩ :=
    perm_g2f γ γ α1 α2 β1 β2 hψ1 hψ1 hα1g.1 hα1g.2.2 hα2g.1 hα2g.2.2 hβ1g.1 hβ1g.2.2 hβ2g.1 hβ2g.2.2
  let c : Fin X.m → Fin 6 := fun f => if C.flip.inA f then σ (ψ f) else ρ (φ f)
  have hcA' : ∀ f, ¬ C.flip.inA f → c f = ρ (φ f) := fun f hf => by simp only [c, if_neg hf]
  have hcB' : ∀ f, C.flip.inA f → c f = σ (ψ f) := fun f hf => by simp only [c, if_pos hf]
  have hc1 : c C.e1 = γ := by rw [hcA' C.e1 (C.flip.not_inA_of_cut (Or.inl rfl))]; exact ρ1
  have hc2 : c C.e2 = γ := by rw [hcA' C.e2 (C.flip.not_inA_of_cut (Or.inr rfl))]; exact ρ2
  have hcφ : ∀ f, C.pole f → c f = ρ (φ f) := by
    intro f hf
    apply hcA'
    rcases hf with h | h
    · exact C.not_flip_of_inA h
    · exact C.flip.not_inA_of_cut h
  have hcψ : ∀ f, C.flip.pole f → c f = σ (ψ f) := by
    intro f hf
    rcases hf with h | h
    · exact hcB' f h
    · rcases h with h | h
      · rw [h]; show c C.e1 = σ (ψ C.e1); rw [hc1, σγ]
      · rw [h]; show c C.e2 = σ (ψ C.e2); rw [hc2, ← hψeq, σγ]
  have hcl : ∀ f, P f → (M f ↔ c f = 5) := by
    intro f hf
    show C.glueN NA NB False f ↔ c f = 5
    rcases C.cases_P hf with h | h | h
    · rw [C.glueN_A h, hcA' f (C.not_flip_of_inA h), hρ5]; exact (hφcl f h).symm
    · rw [C.glueN_B h, hcB' f h]
      constructor
      · intro hn; rw [(hψcl f h).2 hn, σ5]
      · intro h5; exact (hψcl f h).1 (σi _ _ (h5.trans σ5.symm))
    · rw [C.glueN_cut h]
      constructor
      · intro hfalse; exact hfalse.elim
      · intro h5
        rcases h with rfl | rfl
        · rw [hc1] at h5; exact hψ1 h5
        · rw [hc2] at h5; exact hψ1 h5
  have hF1' : ∀ r, M r → (X.Joins r C.a1 C.a2 ∨ X.Joins r C.b1 C.b2) → c C.e1 ≠ c C.e2 := by
    intro r hr hj
    exfalso
    rcases hr with ⟨hA, hn⟩ | ⟨hB, hn⟩ | ⟨_, hfalse⟩
    · rcases hj with hj | hj
      · exact hnoA r hA hn hj
      · have := C.side_of_inA hA (joins_inc_left hj); rw [C.sb1] at this; exact absurd this (by decide)
    · rcases hj with hj | hj
      · have := C.flip.side_of_inA hB (joins_inc_left hj); rw [Cut2.flip_S, C.sa1] at this
        exact absurd this (by decide)
      · exact hnoB r hB hn hj
    · exact hfalse
  have cross : ∀ f f', ((P f ∧ ¬ M f ∧ f ≠ C.e1 ∧ X.Inc f C.a1 ∧ P f' ∧ ¬ M f' ∧ f' ≠ C.e1 ∧ X.Inc f' C.b1) ∨
      (P f ∧ ¬ M f ∧ f ≠ C.e2 ∧ X.Inc f C.a2 ∧ P f' ∧ ¬ M f' ∧ f' ≠ C.e2 ∧ X.Inc f' C.b2)) → c f ≠ c f' := by
    rintro f f' (⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u⟩ | ⟨hf, nf, hfe, hfu, hf', nf', hf'e, hf'u⟩)
    · have hfA := C.F_at_A (Or.inl rfl) (joins_inc_left C.j1) C.sa1 hf hfu hfe
      have hf'B := C.flip.F_at_A (Or.inl rfl) (joins_inc_right C.j1) C.flip.sa1 hf' hf'u hf'e
      rw [hcA' f (C.not_flip_of_inA hfA), hα1 f ⟨hf, nf, hfu, hfe⟩, hcB' f' hf'B, hβ1 f' ⟨hf', nf', hf'u, hf'e⟩]
      exact Ne.symm s11
    · have hfA := C.F_at_A (Or.inr rfl) (joins_inc_left C.j2) C.sa2 hf hfu hfe
      have hf'B := C.flip.F_at_A (Or.inr rfl) (joins_inc_right C.j2) C.flip.sa2 hf' hf'u hf'e
      rw [hcA' f (C.not_flip_of_inA hfA), hα2 f ⟨hf, nf, hfu, hfe⟩, hcB' f' hf'B, hβ2 f' ⟨hf', nf', hf'u, hf'e⟩]
      exact Ne.symm s22
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
  exact ⟨c, glue_F hG.1 hM C (nMcut _ (Or.inl rfl)) (nMcut _ (Or.inr rfl)) (fun f => ρ (φ f)) (fun f => σ (ψ f)) c
    hφ' (starOn_map σ σi hψ) hcφ hcψ hcl hF1' hF2', hcl⟩

end glue2

end RH2F

-- ===== from RH2GlueM.lean =====
/-
  RH2GlueM.lean — M-type gluing of pole colourings (Lemma 2P(2) with the permutation of Lemma 2P(4a),
  fact 8f2b69f6533dd766): if `{t_φ, t_ψ} ≠ {0, 2}` then a colour permutation of side `B` makes the glued colouring
  a star colouring with the glued matching as colour class 5.
-/

namespace RH2F
open MGraph

/-- the normalised 2P(4a) problem: `S1 = T1 = {0, 1}`; the overlap condition `{t_φ, t_ψ} ≠ {0, 2}` -/
def g4aChk : Bool := all5 fun s2 => all5 fun s2' => all5 fun t2 => all5 fun t2' =>
  s2 == s2' || t2 == t2' ||
  -- S disjoint and T equal
  ((s2 != 0 && s2 != 1 && s2' != 0 && s2' != 1) && ((t2 == 0 && t2' == 1) || (t2 == 1 && t2' == 0))) ||
  -- S equal and T disjoint
  (((s2 == 0 && s2' == 1) || (s2 == 1 && s2' == 0)) && (t2 != 0 && t2 != 1 && t2' != 0 && t2' != 1)) ||
  p5L.any fun l => ap5 l 0 != 0 && ap5 l 0 != 1 && ap5 l 1 != 0 && ap5 l 1 != 1 &&
    ap5 l t2 != s2 && ap5 l t2 != s2' && ap5 l t2' != s2 && ap5 l t2' != s2'

theorem g4aChk_ok : g4aChk = true := by decide +kernel

/-- two 2-sets are equal -/
def SEq (s1 s1' s2 s2' : Fin 6) : Prop := (s1 = s2 ∧ s1' = s2') ∨ (s1 = s2' ∧ s1' = s2)
/-- two 2-sets are disjoint -/
def SDisj (s1 s1' s2 s2' : Fin 6) : Prop := s1 ≠ s2 ∧ s1 ≠ s2' ∧ s1' ≠ s2 ∧ s1' ≠ s2'

/-- **the permutation of Lemma 2P(4a)** -/
theorem perm_4a (s1 s1' s2 s2' t1 t1' t2 t2' : Fin 6)
    (h1 : s1 ≠ 5) (h1' : s1' ≠ 5) (h2 : s2 ≠ 5) (h2' : s2' ≠ 5)
    (k1 : t1 ≠ 5) (k1' : t1' ≠ 5) (k2 : t2 ≠ 5) (k2' : t2' ≠ 5)
    (hs1 : s1 ≠ s1') (hs2 : s2 ≠ s2') (ht1 : t1 ≠ t1') (ht2 : t2 ≠ t2')
    (hcond : ¬ (SDisj s1 s1' s2 s2' ∧ SEq t1 t1' t2 t2') ∧ ¬ (SEq s1 s1' s2 s2' ∧ SDisj t1 t1' t2 t2')) :
    ∃ σ : Fin 6 → Fin 6, (∀ x y, σ x = σ y → x = y) ∧ σ 5 = 5 ∧
      σ t1 ≠ s1 ∧ σ t1 ≠ s1' ∧ σ t1' ≠ s1 ∧ σ t1' ≠ s1' ∧
      σ t2 ≠ s2 ∧ σ t2 ≠ s2' ∧ σ t2' ≠ s2 ∧ σ t2' ≠ s2' := by
  obtain ⟨α, α', hαα, hα'α, hα5, hαs1, hαs1'⟩ := norm_perm h1 h1' hs1
  obtain ⟨β, β', hββ, _, hβ5, hβt1, hβt1'⟩ := norm_perm k1 k1' ht1
  have αi := inj_of_linv hαα
  have βi := inj_of_linv hββ
  have ne5α : ∀ x, x ≠ 5 → α x ≠ 5 := fun x hx h => hx (αi _ _ (h.trans hα5.symm))
  have ne5β : ∀ x, x ≠ 5 → β x ≠ 5 := fun x hx h => hx (βi _ _ (h.trans hβ5.symm))
  have h := all5_sound (all5_sound (all5_sound (all5_sound g4aChk_ok (α s2) (ne5α _ h2)) (α s2') (ne5α _ h2'))
    (β t2) (ne5β _ k2)) (β t2') (ne5β _ k2')
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  -- transport of the overlap conditions
  have eqS : ((α s2 = 0 ∧ α s2' = 1) ∨ (α s2 = 1 ∧ α s2' = 0)) → SEq s1 s1' s2 s2' := by
    rintro (⟨a, b⟩ | ⟨a, b⟩)
    · exact Or.inl ⟨αi _ _ (hαs1.trans a.symm), αi _ _ (hαs1'.trans b.symm)⟩
    · exact Or.inr ⟨αi _ _ (hαs1.trans b.symm), αi _ _ (hαs1'.trans a.symm)⟩
  have eqT : ((β t2 = 0 ∧ β t2' = 1) ∨ (β t2 = 1 ∧ β t2' = 0)) → SEq t1 t1' t2 t2' := by
    rintro (⟨a, b⟩ | ⟨a, b⟩)
    · exact Or.inl ⟨βi _ _ (hβt1.trans a.symm), βi _ _ (hβt1'.trans b.symm)⟩
    · exact Or.inr ⟨βi _ _ (hβt1.trans b.symm), βi _ _ (hβt1'.trans a.symm)⟩
  have disS : (¬ α s2 = 0 ∧ ¬ α s2 = 1 ∧ ¬ α s2' = 0 ∧ ¬ α s2' = 1) → SDisj s1 s1' s2 s2' := by
    rintro ⟨a, b, c, d⟩
    refine ⟨fun h => a (h ▸ hαs1), fun h => c (h ▸ hαs1), fun h => b (h ▸ hαs1'), fun h => d (h ▸ hαs1')⟩
  have disT : (¬ β t2 = 0 ∧ ¬ β t2 = 1 ∧ ¬ β t2' = 0 ∧ ¬ β t2' = 1) → SDisj t1 t1' t2 t2' := by
    rintro ⟨a, b, c, d⟩
    refine ⟨fun h => a (h ▸ hβt1), fun h => c (h ▸ hβt1), fun h => b (h ▸ hβt1'), fun h => d (h ▸ hβt1')⟩
  rcases h with ((((h | h) | h) | h) | h)
  · exact absurd (αi _ _ h) hs2
  · exact absurd (βi _ _ h) ht2
  · obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
    exact absurd ⟨disS ⟨a, b, c, d⟩, eqT e⟩ hcond.1
  · obtain ⟨e, ⟨⟨⟨a, b⟩, c⟩, d⟩⟩ := h
    exact absurd ⟨eqS e, disT ⟨a, b, c, d⟩⟩ hcond.2
  obtain ⟨l, hl, hg⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩ := hg
  obtain ⟨l5, linj⟩ := p5_props hl
  have hα's : ∀ x y, α' x = y → x = α y := fun x y h => by rw [← h]; exact (hα'α x).symm
  have α'i : ∀ x y, α' x = α' y → x = y := fun x y h => by rw [← hα'α x, h, hα'α y]
  have hα'5 : α' 5 = 5 := by have := hαα 5; rw [hα5] at this; exact this
  refine ⟨fun x => α' (ap5 l (β x)), fun x y hxy => βi _ _ (linj _ _ (α'i _ _ hxy)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show α' (ap5 l (β 5)) = 5
    rw [hβ5, l5, hα'5]
  all_goals intro hc
  · have := hα's _ _ hc; rw [hβt1, hαs1] at this; exact g1 this
  · have := hα's _ _ hc; rw [hβt1, hαs1'] at this; exact g2 this
  · have := hα's _ _ hc; rw [hβt1', hαs1] at this; exact g3 this
  · have := hα's _ _ hc; rw [hβt1', hαs1'] at this; exact g4 this
  · exact g5 (hα's _ _ hc)
  · exact g6 (hα's _ _ hc)
  · exact g7 (hα's _ _ hc)
  · exact g8 (hα's _ _ hc)

section gm
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the colours of the edges inside `A` at `v` -/
def Cut2.Pset (C : Cut2 P) (φ : Fin X.m → Fin 6) (v : Fin X.n) (κ : Fin 6) : Prop :=
  ∃ f, C.inA f ∧ X.Inc f v ∧ φ f = κ

/-- at the `A`-end `u` of a cut edge there are exactly two edges inside `A` -/
theorem Cut2.pair_at (C : Cut2 P) (hcub : CubicOn P) {e : Fin X.m} {u : Fin X.n} (he : C.isCut e)
    (heu : X.Inc e u) (hu : C.S u = true) :
    ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ X.Inc f u ∧ X.Inc f' u ∧ ∀ g, C.inA g → X.Inc g u → g = f ∨ g = f' := by
  have hPe : P e := C.pole_P (Or.inr he)
  obtain ⟨f, f', hne, hf, hf', i, i'⟩ := C.two_inA hcub he heu hu hPe
  refine ⟨f, f', hne, hf, hf', i, i', fun g hg hgu => ?_⟩
  by_cases h1 : g = f
  · exact Or.inl h1
  by_cases h2 : g = f'
  · exact Or.inr h2
  exfalso
  have hge := uniq3 hcub hf.1 hf'.1 hg.1 hPe i i' hgu heu hne h1 h2
    (fun h => C.not_inA_of_cut (h ▸ he) hf) (fun h => C.not_inA_of_cut (h ▸ he) hf')
  exact C.not_inA_of_cut he (hge ▸ hg)

/-- **M-type gluing of pole colourings** (Lemma 2P(2) and (4a)). -/
theorem Cut2.glue_Mt (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} (hcovA : C.CoverA NA True)
    (hcovB : C.flip.CoverA NB True) (φ ψ : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ)
    (hψ : StarOn C.flip.pole 6 ψ)
    (hφcl : ∀ f, C.pole f → (φ f = 5 ↔ C.isCut f ∨ (C.inA f ∧ NA f)))
    (hψcl : ∀ f, C.flip.pole f → (ψ f = 5 ↔ C.isCut f ∨ (C.flip.inA f ∧ NB f)))
    (hcond : ¬ ((∀ κ, ¬ (C.Pset φ C.a1 κ ∧ C.Pset φ C.a2 κ)) ∧ (∀ κ, C.flip.Pset ψ C.b1 κ ↔ C.flip.Pset ψ C.b2 κ)) ∧
      ¬ ((∀ κ, C.Pset φ C.a1 κ ↔ C.Pset φ C.a2 κ) ∧ (∀ κ, ¬ (C.flip.Pset ψ C.b1 κ ∧ C.flip.Pset ψ C.b2 κ)))) :
    ∃ c, MC5 P (C.glueN NA NB True) c := by
  classical
  have hcub := hG.2.2.2
  -- the two F-edges at each cut end
  have side : ∀ (D : Cut2 P) (N : Fin X.m → Prop) (χ : Fin X.m → Fin 6), D.CoverA N True → StarOn D.pole 6 χ →
      (∀ f, D.pole f → (χ f = 5 ↔ D.isCut f ∨ (D.inA f ∧ N f))) → ∀ (e : Fin X.m) (u : Fin X.n), D.isCut e →
      X.Inc e u → D.S u = true → (u = D.a1 ∨ u = D.a2) →
      ∃ f f', χ f ≠ 5 ∧ χ f' ≠ 5 ∧ χ f ≠ χ f' ∧ (∀ κ, D.Pset χ u κ ↔ κ = χ f ∨ κ = χ f') ∧
        ∀ g, D.inA g → X.Inc g u → χ g = χ f ∨ χ g = χ f' := by
    intro D N χ hcov hχ hcl e u he heu hu hu12
    obtain ⟨f, f', hne, hf, hf', i, i', hcov2⟩ := D.pair_at hcub he heu hu
    have nN : ∀ g, D.inA g → X.Inc g u → ¬ N g := fun g hg hgu hN =>
      (hcov u hu ⟨g, hg.1, hgu⟩).1 ⟨trivial, hu12⟩ g hg hN hgu
    have n5 : ∀ g, D.inA g → X.Inc g u → χ g ≠ 5 := by
      intro g hg hgu h
      rcases (hcl g (Or.inl hg)).1 h with h' | h'
      · exact D.not_inA_of_cut h' hg
      · exact nN g hg hgu h'.2
    refine ⟨f, f', n5 f hf i, n5 f' hf' i', hχ.1 f f' ⟨hne, u, i, i'⟩ (Or.inl hf) (Or.inl hf'), ?_, ?_⟩
    · intro κ
      constructor
      · rintro ⟨g, hg, hgu, rfl⟩
        rcases hcov2 g hg hgu with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨f, hf, i, rfl⟩
        · exact ⟨f', hf', i', rfl⟩
    · intro g hg hgu
      rcases hcov2 g hg hgu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  obtain ⟨f1, f1', s1n, s1n', s1d, hS1, cS1⟩ :=
    side C NA φ hcovA hφ hφcl C.e1 C.a1 (Or.inl rfl) (joins_inc_left C.j1) C.sa1 (Or.inl rfl)
  obtain ⟨f2, f2', s2n, s2n', s2d, hS2, cS2⟩ :=
    side C NA φ hcovA hφ hφcl C.e2 C.a2 (Or.inr rfl) (joins_inc_left C.j2) C.sa2 (Or.inr rfl)
  obtain ⟨g1, g1', t1n, t1n', t1d, hT1, cT1⟩ :=
    side C.flip NB ψ hcovB hψ hψcl C.e1 C.b1 (Or.inl rfl) (joins_inc_right C.j1) C.flip.sa1 (Or.inl rfl)
  obtain ⟨g2, g2', t2n, t2n', t2d, hT2, cT2⟩ :=
    side C.flip NB ψ hcovB hψ hψcl C.e2 C.b2 (Or.inr rfl) (joins_inc_right C.j2) C.flip.sa2 (Or.inr rfl)
  -- the overlap condition in pair form
  have disj_of : ∀ {D : Cut2 P} {χ : Fin X.m → Fin 6} {u v : Fin X.n} {x x' y y' : Fin 6},
      (∀ κ, D.Pset χ u κ ↔ κ = x ∨ κ = x') → (∀ κ, D.Pset χ v κ ↔ κ = y ∨ κ = y') → SDisj x x' y y' →
      ∀ κ, ¬ (D.Pset χ u κ ∧ D.Pset χ v κ) := by
    intro D χ u v x x' y y' hu hv hd κ ⟨h1, h2⟩
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
    perm_4a (φ f1) (φ f1') (φ f2) (φ f2') (ψ g1) (ψ g1') (ψ g2) (ψ g2') s1n s1n' s2n s2n' t1n t1n' t2n t2n'
      s1d s2d t1d t2d
      ⟨fun h => hcond.1 ⟨disj_of hS1 hS2 h.1, eq_of hT1 hT2 h.2⟩,
       fun h => hcond.2 ⟨eq_of hS1 hS2 h.1, disj_of hT1 hT2 h.2⟩⟩
  -- the glued colouring
  let M := C.glueN NA NB True
  have hM : PMOn P M := C.pm_glue hcovA hcovB
  let c : Fin X.m → Fin 6 := fun f => if C.flip.inA f then σ (ψ f) else φ f
  have hcA' : ∀ f, ¬ C.flip.inA f → c f = φ f := fun f hf => by simp only [c, if_neg hf]
  have hcB' : ∀ f, C.flip.inA f → c f = σ (ψ f) := fun f hf => by simp only [c, if_pos hf]
  have hcφ : ∀ f, C.pole f → c f = φ f := by
    intro f hf
    apply hcA'
    rcases hf with h | h
    · exact C.not_flip_of_inA h
    · exact C.flip.not_inA_of_cut h
  have hcψ : ∀ f, C.flip.pole f → c f = σ (ψ f) := by
    intro f hf
    rcases hf with h | h
    · exact hcB' f h
    · rw [hcA' f (C.flip.not_inA_of_cut h), (hφcl f (Or.inr h)).2 (Or.inl h), (hψcl f (Or.inr h)).2 (Or.inl h), σ5]
  have hσ5' : ∀ y, σ y = 5 ↔ y = 5 := fun y => ⟨fun h => σi _ _ (h.trans σ5.symm), fun h => h ▸ σ5⟩
  have hcl : ∀ f, P f → (M f ↔ c f = 5) := by
    intro f hf
    show C.glueN NA NB True f ↔ c f = 5
    rcases C.cases_P hf with h | h | h
    · rw [C.glueN_A h, hcA' f (C.not_flip_of_inA h), hφcl f (Or.inl h)]
      exact ⟨fun hn => Or.inr ⟨h, hn⟩, fun h' => h'.elim (fun h'' => absurd h (C.not_inA_of_cut h'')) (fun h'' => h''.2)⟩
    · rw [C.glueN_B h, hcB' f h, hσ5', hψcl f (Or.inl h)]
      exact ⟨fun hn => Or.inr ⟨h, hn⟩,
        fun h' => h'.elim (fun h'' => absurd h (C.flip.not_inA_of_cut h'')) (fun h'' => h''.2)⟩
    · rw [C.glueN_cut h, hcA' f (C.flip.not_inA_of_cut h), hφcl f (Or.inr h)]
      exact ⟨fun _ => Or.inl h, fun _ => trivial⟩
  have hMcut : ∀ e, C.isCut e → M e := fun e he => (C.glueN_cut he).2 trivial
  -- F-edges at the cut ends
  have atA : ∀ e u f, C.isCut e → X.Inc e u → C.S u = true → P f → ¬ M f → X.Inc f u → C.inA f := by
    intro e u f he heu hu hf nf hfu
    have hfe : f ≠ e := fun h => nf (h ▸ hMcut e he)
    exact C.F_at_A he heu hu hf hfu hfe
  have atB : ∀ e u f, C.isCut e → X.Inc e u → C.S u = false → P f → ¬ M f → X.Inc f u → C.flip.inA f := by
    intro e u f he heu hu hf nf hfu
    have hfe : f ≠ e := fun h => nf (h ▸ hMcut e he)
    exact C.flip.F_at_A he heu (Cut2.flip_true hu) hf hfu hfe
  have cross : ∀ f f', ((P f ∧ ¬ M f ∧ X.Inc f C.a1 ∧ P f' ∧ ¬ M f' ∧ X.Inc f' C.b1) ∨
      (P f ∧ ¬ M f ∧ X.Inc f C.a2 ∧ P f' ∧ ¬ M f' ∧ X.Inc f' C.b2)) → c f ≠ c f' := by
    rintro f f' (⟨hf, nf, hfu, hf', nf', hf'u⟩ | ⟨hf, nf, hfu, hf', nf', hf'u⟩)
    · have hfA := atA C.e1 C.a1 f (Or.inl rfl) (joins_inc_left C.j1) C.sa1 hf nf hfu
      have hf'B := atB C.e1 C.b1 f' (Or.inl rfl) (joins_inc_right C.j1) C.sb1 hf' nf' hf'u
      rw [hcA' f (C.not_flip_of_inA hfA), hcB' f' hf'B]
      rcases cS1 f hfA hfu with h | h <;> rcases cT1 f' hf'B hf'u with h' | h' <;> rw [h, h'] <;>
        first | exact Ne.symm x1 | exact Ne.symm x2 | exact Ne.symm x3 | exact Ne.symm x4
    · have hfA := atA C.e2 C.a2 f (Or.inr rfl) (joins_inc_left C.j2) C.sa2 hf nf hfu
      have hf'B := atB C.e2 C.b2 f' (Or.inr rfl) (joins_inc_right C.j2) C.sb2 hf' nf' hf'u
      rw [hcA' f (C.not_flip_of_inA hfA), hcB' f' hf'B]
      rcases cS2 f hfA hfu with h | h <;> rcases cT2 f' hf'B hf'u with h' | h' <;> rw [h, h'] <;>
        first | exact Ne.symm x5 | exact Ne.symm x6 | exact Ne.symm x7 | exact Ne.symm x8
  have hdisj : ∀ e f f' u u', C.isCut e → X.Joins e u u' → P f → ¬ M f → X.Inc f u → P f' → ¬ M f' →
      X.Inc f' u' → c f ≠ c f' := by
    intro e f f' u u' he hj hf nf hfu hf' nf' hf'u'
    rcases C.cut_sides he hj with ⟨hu, _⟩ | ⟨_, hu'⟩
    · rcases C.cutA he (joins_inc_left hj) hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : u' = C.b1 := by
          rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h C.a1_ne_b1
        subst this
        exact cross f f' (Or.inl ⟨hf, nf, hfu, hf', nf', hf'u'⟩)
      · have : u' = C.b2 := by
          rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h C.a2_ne_b2
        subst this
        exact cross f f' (Or.inr ⟨hf, nf, hfu, hf', nf', hf'u'⟩)
    · rcases C.cutA he (joins_inc_right hj) hu' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : u = C.b1 := by
          rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h C.a1_ne_b1
          · exact h
        subst this
        exact Ne.symm (cross f' f (Or.inl ⟨hf', nf', hf'u', hf, nf, hfu⟩))
      · have : u = C.b2 := by
          rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h C.a2_ne_b2
          · exact h
        subst this
        exact Ne.symm (cross f' f (Or.inr ⟨hf', nf', hf'u', hf, nf, hfu⟩))
  exact ⟨c, glue_M hM C (hMcut _ (Or.inl rfl)) (hMcut _ (Or.inr rfl)) φ (fun f => σ (ψ f)) c hφ
    (starOn_map σ σi hψ) hcφ hcψ hdisj, hcl⟩

end gm

end RH2F

-- ===== from RH2CL3.lean =====
/-
  RH2CL3.lean — Lemma CL (fact ecc9734f558cf885), classes of the pole colourings, part (CL3), and the overlap
  statements used by Lemma SR (fact 5a68c9cb62d7148d).
-/

namespace RH2F
open MGraph

theorem meet_chk : all234 (fun a => all234 fun b => all234 fun c => all234 fun d =>
    a == b || c == d || a == c || a == d || b == c || b == d) = true := by decide +kernel

/-- two 2-subsets of the 3 colours outside `{x, y, 5}` intersect -/
theorem meet3 {x y a b c d : Fin 6} (hxy : x ≠ y) (hx : x ≠ 5) (hy : y ≠ 5) (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ≠ x ∧ a ≠ y ∧ a ≠ 5) (hb : b ≠ x ∧ b ≠ y ∧ b ≠ 5) (hc : c ≠ x ∧ c ≠ y ∧ c ≠ 5)
    (hd : d ≠ x ∧ d ≠ y ∧ d ≠ 5) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  obtain ⟨α, _, hαα, _, hα5, hαx, hαy⟩ := norm_perm hx hy hxy
  have αi := inj_of_linv hαα
  have nr : ∀ z, z ≠ x ∧ z ≠ y ∧ z ≠ 5 → α z ≠ 0 ∧ α z ≠ 1 ∧ α z ≠ 5 := fun z hz =>
    ⟨fun h => hz.1 (αi _ _ (h.trans hαx.symm)), fun h => hz.2.1 (αi _ _ (h.trans hαy.symm)),
     fun h => hz.2.2 (αi _ _ (h.trans hα5.symm))⟩
  obtain ⟨a0, a1, a5⟩ := nr a ha
  obtain ⟨b0, b1, b5⟩ := nr b hb
  obtain ⟨c0, c1, c5⟩ := nr c hc
  obtain ⟨d0, d1, d5⟩ := nr d hd
  have h := all234_sound (all234_sound (all234_sound (all234_sound meet_chk _ a0 a1 a5) _ b0 b1 b5) _ c0 c1 c5)
    _ d0 d1 d5
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with h | h | h | h | h | h
  · exact absurd (αi _ _ h) hab
  · exact absurd (αi _ _ h) hcd
  · exact Or.inl (αi _ _ h)
  · exact Or.inr (Or.inl (αi _ _ h))
  · exact Or.inr (Or.inr (Or.inl (αi _ _ h)))
  · exact Or.inr (Or.inr (Or.inr (αi _ _ h)))

section cl3
variable {X : MGraph} {P : Fin X.m → Prop}

/-- equal 2-sets given by membership are equal as pairs -/
theorem seq_of_sets {x x' y y' : Fin 6} (hx : x ≠ x') (h : ∀ κ, (κ = x ∨ κ = x') ↔ (κ = y ∨ κ = y')) :
    SEq x x' y y' := by
  rcases (h x).1 (Or.inl rfl) with h1 | h1
  · rcases (h x').1 (Or.inr rfl) with h2 | h2
    · exact absurd (h1.trans h2.symm) hx
    · exact Or.inl ⟨h1, h2⟩
  · rcases (h x').1 (Or.inr rfl) with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hx

/-- the colour sets at the two ends of the pole, as pairs -/
theorem Cut2.Pset_pair (C : Cut2 P) (hcub : CubicOn P) (χ : Fin X.m → Fin 6) {e : Fin X.m} {u : Fin X.n}
    (he : C.isCut e) (heu : X.Inc e u) (hu : C.S u = true) :
    ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ X.Inc f u ∧ X.Inc f' u ∧ (∀ κ, C.Pset χ u κ ↔ κ = χ f ∨ κ = χ f') := by
  obtain ⟨f, f', hne, hf, hf', i, i', hcov⟩ := C.pair_at hcub he heu hu
  refine ⟨f, f', hne, hf, hf', i, i', fun κ => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg, hgu, rfl⟩
    rcases hcov g hg hgu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨f, hf, i, rfl⟩
    · exact ⟨f', hf', i', rfl⟩

/-- **(CL1)**: the class of the pole colouring when `g_A ∈ N` -/
theorem Cut2.cl1_class (C : Cut2 P) {N : Fin (addEdge X C.a1 C.a2).m → Prop} {c : Fin (addEdge X C.a1 C.a2).m → Fin 6}
    (hc : MC5 C.clo N c) (hl : N (Fin.last X.m)) :
    ∀ f, C.pole f → (c (C.toClo f) = 5 ↔ C.isCut f ∨ (C.inA f ∧ N (Fin.castSucc f))) := by
  intro f hf
  by_cases hcut : C.isCut f
  · rw [C.toClo_cut hcut]
    exact ⟨fun _ => Or.inl hcut, fun _ => (hc.2 _ C.clo_last).1 hl⟩
  · have hA : C.inA f := hf.resolve_right hcut
    rw [C.toClo_old hcut, ← hc.2 _ (C.clo_old hA)]
    exact ⟨fun h => Or.inr ⟨hA, h⟩, fun h => h.elim (fun h' => absurd h' hcut) (fun h' => h'.2)⟩

/-- **(CL2)**: the class of the pole colouring when `g_A ∉ N` -/
theorem Cut2.cl2_class (C : Cut2 P) {N : Fin (addEdge X C.a1 C.a2).m → Prop} {c : Fin (addEdge X C.a1 C.a2).m → Fin 6}
    (hc : MC5 C.clo N c) : ∀ f, C.inA f → (c (C.toClo f) = 5 ↔ N (Fin.castSucc f)) := by
  intro f hf
  rw [C.toClo_old (fun h => C.not_inA_of_cut h hf)]
  exact (hc.2 _ (C.clo_old hf)).symm

/-- **(CL1)**, overlap: if at most one edge joins `a1, a2` then the two colour sets are not equal (`t ≤ 1`) -/
theorem Cut2.cl1_small (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    {N : Fin (addEdge X C.a1 C.a2).m → Prop} (hN : PMOn C.clo N) {c : Fin (addEdge X C.a1 C.a2).m → Fin 6}
    (hc : MC5 C.clo N c) (hl : N (Fin.last X.m)) :
    ¬ (∀ κ, C.Pset (fun f => c (C.toClo f)) C.a1 κ ↔ C.Pset (fun f => c (C.toClo f)) C.a2 κ) := by
  intro heq
  have rb := rb_of_star (C.clo_loopless hG.1) hN hc.2 hc.1
  obtain ⟨f1, f1', d1, i1, i1', a1, a1', h1⟩ := C.Pset_pair hG.2.2.2 (fun f => c (C.toClo f)) (Or.inl rfl)
    (joins_inc_left C.j1) C.sa1
  obtain ⟨f2, f2', d2, i2, i2', a2, a2', h2⟩ := C.Pset_pair hG.2.2.2 (fun f => c (C.toClo f)) (Or.inr rfl)
    (joins_inc_left C.j2) C.sa2
  have tc : ∀ g, C.inA g → C.toClo g = Fin.castSucc g := fun g hg => C.toClo_old (fun h => C.not_inA_of_cut h hg)
  -- the edges inside `A` at `a_i` are not in `N` (the matching edge there is `g_A`)
  have nN : ∀ g u, C.inA g → X.Inc g u → (u = C.a1 ∨ u = C.a2) → ¬ N (Fin.castSucc g) := by
    intro g u hg hgu hu hn
    exact castSucc_ne_last g (pm_unique hN hn hl (addEdge_inc_old.2 hgu) ((C.inc_new_iff).2 hu))
  have same : ∀ g g', C.inA g → C.inA g' → X.Inc g C.a1 → X.Inc g' C.a2 →
      c (Fin.castSucc g) = c (Fin.castSucc g') → g = g' := by
    intro g g' hg hg' ga ga' heq'
    apply Classical.byContradiction
    intro hne
    exact rb (Fin.last X.m) C.a1 C.a2 _ _ hl addEdge_joins_new (C.clo_old hg) (nN g C.a1 hg ga (Or.inl rfl))
      (addEdge_inc_old.2 ga) (C.clo_old hg') (nN g' C.a2 hg' ga' (Or.inr rfl)) (addEdge_inc_old.2 ga')
      (fun h => hne (castSucc_inj' h)) heq'
  have hS : SEq (c (C.toClo f1)) (c (C.toClo f1')) (c (C.toClo f2)) (c (C.toClo f2')) := by
    apply seq_of_sets
    · intro h
      rw [tc f1 i1, tc f1' i1'] at h
      exact (hc.1.1 _ _ ⟨fun h' => d1 (castSucc_inj' h'), C.a1, addEdge_inc_old.2 a1, addEdge_inc_old.2 a1'⟩
        (C.clo_old i1) (C.clo_old i1')) h
    · intro κ; rw [← h1 κ, ← h2 κ]; exact heq κ
  rw [tc f1 i1, tc f1' i1', tc f2 i2, tc f2' i2'] at hS
  rcases hS with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have := same _ _ i1 i2 a1 a2 e1
    have := same _ _ i1' i2' a1' a2' e2
    subst_vars
    exact d1 (hpa _ _ i1.1 i1'.1 (joins_of_inc2 a1 a2 C.ha) (joins_of_inc2 a1' a2' C.ha))
  · have := same _ _ i1 i2' a1 a2' e1
    have := same _ _ i1' i2 a1' a2 e2
    subst_vars
    exact d1 (hpa _ _ i1.1 i1'.1 (joins_of_inc2 a1 a2' C.ha) (joins_of_inc2 a1' a2 C.ha))

/-- the edges of the digon closure at `b_i` are `oD e_i`, `δ`, `δ′` -/
theorem Cut2.cloD_at_b (C : Cut2 P) {j : Fin C.XD.m} (hj : C.cloD j) {b : Fin X.n} (hb : b = C.b1 ∨ b = C.b2)
    (hjb : C.XD.Inc j b) : j = C.dl1 ∨ j = C.dl2 ∨ (j = C.oD C.e1 ∧ b = C.b1) ∨ (j = C.oD C.e2 ∧ b = C.b2) := by
  have hbS : C.S b = false := by rcases hb with rfl | rfl; exact C.sb1; exact C.sb2
  rcases hj with rfl | rfl | ⟨d, rfl, hd⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · have hdb := (C.XD_inc_old).1 hjb
    rcases hd with hd | hd
    · have := C.side_of_inA hd hdb; rw [hbS] at this; exact absurd this (by decide)
    · rcases hd with rfl | rfl
      · rcases C.inc_e1 hdb with h | h
        · rw [h, C.sa1] at hbS; exact absurd hbS (by decide)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
      · rcases C.inc_e2 hdb with h | h
        · rw [h, C.sa2] at hbS; exact absurd hbS (by decide)
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/-- the walk of (CL3): a digon edge and an F-edge at `a` next to the matching cut edge `e = a b` are not equally
    coloured -/
theorem Cut2.cl3_walk (C : Cut2 P) (hloop : Loopless X) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N)
    {c : Fin C.XD.m → Fin 6} (hc : MC5 C.cloD N c) {e : Fin X.m} {a b b' : Fin X.n} (he : C.isCut e)
    (hjab : X.Joins e a b) (ha : C.S a = true) (hbb : b ≠ b') (hb' : b' = C.b1 ∨ b' = C.b2)
    (hb : b = C.b1 ∨ b = C.b2) (hNe : N (C.oD e)) {δ : Fin C.XD.m} (hδ : δ = C.dl1 ∨ δ = C.dl2)
    (hδj : C.XD.Joins δ b' b) {f : Fin X.m} (hf : C.inA f) (hfa : X.Inc f a) : c δ ≠ c (C.oD f) := by
  intro heq
  have notB : ∀ v, C.S v = true → v ≠ C.b1 ∧ v ≠ C.b2 := fun v hv =>
    ⟨fun h => by rw [h, C.sb1] at hv; exact absurd hv (by decide),
     fun h => by rw [h, C.sb2] at hv; exact absurd hv (by decide)⟩
  have bB : ∀ v, (v = C.b1 ∨ v = C.b2) → C.S v = false := fun v hv => by
    rcases hv with rfl | rfl; exact C.sb1; exact C.sb2
  obtain ⟨y, hy⟩ := joins_of_inc hfa
  have hyA : C.S y = true := C.side_of_inA hf (joins_inc_right hy)
  obtain ⟨d, hdN, hdp, hdy, _⟩ := C.cloD_N_at_A hN hyA ⟨f, Or.inl hf, joins_inc_right hy⟩
  obtain ⟨z, hz⟩ := joins_of_inc hdy
  have hay : a ≠ y := ne_of_joins hloop hy
  -- `z` lies in `A` or is the `B`-end of the other cut edge
  have hzb : z ≠ b := by
    intro hzb
    subst hzb
    rcases hdp with hdA | hdc
    · have := C.side_of_inA hdA (joins_inc_right hz); rw [bB z hb] at this; exact absurd this (by decide)
    · -- `d` is a cut edge joining `y ∈ A` and `z = b`, so `d = e` and `y = a`
      have hde : d = e := by
        apply Classical.byContradiction; intro hne
        exact C.cut_disj hdc he hne (joins_inc_right hz) (joins_inc_right hjab)
      subst hde
      rcases joins_unique hz hjab with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hay h1.symm
      · rw [h1, bB z hb] at hyA; exact absurd hyA (by decide)
  have haz : a ≠ z := by
    intro haz
    have := pm_unique hN hdN hNe ((C.XD_inc_old).2 (haz ▸ joins_inc_right hz)) ((C.XD_inc_old).2 (joins_inc_left hjab))
    have hde := C.oD_inj this
    subst hde
    rcases inc_of_joins hjab (joins_inc_left hz) with h | h
    · exact hay h.symm
    · rw [h, bB b hb] at hyA; exact absurd hyA (by decide)
  have hδN : c δ = c (C.oD f) := heq
  have hcδ : C.cloD δ := by rcases hδ with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
  let W : C.XD.Walk4 :=
    { v0 := b', v1 := b, v2 := a, v3 := y, v4 := z
      e1 := δ, e2 := C.oD e, e3 := C.oD f, e4 := C.oD d
      h1 := hδj, h2 := (C.XD_joins_old).2 (Or.symm hjab), h3 := (C.XD_joins_old).2 hy, h4 := (C.XD_joins_old).2 hz
      d01 := Ne.symm hbb
      d02 := fun h => by rw [← h, bB b' hb'] at ha; exact absurd ha (by decide)
      d03 := fun h => by rw [← h, bB b' hb'] at hyA; exact absurd hyA (by decide)
      d12 := fun h => by rw [← h, bB b hb] at ha; exact absurd ha (by decide)
      d13 := fun h => by rw [← h, bB b hb] at hyA; exact absurd hyA (by decide)
      d14 := Ne.symm hzb, d23 := hay, d24 := haz, d34 := ne_of_joins hloop hz }
  apply hc.1.2 W hcδ ((C.cloD_old_iff).2 (Or.inr he)) ((C.cloD_old_iff).2 (Or.inl hf)) ((C.cloD_old_iff).2 hdp)
  exact ⟨hδN, ((hc.2 _ ((C.cloD_old_iff).2 (Or.inr he))).1 hNe).trans ((hc.2 _ (hN.1 _ hdN)).1 hdN).symm⟩

/-- **(CL3)** (fact ecc9734f558cf885): if `e1 ∈ N` for a perfect matching of the digon closure, then `e2 ∈ N` and the
    F-colour sets of the pole at `a1` and `a2` intersect (`t ≥ 1`). -/
theorem Cut2.cl3 (C : Cut2 P) (hG : InG X P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N)
    (h1 : N (C.oD C.e1)) {c : Fin C.XD.m → Fin 6} (hc : MC5 C.cloD N c) :
    N (C.oD C.e2) ∧ ∃ κ, C.Pset (fun f => c (C.oD f)) C.a1 κ ∧ C.Pset (fun f => c (C.oD f)) C.a2 κ := by
  have hloop := hG.1
  have ib1 : C.XD.Inc (C.oD C.e1) C.b1 := (C.XD_inc_old).2 (joins_inc_right C.j1)
  have nd1 : ¬ N C.dl1 := fun h => C.oD_ne_dl1 _ (pm_unique hN h1 h ib1 ((C.XD_inc_dl1).2 (Or.inl rfl))).symm.symm
  have nd2 : ¬ N C.dl2 := fun h => C.oD_ne_dl2 _ (pm_unique hN h1 h ib1 ((C.XD_inc_dl2).2 (Or.inl rfl)))
  have h2 : N (C.oD C.e2) := by
    obtain ⟨j, hjN, hjb, _⟩ := hN.2 C.b2 ⟨C.oD C.e2, (C.cloD_old_iff).2 (Or.inr (Or.inr rfl)),
      (C.XD_inc_old).2 (joins_inc_right C.j2)⟩
    rcases C.cloD_at_b (hN.1 _ hjN) (Or.inr rfl) hjb with rfl | rfl | ⟨_, h⟩ | ⟨rfl, _⟩
    · exact absurd hjN nd1
    · exact absurd hjN nd2
    · exact absurd h.symm C.hb
    · exact hjN
  refine ⟨h2, ?_⟩
  -- the digon colours
  have x5 : c C.dl1 ≠ 5 := fun h => nd1 ((hc.2 _ (Or.inl rfl)).2 h)
  have y5 : c C.dl2 ≠ 5 := fun h => nd2 ((hc.2 _ (Or.inr (Or.inl rfl))).2 h)
  have xy : c C.dl1 ≠ c C.dl2 := hc.1.1 _ _ ⟨C.dl1_ne_dl2, C.b1, (C.XD_inc_dl1).2 (Or.inl rfl),
    (C.XD_inc_dl2).2 (Or.inl rfl)⟩ (Or.inl rfl) (Or.inr (Or.inl rfl))
  obtain ⟨f1, f1', d1, i1, i1', a1, a1', hP1⟩ := C.Pset_pair hG.2.2.2 (fun f => c (C.oD f)) (Or.inl rfl)
    (joins_inc_left C.j1) C.sa1
  obtain ⟨f2, f2', d2, i2, i2', a2, a2', hP2⟩ := C.Pset_pair hG.2.2.2 (fun f => c (C.oD f)) (Or.inr rfl)
    (joins_inc_left C.j2) C.sa2
  -- an F-edge at `a_i` avoids the digon colours and 5
  have avoid : ∀ (e : Fin X.m) (a b b' : Fin X.n), C.isCut e → X.Joins e a b → C.S a = true → b ≠ b' →
      (b' = C.b1 ∨ b' = C.b2) → (b = C.b1 ∨ b = C.b2) → N (C.oD e) → C.XD.Joins C.dl1 b' b →
      C.XD.Joins C.dl2 b' b → ∀ f, C.inA f → X.Inc f a →
      c (C.oD f) ≠ c C.dl1 ∧ c (C.oD f) ≠ c C.dl2 ∧ c (C.oD f) ≠ 5 := by
    intro e a b b' he hj ha hbb hb' hb hNe j1 j2 f hf hfa
    refine ⟨fun h => C.cl3_walk hloop hN hc he hj ha hbb hb' hb hNe (Or.inl rfl) j1 hf hfa h.symm,
      fun h => C.cl3_walk hloop hN hc he hj ha hbb hb' hb hNe (Or.inr rfl) j2 hf hfa h.symm, fun h => ?_⟩
    have hNf : N (C.oD f) := (hc.2 _ ((C.cloD_old_iff).2 (Or.inl hf))).2 h
    have := C.oD_inj (pm_unique hN hNf hNe ((C.XD_inc_old).2 hfa) ((C.XD_inc_old).2 (joins_inc_left hj)))
    exact C.not_inA_of_cut (this ▸ he) hf
  have j1r : C.XD.Joins C.dl1 C.b2 C.b1 := Or.symm C.XD_joins_dl1
  have j2r : C.XD.Joins C.dl2 C.b2 C.b1 := Or.symm C.XD_joins_dl2
  have A1 := avoid C.e1 C.a1 C.b1 C.b2 (Or.inl rfl) C.j1 C.sa1 C.hb (Or.inr rfl) (Or.inl rfl) h1 j1r j2r
  have A2 := avoid C.e2 C.a2 C.b2 C.b1 (Or.inr rfl) C.j2 C.sa2 (Ne.symm C.hb) (Or.inl rfl) (Or.inr rfl) h2
    C.XD_joins_dl1 C.XD_joins_dl2
  have pr : ∀ g g' u, C.inA g → C.inA g' → X.Inc g u → X.Inc g' u → g ≠ g' → c (C.oD g) ≠ c (C.oD g') :=
    fun g g' u hg hg' hgu hg'u hne => hc.1.1 _ _ ⟨fun h => hne (C.oD_inj h), u, (C.XD_inc_old).2 hgu,
      (C.XD_inc_old).2 hg'u⟩ ((C.cloD_old_iff).2 (Or.inl hg)) ((C.cloD_old_iff).2 (Or.inl hg'))
  rcases meet3 xy x5 y5 (pr _ _ _ i1 i1' a1 a1' d1) (pr _ _ _ i2 i2' a2 a2' d2)
    (A1 f1 i1 a1) (A1 f1' i1' a1') (A2 f2 i2 a2) (A2 f2' i2' a2') with h | h | h | h
  · exact ⟨_, (hP1 _).2 (Or.inl rfl), (hP2 _).2 (Or.inl h)⟩
  · exact ⟨_, (hP1 _).2 (Or.inl rfl), (hP2 _).2 (Or.inr h)⟩
  · exact ⟨_, (hP1 _).2 (Or.inr rfl), (hP2 _).2 (Or.inl h)⟩
  · exact ⟨_, (hP1 _).2 (Or.inr rfl), (hP2 _).2 (Or.inr h)⟩

end cl3

end RH2F

-- ===== from RH2SR.lean =====
/-
  RH2SR.lean — Lemma SR (fact 5a68c9cb62d7148d) in Lean 4.20 core: EX1 across a 2-edge-cut from a certified side
  and one closure of the other side.  Certificates of side `A` are star colourings of the pole `A⁺`
  (`C.pole = E(G[A]) ∪ {e1, e2}`) of the types M_t, Feq, Fnc, Fneq of the prose.
-/

namespace RH2F
open MGraph

section sr
variable {X : MGraph} {P : Fin X.m → Prop}

/-! ### certificates -/

/-- an M-type certificate: the class `5` is `{e1, e2} ∪ N` with `N ⊆ E(G[A])` covering `A ∖ {a1, a2}` exactly once -/
def Cut2.CertM (C : Cut2 P) (N : Fin X.m → Prop) (φ : Fin X.m → Fin 6) : Prop :=
  C.CoverA N True ∧ StarOn C.pole 6 φ ∧ ∀ f, C.pole f → (φ f = 5 ↔ C.isCut f ∨ (C.inA f ∧ N f))

/-- `t ≤ 1`: the F-colour sets at `a1`, `a2` differ -/
def Cut2.TSmall (C : Cut2 P) (φ : Fin X.m → Fin 6) : Prop := ¬ ∀ κ, C.Pset φ C.a1 κ ↔ C.Pset φ C.a2 κ

/-- `t ≥ 1`: the F-colour sets at `a1`, `a2` meet -/
def Cut2.TMeet (C : Cut2 P) (φ : Fin X.m → Fin 6) : Prop := ∃ κ, C.Pset φ C.a1 κ ∧ C.Pset φ C.a2 κ

/-- an F-type certificate: the class `5` is `N ⊆ E(G[A])` covering `A` exactly once -/
def Cut2.CertF (C : Cut2 P) (N : Fin X.m → Prop) (φ : Fin X.m → Fin 6) : Prop :=
  C.CoverA N False ∧ StarOn C.pole 6 φ ∧ (∀ f, C.inA f → (φ f = 5 ↔ N f)) ∧ φ C.e1 ≠ 5 ∧ φ C.e2 ≠ 5

/-- type Feq -/
def Cut2.Feq (C : Cut2 P) (N : Fin X.m → Prop) (φ : Fin X.m → Fin 6) : Prop :=
  C.CertF N φ ∧ φ C.e1 = φ C.e2 ∧ ∀ r, C.inA r → N r → ¬ X.Joins r C.a1 C.a2

/-- type Fneq -/
def Cut2.Fneq (C : Cut2 P) (N : Fin X.m → Prop) (φ : Fin X.m → Fin 6) : Prop :=
  C.CertF N φ ∧ φ C.e1 ≠ φ C.e2

/-- type Fnc -/
def Cut2.Fnc (C : Cut2 P) (N : Fin X.m → Prop) (φ : Fin X.m → Fin 6) : Prop :=
  C.Fneq N φ ∧ (∀ f, C.inA f → ¬ N f → X.Inc f C.a1 → φ f ≠ φ C.e2) ∧
    (∀ f, C.inA f → ¬ N f → X.Inc f C.a2 → φ f ≠ φ C.e1)

/-- recipe D -/
def Cut2.RecipeD (C : Cut2 P) : Prop :=
  (∃ N φ, C.CertM N φ ∧ C.TMeet φ) ∧ (∃ N φ, C.Fnc N φ) ∧
  ∀ h, C.inA h → ∀ s : Bool, ∃ N φ, ((C.CertM N φ ∧ C.TMeet φ) ∨ C.Fnc N φ) ∧ (N h ↔ s = true)

/-- recipe E -/
def Cut2.RecipeE (C : Cut2 P) : Prop :=
  (∃ N φ, C.CertM N φ ∧ C.TSmall φ) ∧ (∃ N φ, C.Feq N φ) ∧ (∃ N φ, C.Fneq N φ) ∧
  ∀ h, C.inA h → ∀ s : Bool, ∃ N φ, ((C.CertM N φ ∧ C.TSmall φ) ∨ C.Feq N φ) ∧ (N h ↔ s = true)

/-! ### the four gluing steps with side `B` given by a closure colouring -/

/-- the result shape: a perfect matching of `P` with a star colouring, prescribed on side `B` -/
def Cut2.GlueOK (C : Cut2 P) (NA NB : Fin X.m → Prop) (s : Prop) : Prop :=
  ∃ c, MC5 P (C.glueN NA NB s) c

/-- (G1) with `t_φ, t_ψ ≤ 1` -/
theorem Cut2.g1_small (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} {φ ψ : Fin X.m → Fin 6}
    (hA : C.CertM NA φ) (hAt : C.TSmall φ) (hB : C.flip.CertM NB ψ) (hBt : C.flip.TSmall ψ) :
    C.GlueOK NA NB True :=
  C.glue_Mt hG hA.1 hB.1 φ ψ hA.2.1 hB.2.1 hA.2.2 hB.2.2
    ⟨fun h => hBt h.2, fun h => hAt h.1⟩

/-- (G1) with `t_φ, t_ψ ≥ 1` -/
theorem Cut2.g1_meet (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} {φ ψ : Fin X.m → Fin 6}
    (hA : C.CertM NA φ) (hAt : C.TMeet φ) (hB : C.flip.CertM NB ψ) (hBt : C.flip.TMeet ψ) :
    C.GlueOK NA NB True := by
  refine C.glue_Mt hG hA.1 hB.1 φ ψ hA.2.1 hB.2.1 hA.2.2 hB.2.2 ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨κ, h1, h2⟩ := hAt; exact h.1 κ ⟨h1, h2⟩
  · obtain ⟨κ, h1, h2⟩ := hBt; exact h.2 κ ⟨h1, h2⟩

/-- (G2) -/
theorem Cut2.g_eq (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} {φ ψ : Fin X.m → Fin 6}
    (hA : C.Feq NA φ) (hB : C.flip.Feq NB ψ) : C.GlueOK NA NB False :=
  C.glue_eq hG hA.1.1 hB.1.1 φ ψ hA.1.2.1 hB.1.2.1 hA.1.2.2.1 hA.1.2.2.2.1 hA.2.1 hB.1.2.2.1 hB.1.2.2.2.1 hB.2.1
    hA.2.2 hB.2.2

/-- (G3): side `B` without cross ends -/
theorem Cut2.g_nc (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} {φ ψ : Fin X.m → Fin 6}
    (hA : C.Fneq NA φ) (hB : C.flip.Fnc NB ψ) : C.GlueOK NA NB False :=
  C.glue_nc hG hA.1.1 hB.1.1.1 φ ψ hA.1.2.1 hB.1.1.2.1 hA.1.2.2.1 hA.1.2.2.2.1 hA.1.2.2.2.2 hA.2 hB.1.1.2.2.1
    hB.1.1.2.2.2.1 hB.1.1.2.2.2.2 hB.1.2 hB.2.1 hB.2.2

theorem Cut2.flip_flip_inA_eq (C : Cut2 P) : C.flip.flip.inA = C.inA := by
  funext f; exact propext C.flip_flip_inA_iff

theorem Cut2.flip_flip_S_eq (C : Cut2 P) : C.flip.flip.S = C.S := by
  funext v; exact C.flip_flip_S v

theorem Cut2.flip_flip_pole_eq (C : Cut2 P) : C.flip.flip.pole = C.pole := by
  funext f; exact propext C.flip_flip_pole

theorem Cut2.flip_flip_CoverA (C : Cut2 P) {N : Fin X.m → Prop} {s : Prop} :
    C.flip.flip.CoverA N s ↔ C.CoverA N s := by
  unfold Cut2.CoverA
  rw [C.flip_flip_inA_eq, C.flip_flip_S_eq]
  exact Iff.rfl

theorem Cut2.flip_flip_CertF (C : Cut2 P) {N : Fin X.m → Prop} {φ : Fin X.m → Fin 6} :
    C.flip.flip.CertF N φ ↔ C.CertF N φ := by
  unfold Cut2.CertF
  rw [C.flip_flip_CoverA, C.flip_flip_pole_eq, C.flip_flip_inA_eq]
  exact Iff.rfl

theorem Cut2.flip_flip_Fnc (C : Cut2 P) {N : Fin X.m → Prop} {φ : Fin X.m → Fin 6} :
    C.flip.flip.Fnc N φ ↔ C.Fnc N φ := by
  unfold Cut2.Fnc Cut2.Fneq
  rw [C.flip_flip_CertF, C.flip_flip_inA_eq]
  exact Iff.rfl

theorem Cut2.glueOK_flip (C : Cut2 P) {NA NB : Fin X.m → Prop} {s : Prop} (h : C.flip.GlueOK NB NA s) :
    C.GlueOK NA NB s := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, mc5_congr hc (fun f _ => C.glueN_symm f)⟩

/-- (G4): side `A` without cross ends -/
theorem Cut2.g_nc' (C : Cut2 P) (hG : InG X P) {NA NB : Fin X.m → Prop} {φ ψ : Fin X.m → Fin 6}
    (hA : C.Fnc NA φ) (hB : C.flip.Fneq NB ψ) : C.GlueOK NA NB False :=
  C.glueOK_flip (C.flip.g_nc hG hB ((C.flip_flip_Fnc).2 hA))

/-! ### certificates of a side from its closures -/

/-- (CL1): a colouring of the edge closure with `g_A ∈ N` is an M-type certificate -/
theorem Cut2.certM_of_clo (C : Cut2 P) {N : Fin (addEdge X C.a1 C.a2).m → Prop} (hN : PMOn C.clo N)
    {c : Fin (addEdge X C.a1 C.a2).m → Fin 6} (hc : MC5 C.clo N c) (hl : N (Fin.last X.m)) :
    C.CertM (fun d => N (Fin.castSucc d)) (fun f => c (C.toClo f)) :=
  ⟨C.coverA_of_clo hN ⟨fun _ => trivial, fun _ => hl⟩, C.pole_of_clo c hc.1, C.cl1_class hc hl⟩

/-- (CL2): a colouring of the edge closure with `g_A ∉ N` and no matching rung is an Feq certificate -/
theorem Cut2.feq_of_clo (C : Cut2 P) {N : Fin (addEdge X C.a1 C.a2).m → Prop} (hN : PMOn C.clo N)
    {c : Fin (addEdge X C.a1 C.a2).m → Fin 6} (hc : MC5 C.clo N c) (hl : ¬ N (Fin.last X.m))
    (hnr : ∀ r, C.inA r → N (Fin.castSucc r) → ¬ X.Joins r C.a1 C.a2) :
    C.Feq (fun d => N (Fin.castSucc d)) (fun f => c (C.toClo f)) := by
  have h5 : c (Fin.last X.m) ≠ 5 := fun h => hl ((hc.2 _ C.clo_last).2 h)
  have e1 : c (C.toClo C.e1) = c (Fin.last X.m) := by rw [C.toClo_cut (Or.inl rfl)]
  have e2 : c (C.toClo C.e2) = c (Fin.last X.m) := by rw [C.toClo_cut (Or.inr rfl)]
  exact ⟨⟨C.coverA_of_clo hN ⟨hl, False.elim⟩, C.pole_of_clo c hc.1, C.cl2_class hc,
    fun h => h5 (e1.symm.trans h), fun h => h5 (e2.symm.trans h)⟩, e1.trans e2.symm, hnr⟩

/-- (CL5): a colouring of the edge closure with `g_A ∉ N` and a matching rung gives an Fnc certificate -/
theorem Cut2.fnc_of_clo (C : Cut2 P) (hG : InG X P)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    {N : Fin (addEdge X C.a1 C.a2).m → Prop} (hN : PMOn C.clo N)
    {c : Fin (addEdge X C.a1 C.a2).m → Fin 6} (hc : MC5 C.clo N c) (hl : ¬ N (Fin.last X.m))
    {r : Fin X.m} (hrP : P r) (hrj : X.Joins r C.a1 C.a2) (hrN : N (Fin.castSucc r)) :
    ∃ ψ, C.Fnc (fun d => N (Fin.castSucc d)) ψ := by
  obtain ⟨ψ, hψ, hin, he1, he2γ, he25, hβ1⟩ := C.cl5 hG hpa hN hl hc hrP hrj hrN
  have h5 : c (Fin.last X.m) ≠ 5 := fun h => hl ((hc.2 _ C.clo_last).2 h)
  refine ⟨ψ, ⟨⟨C.coverA_of_clo hN ⟨hl, False.elim⟩, hψ, fun f hf => ?_, fun h => h5 (he1.symm.trans h), he25⟩,
    fun h => he2γ (h.symm.trans he1)⟩, hβ1, fun f hf _ hfa => ?_⟩
  · rw [hin f hf]; exact (hc.2 _ (C.clo_old hf)).symm
  · rw [hin f hf, he1]
    exact hc.1.1 _ _ ⟨castSucc_ne_last f, C.a2, addEdge_inc_old.2 hfa, (C.inc_new_iff).2 (Or.inr rfl)⟩
      (C.clo_old hf) C.clo_last

/-- (CL3): a colouring of the digon closure with `e1 ∈ N` is an M-type certificate with `t ≥ 1` -/
theorem Cut2.certM_of_cloD (C : Cut2 P) (hG : InG X P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N)
    {c : Fin C.XD.m → Fin 6} (hc : MC5 C.cloD N c) (h1 : N (C.oD C.e1)) :
    C.CertM (fun d => N (C.oD d)) (fun f => c (C.oD f)) ∧ C.TMeet (fun f => c (C.oD f)) := by
  obtain ⟨h2, hmeet⟩ := C.cl3 hG hN h1 hc
  refine ⟨⟨?_, C.pole_of_cloD c hc.1, fun f hf => ?_⟩, hmeet⟩
  · intro x hxA hx
    obtain ⟨f, hf, hfx⟩ := hx
    obtain ⟨d, hNd, hdp, hdx, hu⟩ := C.cloD_N_at_A hN hxA ⟨f, C.pole_of_inc hf hfx hxA, hfx⟩
    constructor
    · rintro ⟨_, hx12⟩ d' hd' hNd' hd'x
      have hcut : C.isCut d := by
        rcases hx12 with rfl | rfl
        · have := C.oD_inj (pm_unique hN hNd h1 ((C.XD_inc_old).2 hdx) ((C.XD_inc_old).2 (joins_inc_left C.j1)))
          exact Or.inl this
        · have := C.oD_inj (pm_unique hN hNd h2 ((C.XD_inc_old).2 hdx) ((C.XD_inc_old).2 (joins_inc_left C.j2)))
          exact Or.inr this
      have := C.oD_inj (hu _ hNd' ((C.XD_inc_old).2 hd'x))
      exact C.not_inA_of_cut (this ▸ hcut) hd'
    · intro hnot
      have hdA : C.inA d := by
        rcases hdp with h | h
        · exact h
        · exfalso; apply hnot; refine ⟨trivial, ?_⟩
          rcases C.cutA h hdx hxA with ⟨_, h'⟩ | ⟨_, h'⟩
          · exact Or.inl h'
          · exact Or.inr h'
      exact ⟨d, hdA, hNd, hdx, fun d' _ hNd' hd'x => C.oD_inj (hu _ hNd' ((C.XD_inc_old).2 hd'x))⟩
  · rw [← (hc.2 _ ((C.cloD_old_iff).2 hf))]
    constructor
    · intro hn
      rcases hf with hA | hcut
      · exact Or.inr ⟨hA, hn⟩
      · exact Or.inl hcut
    · rintro (hcut | ⟨_, hn⟩)
      · rcases hcut with rfl | rfl
        · exact h1
        · exact h2
      · exact hn

/-- (CL4): a colouring of the digon closure with `δ ∈ N` is an Fneq certificate -/
theorem Cut2.fneq_of_cloD (C : Cut2 P) (hG : InG X P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N)
    {c : Fin C.XD.m → Fin 6} (hc : MC5 C.cloD N c) (hδ : N C.dl1) :
    C.Fneq (fun d => N (C.oD d)) (fun f => c (C.oD f)) := by
  obtain ⟨n1, n2, hne⟩ := C.cl4_pend hG.1 hN hδ c hc
  refine ⟨⟨C.coverA_of_cloD hN hδ, C.pole_of_cloD c hc.1, fun f hf => (hc.2 _ ((C.cloD_old_iff).2 (Or.inl hf))).symm,
    fun h => n1 ((hc.2 _ ((C.cloD_old_iff).2 (Or.inr (Or.inl rfl)))).2 h),
    fun h => n2 ((hc.2 _ ((C.cloD_old_iff).2 (Or.inr (Or.inr rfl)))).2 h)⟩, hne⟩

/-- exchanging the two parallel digon edges `δ`, `δ′` -/
def Cut2.swD (C : Cut2 P) (i : Fin C.XD.m) : Fin C.XD.m :=
  if i = C.dl1 then C.dl2 else if i = C.dl2 then C.dl1 else i

theorem Cut2.swD_dl1 (C : Cut2 P) : C.swD C.dl1 = C.dl2 := by simp [Cut2.swD]
theorem Cut2.swD_dl2 (C : Cut2 P) : C.swD C.dl2 = C.dl1 := by
  simp [Cut2.swD, Ne.symm C.dl1_ne_dl2]
theorem Cut2.swD_oD (C : Cut2 P) (d : Fin X.m) : C.swD (C.oD d) = C.oD d := by
  simp [Cut2.swD, C.oD_ne_dl1 d, C.oD_ne_dl2 d]
theorem Cut2.swD_invol (C : Cut2 P) (i : Fin C.XD.m) : C.swD (C.swD i) = i := by
  rcases C.XD_cases i with rfl | rfl | ⟨d, rfl⟩
  · rw [C.swD_dl2, C.swD_dl1]
  · rw [C.swD_dl1, C.swD_dl2]
  · rw [C.swD_oD, C.swD_oD]
theorem Cut2.swD_ends (C : Cut2 P) (i : Fin C.XD.m) : C.XD.ends (C.swD i) = C.XD.ends i := by
  rcases C.XD_cases i with rfl | rfl | ⟨d, rfl⟩
  · rw [C.swD_dl2, C.XD_ends_dl1, C.XD_ends_dl2]
  · rw [C.swD_dl1, C.XD_ends_dl1, C.XD_ends_dl2]
  · rw [C.swD_oD]
theorem Cut2.swD_cloD (C : Cut2 P) (i : Fin C.XD.m) : C.cloD (C.swD i) ↔ C.cloD i := by
  rcases C.XD_cases i with rfl | rfl | ⟨d, rfl⟩
  · rw [C.swD_dl2]; exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => Or.inl rfl⟩
  · rw [C.swD_dl1]; exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr (Or.inl rfl)⟩
  · rw [C.swD_oD]

theorem Cut2.swD_inc (C : Cut2 P) (i : Fin C.XD.m) (x : Fin X.n) : C.XD.Inc (C.swD i) x ↔ C.XD.Inc i x := by
  unfold Inc; rw [C.swD_ends]

theorem Cut2.mc5_swD (C : Cut2 P) {N : Fin C.XD.m → Prop} {c : Fin C.XD.m → Fin 6} (hc : MC5 C.cloD N c) :
    MC5 C.cloD (fun i => N (C.swD i)) (fun i => c (C.swD i)) := by
  refine ⟨starOn_embed (G := C.XD) (H := C.XD) (fun x => x) C.swD (fun _ _ _ _ _ _ _ _ h => h)
    (fun a b _ _ h => by rw [← C.swD_invol a, h, C.swD_invol]) (fun a ha => (C.swD_cloD a).2 ha)
    (fun a _ => by show C.XD.Joins (C.swD a) _ _; unfold Joins; rw [C.swD_ends]; exact Or.inl rfl) hc.1,
    fun i hi => hc.2 _ ((C.swD_cloD i).2 hi)⟩

theorem Cut2.pm_swD (C : Cut2 P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N) :
    PMOn C.cloD (fun i => N (C.swD i)) := by
  refine ⟨fun f hf => (C.swD_cloD f).1 (hN.1 _ hf), fun x ⟨f, hf, hfx⟩ => ?_⟩
  obtain ⟨a, ha, hax, hu⟩ := hN.2 x ⟨f, hf, hfx⟩
  refine ⟨C.swD a, by show N (C.swD (C.swD a)); rw [C.swD_invol]; exact ha, (C.swD_inc a x).2 hax, ?_⟩
  intro d hd hdx
  have := hu _ hd ((C.swD_inc d x).2 hdx)
  rw [← this, C.swD_invol]

/-- the matching edge at the digon vertex `b1` is `e1`, `δ` or `δ′` -/
theorem Cut2.cloD_N_b1 (C : Cut2 P) {N : Fin C.XD.m → Prop} (hN : PMOn C.cloD N) :
    N (C.oD C.e1) ∨ N C.dl1 ∨ N C.dl2 := by
  obtain ⟨j, hjN, hjb, _⟩ := hN.2 C.b1 ⟨C.dl1, Or.inl rfl, (C.XD_inc_dl1).2 (Or.inl rfl)⟩
  rcases C.cloD_at_b (hN.1 _ hjN) (Or.inl rfl) hjb with rfl | rfl | ⟨rfl, _⟩ | ⟨_, h⟩
  · exact Or.inr (Or.inl hjN)
  · exact Or.inr (Or.inr hjN)
  · exact Or.inl hjN
  · exact absurd h C.hb

/-! ### Lemma SR -/

/-- **Lemma SR (b)** (fact 5a68c9cb62d7148d): recipe E for side `A` and EX1-goodness of `G_B` give EX1-goodness,
    when at most one edge joins `b1, b2`. -/
theorem Cut2.sr_b (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hpb : ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f')
    (hRE : C.RecipeE) (hB : EX1On C.flip.clo) : EX1On P := by
  classical
  obtain ⟨⟨NM, φM, hcM, hsM⟩, ⟨NQ, φQ, hcQ⟩, ⟨NF, φF, hcF⟩, hcov⟩ := hRE
  have GB := C.flip.clo_inG hG
  have certB_M : ∃ NB ψ, C.flip.CertM NB ψ ∧ C.flip.TSmall ψ := by
    obtain ⟨N, c, hN, hst, hc⟩ := ex1_full hPS GB hB C.flip.clo_last true
    exact ⟨_, _, C.flip.certM_of_clo hN hc (hst.2 rfl), C.flip.cl1_small hG hpb hN hc (hst.2 rfl)⟩
  have certB_Feq : ∃ NB ψ, C.flip.Feq NB ψ := by
    obtain ⟨f, hf, hfb, hfj⟩ := C.flip.nonrung hG.2.2.2 hpb
    obtain ⟨N, c, hN, hst, hc⟩ := ex1_full hPS GB hB (C.flip.clo_old hf) true
    have hNf : N (Fin.castSucc f) := hst.2 rfl
    have hfb' : (addEdge X C.flip.a1 C.flip.a2).Inc (Fin.castSucc f) C.flip.a1 := addEdge_inc_old.2 hfb
    have hlb : (addEdge X C.flip.a1 C.flip.a2).Inc (Fin.last X.m) C.flip.a1 := (C.flip.inc_new_iff).2 (Or.inl rfl)
    have hnl : ¬ N (Fin.last X.m) := fun h => castSucc_ne_last f (pm_unique hN hNf h hfb' hlb)
    refine ⟨_, _, C.flip.feq_of_clo hN hc hnl (fun r _ hrN hrj => ?_)⟩
    have := castSucc_inj' (pm_unique hN hrN hNf (addEdge_inc_old.2 (joins_inc_left hrj)) hfb')
    exact hfj (this ▸ hrj)
  intro g hg t _
  have main : ∃ M c, PMOn P M ∧ (M g ↔ t = true) ∧ MC5 P M c := by
    rcases C.cases_P hg with h | h | h
    · obtain ⟨N, φ, hcert, hst⟩ := hcov g h t
      rcases hcert with ⟨hM, hsm⟩ | hQ
      · obtain ⟨NB, ψ, hBM, hBs⟩ := certB_M
        obtain ⟨c, hc⟩ := C.g1_small hG hM hsm hBM hBs
        exact ⟨_, c, C.pm_glue hM.1 hBM.1, by rw [C.glueN_A h]; exact hst, hc⟩
      · obtain ⟨NB, ψ, hBQ⟩ := certB_Feq
        obtain ⟨c, hc⟩ := C.g_eq hG hQ hBQ
        exact ⟨_, c, C.pm_glue hQ.1.1 hBQ.1.1, by rw [C.glueN_A h]; exact hst, hc⟩
    · obtain ⟨N, c, hN, hst, hc⟩ := ex1_full hPS GB hB (C.flip.clo_old h) t
      by_cases hl : N (Fin.last X.m)
      · have hBM := C.flip.certM_of_clo hN hc hl
        obtain ⟨cg, hcg⟩ := C.g1_small hG hcM hsM hBM (C.flip.cl1_small hG hpb hN hc hl)
        exact ⟨_, cg, C.pm_glue hcM.1 hBM.1, by rw [C.glueN_B h]; exact hst, hcg⟩
      · by_cases hr : ∃ r, C.flip.inA r ∧ N (Fin.castSucc r) ∧ X.Joins r C.b1 C.b2
        · obtain ⟨r, hrA, hrN, hrj⟩ := hr
          obtain ⟨ψ, hψ⟩ := C.flip.fnc_of_clo hG hpb hN hc hl hrA.1 hrj hrN
          obtain ⟨cg, hcg⟩ := C.g_nc hG hcF hψ
          exact ⟨_, cg, C.pm_glue hcF.1.1 hψ.1.1.1, by rw [C.glueN_B h]; exact hst, hcg⟩
        · have hBQ := C.flip.feq_of_clo hN hc hl (fun r hrA hrN hrj => hr ⟨r, hrA, hrN, hrj⟩)
          obtain ⟨cg, hcg⟩ := C.g_eq hG hcQ hBQ
          exact ⟨_, cg, C.pm_glue hcQ.1.1 hBQ.1.1, by rw [C.glueN_B h]; exact hst, hcg⟩
    · cases t
      · obtain ⟨NB, ψ, hBQ⟩ := certB_Feq
        obtain ⟨cg, hcg⟩ := C.g_eq hG hcQ hBQ
        exact ⟨_, cg, C.pm_glue hcQ.1.1 hBQ.1.1, by rw [C.glueN_cut h]; simp, hcg⟩
      · obtain ⟨NB, ψ, hBM, hBs⟩ := certB_M
        obtain ⟨cg, hcg⟩ := C.g1_small hG hcM hsM hBM hBs
        exact ⟨_, cg, C.pm_glue hcM.1 hBM.1, by rw [C.glueN_cut h]; simp, hcg⟩
  obtain ⟨M, c, hM, hst, hc⟩ := main
  exact ⟨M, hM, hst, c, hc.1, 5, hc.2⟩

/-- **Lemma SR (a)** (fact 5a68c9cb62d7148d): recipe D for side `A` and EX1-goodness of `G_B^D` give
    EX1-goodness. -/
theorem Cut2.sr_a (hPS : PStat) (C : Cut2 P) (hG : InG X P) (hRD : C.RecipeD) (hBD : EX1On C.flip.cloD) :
    EX1On P := by
  classical
  obtain ⟨⟨NM, φM, hcM, hsM⟩, ⟨NF, φF, hcF⟩, hcov⟩ := hRD
  have GD := C.flip.cloD_inG hG
  -- the three kinds of closure colourings of `G_B^D`
  have fromD : ∀ (N : Fin C.flip.XD.m → Prop) (c : Fin C.flip.XD.m → Fin 6), PMOn C.flip.cloD N →
      MC5 C.flip.cloD N c →
      (∃ NB ψ, C.flip.CertM NB ψ ∧ C.flip.TMeet ψ ∧ ∀ f, NB f ↔ N (C.flip.oD f)) ∨
      (∃ NB ψ, C.flip.Fneq NB ψ ∧ ∀ f, NB f ↔ N (C.flip.oD f)) := by
    intro N c hN hc
    rcases C.flip.cloD_N_b1 hN with h1 | h1 | h1
    · obtain ⟨hcm, hmt⟩ := C.flip.certM_of_cloD hG hN hc h1
      exact Or.inl ⟨_, _, hcm, hmt, fun _ => Iff.rfl⟩
    · exact Or.inr ⟨_, _, C.flip.fneq_of_cloD hG hN hc h1, fun _ => Iff.rfl⟩
    · have hN' := C.flip.pm_swD hN
      have hc' := C.flip.mc5_swD hc
      have h1' : N (C.flip.swD C.flip.dl1) := by rw [C.flip.swD_dl1]; exact h1
      refine Or.inr ⟨_, _, C.flip.fneq_of_cloD hG hN' hc' h1', fun f => ?_⟩
      show N (C.flip.swD (C.flip.oD f)) ↔ N (C.flip.oD f)
      rw [C.flip.swD_oD]
  have certB_M : ∃ NB ψ, C.flip.CertM NB ψ ∧ C.flip.TMeet ψ := by
    obtain ⟨N, c, hN, hst, hc⟩ := ex1_full hPS GD hBD ((C.flip.cloD_old_iff).2 (Or.inr (Or.inl rfl))) true
    obtain ⟨hcm, hmt⟩ := C.flip.certM_of_cloD hG hN hc (hst.2 rfl)
    exact ⟨_, _, hcm, hmt⟩
  have certB_F : ∃ NB ψ, C.flip.Fneq NB ψ := by
    obtain ⟨N, c, hN, hst, hc⟩ := ex1_full hPS GD hBD (Or.inl rfl : C.flip.cloD C.flip.dl1) true
    exact ⟨_, _, C.flip.fneq_of_cloD hG hN hc (hst.2 rfl)⟩
  intro g hg t _
  have main : ∃ M c, PMOn P M ∧ (M g ↔ t = true) ∧ MC5 P M c := by
    rcases C.cases_P hg with h | h | h
    · obtain ⟨N, φ, hcert, hst⟩ := hcov g h t
      rcases hcert with ⟨hM, hsm⟩ | hF
      · obtain ⟨NB, ψ, hBM, hBs⟩ := certB_M
        obtain ⟨c, hc⟩ := C.g1_meet hG hM hsm hBM hBs
        exact ⟨_, c, C.pm_glue hM.1 hBM.1, by rw [C.glueN_A h]; exact hst, hc⟩
      · obtain ⟨NB, ψ, hBF⟩ := certB_F
        obtain ⟨c, hc⟩ := C.g_nc' hG hF hBF
        exact ⟨_, c, C.pm_glue hF.1.1.1 hBF.1.1, by rw [C.glueN_A h]; exact hst, hc⟩
    · obtain ⟨N, c, hN, hst, hc⟩ := ex1_full hPS GD hBD ((C.flip.cloD_old_iff).2 (Or.inl h)) t
      rcases fromD N c hN hc with ⟨NB, ψ, hBM, hBs, hNB⟩ | ⟨NB, ψ, hBF, hNB⟩
      · obtain ⟨cg, hcg⟩ := C.g1_meet hG hcM hsM hBM hBs
        exact ⟨_, cg, C.pm_glue hcM.1 hBM.1, by rw [C.glueN_B h, hNB]; exact hst, hcg⟩
      · obtain ⟨cg, hcg⟩ := C.g_nc' hG hcF hBF
        exact ⟨_, cg, C.pm_glue hcF.1.1.1 hBF.1.1, by rw [C.glueN_B h, hNB]; exact hst, hcg⟩
    · cases t
      · obtain ⟨NB, ψ, hBF⟩ := certB_F
        obtain ⟨cg, hcg⟩ := C.g_nc' hG hcF hBF
        exact ⟨_, cg, C.pm_glue hcF.1.1.1 hBF.1.1, by rw [C.glueN_cut h]; simp, hcg⟩
      · obtain ⟨NB, ψ, hBM, hBs⟩ := certB_M
        obtain ⟨cg, hcg⟩ := C.g1_meet hG hcM hsM hBM hBs
        exact ⟨_, cg, C.pm_glue hcM.1 hBM.1, by rw [C.glueN_cut h]; simp, hcg⟩
  obtain ⟨M, c, hM, hst, hc⟩ := main
  exact ⟨M, hM, hst, c, hc.1, 5, hc.2⟩

end sr

end RH2F

namespace RH2F
open MGraph

/-- **Layer 3 of the Lean formalization of RH2**: Lemma SR (fact 5a68c9cb62d7148d), parts (a) and (b), from part (P)
    of fact f6e8c173bef4cfa1. -/
theorem layer3 :
    (PStat → ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → C.RecipeD → EX1On C.flip.cloD →
      EX1On P) ∧
    (PStat → ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P →
      (∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f') →
      C.RecipeE → EX1On C.flip.clo → EX1On P) :=
  ⟨fun hPS _ _ C hG hRD hBD => C.sr_a hPS hG hRD hBD,
   fun hPS _ _ C hG hpb hRE hB => C.sr_b hPS hG hpb hRE hB⟩

end RH2F
