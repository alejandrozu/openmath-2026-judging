import InflationD

namespace Inflation

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem complete_three :
    ∀ t0 t1 t2 : Fin 6,
      (t0.val = 5 ∨ t1.val = 5 ∨ t0 ≠ t1) →
      (t0.val = 5 ∨ t2.val = 5 ∨ t0 ≠ t2) →
      (t1.val = 5 ∨ t2.val = 5 ∨ t1 ≠ t2) →
      ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (t0.val < 5 → a.val = t0.val) ∧
        (t1.val < 5 → b.val = t1.val) ∧
        (t2.val < 5 → c.val = t2.val) := by decide

theorem perm_three (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ ρ : Fin 5 → Fin 5, Function.Injective ρ ∧
      ρ (pi 0) = a ∧ ρ (pi 1) = b ∧ ρ (pi 2) = c := by
  let p0 : Equiv.Perm (Fin 5) := Equiv.swap 4 a
  let p1 : Equiv.Perm (Fin 5) := p0.trans (Equiv.swap (p0 3) b)
  let p2 : Equiv.Perm (Fin 5) := p1.trans (Equiv.swap (p1 1) c)
  have h04 : p0 4 = a := Equiv.swap_apply_left 4 a
  have h13 : p1 3 = b := by
    simp only [p1, Equiv.trans_apply]
    exact Equiv.swap_apply_left (p0 3) b
  have h14 : p1 4 = a := by
    change (Equiv.swap (p0 3) b) (p0 4) = a
    have hn : p0 4 ≠ p0 3 := fun h => (by decide : (4 : Fin 5) ≠ 3) (p0.injective h)
    have hb : p0 4 ≠ b := by rwa [h04]
    rw [Equiv.swap_apply_of_ne_of_ne hn hb]
    exact h04
  have h21 : p2 1 = c := by
    simp only [p2, Equiv.trans_apply]
    exact Equiv.swap_apply_left (p1 1) c
  have h23 : p2 3 = b := by
    change (Equiv.swap (p1 1) c) (p1 3) = b
    have hn : p1 3 ≠ p1 1 := fun h => (by decide : (3 : Fin 5) ≠ 1) (p1.injective h)
    have hc : p1 3 ≠ c := by rwa [h13]
    rw [Equiv.swap_apply_of_ne_of_ne hn hc]
    exact h13
  have h24 : p2 4 = a := by
    change (Equiv.swap (p1 1) c) (p1 4) = a
    have hn : p1 4 ≠ p1 1 := fun h => (by decide : (4 : Fin 5) ≠ 1) (p1.injective h)
    have hc : p1 4 ≠ c := by rwa [h14]
    rw [Equiv.swap_apply_of_ne_of_ne hn hc]
    exact h14
  exact ⟨p2, p2.injective, by simpa [pi] using h24,
    by simpa [pi] using h23, by simpa [pi] using h21⟩

variable (H : MGraph) (slot : Fin H.m → Bool → Fin 3)

noncomputable def portTarget (φ : Fin H.m → Fin 5) (X : Fin H.n) (i : Fin 3) : Fin 6 :=
  if h : ∃ q : Fin H.m × Bool, endOf H q.1 q.2 = X ∧ slot q.1 q.2 = i then
    ⟨(φ (Classical.choose h).1).val, by have := (φ (Classical.choose h).1).isLt; omega⟩
  else 5

theorem portTarget_source (φ : Fin H.m → Fin 5) (X : Fin H.n) (i : Fin 3)
    (ht : (portTarget H slot φ X i).val < 5) :
    ∃ e : Fin H.m, ∃ b : Bool,
      endOf H e b = X ∧ slot e b = i ∧ (portTarget H slot φ X i).val = (φ e).val := by
  by_cases h : ∃ q : Fin H.m × Bool, endOf H q.1 q.2 = X ∧ slot q.1 q.2 = i
  · refine ⟨(Classical.choose h).1, (Classical.choose h).2,
      (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
    simp [portTarget, h]
  · have hf : (portTarget H slot φ X i).val = 5 := by simp [portTarget, h]
    omega

theorem portTarget_match (hinj : PortsInj H slot)
    (φ : Fin H.m → Fin 5) (e : Fin H.m) (b : Bool) :
    (portTarget H slot φ (endOf H e b) (slot e b)).val = (φ e).val := by
  unfold portTarget
  split_ifs with h
  · have hp := Classical.choose_spec h
    have he : (Classical.choose h).1 = e := (hinj _ _ e b hp.1 hp.2).1
    simpa only [he]
  · exact False.elim (h ⟨(e, b), rfl, rfl⟩)

theorem side_unique (hl : H.Loopless) (e : Fin H.m) (b b' : Bool)
    (h : endOf H e b = endOf H e b') : b = b' := by
  cases b <;> cases b'
  · rfl
  · exact False.elim ((hl e) (by simpa [endOf] using h))
  · exact False.elim ((hl e) (by simpa [endOf] using h.symm))
  · rfl

theorem portTarget_ne (hl : H.Loopless)
    (φ : Fin H.m → Fin 5)
    (hφ : ∀ e f, H.Adj e f → φ e ≠ φ f)
    (X : Fin H.n) (i j : Fin 3) (hij : i ≠ j)
    (hi : (portTarget H slot φ X i).val < 5)
    (hj : (portTarget H slot φ X j).val < 5) :
    portTarget H slot φ X i ≠ portTarget H slot φ X j := by
  obtain ⟨e, b, heX, hei, hte⟩ := portTarget_source H slot φ X i hi
  obtain ⟨f, b', hfX, hfj, htf⟩ := portTarget_source H slot φ X j hj
  have hef : e ≠ f := by
    intro h
    subst f
    have hbb : b = b' := side_unique H hl e b b' (heX.trans hfX.symm)
    subst b'
    exact hij (hei.symm.trans hfj)
  have hincE : H.Inc e X := by
    cases b <;> simp only [endOf] at heX
    · exact Or.inl heX
    · exact Or.inr heX
  have hincF : H.Inc f X := by
    cases b' <;> simp only [endOf] at hfX
    · exact Or.inl hfX
    · exact Or.inr hfX
  have hneq := hφ e f ⟨hef, X, hincE, hincF⟩
  intro h
  apply hneq
  apply Fin.ext
  have hv := congrArg Fin.val h
  omega

theorem local_permutation (hl : H.Loopless) (hinj : PortsInj H slot)
    (φ : Fin H.m → Fin 5)
    (hφ : ∀ e f, H.Adj e f → φ e ≠ φ f)
    (X : Fin H.n) :
    ∃ ρ : Fin 5 → Fin 5, Function.Injective ρ ∧
      ∀ e b, endOf H e b = X → ρ (pi (slot e b)) = φ e := by
  let t0 := portTarget H slot φ X 0
  let t1 := portTarget H slot φ X 1
  let t2 := portTarget H slot φ X 2
  have d01 : t0.val = 5 ∨ t1.val = 5 ∨ t0 ≠ t1 := by
    by_cases h0 : t0.val = 5
    · exact Or.inl h0
    by_cases h1 : t1.val = 5
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr (portTarget_ne H slot hl φ hφ X 0 1
      (by decide) (by have := t0.isLt; omega) (by have := t1.isLt; omega)))
  have d02 : t0.val = 5 ∨ t2.val = 5 ∨ t0 ≠ t2 := by
    by_cases h0 : t0.val = 5
    · exact Or.inl h0
    by_cases h2 : t2.val = 5
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (portTarget_ne H slot hl φ hφ X 0 2
      (by decide) (by have := t0.isLt; omega) (by have := t2.isLt; omega)))
  have d12 : t1.val = 5 ∨ t2.val = 5 ∨ t1 ≠ t2 := by
    by_cases h1 : t1.val = 5
    · exact Or.inl h1
    by_cases h2 : t2.val = 5
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (portTarget_ne H slot hl φ hφ X 1 2
      (by decide) (by have := t1.isLt; omega) (by have := t2.isLt; omega)))
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := complete_three t0 t1 t2 d01 d02 d12
  obtain ⟨ρ, hρ, hρa, hρb, hρc⟩ := perm_three a b c hab hac hbc
  have htarget : ∀ i : Fin 3, (portTarget H slot φ X i).val < 5 →
      (ρ (pi i)).val = (portTarget H slot φ X i).val := by
    intro i hi
    fin_cases i
    · change (ρ (pi 0)).val = (portTarget H slot φ X 0).val
      rw [hρa]
      exact ha hi
    · change (ρ (pi 1)).val = (portTarget H slot φ X 1).val
      rw [hρb]
      exact hb hi
    · change (ρ (pi 2)).val = (portTarget H slot φ X 2).val
      rw [hρc]
      exact hc hi
  refine ⟨ρ, hρ, ?_⟩
  intro e b heX
  have hm : (portTarget H slot φ X (slot e b)).val = (φ e).val := by
    rw [← heX]
    exact portTarget_match H slot hinj φ e b
  apply Fin.ext
  calc
    (ρ (pi (slot e b))).val = (portTarget H slot φ X (slot e b)).val :=
      htarget _ (by rw [hm]; exact (φ e).isLt)
    _ = (φ e).val := hm

end Inflation
