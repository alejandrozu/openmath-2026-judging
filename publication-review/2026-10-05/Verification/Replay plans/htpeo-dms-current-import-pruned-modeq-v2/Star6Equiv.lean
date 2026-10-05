/-
  Star6Equiv.lean — DMS is equivalent to its restriction to connected bridgeless cubic multigraphs on at least 16
  vertices and their leaf graphs (Lean 4.33.1 + Mathlib v4.33.1).  Statements fixed by the lead.
-/
import Star6Corollaries
set_option backward.isDefEq.respectTransparency false

namespace Star6
open MGraph RH2F
open Classical

/-- A degree bound on an edge set is enough to apply DMS to that edge set. -/
private theorem colourable_of_dms_sub (h : DMS) (X : MGraph) (P : Fin X.m → Prop)
    (hL : Loopless X)
    (h3 : ∀ x a b c d, P a → P b → P c → P d → X.Inc a x → X.Inc b x →
      X.Inc c x → X.Inc d x → a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False) :
    Colourable P 6 := by
  let R := RH2Fid.subRep X P
  let en := RH2Fid.subEn X P
  have hd : RH2Fid.MaxDeg3 en := by
    intro v
    by_contra hlt
    have hcount : RH2Fid.deg en v = (Finset.univ.filter (fun e => v ∈ en e)).card := by
      unfold RH2Fid.deg
      congr 1
      ext e
      simp
    have hfour : 3 < (Finset.univ.filter (fun e => v ∈ en e)).card := by
      rw [← hcount]
      omega
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      RH2Fid.exists_four (Finset.univ.filter (fun e => v ∈ en e)) hfour
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc hd
    exact h3 (R.φ v) (R.ψ a) (R.ψ b) (R.ψ c) (R.ψ d)
      (R.ψP a) (R.ψP b) (R.ψP c) (R.ψP d)
      ((R.inc_iff _ _).2 ha) ((R.inc_iff _ _).2 hb)
      ((R.inc_iff _ _).2 hc) ((R.inc_iff _ _).2 hd)
      (fun he => hab (R.ψinj _ _ he)) (fun he => hac (R.ψinj _ _ he))
      (fun he => had (R.ψinj _ _ he)) (fun he => hbc (R.ψinj _ _ he))
      (fun he => hbd (R.ψinj _ _ he)) (fun he => hcd (R.ψinj _ _ he))
  have hs := (RH2Fid.dms_iff.1 h) (RH2Fid.SubV X P) (RH2Fid.SubE X P)
    (RH2Fid.subEn X P) (RH2Fid.sub_loopless X P hL) hd
  exact (R.colourable_iff (by decide)).2 ((RH2Fid.star6P_iff _).1 hs)

private theorem cubic_no_four (X : MGraph) (P : Fin X.m → Prop) (hK : CubicOn P) :
    ∀ x a b c d, P a → P b → P c → P d → X.Inc a x → X.Inc b x →
      X.Inc c x → X.Inc d x → a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  intro x a b c d ha hb hc hd hax hbx hcx hdx hab hac had hbc hbd hcd
  obtain ⟨e, f, k, _, _, _, _, _, _, _, _, _, hall⟩ := hK x ⟨a, ha, hax⟩
  rcases hall a ha hax with ha' | ha' | ha' <;>
    rcases hall b hb hbx with hb' | hb' | hb' <;>
    rcases hall c hc hcx with hc' | hc' | hc' <;>
    rcases hall d hd hdx with hd' | hd' | hd' <;>
    subst_vars <;> contradiction

private theorem four_of_three {α : Type} (u v w a b c d : α)
    (ha : a = u ∨ a = v ∨ a = w) (hb : b = u ∨ b = v ∨ b = w)
    (hc : c = u ∨ c = v ∨ c = w) (hd : d = u ∨ d = v ∨ d = w)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;>
    rcases hd with hd | hd | hd <;>
    subst_vars <;> contradiction

private def leafRepl (X : MGraph) (g : Fin X.m) (v : Fin X.n) (d : Fin X.m) :
    Fin (leafG X g).m :=
  if d = g then
    if v = (X.ends g).1 then newE g 0 (by decide) else newE g 1 (by decide)
  else oldE g d

private theorem leaf_inc_old (X : MGraph) (P : Fin X.m → Prop) (hL : Loopless X)
    (g : Fin X.m) (hg : P g) (v : Fin X.n) (a : Fin (leafG X g).m)
    (ha : leafSet P g a) (hax : (leafG X g).Inc a (lv v)) :
    ∃ d, P d ∧ X.Inc d v ∧ a = leafRepl X g v d := by
  rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
  · obtain ⟨hd, hne⟩ := (set_old P g d).1 ha
    obtain ⟨w, hw, hdw⟩ := inc_old_lv hax
    have hvw : v = w := lv_inj hw
    subst w
    exact ⟨d, hd, hdw, by simp [leafRepl, hne]⟩
  · unfold MGraph.Inc at hax
    rw [ends_new0] at hax
    rcases hax with hax | hax
    · have hv : v = (X.ends g).1 := lv_inj hax.symm
      subst v
      exact ⟨g, hg, Or.inl rfl, by simp [leafRepl]⟩
    · exact False.elim ((lv_ne_vx v) hax.symm)
  · unfold MGraph.Inc at hax
    rw [ends_new1] at hax
    rcases hax with hax | hax
    · exact False.elim ((lv_ne_vx v) hax.symm)
    · have hv : v = (X.ends g).2 := lv_inj hax.symm
      subst v
      have hne : (X.ends g).2 ≠ (X.ends g).1 := Ne.symm (hL g)
      exact ⟨g, hg, Or.inr rfl, by simp [leafRepl, hne]⟩
  · unfold MGraph.Inc at hax
    rw [ends_new2] at hax
    rcases hax with hax | hax
    · exact False.elim ((lv_ne_vx v) hax.symm)
    · exact False.elim ((lv_ne_vl v) hax.symm)

private theorem leaf_loopless (X : MGraph) (hL : Loopless X) (g : Fin X.m) :
    Loopless (leafG X g) := by
  intro a
  rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
  · rw [ends_old]
    intro he
    exact hL d (lv_inj he)
  · rw [ends_new0]
    exact lv_ne_vx _
  · rw [ends_new1]
    exact (lv_ne_vx _).symm
  · rw [ends_new2]
    exact vx_ne_vl X

private theorem leaf_no_four (X : MGraph) (P : Fin X.m → Prop) (hL : Loopless X)
    (hK : CubicOn P) (g : Fin X.m) (hg : P g) :
    ∀ x a b c d, leafSet P g a → leafSet P g b → leafSet P g c → leafSet P g d →
      (leafG X g).Inc a x → (leafG X g).Inc b x → (leafG X g).Inc c x →
      (leafG X g).Inc d x → a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  intro x a b c d ha hb hc hd hax hbx hcx hdx hab hac had hbc hbd hcd
  by_cases hx : x.val < X.n
  · let v : Fin X.n := ⟨x.val, hx⟩
    have hxv : x = lv v := Fin.ext (by simp [v, lv_val])
    rw [hxv] at hax hbx hcx hdx
    obtain ⟨a', haP, haI, hae⟩ := leaf_inc_old X P hL g hg v a ha hax
    obtain ⟨b', hbP, hbI, hbe⟩ := leaf_inc_old X P hL g hg v b hb hbx
    obtain ⟨c', hcP, hcI, hce⟩ := leaf_inc_old X P hL g hg v c hc hcx
    obtain ⟨d', hdP, hdI, hde⟩ := leaf_inc_old X P hL g hg v d hd hdx
    obtain ⟨u, w, z, _, _, _, _, _, _, _, _, _, hall⟩ := hK v ⟨a', haP, haI⟩
    have cover : ∀ t, P t → X.Inc t v →
        leafRepl X g v t = leafRepl X g v u ∨
        leafRepl X g v t = leafRepl X g v w ∨
        leafRepl X g v t = leafRepl X g v z := by
      intro t ht htv
      rcases hall t ht htv with h | h | h
      · exact Or.inl (congrArg (leafRepl X g v) h)
      · exact Or.inr (Or.inl (congrArg (leafRepl X g v) h))
      · exact Or.inr (Or.inr (congrArg (leafRepl X g v) h))
    exact four_of_three (leafRepl X g v u) (leafRepl X g v w) (leafRepl X g v z)
      a b c d (hae.symm ▸ cover a' haP haI) (hbe.symm ▸ cover b' hbP hbI)
      (hce.symm ▸ cover c' hcP hcI) (hde.symm ▸ cover d' hdP hdI)
      hab hac had hbc hbd hcd
  · have only_new : ∀ e, (leafG X g).Inc e x →
        e = newE g 0 (by decide) ∨ e = newE g 1 (by decide) ∨ e = newE g 2 (by decide) := by
      intro e hex
      rcases leaf_cases g e with ⟨f, rfl⟩ | h | h | h
      · obtain ⟨w, hw, _⟩ := inc_old_lv hex
        exact False.elim (hx (by rw [hw, lv_val]; exact w.isLt))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact four_of_three (newE g 0 (by decide)) (newE g 1 (by decide)) (newE g 2 (by decide))
      a b c d (only_new a hax) (only_new b hbx) (only_new c hcx) (only_new d hdx)
      hab hac had hbc hbd hcd

/-- DMS gives star 6-colourability of every cubic edge set `P` of a loopless multigraph `X`
    (the ambient multigraph `X` need not be subcubic) -/
theorem colourable_of_dms_cubic (h : DMS) (X : MGraph) (P : Fin X.m → Prop) (hL : Loopless X) (hK : CubicOn P) :
    Colourable P 6 := by
  exact colourable_of_dms_sub h X P hL (cubic_no_four X P hK)

/-- DMS gives star 6-colourability of every leaf graph T(P, g) of a cubic edge set `P` of a loopless multigraph -/
theorem leaf_of_dms (h : DMS) (X : MGraph) (P : Fin X.m → Prop) (hL : Loopless X) (hK : CubicOn P) (g : Fin X.m)
    (hg : P g) : Colourable (leafSet P g) 6 := by
  exact colourable_of_dms_sub h (leafG X g) (leafSet P g)
    (leaf_loopless X hL g) (leaf_no_four X P hL hK g hg)

/-- **Equivalence theorem.** The Dvořák–Mohar–Šámal conjecture (every loopless multigraph of maximum degree at most
    3 is star 6-edge-colourable) holds if and only if every connected bridgeless cubic loopless multigraph `P` on at
    least 16 vertices is star 6-edge-colourable and so is each of its leaf graphs T(P, g). -/
theorem dms_iff_cubic16 :
    DMS ↔ ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 16 ≤ vcount P →
      Colourable P 6 ∧ ∀ g, P g → Colourable (leafSet P g) 6 := by
  constructor
  · intro h X P hG _
    exact ⟨colourable_of_dms_cubic h X P hG.1 hG.2.2.2, fun g hg => leaf_of_dms h X P hG.1 hG.2.2.2 g hg⟩
  · intro h
    apply Classical.byContradiction
    intro hD
    rcases counterexample_cubic16 hD with ⟨X, P, hG, h16, hc⟩ | ⟨X, P, g, hG, h16, hg, hc⟩
    · exact hc (h X P hG h16).1
    · exact hc ((h X P hG h16).2 g hg)

end Star6

#print axioms Star6.colourable_of_dms_cubic
#print axioms Star6.leaf_of_dms
#print axioms Star6.dms_iff_cubic16
