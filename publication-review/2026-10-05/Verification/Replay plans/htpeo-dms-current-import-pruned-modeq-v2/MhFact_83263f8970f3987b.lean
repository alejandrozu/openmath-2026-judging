-- Lean proof of fact 83263f8970f3987b (RH2F.layer24); added by fact_submit, do not edit
import MhFact_bde9371a01dd2855
set_option backward.isDefEq.respectTransparency false


/-
  W1.lean — the colour renaming of Theorem W-RED (a) (fact 1a864fdc0e0af441), Step 1: a permutation `π` of the six
  colours fixing `6` (Lean colour `5`) with `π(A) = a_j`, `π(B) = a_k`, which maps the free colour `γ_j` of `x_j`
  away from `β_j`, the free colour `γ_k` of `x_k` away from `β_k`, and, in shape (S1), the colour `c` to `τ`.
  The general case is reduced to `A = a_j = 0`, `B = a_k = 1` by two explicit permutations; the reduced case is a
  finite check.
-/

namespace RH2F

/-- the transposition of `a` and `b` -/
def sw (a b x : Fin 6) : Fin 6 := if x = a then b else if x = b then a else x

/-- a permutation sending `A ↦ 0`, `B ↦ 1`, `5 ↦ 5` (for distinct `A`, `B` other than `5`) -/
def nrm (A B x : Fin 6) : Fin 6 := sw 1 (sw 0 A B) (sw 0 A x)

/-- its inverse -/
def nrmInv (A B x : Fin 6) : Fin 6 := sw 0 A (sw 1 (sw 0 A B) x)

theorem nrm_spec : ∀ A B : Fin 6, A ≠ B → A ≠ 5 → B ≠ 5 →
    nrm A B A = 0 ∧ nrm A B B = 1 ∧ nrm A B 5 = 5 ∧ ∀ x, nrmInv A B (nrm A B x) = x ∧ nrm A B (nrmInv A B x) = x := by
  decide

/-- the six permutations fixing `0`, `1`, `5` -/
def perms234 : List (Fin 6 → Fin 6) :=
  [![0, 1, 2, 3, 4, 5], ![0, 1, 2, 4, 3, 5], ![0, 1, 3, 2, 4, 5], ![0, 1, 3, 4, 2, 5], ![0, 1, 4, 2, 3, 5],
   ![0, 1, 4, 3, 2, 5]]

def free (x : Fin 6) : Bool := x == 2 || x == 3 || x == 4

/-- **the reduced renaming, shape (SU)**: the free colours of `x_j`, `x_k` avoid `β_j`, `β_k` -/
theorem core_su : ∀ gj gk bj bk : Fin 6,
    ∃ p ∈ perms234, (free gj = true → p gj ≠ bj) ∧ (free gk = true → p gk ≠ bk) := by
  decide +kernel

/-- **the reduced renaming, shape (S1)**: `c ↦ τ`, and one free colour `g ≠ c` avoids `b` -/
theorem core_s1 : ∀ g b c τ : Fin 6, free c = true → free τ = true → g ≠ c →
    ∃ p ∈ perms234, (free g = true → p g ≠ b) ∧ p c = τ := by
  decide +kernel

theorem perms234_spec : ∀ p ∈ perms234, (∀ x y, p x = p y → x = y) ∧ p 5 = 5 ∧ p 0 = 0 ∧ p 1 = 1 := by
  intro p hp
  simp only [perms234, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem nrm_free : ∀ A B : Fin 6, A ≠ B → A ≠ 5 → B ≠ 5 → ∀ x,
    (free (nrm A B x) = true ↔ x ≠ 5 ∧ x ≠ A ∧ x ≠ B) := by decide

theorem nrm_inj : ∀ A B : Fin 6, A ≠ B → A ≠ 5 → B ≠ 5 → ∀ x y, nrm A B x = nrm A B y → x = y := by decide

theorem nrmInv_inj : ∀ A B : Fin 6, A ≠ B → A ≠ 5 → B ≠ 5 → ∀ x y, nrmInv A B x = nrmInv A B y → x = y := by decide

theorem nrmInv_vals : ∀ A B : Fin 6, A ≠ B → A ≠ 5 → B ≠ 5 →
    nrmInv A B 5 = 5 ∧ nrmInv A B 0 = A ∧ nrmInv A B 1 = B := by decide

/-- **the renaming of Step 1, shape (SU)** -/
theorem perm_su {A B aj ak : Fin 6} (hA : A ≠ 5) (hB : B ≠ 5) (hAB : A ≠ B) (haj : aj ≠ 5) (hak : ak ≠ 5)
    (hajk : aj ≠ ak) (gj gk bj bk : Fin 6) :
    ∃ π : Fin 6 → Fin 6, (∀ x y, π x = π y → x = y) ∧ π 5 = 5 ∧ π A = aj ∧ π B = ak ∧
      ((gj ≠ 5 ∧ gj ≠ A ∧ gj ≠ B) → π gj ≠ bj) ∧ ((gk ≠ 5 ∧ gk ≠ A ∧ gk ≠ B) → π gk ≠ bk) := by
  obtain ⟨p, hp, h1, h2⟩ := core_su (nrm A B gj) (nrm A B gk) (nrm aj ak bj) (nrm aj ak bk)
  obtain ⟨pinj, p5, p0, p1⟩ := perms234_spec p hp
  obtain ⟨sA, sB, s5, sinv⟩ := nrm_spec A B hAB hA hB
  obtain ⟨ta, tb, t5, tinv⟩ := nrm_spec aj ak hajk haj hak
  obtain ⟨v5, v0, v1⟩ := nrmInv_vals aj ak hajk haj hak
  refine ⟨fun x => nrmInv aj ak (p (nrm A B x)), fun x y h => nrm_inj A B hAB hA hB _ _
    (pinj _ _ (nrmInv_inj aj ak hajk haj hak _ _ h)), by simp only [s5, p5, v5], by simp only [sA, p0, v0],
    by simp only [sB, p1, v1], fun hg e => ?_, fun hg e => ?_⟩
  · apply h1 ((nrm_free A B hAB hA hB gj).2 hg)
    rw [← e, (tinv _).2]
  · apply h2 ((nrm_free A B hAB hA hB gk).2 hg)
    rw [← e, (tinv _).2]

/-- **the renaming of Step 1, shape (S1)** -/
theorem perm_s1 {A B aj ak : Fin 6} (hA : A ≠ 5) (hB : B ≠ 5) (hAB : A ≠ B) (haj : aj ≠ 5) (hak : ak ≠ 5)
    (hajk : aj ≠ ak) (g b c τ : Fin 6) (hc : c ≠ 5 ∧ c ≠ A ∧ c ≠ B) (hτ : τ ≠ 5 ∧ τ ≠ aj ∧ τ ≠ ak) (hgc : g ≠ c) :
    ∃ π : Fin 6 → Fin 6, (∀ x y, π x = π y → x = y) ∧ π 5 = 5 ∧ π A = aj ∧ π B = ak ∧
      ((g ≠ 5 ∧ g ≠ A ∧ g ≠ B) → π g ≠ b) ∧ π c = τ := by
  obtain ⟨p, hp, h1, h2⟩ := core_s1 (nrm A B g) (nrm aj ak b) (nrm A B c) (nrm aj ak τ)
    ((nrm_free A B hAB hA hB c).2 hc) ((nrm_free aj ak hajk haj hak τ).2 hτ)
    (fun e => hgc (nrm_inj A B hAB hA hB _ _ e))
  obtain ⟨pinj, p5, p0, p1⟩ := perms234_spec p hp
  obtain ⟨sA, sB, s5, sinv⟩ := nrm_spec A B hAB hA hB
  obtain ⟨ta, tb, t5, tinv⟩ := nrm_spec aj ak hajk haj hak
  obtain ⟨v5, v0, v1⟩ := nrmInv_vals aj ak hajk haj hak
  refine ⟨fun x => nrmInv aj ak (p (nrm A B x)), fun x y h => nrm_inj A B hAB hA hB _ _
    (pinj _ _ (nrmInv_inj aj ak hajk haj hak _ _ h)), by simp only [s5, p5, v5], by simp only [sA, p0, v0],
    by simp only [sB, p1, v1], fun hg e => ?_, ?_⟩
  · apply h1 ((nrm_free A B hAB hA hB g).2 hg)
    rw [← e, (tinv _).2]
  · show nrmInv aj ak (p (nrm A B c)) = τ
    rw [h2, (tinv _).1]

end RH2F


/-
  W2.lean — facts about MC pole colourings used by Theorem W-RED (fact 1a864fdc0e0af441): invariance under an injective
  renaming of the colours fixing `6` (Lean `5`); at a port vertex `x_t` whose port edge is not of colour `6` the other
  two pole edges have colours `6` and one colour `γ_t`; properness at the port; and (Step 4) colour `6` is never
  blocking at such a port when the three port colours are distinct.
-/

namespace RH2F
open MGraph
open Classical

section wpole
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n}

theorem vPole_inc_old' (D : Ports Q v) {f : Fin Y.m} (hf : vPole D f) {u : Fin Y.n}
    (h : (splitV D).Inc f (Fin.castAdd 3 u)) : Q f ∧ Y.Inc f u := by
  by_cases hp : ∃ t, f = D.p t
  · obtain ⟨t, rfl⟩ := hp
    refine ⟨D.hp t, ?_⟩
    unfold Inc at h; rw [splitV_ends_port] at h
    rcases h with h | h
    · rw [← Fin.castAdd_injective _ _ h]; exact joins_inc_right (D.hj t)
    · exfalso; have := congrArg Fin.val h; simp at this; have := u.isLt; omega
  · have hQ : Q f := by
      rcases hf with hf | hf
      · exact hf.1
      · exact absurd hf hp
    refine ⟨hQ, ?_⟩
    unfold Inc at h; rw [splitV_ends_other D hp] at h
    rcases h with h | h
    · exact Or.inl (Fin.castAdd_injective _ _ h)
    · exact Or.inr (Fin.castAdd_injective _ _ h)

/-- a port edge meets an old vertex only at its port -/
theorem port_inc_old (D : Ports Q v) {s : Fin 3} {u : Fin Y.n} (h : (splitV D).Inc (D.p s) (Fin.castAdd 3 u)) :
    u = D.x s := by
  unfold Inc at h; rw [splitV_ends_port] at h
  rcases h with h | h
  · exact (Fin.castAdd_injective _ _ h).symm
  · exfalso; have := congrArg Fin.val h; simp at this; have := u.isLt; omega

/-- a non-port pole edge has old ends -/
theorem nonport_ends (D : Ports Q v) {f : Fin Y.m} (hp : ¬ ∃ t, f = D.p t) :
    (splitV D).ends f = (Fin.castAdd 3 (Y.ends f).1, Fin.castAdd 3 (Y.ends f).2) := splitV_ends_other D hp

theorem mcpole_comp {D : Ports Q v} {d : Fin Y.m → Fin 6} (hd : MCPole D d) {π : Fin 6 → Fin 6}
    (hπ : ∀ a b, π a = π b → a = b) (h5 : π 5 = 5) : MCPole D (fun f => π (d f)) := by
  refine ⟨starOn_comp_inj π hπ hd.1, fun x hx hxm => ?_⟩
  obtain ⟨a, ha, hax, ha5, hu⟩ := hd.2 x hx hxm
  refine ⟨a, ha, hax, by simp only [ha5, h5], fun b hb hbx hb5 => hu b hb hbx (hπ _ _ (hb5.trans h5.symm))⟩

theorem vCol_comp {D : Ports Q v} {d : Fin Y.m → Fin 6} {π : Fin 6 → Fin 6} (hπ : ∀ a b, π a = π b → a = b)
    {t : Fin 3} {κ : Fin 6} : vCol D (fun f => π (d f)) t (π κ) ↔ vCol D d t κ := by
  constructor
  · rintro ⟨f, hf, hfp, hfx, hfc⟩; exact ⟨f, hf, hfp, hfx, hπ _ _ hfc⟩
  · rintro ⟨f, hf, hfp, hfx, rfl⟩; exact ⟨f, hf, hfp, hfx, rfl⟩

theorem vCol_comp' {D : Ports Q v} {d : Fin Y.m → Fin 6} {π : Fin 6 → Fin 6} {t : Fin 3} {κ : Fin 6}
    (h : vCol D (fun f => π (d f)) t κ) : ∃ κ', vCol D d t κ' ∧ π κ' = κ := by
  obtain ⟨f, hf, hfp, hfx, rfl⟩ := h
  exact ⟨d f, ⟨f, hf, hfp, hfx, rfl⟩, rfl⟩

theorem vBlk_comp {D : Ports Q v} {d : Fin Y.m → Fin 6} {π : Fin 6 → Fin 6} (hπ : ∀ a b, π a = π b → a = b)
    {t : Fin 3} {κ : Fin 6} : vBlk D (fun f => π (d f)) t (π κ) ↔ vBlk D d t κ := by
  constructor
  · rintro ⟨f, r, hf, hfp, hj, hfc, f', hf', hf'f, hf'r, hc'⟩
    exact ⟨f, r, hf, hfp, hj, hπ _ _ hfc, f', hf', hf'f, hf'r, hπ _ _ hc'⟩
  · rintro ⟨f, r, hf, hfp, hj, rfl, f', hf', hf'f, hf'r, hc'⟩
    exact ⟨f, r, hf, hfp, hj, rfl, f', hf', hf'f, hf'r, by simp only [hc']⟩

theorem vBlk_comp' {D : Ports Q v} {d : Fin Y.m → Fin 6} {π : Fin 6 → Fin 6} {t : Fin 3} {κ : Fin 6}
    (hπ : ∀ a b, π a = π b → a = b) (h : vBlk D (fun f => π (d f)) t κ) : ∃ κ', vBlk D d t κ' ∧ π κ' = κ := by
  obtain ⟨f, r, hf, hfp, hj, rfl, f', hf', hf'f, hf'r, hc'⟩ := h
  exact ⟨d f, ⟨f, r, hf, hfp, hj, rfl, f', hf', hf'f, hf'r, hπ _ _ hc'⟩, rfl⟩

/-- the port vertex `x t` is an old vertex other than `v` meeting `Q` -/
theorem x_ne_v (hloop : Loopless Y) (D : Ports Q v) (t : Fin 3) : D.x t ≠ v := fun h =>
  ne_of_joins' hloop (D.hj t) h.symm

theorem port_inc_x (D : Ports Q v) (t : Fin 3) : (splitV D).Inc (D.p t) (Fin.castAdd 3 (D.x t)) := by
  unfold Inc; rw [splitV_ends_port]; exact Or.inl rfl

/-- **properness at the port** -/
theorem port_proper {D : Ports Q v} {d : Fin Y.m → Fin 6} (hd : MCPole D d) (t : Fin 3) :
    ¬ vCol D d t (d (D.p t)) := by
  rintro ⟨f, hf, hfp, hfx, hfc⟩
  exact hd.1.1 f (D.p t) ⟨hfp, _, hfx, port_inc_x D t⟩ hf (Or.inr ⟨t, rfl⟩) hfc

/-- **the colours at a port vertex**: if `d(p_t) ≠ 6`, then `Col_t(d) = {6, γ}` for a colour `γ ≠ 6, d(p_t)` -/
theorem col_two (hG : InG Y Q) {D : Ports Q v} {d : Fin Y.m → Fin 6} (hd : MCPole D d) {t : Fin 3}
    (h5 : d (D.p t) ≠ 5) : ∃ γ, γ ≠ 5 ∧ γ ≠ d (D.p t) ∧ ∀ κ, vCol D d t κ ↔ κ = 5 ∨ κ = γ := by
  have hxm : meets Q (D.x t) := ⟨D.p t, D.hp t, joins_inc_right (D.hj t)⟩
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hG.2.2.2 (D.x t) hxm
  -- the pole edges at `x t` other than `p t` are the two other `Q`-edges at `x t`
  have other : ∀ f, Q f → Y.Inc f (D.x t) → f ≠ D.p t → vPole D f ∧ ¬ (∃ s, f = D.p s) := by
    intro f hf hfx hne
    have hnp : ¬ ∃ s, f = D.p s := by
      rintro ⟨s, rfl⟩
      have : D.x s = D.x t ∨ v = D.x t := by
        rcases inc_of_joins (D.hj s) hfx with h | h
        · exact Or.inr h.symm
        · exact Or.inl h.symm
      rcases this with h | h
      · exact hne (by rw [D.xinj _ _ h])
      · exact x_ne_v hG.1 D t h.symm
    refine ⟨Or.inl ⟨hf, fun hv => hnp ?_⟩, hnp⟩
    obtain ⟨s, hs⟩ := D.all f hf hv
    exact ⟨s, hs⟩
  have incS : ∀ f, ¬ (∃ s, f = D.p s) → Y.Inc f (D.x t) → (splitV D).Inc f (Fin.castAdd 3 (D.x t)) := by
    intro f hnp hfx
    unfold Inc; rw [nonport_ends D hnp]
    rcases hfx with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the two other edges `f1`, `f2`
  obtain ⟨f1, f2, hf1, hf2, i1, i2, n1, n2, n12⟩ : ∃ f1 f2, Q f1 ∧ Q f2 ∧ Y.Inc f1 (D.x t) ∧ Y.Inc f2 (D.x t) ∧
      f1 ≠ D.p t ∧ f2 ≠ D.p t ∧ f1 ≠ f2 := by
    rcases hall (D.p t) (D.hp t) (joins_inc_right (D.hj t)) with h | h | h
    · exact ⟨q, r, hq, hr, iq, ir, fun e => dpq (e.trans h).symm, fun e => dpr (e.trans h).symm, dqr⟩
    · exact ⟨p, r, hp, hr, ip, ir, fun e => dpq (e.trans h), fun e => dqr (e.trans h).symm, dpr⟩
    · exact ⟨p, q, hp, hq, ip, iq, fun e => dpr (e.trans h), fun e => dqr (e.trans h), dpq⟩
  have all3 : ∀ f, Q f → Y.Inc f (D.x t) → f = D.p t ∨ f = f1 ∨ f = f2 :=
    RH2F.cubic_exact hG.2.2.2 (D.hp t) hf1 hf2 (joins_inc_right (D.hj t)) i1 i2 (Ne.symm n1) (Ne.symm n2) n12
  obtain ⟨o1, np1⟩ := other f1 hf1 i1 n1
  obtain ⟨o2, np2⟩ := other f2 hf2 i2 n2
  have s1 := incS f1 np1 i1
  have s2 := incS f2 np2 i2
  -- the colour-`6` edge at `x t`
  obtain ⟨a, ha, hax, ha5, hau⟩ := hd.2 (D.x t) (x_ne_v hG.1 D t) hxm
  have hcol : ∀ κ, vCol D d t κ ↔ κ = d f1 ∨ κ = d f2 := by
    intro κ
    constructor
    · rintro ⟨f, hf, hfp, hfx, rfl⟩
      obtain ⟨hfQ, hfY⟩ := vPole_inc_old' D hf hfx
      rcases all3 f hfQ hfY with h | h | h
      · exact absurd h hfp
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · rintro (rfl | rfl)
      · exact ⟨f1, o1, n1, s1, rfl⟩
      · exact ⟨f2, o2, n2, s2, rfl⟩
  have hprop : d f1 ≠ d f2 := hd.1.1 f1 f2 ⟨n12, _, s1, s2⟩ o1 o2
  obtain ⟨haQ, haY⟩ := vPole_inc_old' D ha hax
  rcases all3 a haQ haY with h | h | h
  · exact absurd (h ▸ ha5) h5
  · subst h
    refine ⟨d f2, fun e => hau f2 o2 s2 e |> fun h => n12 h.symm, ?_, fun κ => by rw [hcol, ha5]⟩
    exact fun e => hd.1.1 f2 (D.p t) ⟨n2, _, s2, port_inc_x D t⟩ o2 (Or.inr ⟨t, rfl⟩) e
  · subst h
    refine ⟨d f1, fun e => hau f1 o1 s1 e |> fun h => n12 h, ?_, fun κ => by rw [hcol, ha5]; exact Or.comm⟩
    exact fun e => hd.1.1 f1 (D.p t) ⟨n1, _, s1, port_inc_x D t⟩ o1 (Or.inr ⟨t, rfl⟩) e


theorem splitV_loopless (hloop : Loopless Y) (D : Ports Q v) : Loopless (splitV D) := by
  intro f
  by_cases hp : ∃ t, f = D.p t
  · obtain ⟨t, rfl⟩ := hp
    rw [splitV_ends_port]
    intro h; have := congrArg Fin.val h; simp at this; have := (D.x t).isLt; omega
  · rw [nonport_ends D hp]
    intro h; exact hloop f (Fin.castAdd_injective _ _ h)

theorem castAdd_ne_natAdd' (a : Fin Y.n) (t : Fin 3) : (Fin.castAdd 3 a : Fin (Y.n + 3)) ≠ Fin.natAdd Y.n t := by
  intro h; have := congrArg Fin.val h; simp at this; have := a.isLt; omega

/-- a pole edge at an old vertex `castAdd u` that is not a port joins `castAdd u` to an old vertex `castAdd u'` with
    `Y.Joins f u u'` -/
theorem nonport_joins (D : Ports Q v) {f : Fin Y.m} (hp : ¬ ∃ t, f = D.p t) {u : Fin Y.n} {r : Fin (splitV D).n}
    (h : (splitV D).Joins f (Fin.castAdd 3 u) r) : ∃ u', r = Fin.castAdd 3 u' ∧ Y.Joins f u u' := by
  have he := nonport_ends D hp
  rcases h with h | h <;> rw [he] at h <;> simp only [Prod.mk.injEq] at h
  · exact ⟨(Y.ends f).2, h.2.symm, Or.inl (by rw [← Fin.castAdd_injective _ _ h.1])⟩
  · exact ⟨(Y.ends f).1, h.1.symm, Or.inr (by rw [← Fin.castAdd_injective _ _ h.2])⟩

/-- **Step 4 of W-RED**: if the three port colours are distinct and `d(p_t) ≠ 6`, colour `6` is not blocking at
    `x_t` -/
theorem noBlk5 (hloop : Loopless Y) {D : Ports Q v} {d : Fin Y.m → Fin 6} (hd : MCPole D d)
    (hport : ∀ s u, d (D.p s) = d (D.p u) → s = u) {t : Fin 3} (h5 : d (D.p t) ≠ 5) : ¬ vBlk D d t 5 := by
  rintro ⟨f, r, hf, hfp, hj, hf5, f', hf', hf'f, hf'r, hc'⟩
  have hsl := splitV_loopless hloop D
  -- `f` is not a port
  have hfnp : ¬ ∃ s, f = D.p s := by
    rintro ⟨s, rfl⟩
    have := port_inc_old D (joins_inc_left hj)
    exact hfp (by rw [D.xinj _ _ this.symm])
  obtain ⟨ρ, rfl, hjY⟩ := nonport_joins D hfnp hj
  have hρx : ρ ≠ D.x t := fun h => hloop f (by
    rcases hjY with h' | h' <;> rw [h'] <;> simp [h])
  have hfQ : Q f ∧ ¬ Y.Inc f v := by
    rcases hf with h | h
    · exact h
    · exact absurd h hfnp
  have hρv : ρ ≠ v := fun h => hfQ.2 (by rw [← h]; exact joins_inc_right hjY)
  -- `f'` is not a port
  have hf'np : ¬ ∃ s, f' = D.p s := by
    rintro ⟨s, rfl⟩
    have hs := port_inc_old D hf'r
    rw [hport _ _ hc'] at hs
    exact hρx hs
  obtain ⟨hf'Q, hf'Y⟩ := vPole_inc_old' D hf' hf'r
  obtain ⟨σ, hσ⟩ : ∃ σ, Y.Joins f' ρ σ := ⟨other f' ρ, joins_other hf'Y⟩
  have hf'Qv : ¬ Y.Inc f' v := by
    rcases hf' with h | h
    · exact h.2
    · exact absurd h hf'np
  have hσv : σ ≠ v := fun h => hf'Qv (by rw [← h]; exact joins_inc_right hσ)
  have hσρ : σ ≠ ρ := fun h => hloop f' (by rcases hσ with h' | h' <;> rw [h'] <;> simp [h])
  have hjs' : (splitV D).Joins f' (Fin.castAdd 3 ρ) (Fin.castAdd 3 σ) := by
    rcases hσ with h | h
    · exact Or.inl (by rw [nonport_ends D hf'np, h])
    · exact Or.inr (by rw [nonport_ends D hf'np, h])
  have hσx : σ ≠ D.x t := by
    intro h
    apply port_proper hd t
    exact ⟨f', hf', fun e => hf'np ⟨t, e⟩, by rw [← h]; exact joins_inc_right hjs', hc'⟩
  -- the colour-`6` edge at `σ`
  have hσm : meets Q σ := ⟨f', hf'Q, joins_inc_right hσ⟩
  obtain ⟨g', hg', hg'σ, hg'5, _⟩ := hd.2 σ hσv hσm
  obtain ⟨w, hw⟩ : ∃ w, (splitV D).Joins g' (Fin.castAdd 3 σ) w := ⟨other g' _, joins_other hg'σ⟩
  have hwσ : w ≠ Fin.castAdd 3 σ := fun h => ne_of_joins' hsl hw h.symm
  have hρm : meets Q ρ := ⟨f, hfQ.1, joins_inc_right hjY⟩
  have hxm : meets Q (D.x t) := ⟨D.p t, D.hp t, joins_inc_right (D.hj t)⟩
  obtain ⟨a5, _, _, _, hu5⟩ := hd.2 ρ hρv hρm
  obtain ⟨b5, _, _, _, hv5⟩ := hd.2 (D.x t) (x_ne_v hloop D t) hxm
  have hwρ : w ≠ Fin.castAdd 3 ρ := by
    intro h
    rw [h] at hw
    have e1 := hu5 g' hg' (joins_inc_right hw) hg'5
    have e2 := hu5 f hf (joins_inc_right hj) hf5
    have hgf : g' = f := e1.trans e2.symm
    subst hgf
    rcases joins_unique hw hj with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hσx (Fin.castAdd_injective _ _ h1)
    · exact hσρ (Fin.castAdd_injective _ _ h1)
  have hwx : w ≠ Fin.castAdd 3 (D.x t) := by
    intro h
    rw [h] at hw
    have e1 := hv5 g' hg' (joins_inc_right hw) hg'5
    have e2 := hv5 f hf (joins_inc_left hj) hf5
    have hgf : g' = f := e1.trans e2.symm
    subst hgf
    rcases joins_unique hw hj with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hσx (Fin.castAdd_injective _ _ h1)
    · exact hσρ (Fin.castAdd_injective _ _ h1)
  have hwo : w ≠ Fin.natAdd Y.n t := by
    intro h
    rw [h] at hw
    by_cases hp : ∃ s, g' = D.p s
    · obtain ⟨s, rfl⟩ := hp
      simp only [MGraph.Joins] at hw
      rw [splitV_ends_port] at hw
      rcases hw with h' | h' <;> simp only [Prod.mk.injEq] at h'
      · have := Fin.natAdd_injective _ _ h'.2; subst this; exact h5 hg'5
      · exact castAdd_ne_natAdd' _ _ h'.1
    · simp only [MGraph.Joins] at hw
      rw [nonport_ends D hp] at hw
      rcases hw with h' | h' <;> simp only [Prod.mk.injEq] at h'
      · exact castAdd_ne_natAdd' _ _ h'.2
      · exact castAdd_ne_natAdd' _ _ h'.1
  let W : (splitV D).Walk4 :=
    { v0 := Fin.natAdd Y.n t, v1 := Fin.castAdd 3 (D.x t), v2 := Fin.castAdd 3 ρ, v3 := Fin.castAdd 3 σ, v4 := w,
      e1 := D.p t, e2 := f, e3 := f', e4 := g'
      h1 := Or.inr (splitV_ends_port D t)
      h2 := hj
      h3 := hjs'
      h4 := hw
      d01 := fun h => castAdd_ne_natAdd' _ _ h.symm
      d02 := fun h => castAdd_ne_natAdd' _ _ h.symm
      d03 := fun h => castAdd_ne_natAdd' _ _ h.symm
      d12 := fun h => hρx (Fin.castAdd_injective _ _ h).symm
      d13 := fun h => hσx (Fin.castAdd_injective _ _ h).symm
      d14 := fun h => hwx h.symm
      d23 := fun h => hσρ (Fin.castAdd_injective _ _ h).symm
      d24 := fun h => hwρ h.symm
      d34 := fun h => hwσ h.symm }
  exact hd.1.2 W (Or.inr ⟨t, rfl⟩) hf hf' hg' ⟨hc'.symm, by show d f = d g'; rw [hf5, hg'5]⟩

end wpole

end RH2F


/-
  W3.lean — **Lemma W-SUFF and Theorem W-RED** (fact 1a864fdc0e0af441): a W-colouring of a pole at M-port `i`
  serves every admissible outside datum at `i` after a renaming of the colours fixing `6` (Lean `5`), with the same
  colour class `6`; hence W-colourings at every port give (D1), W-colourings with prescribed status give (D2), and
  the boundary-extension hypothesis (W-EXT) implies (POLE).
-/

namespace RH2F
open MGraph
open Classical

section wred
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n}

/-- a **W-colouring** of the pole at M-port `i` (`{j, k}` the other ports): an MC pole colouring with `d(p_i) = 6`,
    `A := d(p_j)`, `B := d(p_k)` distinct colours other than `6`; (W0) `B ∉ Blk_j(d)` and `A ∉ Blk_k(d)`; and shape
    (SU) `Col_i(d) = {A, B}` or shape (S1) `Col_i(d) = {A, c}` or `{B, c}` for a colour `c ∉ {6, A, B}` with
    `c ∉ Col_j(d)`, `c ∉ Col_k(d)`, and not both `Col_j(d)` and `Col_k(d)` meeting `{1,…,5} ∖ {A, B}` -/
def WCol (D : Ports Q v) (i j k : Fin 3) (d : Fin Y.m → Fin 6) : Prop :=
  MCPole D d ∧ d (D.p i) = 5 ∧ d (D.p j) ≠ 5 ∧ d (D.p k) ≠ 5 ∧ d (D.p j) ≠ d (D.p k) ∧
  ¬ vBlk D d j (d (D.p k)) ∧ ¬ vBlk D d k (d (D.p j)) ∧
  ((∀ κ, vCol D d i κ ↔ κ = d (D.p j) ∨ κ = d (D.p k)) ∨
   ∃ c, c ≠ 5 ∧ c ≠ d (D.p j) ∧ c ≠ d (D.p k) ∧
     ((∀ κ, vCol D d i κ ↔ κ = d (D.p j) ∨ κ = c) ∨ (∀ κ, vCol D d i κ ↔ κ = d (D.p k) ∨ κ = c)) ∧
     ¬ vCol D d j c ∧ ¬ vCol D d k c ∧
     ¬ ((∃ κ, κ ≠ 5 ∧ κ ≠ d (D.p j) ∧ κ ≠ d (D.p k) ∧ vCol D d j κ) ∧
        (∃ κ, κ ≠ 5 ∧ κ ≠ d (D.p j) ∧ κ ≠ d (D.p k) ∧ vCol D d k κ)))

/-- compatibility of a renamed colouring, from the renaming conditions at `j`, `k` and a condition at `i` -/
theorem compat_of_perm (hG : InG Y Q) {D : Ports Q v} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {d : Fin Y.m → Fin 6} (hd : MCPole D d) (hdi : d (D.p i) = 5) (hA5 : d (D.p j) ≠ 5) (hB5 : d (D.p k) ≠ 5)
    (hAB : d (D.p j) ≠ d (D.p k)) (hW0j : ¬ vBlk D d j (d (D.p k))) (hW0k : ¬ vBlk D d k (d (D.p j)))
    {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop} (hadm : Admissible i a O B)
    {γj γk βj βk : Fin 6} (hCj : ∀ κ, vCol D d j κ ↔ κ = 5 ∨ κ = γj) (hCk : ∀ κ, vCol D d k κ ↔ κ = 5 ∨ κ = γk)
    (hγjA : γj ≠ d (D.p j)) (hγkB : γk ≠ d (D.p k)) (hγj5 : γj ≠ 5) (hγk5 : γk ≠ 5)
    (hOj : ∀ κ, O j κ ↔ κ = 5 ∨ κ = βj) (hOk : ∀ κ, O k κ ↔ κ = 5 ∨ κ = βk)
    {π : Fin 6 → Fin 6} (hπ : ∀ x y, π x = π y → x = y) (hπ5 : π 5 = 5) (hπA : π (d (D.p j)) = a j)
    (hπB : π (d (D.p k)) = a k)
    (hP1j : (γj ≠ 5 ∧ γj ≠ d (D.p j) ∧ γj ≠ d (D.p k)) → π γj ≠ βj)
    (hP1k : (γk ≠ 5 ∧ γk ≠ d (D.p j) ∧ γk ≠ d (D.p k)) → π γk ≠ βk)
    (hport : ∀ κ, vCol D d i κ → ¬ O i (π κ)) :
    Compat D (fun f => π (d f)) a O B := by
  obtain ⟨ha_inj, hai, _, _, _, _, hO2, _⟩ := hadm
  have hports : ∀ s u, d (D.p s) = d (D.p u) → s = u := by
    have hv : ∀ s, s = i ∨ s = j ∨ s = k := fun s => fin3_cases i j k s hij hik hjk
    intro s u h
    rcases hv s with rfl | rfl | rfl <;> rcases hv u with rfl | rfl | rfl
    all_goals first
      | rfl
      | (exfalso; first
          | exact hA5 (h.symm.trans hdi) | exact hA5 (h.trans hdi) | exact hB5 (h.symm.trans hdi)
          | exact hB5 (h.trans hdi) | exact hAB h | exact hAB h.symm)
  have blk5 : ∀ t, d (D.p t) ≠ 5 → ¬ vBlk D (fun f => π (d f)) t 5 := by
    intro t ht hb
    obtain ⟨κ, hκ, hκ5⟩ := vBlk_comp' hπ hb
    have : κ = 5 := hπ _ _ (hκ5.trans hπ5.symm)
    subst this
    exact noBlk5 hG.1 hd hports ht hκ
  refine ⟨fun t => ?_, fun t κ' hcol hO hB => ?_⟩
  · rcases fin3_cases i j k t hij hik hjk with rfl | rfl | rfl
    · show π (d (D.p t)) = a t; rw [hdi, hπ5, hai]
    · exact hπA
    · exact hπB
  obtain ⟨κ, hκ, rfl⟩ := vCol_comp' hcol
  rcases fin3_cases i j k t hij hik hjk with rfl | rfl | rfl
  · exact hport κ hκ hO
  · rcases (hCj κ).1 hκ with rfl | rfl
    · rw [hπ5] at hB
      rcases hB with hB | hB
      · exact blk5 t hA5 hB
      · exact ((hO2 t (Ne.symm hij)).2.2 5 hB).1 rfl
    · rcases (hOj _).1 hO with h | h
      · exact hγj5 (hπ _ _ (h.trans hπ5.symm))
      · by_cases hfree : κ ≠ 5 ∧ κ ≠ d (D.p t) ∧ κ ≠ d (D.p k)
        · exact hP1j hfree h
        · have hκB : κ = d (D.p k) := Classical.byContradiction fun hne => hfree ⟨hγj5, hγjA, hne⟩
          subst hκB
          rw [hπB] at hB h
          rcases hB with hB | hB
          · rw [← hπB] at hB; exact hW0j ((vBlk_comp hπ).1 hB)
          · exact ((hO2 t (Ne.symm hij)).2.2 _ hB).2 k (Ne.symm hik) rfl
  · rcases (hCk κ).1 hκ with rfl | rfl
    · rw [hπ5] at hB
      rcases hB with hB | hB
      · exact blk5 t hB5 hB
      · exact ((hO2 t (Ne.symm hik)).2.2 5 hB).1 rfl
    · rcases (hOk _).1 hO with h | h
      · exact hγk5 (hπ _ _ (h.trans hπ5.symm))
      · by_cases hfree : κ ≠ 5 ∧ κ ≠ d (D.p j) ∧ κ ≠ d (D.p t)
        · exact hP1k hfree h
        · have hκA : κ = d (D.p j) := Classical.byContradiction fun hne => hfree ⟨hγk5, hne, hγkB⟩
          subst hκA
          rw [hπA] at hB h
          rcases hB with hB | hB
          · rw [← hπA] at hB; exact hW0k ((vBlk_comp hπ).1 hB)
          · exact ((hO2 t (Ne.symm hik)).2.2 _ hB).2 j (Ne.symm hij) rfl

/-- **W-RED (a)**: a W-colouring at `i`, renamed, is compatible with every admissible datum at `i`, with the same
    colour class `6` -/
theorem wred_a (hG : InG Y Q) {D : Ports Q v} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {d : Fin Y.m → Fin 6} (hW : WCol D i j k d) {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop}
    (hadm : Admissible i a O B) :
    ∃ d', MCPole D d' ∧ Compat D d' a O B ∧ ∀ g, (d' g = 5 ↔ d g = 5) := by
  obtain ⟨hd, hdi, hA5, hB5, hAB, hW0j, hW0k, hshape⟩ := hW
  have hadm' := hadm
  obtain ⟨ha_inj, hai, hTwo, _, hO1, _, hO2, _⟩ := hadm'
  have haj5 : a j ≠ 5 := fun h => hij (ha_inj _ _ (hai.trans h.symm))
  have hak5 : a k ≠ 5 := fun h => hik (ha_inj _ _ (hai.trans h.symm))
  have hajk : a j ≠ a k := fun h => hjk (ha_inj _ _ h)
  obtain ⟨o1, o2, ho12, hOi⟩ := hTwo i
  have ho1 := hO1 o1 ((hOi o1).2 (Or.inl rfl))
  have ho2 := hO1 o2 ((hOi o2).2 (Or.inr rfl))
  obtain ⟨τ, hτ5, hτj, hτk, hτ1, hτ2⟩ := fifth_colour (a j) (a k) o1 o2 haj5 hak5 ho1.1 ho2.1 hajk
    (Ne.symm (ho1.2 j (Ne.symm hij))) (Ne.symm (ho2.2 j (Ne.symm hij))) (Ne.symm (ho1.2 k (Ne.symm hik)))
    (Ne.symm (ho2.2 k (Ne.symm hik))) ho12
  obtain ⟨βj, _, hOj⟩ := two_with5 (hTwo j) (hO2 j (Ne.symm hij)).1
  obtain ⟨βk, _, hOk⟩ := two_with5 (hTwo k) (hO2 k (Ne.symm hik)).1
  obtain ⟨γj, hγj5, hγjA, hCj⟩ := col_two hG hd hA5
  obtain ⟨γk, hγk5, hγkB, hCk⟩ := col_two hG hd hB5
  have notOi : ∀ κ, O i κ → κ ≠ a j ∧ κ ≠ a k := fun κ h =>
    ⟨(hO1 κ h).2 j (Ne.symm hij), (hO1 κ h).2 k (Ne.symm hik)⟩
  have tauOi : ¬ O i τ := by
    intro h
    rcases (hOi τ).1 h with e | e
    · exact hτ1 e
    · exact hτ2 e
  have fin : ∀ {π : Fin 6 → Fin 6}, (∀ x y, π x = π y → x = y) → π 5 = 5 → π (d (D.p j)) = a j →
      π (d (D.p k)) = a k → ((γj ≠ 5 ∧ γj ≠ d (D.p j) ∧ γj ≠ d (D.p k)) → π γj ≠ βj) →
      ((γk ≠ 5 ∧ γk ≠ d (D.p j) ∧ γk ≠ d (D.p k)) → π γk ≠ βk) → (∀ κ, vCol D d i κ → ¬ O i (π κ)) →
      ∃ d', MCPole D d' ∧ Compat D d' a O B ∧ ∀ g, (d' g = 5 ↔ d g = 5) := by
    intro π hπ hπ5 hπA hπB h1 h2 hp
    refine ⟨fun f => π (d f), mcpole_comp hd hπ hπ5,
      compat_of_perm hG hij hik hjk hd hdi hA5 hB5 hAB hW0j hW0k hadm hCj hCk hγjA hγkB hγj5 hγk5 hOj hOk
        hπ hπ5 hπA hπB h1 h2 hp, fun g => ⟨fun h => hπ _ _ (h.trans hπ5.symm), fun h => by simp only [h, hπ5]⟩⟩
  rcases hshape with hSU | ⟨c, hc5, hcA, hcB, hci, hcj, hck, hboth⟩
  · obtain ⟨π, hπ, h5, hA', hB', h1, h2⟩ := perm_su hA5 hB5 hAB haj5 hak5 hajk γj γk βj βk
    refine fin hπ h5 hA' hB' h1 h2 (fun κ hκ hO => ?_)
    rcases (hSU κ).1 hκ with rfl | rfl
    · rw [hA'] at hO; exact (notOi _ hO).1 rfl
    · rw [hB'] at hO; exact (notOi _ hO).2 rfl
  · have hγjc : γj ≠ c := fun e => hcj ((hCj c).2 (Or.inr e.symm))
    have hγkc : γk ≠ c := fun e => hck ((hCk c).2 (Or.inr e.symm))
    have porti : ∀ {π : Fin 6 → Fin 6}, π (d (D.p j)) = a j → π (d (D.p k)) = a k → π c = τ →
        ∀ κ, vCol D d i κ → ¬ O i (π κ) := by
      intro π hA' hB' hc κ hκ hO
      rcases hci with h | h <;> rcases (h κ).1 hκ with rfl | rfl
      · rw [hA'] at hO; exact (notOi _ hO).1 rfl
      · rw [hc] at hO; exact tauOi hO
      · rw [hB'] at hO; exact (notOi _ hO).2 rfl
      · rw [hc] at hO; exact tauOi hO
    by_cases hjf : γj ≠ 5 ∧ γj ≠ d (D.p j) ∧ γj ≠ d (D.p k)
    · have hkf : ¬ (γk ≠ 5 ∧ γk ≠ d (D.p j) ∧ γk ≠ d (D.p k)) := fun hk => hboth
        ⟨⟨γj, hjf.1, hjf.2.1, hjf.2.2, (hCj γj).2 (Or.inr rfl)⟩, ⟨γk, hk.1, hk.2.1, hk.2.2, (hCk γk).2 (Or.inr rfl)⟩⟩
      obtain ⟨π, hπ, h5, hA', hB', h1, h2⟩ := perm_s1 hA5 hB5 hAB haj5 hak5 hajk γj βj c τ ⟨hc5, hcA, hcB⟩
        ⟨hτ5, hτj, hτk⟩ hγjc
      exact fin hπ h5 hA' hB' h1 (fun hk => absurd hk hkf) (porti hA' hB' h2)
    · obtain ⟨π, hπ, h5, hA', hB', h1, h2⟩ := perm_s1 hA5 hB5 hAB haj5 hak5 hajk γk βk c τ ⟨hc5, hcA, hcB⟩
        ⟨hτ5, hτj, hτk⟩ hγkc
      exact fin hπ h5 hA' hB' (fun hj => absurd hj hjf) h1 (porti hA' hB' h2)

/-- **W-RED (b)**, (D1): W-colourings at every port give (D1) at every port -/
theorem wred_d1 (hG : InG Y Q) {D : Ports Q v} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hW : ∃ d, WCol D i j k d) : D1 D i := by
  intro a O B hadm
  obtain ⟨d, hd⟩ := hW
  obtain ⟨d', hd', hc, _⟩ := wred_a hG hij hik hjk hd hadm
  exact ⟨d', hd', hc⟩

/-- **W-RED (b)**, (D2): for an edge `g` and status `s`, a W-colouring at some port `i` with `[d(g) = 6] = s` makes
    `i` witness (D2) for `(g, s)` -/
theorem wred_d2 (hG : InG Y Q) {D : Ports Q v} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {g : Fin Y.m} {s : Bool} (hW : ∃ d, WCol D i j k d ∧ (d g = 5 ↔ s = true)) :
    ∀ a O B, Admissible i a O B → ∃ d, MCPole D d ∧ Compat D d a O B ∧ (d g = 5 ↔ s = true) := by
  intro a O B hadm
  obtain ⟨d, hd, hst⟩ := hW
  obtain ⟨d', hd', hc, h5⟩ := wred_a hG hij hik hjk hd hadm
  exact ⟨d', hd', hc, (h5 g).trans hst⟩

end wred

theorem fin3_others : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide

/-- (W-EXT) (fact 1a864fdc0e0af441 (c)): for every 2-cut-reduced member of 𝒢 with at least 10 vertices and every
    vertex `v` with three distinct neighbours (a labelling `D` of its ports), the pole `Q(X, v)` has a W-colouring at
    every M-port, and for every edge `g` of `X − v` and every status `s` a W-colouring at some M-port with
    `[d(g) = 6] = s` -/
def WEXT : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P →
    ∀ (v : Fin X.n) (D : Ports P v),
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ d, WCol D i j k d) ∧
      (∀ g, P g → ¬ X.Inc g v → ∀ s : Bool,
        ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ∃ d, WCol D i j k d ∧ (d g = 5 ↔ s = true))

/-- **W-RED (c)**: (W-EXT) implies (POLE) -/
theorem wred_c (hW : WEXT) : POLE := by
  intro X P hG h10 h2 v D
  obtain ⟨h1, h2'⟩ := hW X P hG h10 h2 v D
  refine ⟨fun i => ?_, fun g hg hgv s => ?_⟩
  · obtain ⟨j, k, hij, hik, hjk⟩ := fin3_others i
    exact wred_d1 hG hij hik hjk (h1 i j k hij hik hjk)
  · obtain ⟨i, j, k, hij, hik, hjk, hd⟩ := h2' g hg hgv s
    exact ⟨i, wred_d2 hG hij hik hjk hd⟩

end RH2F

namespace RH2F
open MGraph

/-- **layer 24 of the Lean formalization**: Lemma W-SUFF and Theorem W-RED (fact 1a864fdc0e0af441) — a W-colouring
    at an M-port serves every admissible outside datum there after renaming the colours, so W-colourings give (D1)
    and (D2), and (W-EXT) implies (POLE); hence Theorem ROOT-CS4 (fact 6010cb59aaf31d7a) with (W-EXT) in place of
    (POLE) -/
theorem layer24 :
    (∀ (Y : MGraph) (Q : Fin Y.m → Prop) (v : Fin Y.n) (D : Ports Q v) (i j k : Fin 3) (d : Fin Y.m → Fin 6),
      InG Y Q → i ≠ j → i ≠ k → j ≠ k → WCol D i j k d → ∀ a O B, Admissible i a O B →
      ∃ d', MCPole D d' ∧ Compat D d' a O B ∧ ∀ g, (d' g = 5 ↔ d g = 5)) ∧
    (WEXT → POLE) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD →
      FEEXTD10 → FEEXISTD10 → WEXT → TDTRI → IID → DMS) :=
  ⟨fun _ _ _ _ _ _ _ _ hG hij hik hjk hW _ _ _ hadm => wred_a hG hij hik hjk hW hadm, wred_c,
   fun hB12 hS14 hB14 hSH hPD hext hex hW htd hD => rootcs4 hB12 hS14 hB14 hSH hPD hext hex (wred_c hW) htd hD⟩

end RH2F
