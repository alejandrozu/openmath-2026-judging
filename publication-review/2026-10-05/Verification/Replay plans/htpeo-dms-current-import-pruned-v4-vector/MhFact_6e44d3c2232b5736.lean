-- Lean proof of fact 6e44d3c2232b5736 (RH2F.layer6b); added by fact_submit, do not edit
import MhFact_09796da8a434e150

-- ===== from CL.lean =====

namespace RH2F
open MGraph Finset
open Classical

section cls
variable {X : MGraph} {P : Fin X.m → Prop}

/-- an isomorphism onto a multigraph without isolated vertices preserves the number of vertices -/
theorem vcount_iso {H : MGraph} (h : IsoFrom P H) (hH : ∀ p : Fin H.n, ∃ e, H.Inc e p) : vcount P = H.n := by
  obtain ⟨α, β, hα, _, hs, hj⟩ := h
  rw [vcount_eq_card]
  have himg : (univ.filter (meets P)).image α = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨e, he⟩ := hH p
    obtain ⟨f, hf, rfl⟩ := hs e
    have hjf := hj f hf
    rw [mem_image]
    rcases inc_of_joins hjf he with h1 | h1
    · exact ⟨(X.ends f).1, by simp [meets]; exact ⟨f, hf, Or.inl rfl⟩, h1.symm⟩
    · exact ⟨(X.ends f).2, by simp [meets]; exact ⟨f, hf, Or.inr rfl⟩, h1.symm⟩
  rw [← card_image_of_injOn (f := α) (fun x hx y hy hxy => hα x y (by simpa using hx) (by simpa using hy) hxy),
    himg, card_univ, Fintype.card_fin]

/-- an isomorphism from a simple `P` excludes parallel edges in the target -/
theorem simple_of_iso {H : MGraph} (h : IsoFrom P H) (hS : SimpleP P) {p q : Fin H.m} (hpq : p ≠ q)
    (hpar : H.ends p = H.ends q ∨ H.ends p = ((H.ends q).2, (H.ends q).1)) : False := by
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := h
  obtain ⟨f, hf, rfl⟩ := hs p
  obtain ⟨g, hg, rfl⟩ := hs q
  have hfg : f ≠ g := fun e => hpq (by rw [e])
  have jf := hj f hf
  have jg := hj g hg
  have mf1 : meets P (X.ends f).1 := ⟨f, hf, Or.inl rfl⟩
  have mf2 : meets P (X.ends f).2 := ⟨f, hf, Or.inr rfl⟩
  have mg1 : meets P (X.ends g).1 := ⟨g, hg, Or.inl rfl⟩
  have mg2 : meets P (X.ends g).2 := ⟨g, hg, Or.inr rfl⟩
  have key : (α (X.ends f).1 = α (X.ends g).1 ∧ α (X.ends f).2 = α (X.ends g).2) ∨
      (α (X.ends f).1 = α (X.ends g).2 ∧ α (X.ends f).2 = α (X.ends g).1) := by
    rcases hpar with hp | hp <;> rcases jf with h1 | h1 <;> rcases jg with h2 | h2 <;>
      rw [h1, h2] at hp <;> simp only [Prod.mk.injEq] at hp
    · exact Or.inl hp
    · exact Or.inr hp
    · exact Or.inr ⟨hp.2, hp.1⟩
    · exact Or.inl ⟨hp.2, hp.1⟩
    · exact Or.inr hp
    · exact Or.inl hp
    · exact Or.inl ⟨hp.2, hp.1⟩
    · exact Or.inr ⟨hp.2, hp.1⟩
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · have e1 := hα _ _ mf1 mg1 k1
    have e2 := hα _ _ mf2 mg2 k2
    exact hfg (hS f g _ _ hf hg (joins_ends f) (by rw [e1, e2]; exact joins_ends g))
  · have e1 := hα _ _ mf1 mg2 k1
    have e2 := hα _ _ mf2 mg1 k2
    exact hfg (hS f g _ _ hf hg (joins_ends f) (by rw [e1, e2]; exact Or.symm (joins_ends g)))

/-- the base case: a member of 𝒢 with two vertices is the triple edge `Rep01` -/
theorem iso_rep1 (hG : InG X P) (h2 : vcount P = 2) : IsoFrom P (repG 1) := by
  obtain ⟨u, hu⟩ := cntF_pos _ _ (by omega : 0 < vcount P)
  obtain ⟨p, q, r, hp, hq, hr, hpu, hqu, hru, hpq, hpr, hqr, hall⟩ := hG.2.2.2 u hu
  let w := other p u
  have jp : X.Joins p u w := joins_other hpu
  have huw : u ≠ w := ne_of_joins hG.1 jp
  have hw : meets P w := ⟨p, hp, joins_inc_right jp⟩
  -- only `u` and `w` meet `P`
  have only2 : ∀ x, meets P x → x = u ∨ x = w := by
    intro x hx
    by_contra hne
    push_neg at hne
    have : ({u, w, x} : Finset (Fin X.n)) ⊆ univ.filter (meets P) := by
      intro y hy; simp only [mem_insert, mem_singleton] at hy
      simp only [mem_filter, mem_univ, true_and]
      rcases hy with rfl | rfl | rfl <;> assumption
    have hc := card_le_card this
    rw [← vcount_eq_card, h2, card_insert_of_notMem (by simp [huw, hne.1.symm]),
      card_insert_of_notMem (by simp [hne.2.symm]), card_singleton] at hc
    omega
  -- every edge of `P` joins `u` and `w`
  have allj : ∀ f, P f → X.Joins f u w := by
    intro f hf
    have h1 := only2 _ ⟨f, hf, Or.inl rfl⟩
    have h2 := only2 _ ⟨f, hf, Or.inr rfl⟩
    have hne := hG.1 f
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
    · exact absurd (h1.trans h2.symm) hne
  let α : Fin X.n → Fin (repG 1).n := fun x => if x = u then ⟨0, by decide⟩ else ⟨1, by decide⟩
  let β : Fin X.m → Fin (repG 1).m := fun f =>
    if f = p then ⟨0, by decide⟩ else if f = q then ⟨1, by decide⟩ else ⟨2, by decide⟩
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy hxy
    rcases only2 x hx with rfl | rfl <;> rcases only2 y hy with rfl | rfl
    · rfl
    · simp [α, huw.symm] at hxy
    · simp [α, huw.symm] at hxy
    · rfl
  · intro f g hf hg hfg
    have hf' := hall f hf (joins_inc_left (allj f hf))
    have hg' := hall g hg (joins_inc_left (allj g hg))
    rcases hf' with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
      simp [β, hpq, hpr, hqr, hpq.symm, hpr.symm, hqr.symm] at hfg ⊢
  · intro j
    have : j.val < 3 := j.isLt
    rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with h | h | h
    · exact ⟨p, hp, Fin.ext (by simp [β, h])⟩
    · exact ⟨q, hq, Fin.ext (by simp [β, hpq.symm, h])⟩
    · exact ⟨r, hr, Fin.ext (by simp [β, hpr.symm, hqr.symm, h])⟩
  · intro f hf
    have hfu := allj f hf
    have hb : ((repG 1).ends (β f)) = (⟨0, by decide⟩, ⟨1, by decide⟩) := by
      simp only [β]; split_ifs <;> rfl
    rcases hfu with h | h <;> rw [h]
    · simp only [α, if_pos rfl, if_neg huw.symm]; exact Or.inl hb
    · simp only [α, if_pos rfl, if_neg huw.symm]; exact Or.inr hb

end cls

end RH2F

namespace RH2F
open MGraph Finset
open Classical

section cls2
variable {X : MGraph} {P : Fin X.m → Prop}

theorem repInc (k : Nat) (hk : k ≤ 25) : ∀ p : Fin (repG k).n, ∃ e, (repG k).Inc e p := by
  have key : ∀ k, k ≤ 25 → allFin (repG k).n (fun p => (List.finRange (repG k).m).any
      (fun e => ((repG k).ends e).1 == p || ((repG k).ends e).2 == p)) = true := by decide +kernel
  intro p
  have h := allFin_sound (key k hk) p
  rw [List.any_eq_true] at h
  obtain ⟨e, _, he⟩ := h
  simp only [Bool.or_eq_true, beq_iff_eq] at he
  exact ⟨e, he⟩

theorem repN_big (k : Nat) (hk : 25 < k) : repN k = 2 := by
  unfold repN; split <;> omega

theorem range_of_repN (k : Nat) (hk : 4 ≤ repN k) : 1 ≤ k ∧ k ≤ 25 := by
  constructor
  · by_contra h
    have : k = 0 := by omega
    subst this; simp [repN] at hk
  · by_contra h
    rw [repN_big k (by omega)] at hk; omega

theorem subChk_all : ∀ j, 1 ≤ j → j ≤ 8 → subChk j = true := by
  intro j h1 h8
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [subChk_1, subChk_2, subChk_3, subChk_4, subChk_5, subChk_6, subChk_7, subChk_8]

theorem infChk_all : ∀ j, 1 ≤ j → j ≤ 8 → infChk j = true := by
  intro j h1 h8
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [infChk_1, infChk_2, infChk_3, infChk_4, infChk_5, infChk_6, infChk_7, infChk_8]

theorem repN_small : ∀ k, 1 ≤ k → k ≤ 25 → repN k ≤ 6 → k ≤ 8 := by decide +kernel
theorem repN_ge2 : ∀ k, k ≤ 25 → 2 ≤ repN k := by decide +kernel

/-- **Classification** (claim (E_n) of fact 7922314679f8733d): every member of 𝒢 with at most 8 vertices is
    isomorphic to one of `Rep01`–`Rep25` (fact be9b0c62ac86fc55). -/
theorem cls : ∀ n, ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P = n → 0 < n → n ≤ 8 →
    ∃ k, 1 ≤ k ∧ k ≤ 25 ∧ repN k = n ∧ IsoFrom P (repG k) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro X P hG hn hpos h8
  have hev := vcount_even' hG
  by_cases h2 : n = 2
  · exact ⟨1, le_refl _, by decide, by rw [h2]; rfl, iso_rep1 hG (hn.trans h2)⟩
  have h4 : 4 ≤ n := by omega
  by_cases hdig : ∃ (u v : Fin X.n) (d1 d2 : Fin X.m), P d1 ∧ P d2 ∧ X.Joins d1 u v ∧ X.Joins d2 u v ∧ d1 ≠ d2
  · -- a digon: `P ≅ Sub(Rep_k, i)`
    obtain ⟨u, v, d1, d2, hd1, hd2, j1, j2, d12⟩ := hdig
    obtain ⟨D, _, _⟩ := digData_of hG (hn ▸ h4) hd1 hd2 j1 j2 d12
    have hvD := D.vcount_digP
    obtain ⟨k, hk1, hk25, hkn, hiso⟩ := ih (n - 2) (by omega) _ _ (D.inG_digP hG) (by omega) (by omega) (by omega)
    obtain ⟨i, hi⟩ := D.lift hiso
    have hk8 : k ≤ 8 := repN_small k hk1 hk25 (by omega)
    have hc := allFin_sound (subChk_all k hk1 hk8) i
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hr := range_of_repN (subD k i.val).1 (by rw [hc.1]; omega)
    exact ⟨(subD k i.val).1, hr.1, hr.2, by rw [hc.1, hkn]; omega, isoFrom_trans hi (concIso_of_chk hc.2)⟩
  · -- simple
    have hS : SimpleP P := by
      intro f g x y hf hg jf jg
      by_contra hne
      exact hdig ⟨x, y, f, g, hf, hg, jf, jg, hne⟩
    by_cases htri : ∃ a b c : Fin X.n, Adjq P a b ∧ Adjq P b c ∧ Adjq P c a
    · -- a triangle: `P ≅ Inf(Rep_k, s, i2, i3)`
      obtain ⟨a, b, c, ⟨ab, hab, jab⟩, ⟨bc, hbc, jbc⟩, ⟨ca, hca, jca⟩⟩ := htri
      obtain ⟨T, _, _, _⟩ := triData_of hG hS hab hbc hca jab jbc jca
      have hvT := T.vcount_triP
      obtain ⟨k, hk1, hk25, hkn, hiso⟩ := ih (n - 2) (by omega) _ _ (T.inG_triP hG) (by omega) (by omega) (by omega)
      obtain ⟨s, i2, i3, h23, hi2, hi3, hi⟩ := T.lift hiso
      have hk8 : k ≤ 8 := repN_small k hk1 hk25 (by omega)
      have hc := allFin_sound (allFin_sound (allFin_sound (infChk_all k hk1 hk8) s) i2) i3
      have g1 : (!(i2 != i3 && ((repG k).ends i2).1 == s || i2 != i3 && ((repG k).ends i2).2 == s)) = false := by
        rcases hi2 with h | h <;> simp [h, h23]
      have g2 : (!(((repG k).ends i3).1 == s || ((repG k).ends i3).2 == s)) = false := by
        rcases hi3 with h | h <;> simp [h]
      rw [g1, g2, Bool.false_or, Bool.false_or] at hc
      by_cases hd0 : (infD k s.val i2.val i3.val).1 = 0
      · exfalso
        simp only [hd0, beq_self_eq_true, if_true] at hc
        unfold parChk at hc
        split_ifs at hc with hp hq
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hc
        exact simple_of_iso hi hS (fun h => hc.1 (congrArg Fin.val h)) hc.2
      · simp only [show ((infD k s.val i2.val i3.val).1 == 0) = false by simpa using hd0] at hc
        simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq] at hc
        have hr := range_of_repN (infD k s.val i2.val i3.val).1 (by rw [hc.1]; omega)
        exact ⟨(infD k s.val i2.val i3.val).1, hr.1, hr.2, by rw [hc.1, hkn]; omega,
          isoFrom_trans hi (concIso_of_chk hc.2)⟩
    · -- simple and triangle-free: `K₃,₃`, cube, Wagner graph
      have hT : TriFree P := fun a b c h1 h2 h3 => htri ⟨a, b, c, h1, h2, h3⟩
      rcases tf_iso hG hS hT (hn ▸ h8) (hn ▸ hpos) with h | h | h
      · exact ⟨8, by decide, by decide, by rw [← hn, vcount_iso h (repInc 8 (by decide))]; rfl, h⟩
      · exact ⟨24, by decide, by decide, by rw [← hn, vcount_iso h (repInc 24 (by decide))]; rfl, h⟩
      · exact ⟨25, by decide, by decide, by rw [← hn, vcount_iso h (repInc 25 (by decide))]; rfl, h⟩

end cls2

end RH2F


-- ===== from FS.lean =====

/-!
  FS.lean — a light star-colouring checker for explicit multigraphs `ofList n el`, using precomputed incidence
  lists `inc` (checked against `el`) and the "other end" of an edge, with a soundness proof.
-/

namespace RH2F
open MGraph

section fs

def gE (el : List (Nat × Nat)) (e : Nat) : Nat × Nat := el.getD e (0, 0)

/-- the end of edge `e` other than `v` -/
def oth (el : List (Nat × Nat)) (e v : Nat) : Nat := if (gE el e).1 == v then (gE el e).2 else (gE el e).1

def colN (cl : List Nat) (e : Nat) : Nat := cl.getD e 0 % 6

/-- the edge list is loopless with ends `< n` -/
def elOK (n : Nat) (el : List (Nat × Nat)) : Bool := el.all (fun e => e.1 < n && e.2 < n && e.1 != e.2)

/-- `inc` lists exactly the edges at each vertex -/
def incOK (n : Nat) (el : List (Nat × Nat)) (inc : List (List Nat)) : Bool :=
  (List.range n).all (fun v => (List.range el.length).all (fun e =>
    ((inc.getD v []).contains e) == ((gE el e).1 == v || (gE el e).2 == v)))

def properOK (n : Nat) (inc : List (List Nat)) (cl : List Nat) : Bool :=
  (List.range n).all (fun v => (inc.getD v []).all (fun a => (inc.getD v []).all (fun b =>
    a == b || colN cl a != colN cl b)))

def walkOKF (n : Nat) (el : List (Nat × Nat)) (inc : List (List Nat)) (cl : List Nat) : Bool :=
  (List.range n).all fun v0 => (inc.getD v0 []).all fun e1 =>
    (inc.getD (oth el e1 v0) []).all fun e2 =>
    (inc.getD (oth el e2 (oth el e1 v0)) []).all fun e3 =>
    (inc.getD (oth el e3 (oth el e2 (oth el e1 v0))) []).all fun e4 =>
      let v1 := oth el e1 v0
      let v2 := oth el e2 v1
      let v3 := oth el e3 v2
      let v4 := oth el e4 v3
      !((v0 != v1) && (v0 != v2) && (v0 != v3) && (v1 != v2) && (v1 != v3) && (v1 != v4) && (v2 != v3) &&
        (v2 != v4) && (v3 != v4) && (colN cl e1 == colN cl e3) && (colN cl e2 == colN cl e4))

/-- the full check -/
def fastStar (n : Nat) (el : List (Nat × Nat)) (inc : List (List Nat)) (cl : List Nat) : Bool :=
  elOK n el && incOK n el inc && properOK n inc cl && walkOKF n el inc cl

/-- the colouring given by a list -/
def colF (m : Nat) (cl : List Nat) : Fin m → Fin 6 := fun e => ⟨colN cl e.val, Nat.mod_lt _ (by decide)⟩

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

theorem ofList_ends (hel : elOK n el = true) (e : Fin (ofList n el hn).m) :
    (((ofList n el hn).ends e).1.val = (gE el e.val).1) ∧ (((ofList n el hn).ends e).2.val = (gE el e.val).2) := by
  have he : el.get e ∈ el := List.get_mem el e
  have hb := List.all_eq_true.1 hel _ he
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  have hlt : e.val < el.length := e.isLt
  have hg : gE el e.val = el.get e := by
    simp [gE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  simp only [ofList, hg]
  exact ⟨Nat.mod_eq_of_lt hb.1.1, Nat.mod_eq_of_lt hb.1.2⟩

theorem ofList_loop (hel : elOK n el = true) (e : Fin (ofList n el hn).m) : (gE el e.val).1 ≠ (gE el e.val).2 := by
  have he : el.get e ∈ el := List.get_mem el e
  have hb := List.all_eq_true.1 hel _ he
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  have hlt : e.val < el.length := e.isLt
  have hg : gE el e.val = el.get e := by
    simp [gE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  rw [hg]; exact hb.2

theorem mem_inc (hel : elOK n el = true) {inc : List (List Nat)} (hinc : incOK n el inc = true)
    {e : Fin (ofList n el hn).m} {x : Fin n} (h : (ofList n el hn).Inc e x) : e.val ∈ inc.getD x.val [] := by
  have h1 := List.all_eq_true.1 hinc x.val (List.mem_range.2 x.isLt)
  have h2 := List.all_eq_true.1 h1 e.val (List.mem_range.2 e.isLt)
  have he := ofList_ends (hn := hn) hel e
  rw [beq_iff_eq] at h2
  have : ((gE el e.val).1 == x.val || (gE el e.val).2 == x.val) = true := by
    rcases h with h | h
    · rw [← he.1, h]; simp
    · rw [← he.2, h]; simp
  rw [this] at h2
  exact List.contains_iff_mem.1 h2

theorem oth_of_joins (hel : elOK n el = true) {e : Fin (ofList n el hn).m} {x y : Fin n}
    (h : (ofList n el hn).Joins e x y) : oth el e.val x.val = y.val := by
  have he := ofList_ends (hn := hn) hel e
  unfold oth
  rcases h with h | h <;> rw [h] at he <;> simp only at he <;> obtain ⟨h1, h2⟩ := he <;> rw [← h1, ← h2]
  · simp
  · by_cases hyx : y.val = x.val
    · simp [hyx]
    · simp [hyx]

/-- **soundness** of the light checker -/
theorem star_of_fast {inc : List (List Nat)} {cl : List Nat} (h : fastStar n el inc cl = true) :
    StarOn (fun _ => True) 6 (colF (ofList n el hn).m cl) := by
  unfold fastStar at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hel, hinc⟩, hprop⟩, hwalk⟩ := h
  constructor
  · intro a b ⟨hab, x, hax, hbx⟩ _ _ heq
    have ha := mem_inc (hn := hn) hel hinc hax
    have hb := mem_inc (hn := hn) hel hinc hbx
    have h1 := List.all_eq_true.1 hprop x.val (List.mem_range.2 x.isLt)
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 a.val ha) b.val hb
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
    have hc : colN cl a.val = colN cl b.val := congrArg Fin.val heq
    rcases h2 with h2 | h2
    · exact hab (Fin.ext h2)
    · exact h2 hc
  · intro w _ _ _ _ hbc
    have m1 := mem_inc (hn := hn) hel hinc (joins_inc_left w.h1)
    have m2 := mem_inc (hn := hn) hel hinc (joins_inc_left w.h2)
    have m3 := mem_inc (hn := hn) hel hinc (joins_inc_left w.h3)
    have m4 := mem_inc (hn := hn) hel hinc (joins_inc_left w.h4)
    have o1 := oth_of_joins (hn := hn) hel w.h1
    have o2 := oth_of_joins (hn := hn) hel w.h2
    have o3 := oth_of_joins (hn := hn) hel w.h3
    have o4 := oth_of_joins (hn := hn) hel w.h4
    have k0 := List.all_eq_true.1 hwalk w.v0.val (List.mem_range.2 w.v0.isLt)
    have k1 := List.all_eq_true.1 k0 w.e1.val m1
    rw [o1] at k1
    have k2 := List.all_eq_true.1 k1 w.e2.val m2
    rw [o2] at k2
    have k3 := List.all_eq_true.1 k2 w.e3.val m3
    rw [o3] at k3
    have k4 := List.all_eq_true.1 k3 w.e4.val m4
    simp only [o1, o2, o3, o4] at k4
    have c13 : colN cl w.e1.val = colN cl w.e3.val := congrArg Fin.val hbc.1
    have c24 : colN cl w.e2.val = colN cl w.e4.val := congrArg Fin.val hbc.2
    have d01 : w.v0.val ≠ w.v1.val := fun h => w.d01 (Fin.ext h)
    have d02 : w.v0.val ≠ w.v2.val := fun h => w.d02 (Fin.ext h)
    have d03 : w.v0.val ≠ w.v3.val := fun h => w.d03 (Fin.ext h)
    have d12 : w.v1.val ≠ w.v2.val := fun h => w.d12 (Fin.ext h)
    have d13 : w.v1.val ≠ w.v3.val := fun h => w.d13 (Fin.ext h)
    have d14 : w.v1.val ≠ w.v4.val := fun h => w.d14 (Fin.ext h)
    have d23 : w.v2.val ≠ w.v3.val := fun h => w.d23 (Fin.ext h)
    have d24 : w.v2.val ≠ w.v4.val := fun h => w.d24 (Fin.ext h)
    have d34 : w.v3.val ≠ w.v4.val := fun h => w.d34 (Fin.ext h)
    simp [d01, d02, d03, d12, d13, d14, d23, d24, d34, c13, c24] at k4

end fs

end RH2F


-- ===== from B8.lean =====

namespace RH2F
open MGraph
open Classical

/-- the colourings of fact be9b0c62ac86fc55 (colours shifted to `0..5`) -/
def repCol : Nat → List Nat
  | 1 => [0, 1, 2]
  | 2 => [0, 1, 2, 3, 4, 2]
  | 3 => [0, 1, 2, 2, 3, 4]
  | 4 => [0, 1, 1, 2, 3, 4, 3, 5, 4]
  | 5 => [0, 1, 2, 3, 4, 3, 5, 2, 3]
  | 6 => [0, 1, 1, 2, 3, 4, 2, 5, 4]
  | 7 => [0, 1, 2, 2, 3, 4, 4, 5, 1]
  | 8 => [0, 1, 2, 1, 3, 4, 2, 4, 5]
  | 9 => [0, 1, 2, 3, 3, 1, 2, 4, 4, 1, 2, 4]
  | 10 => [0, 1, 0, 1, 2, 3, 4, 2, 2, 3, 4, 2]
  | 11 => [0, 1, 2, 3, 3, 1, 2, 0, 2, 4, 1, 2]
  | 12 => [0, 0, 1, 2, 1, 3, 2, 4, 4, 3, 2, 4]
  | 13 => [0, 1, 2, 1, 3, 4, 5, 3, 3, 4, 5, 3]
  | 14 => [0, 1, 2, 3, 4, 2, 4, 3, 3, 0, 1, 3]
  | 15 => [0, 1, 1, 2, 3, 4, 5, 4, 3, 1, 2, 3]
  | 16 => [0, 1, 1, 2, 3, 4, 5, 3, 3, 4, 5, 3]
  | 17 => [0, 1, 2, 3, 2, 4, 1, 5, 5, 4, 1, 5]
  | 18 => [0, 1, 2, 3, 4, 1, 2, 4, 3, 0, 1, 3]
  | 19 => [0, 1, 1, 2, 3, 3, 4, 5, 5, 3, 4, 5]
  | 20 => [0, 1, 2, 3, 4, 0, 3, 1, 3, 2, 4, 3]
  | 21 => [0, 1, 2, 2, 3, 4, 4, 0, 1, 1, 2, 3]
  | 22 => [0, 1, 1, 2, 3, 0, 3, 4, 4, 2, 3, 4]
  | 23 => [0, 1, 2, 2, 0, 1, 3, 4, 5, 3, 4, 5]
  | 24 => [0, 1, 2, 0, 1, 2, 2, 3, 2, 4, 3, 4]
  | 25 => [0, 1, 2, 3, 1, 3, 2, 4, 2, 5, 5, 4]
  | _ => [0, 1, 2]

def repIncL : Nat → List (List Nat)
  | 1 => [[0, 1, 2], [0, 1, 2]]
  | 2 => [[0, 1, 2], [0, 1, 5], [2, 3, 4], [3, 4, 5]]
  | 3 => [[0, 3, 5], [0, 1, 2], [1, 3, 4], [2, 4, 5]]
  | 4 => [[0, 1, 5], [0, 1, 4], [2, 3, 8], [2, 3, 4], [5, 6, 7], [6, 7, 8]]
  | 5 => [[0, 1, 5], [0, 4, 8], [1, 2, 3], [2, 3, 4], [5, 6, 7], [6, 7, 8]]
  | 6 => [[2, 4, 5], [0, 1, 8], [0, 2, 3], [1, 3, 4], [5, 6, 7], [6, 7, 8]]
  | 7 => [[0, 6, 8], [0, 1, 2], [1, 3, 4], [2, 4, 5], [3, 6, 7], [5, 7, 8]]
  | 8 => [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8]]
  | 9 => [[0, 4, 8], [0, 3, 11], [1, 2, 7], [1, 2, 3], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 10 => [[0, 1, 4], [0, 1, 11], [2, 3, 7], [2, 3, 8], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 11 => [[0, 4, 8], [3, 7, 11], [0, 1, 2], [1, 2, 3], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 12 => [[0, 4, 8], [0, 3, 7], [1, 2, 11], [1, 2, 3], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 13 => [[0, 1, 4], [0, 3, 7], [1, 2, 8], [2, 3, 11], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 14 => [[2, 4, 8], [0, 1, 7], [0, 2, 3], [1, 3, 4], [5, 6, 11], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 15 => [[2, 4, 5], [0, 1, 7], [0, 2, 3], [1, 3, 4], [5, 6, 8], [6, 7, 11], [8, 9, 10], [9, 10, 11]]
  | 16 => [[2, 3, 4], [0, 1, 7], [0, 2, 8], [1, 3, 11], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 17 => [[3, 4, 8], [0, 1, 7], [0, 2, 11], [1, 2, 3], [4, 5, 6], [5, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 18 => [[2, 4, 5], [0, 1, 8], [0, 2, 3], [1, 3, 4], [5, 9, 11], [6, 7, 8], [6, 9, 10], [7, 10, 11]]
  | 19 => [[0, 5, 7], [0, 1, 11], [2, 3, 8], [1, 3, 4], [2, 5, 6], [4, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 20 => [[5, 7, 8], [0, 1, 11], [0, 2, 3], [1, 3, 4], [2, 5, 6], [4, 6, 7], [8, 9, 10], [9, 10, 11]]
  | 21 => [[0, 9, 11], [0, 1, 2], [1, 3, 4], [2, 4, 5], [3, 6, 7], [5, 7, 8], [6, 9, 10], [8, 10, 11]]
  | 22 => [[0, 1, 8], [2, 3, 4], [5, 6, 7], [2, 5, 11], [0, 3, 6], [1, 4, 7], [8, 9, 10], [9, 10, 11]]
  | 23 => [[0, 9, 11], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [1, 9, 10], [2, 10, 11]]
  | 24 => [[0, 1, 2], [0, 6, 7], [1, 8, 9], [2, 10, 11], [3, 4, 5], [3, 8, 10], [4, 6, 11], [5, 7, 9]]
  | 25 => [[0, 1, 2], [0, 6, 10], [1, 7, 8], [2, 9, 11], [3, 8, 9], [3, 4, 6], [4, 5, 7], [5, 10, 11]]
  | _ => [[0, 1, 2], [0, 1, 2]]

theorem repFast_1 : fastStar (repN 1) (repL 1) (repIncL 1) (repCol 1) = true := by decide +kernel
theorem repFast_2 : fastStar (repN 2) (repL 2) (repIncL 2) (repCol 2) = true := by decide +kernel
theorem repFast_3 : fastStar (repN 3) (repL 3) (repIncL 3) (repCol 3) = true := by decide +kernel
theorem repFast_4 : fastStar (repN 4) (repL 4) (repIncL 4) (repCol 4) = true := by decide +kernel
theorem repFast_5 : fastStar (repN 5) (repL 5) (repIncL 5) (repCol 5) = true := by decide +kernel
theorem repFast_6 : fastStar (repN 6) (repL 6) (repIncL 6) (repCol 6) = true := by decide +kernel
theorem repFast_7 : fastStar (repN 7) (repL 7) (repIncL 7) (repCol 7) = true := by decide +kernel
theorem repFast_8 : fastStar (repN 8) (repL 8) (repIncL 8) (repCol 8) = true := by decide +kernel
theorem repFast_9 : fastStar (repN 9) (repL 9) (repIncL 9) (repCol 9) = true := by decide +kernel
theorem repFast_10 : fastStar (repN 10) (repL 10) (repIncL 10) (repCol 10) = true := by decide +kernel
theorem repFast_11 : fastStar (repN 11) (repL 11) (repIncL 11) (repCol 11) = true := by decide +kernel
theorem repFast_12 : fastStar (repN 12) (repL 12) (repIncL 12) (repCol 12) = true := by decide +kernel
theorem repFast_13 : fastStar (repN 13) (repL 13) (repIncL 13) (repCol 13) = true := by decide +kernel
theorem repFast_14 : fastStar (repN 14) (repL 14) (repIncL 14) (repCol 14) = true := by decide +kernel
theorem repFast_15 : fastStar (repN 15) (repL 15) (repIncL 15) (repCol 15) = true := by decide +kernel
theorem repFast_16 : fastStar (repN 16) (repL 16) (repIncL 16) (repCol 16) = true := by decide +kernel
theorem repFast_17 : fastStar (repN 17) (repL 17) (repIncL 17) (repCol 17) = true := by decide +kernel
theorem repFast_18 : fastStar (repN 18) (repL 18) (repIncL 18) (repCol 18) = true := by decide +kernel
theorem repFast_19 : fastStar (repN 19) (repL 19) (repIncL 19) (repCol 19) = true := by decide +kernel
theorem repFast_20 : fastStar (repN 20) (repL 20) (repIncL 20) (repCol 20) = true := by decide +kernel
theorem repFast_21 : fastStar (repN 21) (repL 21) (repIncL 21) (repCol 21) = true := by decide +kernel
theorem repFast_22 : fastStar (repN 22) (repL 22) (repIncL 22) (repCol 22) = true := by decide +kernel
theorem repFast_23 : fastStar (repN 23) (repL 23) (repIncL 23) (repCol 23) = true := by decide +kernel
theorem repFast_24 : fastStar (repN 24) (repL 24) (repIncL 24) (repCol 24) = true := by decide +kernel
theorem repFast_25 : fastStar (repN 25) (repL 25) (repIncL 25) (repCol 25) = true := by decide +kernel

theorem repFast (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 25) : fastStar (repN k) (repL k) (repIncL k) (repCol k) = true := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
    k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
    k = 24 ∨ k = 25) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [repFast_1, repFast_2, repFast_3, repFast_4, repFast_5, repFast_6, repFast_7, repFast_8, repFast_9, repFast_10, repFast_11, repFast_12, repFast_13, repFast_14, repFast_15, repFast_16, repFast_17, repFast_18, repFast_19, repFast_20, repFast_21, repFast_22, repFast_23, repFast_24, repFast_25]

section b8
variable {X : MGraph} {P : Fin X.m → Prop}

/-- star colourings pull back along an isomorphism onto a concrete multigraph -/
theorem starOn_of_iso {H : MGraph} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m}
    (hα : ∀ x y, meets P x → meets P y → α x = α y → x = y) (hβ : ∀ f g, P f → P g → β f = β g → f = g)
    (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {c : Fin H.m → Fin 6}
    (hc : StarOn (fun _ => True) 6 c) : StarOn P 6 (fun f => c (β f)) :=
  starOn_embed α β (fun x y a b ha hb hax hby h => hα x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h) hβ (fun _ _ => trivial) hj hc

theorem colourable_of_iso {H : MGraph} (h : IsoFrom P H) (hc : Colourable (fun _ : Fin H.m => True) 6) :
    Colourable P 6 := by
  obtain ⟨α, β, hα, hβ, _, hj⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨_, starOn_of_iso hα hβ hj hc⟩

theorem rep_colourable (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 25) : Colourable (fun _ : Fin (repG k).m => True) 6 :=
  ⟨_, star_of_fast (hn := repN_pos k) (repFast k hk1 hk)⟩

/-- **Theorem B8** (fact 7922314679f8733d) -/
theorem b8s : B8S := by
  intro X P hG h8
  by_cases hne : ∃ f, P f
  · obtain ⟨f, hf⟩ := hne
    have hpos : 0 < vcount P := by
      have := cntF_le_of_mem X.n (meets P) (i := (X.ends f).1) ⟨f, hf, Or.inl rfl⟩
      unfold vcount; omega
    obtain ⟨k, hk1, hk25, _, hiso⟩ := cls _ X P hG rfl hpos h8
    exact colourable_of_iso hiso (rep_colourable k hk1 hk25)
  · exact ⟨fun _ => 0, fun a _ _ ha _ => absurd ⟨a, ha⟩ hne, fun w h1 _ _ _ => absurd ⟨w.e1, h1⟩ hne⟩

end b8

end RH2F

namespace RH2F
open MGraph

/-- **Layer 6b of the Lean formalization of RH2**: the classification of the members of 𝒢 with at most 8 vertices
    (claim (E_n) of fact 7922314679f8733d), Theorem B8 itself, and Theorem RH2 (fact 6bfcd4d52c94468a) with part (P)
    and B8 discharged. -/
theorem layer6b :
    (∀ n (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P = n → 0 < n → n ≤ 8 →
      ∃ k, 1 ≤ k ∧ k ≤ 25 ∧ repN k = n ∧ IsoFrom P (repG k)) ∧
    B8S ∧ (SmallFacts → Hyp → II → DMS) :=
  ⟨cls, b8s, fun hSF => RH2P.rh2_P hSF b8s⟩

end RH2F
