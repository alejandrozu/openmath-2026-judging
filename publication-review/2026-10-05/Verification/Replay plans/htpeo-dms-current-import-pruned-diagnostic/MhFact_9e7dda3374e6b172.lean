-- Lean proof of fact 9e7dda3374e6b172 (RH2F.layer13); added by fact_submit, do not edit
import MhFact_90b4662cdeba097d
set_option backward.isDefEq.respectTransparency false

-- ===== from III1.lean =====
/-
  III1.lean — 3-edge-cuts with distinct ends (Theorem 3CUT-MULTI, fact 4f30e30e4f4d4e99): the cut structure `Cut3`,
  its poles inside the ambient multigraph (the pendant vertex of port `i` is the far end of the cut edge `e_i`), and
  the exact gluing (A-M), direction ⇐, of star colourings of the two poles.
-/

namespace RH2F
open MGraph
open Classical

section cut3
variable {X : MGraph}

/-- a 3-edge-cut of `P` with distinct ends: side map `S` (side `A` = `true`), cut edges `e i` joining `y i ∈ A` and
    `w i ∈ B` -/
structure Cut3 (P : Fin X.m → Prop) where
  S : Fin X.n → Bool
  e : Fin 3 → Fin X.m
  y : Fin 3 → Fin X.n
  w : Fin 3 → Fin X.n
  hP : ∀ i, P (e i)
  hj : ∀ i, X.Joins (e i) (y i) (w i)
  sy : ∀ i, S (y i) = true
  sw : ∀ i, S (w i) = false
  einj : ∀ i j, e i = e j → i = j
  yinj : ∀ i j, y i = y j → i = j
  winj : ∀ i j, w i = w j → i = j
  cut : ∀ f, P f → S (X.ends f).1 ≠ S (X.ends f).2 → ∃ i, f = e i

variable {P : Fin X.m → Prop}

namespace Cut3
variable (C : Cut3 P)

/-- the same cut seen from side `B` -/
def flip : Cut3 P where
  S := fun v => !C.S v
  e := C.e
  y := C.w
  w := C.y
  hP := C.hP
  hj := fun i => Or.symm (C.hj i)
  sy := fun i => by simp [C.sw i]
  sw := fun i => by simp [C.sy i]
  einj := C.einj
  yinj := C.winj
  winj := C.yinj
  cut := fun f hf h => C.cut f hf (fun h' => h (by simp [h']))

/-- `f ∈ P` has both ends in side `A` -/
def inA (f : Fin X.m) : Prop := P f ∧ C.S (X.ends f).1 = true ∧ C.S (X.ends f).2 = true
/-- `f` is a cut edge -/
def isCut (f : Fin X.m) : Prop := ∃ i, f = C.e i
/-- the pole `Q1`: the edges inside `A` and the three cut edges (pendant vertex of port `i` is `w i`) -/
def pole (f : Fin X.m) : Prop := C.inA f ∨ C.isCut f

theorem flip_S (v : Fin X.n) : C.flip.S v = !C.S v := rfl
theorem flip_isCut {f : Fin X.m} : C.flip.isCut f ↔ C.isCut f := Iff.rfl

theorem side_of_inA {f : Fin X.m} {x : Fin X.n} (hf : C.inA f) (hx : X.Inc f x) : C.S x = true := by
  rcases hx with hx | hx
  · rw [← hx]; exact hf.2.1
  · rw [← hx]; exact hf.2.2

theorem pole_P {f : Fin X.m} (h : C.pole f) : P f := by
  rcases h with h | ⟨i, rfl⟩
  · exact h.1
  · exact C.hP i

theorem cases_P {f : Fin X.m} (hf : P f) : C.inA f ∨ C.flip.inA f ∨ C.isCut f := by
  by_cases h : C.S (X.ends f).1 = C.S (X.ends f).2
  · cases h1 : C.S (X.ends f).1
    · have h2 : C.S (X.ends f).2 = false := h ▸ h1
      exact Or.inr (Or.inl ⟨hf, by simp [flip_S, h1], by simp [flip_S, h2]⟩)
    · have h2 : C.S (X.ends f).2 = true := h ▸ h1
      exact Or.inl ⟨hf, h1, h2⟩
  · exact Or.inr (Or.inr (C.cut f hf h))

theorem not_inA_of_cut {f : Fin X.m} (hf : C.isCut f) : ¬ C.inA f := by
  intro hin
  obtain ⟨i, rfl⟩ := hf
  have h := C.side_of_inA hin (joins_inc_right (C.hj i)); rw [C.sw i] at h; exact absurd h (by decide)

theorem not_flip_of_inA {f : Fin X.m} (hf : C.inA f) : ¬ C.flip.inA f := by
  intro h
  have h1 := h.2.1
  rw [flip_S, hf.2.1] at h1
  exact absurd h1 (by decide)

theorem inA_of_notcut {f : Fin X.m} {x : Fin X.n} (hf : P f) (hnc : ¬ C.isCut f) (hx : X.Inc f x)
    (hs : C.S x = true) : C.inA f := by
  rcases C.cases_P hf with h | h | h
  · exact h
  · have h' := C.flip.side_of_inA h hx
    rw [flip_S, hs] at h'
    exact absurd h' (by decide)
  · exact absurd h hnc

/-- every edge of `P` at a vertex of side `A` lies in the pole -/
theorem pole_of_inc {f : Fin X.m} {x : Fin X.n} (hf : P f) (hx : X.Inc f x) (hs : C.S x = true) : C.pole f := by
  by_cases hc : C.isCut f
  · exact Or.inr hc
  · exact Or.inl (C.inA_of_notcut hf hc hx hs)

theorem y_ne_w (i j : Fin 3) : C.y i ≠ C.w j := fun h => by
  have h1 := C.sy i; rw [h, C.sw j] at h1; exact absurd h1 (by decide)

/-- the ends of the cut edge `e i` -/
theorem ends_e {i : Fin 3} {u u' : Fin X.n} (hj : X.Joins (C.e i) u u') :
    (u = C.y i ∧ u' = C.w i) ∨ (u = C.w i ∧ u' = C.y i) := by
  rcases joins_unique hj (C.hj i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- a cut edge at `y i` is `e i` -/
theorem cut_at_y {i j : Fin 3} (h : X.Inc (C.e j) (C.y i)) : j = i := by
  rcases inc_of_joins (C.hj j) h with h' | h'
  · exact C.yinj _ _ h'.symm
  · exact absurd h' (C.y_ne_w i j)

/-- a cut edge at `w i` is `e i` -/
theorem cut_at_w {i j : Fin 3} (h : X.Inc (C.e j) (C.w i)) : j = i := by
  rcases inc_of_joins (C.hj j) h with h' | h'
  · exact absurd h'.symm (C.y_ne_w j i)
  · exact C.winj _ _ h'.symm

/-- an edge of `P` at `y i` other than `e i` is inside `A` -/
theorem inA_at_y {i : Fin 3} {f : Fin X.m} (hf : P f) (hfy : X.Inc f (C.y i)) (hne : f ≠ C.e i) : C.inA f :=
  C.inA_of_notcut hf (fun ⟨j, hj⟩ => hne (by subst hj; rw [C.cut_at_y hfy])) hfy (C.sy i)

/-- the colours of the edges inside `A` at `y i` -/
def Col (φ : Fin X.m → Fin 6) (i : Fin 3) (κ : Fin 6) : Prop := ∃ f, C.inA f ∧ X.Inc f (C.y i) ∧ φ f = κ

/-- the colours of the blocking edges inside `A` at `y i`: `f = y_i r` such that `r` is incident with another pole
    edge of the colour of the port edge `e i` -/
def Blk (φ : Fin X.m → Fin 6) (i : Fin 3) (κ : Fin 6) : Prop :=
  ∃ f r, C.inA f ∧ X.Joins f (C.y i) r ∧ φ f = κ ∧ ∃ f', C.pole f' ∧ f' ≠ f ∧ X.Inc f' r ∧ φ f' = φ (C.e i)

theorem flip_flip_inA {f : Fin X.m} : C.flip.flip.inA f ↔ C.inA f := by
  unfold inA; simp [flip_S]
theorem flip_flip_pole {f : Fin X.m} : C.flip.flip.pole f ↔ C.pole f := by
  unfold pole; rw [flip_flip_inA]; exact Iff.rfl
theorem flip_flip_Col {φ : Fin X.m → Fin 6} {i : Fin 3} {κ : Fin 6} : C.flip.flip.Col φ i κ ↔ C.Col φ i κ := by
  unfold Col; simp only [flip_flip_inA]; exact Iff.rfl
theorem flip_flip_Blk {φ : Fin X.m → Fin 6} {i : Fin 3} {κ : Fin 6} : C.flip.flip.Blk φ i κ ↔ C.Blk φ i κ := by
  unfold Blk; simp only [flip_flip_inA, flip_flip_pole]; exact Iff.rfl

/-- properness of a glued colouring -/
theorem glue_prop3 (φ ψ c : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f) :
    ∀ a b, X.Adj a b → P a → P b → c a ≠ c b := by
  intro a b hab ha hb
  obtain ⟨hne, x, hax, hbx⟩ := hab
  cases hs : C.S x
  · have hs' : C.flip.S x = true := by rw [flip_S, hs]; rfl
    have pa := C.flip.pole_of_inc ha hax hs'
    have pb := C.flip.pole_of_inc hb hbx hs'
    rw [hcψ a pa, hcψ b pb]
    exact hψ.1 a b ⟨hne, x, hax, hbx⟩ pa pb
  · have pa := C.pole_of_inc ha hax hs
    have pb := C.pole_of_inc hb hbx hs
    rw [hcφ a pa, hcφ b pb]
    exact hφ.1 a b ⟨hne, x, hax, hbx⟩ pa pb

/-- a walk whose two middle edges are not cut edges lies in one pole -/
theorem glue_mid3 (φ ψ c : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f) (w : X.Walk4)
    (h1 : P w.e1) (h2 : P w.e2) (h3 : P w.e3) (h4 : P w.e4) (c2 : ¬ C.isCut w.e2) (c3 : ¬ C.isCut w.e3) :
    ¬ Bicol c w := by
  intro hb
  have same : ∀ {f : Fin X.m} {x y : Fin X.n}, P f → ¬ C.isCut f → X.Joins f x y → C.S x = C.S y := by
    intro f x y hf hnc hj
    rcases C.cases_P hf with h | h | h
    · rw [C.side_of_inA h (joins_inc_left hj), C.side_of_inA h (joins_inc_right hj)]
    · have hx := C.flip.side_of_inA h (joins_inc_left hj)
      have hy := C.flip.side_of_inA h (joins_inc_right hj)
      rw [flip_S] at hx hy
      cases hx' : C.S x <;> cases hy' : C.S y <;> simp_all
    · exact absurd h hnc
  have s12 : C.S w.v1 = C.S w.v2 := same h2 c2 w.h2
  have s23 : C.S w.v2 = C.S w.v3 := same h3 c3 w.h3
  cases hs : C.S w.v1
  · have t1 : C.flip.S w.v1 = true := by rw [flip_S, hs]; rfl
    have t2 : C.flip.S w.v2 = true := by rw [flip_S, ← s12, hs]; rfl
    have t3 : C.flip.S w.v3 = true := by rw [flip_S, ← s23, ← s12, hs]; rfl
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

/-- the key case: the second edge `e i` of a bicoloured walk is a cut edge, `v1 = y i`; then the colour of `e1`
    lies in `Col_i(φ) ∩ Col_i(ψ) ∩ Blk_i(ψ)` -/
theorem key3 (φ ψ c : Fin X.m → Fin 6)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f)
    {i : Fin 3} {f1 f3 f4 : Fin X.m} {v3 : Fin X.n} (h1 : P f1) (h3 : P f3) (h4 : P f4)
    (i1 : X.Inc f1 (C.y i)) (n1 : f1 ≠ C.e i) (j3 : X.Joins f3 (C.w i) v3) (n3 : f3 ≠ C.e i)
    (i4 : X.Inc f4 v3) (n34 : f3 ≠ f4) (b13 : c f1 = c f3) (b24 : c (C.e i) = c f4) :
    C.Col φ i (c f1) ∧ C.flip.Col ψ i (c f1) ∧ C.flip.Blk ψ i (c f1) := by
  have hA : C.inA f1 := C.inA_at_y h1 i1 n1
  have hB : C.flip.inA f3 := C.flip.inA_at_y h3 (joins_inc_left j3) n3
  have hv3 : C.flip.S v3 = true := C.flip.side_of_inA hB (joins_inc_right j3)
  have p4 : C.flip.pole f4 := C.flip.pole_of_inc h4 i4 hv3
  refine ⟨⟨f1, hA, i1, (hcφ f1 (Or.inl hA)).symm⟩, ⟨f3, hB, joins_inc_left j3, ?_⟩,
    ⟨f3, v3, hB, j3, ?_, f4, p4, n34.symm, i4, ?_⟩⟩
  · rw [← hcψ f3 (Or.inl hB)]; exact b13.symm
  · rw [← hcψ f3 (Or.inl hB)]; exact b13.symm
  · show ψ f4 = ψ (C.e i)
    rw [← hcψ f4 p4, ← hcψ (C.e i) (Or.inr ⟨i, rfl⟩)]; exact b24.symm

/-- **3CUT-MULTI (A-M), direction ⇐** (pole form): star colourings `φ` of `Q1` and `ψ` of `Q2` that agree on the cut
    edges, with `Col_i(φ) ∩ Col_i(ψ) ∩ (Blk_i(φ) ∪ Blk_i(ψ)) = ∅` for every `i`, glue to a star colouring of `P` -/
theorem glue3 (φ ψ c : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcφ : ∀ f, C.pole f → c f = φ f) (hcψ : ∀ f, C.flip.pole f → c f = ψ f)
    (htri : ∀ i κ, C.Col φ i κ → C.flip.Col ψ i κ → (C.Blk φ i κ ∨ C.flip.Blk ψ i κ) → False) :
    StarOn P 6 c := by
  refine ⟨C.glue_prop3 φ ψ c hφ hψ hcφ hcψ, ?_⟩
  intro w h1 h2 h3 h4 hb
  have cc : ∀ f g : Fin X.m, C.isCut f → C.isCut g → f ≠ g → ∀ x, X.Inc f x → X.Inc g x → False := by
    rintro f g ⟨i, rfl⟩ ⟨j, rfl⟩ hne x hf hg
    apply hne
    rcases inc_of_joins (C.hj i) hf with rfl | rfl
    · rw [C.cut_at_y hg]
    · rw [C.cut_at_w hg]
  -- the flipped cut has the same cut edges and colouring data
  have hcφ' : ∀ f, C.flip.flip.pole f → c f = φ f := fun f hf => hcφ f (by
    rcases hf with h | h
    · exact Or.inl ⟨h.1, by simpa [flip_S] using h.2.1, by simpa [flip_S] using h.2.2⟩
    · exact Or.inr h)
  by_cases c2 : C.isCut w.e2
  · obtain ⟨i, hi⟩ := c2
    have n1 : w.e1 ≠ C.e i := hi ▸ w.e1_ne_e2
    have n3 : w.e3 ≠ C.e i := hi ▸ w.e2_ne_e3.symm
    rcases C.ends_e (hi ▸ w.h2) with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · have := C.key3 φ ψ c hcφ hcψ h1 h3 h4 (hv1 ▸ w.inc_e1_v1) n1 (hv2 ▸ w.h3) n3 w.inc_e4_v3
        w.e3_ne_e4 hb.1 (hi ▸ hb.2)
      exact htri i _ this.1 this.2.1 (Or.inr this.2.2)
    · have := C.flip.key3 ψ φ c hcψ hcφ' h1 h3 h4 (show X.Inc w.e1 (C.w i) from hv1 ▸ w.inc_e1_v1) n1
        (show X.Joins w.e3 (C.y i) w.v3 from hv2 ▸ w.h3) n3 w.inc_e4_v3 w.e3_ne_e4 hb.1 (hi ▸ hb.2)
      exact htri i _ (C.flip_flip_Col.1 this.2.1) this.1 (Or.inl (C.flip_flip_Blk.1 this.2.2))
  by_cases c3 : C.isCut w.e3
  · -- read the walk backwards
    obtain ⟨i, hi⟩ := c3
    have n4 : w.e4 ≠ C.e i := hi ▸ w.e3_ne_e4.symm
    have n2 : w.e2 ≠ C.e i := hi ▸ w.e2_ne_e3
    rcases C.ends_e (hi ▸ Or.symm w.h3) with ⟨hv3, hv2⟩ | ⟨hv3, hv2⟩
    · have := C.key3 φ ψ c hcφ hcψ h4 h2 h1 (hv3 ▸ w.inc_e4_v3) n4 (hv2 ▸ Or.symm w.h2) n2 w.inc_e1_v1
        w.e1_ne_e2.symm hb.2.symm (hi ▸ hb.1.symm)
      exact htri i _ this.1 this.2.1 (Or.inr this.2.2)
    · have := C.flip.key3 ψ φ c hcψ hcφ' h4 h2 h1 (show X.Inc w.e4 (C.w i) from hv3 ▸ w.inc_e4_v3) n4
        (show X.Joins w.e2 (C.y i) w.v1 from hv2 ▸ Or.symm w.h2) n2 w.inc_e1_v1 w.e1_ne_e2.symm hb.2.symm
        (hi ▸ hb.1.symm)
      exact htri i _ (C.flip_flip_Col.1 this.2.1) this.1 (Or.inl (C.flip_flip_Blk.1 this.2.2))
  exact C.glue_mid3 φ ψ c hφ hψ hcφ hcψ w h1 h2 h3 h4 c2 c3 hb

end Cut3

end cut3

end RH2F

-- ===== from III2.lean =====
/-
  III2.lean — Theorem 3CUT-MULTI (fact 4f30e30e4f4d4e99), part (B-M): the contraction `X/V_A` (side `A` contracted to
  a hub vertex `z`) as an edge set of `addHub X w` (a new vertex joined to `w 0, w 1, w 2` by three new edges), and the
  pole colouring of side `B` induced by a star colouring of the contraction.
-/

namespace RH2F
open MGraph
open Classical

section hub
variable {X : MGraph}

/-- `X` with a new vertex (index `X.n`) joined to `q 0`, `q 1`, `q 2` by three new edges (indices `X.m + t`) -/
def addHub (X : MGraph) (q : Fin 3 → Fin X.n) : MGraph where
  n := X.n + 1
  m := X.m + 3
  ends := fun e => if h : e.val < X.m then (Fin.castSucc (X.ends ⟨e.val, h⟩).1, Fin.castSucc (X.ends ⟨e.val, h⟩).2)
    else (Fin.last X.n, Fin.castSucc (q ⟨e.val - X.m, by have := e.isLt; omega⟩))

variable (q : Fin 3 → Fin X.n)

def hOld (d : Fin X.m) : Fin (addHub X q).m := ⟨d.val, by show d.val < X.m + 3; omega⟩
def hNew (t : Fin 3) : Fin (addHub X q).m := ⟨X.m + t.val, by show X.m + t.val < X.m + 3; omega⟩
def hub : Fin (addHub X q).n := Fin.last X.n
def hv (v : Fin X.n) : Fin (addHub X q).n := Fin.castSucc v

theorem hub_ends_old (d : Fin X.m) : (addHub X q).ends (hOld q d) = (hv q (X.ends d).1, hv q (X.ends d).2) := by
  simp [addHub, hOld, hv, d.isLt]
theorem hub_ends_new (t : Fin 3) : (addHub X q).ends (hNew q t) = (hub q, hv q (q t)) := by
  simp only [addHub, hNew, hub, hv]
  rw [dif_neg (by omega)]
  congr 3
  apply Fin.ext; simp

theorem hv_inj {a b : Fin X.n} (h : hv q a = hv q b) : a = b := by
  have := congrArg Fin.val h; simp [hv] at this; exact Fin.ext this
theorem hv_ne_hub (a : Fin X.n) : hv q a ≠ hub q := by
  intro h; have := congrArg Fin.val h; simp [hv, hub] at this; omega
theorem hOld_inj {d d' : Fin X.m} (h : hOld q d = hOld q d') : d = d' := by
  have := congrArg Fin.val h; simp [hOld] at this; exact Fin.ext this
theorem hNew_inj {t t' : Fin 3} (h : hNew q t = hNew q t') : t = t' := by
  have := congrArg Fin.val h; simp [hNew] at this; exact Fin.ext this
theorem hOld_ne_hNew (d : Fin X.m) (t : Fin 3) : hOld q d ≠ hNew q t := by
  intro h; have := congrArg Fin.val h; simp [hOld, hNew] at this; have := d.isLt; omega

theorem hub_cases (e : Fin (addHub X q).m) : (∃ d, e = hOld q d) ∨ ∃ t, e = hNew q t := by
  have he : e.val < X.m + 3 := e.isLt
  by_cases h : e.val < X.m
  · exact Or.inl ⟨⟨e.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨e.val - X.m, by omega⟩, Fin.ext (by simp [hNew]; omega)⟩

theorem hub_inc_old {d : Fin X.m} {v : Fin X.n} : (addHub X q).Inc (hOld q d) (hv q v) ↔ X.Inc d v := by
  unfold Inc; rw [hub_ends_old]
  constructor
  · rintro (h | h)
    · exact Or.inl (hv_inj q h)
    · exact Or.inr (hv_inj q h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
theorem hub_not_inc_old {d : Fin X.m} : ¬ (addHub X q).Inc (hOld q d) (hub q) := by
  unfold Inc; rw [hub_ends_old]
  rintro (h | h)
  · exact hv_ne_hub q _ h
  · exact hv_ne_hub q _ h
theorem hub_joins_old {d : Fin X.m} {u u' : Fin X.n} (h : X.Joins d u u') :
    (addHub X q).Joins (hOld q d) (hv q u) (hv q u') := by
  rcases h with h | h
  · left; rw [hub_ends_old, h]
  · right; rw [hub_ends_old, h]
theorem hub_inc_new_hub (t : Fin 3) : (addHub X q).Inc (hNew q t) (hub q) := by
  unfold Inc; rw [hub_ends_new]; exact Or.inl rfl
theorem hub_inc_new {t : Fin 3} {v : Fin X.n} : (addHub X q).Inc (hNew q t) (hv q v) ↔ q t = v := by
  unfold Inc; rw [hub_ends_new]
  constructor
  · rintro (h | h)
    · exact absurd h.symm (hv_ne_hub q v)
    · exact hv_inj q h
  · intro h; exact Or.inr (by rw [h])

end hub

section contr
variable {X : MGraph} {P : Fin X.m → Prop}

namespace Cut3
variable (C : Cut3 P)

/-- the contraction `X/V_A`: side `A` contracted to the hub, i.e. the edges inside `B` and the hub edges `z w_t` -/
def cont : Fin (addHub X C.w).m → Prop :=
  fun e => (∃ d, e = hOld C.w d ∧ C.flip.inA d) ∨ ∃ t, e = hNew C.w t

/-- the edges of `X` to the edges of the contraction: `e_t ↦ z w_t` -/
noncomputable def toCont (f : Fin X.m) : Fin (addHub X C.w).m :=
  if h : ∃ t, f = C.e t then hNew C.w (Classical.choose h) else hOld C.w f

theorem toCont_e (t : Fin 3) : C.toCont (C.e t) = hNew C.w t := by
  have h : ∃ t', C.e t = C.e t' := ⟨t, rfl⟩
  simp only [toCont, dif_pos h]
  rw [C.einj _ _ (Classical.choose_spec h).symm]
theorem toCont_old {f : Fin X.m} (h : ¬ C.isCut f) : C.toCont f = hOld C.w f := by
  simp only [toCont]; rw [dif_neg (show ¬ ∃ t, f = C.e t from h)]

/-- vertices of `X` to vertices of the contraction: side `A` to the hub -/
def toV (v : Fin X.n) : Fin (addHub X C.w).n := if C.S v = true then hub C.w else hv C.w v

theorem toV_B {v : Fin X.n} (h : C.S v = false) : C.toV v = hv C.w v := by simp [toV, h]
theorem toV_A {v : Fin X.n} (h : C.S v = true) : C.toV v = hub C.w := by simp [toV, h]

theorem flip_pole_cases {f : Fin X.m} (h : C.flip.pole f) : C.flip.inA f ∨ ∃ t, f = C.e t := h

theorem toCont_mem {f : Fin X.m} (h : C.flip.pole f) : C.cont (C.toCont f) := by
  rcases h with h | ⟨t, ht⟩
  · rw [C.toCont_old (C.flip.not_inA_of_cut · h)]; exact Or.inl ⟨f, rfl, h⟩
  · have ht' : f = C.e t := ht
    rw [ht', C.toCont_e]; exact Or.inr ⟨t, rfl⟩

theorem toCont_joins {f : Fin X.m} (h : C.flip.pole f) :
    (addHub X C.w).Joins (C.toCont f) (C.toV (X.ends f).1) (C.toV (X.ends f).2) := by
  rcases h with h | ⟨t, ht⟩
  · have s1 : C.S (X.ends f).1 = false := by have := h.2.1; rw [flip_S] at this; simpa using this
    have s2 : C.S (X.ends f).2 = false := by have := h.2.2; rw [flip_S] at this; simpa using this
    rw [C.toCont_old (C.flip.not_inA_of_cut · h), C.toV_B s1, C.toV_B s2]
    exact Or.inl (hub_ends_old C.w f)
  · have ht' : f = C.e t := ht
    rw [ht', C.toCont_e]
    rcases C.hj t with h' | h' <;> rw [h'] <;> simp only [C.toV_A (C.sy t), C.toV_B (C.sw t)]
    · exact Or.inl (hub_ends_new C.w t)
    · exact Or.inr (hub_ends_new C.w t)

theorem toCont_inj {f g : Fin X.m} (h : C.toCont f = C.toCont g) : f = g := by
  by_cases hf : C.isCut f <;> by_cases hg : C.isCut g
  · obtain ⟨t, rfl⟩ := hf; obtain ⟨t', rfl⟩ := hg
    rw [C.toCont_e, C.toCont_e] at h; rw [hNew_inj C.w h]
  · obtain ⟨t, rfl⟩ := hf
    rw [C.toCont_e, C.toCont_old hg] at h; exact absurd h.symm (hOld_ne_hNew _ _ _)
  · obtain ⟨t', rfl⟩ := hg
    rw [C.toCont_e, C.toCont_old hf] at h; exact absurd h (hOld_ne_hNew _ _ _)
  · rw [C.toCont_old hf, C.toCont_old hg] at h; exact hOld_inj C.w h

/-- a vertex of side `A` meets at most one edge of the pole of side `B` -/
theorem flip_pole_A {f g : Fin X.m} {x : Fin X.n} (hf : C.flip.pole f) (hg : C.flip.pole g) (hfx : X.Inc f x)
    (hgx : X.Inc g x) (hx : C.S x = true) : f = g := by
  have cutA : ∀ h, C.flip.pole h → X.Inc h x → ∃ t, h = C.e t ∧ x = C.y t := by
    intro h hh hhx
    rcases hh with hh | ⟨t, rfl⟩
    · have := C.flip.side_of_inA hh hhx; rw [flip_S, hx] at this; exact absurd this (by decide)
    · rcases inc_of_joins (C.hj t) hhx with h' | h'
      · exact ⟨t, rfl, h'⟩
      · rw [h', C.sw t] at hx; exact absurd hx (by decide)
  obtain ⟨t, rfl, hxt⟩ := cutA f hf hfx
  obtain ⟨t', rfl, hxt'⟩ := cutA g hg hgx
  rw [C.yinj _ _ (hxt.symm.trans hxt')]

theorem toV_ne {u v : Fin X.n} (hu : C.S u = false) (hne : u ≠ v) : C.toV u ≠ C.toV v := by
  rw [C.toV_B hu]
  by_cases hv' : C.S v = true
  · rw [C.toV_A hv']; exact hv_ne_hub _ _
  · rw [C.toV_B (by simpa using hv')]; exact fun h => hne (hv_inj _ h)

/-- **3CUT-MULTI (B-M)**, first part: a star colouring `c` of the contraction gives the star colouring `c ∘ toCont`
    of the pole of side `B` -/
theorem pole_of_cont {k : Nat} (c : Fin (addHub X C.w).m → Fin k) (hc : StarOn C.cont k c) :
    StarOn C.flip.pole k (fun f => c (C.toCont f)) := by
  constructor
  · rintro a b ⟨hab, x, hax, hbx⟩ ha hb heq
    have hxB : C.S x = false := by
      cases hs : C.S x
      · rfl
      · exact absurd (C.flip_pole_A ha hb hax hbx hs) hab
    have ja := C.toCont_joins ha
    have jb := C.toCont_joins hb
    refine hc.1 _ _ ⟨fun h => hab (C.toCont_inj h), C.toV x, ?_, ?_⟩ (C.toCont_mem ha) (C.toCont_mem hb) heq
    · rcases hax with h | h <;> rw [← h]
      · exact joins_inc_left ja
      · exact joins_inc_right ja
    · rcases hbx with h | h <;> rw [← h]
      · exact joins_inc_left jb
      · exact joins_inc_right jb
  · intro w h1 h2 h3 h4 hb
    -- the inner vertices lie in side `B`
    have inB : ∀ {f g : Fin X.m} {x : Fin X.n}, C.flip.pole f → C.flip.pole g → f ≠ g → X.Inc f x → X.Inc g x →
        C.S x = false := by
      intro f g x hf hg hne hfx hgx
      cases hs : C.S x
      · rfl
      · exact absurd (C.flip_pole_A hf hg hfx hgx hs) hne
    have b1 := inB h1 h2 w.e1_ne_e2 w.inc_e1_v1 w.inc_e2_v1
    have b2 := inB h2 h3 w.e2_ne_e3 w.inc_e2_v2 w.inc_e3_v2
    have b3 := inB h3 h4 w.e3_ne_e4 w.inc_e3_v3 w.inc_e4_v3
    have jw : ∀ {f : Fin X.m} {u u' : Fin X.n}, C.flip.pole f → X.Joins f u u' →
        (addHub X C.w).Joins (C.toCont f) (C.toV u) (C.toV u') := by
      intro f u u' hf hj
      have := C.toCont_joins hf
      rcases joins_unique hj (joins_ends f) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> rw [h1', h2']
      · exact this
      · exact Or.symm this
    let w' : (addHub X C.w).Walk4 :=
      { v0 := C.toV w.v0, v1 := C.toV w.v1, v2 := C.toV w.v2, v3 := C.toV w.v3, v4 := C.toV w.v4,
        e1 := C.toCont w.e1, e2 := C.toCont w.e2, e3 := C.toCont w.e3, e4 := C.toCont w.e4,
        h1 := jw h1 w.h1, h2 := jw h2 w.h2, h3 := jw h3 w.h3, h4 := jw h4 w.h4,
        d01 := fun h => C.toV_ne b1 w.d01.symm h.symm
        d02 := fun h => C.toV_ne b2 w.d02.symm h.symm
        d03 := fun h => C.toV_ne b3 w.d03.symm h.symm
        d12 := C.toV_ne b1 w.d12
        d13 := C.toV_ne b1 w.d13
        d14 := C.toV_ne b1 w.d14
        d23 := C.toV_ne b2 w.d23
        d24 := C.toV_ne b2 w.d24
        d34 := C.toV_ne b3 w.d34 }
    exact hc.2 w' (C.toCont_mem h1) (C.toCont_mem h2) (C.toCont_mem h3) (C.toCont_mem h4) hb

/-- **(B-M)**: the three hub colours are pairwise distinct -/
theorem hub_distinct {k : Nat} (c : Fin (addHub X C.w).m → Fin k) (hc : StarOn C.cont k c) {t t' : Fin 3}
    (h : c (hNew C.w t) = c (hNew C.w t')) : t = t' := by
  apply Classical.byContradiction
  intro hne
  exact hc.1 _ _ ⟨fun h' => hne (hNew_inj _ h'), hub C.w, hub_inc_new_hub _ t, hub_inc_new_hub _ t'⟩
    (Or.inr ⟨t, rfl⟩) (Or.inr ⟨t', rfl⟩) h


/-- an edge inside `B` corresponds to the old edge of the contraction -/
theorem toCont_flip_inA {f : Fin X.m} (h : C.flip.inA f) : C.toCont f = hOld C.w f :=
  C.toCont_old (C.flip.not_inA_of_cut · h)

theorem flip_inA_hv {f : Fin X.m} {x : Fin X.n} (h : C.flip.inA f) (hx : X.Inc f x) :
    (addHub X C.w).Inc (hOld C.w f) (hv C.w x) := (hub_inc_old C.w).2 hx

/-- **(B-M)**: no hub colour is blocking at any port of the pole of side `B` -/
theorem cont_noBlk (hloop : Loopless X) (c : Fin (addHub X C.w).m → Fin 6) (hc : StarOn C.cont 6 c)
    (i j : Fin 3) : ¬ C.flip.Blk (fun f => c (C.toCont f)) i (c (hNew C.w j)) := by
  rintro ⟨f, r, hfB, hj0, hfc0, f', hf'p, hf'f, hf'r, hf'c0⟩
  have hψ := C.pole_of_cont c hc
  have ce : ∀ t, c (C.toCont (C.e t)) = c (hNew C.w t) := fun t => by rw [C.toCont_e]
  have hj : X.Joins f (C.w i) r := hj0
  have hfc : c (C.toCont f) = c (hNew C.w j) := hfc0
  have hf'c : c (C.toCont f') = c (hNew C.w i) := by
    have : c (C.toCont f') = c (C.toCont (C.e i)) := hf'c0
    rw [this, ce]
  have hfw : X.Inc f (C.w i) := joins_inc_left hj
  have hrB : C.S r = false := by
    have := C.flip.side_of_inA hfB (joins_inc_right hj); rw [flip_S] at this; simpa using this
  have hrw : r ≠ C.w i := fun h => ne_of_joins' hloop hj h.symm
  by_cases hij : j = i
  · subst hij
    apply hψ.1 f (C.e j) ⟨fun h => C.flip.not_inA_of_cut ⟨j, h⟩ hfB, C.w j, hfw, joins_inc_right (C.hj j)⟩
      (Or.inl hfB) (Or.inr ⟨j, rfl⟩)
    show c (C.toCont f) = c (C.toCont (C.e j)); rw [hfc, ce]
  · have hf'B : C.flip.inA f' := by
      rcases hf'p with h | ⟨t, ht⟩
      · exact h
      · exfalso
        have ht' : f' = C.e t := ht
        rw [ht'] at hf'r hf'c
        have := C.hub_distinct c hc ((ce t).symm.trans hf'c)
        subst this
        rcases inc_of_joins (C.hj t) hf'r with h | h
        · rw [h, C.sy t] at hrB; exact absurd hrB (by decide)
        · exact hrw h
    obtain ⟨r', hj'⟩ : ∃ r', X.Joins f' r r' := ⟨other f' r, joins_other hf'r⟩
    have hr'r : r' ≠ r := fun h => ne_of_joins' hloop hj' h.symm
    have hr'w : r' ≠ C.w i := by
      intro h
      rw [h] at hj'
      apply hψ.1 f' (C.e i) ⟨fun h' => C.flip.not_inA_of_cut ⟨i, h'⟩ hf'B, C.w i, joins_inc_right hj',
        joins_inc_right (C.hj i)⟩ (Or.inl hf'B) (Or.inr ⟨i, rfl⟩)
      show c (C.toCont f') = c (C.toCont (C.e i)); rw [hf'c, ce]
    have hrwj : r ≠ C.w j := by
      intro h
      rw [h] at hj
      apply hc.1 (hOld C.w f) (hNew C.w j) ⟨hOld_ne_hNew _ _ _, hv C.w (C.w j), C.flip_inA_hv hfB
        (joins_inc_right hj), (hub_inc_new _).2 rfl⟩ (Or.inl ⟨f, rfl, hfB⟩) (Or.inr ⟨j, rfl⟩)
      rw [← C.toCont_flip_inA hfB]; exact hfc
    have hwij : C.w i ≠ C.w j := fun h => hij (C.winj _ _ h).symm
    let W : (addHub X C.w).Walk4 :=
      { v0 := hv C.w r', v1 := hv C.w r, v2 := hv C.w (C.w i), v3 := hub C.w, v4 := hv C.w (C.w j),
        e1 := hOld C.w f', e2 := hOld C.w f, e3 := hNew C.w i, e4 := hNew C.w j,
        h1 := hub_joins_old C.w (Or.symm hj')
        h2 := hub_joins_old C.w (Or.symm hj)
        h3 := Or.inr (hub_ends_new C.w i)
        h4 := Or.inl (hub_ends_new C.w j)
        d01 := fun h => hr'r (hv_inj _ h)
        d02 := fun h => hr'w (hv_inj _ h)
        d03 := hv_ne_hub _ _
        d12 := fun h => hrw (hv_inj _ h)
        d13 := hv_ne_hub _ _
        d14 := fun h => hrwj (hv_inj _ h)
        d23 := hv_ne_hub _ _
        d24 := fun h => hwij (hv_inj _ h)
        d34 := fun h => hv_ne_hub _ _ h.symm }
    refine hc.2 W (Or.inl ⟨f', rfl, hf'B⟩) (Or.inl ⟨f, rfl, hfB⟩) (Or.inr ⟨i, rfl⟩) (Or.inr ⟨j, rfl⟩) ⟨?_, ?_⟩
    · show c (hOld C.w f') = c (hNew C.w i)
      rw [← C.toCont_flip_inA hf'B]; exact hf'c
    · show c (hOld C.w f) = c (hNew C.w j)
      rw [← C.toCont_flip_inA hfB]; exact hfc

/-- **(B-M)**, cross condition: for `i ≠ j`, not both `a_j ∈ Col_i` and `a_i ∈ Col_j` -/
theorem cont_cross (hloop : Loopless X) (c : Fin (addHub X C.w).m → Fin 6) (hc : StarOn C.cont 6 c)
    {i j : Fin 3} (hij : i ≠ j) :
    ¬ (C.flip.Col (fun f => c (C.toCont f)) i (c (hNew C.w j)) ∧
      C.flip.Col (fun f => c (C.toCont f)) j (c (hNew C.w i))) := by
  rintro ⟨⟨f, hfB, hfw, hfc0⟩, ⟨h, hhB, hhw, hhc0⟩⟩
  have hfw' : X.Inc f (C.w i) := hfw
  have hhw' : X.Inc h (C.w j) := hhw
  have hfc : c (hOld C.w f) = c (hNew C.w j) := by rw [← C.toCont_flip_inA hfB]; exact hfc0
  have hhc : c (hOld C.w h) = c (hNew C.w i) := by rw [← C.toCont_flip_inA hhB]; exact hhc0
  obtain ⟨r, hjf⟩ : ∃ r, X.Joins f r (C.w i) := ⟨other f (C.w i), Or.symm (joins_other hfw')⟩
  obtain ⟨r', hjh⟩ : ∃ r', X.Joins h (C.w j) r' := ⟨other h (C.w j), joins_other hhw'⟩
  have hwij : C.w i ≠ C.w j := fun h' => hij (C.winj _ _ h')
  have hrw : r ≠ C.w i := ne_of_joins' hloop hjf
  have hr'w : r' ≠ C.w j := fun h' => ne_of_joins' hloop hjh h'.symm
  have hrwj : r ≠ C.w j := by
    intro h'
    rw [h'] at hjf
    exact hc.1 (hOld C.w f) (hNew C.w j) ⟨hOld_ne_hNew _ _ _, hv C.w (C.w j), C.flip_inA_hv hfB
      (joins_inc_left hjf), (hub_inc_new _).2 rfl⟩ (Or.inl ⟨f, rfl, hfB⟩) (Or.inr ⟨j, rfl⟩) hfc
  have hr'wi : r' ≠ C.w i := by
    intro h'
    rw [h'] at hjh
    exact hc.1 (hOld C.w h) (hNew C.w i) ⟨hOld_ne_hNew _ _ _, hv C.w (C.w i), C.flip_inA_hv hhB
      (joins_inc_right hjh), (hub_inc_new _).2 rfl⟩ (Or.inl ⟨h, rfl, hhB⟩) (Or.inr ⟨i, rfl⟩) hhc
  let W : (addHub X C.w).Walk4 :=
    { v0 := hv C.w r, v1 := hv C.w (C.w i), v2 := hub C.w, v3 := hv C.w (C.w j), v4 := hv C.w r',
      e1 := hOld C.w f, e2 := hNew C.w i, e3 := hNew C.w j, e4 := hOld C.w h,
      h1 := hub_joins_old C.w hjf
      h2 := Or.inr (hub_ends_new C.w i)
      h3 := Or.inl (hub_ends_new C.w j)
      h4 := hub_joins_old C.w hjh
      d01 := fun h' => hrw (hv_inj _ h')
      d02 := hv_ne_hub _ _
      d03 := fun h' => hrwj (hv_inj _ h')
      d12 := hv_ne_hub _ _
      d13 := fun h' => hwij (hv_inj _ h')
      d14 := fun h' => hr'wi (hv_inj _ h').symm
      d23 := fun h' => hv_ne_hub _ _ h'.symm
      d24 := fun h' => hv_ne_hub _ _ h'.symm
      d34 := fun h' => hr'w (hv_inj _ h').symm }
  exact hc.2 W (Or.inl ⟨f, rfl, hfB⟩) (Or.inr ⟨i, rfl⟩) (Or.inr ⟨j, rfl⟩) (Or.inl ⟨h, rfl, hhB⟩) ⟨hfc, hhc.symm⟩

end Cut3

end contr

end RH2F

-- ===== from III3.lean =====
/-
  III3.lean — poles of a vertex, outside data, (D1) (facts 87fba73118e1699c, 82bc44210c5765d5), and the MC gluing
  across a 3-edge-cut with the outside datum read off an MC colouring of the contraction (3CUT-MULTI (MC-M), (B-M),
  fact 4f30e30e4f4d4e99).  Colour `6` of the prose is `5 : Fin 6`.
-/

namespace RH2F
open MGraph
open Classical

/-! ### MC colourings -/

section mc
variable {X : MGraph}

/-- `c` is an MC colouring of the edge set `P`: a star 6-colouring whose colour class `5` is a perfect matching -/
def MCol (P : Fin X.m → Prop) (c : Fin X.m → Fin 6) : Prop :=
  StarOn P 6 c ∧ ∀ x, meets P x → ∃ a, P a ∧ X.Inc a x ∧ c a = 5 ∧ ∀ b, P b → X.Inc b x → c b = 5 → b = a

end mc

/-! ### poles of a vertex -/

section vpole
variable {Y : MGraph}

/-- the three edges at `v`, joining `v` to three pairwise distinct vertices -/
structure Ports (Q : Fin Y.m → Prop) (v : Fin Y.n) where
  p : Fin 3 → Fin Y.m
  x : Fin 3 → Fin Y.n
  hp : ∀ t, Q (p t)
  hj : ∀ t, Y.Joins (p t) v (x t)
  xinj : ∀ s t, x s = x t → s = t
  pinj : ∀ s t, p s = p t → s = t
  all : ∀ f, Q f → Y.Inc f v → ∃ t, f = p t

variable {Q : Fin Y.m → Prop} {v : Fin Y.n}

/-- the ambient of the pole `Q(Y, v)`: `Y` with three new vertices `o t` (index `Y.n + t`); the port edge `p t` is
    redirected to join `x t` and `o t`; all other edges keep their ends -/
noncomputable def splitV (D : Ports Q v) : MGraph where
  n := Y.n + 3
  m := Y.m
  ends := fun f => if h : ∃ t, f = D.p t then (Fin.castAdd 3 (D.x (Classical.choose h)),
      Fin.natAdd Y.n (Classical.choose h)) else (Fin.castAdd 3 (Y.ends f).1, Fin.castAdd 3 (Y.ends f).2)

/-- the edge set of the pole `Q(Y, v)`: the edges of `Q` not at `v`, and the three port edges -/
def vPole (D : Ports Q v) : Fin Y.m → Prop := fun f => (Q f ∧ ¬ Y.Inc f v) ∨ ∃ t, f = D.p t

/-- an MC pole colouring: a star 6-colouring of the pole in which every vertex of `Y − v` meeting `Q` meets exactly
    one pole edge of colour `5` -/
def MCPole (D : Ports Q v) (d : Fin Y.m → Fin 6) : Prop :=
  StarOn (G := splitV D) (@vPole Y Q v D) 6 d ∧ ∀ x, x ≠ v → meets Q x →
    ∃ a, vPole D a ∧ (splitV D).Inc a (Fin.castAdd 3 x) ∧ d a = 5 ∧
      ∀ b, vPole D b → (splitV D).Inc b (Fin.castAdd 3 x) → d b = 5 → b = a

/-- `Col_t(d)`: the colours of the pole edges other than `p t` at `x t` -/
def vCol (D : Ports Q v) (d : Fin Y.m → Fin 6) (t : Fin 3) (κ : Fin 6) : Prop :=
  ∃ f, vPole D f ∧ f ≠ D.p t ∧ (splitV D).Inc f (Fin.castAdd 3 (D.x t)) ∧ d f = κ

/-- `Blk_t(d)`: the colours of those edges `f = x_t r` (pole edges other than `p t`) for which `r` meets another pole
    edge of the colour of `p t` -/
def vBlk (D : Ports Q v) (d : Fin Y.m → Fin 6) (t : Fin 3) (κ : Fin 6) : Prop :=
  ∃ f r, vPole D f ∧ f ≠ D.p t ∧ (splitV D).Joins f (Fin.castAdd 3 (D.x t)) r ∧ d f = κ ∧
    ∃ f', vPole D f' ∧ f' ≠ f ∧ (splitV D).Inc f' r ∧ d f' = d (D.p t)

end vpole

/-! ### outside data -/

/-- `S` is a 2-set -/
def Two (S : Fin 6 → Prop) : Prop := ∃ α β, α ≠ β ∧ ∀ κ, S κ ↔ κ = α ∨ κ = β

/-- an admissible outside datum at M-port `i` (conditions (O1)–(O3); colour `6` is `5`) -/
def Admissible (i : Fin 3) (a : Fin 3 → Fin 6) (O B : Fin 3 → Fin 6 → Prop) : Prop :=
  (∀ s t, a s = a t → s = t) ∧ a i = 5 ∧ (∀ t, Two (O t)) ∧ (∀ t κ, B t κ → O t κ) ∧
  -- (O1)
  (∀ κ, O i κ → κ ≠ 5 ∧ ∀ t, t ≠ i → κ ≠ a t) ∧ (∀ κ, B i κ ↔ O i κ) ∧
  -- (O2)
  (∀ t, t ≠ i → O t 5 ∧ ¬ O t (a t) ∧ ∀ κ, B t κ → κ ≠ 5 ∧ ∀ s, s ≠ i → κ ≠ a s) ∧
  -- (O3)
  (∀ j k, j ≠ i → k ≠ i → j ≠ k → ¬ (O j (a k) ∧ O k (a j)))

section d1
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n}

/-- `d` is compatible with the datum -/
def Compat (D : Ports Q v) (d : Fin Y.m → Fin 6) (a : Fin 3 → Fin 6) (O B : Fin 3 → Fin 6 → Prop) : Prop :=
  (∀ t, d (D.p t) = a t) ∧ ∀ t κ, vCol D d t κ → O t κ → (vBlk D d t κ ∨ B t κ) → False

/-- the pole `Q(Y, v)` satisfies (D1) at port `i` -/
def D1 (D : Ports Q v) (i : Fin 3) : Prop :=
  ∀ a O B, Admissible i a O B → ∃ d, MCPole D d ∧ Compat D d a O B

end d1

/-! ### the MC gluing across a 3-edge-cut -/

section mcglue
variable {X : MGraph} {P : Fin X.m → Prop}

namespace Cut3
variable (C : Cut3 P)

/-- at a cut end `w t` with three edges there are exactly two edges inside `B` -/
theorem pairB {t : Fin 3} (h3 : CubicAt P (C.w t)) :
    ∃ f f', f ≠ f' ∧ C.flip.inA f ∧ C.flip.inA f' ∧ X.Inc f (C.w t) ∧ X.Inc f' (C.w t) ∧
      ∀ g, C.flip.inA g → X.Inc g (C.w t) → g = f ∨ g = f' := by
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := h3
  have hPe : P (C.e t) := C.hP t
  have he : X.Inc (C.e t) (C.w t) := joins_inc_right (C.hj t)
  have nc : ∀ g, P g → X.Inc g (C.w t) → g ≠ C.e t → C.flip.inA g := fun g hg hgw hne =>
    C.flip.inA_at_y hg hgw hne
  have ncut : ∀ g, C.flip.inA g → g ≠ C.e t := fun g hg h => C.flip.not_inA_of_cut ⟨t, h⟩ hg
  rcases hall (C.e t) hPe he with h | h | h
  · rw [← h] at dpq dpr
    refine ⟨q, r, dqr, nc q hq iq (Ne.symm dpq), nc r hr ir (Ne.symm dpr), iq, ir, fun g hg hgw => ?_⟩
    rcases hall g hg.1 hgw with h' | h' | h'
    · exact absurd (h'.trans h.symm) (ncut g hg)
    · exact Or.inl h'
    · exact Or.inr h'
  · rw [← h] at dpq dqr
    refine ⟨p, r, dpr, nc p hp ip dpq, nc r hr ir (Ne.symm dqr), ip, ir, fun g hg hgw => ?_⟩
    rcases hall g hg.1 hgw with h' | h' | h'
    · exact Or.inl h'
    · exact absurd (h'.trans h.symm) (ncut g hg)
    · exact Or.inr h'
  · rw [← h] at dpr dqr
    refine ⟨p, q, dpq, nc p hp ip dpr, nc q hq iq dqr, ip, iq, fun g hg hgw => ?_⟩
    rcases hall g hg.1 hgw with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd (h'.trans h.symm) (ncut g hg)

/-- the edges of the contraction at an old vertex `x` of side `B` come from pole edges of side `B` at `x` -/
theorem cont_at {a : Fin (addHub X C.w).m} {x : Fin X.n} (ha : C.cont a) (hax : (addHub X C.w).Inc a (hv C.w x)) :
    ∃ f, C.flip.pole f ∧ X.Inc f x ∧ a = C.toCont f := by
  rcases ha with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩
  · exact ⟨d, Or.inl hd, (hub_inc_old C.w).1 hax, (C.toCont_flip_inA hd).symm⟩
  · have := (hub_inc_new C.w).1 hax
    exact ⟨C.e t, Or.inr ⟨t, rfl⟩, by rw [← this]; exact joins_inc_right (C.hj t), (C.toCont_e t).symm⟩

/-- the outside datum read off a colouring `c` of the contraction: port colours `a t = c(z w_t)`, sets `O t = Col_t`,
    `B t = Blk_t` of the pole colouring `c ∘ toCont` of side `B` -/
noncomputable def datA (c : Fin (addHub X C.w).m → Fin 6) (t : Fin 3) : Fin 6 := c (hNew C.w t)
def datO (c : Fin (addHub X C.w).m → Fin 6) (t : Fin 3) (κ : Fin 6) : Prop := C.flip.Col (fun f => c (C.toCont f)) t κ
def datB (c : Fin (addHub X C.w).m → Fin 6) (t : Fin 3) (κ : Fin 6) : Prop := C.flip.Blk (fun f => c (C.toCont f)) t κ

/-- **the datum of an MC colouring of the contraction is admissible** at the port of colour `5` -/
theorem dat_admissible (hloop : Loopless X) (hw : ∀ t, CubicAt P (C.w t)) (c : Fin (addHub X C.w).m → Fin 6)
    (hc : MCol C.cont c) {i : Fin 3} (hi : c (hNew C.w i) = 5) :
    Admissible i (C.datA c) (C.datO c) (C.datB c) := by
  have hst := hc.1
  have hψ := C.pole_of_cont c hst
  have ce : ∀ t, c (C.toCont (C.e t)) = c (hNew C.w t) := fun t => by rw [C.toCont_e]
  -- colours at `w t` avoid the hub colour `a t`
  have proper_w : ∀ t f, C.flip.inA f → X.Inc f (C.w t) → c (C.toCont f) ≠ c (hNew C.w t) := by
    intro t f hf hfw h
    rw [C.toCont_flip_inA hf] at h
    exact hst.1 (hOld C.w f) (hNew C.w t) ⟨hOld_ne_hNew _ _ _, hv C.w (C.w t), C.flip_inA_hv hf hfw,
      (hub_inc_new _).2 rfl⟩ (Or.inl ⟨f, rfl, hf⟩) (Or.inr ⟨t, rfl⟩) h
  -- every `w t` with `t ≠ i` has an edge of colour 5 inside `B`
  have five_at : ∀ t, t ≠ i → C.datO c t 5 := by
    intro t hti
    obtain ⟨a, ha, hax, ha5, _⟩ := hc.2 (hv C.w (C.w t)) ⟨hNew C.w t, Or.inr ⟨t, rfl⟩, (hub_inc_new _).2 rfl⟩
    obtain ⟨f, hfp, hfx, rfl⟩ := C.cont_at ha hax
    rcases hfp with hf | ⟨s, hs⟩
    · exact ⟨f, hf, hfx, ha5⟩
    · exfalso
      have hs' : f = C.e s := hs
      subst hs'
      have hst' : s = t := C.cut_at_w hfx
      subst hst'
      rw [ce] at ha5
      exact hti (C.hub_distinct c hst (ha5.trans hi.symm))
  have two : ∀ t, Two (C.datO c t) := by
    intro t
    obtain ⟨f, f', hne, hf, hf', i1, i2, hall⟩ := C.pairB (hw t)
    refine ⟨c (C.toCont f), c (C.toCont f'), fun h => hψ.1 f f' ⟨hne, C.w t, i1, i2⟩ (Or.inl hf) (Or.inl hf') h,
      fun κ => ⟨?_, ?_⟩⟩
    · rintro ⟨g, hg, hgw, rfl⟩
      rcases hall g hg hgw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨f, hf, i1, rfl⟩
      · exact ⟨f', hf', i2, rfl⟩
  have BO : ∀ t κ, C.datB c t κ → C.datO c t κ := by
    rintro t κ ⟨f, r, hf, hj, hfc, _⟩
    exact ⟨f, hf, joins_inc_left hj, hfc⟩
  have O1a : ∀ κ, C.datO c i κ → κ ≠ 5 ∧ ∀ t, t ≠ i → κ ≠ C.datA c t := by
    intro κ hκ
    refine ⟨?_, fun t hti h => ?_⟩
    · obtain ⟨f, hf, hfw, rfl⟩ := hκ
      rw [← hi]; exact proper_w i f hf hfw
    · have h1 : C.datO c i (C.datA c t) := h ▸ hκ
      have h2 : C.datO c t (C.datA c i) := by
        show C.datO c t (c (hNew C.w i)); rw [hi]; exact five_at t hti
      exact C.cont_cross hloop c hst (Ne.symm hti) ⟨h1, h2⟩
  have O1b : ∀ κ, C.datB c i κ ↔ C.datO c i κ := by
    intro κ
    refine ⟨BO i κ, fun h => ?_⟩
    obtain ⟨f, hf, hfw, rfl⟩ := h
    have hfw' : X.Inc f (C.w i) := hfw
    obtain ⟨r, hjr⟩ : ∃ r, X.Joins f (C.w i) r := ⟨other f (C.w i), joins_other hfw'⟩
    obtain ⟨a, ha, hax, ha5, _⟩ := hc.2 (hv C.w r) ⟨hOld C.w f, Or.inl ⟨f, rfl, hf⟩,
      C.flip_inA_hv hf (joins_inc_right hjr)⟩
    obtain ⟨f', hf'p, hf'r, rfl⟩ := C.cont_at ha hax
    refine ⟨f, r, hf, hjr, rfl, f', hf'p, fun h => ?_, hf'r, ?_⟩
    · subst h
      exact proper_w i f' hf hfw (ha5.trans hi.symm)
    · show c (C.toCont f') = c (C.toCont (C.e i)); rw [ha5, ce, hi]
  have O2 : ∀ t, t ≠ i → C.datO c t 5 ∧ ¬ C.datO c t (C.datA c t) ∧
      ∀ κ, C.datB c t κ → κ ≠ 5 ∧ ∀ s, s ≠ i → κ ≠ C.datA c s := by
    intro t hti
    refine ⟨five_at t hti, ?_, fun κ hκ => ⟨?_, fun s _ => ?_⟩⟩
    · rintro ⟨f, hf, hfw, hfc⟩
      exact proper_w t f hf hfw hfc
    · rintro rfl
      exact C.cont_noBlk hloop c hst t i (hi ▸ hκ)
    · rintro rfl
      exact C.cont_noBlk hloop c hst t s hκ
  have O3 : ∀ j k, j ≠ i → k ≠ i → j ≠ k → ¬ (C.datO c j (C.datA c k) ∧ C.datO c k (C.datA c j)) :=
    fun j k _ _ hjk h => C.cont_cross hloop c hst hjk ⟨h.1, h.2⟩
  exact ⟨fun s t h => C.hub_distinct c hst h, hi, two, BO, O1a, O1b, O2, O3⟩

/-- **MC gluing across a 3-edge-cut** (3CUT-MULTI (MC-M), direction ⇐): an MC colouring `c` of the contraction and
    a star colouring `φ` of the pole of side `A` that is MC on side `A`, agrees with the hub colours on the cut edges,
    and is compatible with the datum of `c`, glue to an MC colouring of `P` -/
theorem mc_glue (c : Fin (addHub X C.w).m → Fin 6) (hc : MCol C.cont c) (φ : Fin X.m → Fin 6)
    (hφ : StarOn C.pole 6 φ) (hφA : ∀ x, C.S x = true → meets P x →
      ∃ a, C.pole a ∧ X.Inc a x ∧ φ a = 5 ∧ ∀ b, C.pole b → X.Inc b x → φ b = 5 → b = a)
    (hφe : ∀ t, φ (C.e t) = C.datA c t)
    (hcomp : ∀ t κ, C.Col φ t κ → C.datO c t κ → (C.Blk φ t κ ∨ C.datB c t κ) → False) :
    ∃ c', MCol P c' := by
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
  refine ⟨c', hstar, fun x hx => ?_⟩
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

end Cut3

end mcglue

end RH2F

-- ===== from III4.lean =====
/-
  III4.lean — the pole `Q(X/V_B, z)` of the contraction of side `B` at its hub is the pole `Q1` of side `A`: an MC pole
  colouring of it compatible with a datum gives the colouring of `Q1` needed for the MC gluing (facts 87fba73118e1699c,
  82bc44210c5765d5).
-/

namespace RH2F
open MGraph
open Classical

section splitv
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n} (D : Ports Q v)

theorem splitV_ends_port (t : Fin 3) :
    (splitV D).ends (D.p t) = (Fin.castAdd 3 (D.x t), Fin.natAdd Y.n t) := by
  have h : ∃ t', D.p t = D.p t' := ⟨t, rfl⟩
  simp only [splitV, dif_pos h]
  rw [D.pinj _ _ (Classical.choose_spec h).symm]

theorem splitV_ends_other {f : Fin Y.m} (h : ¬ ∃ t, f = D.p t) :
    (splitV D).ends f = (Fin.castAdd 3 (Y.ends f).1, Fin.castAdd 3 (Y.ends f).2) := by
  simp only [splitV, dif_neg h]

end splitv

section hubpole
variable {X : MGraph} {P : Fin X.m → Prop}

namespace Cut3
variable (C : Cut3 P)

/-- the ports of the contraction of side `B` (`C.flip.cont`, in `addHub X C.flip.w`) at its hub -/
def hubPorts : Ports C.flip.cont (hub C.flip.w) where
  p := fun t => hNew C.flip.w t
  x := fun t => hv C.flip.w (C.flip.w t)
  hp := fun t => Or.inr ⟨t, rfl⟩
  hj := fun t => Or.inl (hub_ends_new C.flip.w t)
  xinj := fun s t h => C.yinj _ _ (hv_inj _ h)
  pinj := fun s t h => hNew_inj _ h
  all := by
    rintro f (⟨d, rfl, _⟩ | ⟨t, rfl⟩) hf
    · exact absurd hf (hub_not_inc_old _)
    · exact ⟨t, rfl⟩

theorem hubPorts_p (t : Fin 3) : C.hubPorts.p t = hNew C.flip.w t := rfl
theorem hubPorts_x (t : Fin 3) : C.hubPorts.x t = hv C.flip.w (C.y t) := rfl

theorem flipToCont_e (t : Fin 3) : C.flip.toCont (C.e t) = hNew C.flip.w t := C.flip.toCont_e t
theorem flipToCont_inA {f : Fin X.m} (hf : C.inA f) : C.flip.toCont f = hOld C.flip.w f :=
  C.flip.toCont_old (fun h => C.not_inA_of_cut h hf)

/-- vertices of `X` to vertices of the pole ambient: `w t ↦ o t`, other vertices to themselves -/
noncomputable def toPV (u : Fin X.n) : Fin (splitV C.hubPorts).n :=
  if h : ∃ t, u = C.w t then Fin.natAdd (X.n + 1) (Classical.choose h) else Fin.castAdd 3 (hv C.flip.w u)

theorem toPV_w (t : Fin 3) : C.toPV (C.w t) = Fin.natAdd (X.n + 1) t := by
  have h : ∃ t', C.w t = C.w t' := ⟨t, rfl⟩
  simp only [toPV, dif_pos h]
  rw [C.winj _ _ (Classical.choose_spec h).symm]

theorem toPV_A {u : Fin X.n} (hu : C.S u = true) : C.toPV u = Fin.castAdd 3 (hv C.flip.w u) := by
  have h : ¬ ∃ t, u = C.w t := fun ⟨t, ht⟩ => by rw [ht, C.sw t] at hu; exact absurd hu (by decide)
  simp only [toPV, dif_neg h]

theorem splitV_old (d : Fin X.m) :
    (splitV C.hubPorts).ends (hOld C.flip.w d) =
      (Fin.castAdd 3 (hv C.flip.w (X.ends d).1), Fin.castAdd 3 (hv C.flip.w (X.ends d).2)) := by
  rw [splitV_ends_other _ (fun ⟨t, ht⟩ => hOld_ne_hNew _ _ _ ht), hub_ends_old]

theorem splitV_new (t : Fin 3) :
    (splitV C.hubPorts).ends (hNew C.flip.w t) = (Fin.castAdd 3 (hv C.flip.w (C.y t)), Fin.natAdd (X.n + 1) t) :=
  splitV_ends_port C.hubPorts t

theorem castAdd_ne_natAdd (a : Fin (X.n + 1)) (t : Fin 3) : Fin.castAdd 3 a ≠ Fin.natAdd (X.n + 1) t := by
  intro h; have := congrArg Fin.val h; simp at this; have := a.isLt; omega

/-- the pole `Q1` of side `A` embeds into the pole of the contraction of side `B` at its hub -/
theorem pole_mem {f : Fin X.m} (hf : C.pole f) : vPole C.hubPorts (C.flip.toCont f) := by
  rcases hf with hf | ⟨t, rfl⟩
  · rw [C.flipToCont_inA hf]
    refine Or.inl ⟨Or.inl ⟨f, rfl, ?_⟩, hub_not_inc_old _⟩
    exact ⟨hf.1, by simp [flip_S, hf.2.1], by simp [flip_S, hf.2.2]⟩
  · rw [C.flipToCont_e]; exact Or.inr ⟨t, rfl⟩

theorem pole_joins {f : Fin X.m} (hf : C.pole f) :
    (splitV C.hubPorts).Joins (C.flip.toCont f) (C.toPV (X.ends f).1) (C.toPV (X.ends f).2) := by
  rcases hf with hf | ⟨t, rfl⟩
  · rw [C.flipToCont_inA hf, C.toPV_A hf.2.1, C.toPV_A hf.2.2]
    exact Or.inl (C.splitV_old f)
  · rw [C.flipToCont_e]
    have hn := C.splitV_new t
    rcases C.hj t with h | h <;> rw [h] <;> simp only [C.toPV_A (C.sy t), C.toPV_w]
    · exact Or.inl hn
    · exact Or.inr hn

theorem toPV_inj_pole {u u' : Fin X.n} (hu : meets C.pole u) (hu' : meets C.pole u') (h : C.toPV u = C.toPV u') :
    u = u' := by
  have cases : ∀ z, meets C.pole z → C.S z = true ∨ ∃ t, z = C.w t := by
    rintro z ⟨f, hf, hfz⟩
    rcases hf with hf | ⟨t, rfl⟩
    · exact Or.inl (C.side_of_inA hf hfz)
    · rcases inc_of_joins (C.hj t) hfz with h | h
      · exact Or.inl (h ▸ C.sy t)
      · exact Or.inr ⟨t, h⟩
  rcases cases u hu with h1 | ⟨t, rfl⟩ <;> rcases cases u' hu' with h2 | ⟨t', rfl⟩
  · rw [C.toPV_A h1, C.toPV_A h2] at h
    exact hv_inj _ (Fin.castAdd_injective _ _ h)
  · rw [C.toPV_A h1, C.toPV_w] at h; exact absurd h (castAdd_ne_natAdd _ _)
  · rw [C.toPV_A h2, C.toPV_w] at h; exact absurd h.symm (castAdd_ne_natAdd _ _)
  · rw [C.toPV_w, C.toPV_w] at h
    rw [(Fin.natAdd_inj _).1 h]

/-- **(D1) of the hub pole gives the pole colouring of side `A`** -/
theorem pole_of_D1 {d : Fin (addHub X C.flip.w).m → Fin 6} (hd : MCPole C.hubPorts d) {a : Fin 3 → Fin 6}
    {O B : Fin 3 → Fin 6 → Prop} (hcomp : Compat C.hubPorts d a O B) :
    StarOn C.pole 6 (fun f => d (C.flip.toCont f)) ∧
    (∀ x, C.S x = true → meets P x →
      ∃ a', C.pole a' ∧ X.Inc a' x ∧ d (C.flip.toCont a') = 5 ∧
        ∀ b, C.pole b → X.Inc b x → d (C.flip.toCont b) = 5 → b = a') ∧
    (∀ t, d (C.flip.toCont (C.e t)) = a t) ∧
    (∀ t κ, C.Col (fun f => d (C.flip.toCont f)) t κ → O t κ →
      (C.Blk (fun f => d (C.flip.toCont f)) t κ ∨ B t κ) → False) := by
  have inj : ∀ f g, C.flip.toCont f = C.flip.toCont g → f = g := fun f g h => C.flip.toCont_inj h
  have hstar : StarOn C.pole 6 (fun f => d (C.flip.toCont f)) :=
    starOn_embed (G := X) (H := splitV C.hubPorts) C.toPV C.flip.toCont
      (fun x y a b ha hb hax hby h => C.toPV_inj_pole ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h)
      (fun a b _ _ h => inj a b h) (fun a ha => C.pole_mem ha) (fun a ha => C.pole_joins ha) hd.1
  -- incidence at an old vertex of side `A`
  have incA : ∀ {f : Fin X.m} {x : Fin X.n}, C.pole f → X.Inc f x → C.S x = true →
      (splitV C.hubPorts).Inc (C.flip.toCont f) (Fin.castAdd 3 (hv C.flip.w x)) := by
    intro f x hf hfx hx
    have hj := C.pole_joins hf
    rw [← C.toPV_A hx]
    rcases hfx with h | h <;> rw [← h]
    · exact joins_inc_left hj
    · exact joins_inc_right hj
  -- pole edges of the hub pole at an old vertex of side `A` come from `Q1`
  have back : ∀ {g : Fin (addHub X C.flip.w).m} {x : Fin X.n}, vPole C.hubPorts g →
      (splitV C.hubPorts).Inc g (Fin.castAdd 3 (hv C.flip.w x)) → ∃ f, C.pole f ∧ X.Inc f x ∧ g = C.flip.toCont f := by
    intro g x hg hgx
    rcases hg with ⟨⟨d', rfl, hd'⟩ | ⟨t, rfl⟩, hnv⟩ | ⟨t, rfl⟩
    · have hA : C.inA d' := by
        refine ⟨hd'.1, ?_, ?_⟩
        · have := hd'.2.1; simp [flip_S] at this; exact this
        · have := hd'.2.2; simp [flip_S] at this; exact this
      refine ⟨d', Or.inl hA, ?_, (C.flipToCont_inA hA).symm⟩
      unfold Inc at hgx; rw [C.splitV_old] at hgx
      rcases hgx with h | h
      · exact Or.inl (hv_inj _ (Fin.castAdd_injective _ _ h))
      · exact Or.inr (hv_inj _ (Fin.castAdd_injective _ _ h))
    · exact absurd (hub_inc_new_hub _ t) hnv
    · refine ⟨C.e t, Or.inr ⟨t, rfl⟩, ?_, (C.flipToCont_e t).symm⟩
      unfold Inc at hgx; rw [C.hubPorts_p, C.splitV_new] at hgx
      rcases hgx with h | h
      · rw [← hv_inj _ (Fin.castAdd_injective _ _ h)]; exact joins_inc_left (C.hj t)
      · exact absurd h.symm (castAdd_ne_natAdd _ _)
  refine ⟨hstar, fun x hx hmx => ?_, fun t => ?_, fun t κ hcol hO hbb => ?_⟩
  · -- MC on side `A`
    obtain ⟨f0, hf0, hf0x⟩ := hmx
    have hp0 := C.pole_of_inc hf0 hf0x hx
    have hmeet : meets C.flip.cont (hv C.flip.w x) := by
      refine ⟨C.flip.toCont f0, C.flip.toCont_mem (C.flip_flip_pole.2 hp0), ?_⟩
      have hj := C.flip.toCont_joins (C.flip_flip_pole.2 hp0)
      have hxv : C.flip.toV x = hv C.flip.w x := C.flip.toV_B (by rw [flip_S, hx]; rfl)
      rw [← hxv]
      rcases hf0x with h | h <;> rw [← h]
      · exact joins_inc_left hj
      · exact joins_inc_right hj
    obtain ⟨g, hg, hgx, hg5, huniq⟩ := hd.2 (hv C.flip.w x) (hv_ne_hub _ _) hmeet
    obtain ⟨f, hf, hfx, rfl⟩ := back hg hgx
    exact ⟨f, hf, hfx, hg5, fun b hb hbx hb5 => inj _ _ (huniq _ (C.pole_mem hb) (incA hb hbx hx) hb5)⟩
  · rw [C.flipToCont_e, ← C.hubPorts_p]; exact hcomp.1 t
  · apply hcomp.2 t κ _ hO
    · rcases hbb with ⟨f, r, hf, hjr, hfc, f', hf'p, hf'f, hf'r, hf'c⟩ | hb
      · left
        have hrA : C.S r = true := C.side_of_inA hf (joins_inc_right hjr)
        have hjf := C.pole_joins (Or.inl hf)
        refine ⟨C.flip.toCont f, C.toPV r, C.pole_mem (Or.inl hf), ?_, ?_, hfc, C.flip.toCont f',
          C.pole_mem hf'p, fun h => hf'f (inj _ _ h), ?_, ?_⟩
        · rw [C.flipToCont_inA hf, C.hubPorts_p]; exact hOld_ne_hNew _ _ _
        · rcases joins_unique hjr (joins_ends f) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [C.hubPorts_x, ← C.toPV_A (C.sy t), h1, h2]; exact hjf
          · rw [C.hubPorts_x, ← C.toPV_A (C.sy t), h1, h2]; exact Or.symm hjf
        · rw [C.toPV_A hrA]; exact incA hf'p hf'r hrA
        · rw [C.hubPorts_p]; show d (C.flip.toCont f') = d (hNew C.flip.w t)
          rw [← C.flipToCont_e]; exact hf'c
      · exact Or.inr hb
    · obtain ⟨f, hf, hfy, hfc⟩ := hcol
      refine ⟨C.flip.toCont f, C.pole_mem (Or.inl hf), ?_, ?_, hfc⟩
      · rw [C.flipToCont_inA hf, C.hubPorts_p]; exact hOld_ne_hNew _ _ _
      · rw [C.hubPorts_x]; exact incA (Or.inl hf) hfy (C.sy t)

end Cut3

end hubpole

end RH2F

-- ===== from III5.lean =====
/-
  III5.lean — generic transports for the 3-cut layer: MC colourings along embeddings, and the pole colouring of side
  `A` from (D1) of any vertex pole into which the pole `Q1` embeds.  The plain 3-cut MC gluing `glue_D1`.
-/

namespace RH2F
open MGraph
open Classical

section transport
variable {X H : MGraph}

/-- **MC colourings pull back along an embedding** that is locally surjective on the edges -/
theorem mcol_emb {Q : Fin X.m → Prop} {P' : Fin H.m → Prop} (ρ : Fin X.n → Fin H.n) (μ : Fin X.m → Fin H.m)
    (hρ : ∀ x y, meets Q x → meets Q y → ρ x = ρ y → x = y) (hμ : ∀ a b, Q a → Q b → μ a = μ b → a = b)
    (hP : ∀ a, Q a → P' (μ a)) (hj : ∀ a, Q a → H.Joins (μ a) (ρ (X.ends a).1) (ρ (X.ends a).2))
    (hsurj : ∀ x, meets Q x → ∀ b, P' b → H.Inc b (ρ x) → ∃ a, Q a ∧ μ a = b)
    {c : Fin H.m → Fin 6} (hc : MCol P' c) : MCol Q (fun a => c (μ a)) := by
  have hst : StarOn Q 6 (fun a => c (μ a)) :=
    starOn_embed ρ μ (fun x y a b ha hb hax hby h => hρ x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h) hμ hP hj hc.1
  have incm : ∀ {a x}, Q a → X.Inc a x → H.Inc (μ a) (ρ x) := by
    intro a x ha hax
    rcases hax with h | h <;> rw [← h]
    · exact joins_inc_left (hj a ha)
    · exact joins_inc_right (hj a ha)
  refine ⟨hst, fun x hx => ?_⟩
  obtain ⟨a0, ha0, ha0x⟩ := hx
  obtain ⟨b, hb, hbx, hb5, hbu⟩ := hc.2 (ρ x) ⟨μ a0, hP a0 ha0, incm ha0 ha0x⟩
  obtain ⟨a, ha, rfl⟩ := hsurj x ⟨a0, ha0, ha0x⟩ b hb hbx
  have hax : X.Inc a x := by
    rcases inc_of_joins (hj a ha) hbx with h | h
    · rw [hρ _ _ ⟨a0, ha0, ha0x⟩ ⟨a, ha, Or.inl rfl⟩ h]; exact Or.inl rfl
    · rw [hρ _ _ ⟨a0, ha0, ha0x⟩ ⟨a, ha, Or.inr rfl⟩ h]; exact Or.inr rfl
  exact ⟨a, ha, hax, hb5, fun a' ha' ha'x ha'5 => hμ _ _ ha' ha (hbu _ (hP a' ha') (incm ha' ha'x) ha'5)⟩

end transport

section gen
variable {X Y : MGraph} {P : Fin X.m → Prop} {Q : Fin Y.m → Prop} {v : Fin Y.n}

namespace Cut3
variable (C : Cut3 P)

/-- **(D1) of a vertex pole into which `Q1` embeds gives the pole colouring of side `A`** (generic form) -/
theorem pole_of_D1_gen (D : Ports Q v) (ρ : Fin X.n → Fin (splitV D).n) (μ : Fin X.m → Fin Y.m)
    (hρ : ∀ u u', meets C.pole u → meets C.pole u' → ρ u = ρ u' → u = u')
    (hμ : ∀ f g, C.pole f → C.pole g → μ f = μ g → f = g)
    (hmem : ∀ f, C.pole f → vPole D (μ f))
    (hj : ∀ f, C.pole f → (splitV D).Joins (μ f) (ρ (X.ends f).1) (ρ (X.ends f).2))
    (hport : ∀ t, μ (C.e t) = D.p t) (hinA : ∀ f, C.inA f → ∀ t, μ f ≠ D.p t)
    (hx : ∀ t, ρ (C.y t) = Fin.castAdd 3 (D.x t))
    (hA : ∀ x, C.S x = true → meets P x → ∃ u, ρ x = Fin.castAdd 3 u ∧ u ≠ v ∧ meets Q u)
    (hback : ∀ g x, vPole D g → C.S x = true → (splitV D).Inc g (ρ x) → ∃ f, C.pole f ∧ X.Inc f x ∧ g = μ f)
    {d : Fin Y.m → Fin 6} (hd : MCPole D d) {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop}
    (hcomp : Compat D d a O B) :
    StarOn C.pole 6 (fun f => d (μ f)) ∧
    (∀ x, C.S x = true → meets P x →
      ∃ a', C.pole a' ∧ X.Inc a' x ∧ d (μ a') = 5 ∧ ∀ b, C.pole b → X.Inc b x → d (μ b) = 5 → b = a') ∧
    (∀ t, d (μ (C.e t)) = a t) ∧
    (∀ t κ, C.Col (fun f => d (μ f)) t κ → O t κ → (C.Blk (fun f => d (μ f)) t κ ∨ B t κ) → False) := by
  have hstar : StarOn C.pole 6 (fun f => d (μ f)) :=
    starOn_embed (G := X) (H := splitV D) ρ μ (fun x y a b ha hb hax hby h => hρ x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h)
      hμ hmem hj hd.1
  have incm : ∀ {f x}, C.pole f → X.Inc f x → (splitV D).Inc (μ f) (ρ x) := by
    intro f x hf hfx
    rcases hfx with h | h <;> rw [← h]
    · exact joins_inc_left (hj f hf)
    · exact joins_inc_right (hj f hf)
  refine ⟨hstar, fun x hx hmx => ?_, fun t => ?_, fun t κ hcol hO hbb => ?_⟩
  · obtain ⟨u, hu, huv, hmu⟩ := hA x hx hmx
    obtain ⟨g, hg, hgx, hg5, huniq⟩ := hd.2 u huv hmu
    rw [← hu] at hgx
    obtain ⟨f, hf, hfx, rfl⟩ := hback g x hg hx hgx
    refine ⟨f, hf, hfx, hg5, fun b hb hbx hb5 => hμ _ _ hb hf (huniq _ (hmem b hb) ?_ hb5)⟩
    rw [← hu]; exact incm hb hbx
  · rw [hport]; exact hcomp.1 t
  · apply hcomp.2 t κ _ hO
    · rcases hbb with ⟨f, r, hf, hjr, hfc, f', hf'p, hf'f, hf'r, hf'c⟩ | hb
      · left
        refine ⟨μ f, ρ r, hmem f (Or.inl hf), hinA f hf t, ?_, hfc, μ f', hmem f' hf'p,
          fun h => hf'f (hμ _ _ hf'p (Or.inl hf) h), incm hf'p hf'r, ?_⟩
        · rw [← hx]
          rcases joins_unique hjr (joins_ends f) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hj f (Or.inl hf)
          · rw [h1, h2]; exact Or.symm (hj f (Or.inl hf))
        · rw [← hport]; exact hf'c
      · exact Or.inr hb
    · obtain ⟨f, hf, hfy, hfc⟩ := hcol
      refine ⟨μ f, hmem f (Or.inl hf), hinA f hf t, ?_, hfc⟩
      rw [← hx]; exact incm (Or.inl hf) hfy

/-- a colour-5 hub edge exists for an MC colouring of the contraction -/
theorem hub_port (c : Fin (addHub X C.w).m → Fin 6) (hc : MCol C.cont c) : ∃ i, c (hNew C.w i) = 5 := by
  obtain ⟨a, ha, hax, ha5, _⟩ := hc.2 (hub C.w) ⟨hNew C.w 0, Or.inr ⟨0, rfl⟩, hub_inc_new_hub _ 0⟩
  rcases ha with ⟨d, rfl, _⟩ | ⟨t, rfl⟩
  · exact absurd hax (hub_not_inc_old _)
  · exact ⟨t, ha5⟩

/-- **the plain 3-cut MC gluing**: an MC colouring of the contraction of side `A` and (D1) of the pole of side `A`
    (the pole of the contraction of side `B` at its hub) at the port of colour `5` give an MC colouring of `P` -/
theorem glue_D1 (hloop : Loopless X) (hw : ∀ t, CubicAt P (C.w t)) (c : Fin (addHub X C.w).m → Fin 6)
    (hc : MCol C.cont c) {i : Fin 3} (hi : c (hNew C.w i) = 5) (hD : D1 C.hubPorts i) : ∃ c', MCol P c' := by
  obtain ⟨d, hd, hcomp⟩ := hD _ _ _ (C.dat_admissible hloop hw c hc hi)
  obtain ⟨hs, hA, he, hcp⟩ := C.pole_of_D1 hd hcomp
  exact C.mc_glue c hc _ hs hA he hcp

end Cut3

end gen

end RH2F

namespace RH2F
open MGraph

/-- **Layer 13 of the Lean formalization** (3-edge-cut layer): Theorem 3CUT-MULTI (fact 4f30e30e4f4d4e99) in pole form
    — (A-M) and (MC-M) in the direction ⇐, (B-M) — and the MC gluing across a 3-edge-cut with distinct ends from (D1)
    of the pole of side `A` (facts 87fba73118e1699c, 82bc44210c5765d5). -/
theorem layer13 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P) (φ ψ c : Fin X.m → Fin 6), StarOn C.pole 6 φ →
      StarOn C.flip.pole 6 ψ → (∀ f, C.pole f → c f = φ f) → (∀ f, C.flip.pole f → c f = ψ f) →
      (∀ i κ, C.Col φ i κ → C.flip.Col ψ i κ → (C.Blk φ i κ ∨ C.flip.Blk ψ i κ) → False) → StarOn P 6 c) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P) (c : Fin (addHub X C.w).m → Fin 6), Loopless X →
      StarOn C.cont 6 c →
      StarOn C.flip.pole 6 (fun f => c (C.toCont f)) ∧ (∀ t t', c (hNew C.w t) = c (hNew C.w t') → t = t') ∧
      (∀ i j, ¬ C.flip.Blk (fun f => c (C.toCont f)) i (c (hNew C.w j))) ∧
      (∀ i j, i ≠ j → ¬ (C.flip.Col (fun f => c (C.toCont f)) i (c (hNew C.w j)) ∧
        C.flip.Col (fun f => c (C.toCont f)) j (c (hNew C.w i))))) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P) (c : Fin (addHub X C.w).m → Fin 6) (i : Fin 3), Loopless X →
      (∀ t, CubicAt P (C.w t)) → MCol C.cont c → c (hNew C.w i) = 5 → Admissible i (C.datA c) (C.datO c) (C.datB c)) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P) (c : Fin (addHub X C.w).m → Fin 6) (φ : Fin X.m → Fin 6),
      MCol C.cont c → StarOn C.pole 6 φ →
      (∀ x, C.S x = true → meets P x →
        ∃ a, C.pole a ∧ X.Inc a x ∧ φ a = 5 ∧ ∀ b, C.pole b → X.Inc b x → φ b = 5 → b = a) →
      (∀ t, φ (C.e t) = C.datA c t) →
      (∀ t κ, C.Col φ t κ → C.datO c t κ → (C.Blk φ t κ ∨ C.datB c t κ) → False) → ∃ c', MCol P c') ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut3 P) (c : Fin (addHub X C.w).m → Fin 6) (i : Fin 3), Loopless X →
      (∀ t, CubicAt P (C.w t)) → MCol C.cont c → c (hNew C.w i) = 5 → D1 C.hubPorts i → ∃ c', MCol P c') :=
  ⟨fun _ _ C φ ψ c hφ hψ hcφ hcψ ht => C.glue3 φ ψ c hφ hψ hcφ hcψ ht,
   fun _ _ C c hl hc => ⟨C.pole_of_cont c hc, fun _ _ h => C.hub_distinct c hc h, fun i j => C.cont_noBlk hl c hc i j,
     fun _ _ hij => C.cont_cross hl c hc hij⟩,
   fun _ _ C c _ hl hw hc hi => C.dat_admissible hl hw c hc hi,
   fun _ _ C c φ hc hφ hA he hcp => C.mc_glue c hc φ hφ hA he hcp,
   fun _ _ C c _ hl hw hc hi hD => C.glue_D1 hl hw c hc hi hD⟩

end RH2F
