-- Lean proof of fact 3c53e18d818a023b (RH2F.layer36a); added by fact_submit, do not edit
import MhFact_cc801c1ba060f9c7
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000

-- ===== from FE1.lean =====
/-
  FE1 — far-exchange certificates on edge lists: a Boolean check of a perfect matching `M` and a far-exchange set
  `C` (conditions (a), (b′), (c) of fact 898eb5ab55d140fe, Lean form `FarEx` of fact 345a55d7429fd4b1) on
  `ofList n el`, its soundness, and the transfer of far-exchange existence along `IsoFrom`.
-/

namespace RH2F
open MGraph

section fe1

/-! ### bit helpers -/

theorem fe_testBit_row (AD a z : Nat) (hz : z < 16) :
    ((AD >>> (16 * a)) &&& 65535).testBit z = AD.testBit (16 * a + z) := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight, show (65535 : Nat) = 2 ^ 16 - 1 by decide,
    Nat.testBit_two_pow_sub_one]
  simp [hz]

theorem fe_and_ne_zero {x y z : Nat} (hx : x.testBit z = true) (hy : y.testBit z = true) : (x &&& y) ≠ 0 := by
  intro h
  have : (x &&& y).testBit z = true := by rw [Nat.testBit_and, hx, hy]; rfl
  rw [h, Nat.zero_testBit] at this
  exact absurd this (by decide)

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

/-- the end of edge `e` selected by `s` (`s = 0`: first end, otherwise second end) -/
def endS (el : List (Nat × Nat)) (e s : Nat) : Nat := cond (Nat.beq s 0) (gER el e).1 (gER el e).2

theorem gER_eq_gE (el : List (Nat × Nat)) (e : Nat) : gER el e = gE el e := by
  unfold gER gE; rw [getR_eq]

/-! ### the Boolean checks -/

/-- digit `v` of `X` in base 32 (a vertex's entry of an encoded `pm` / `cv` table) -/
def gN (X v : Nat) : Nat := dgt X 32 v

/-- the ends of edge `e` from the edge code `E` (`encE`) -/
def gEE (E e : Nat) : Nat × Nat := (dgt E 256 e % 16, dgt E 256 e / 16)

/-- (PM) `pmf v` is an `M`-edge at `v` for every vertex `v < n`, and both ends `x` of every `M`-edge `e` have
    `pmf x = e`; `en e` are the ends of edge `e`, `m` the number of edges -/
def pmB (n m : Nat) (en : Nat → Nat × Nat) (Mb : Nat) (pmf : Nat → Nat) : Bool :=
  rangeAll n (fun v => Nat.blt (pmf v) m && Mb.testBit (pmf v) &&
    (Nat.beq (en (pmf v)).1 v || Nat.beq (en (pmf v)).2 v)) &&
  rangeAll m (fun e => !Mb.testBit e || (Nat.beq (pmf (en e).1) e && Nat.beq (pmf (en e).2) e))

/-- `C` is disjoint from `M`, both ends `x` of every `C`-edge `c` have `cvf x = c`, and `cvf v < m` only if `cvf v`
    is a `C`-edge at `v` -/
def cvB (n m : Nat) (en : Nat → Nat × Nat) (Mb Cb : Nat) (cvf : Nat → Nat) : Bool :=
  Nat.beq (Mb &&& Cb) 0 &&
  rangeAll m (fun e => !Cb.testBit e || (Nat.beq (cvf (en e).1) e && Nat.beq (cvf (en e).2) e)) &&
  rangeAll n (fun v => Nat.ble m (cvf v) ||
    (Cb.testBit (cvf v) && (Nat.beq (en (cvf v)).1 v || Nat.beq (en (cvf v)).2 v)))

/-- the ends of edge `e` are not both on `C`-edges, unless on the same one -/
def endsOK (m : Nat) (en : Nat → Nat × Nat) (cvf : Nat → Nat) (e : Nat) : Bool :=
  Nat.ble m (cvf (en e).1) || Nat.ble m (cvf (en e).2) || Nat.beq (cvf (en e).1) (cvf (en e).2)

/-- (a) and (b′): every edge outside `C` passes `endsOK` -/
def abB (m : Nat) (en : Nat → Nat × Nat) (Cb : Nat) (cvf : Nat → Nat) : Bool :=
  rangeAll m (fun e => Cb.testBit e || endsOK m en cvf e)

/-- an exchange: an `M`-edge with both ends free of `C` -/
def isX (m : Nat) (en : Nat → Nat × Nat) (Mb : Nat) (cvf : Nat → Nat) (p : Nat) : Bool :=
  Mb.testBit p && Nat.ble m (cvf (en p).1) && Nat.ble m (cvf (en p).2)

/-- the vertices `a`, `b` are distinct, not adjacent and have no common neighbour (adjacency bitset `AD`) -/
def far2 (AD a b : Nat) : Bool :=
  !Nat.beq a b && !AD.testBit (16 * a + b) && Nat.beq (((AD >>> (16 * a)) &&& 65535) &&& ((AD >>> (16 * b)) &&& 65535)) 0

/-- (c) for the pair `p`, `p'` -/
def d3B (en : Nat → Nat × Nat) (AD p p' : Nat) : Bool :=
  far2 AD (en p).1 (en p').1 && far2 AD (en p).1 (en p').2 &&
  far2 AD (en p).2 (en p').1 && far2 AD (en p).2 (en p').2

/-- (c): distinct exchanges are at distance at least 3 -/
def cB (m : Nat) (en : Nat → Nat × Nat) (AD Mb : Nat) (cvf : Nat → Nat) : Bool :=
  rangeAll m (fun p => !isX m en Mb cvf p ||
    rangeAll m (fun p' => !isX m en Mb cvf p' || Nat.beq p p' || d3B en AD p p'))

/-- a far-exchange structure `(Mb, Cb, PM, CV)`: bitmasks of `M` and `C` and the base-32 tables `pm`, `cv` -/
abbrev FES := Nat × Nat × Nat × Nat

def feB (n m : Nat) (en : Nat → Nat × Nat) (AD : Nat) (s : FES) : Bool :=
  pmB n m en s.1 (gN s.2.2.1) && cvB n m en s.1 s.2.1 (gN s.2.2.2) && abB m en s.2.1 (gN s.2.2.2) &&
    cB m en AD s.1 (gN s.2.2.2)

/-- the certificate check with the edge code `E` and adjacency bitset `AD` -/
def feCertE (n m E AD : Nat) (L : List FES) : Bool :=
  allR (feB n m (gEE E) AD) L &&
  rangeAll m (fun g => anyR (fun s => s.1.testBit g) L && anyR (fun s => !s.1.testBit g) L)

/-- the certificate of a graph: every structure passes, and every edge is in some `M` and outside some `M` -/
def feCert (n : Nat) (el : List (Nat × Nat)) (L : List FES) : Bool :=
  elOK n el && Nat.ble n 16 && feCertE n el.length (encE el) (adjF id el) L

/-! ### soundness -/

/-- far-exchange existence at every edge and status on the whole of `H` -/
def FEGood (H : MGraph) : Prop :=
  ∀ (g : Fin H.m) (t : Bool), ∃ M : Fin H.m → Prop, PMOn (fun _ => True) M ∧ (M g ↔ t = true) ∧
    ∃ C, FarEx (fun _ => True) M C

theorem fe_inc_iff (hel : elOK n el = true) {f : Fin (ofList n el hn).m} {x : Fin (ofList n el hn).n} :
    (ofList n el hn).Inc f x ↔ ((gER el f.val).1 = x.val ∨ (gER el f.val).2 = x.val) := by
  rw [ofList_inc hel, gER_eq_gE]; unfold incN; simp

/-- the vertex `⟨v, _⟩` of `ofList` -/
theorem fe_ends_lt (hel : elOK n el = true) {f : Nat} (hf : f < el.length) :
    (gER el f).1 < n ∧ (gER el f).2 < n := by
  rw [gER_eq_gE]; exact gE_lt hel hf

theorem fe_joins_iff (hel : elOK n el = true) {f : Fin (ofList n el hn).m} {x y : Fin (ofList n el hn).n} :
    (ofList n el hn).Joins f x y ↔
      (((gER el f.val).1 = x.val ∧ (gER el f.val).2 = y.val) ∨ ((gER el f.val).1 = y.val ∧ (gER el f.val).2 = x.val)) := by
  have he := ofList_ends (hn := hn) hel f
  rw [← gER_eq_gE] at he
  unfold MGraph.Joins
  constructor
  · rintro (h | h) <;> rw [h] at he <;> simp only at he
    · exact Or.inl ⟨he.1.symm, he.2.symm⟩
    · exact Or.inr ⟨he.1.symm, he.2.symm⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; exact Prod.ext (Fin.ext (he.1.trans h1)) (Fin.ext (he.2.trans h2))
    · right; exact Prod.ext (Fin.ext (he.1.trans h1)) (Fin.ext (he.2.trans h2))

theorem fe_rangeAll {k : Nat} {p : Nat → Bool} (h : rangeAll k p = true) {i : Nat} (hi : i < k) : p i = true := by
  rw [rangeAll_eq, List.all_eq_true] at h; exact h i (List.mem_range.2 hi)

section sound
variable (hel : elOK n el = true) (h16 : n ≤ 16) {en : Nat → Nat × Nat}
  (hen : ∀ e, e < el.length → en e = gER el e)
include hel

include hen in
theorem pmOn_of_pmB {Mb : Nat} {pmf : Nat → Nat} (h : pmB n el.length en Mb pmf = true) :
    PMOn (X := ofList n el hn) (fun _ => True) (fun f => Mb.testBit f.val = true) := by
  unfold pmB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun _ _ => trivial, ?_⟩
  intro x _
  have hx := fe_rangeAll h1 x.isLt
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hx
  obtain ⟨⟨hlt, hM⟩, hinc⟩ := hx
  have hlt' : pmf x.val < el.length := by simpa [Nat.blt_eq] using hlt
  rw [hen _ hlt'] at hinc
  refine ⟨⟨pmf x.val, hlt'⟩, hM, ?_, ?_⟩
  · rw [fe_inc_iff hel]
    rcases hinc with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · exact Or.inr (Nat.eq_of_beq_eq_true h)
  · intro d hd hdx
    have he := fe_rangeAll h2 d.isLt
    rw [hen _ d.isLt] at he
    simp only [hd, Bool.not_true, Bool.false_or, Bool.and_eq_true] at he
    rw [fe_inc_iff hel] at hdx
    apply Fin.ext
    show d.val = pmf x.val
    rcases hdx with hx | hx
    · rw [← hx]; exact (Nat.eq_of_beq_eq_true he.1).symm
    · rw [← hx]; exact (Nat.eq_of_beq_eq_true he.2).symm

include hen in
/-- a `C`-edge at `x` is `cvf x` -/
theorem cv_of_inc {Mb Cb : Nat} {cvf : Nat → Nat} (h : cvB n el.length en Mb Cb cvf = true)
    {c : Fin (ofList n el hn).m} (hc : Cb.testBit c.val = true) {x : Fin (ofList n el hn).n}
    (hx : (ofList n el hn).Inc c x) : cvf x.val = c.val := by
  unfold cvB at h
  simp only [Bool.and_eq_true] at h
  have he := fe_rangeAll h.1.2 c.isLt
  rw [hen _ c.isLt] at he
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at he
  rw [fe_inc_iff hel] at hx
  rcases hx with hx | hx
  · rw [← hx]; exact Nat.eq_of_beq_eq_true he.1
  · rw [← hx]; exact Nat.eq_of_beq_eq_true he.2

include hen in
/-- `cvf v < |el|` names a `C`-edge at `v` -/
theorem c_of_cv {Mb Cb : Nat} {cvf : Nat → Nat} (h : cvB n el.length en Mb Cb cvf = true) {v : Nat}
    (hv : v < n) (hlt : cvf v < el.length) :
    Cb.testBit (cvf v) = true ∧ ((gER el (cvf v)).1 = v ∨ (gER el (cvf v)).2 = v) := by
  unfold cvB at h
  simp only [Bool.and_eq_true] at h
  have he := fe_rangeAll h.2 hv
  rw [hen _ hlt] at he
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at he
  rcases he with he | ⟨hC, hi⟩
  · exact absurd (Nat.le_of_ble_eq_true he) (Nat.not_le.2 hlt)
  · exact ⟨hC, hi.imp Nat.eq_of_beq_eq_true Nat.eq_of_beq_eq_true⟩

omit hel in
theorem not_mc_of_cvB {Mb Cb : Nat} {cvf : Nat → Nat} (h : cvB n el.length en Mb Cb cvf = true) {f : Nat}
    (hc : Cb.testBit f = true) : Mb.testBit f = false := by
  unfold cvB at h
  simp only [Bool.and_eq_true] at h
  have h0 := Nat.eq_of_beq_eq_true h.1.1
  have : (Mb &&& Cb).testBit f = false := by rw [h0, Nat.zero_testBit]
  rw [Nat.testBit_and, hc, Bool.and_true] at this
  exact this

/-- the ends of an `ofList` edge as vertices -/
def feV1 (f : Fin (ofList n el hn).m) : Fin (ofList n el hn).n := ⟨(gER el f.val).1, (fe_ends_lt hel f.isLt).1⟩
def feV2 (f : Fin (ofList n el hn).m) : Fin (ofList n el hn).n := ⟨(gER el f.val).2, (fe_ends_lt hel f.isLt).2⟩

theorem ends_feV (f : Fin (ofList n el hn).m) :
    ((ofList n el hn).ends f).1 = feV1 hel f ∧ ((ofList n el hn).ends f).2 = feV2 hel f := by
  have he := ofList_ends (hn := hn) hel f
  rw [← gER_eq_gE] at he
  exact ⟨Fin.ext he.1, Fin.ext he.2⟩

omit hel in
include h16 in
/-- vertices of `ofList` are below `16` -/
theorem fe_lt16 (x : Fin (ofList n el hn).n) : x.val < 16 := Nat.lt_of_lt_of_le x.isLt h16

theorem adj_bit {e : Fin (ofList n el hn).m} {a b : Fin (ofList n el hn).n} (h : (ofList n el hn).Joins e a b) :
    (adjF id el).testBit (16 * a.val + b.val) = true := by
  rw [testBit_adjF]
  refine ⟨e.val, e.isLt, ?_⟩
  rw [← gER_eq_gE]
  rcases (fe_joins_iff hel).1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; simp [h1, h2]
  · right; simp [h1, h2]

include h16 hen in
theorem dist3_of_far2 {p p' : Fin (ofList n el hn).m}
    (h : d3B en (adjF id el) p.val p'.val = true) : Dist3 (fun _ => True) p p' := by
  rw [d3B, hen _ p.isLt, hen _ p'.isLt] at h
  intro a b ha hb
  rw [fe_inc_iff hel] at ha hb
  have key : far2 (adjF id el) a.val b.val = true := by
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h11, h12⟩, h21⟩, h22⟩ := h
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [← ha, ← hb] <;> assumption
  unfold far2 at key
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at key
  obtain ⟨⟨hab, hadj⟩, hcn⟩ := key
  refine ⟨fun e => ?_, ?_, ?_⟩
  · rw [e] at hab; exact absurd (Nat.beq_refl b.val) (by rw [hab]; decide)
  · rintro ⟨e, _, he⟩
    rw [adj_bit hel he] at hadj; exact absurd hadj (by decide)
  · rintro ⟨e1, e2, z, _, _, h1, h2⟩
    have b1 := adj_bit hel h1
    have b2 := adj_bit hel (Or.symm h2)
    have hz := fe_lt16 h16 z
    rw [← fe_testBit_row _ _ _ hz] at b1 b2
    exact fe_and_ne_zero b1 b2 (Nat.eq_of_beq_eq_true hcn)

include h16 hen in
theorem farEx_of_feB {s : FES} (h : feB n el.length en (adjF id el) s = true) :
    PMOn (X := ofList n el hn) (fun _ => True) (fun f => s.1.testBit f.val = true) ∧
    FarEx (X := ofList n el hn) (fun _ => True) (fun f => s.1.testBit f.val = true)
      (fun f => s.2.1.testBit f.val = true) := by
  obtain ⟨Mb, Cb, PM, CV⟩ := s
  unfold feB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpm, hcv⟩, hab⟩, hc⟩ := h
  have hPM := pmOn_of_pmB (hn := hn) hel hen hpm
  refine ⟨hPM, ?_, ?_, ?_, ?_⟩
  · intro f hf
    exact ⟨trivial, by simp [not_mc_of_cvB hcv hf]⟩
  · -- (a)
    intro p c1 c2 hp hc1 hc2 ⟨x, hpx, hc1x⟩ ⟨y, hpy, hc2y⟩
    have e1 := cv_of_inc hel hen hcv hc1 hc1x
    have e2 := cv_of_inc hel hen hcv hc2 hc2y
    by_cases hxy : x = y
    · subst hxy; exact Fin.ext (e1.symm.trans e2)
    · have hpC : Cb.testBit p.val = false := by
        have := not_mc_of_cvB hcv (f := p.val)
        cases hq : Cb.testBit p.val
        · rfl
        · rw [this hq] at hp; exact absurd hp (by decide)
      have hok := fe_rangeAll hab p.isLt
      rw [hpC, Bool.false_or] at hok
      unfold endsOK at hok
      rw [hen _ p.isLt] at hok
      simp only [Bool.or_eq_true] at hok
      rw [fe_inc_iff hel] at hpx hpy
      have hc1lt : c1.val < el.length := c1.isLt
      have hc2lt : c2.val < el.length := c2.isLt
      have hl : ((gER el p.val).1 = x.val ∧ (gER el p.val).2 = y.val) ∨
          ((gER el p.val).1 = y.val ∧ (gER el p.val).2 = x.val) := by
        rcases hpx with h1 | h1 <;> rcases hpy with h2 | h2
        · exact absurd (Fin.ext (h1.symm.trans h2)) hxy
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
        · exact absurd (Fin.ext (h1.symm.trans h2)) hxy
      rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hok
      · rcases hok with (hk | hk) | hk
        · have := Nat.le_of_ble_eq_true hk; rw [e1] at this; omega
        · have := Nat.le_of_ble_eq_true hk; rw [e2] at this; omega
        · exact Fin.ext (e1.symm.trans ((Nat.eq_of_beq_eq_true hk).trans e2))
      · rcases hok with (hk | hk) | hk
        · have := Nat.le_of_ble_eq_true hk; rw [e2] at this; omega
        · have := Nat.le_of_ble_eq_true hk; rw [e1] at this; omega
        · exact Fin.ext (e1.symm.trans ((Nat.eq_of_beq_eq_true hk).symm.trans e2))
  · -- (b′)
    intro e _ _ hCe hnp ⟨⟨c1, hc1, hc1x⟩, ⟨c2, hc2, hc2y⟩⟩
    have e1 := cv_of_inc hel hen hcv hc1 hc1x
    have e2 := cv_of_inc hel hen hcv hc2 hc2y
    have hok := fe_rangeAll hab e.isLt
    have hCe' : Cb.testBit e.val = false := by
      cases hq : Cb.testBit e.val
      · rfl
      · exact absurd hq hCe
    rw [hCe', Bool.false_or] at hok
    unfold endsOK at hok
    rw [hen _ e.isLt] at hok
    simp only [Bool.or_eq_true] at hok
    obtain ⟨en1, en2⟩ := ends_feV hel e
    rw [en1] at e1; rw [en2] at e2
    change gN CV (gER el e.val).1 = c1.val at e1
    change gN CV (gER el e.val).2 = c2.val at e2
    rcases hok with (hk | hk) | hk
    · exact absurd (Nat.le_of_ble_eq_true hk) (by rw [e1]; exact Nat.not_le.2 c1.isLt)
    · exact absurd (Nat.le_of_ble_eq_true hk) (by rw [e2]; exact Nat.not_le.2 c2.isLt)
    · have hc12 : c1 = c2 := Fin.ext (e1.symm.trans ((Nat.eq_of_beq_eq_true hk).trans e2))
      subst hc12
      apply hnp
      refine ⟨c1, hc1, ?_⟩
      have hloop := ofList_loop (hn := hn) hel e
      rw [← gER_eq_gE] at hloop
      rw [en1] at hc1x; rw [en2] at hc2y
      rw [fe_joins_iff hel]
      rw [fe_inc_iff hel] at hc1x hc2y
      change (gER el c1.val).1 = (gER el e.val).1 ∨ (gER el c1.val).2 = (gER el e.val).1 at hc1x
      change (gER el c1.val).1 = (gER el e.val).2 ∨ (gER el c1.val).2 = (gER el e.val).2 at hc2y
      rw [en1, en2]
      change ((gER el c1.val).1 = (gER el e.val).1 ∧ (gER el c1.val).2 = (gER el e.val).2) ∨
        ((gER el c1.val).1 = (gER el e.val).2 ∧ (gER el c1.val).2 = (gER el e.val).1)
      rcases hc1x with h1 | h1 <;> rcases hc2y with h2 | h2
      · exact absurd (h1.symm.trans h2) hloop
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact absurd (h1.symm.trans h2) hloop
  · -- (c)
    intro p p' hp hp' hne hfp hfp'
    have hX : ∀ q : Fin (ofList n el hn).m, Mb.testBit q.val = true →
        (∀ c : Fin (ofList n el hn).m, Cb.testBit c.val = true → ¬ Meet q c) →
          isX el.length en Mb (gN CV) q.val = true := by
      intro q hq hfq
      have hlt := fe_ends_lt hel q.isLt
      have hfree : ∀ v, v < n → ((gER el q.val).1 = v ∨ (gER el q.val).2 = v) →
          Nat.ble el.length (gN CV v) = true := by
        intro v hv hqv
        apply Nat.ble_eq_true_of_le
        apply Nat.not_lt.1
        intro hlt2
        obtain ⟨hC, hi⟩ := c_of_cv hel hen hcv hv hlt2
        apply hfq ⟨gN CV v, hlt2⟩ hC
        refine ⟨⟨v, hv⟩, ?_, ?_⟩
        · rw [fe_inc_iff hel]; exact hqv
        · rw [fe_inc_iff hel]; exact hi
      unfold isX
      rw [hen _ q.isLt, hq, hfree _ hlt.1 (Or.inl rfl), hfree _ hlt.2 (Or.inr rfl)]
      rfl
    have hc1 := fe_rangeAll hc p.isLt
    rw [hX p hp hfp, Bool.not_true, Bool.false_or] at hc1
    have hc2 := fe_rangeAll hc1 p'.isLt
    rw [hX p' hp' hfp', Bool.not_true, Bool.false_or] at hc2
    have hneq : Nat.beq p.val p'.val = false := by
      cases hb : Nat.beq p.val p'.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)) hne
    rw [hneq, Bool.false_or] at hc2
    exact dist3_of_far2 hel h16 hen hc2

end sound

end fe1

end RH2F

-- ===== from FE2.lean =====
/-
  FE2 — soundness of the far-exchange certificate of a graph, and the transfer of far-exchange existence along
  `IsoFrom`.
-/

namespace RH2F
open MGraph

section fe2

theorem gEE_encE {n : Nat} {el : List (Nat × Nat)} (hel : elOK n el = true) (h16 : n ≤ 16) :
    ∀ e, e < el.length → gEE (encE el) e = gER el e := by
  intro e he
  have h := dgt_encE el (small_of_elOK hel h16) e he
  rw [gER_eq_gE]
  unfold gEE
  rw [h.1, h.2]

theorem feGood_of_cert {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} {L : List FES} (h : feCert n el L = true) :
    FEGood (ofList n el hn) := by
  unfold feCert feCertE at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hel, h16⟩, hall, hcov⟩ := h
  have h16' := Nat.le_of_ble_eq_true h16
  have hen := gEE_encE hel h16'
  intro g t
  have hg := fe_rangeAll hcov g.isLt
  simp only [Bool.and_eq_true] at hg
  cases t with
  | false =>
    obtain ⟨s, hs, hsg⟩ := anyR_mem hg.2
    obtain ⟨hPM, hFE⟩ := farEx_of_feB (hn := hn) hel h16' hen (allR_mem hall hs)
    refine ⟨_, hPM, ?_, _, hFE⟩
    simp only [Bool.not_eq_true'] at hsg
    simp [hsg]
  | true =>
    obtain ⟨s, hs, hsg⟩ := anyR_mem hg.1
    obtain ⟨hPM, hFE⟩ := farEx_of_feB (hn := hn) hel h16' hen (allR_mem hall hs)
    refine ⟨_, hPM, ?_, _, hFE⟩
    simp [hsg]

variable {X H : MGraph} {P : Fin X.m → Prop} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m}

theorem fe_meets {f : Fin X.m} {x : Fin X.n} (hf : P f) (hx : X.Inc f x) : meets P x := ⟨f, hf, hx⟩

theorem fe_inc_map (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {f : Fin X.m} {x : Fin X.n}
    (hf : P f) (hx : X.Inc f x) : H.Inc (β f) (α x) := by
  rcases hj f hf with h | h <;> rcases hx with hx | hx <;> rw [← hx] <;> unfold MGraph.Inc <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem fe_inc_back (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {f : Fin X.m} {y : Fin H.n}
    (hf : P f) (hy : H.Inc (β f) y) : ∃ x, X.Inc f x ∧ α x = y := by
  rcases hj f hf with h | h <;> unfold MGraph.Inc at hy <;> rw [h] at hy <;> simp only at hy
  · rcases hy with hy | hy
    · exact ⟨_, Or.inl rfl, hy⟩
    · exact ⟨_, Or.inr rfl, hy⟩
  · rcases hy with hy | hy
    · exact ⟨_, Or.inr rfl, hy⟩
    · exact ⟨_, Or.inl rfl, hy⟩

theorem fe_joins_map (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {e : Fin X.m}
    {a b : Fin X.n} (he : P e) (hab : X.Joins e a b) : H.Joins (β e) (α a) (α b) := by
  have h := hj e he
  rcases hab with hab | hab <;> rw [hab] at h <;> simp only at h
  · exact h
  · exact Or.symm h

/-- **transfer of far-exchange existence along `IsoFrom`** -/
theorem fe_transfer (hI : IsoFrom P H) (hG : FEGood H) :
    ∀ g, P g → ∀ t : Bool, ∃ M, PMOn P M ∧ (M g ↔ t = true) ∧ ∃ C, FarEx P M C := by
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := hI
  intro g hg t
  obtain ⟨MH, hPM, hst, CH, hFE⟩ := hG (β g) t
  obtain ⟨hFE0, hFEa, hFEb, hFEc⟩ := hFE
  -- two edges of `P` meeting in `X` have images meeting in `H`, and conversely
  have meet_map : ∀ p c, P p → P c → Meet p c → Meet (β p) (β c) := by
    rintro p c hp hc ⟨x, hpx, hcx⟩
    exact ⟨α x, fe_inc_map hj hp hpx, fe_inc_map hj hc hcx⟩
  have meet_back : ∀ p c, P p → P c → Meet (β p) (β c) → Meet p c := by
    rintro p c hp hc ⟨y, hpy, hcy⟩
    obtain ⟨x, hx, rfl⟩ := fe_inc_back hj hp hpy
    obtain ⟨x', hx', hxx⟩ := fe_inc_back hj hc hcy
    have := hα _ _ (fe_meets hc hx') (fe_meets hp hx) hxx
    subst this
    exact ⟨x', hx, hx'⟩
  refine ⟨fun f => P f ∧ MH (β f), ⟨fun f hf => hf.1, ?_⟩, ?_, fun f => P f ∧ CH (β f), ?_, ?_, ?_, ?_⟩
  · -- perfect matching
    rintro x ⟨f, hf, hfx⟩
    obtain ⟨a', hMa', hinc', hu⟩ := hPM.2 (α x) ⟨β f, trivial, fe_inc_map hj hf hfx⟩
    obtain ⟨a, ha, rfl⟩ := hs a'
    obtain ⟨x', hx', hxx⟩ := fe_inc_back hj ha hinc'
    have := hα _ _ (fe_meets ha hx') (fe_meets hf hfx) hxx
    subst this
    refine ⟨a, ⟨ha, hMa'⟩, hx', ?_⟩
    rintro d ⟨hd, hMd⟩ hdx
    exact hβ d a hd ha (hu (β d) hMd (fe_inc_map hj hd hdx))
  · -- status
    constructor
    · rintro ⟨_, h⟩; exact hst.1 h
    · intro h; exact ⟨hg, hst.2 h⟩
  · -- `C` misses `M`
    rintro f ⟨hf, hC⟩
    exact ⟨hf, fun hM => (hFE0 (β f) hC).2 hM.2⟩
  · -- (a)
    rintro p c1 c2 ⟨hp, hMp⟩ ⟨hc1, hC1⟩ ⟨hc2, hC2⟩ hm1 hm2
    exact hβ c1 c2 hc1 hc2 (hFEa (β p) (β c1) (β c2) hMp hC1 hC2 (meet_map p c1 hp hc1 hm1) (meet_map p c2 hp hc2 hm2))
  · -- (b′)
    rintro e he hMe hCe hnp ⟨⟨c1, ⟨hc1, hC1⟩, hi1⟩, ⟨c2, ⟨hc2, hC2⟩, hi2⟩⟩
    have hMe' : ¬ MH (β e) := fun h => hMe ⟨he, h⟩
    have hCe' : ¬ CH (β e) := fun h => hCe ⟨he, h⟩
    have hb := hFEb (β e) trivial hMe' hCe'
    have hje := hj e he
    by_cases hex : ∃ c', CH c' ∧ H.Joins c' (H.ends (β e)).1 (H.ends (β e)).2
    · obtain ⟨c', hC', hjc'⟩ := hex
      obtain ⟨c, hc, rfl⟩ := hs c'
      have hjc := hj c hc
      have hj2 : H.Joins (β c) (α (X.ends e).1) (α (X.ends e).2) := by
        rcases hje with h | h <;> rw [h] at hjc' <;> simp only at hjc'
        · exact hjc'
        · exact Or.symm hjc'
      apply hnp
      refine ⟨c, ⟨hc, hC'⟩, ?_⟩
      have m1 : meets P (X.ends c).1 := ⟨c, hc, Or.inl rfl⟩
      have m2 : meets P (X.ends c).2 := ⟨c, hc, Or.inr rfl⟩
      have n1 : meets P (X.ends e).1 := ⟨e, he, Or.inl rfl⟩
      have n2 : meets P (X.ends e).2 := ⟨e, he, Or.inr rfl⟩
      rcases joins_unique hjc hj2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · left; exact Prod.ext (hα _ _ m1 n1 a1) (hα _ _ m2 n2 a2)
      · right; exact Prod.ext (hα _ _ m1 n2 a1) (hα _ _ m2 n1 a2)
    · apply hb hex
      have i1 := fe_inc_map hj hc1 hi1
      have i2 := fe_inc_map hj hc2 hi2
      rcases hje with h | h <;> rw [h] <;> simp only
      · exact ⟨⟨β c1, hC1, i1⟩, ⟨β c2, hC2, i2⟩⟩
      · exact ⟨⟨β c2, hC2, i2⟩, ⟨β c1, hC1, i1⟩⟩
  · -- (c)
    rintro p p' ⟨hp, hMp⟩ ⟨hp', hMp'⟩ hne hfp hfp'
    have hne' : β p ≠ β p' := fun h => hne (hβ p p' hp hp' h)
    have hf : ∀ q, P q → (∀ c, (P c ∧ CH (β c)) → ¬ Meet q c) → ∀ c', CH c' → ¬ Meet (β q) c' := by
      intro q hq hfq c' hC' hm
      obtain ⟨c, hc, rfl⟩ := hs c'
      exact hfq c ⟨hc, hC'⟩ (meet_back q c hq hc hm)
    have hD := hFEc (β p) (β p') hMp hMp' hne' (hf p hp hfp) (hf p' hp' hfp')
    intro a b ha hb
    obtain ⟨hab, hnj, hnp⟩ := hD (α a) (α b) (fe_inc_map hj hp ha) (fe_inc_map hj hp' hb)
    refine ⟨fun h => hab (h ▸ rfl), ?_, ?_⟩
    · rintro ⟨e, he, hje⟩
      exact hnj ⟨β e, trivial, fe_joins_map hj he hje⟩
    · rintro ⟨e1, e2, z, he1, he2, hj1, hj2⟩
      exact hnp ⟨β e1, β e2, α z, trivial, trivial, fe_joins_map hj he1 hj1, fe_joins_map hj he2 hj2⟩

end fe2

end RH2F

-- ===== from FE3.lean =====
/-
  FE3 — excluding non-c4c graphs by a kernel-checked cut witness, and the classification step for the cyclically
  4-edge-connected members of 𝒮 (C4C, fact 81c52cea8147de67) from insertion tables whose rows are either an
  isomorphism onto a listed graph or a cut witness of the insertion.
-/

namespace RH2F
open MGraph

section fe3

/-- `P` is not isomorphic to any c4c edge set -/
def NC4 (H : MGraph) : Prop := ∀ (Y : MGraph) (Q : Fin Y.m → Prop), IsoFrom Q H → ¬ C4C Y Q

/-- the field of width `w` at offset `o` of `W` -/
def fld (W o w : Nat) : Nat := (W >>> o) % 2 ^ w

/-- edge `e` of `el` crosses the vertex set `U` -/
def crsB (el : List (Nat × Nat)) (U e : Nat) : Bool := U.testBit (gER el e).1 != U.testBit (gER el e).2

/-- the selected end `v / 2` of edge `v / 2`… : the vertex coded by `v` (`v = 2 e + s`) -/
def vtx (el : List (Nat × Nat)) (v : Nat) : Nat := endS el (v / 2) (v % 2)

/-- the cut witness `W`: side `U = fld W 0 16`, the `k = fld W 16 2 ∈ {2, 3}` crossing edges
    `c0 = fld W 18 5`, `c1 = fld W 23 5`, `c2 = fld W 28 5`, and vertices `A, B ∈ U`, `C, D ∉ U` coded by
    `fld W 33 6`, `fld W 39 6`, `fld W 45 6`, `fld W 51 6` -/
def cutB (el : List (Nat × Nat)) (W : Nat) : Bool :=
  let U := fld W 0 16
  let k := fld W 16 2
  let c0 := fld W 18 5
  let c1 := fld W 23 5
  let c2 := fld W 28 5
  let A := fld W 33 6
  let B := fld W 39 6
  let C := fld W 45 6
  let D := fld W 51 6
  (Nat.beq k 2 || Nat.beq k 3) &&
  Nat.blt c0 el.length && Nat.blt c1 el.length && (Nat.beq k 2 || Nat.blt c2 el.length) &&
  !Nat.beq c0 c1 && (Nat.beq k 2 || (!Nat.beq c0 c2 && !Nat.beq c1 c2)) &&
  crsB el U c0 && crsB el U c1 && (Nat.beq k 2 || crsB el U c2) &&
  rangeAll el.length (fun e => !crsB el U e || Nat.beq e c0 || Nat.beq e c1 || (Nat.beq k 3 && Nat.beq e c2)) &&
  Nat.blt (A / 2) el.length && Nat.blt (B / 2) el.length && Nat.blt (C / 2) el.length && Nat.blt (D / 2) el.length &&
  !Nat.beq (vtx el A) (vtx el B) && !Nat.beq (vtx el C) (vtx el D) &&
  U.testBit (vtx el A) && U.testBit (vtx el B) && !U.testBit (vtx el C) && !U.testBit (vtx el D)

theorem two_le_cntF {n : Nat} {W : Fin n → Prop} {i j : Fin n} (hi : W i) (hj : W j) (hij : i ≠ j) :
    2 ≤ cntF n W := by
  rw [cntF_split n W (fun k => k = i)]
  have h1 := cntF_le_of_mem n (fun k => W k ∧ k = i) (i := i) ⟨hi, rfl⟩
  have h2 := cntF_le_of_mem n (fun k => W k ∧ ¬ k = i) (i := j) ⟨hj, fun h => hij h.symm⟩
  omega

variable {N : Nat} {el : List (Nat × Nat)} {hN : 0 < N}

theorem vtx_lt (hel : elOK N el = true) {v : Nat} (hv : v / 2 < el.length) : vtx el v < N := by
  have := fe_ends_lt hel hv
  unfold vtx endS
  cases Nat.beq (v % 2) 0
  · exact this.2
  · exact this.1

theorem vtx_inc (hel : elOK N el = true) {v : Nat} (hv : v / 2 < el.length) :
    (ofList N el hN).Inc ⟨v / 2, hv⟩ ⟨vtx el v, vtx_lt hel hv⟩ := by
  rw [fe_inc_iff hel]
  show (gER el (v / 2)).1 = vtx el v ∨ (gER el (v / 2)).2 = vtx el v
  unfold vtx endS
  cases Nat.beq (v % 2) 0
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem nb_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h
theorem nb_false {a b : Nat} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact absurd h (by decide)
theorem nblt {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

/-- **a cut witness excludes c4c** -/
theorem nc4_of_cutB (hel : elOK N el = true) {W : Nat} (h : cutB el W = true) : NC4 (ofList N el hN) := by
  intro Y Q ⟨α, β, hα, hβ, hs, hj⟩ hC
  simp only [cutB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hc0⟩, hc1⟩, hc2⟩, h01⟩, h012⟩, x0⟩, x1⟩, x2⟩, hall⟩, lA⟩, lB⟩, lC⟩, lD⟩,
    hAB⟩, hCD⟩, uA⟩, uB⟩, uC⟩, uD⟩ := h
  let U := fld W 0 16
  let S : Fin Y.n → Bool := fun y => U.testBit (α y).val
  -- crossing is preserved
  have hcr : ∀ f, Q f → (Crosses Q S f ↔ crsB el U (β f).val = true) := by
    intro f hf
    have hjf := (fe_joins_iff hel).1 (hj f hf)
    unfold Crosses crsB
    rcases hjf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp only [bne_iff_ne, ne_eq, S]
    · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
    · exact ⟨fun h e => h.2 e.symm, fun h => ⟨hf, fun e => h e.symm⟩⟩
  -- the crossing edges
  have pre : ∀ c, c < el.length → crsB el U c = true → ∃ f, Q f ∧ (β f).val = c ∧ Crosses Q S f := by
    intro c hc hx
    obtain ⟨f, hf, hfe⟩ := hs ⟨c, hc⟩
    refine ⟨f, hf, by rw [hfe], (hcr f hf).2 (by rw [hfe]; exact hx)⟩
  obtain ⟨f0, hq0, hb0, cr0⟩ := pre _ (nblt hc0) x0
  obtain ⟨f1, hq1, hb1, cr1⟩ := pre _ (nblt hc1) x1
  have hne01 : f0 ≠ f1 := fun e => nb_false h01 (by rw [← hb0, ← hb1, e])
  have hall' : ∀ d, Crosses Q S d → (β d).val = fld W 18 5 ∨ (β d).val = fld W 23 5 ∨
      (Nat.beq (fld W 16 2) 3 = true ∧ (β d).val = fld W 28 5) := by
    intro d hd
    have := fe_rangeAll hall (β d).isLt
    rw [(hcr d hd.1).1 hd] at this
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at this
    rcases this with (h | h) | ⟨h3, h⟩
    · exact Or.inl (nb_true h)
    · exact Or.inr (Or.inl (nb_true h))
    · exact Or.inr (Or.inr ⟨h3, nb_true h⟩)
  have eqpre : ∀ d f, Q f → Crosses Q S d → (β d).val = (β f).val → d = f :=
    fun d f hf hd e => hβ d f hd.1 hf (Fin.ext e)
  -- vertices of the witness
  have vert : ∀ a, a / 2 < el.length → ∃ y, meets Q y ∧ (α y).val = vtx el a := by
    intro a ha
    obtain ⟨f, hf, hfe⟩ := hs ⟨a / 2, ha⟩
    have hi := vtx_inc (hN := hN) hel ha
    rw [← hfe] at hi
    obtain ⟨y, hy, hya⟩ := fe_inc_back hj hf hi
    exact ⟨y, ⟨f, hf, hy⟩, by rw [hya]⟩
  have two : ∀ b : Bool, ∀ a a', a / 2 < el.length → a' / 2 < el.length → vtx el a ≠ vtx el a' →
      U.testBit (vtx el a) = b → U.testBit (vtx el a') = b → 2 ≤ scount Q S b := by
    intro b a a' ha ha' hne hb hb'
    obtain ⟨y, my, hy⟩ := vert a ha
    obtain ⟨y', my', hy'⟩ := vert a' ha'
    refine two_le_cntF (i := y) (j := y') ⟨my, ?_⟩ ⟨my', ?_⟩ ?_
    · show U.testBit (α y).val = b; rw [hy]; exact hb
    · show U.testBit (α y').val = b; rw [hy']; exact hb'
    · intro e; subst e; exact hne (hy.symm.trans hy')
  rw [Bool.or_eq_true] at hk
  rcases hk with hk | hk
  · -- two crossing edges: a 2-edge-cut
    have h3 : Nat.beq (fld W 16 2) 3 = false := by rw [nb_true hk]; rfl
    apply hC.2.1 S
    refine ⟨f0, f1, hne01, cr0, cr1, fun d hd => ?_⟩
    rcases hall' d hd with h | h | ⟨h, _⟩
    · exact Or.inl (eqpre d f0 hq0 hd (h.trans hb0.symm))
    · exact Or.inr (eqpre d f1 hq1 hd (h.trans hb1.symm))
    · rw [h3] at h; exact absurd h (by decide)
  · -- three crossing edges with at least two vertices on each side
    have h2 : Nat.beq (fld W 16 2) 2 = false := by rw [nb_true hk]; rfl
    rw [h2, Bool.false_or] at hc2 h012 x2
    simp only [Bool.and_eq_true] at h012
    obtain ⟨f2, hq2, hb2, cr2⟩ := pre _ (nblt hc2) x2
    have hne02 : f0 ≠ f2 := fun e => nb_false h012.1 (by rw [← hb0, ← hb2, e])
    have hne12 : f1 ≠ f2 := fun e => nb_false h012.2 (by rw [← hb1, ← hb2, e])
    have h3c := hC.2.2 S ⟨f0, f1, f2, hne01, hne02, hne12, cr0, cr1, cr2, fun d hd => by
      rcases hall' d hd with h | h | ⟨_, h⟩
      · exact Or.inl (eqpre d f0 hq0 hd (h.trans hb0.symm))
      · exact Or.inr (Or.inl (eqpre d f1 hq1 hd (h.trans hb1.symm)))
      · exact Or.inr (Or.inr (eqpre d f2 hq2 hd (h.trans hb2.symm)))⟩
    have t1 := two true _ _ (nblt lA) (nblt lB) (nb_false hAB) uA uB
    have t2 := two false _ _ (nblt lC) (nblt lD) (nb_false hCD)
      (by simpa using uC) (by simpa using uD)
    omega

end fe3

end RH2F

-- ===== from FE4.lean =====
/-
  FE4 — insertion tables with cut-witness rows, and the classification step for c4c members of 𝒮.
-/

namespace RH2F
open MGraph

section fe4

theorem nc4_of_conc {H H' : MGraph} (hc : ConcIso H H') (h : NC4 H') : NC4 H :=
  fun Y Q hI => h Y Q (isoFrom_trans hI hc)

/-- walk along the rows (row at position `q` belongs to the pair `(q / m, q % m)`, used only if `q / m < q % m`):
    row `(k', S)` with `k' < K2` says `Ins(el, i, j) ≅ L2[k']` via the vertex permutation `sv S`; a row `(k', W)`
    with `k' ≥ K2` gives a cut witness `W` of `Ins(el, i, j)` -/
def walkW (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) (rows : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun r _ ih q =>
    (Nat.ble (q % el.length) (q / el.length) ||
      cond (Nat.blt r.1 K2)
        (permB (n + 2) r.2 &&
          Nat.beq (mapGo r.2 n (q / el.length) (q % el.length)
            [(n, (gER el (q / el.length)).2), (n + 1, (gER el (q % el.length)).2), (n, n + 1)] el 0)
            (slice AD r.1))
        (cutB (insL n el (q / el.length) (q % el.length)) r.2))
    && ih (q + 1)) rows

/-- the insertion table (with cut witnesses) of host `el` -/
def tabW (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) (rows : List (Nat × Nat)) : Bool :=
  Nat.beq rows.length (el.length * el.length) && walkW n el K2 AD rows 0

/-- the body of row `q` -/
def rowW (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) (r : Nat × Nat) (q : Nat) : Bool :=
  Nat.ble (q % el.length) (q / el.length) ||
    cond (Nat.blt r.1 K2)
      (permB (n + 2) r.2 &&
        Nat.beq (mapGo r.2 n (q / el.length) (q % el.length)
          [(n, (gER el (q / el.length)).2), (n + 1, (gER el (q % el.length)).2), (n, n + 1)] el 0)
          (slice AD r.1))
      (cutB (insL n el (q / el.length) (q % el.length)) r.2)

theorem walkW_get (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) :
    ∀ (rows : List (Nat × Nat)) (q0 : Nat), walkW n el K2 AD rows q0 = true → ∀ r, r < rows.length →
      rowW n el K2 AD (rows.getD r (0, 0)) (q0 + r) = true
  | [], _, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | row :: rows, q0, h, r, hr => by
    have h' : (rowW n el K2 AD row q0 && walkW n el K2 AD rows (q0 + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases r with
    | zero => simpa using h'.1
    | succ r =>
      have := walkW_get n el K2 AD rows (q0 + 1) h'.2 r (by simp at hr; omega)
      rw [show q0 + 1 + r = q0 + (r + 1) by omega] at this
      simpa using this

/-- the row of the pair `i < j` of a passed table -/
theorem tabW_row {n : Nat} {el : List (Nat × Nat)} {L2 : List (List (Nat × Nat))} {K2 AD m2 : Nat}
    {rows : List (Nat × Nat)} (h : tabW n el K2 AD rows = true) (hel : elOK n el = true)
    (hL2 : repsB (n + 2) m2 L2 = true) (hm2 : el.length + 3 = m2) (hK2 : L2.length = K2)
    (hAD : adGo AD L2 0 = true) (h16 : n + 2 ≤ 16) (hn2 : 0 < n + 2)
    {i j : Nat} (hi : i < el.length) (hj : j < el.length) (hij : i < j) : (∃ k', k' < L2.length ∧
      ConcIso (ofList (n + 2) (insL n el i j) hn2) (ofList (n + 2) (L2.getD k' []) hn2)) ∨
      NC4 (ofList (n + 2) (insL n el i j) hn2) := by
  unfold tabW at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlen, hw⟩ := h
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hq : i * el.length + j < rows.length := by
    rw [hlen']
    have : i * el.length + j < (i + 1) * el.length := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hi)
  have h1 := walkW_get n el K2 AD rows 0 hw _ hq
  have hpos : 0 < el.length := by omega
  have hdiv : (0 + (i * el.length + j)) / el.length = i := by
    rw [Nat.zero_add, Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (0 + (i * el.length + j)) % el.length = j := by
    rw [Nat.zero_add, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  unfold rowW at h1
  rw [hdiv, hmod] at h1
  simp only [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd (Nat.le_of_ble_eq_true h1) (by omega)
  · cases hk : Nat.blt (rows.getD (i * el.length + j) (0, 0)).1 K2 with
    | false =>
      rw [hk] at h1
      exact Or.inr (nc4_of_cutB (elOK_insL hel hi hj) h1)
    | true =>
      rw [hk] at h1
      simp only [cond_true, Bool.and_eq_true] at h1
      obtain ⟨hp, hA⟩ := h1
      left
      have hk' : (rows.getD (i * el.length + j) (0, 0)).1 < L2.length := hK2 ▸ nblt hk
      refine ⟨_, hk', ?_⟩
      obtain ⟨hel2, hlen2, hfr2⟩ := repsB_get hL2 hk'
      have hA' := Nat.eq_of_beq_eq_true hA
      rw [mapGo_eq] at hA'
      have hs := adGo_sound AD L2 0 hAD _ hk'
      rw [Nat.zero_add] at hs
      rw [hs] at hA'
      have hins : insGo n i j [(n, (gER el i).2), (n + 1, (gER el j).2), (n, n + 1)] el 0 = insL n el i j := rfl
      rw [hins] at hA'
      exact concIso_of_adj h16 (elOK_insL hel hi hj) hel2 hfr2 (by rw [length_insL, hlen2, hm2]) hp hA'

/-- the property of host `k` of `L` delivered by its table -/
def HostTabW (n : Nat) (L L2 : List (List (Nat × Nat))) (hn : 0 < n) (hn2 : 0 < n + 2) (k : Nat) : Prop :=
  ∀ i j : Fin (ofList n (L.getD k []) hn).m, i ≠ j → (∃ k', k' < L2.length ∧
    ConcIso (ofList (n + 2) (insL n (L.getD k []) i.val j.val) hn2) (ofList (n + 2) (L2.getD k' []) hn2)) ∨
    NC4 (ofList (n + 2) (insL n (L.getD k []) i.val j.val) hn2)

theorem hostTabW_of_tabW {n : Nat} {L L2 : List (List (Nat × Nat))} {K2 AD m2 : Nat} {k : Nat}
    {rows : List (Nat × Nat)} (h : tabW n (L.getD k []) K2 AD rows = true) (hel : elOK n (L.getD k []) = true)
    (hL2 : repsB (n + 2) m2 L2 = true) (hm2 : (L.getD k []).length + 3 = m2) (hK2 : L2.length = K2)
    (hAD : adGo AD L2 0 = true) (h16 : n + 2 ≤ 16) (hn : 0 < n) (hn2 : 0 < n + 2) :
    HostTabW n L L2 hn hn2 k := by
  intro i j hij
  have hi : i.val < (L.getD k []).length := i.isLt
  have hj : j.val < (L.getD k []).length := j.isLt
  have hne : i.val ≠ j.val := fun h' => hij (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact tabW_row h hel hL2 hm2 hK2 hAD h16 hn2 hi hj hlt
  · have hsw := insL_swap hel hi hj hne hn2
    rcases tabW_row h hel hL2 hm2 hK2 hAD h16 hn2 hj hi hgt with ⟨k', hk', hc⟩ | hnc
    · exact Or.inl ⟨k', hk', concIso_trans hsw hc⟩
    · exact Or.inr (nc4_of_conc hsw hnc)

/-- the tables of the hosts `k0, k0 + 1, …` (entry `r` of `TD` is the table of host `k0 + r`) -/
def tabRangeW (n : Nat) (L : List (List (Nat × Nat))) (K2 AD : Nat) (k0 : Nat) (TD : List (List (Nat × Nat))) : Bool :=
  rangeAll TD.length (fun r => tabW n (getR L (k0 + r) []) K2 AD (getR TD r []))

theorem hostTabW_of_range {n : Nat} {L L2 : List (List (Nat × Nat))} {K2 AD m m2 : Nat} {k0 : Nat}
    {TD : List (List (Nat × Nat))} (h : tabRangeW n L K2 AD k0 TD = true)
    (hL : repsB n m L = true) (hL2 : repsB (n + 2) m2 L2 = true) (hm2 : m + 3 = m2) (hK2 : L2.length = K2)
    (hAD : adGo AD L2 0 = true) (h16 : n + 2 ≤ 16) (hn : 0 < n) (hn2 : 0 < n + 2) :
    ∀ k, k0 ≤ k → k < k0 + TD.length → k < L.length → HostTabW n L L2 hn hn2 k := by
  intro k hk0 hk1 hkL
  unfold tabRangeW at h
  rw [rangeAll_eq, List.all_eq_true] at h
  have h1 := h (k - k0) (List.mem_range.2 (by omega))
  have e : k0 + (k - k0) = k := by omega
  rw [e, getR_eq, getR_eq] at h1
  obtain ⟨hel, hlen, _⟩ := repsB_get hL hkL
  exact hostTabW_of_tabW h1 hel hL2 (by rw [hlen, hm2]) hK2 hAD h16 hn hn2

/-- a c4c simple edge set is in 𝒮 -/
theorem inS_of_c4c {X : MGraph} {P : Fin X.m → Prop} (hC : C4C X P) (hS : SimpleP P) : InS X P :=
  ⟨hC.1, hS, hC.2.1⟩

/-- **classification step for c4c**: a classification of 𝒮 at `n ≥ 4` vertices by `L` and complete insertion
    tables with cut witnesses give a classification of the simple c4c edge sets at `n + 2` vertices by `L2` -/
theorem cls_stepC {n : Nat} (hn4 : 4 ≤ n) {L L2 : List (List (Nat × Nat))} (hn : 0 < n) (hn2 : 0 < n + 2)
    (hL : repsOK n L = true)
    (ih : ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n →
      ∃ k, k < L.length ∧ IsoFrom P (ofList n (L.getD k []) hn))
    (htab : ∀ k, k < L.length → HostTabW n L L2 hn hn2 k) :
    ∀ (X : MGraph) (P : Fin X.m → Prop), C4C X P → SimpleP P → vcount P = n + 2 →
      ∃ k, k < L2.length ∧ IsoFrom P (ofList (n + 2) (L2.getD k []) hn2) := by
  intro X P hC hS hv
  obtain ⟨R, hR⟩ := removable (inS_of_c4c hC hS) (by omega)
  have hvr : vcount R.redP = n := by have := R.vcount_red; omega
  obtain ⟨k, hk, hiso⟩ := ih _ _ hR hvr
  obtain ⟨i, j, hij, hiso2⟩ := R.lift hiso
  have hI := isoFrom_trans hiso2 (ins_conc (repsOK_get hL hk) i j hij hn2)
  rcases htab k hk i j hij with ⟨k', hk', hc⟩ | hnc
  · exact ⟨k', hk', isoFrom_trans hI hc⟩
  · exact absurd hC (hnc X P hI)

end fe4

end RH2F

-- ===== from FE5.lean =====
/-
  FE5 — the per-host check for far-exchange existence on digon insertions with 16 vertices: a host of 𝒮_q is either
  excluded by a cut witness (not c4c), or its automorphisms and representative marking codes cover all markings with
  `(16 - q) / 2` digons, and each representative digon insertion carries a far-exchange certificate.
-/

namespace RH2F
open MGraph

section fe5

/-- far-exchange existence at every edge and status of `P` -/
def FEAll {X : MGraph} (P : Fin X.m → Prop) : Prop :=
  ∀ g, P g → ∀ t : Bool, ∃ M, PMOn P M ∧ (M g ↔ t = true) ∧ ∃ C, FarEx P M C

/-- the certificate of the digon insertion of `el` at the marking code `rc` -/
def feCertD (q : Nat) (el : List (Nat × Nat)) (rc : Nat) (L : List FES) : Bool :=
  feCert (q + 2 * cntT (decodeB el.length rc)) (digEl q el (decodeB el.length rc)) L

theorem feGood_of_certD {q : Nat} {hq : 0 < q} {el : List (Nat × Nat)} {rc : Nat} {L : List FES}
    (h : feCertD q el rc L = true) : FEGood (digGrC q hq el rc) :=
  feGood_of_cert h

/-- the conclusion for a host `el` of `𝒮_q` -/
def HostFE (q lo hi : Nat) (hq : 0 < q) (el : List (Nat × Nat)) : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), C4C Y Q → IsoFrom Q (ofList q el hq) →
    lo ≤ q + 2 * cntF Y.m (fun d => Q d ∧ D d) → cntF Y.m (fun d => Q d ∧ D d) ≤ hi → FEAll (digSet Q D)

/-- a host with a cut witness is not c4c -/
theorem hostFE_of_cut {q lo hi : Nat} {hq : 0 < q} {el : List (Nat × Nat)} {W : Nat} (hel : elOK q el = true)
    (h : cutB el W = true) : HostFE q lo hi hq el :=
  fun Y Q _ hC hiso _ _ => absurd hC (nc4_of_cutB hel h Y Q hiso)

/-- the coverage check of a host: loopless list with edges, cheap automorphisms `AUT`, and all markings with
    `lo ≤ q + 2 d`, `d ≤ hi` covered by the codes `RC` -/
def covFE (q lo hi : Nat) (el : List (Nat × Nat)) (AUT : List (Nat × List Nat)) (RC : List Nat) : Bool :=
  elOK q el && Nat.blt 0 el.length && allR (fun a => autOKB q el.length (encE el) a.1 a.2) AUT &&
    covS q lo hi el.length (orSet (AUT.map Prod.snd) RC)

/-- the certificates of the codes of a host -/
def certsFE (q : Nat) (el : List (Nat × Nat)) (CS : List (Nat × List FES)) : Bool :=
  allR (fun c => feCertD q el c.1 c.2) CS

theorem allR_append' {α : Type} (p : α → Bool) (l l' : List α) : allR p (l ++ l') = (allR p l && allR p l') := by
  rw [allR_eq, allR_eq, allR_eq, List.all_append]

/-- **a covered host with certified codes** -/
theorem hostFE_of_parts {q lo hi : Nat} {hq : 0 < q} (hq16 : q ≤ 16) {el : List (Nat × Nat)}
    {AUT : List (Nat × List Nat)} {CS : List (Nat × List FES)} (hcov : covFE q lo hi el AUT (CS.map Prod.fst) = true)
    (hcs : certsFE q el CS = true) : HostFE q lo hi hq el := by
  intro Y Q D hC hiso hlo hhi
  unfold covFE at hcov
  simp only [Bool.and_eq_true] at hcov
  obtain ⟨⟨⟨hel, hm0⟩, haut⟩, hcov⟩ := hcov
  let AUTL : List (List Nat × List Nat) := AUT.map (fun a => ((List.range q).map (sv a.1), a.2))
  have haut' : allR (autOKR q el) AUTL = true := by
    rw [allR_eq, List.all_eq_true]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rw [allR_eq, List.all_eq_true] at haut
    have := autOK_of_autOKB hel hq16 (haut b hb)
    unfold autOKR
    simp only [Bool.and_eq_true]
    refine ⟨?_, nbeq_true this.2⟩
    have h1 := this.1
    unfold autOK at h1
    simpa only [rangeAll_eq, getR_eq, anyR_eq, gER, gE, Bool.and_eq_true] using h1
  have hmap : AUTL.map Prod.snd = AUT.map Prod.snd := by
    simp [AUTL, List.map_map, Function.comp_def]
  rw [← hmap] at hcov
  obtain ⟨rc, hrc, hI⟩ := dig_class_code hC.1.1 hiso hel (Nat.le_of_ble_eq_true hm0) hlo hhi haut' hcov
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hrc
  have hG := feGood_of_certD (hq := hq) (allR_mem hcs hc)
  exact fe_transfer hI hG

/-- the per-`q` conclusion from the host conclusions and the classification of 𝒮_q -/
theorem fe_of_hosts {q lo hi : Nat} {hq : 0 < q} {L : List (List (Nat × Nat))}
    (hcls : ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = q →
      ∃ k, k < L.length ∧ IsoFrom P (ofList q (L.getD k []) hq))
    (hh : ∀ k, k < L.length → HostFE q lo hi hq (L.getD k [])) :
    ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), C4C Y Q → SimpleP Q → vcount Q = q →
      lo ≤ q + 2 * cntF Y.m (fun d => Q d ∧ D d) → cntF Y.m (fun d => Q d ∧ D d) ≤ hi → FEAll (digSet Q D) := by
  intro Y Q D hC hS hv hlo hhi
  obtain ⟨k, hk, hI⟩ := hcls Y Q (inS_of_c4c hC hS) hv
  exact hh k hk Y Q D hC hI hlo hhi

/-- the case without digons on `16` vertices: the c4c classification `L` and certificates at the code `0` -/
def rangeFE0 (q : Nat) (L : List (List (Nat × Nat))) (k0 : Nat) (CS : List (List FES)) : Bool :=
  rangeAll CS.length (fun r => elOK q (getR L (k0 + r) []) && Nat.blt 0 (getR L (k0 + r) []).length &&
    feCertD q (getR L (k0 + r) []) 0 (getR CS r []))

/-- the conclusion for c4c host `k` without digons -/
def HostFE0 (q : Nat) (hq : 0 < q) (L : List (List (Nat × Nat))) (k : Nat) : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Loopless Y → IsoFrom Q (ofList q (L.getD k []) hq) →
    cntF Y.m (fun d => Q d ∧ D d) = 0 → FEAll (digSet Q D)

theorem hostFE0_of_range {q : Nat} {hq : 0 < q} {L : List (List (Nat × Nat))} {k0 : Nat} {CS : List (List FES)}
    (h : rangeFE0 q L k0 CS = true) : ∀ k, k0 ≤ k → k < k0 + CS.length → HostFE0 q hq L k := by
  intro k hk0 hk1 Y Q D hloop hI h0
  unfold rangeFE0 at h
  have h1 := fe_rangeAll h (i := k - k0) (by omega)
  have e : k0 + (k - k0) = k := by omega
  rw [e, getR_eq, getR_eq] at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨hel, hm0⟩, hc⟩ := h1
  have hI0 := dig_class_zero hloop hI hel (nblt hm0) h0
  exact fe_transfer hI0 (feGood_of_certD hc)

theorem certsFE_append (q : Nat) (el : List (Nat × Nat)) (l l' : List (Nat × List FES)) :
    certsFE q el (l ++ l') = (certsFE q el l && certsFE q el l') := allR_append' _ _ _

/-- stepping a range statement -/
theorem rangeP_step {P : Nat → Prop} {a b : Nat} (h : P a) (ih : ∀ k, a + 1 ≤ k → k < b → P k) :
    ∀ k, a ≤ k → k < b → P k := fun k h1 h2 => if e : k = a then e ▸ h else ih k (by omega) h2

theorem rangeP_nil {P : Nat → Prop} {b : Nat} : ∀ k, b ≤ k → k < b → P k :=
  fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl b)

theorem rangeP_join {P : Nat → Prop} {a b c : Nat} (h1 : ∀ k, a ≤ k → k < b → P k) (h2 : ∀ k, b ≤ k → k < c → P k) :
    ∀ k, a ≤ k → k < c → P k := fun k ha hc => if e : k < b then h1 k ha e else h2 k (by omega) hc

end fe5

end RH2F

-- ===== from P16C.lean =====
namespace RH2F
open MGraph

/-- the 607 cyclically 4-edge-connected simple cubic graphs on 16 vertices -/
def c16 : List (List (Nat × Nat)) := [
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 14), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 12), (5, 10), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (6, 15), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 11), (2, 13), (3, 9), (3, 13), (3, 14), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 11), (2, 13), (3, 9), (3, 13), (3, 14), (4, 10), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (6, 15), (7, 12), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 11), (5, 13), (6, 12), (6, 13), (6, 14), (7, 12), (7, 13), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 10), (5, 13), (5, 15), (6, 11), (6, 12), (6, 14), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 10), (5, 13), (5, 15), (6, 11), (6, 12), (6, 13), (7, 12), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 12), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 13), (3, 14), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (6, 14), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 14), (7, 13), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 13), (3, 14), (4, 10), (4, 11), (4, 12), (5, 10), (5, 13), (5, 15), (6, 11), (6, 14), (6, 15), (7, 12), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 13), (5, 14), (6, 11), (6, 13), (6, 15), (7, 12), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 13), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 12), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (6, 15), (7, 12), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (6, 15), (7, 12), (7, 13), (7, 14)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 13), (3, 15), (4, 10), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 13), (7, 11), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 10), (5, 12), (5, 14), (6, 11), (6, 12), (6, 13), (7, 11), (7, 13), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 11), (1, 13), (2, 8), (2, 12), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 12), (5, 13), (6, 10), (6, 14), (6, 15), (7, 11), (7, 14), (7, 15)],
  [(0, 8), (0, 9), (0, 10), (1, 8), (1, 11), (1, 13), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 14), (6, 10), (6, 13), (6, 15), (7, 11), (7, 14), (7, 15)],
  [(0, 7), (0, 8), (0, 9), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 10), (3, 11), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 11), (3, 14), (4, 10), (4, 12), (4, 15), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 12), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 11), (6, 12), (6, 15), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 11), (6, 12), (6, 15), (7, 13), (7, 14), (8, 13)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 11), (3, 14), (4, 10), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 13), (8, 15)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 11), (7, 13), (8, 15)],
  [(0, 7), (0, 8), (0, 14), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 8), (0, 14), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 10), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 15), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 14), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 13), (3, 9), (3, 12), (3, 13), (4, 10), (4, 14), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 8), (0, 14), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 8), (0, 14), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 10), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 13), (3, 14), (4, 10), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 12), (2, 13), (3, 9), (3, 13), (3, 14), (4, 10), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 8), (0, 15), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 14), (3, 9), (3, 11), (3, 13), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 11), (8, 12)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 15), (3, 9), (3, 12), (3, 13), (4, 11), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 11), (8, 14)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 10), (2, 13), (3, 9), (3, 13), (3, 14), (4, 11), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 10), (7, 11), (8, 15)],
  [(0, 7), (0, 8), (0, 11), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 12), (3, 9), (3, 12), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 10), (7, 12), (8, 13)],
  [(0, 7), (0, 8), (0, 11), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 12), (3, 9), (3, 13), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 14), (6, 13), (6, 14), (6, 15), (7, 10), (7, 12), (8, 13)],
  [(0, 7), (0, 8), (0, 11), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 12), (3, 9), (3, 13), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 10), (7, 12), (8, 13)],
  [(0, 7), (0, 8), (0, 11), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 13), (6, 15), (7, 10), (7, 12), (8, 13)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 12), (3, 13), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 10), (7, 11), (8, 15)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 13), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 11), (8, 15)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 11), (8, 15)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 14), (6, 12), (6, 13), (6, 15), (7, 10), (7, 11), (8, 15)],
  [(0, 7), (0, 8), (0, 12), (1, 8), (1, 9), (1, 10), (2, 9), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 14), (7, 10), (7, 11), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 15), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 13)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 15), (4, 11), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 15), (4, 11), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 15), (4, 11), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 15), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 14), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 15)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 13), (4, 11), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 12), (8, 14)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 10), (7, 13), (8, 15)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 13), (8, 15)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 10), (7, 12), (8, 13)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 12), (3, 14), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 12), (5, 14), (6, 13), (6, 14), (6, 15), (7, 10), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 10), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 10), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 10), (7, 12), (8, 15)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 13), (5, 11), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 14), (4, 10), (4, 13), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 10), (7, 12), (8, 15)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 13), (5, 11), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 10), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 10), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 13), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 10), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 13), (3, 15), (4, 10), (4, 11), (4, 13), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 13), (3, 14), (4, 10), (4, 11), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 14), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 12), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 12), (5, 14), (6, 11), (6, 13), (6, 15), (7, 10), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 15), (5, 11), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 10), (7, 13), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 9), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 13), (4, 15), (5, 12), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 9), (2, 14), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 11), (4, 14), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 14), (8, 13)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 14), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 12), (4, 14), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 13), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 11), (7, 15), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 10), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 15), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 14), (4, 15), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 10), (3, 13), (4, 9), (4, 12), (4, 15), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 10), (3, 15), (4, 9), (4, 12), (4, 13), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 12), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 12), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 13), (3, 9), (3, 11), (3, 15), (4, 9), (4, 12), (4, 14), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 13), (7, 15), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 13), (7, 13), (7, 15), (8, 14)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 14), (7, 12), (7, 13), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 15), (2, 8), (2, 12), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 12), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 10), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 10), (5, 13), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 13), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 13), (6, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 15), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 14), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (6, 15), (7, 12), (7, 13), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 13), (5, 15), (6, 11), (6, 14), (6, 15), (7, 12), (7, 13), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 13), (2, 14), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 13), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 14), (7, 12), (7, 13), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 13), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 14), (8, 12)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 12), (1, 13), (2, 8), (2, 13), (2, 14), (3, 9), (3, 10), (3, 11), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 13), (7, 11), (7, 12), (8, 15)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 12), (1, 13), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 10), (5, 11), (5, 12), (6, 10), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 13)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 12), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 10), (3, 12), (4, 9), (4, 12), (4, 13), (5, 11), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 10), (3, 15), (4, 9), (4, 12), (4, 13), (5, 11), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 14), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 14), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 12), (4, 15), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 13), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 14), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 12), (4, 13), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 14), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 11), (5, 12), (5, 15), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 14), (3, 9), (3, 10), (3, 13), (4, 9), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 14), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 14), (4, 9), (4, 13), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 14), (6, 12), (6, 13), (6, 15), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 12), (6, 13), (6, 15), (7, 12), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 13)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 13), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 10), (5, 11), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 14), (6, 15), (7, 12), (7, 13), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (6, 15), (7, 12), (7, 13), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 12), (4, 14), (5, 10), (5, 13), (5, 15), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 12), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 15), (6, 11), (6, 12), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 14), (6, 11), (6, 14), (6, 15), (7, 13), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 15), (6, 11), (6, 14), (6, 15), (7, 13), (7, 15), (8, 14)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 13), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 14), (6, 15), (7, 12), (7, 13), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 15), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 14), (7, 13), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 14), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 15), (6, 11), (6, 12), (6, 15), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 15), (6, 11), (6, 12), (6, 13), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 14), (6, 11), (6, 12), (6, 15), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 14), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (6, 15), (7, 12), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 14), (7, 12), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 12), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 13), (7, 12), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 11), (6, 12), (6, 13), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 11), (5, 13), (6, 11), (6, 12), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 15), (6, 11), (6, 12), (6, 13), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 11), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 11), (5, 15), (6, 11), (6, 12), (6, 13), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 10), (0, 14), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 14), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 10), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 11), (7, 12), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 13), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 15), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 14), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 13), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 11), (6, 13), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 10), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 15)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 15), (6, 11), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12)],
  [(0, 7), (0, 12), (0, 14), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 13), (7, 15), (8, 12)],
  [(0, 7), (0, 12), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (6, 13), (7, 13), (7, 14), (8, 12)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 10), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 14), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 15), (3, 9), (3, 10), (3, 14), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 15), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 14), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 14), (6, 11), (6, 13), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 15), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 12), (5, 10), (5, 12), (5, 13), (6, 11), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 10), (5, 11), (5, 12), (6, 10), (6, 14), (6, 15), (7, 14), (7, 15), (8, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 10), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 10), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 10), (5, 12), (5, 13), (6, 10), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 10), (5, 12), (5, 13), (6, 10), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 14), (6, 10), (6, 13), (6, 15), (7, 13), (7, 14), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 10), (6, 12), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 10), (6, 12), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 12), (0, 13), (1, 8), (1, 9), (1, 10), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 11), (5, 12), (6, 10), (6, 13), (6, 15), (7, 14), (7, 15), (8, 11)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 13), (3, 15), (4, 11), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 14), (3, 15), (4, 11), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 13), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 15), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 13), (5, 11), (5, 12), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 13), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 12), (4, 11), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 15), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 11), (7, 12), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 13), (4, 15), (5, 11), (5, 12), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 14), (6, 13), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 13), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 14), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 14), (4, 10), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 15), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 14), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (6, 14), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 15), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 14), (5, 11), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 12), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 12), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 15), (4, 10), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 11), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 12), (4, 10), (4, 12), (4, 13), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 11), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 11), (2, 13), (3, 9), (3, 10), (3, 15), (4, 10), (4, 11), (4, 12), (5, 12), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 11), (2, 13), (3, 9), (3, 10), (3, 15), (4, 10), (4, 11), (4, 12), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 10), (4, 12), (4, 15), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 10), (4, 13), (4, 15), (5, 11), (5, 12), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 12), (2, 14), (3, 9), (3, 10), (3, 11), (4, 10), (4, 13), (4, 15), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 12), (4, 14), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 10), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 12), (1, 13), (2, 8), (2, 12), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 12), (1, 13), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 13), (1, 14), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 10), (4, 11), (4, 12), (5, 11), (5, 12), (5, 13), (6, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 11), (2, 14), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 12), (5, 10), (5, 13), (5, 15), (6, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 11), (2, 14), (3, 9), (3, 13), (3, 15), (4, 10), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 9)],
  [(0, 7), (0, 9), (0, 10), (1, 8), (1, 11), (1, 12), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 10), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 9)],
  [(0, 7), (0, 11), (0, 13), (1, 8), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 9)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 12), (6, 13), (6, 15), (7, 14), (7, 15), (8, 9)],
  [(0, 7), (0, 11), (0, 12), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 13), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 11), (0, 13), (1, 8), (1, 10), (1, 11), (2, 8), (2, 13), (2, 15), (3, 9), (3, 10), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 9)],
  [(0, 7), (0, 11), (0, 13), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 12), (6, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 9)],
  [(0, 7), (0, 12), (0, 14), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 11), (6, 14), (6, 15), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 11), (0, 15), (1, 8), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 10), (6, 14), (6, 15), (7, 13), (7, 14), (8, 9)],
  [(0, 7), (0, 11), (0, 14), (1, 8), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13), (7, 13), (7, 15), (8, 9)],
  [(0, 7), (0, 8), (0, 11), (1, 7), (1, 14), (1, 15), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (6, 14), (7, 10), (8, 13), (9, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 13), (1, 14), (2, 8), (2, 10), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 10), (4, 14), (5, 9), (5, 12), (5, 15), (6, 11), (6, 14), (6, 15), (7, 10), (8, 12), (9, 13)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 11), (1, 13), (2, 8), (2, 10), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 13), (5, 9), (5, 13), (5, 14), (6, 10), (6, 14), (6, 15), (7, 10), (8, 12), (9, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 14), (1, 15), (2, 8), (2, 10), (2, 11), (3, 8), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 9), (5, 13), (5, 14), (6, 10), (6, 14), (6, 15), (7, 10), (8, 13), (9, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 14), (1, 15), (2, 8), (2, 10), (2, 11), (3, 8), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 9), (5, 13), (5, 14), (6, 10), (6, 14), (6, 15), (7, 10), (8, 12), (9, 15)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 13), (1, 15), (2, 8), (2, 10), (2, 11), (3, 8), (3, 13), (3, 14), (4, 9), (4, 11), (4, 12), (5, 9), (5, 12), (5, 14), (6, 10), (6, 14), (6, 15), (7, 10), (8, 15), (9, 13)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 13), (1, 15), (2, 8), (2, 10), (2, 12), (3, 8), (3, 13), (3, 14), (4, 9), (4, 11), (4, 14), (5, 9), (5, 12), (5, 15), (6, 10), (6, 14), (6, 15), (7, 10), (8, 11), (9, 13)],
  [(0, 7), (0, 11), (0, 12), (1, 7), (1, 14), (1, 15), (2, 8), (2, 10), (2, 12), (3, 8), (3, 13), (3, 14), (4, 9), (4, 11), (4, 14), (5, 9), (5, 12), (5, 15), (6, 10), (6, 13), (6, 15), (7, 10), (8, 11), (9, 13)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 9), (2, 10), (3, 11), (3, 12), (3, 13), (4, 11), (4, 13), (4, 14), (5, 12), (5, 13), (5, 15), (6, 10), (6, 12), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 9), (2, 10), (3, 11), (3, 12), (3, 13), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 12), (7, 12), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 12), (1, 7), (1, 9), (1, 11), (2, 8), (2, 9), (2, 10), (3, 11), (3, 12), (3, 13), (4, 12), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 10), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 12), (1, 7), (1, 9), (1, 11), (2, 8), (2, 9), (2, 10), (3, 11), (3, 12), (3, 13), (4, 12), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 10), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 14), (1, 7), (1, 9), (1, 11), (2, 8), (2, 9), (2, 10), (3, 11), (3, 12), (3, 13), (4, 12), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 10), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 14), (6, 13), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 13), (6, 15), (7, 14), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 13), (6, 15), (7, 14), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 13), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 11), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 11), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 11), (6, 12), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 15), (6, 11), (6, 12), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 11), (4, 13), (4, 15), (5, 12), (5, 13), (5, 14), (6, 11), (6, 12), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 11), (6, 12), (7, 12), (7, 13), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 12), (7, 13), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 13), (3, 9), (3, 11), (3, 12), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 13), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 11), (7, 12), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 13), (3, 9), (3, 14), (3, 15), (4, 11), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 11), (7, 12), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 13), (5, 14), (6, 13), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 13), (4, 15), (5, 12), (5, 13), (5, 14), (6, 12), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 12), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 11), (6, 15), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 12), (4, 13), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 13), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 10), (4, 13), (4, 15), (5, 11), (5, 13), (5, 14), (6, 11), (6, 12), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 10), (4, 11), (4, 12), (5, 13), (5, 14), (5, 15), (6, 13), (6, 15), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 15), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 10), (4, 11), (4, 13), (5, 12), (5, 13), (5, 14), (6, 12), (6, 15), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 10), (4, 11), (4, 13), (5, 13), (5, 14), (5, 15), (6, 14), (6, 15), (7, 11), (7, 14), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 15), (6, 14), (6, 15), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 10), (4, 12), (4, 13), (5, 11), (5, 12), (5, 15), (6, 14), (6, 15), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 15), (5, 11), (5, 12), (5, 13), (6, 13), (6, 14), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 10), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 13), (5, 15), (6, 12), (6, 13), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 12), (6, 15), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 15), (5, 11), (5, 13), (5, 14), (6, 12), (6, 13), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 13), (6, 12), (6, 15), (7, 11), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 15), (7, 11), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 10), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 11), (6, 13), (7, 11), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 11), (6, 13), (7, 11), (7, 15), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 9), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 11), (7, 13), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 12), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 14), (4, 11), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 10), (6, 12), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 10), (6, 12), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 10), (6, 12), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 10), (6, 12), (7, 13), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 11), (3, 9), (3, 13), (3, 14), (4, 11), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 12), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 12), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 13), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 11), (7, 12), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 12), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 13), (7, 14), (8, 11), (8, 15)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 12), (3, 9), (3, 14), (3, 15), (4, 11), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 12), (7, 15), (8, 11), (8, 14)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 12), (3, 13), (4, 11), (4, 12), (4, 14), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 14), (7, 15), (8, 11), (8, 12)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 13), (3, 14), (4, 11), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 10), (6, 11), (7, 14), (7, 15), (8, 11), (8, 12)],
  [(0, 6), (0, 9), (0, 12), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 13), (3, 9), (3, 13), (3, 15), (4, 11), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 12), (7, 14), (8, 11), (8, 12)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 10), (6, 11), (7, 12), (7, 15), (8, 11), (8, 12)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 13), (3, 14), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 10), (6, 11), (7, 12), (7, 13), (8, 11), (8, 12)],
  [(0, 6), (0, 9), (0, 13), (1, 7), (1, 9), (1, 10), (2, 8), (2, 10), (2, 15), (3, 9), (3, 14), (3, 15), (4, 11), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 10), (6, 11), (7, 12), (7, 13), (8, 11), (8, 12)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 12), (4, 11), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 13), (4, 11), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 10), (6, 12), (7, 13), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 10), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 10), (6, 12), (7, 13), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 15), (3, 9), (3, 14), (3, 15), (4, 10), (4, 11), (4, 12), (5, 12), (5, 14), (5, 15), (6, 10), (6, 13), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 12), (4, 13), (5, 11), (5, 13), (5, 14), (6, 10), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 12), (4, 15), (5, 11), (5, 13), (5, 14), (6, 10), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 10), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 10), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 12), (5, 15), (6, 10), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 12), (4, 13), (5, 11), (5, 12), (5, 15), (6, 10), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 12), (5, 13), (6, 10), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 13), (3, 14), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 15), (6, 10), (6, 13), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 10), (6, 13), (7, 12), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 10), (6, 12), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 12), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 10), (6, 12), (7, 12), (7, 13), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 13), (3, 15), (4, 10), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 12), (7, 11), (7, 12), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 11), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 12), (7, 11), (7, 12), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 13), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 10), (6, 12), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 11), (1, 7), (1, 9), (1, 10), (2, 8), (2, 12), (2, 13), (3, 9), (3, 14), (3, 15), (4, 10), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 10), (6, 12), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 11), (4, 14), (5, 12), (5, 13), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 11), (4, 14), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 11), (4, 14), (5, 13), (5, 14), (5, 15), (6, 12), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 13), (5, 14), (5, 15), (6, 12), (6, 14), (7, 14), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 13), (5, 11), (5, 12), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 11), (5, 12), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 14), (4, 9), (4, 13), (4, 14), (5, 11), (5, 12), (5, 15), (6, 12), (6, 13), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 14), (6, 12), (6, 15), (7, 13), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (7, 13), (7, 14), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 12), (5, 13), (5, 15), (6, 11), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 11), (6, 13), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 14), (4, 9), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 11), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 11), (6, 14), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 12), (5, 14), (5, 15), (6, 11), (6, 14), (7, 13), (7, 14), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 11), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 14), (5, 15), (6, 11), (6, 13), (7, 12), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 12), (5, 13), (5, 14), (6, 12), (6, 13), (7, 11), (7, 12), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 15), (4, 9), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 14), (6, 15), (7, 11), (7, 13), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 11), (7, 14), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 13), (5, 14), (5, 15), (6, 14), (6, 15), (7, 11), (7, 12), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 14), (6, 15), (7, 11), (7, 12), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 15), (7, 11), (7, 12), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 13), (7, 11), (7, 12), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 11), (7, 12), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 14), (5, 15), (6, 12), (6, 14), (7, 11), (7, 13), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 15), (5, 11), (5, 14), (5, 15), (6, 14), (6, 15), (7, 11), (7, 13), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 14), (5, 15), (6, 13), (6, 15), (7, 11), (7, 13), (8, 12), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 14), (6, 15), (7, 11), (7, 12), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (7, 11), (7, 12), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 12), (5, 13), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 12), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 12), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 13), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 12), (5, 13), (5, 14), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 12), (5, 13), (5, 14), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 13), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 13), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 13), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 14), (4, 15), (5, 11), (5, 12), (5, 13), (6, 12), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 14), (6, 15), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 12), (2, 8), (2, 12), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 13), (5, 11), (5, 12), (5, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 13), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 12), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 11), (5, 13), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 12), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 13), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 12), (5, 13), (5, 15), (6, 12), (6, 14), (7, 11), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 12), (4, 15), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 13), (6, 13), (6, 14), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 14), (5, 10), (5, 13), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 12), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 12), (6, 13), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 12), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 12), (6, 13), (7, 12), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 12), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 14), (4, 9), (4, 13), (4, 15), (5, 10), (5, 13), (5, 14), (6, 12), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 12), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 12), (5, 15), (6, 14), (6, 15), (7, 13), (7, 14), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 14), (6, 13), (6, 15), (7, 13), (7, 14), (8, 12), (8, 13)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 11), (5, 15), (6, 14), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 15), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 12), (6, 14), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 12), (6, 13), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 11), (5, 14), (6, 12), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 11), (5, 13), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 14), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 11), (4, 13), (5, 10), (5, 11), (5, 12), (6, 14), (6, 15), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 11), (4, 14), (5, 10), (5, 11), (5, 12), (6, 12), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 11), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 15), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 11), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 14), (6, 11), (6, 15), (7, 12), (7, 14), (8, 13), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 13), (5, 15), (6, 11), (6, 15), (7, 12), (7, 14), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 15), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 11), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 13), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 15), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 12), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (7, 12), (7, 13), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 11), (1, 12), (2, 8), (2, 11), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 11), (1, 12), (2, 8), (2, 11), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 13), (8, 14)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 11), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 13), (8, 14), (8, 15)],
  [(0, 6), (0, 9), (0, 10), (1, 7), (1, 11), (1, 12), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 14), (8, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 9), (2, 14), (3, 9), (3, 11), (3, 13), (4, 10), (4, 12), (4, 13), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 14), (1, 7), (1, 11), (1, 15), (2, 8), (2, 9), (2, 10), (3, 9), (3, 10), (3, 12), (4, 12), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 10), (6, 11), (7, 12), (7, 13), (8, 11), (9, 13)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 13), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 15), (7, 12), (7, 13), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 12), (7, 13), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 11), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 15), (5, 11), (5, 12), (5, 14), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (9, 14)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 13), (2, 8), (2, 14), (2, 15), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 12), (5, 11), (5, 13), (5, 14), (6, 13), (6, 15), (7, 12), (7, 15), (8, 12), (9, 14)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 13), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 10), (3, 12), (4, 9), (4, 11), (4, 13), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 13), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 12), (5, 12), (5, 13), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 15), (4, 9), (4, 11), (4, 13), (5, 13), (5, 14), (5, 15), (6, 12), (6, 14), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 15), (4, 9), (4, 11), (4, 13), (5, 13), (5, 14), (5, 15), (6, 14), (6, 15), (7, 12), (7, 14), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 11), (1, 14), (2, 8), (2, 10), (2, 11), (3, 9), (3, 10), (3, 13), (4, 9), (4, 11), (4, 12), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 15), (8, 14), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 11), (1, 12), (2, 8), (2, 10), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 11), (1, 12), (2, 8), (2, 13), (2, 14), (3, 9), (3, 10), (3, 11), (4, 9), (4, 10), (4, 13), (5, 12), (5, 14), (5, 15), (6, 12), (6, 14), (7, 13), (7, 15), (8, 11), (9, 15)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 11), (1, 14), (2, 8), (2, 12), (2, 13), (3, 9), (3, 10), (3, 11), (4, 9), (4, 10), (4, 13), (5, 12), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 15), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 13), (6, 14), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 14), (6, 15), (7, 13), (7, 14), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 13), (6, 15), (7, 13), (7, 14), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 12), (6, 15), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 12), (6, 15), (7, 13), (7, 14), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 13), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 13), (6, 12), (6, 15), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 14), (2, 15), (3, 9), (3, 11), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 12), (6, 15), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 13), (2, 14), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 12), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 10), (1, 7), (1, 10), (1, 11), (2, 8), (2, 12), (2, 13), (3, 9), (3, 11), (3, 13), (4, 9), (4, 14), (4, 15), (5, 10), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 8), (0, 13), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 11), (3, 9), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 12), (9, 15)],
  [(0, 6), (0, 8), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 10), (2, 11), (3, 9), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 10), (5, 14), (5, 15), (6, 12), (6, 14), (7, 13), (7, 14), (8, 15), (9, 10)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 10), (1, 14), (2, 8), (2, 9), (2, 10), (3, 8), (3, 12), (3, 13), (4, 9), (4, 11), (4, 12), (5, 12), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11), (9, 13)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 10), (1, 14), (2, 8), (2, 9), (2, 10), (3, 8), (3, 12), (3, 13), (4, 9), (4, 11), (4, 13), (5, 12), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 15), (8, 11), (9, 12)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 10), (1, 14), (2, 8), (2, 9), (2, 10), (3, 8), (3, 13), (3, 15), (4, 9), (4, 11), (4, 15), (5, 12), (5, 14), (5, 15), (6, 13), (6, 14), (7, 12), (7, 13), (8, 11), (9, 12)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 10), (3, 8), (3, 10), (3, 14), (4, 9), (4, 12), (4, 13), (5, 12), (5, 13), (5, 15), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (9, 11)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 10), (3, 8), (3, 10), (3, 14), (4, 9), (4, 12), (4, 13), (5, 12), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 15), (8, 13), (9, 11)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 15), (2, 8), (2, 9), (2, 10), (3, 8), (3, 10), (3, 12), (4, 9), (4, 12), (4, 14), (5, 13), (5, 14), (5, 15), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (9, 11)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 15), (2, 8), (2, 9), (2, 10), (3, 8), (3, 10), (3, 12), (4, 9), (4, 14), (4, 15), (5, 13), (5, 14), (5, 15), (6, 12), (6, 14), (7, 12), (7, 13), (8, 13), (9, 11)],
  [(0, 6), (0, 10), (0, 13), (1, 7), (1, 10), (1, 11), (2, 8), (2, 9), (2, 12), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 13), (5, 11), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 15), (8, 10), (9, 14)],
  [(0, 6), (0, 10), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 14), (4, 9), (4, 10), (4, 11), (5, 13), (5, 14), (5, 15), (6, 12), (6, 15), (7, 14), (7, 15), (8, 10), (9, 12)],
  [(0, 6), (0, 10), (0, 13), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 12), (3, 8), (3, 13), (3, 14), (4, 9), (4, 10), (4, 11), (5, 11), (5, 14), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 13), (1, 7), (1, 12), (1, 15), (2, 8), (2, 9), (2, 12), (3, 8), (3, 14), (3, 15), (4, 9), (4, 10), (4, 11), (5, 11), (5, 14), (5, 15), (6, 11), (6, 12), (7, 13), (7, 14), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 12), (3, 13), (4, 9), (4, 13), (4, 14), (5, 10), (5, 14), (5, 15), (6, 12), (6, 13), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 12), (3, 15), (4, 9), (4, 13), (4, 14), (5, 10), (5, 13), (5, 14), (6, 12), (6, 13), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 12), (6, 14), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 14), (5, 15), (6, 12), (6, 14), (7, 13), (7, 14), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 12), (6, 14), (7, 13), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 15), (6, 12), (6, 14), (7, 13), (7, 14), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 13), (4, 14), (5, 10), (5, 12), (5, 13), (6, 12), (6, 13), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 11), (3, 8), (3, 12), (3, 14), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 15), (6, 14), (6, 15), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 14), (4, 9), (4, 11), (4, 12), (5, 10), (5, 14), (5, 15), (6, 12), (6, 15), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 11), (4, 12), (5, 10), (5, 13), (5, 15), (6, 12), (6, 14), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 11), (5, 14), (6, 13), (6, 14), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 11), (5, 14), (6, 14), (6, 15), (7, 13), (7, 14), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 14), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 11), (4, 12), (5, 10), (5, 11), (5, 12), (6, 13), (6, 15), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 15), (1, 7), (1, 12), (1, 14), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 11), (4, 14), (5, 10), (5, 11), (5, 13), (6, 12), (6, 13), (7, 13), (7, 15), (8, 10), (9, 12)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 13), (5, 14), (6, 11), (6, 14), (7, 13), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 14), (4, 9), (4, 12), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 15), (5, 10), (5, 14), (5, 15), (6, 11), (6, 13), (7, 13), (7, 14), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 14), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 14), (6, 11), (6, 15), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 12), (4, 13), (5, 10), (5, 12), (5, 14), (6, 11), (6, 14), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 11), (3, 8), (3, 12), (3, 15), (4, 9), (4, 13), (4, 14), (5, 10), (5, 11), (5, 14), (6, 11), (6, 13), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 13), (4, 14), (5, 10), (5, 11), (5, 12), (6, 11), (6, 13), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 11), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 15), (4, 9), (4, 10), (4, 12), (5, 10), (5, 14), (5, 15), (6, 12), (6, 14), (7, 13), (7, 14), (8, 10), (9, 15)],
  [(0, 6), (0, 11), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 14), (3, 15), (4, 9), (4, 10), (4, 12), (5, 10), (5, 13), (5, 15), (6, 12), (6, 14), (7, 13), (7, 14), (8, 10), (9, 15)],
  [(0, 6), (0, 11), (0, 13), (1, 7), (1, 11), (1, 12), (2, 8), (2, 9), (2, 11), (3, 8), (3, 13), (3, 14), (4, 9), (4, 10), (4, 12), (5, 10), (5, 14), (5, 15), (6, 12), (6, 15), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 11), (0, 12), (1, 7), (1, 12), (1, 15), (2, 8), (2, 9), (2, 11), (3, 8), (3, 11), (3, 13), (4, 9), (4, 10), (4, 12), (5, 10), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 14), (8, 10), (9, 13)],
  [(0, 6), (0, 11), (0, 12), (1, 7), (1, 12), (1, 13), (2, 8), (2, 9), (2, 12), (3, 8), (3, 11), (3, 14), (4, 9), (4, 10), (4, 11), (5, 10), (5, 14), (5, 15), (6, 13), (6, 15), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 11), (0, 12), (1, 7), (1, 12), (1, 15), (2, 8), (2, 9), (2, 12), (3, 8), (3, 11), (3, 13), (4, 9), (4, 10), (4, 11), (5, 10), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 14), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 10), (1, 11), (2, 8), (2, 10), (2, 12), (3, 8), (3, 11), (3, 12), (4, 9), (4, 12), (4, 13), (5, 9), (5, 13), (5, 14), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (9, 15)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 10), (1, 12), (2, 8), (2, 11), (2, 12), (3, 8), (3, 14), (3, 15), (4, 9), (4, 11), (4, 14), (5, 9), (5, 12), (5, 15), (6, 13), (6, 14), (7, 13), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 11), (1, 7), (1, 10), (1, 15), (2, 8), (2, 11), (2, 12), (3, 8), (3, 14), (3, 15), (4, 9), (4, 11), (4, 12), (5, 9), (5, 12), (5, 13), (6, 13), (6, 15), (7, 13), (7, 14), (8, 10), (9, 14)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 10), (1, 11), (2, 8), (2, 11), (2, 12), (3, 8), (3, 14), (3, 15), (4, 9), (4, 12), (4, 13), (5, 9), (5, 13), (5, 14), (6, 11), (6, 13), (7, 14), (7, 15), (8, 10), (9, 15)],
  [(0, 6), (0, 10), (0, 12), (1, 7), (1, 12), (1, 14), (2, 8), (2, 11), (2, 12), (3, 8), (3, 11), (3, 13), (4, 9), (4, 10), (4, 11), (5, 9), (5, 14), (5, 15), (6, 14), (6, 15), (7, 13), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 14), (1, 7), (1, 12), (1, 13), (2, 8), (2, 11), (2, 12), (3, 8), (3, 14), (3, 15), (4, 9), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 13), (6, 15), (7, 14), (7, 15), (8, 10), (9, 13)],
  [(0, 6), (0, 10), (0, 15), (1, 7), (1, 12), (1, 14), (2, 8), (2, 11), (2, 13), (3, 8), (3, 14), (3, 15), (4, 9), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 12), (6, 13), (7, 13), (7, 15), (8, 10), (9, 14)],
  [(0, 6), (0, 10), (0, 15), (1, 7), (1, 12), (1, 14), (2, 8), (2, 11), (2, 13), (3, 8), (3, 14), (3, 15), (4, 9), (4, 10), (4, 11), (5, 9), (5, 11), (5, 14), (6, 12), (6, 13), (7, 13), (7, 15), (8, 10), (9, 12)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 13), (2, 7), (2, 10), (2, 11), (3, 8), (3, 12), (3, 13), (4, 9), (4, 11), (4, 14), (5, 13), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 14), (8, 15), (9, 12)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 13), (2, 7), (2, 10), (2, 11), (3, 8), (3, 12), (3, 15), (4, 9), (4, 11), (4, 13), (5, 14), (5, 15), (6, 11), (6, 12), (7, 14), (7, 15), (8, 13), (8, 14), (9, 12)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 12), (3, 8), (3, 11), (3, 15), (4, 9), (4, 12), (4, 13), (5, 12), (5, 13), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (8, 14), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 13), (3, 8), (3, 11), (3, 12), (4, 9), (4, 12), (4, 14), (5, 13), (5, 14), (6, 12), (6, 15), (7, 14), (7, 15), (8, 13), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 15), (3, 8), (3, 11), (3, 12), (4, 9), (4, 12), (4, 14), (5, 13), (5, 14), (6, 13), (6, 15), (7, 12), (7, 13), (8, 14), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 13), (3, 8), (3, 11), (3, 12), (4, 9), (4, 12), (4, 14), (5, 13), (5, 14), (6, 14), (6, 15), (7, 12), (7, 15), (8, 13), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 15), (3, 8), (3, 11), (3, 12), (4, 9), (4, 12), (4, 14), (5, 13), (5, 15), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 14), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 13), (3, 8), (3, 11), (3, 12), (4, 9), (4, 13), (4, 14), (5, 12), (5, 14), (6, 14), (6, 15), (7, 12), (7, 15), (8, 13), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 15), (3, 8), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 12), (5, 14), (6, 14), (6, 15), (7, 12), (7, 13), (8, 13), (8, 14), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 10), (2, 15), (3, 8), (3, 11), (3, 12), (4, 9), (4, 13), (4, 15), (5, 14), (5, 15), (6, 12), (6, 14), (7, 12), (7, 13), (8, 13), (8, 14), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 12), (2, 7), (2, 10), (2, 11), (3, 8), (3, 12), (3, 14), (4, 9), (4, 14), (4, 15), (5, 14), (5, 15), (6, 11), (6, 13), (7, 12), (7, 13), (8, 13), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 13), (2, 7), (2, 10), (2, 12), (3, 8), (3, 12), (3, 14), (4, 9), (4, 14), (4, 15), (5, 14), (5, 15), (6, 11), (6, 12), (7, 11), (7, 13), (8, 13), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 13), (2, 7), (2, 11), (2, 12), (3, 8), (3, 11), (3, 14), (4, 9), (4, 10), (4, 11), (5, 12), (5, 13), (6, 12), (6, 15), (7, 14), (7, 15), (8, 13), (8, 15), (9, 14)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 12), (2, 7), (2, 11), (2, 13), (3, 8), (3, 12), (3, 14), (4, 9), (4, 10), (4, 11), (5, 11), (5, 12), (6, 14), (6, 15), (7, 14), (7, 15), (8, 13), (8, 15), (9, 13)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 11), (2, 12), (3, 8), (3, 12), (3, 13), (4, 9), (4, 10), (4, 12), (5, 13), (5, 14), (6, 13), (6, 15), (7, 14), (7, 15), (8, 14), (8, 15), (9, 11)],
  [(0, 5), (0, 9), (0, 10), (1, 6), (1, 10), (1, 11), (2, 7), (2, 11), (2, 12), (3, 8), (3, 12), (3, 13), (4, 9), (4, 10), (4, 12), (5, 13), (5, 14), (6, 14), (6, 15), (7, 13), (7, 15), (8, 14), (8, 15), (9, 11)]
]
theorem c16_len : c16.length = 607 := by decide +kernel
theorem c16_B : repsB 16 24 c16 = true := by decide +kernel
/-- packed adjacency bitsets of `c16`, 256 bits per graph -/
def adC16 : Nat := 307531429888407708663065229361065880453779571988801658067405740766385851617253679580551089578195623872049397974586955345242495815686734079253332384832070950199332462334442143997264246002031636262462951307005637386259641475090777976032694266080465133089947912593789433239479527543627313194338396326687889854181354427143587783053242593014153298072077789221071475579340994258369832241350114571943065223523296947765757303335005616283298872287516567849768462233889446196920781435633447783810521342119901240664132345688449064491681607506643106462101404040818253923591214133689579709654546186007594076119788271842867253778721360608182050698479160195979133784639839664576069636950143060970975144236734680669778400802267775504597495712618310385632479621917267185097743968690726149783956854866172787347246351514257718368829467728518348072655833528059739686754626898354580086517182414965395791981652395497779554618040269799637338819888759742321872560307991434189981316601134593299771946777944775921217292222513406406890776634338011215331647916995519164699179922336712619606831568550337548255971130561214519284256480335409724761381314294216389418191040448038154017656583230714962093718272725854196009819777710620765907239393679814213671712374751867416185301102547171995911372219449003337363487149136407467043821837413817662909481832456539867736827027507497357361334628353971430499743885094250561115318566624879885601221820433272234198803027953717906047612624427694415098644386225925600854858611717563438898645688448598665323475764247684988743440783776660099853842339036080948243378597610816099482257066867174678928302619689553574433063855696651268253432806001682044020106366545949985853337964639540699636595401769471958591450483670558780020751126179352402790840551236195204593169887218947509994143126248391518575490863499503875477929881591782317072895918194896010231558175362321670883663047770199045706756077753566058410231372041442443926646901246174566154032110783015789056507691126170510797417825511795117769339178672080286749550416797188888341208371296475626634851743959266789540072020455259038873667615866385492127990354680144904753736823234954210063308912761826639705679994660373881447973521092512813699389602077492211493509517271336131591936752807154695494676742636449505957884449476446961369227920815732224350699344920572353244980541651300162245204855153705195280472646787186769438176389276681539937053460320508539435216748627377468099778756763465607319001947994960728593977475508794874885155503110793009114108888093944146714989363140527815189719165348131409599206513341125051121492060977196827661141266413847331413475885675018124175518145941561458596352593534866129943495106845323499187139419816776627285798639147932365551209589144470442174697648459471891177464289595191286561716478916051871523904818660058615805427142107082144877975583256722532561508525761345871762311200837175214974209106865211129001153699911131465902156599136814208914776683552065629297606112139167243990313628904971818187229273327371613603442989587652855892274510625934182083635296483038737532652136690036183660865193278117649935298657710756010969512227517158642706779312757396028982831859300550057555735977412786907783571468168706550522401019158145150631754783293947288380976511541950952223375092371997735958773592547286443648382158036517867610702485830621173172398764081247307669407007621367203823138318709109821136174484005704629714048037188171435537970636041596733653500558595881823216938748336725077346084333506989896102801362407856739287309166564411907521200462059740842047241985873031080882293544344338560382870026866503506591221692575590947573549086891739590916927962167003874125510746250325943298062027200554738008615541077624962428256233935632024656667678923012766176867021258244338249407587253782115532105407724583421389669330595136772582005482004501383030394444634646430821390910376118237863011950059655985090293610700785501570254193150092400145866993558024955742123530879219759310005290069832392684909189617249533731489314378092986771323686796613444343925695307677451935506825133552790981657036848360694911898235965512204386449273539283467308639002688981529076736270945288011915333391436194385458860284019272555431772981010447123700925040028479486104486405678073662932336242462463217321713370867331910358707821163757260138471480938111061729801328046548822900365419642022358656138558175712986926078421822522738794739321530892015987971936830195254361768430060222967503988768705211171245464330661877344111164919838173495981385152205498381547773784262253681039380108686764541297723677587366930613146809523387704505252707284356580471181336024598611619863039102500196507130405986192365339182040454433311523713799100881208815767716300138309181896809061622429022214845361166706295555719009554070207933953838687285289284270625229941575989422311871406959493108761337088787538786686697168378782858804724634731034364631369058666408006847613480821945557776136905036655335157268433786101681735422722850645874386465190937950854939633979482556490412990949456436067329042591249044783420280374543515109510063120985074218972707858268046283342954133968575449555327727093975001515907023736889479227850637973278112924009317047818084404403861875987196792873174470300670002427712561851883974594524777627312220143005042220046269070643477699543798744746131043623279358744936872583770381732176535541958189692748599794376297324080285895901039650629856226063772600025873670692372508784406165342796687040657160243183129828123930573302277084204907046401567489775370246933216126146772939046943821439631843668914040791623130612752854934596054579342449229014989327860424614023914392217796646190863537884146996100525159105329319261367875516061945295480280810933817070857977091699946170842505715478969067025192397006168944847702829985628840207128280766776373051590670789111847753075060522503453857418600087120808306932990632148148234378671234110413313768044396114779377417296976788375775794013286349326340764596944078339668807791582140615728822394897831803696544896705828865653061869721930285819154187655743193591254403432049818079751758331538854719430773333003031017024417233849022396856429424124273463342364430224684092176917697148718058636787300184078453753217172284143824169989442754669024811013428882018166156537987951211909306063795298770378017933097423324893601868448776155453932344465706121275267871845678850680959743233068325671243888363265567092484408315973040473903331803515209790634830284480425817727976722914507384466156035586953905306626568846745673744379165944436348706971992900346035768410235236494015449715408139890235488203296530688438844426892228693802950705585431993124913633096316984496357133065010840999821856309626366507239648301090815484641375522562804374424670862205337544649674242203576792831170031451404146033037868571453350847260593723017505706324270020208724590126969529115767696046636788565282717350981774370357350076363826568620553155723896898182695744590672011079952186879433612474986210892876591749649406433534463947103810190720009028088671452039575820617239900954536983779861967501303246799080786285687661858925884588060746405101037000702074846742083145656582791871724618092828713178735658019747422248622867951260512317458885570068736709563671227465434490236651027760205375965077589677667038570019488769086921525132111268868227855373081094352834670281940047697191972398289878471187125417652107201390236218279980472677519255552752062802904041494230621849995353445862250805073062555714317458074095945550831202169676781128857277711152558603816314982933304893975480729567780561163492146778245417684443995393495700063391414031644583134983462319831768917005848035002588292066217484753649940490201174967676189756366812237169916247305430908604511653995414302592530569731775319249040443987556261587562390444367865547982490815512965012849930418372691978316831644368453602804442599496890540121106336445176947578996288174195368592836560755619436572676929124563081767934101149161396600634416783191379264601938828478590340065615401678272500986306408167200507070153236592566368611113860300716737473349794185903983101101969860456263403436106325885806031123213576755954264121265225723206737647771137843393225201717066137718218398336820911548778318195444583806191828477622897866431864830296924955911629588227375821611723573906775112240637379606318648115889586343853438531804995868776734779696650798984624881446668887652997551600473016885562639885189135214756061397905852516136036632817079547497625616584654551478595733614783950151569850300894621703425036222131269637881039016964614645452707489210736773858331384320374365379008041212139509296225654378760946797498813886318378739425849767453546664381716555610097067707418554319286496002056789074568852469743866422278412591170408555464343433678388691371569382976071917462760936155185087204829024993014098302839128148997473324604218206449194295012026310903139289601293277616492592486088150790504499987615292450323759413998973880611727837463907946499603946576578691224740487684922950128981926027627712456661158138389420583360204231236271207966291068260324674705288729748927757320845163968086158474472188351663102587158960601432521713113755724166301809646462696013363527809422949647977682883684857413137076971564037050818592880821371370618643387414698463514773916988460362152172063659726920651320162373064181220659509560122604865782186003584761941970673239225436239354312329028814579423292852962436835759956605821257756272484503187823629948137733535914514469068844178047870763269334031723124945985411987068835966387358660713568708319821404993775965497591450033181517342635040365149650712974642737308895801496606302412675886456853202067096953730974052377566038989944810506307439627885010717342641927897653681952351693454732328825195074494940051283200097955620970824799669253863388443064100835659501146489179578172575287867065301145441605466863850890757443185349128103395140041666405154695499691944665793269282653226092507297551390926204817775810469155635587723992959959856735085338670916861082635977515399052697599124390860556451711694100092356628145299390872175816406867184256379896679685656599351393780671589614096438489265948016403358548339599383656553532522619485029580098771091246835932864796424538980902182819748143164687448838017711054909445706567719094306043499453935148269923343991408101626982847182710535622041544212811982908879830218841929469837860239510435755085961893449812790181260105492836451417451312885256049148552149846016468755284973951651545198596769984506768338373982719892862708491687101528773832674481226746420984103948794052635707457056356195134402792399783988751756640078794027697439890645650704564547072758778363090359754880850097035468769531565243784442095417876179470179494137061166472621161842978567639095479444907172156110730605365558127859369505609935600307711326037261145849262583620414991351861890788567127900234379276640557336830794923902989883933077023683741112905706310169377350663843063828133638901034884698417537723712943513172464512996666751303483150964293368150660742088384916139906105582010844264637790042159036089820696246813896988348993619478467165729026214315421773213077186001882353341810092738896762881331689456493365750934403995425174598280125485677656710590464919572336586587799404600629730302502861493106601380068977992150487961977225872128925564465821517459959488629989376354681582733128325806021865176691031516204086395622628198235456779737115560630029391787159625968364911900158531698785150812462317835804214828156499673410967340064459571153538120029566164278170889384605321339695938959963419679433788830353009663883374039010873017387499701846585959525952033067156235703486363142139821630035142355924492030563604603227372947230527691417821625658871781847069072040436658292243007761497839980327629278661218045033267294851041051244893139996448478013101824026350239502307637751535581895551069815178938987901069799472814899676201198296634778627476292876268338226177824612528440320698422223155533949430848698432500505659134747472997602377361139980784425782532485808072182483604236549115187561064386474695236837099783004161365824364720325005100603554194052421044638393593889997728935076185996482165293870788196526307881176534177483551238458512175991012462865157179281228718117794990400256902371884644217217226649655575804959711632947900201511249940734007523691756321327870559968754045856599564678460987010141327219995934562831995243972726930692539544674492607117599803356660574427687377944728075075588691372607113961240602770726192570469501118533381850687800297729456071103037329893777006273424486432275943232413951830369081325649637105865941831758219001030241727804649627602797220638641006088343400950984481203885043600699835824195703671940167959611166413359544405661648208881615267941425337020558074810625311705295310566083334706978051744250414053214454953554175639316763298770252126515433549504972309013145755212012375016750200043468782448346833272246258847899283230472525812783583178331853195381522255591925509188924526003186853788536177058889530333650249450431084103116681736616535121621835654739295859183945344903295741761366593170637526415959788061700047208072826192211150320293358053449731391576665042239128654755429112368760538987356131846329170792941236580391240595366781149268345100960951773597717555292389438045402180681572608351948970793612202189797602521826885098795135970940726426723940192033383268078643530966327083655474771007030433655317978350345040254199957703019598030596807572294650601494814505397776845921389897628280750970943385543220138031318563880715536674968104292316250030449718280525985742664495337275946449590477119262547258314806815329876375624884821643463115823655688033133964928209513343671599090623852252908549942777334164766150330341899518447713639451785539329967082860850271596929710356058653210403544126601723165038007734578828493520275400502234193607587996600906770048219984616751850153487926677809086120316386526471257011662844333149884869866288997830959449664216601187624600811027968178324816027054402748494619477886833512135724496231747773489053610663919505277467779457889107854513848179820250713438539415643237973702541885073730306879234501081889576456868703901283088678967087362702311096093799626039269093667341640285497131350873032676113173696315432403873376679242455010407402261643205813702412755344268037016982697484911876984462169701013935339991155931010534502744809489631879455105570918428419264064266518306718226394955348829818809411966934639560192823815323695876440820716593178475851107998134658098333637759787446281662400505762304216518264914939135420050224859661321954294775467985094840956112761614540762207240830096649769106141248159042553536715307969066666966603871117869110897923028240779396621117973205512229823369208818038544199647111239435836444268009784942337358333887576522566164284667556748965032068764043031026821578743958494144240079179192573145504074411550345712601975061833144024868419538987352905091401486673707914156863823173470119507909749562561900043861078851674555302520403181324901830711135318362672274787068398221874761001872558293567223258184055360693876200836555974656168993406298324371508528227278407023514875920193944228148077039113808105737981619424701146884424046459202508795301751412494357697299308068302049193117832329627519345521603119077405916209825362965457397603772215411215148269556961962233259859669213658900970078537435207352156680860942958295376922696034719733515490920170900899519541775259608556128244095930716953831152577767351961918103767907684012853631381641163872789359942901986992245466125535218348713268995333413028243977580394895505330140179292741894734248270514493238023433931764515486246329922662531571199574402774012509340552760422347879400353074819668485930373429250478613500969555656651854375633725882833044797619821502516850592354386955548457720145516546852421036643170869317567332275499740949247342973674449048389794380363124759261927316907344113609606049125334456954644872975829415947835422201014670203789419579472137440644704452782570953686655312231305539473919577885278598471747204707008339156039254404559805869891817473490465090619499856846667744803979582453287204881885694224850894317372751692479456105901441862033696915096024779093349670211661318076913218042733081448513822304760399321202039730842761067439016874310830445669823241622057802938777299810306641549157197652811118516580713116734366649436693290595319839320615341247787619823670698109903394293471882149178398981824640262263494469231708908268631008112833638596313905563326064500211805114338659160769650508606976292363499969942835767601854155694831295035167760341181432309980317349781618061336844669031576500170806992838656055308194180146383591342264064294207499443825601221066585926782488158581627446181387929470623848145763287916941460706126010807057134002689097065223449376488712642695565311283108216395204859463780788510142930320640349460898873390049634375823454230861046095654858147386992596602419561478978686267121810414347211845037068164456675434673296290945671257497722759702044808269177116201137466828786118916684382189979420418170021096339692627097012543012945906126097890888189628462808156628152874593057418841474961061951396788711593658877204865187601441240157012394962359856335481173003761290109469555170061745640037294255940291750202331232855663819624847519486728036108901862357638203668550166954003671175990557306541378422966960061023763379276526067327207491381476567151202238631736812901180101730191586855407329849745875286698827650918875534155931528125996632366054454865496155951736296236294594359308892770133107969261924941999940798307452048141604875047782440337989966238429715413377276096215691305817189625183944663450925214826606131997850866432375364804270286817425684588452771107826212848933063136132123530261142057716960889665116411580671822193915975455077202357060583531183052591610598267205743472263188511946381179737125005550462746120607562479503144888282544203890167906301405095421521836947407052872877278685812832581660109460912954398573608855673332452344899859498063884376467091513679573150567678591025048667175500842988424743018955276944577239036136314375715541591794055985758002051049645552166050712644737530320738386039665068093620039023093762865557830594013960004689267663381911417381747815934629520913467494503140796387846825048959963370864000627940586121214429790317573775483632187497153083527922114316188672506751660948400755924466412073645608405633695746404238890690854142091784330804506239777876086522393945392739805933723855805308831672230150283704465277595438110598249705269453313851865445261238549415026395489521505583667148197215383493738569728611232159743577585074318773682495258863664744584290903366723127674053593350813978013581845990936233701636203177398454513733235383681358324907006271104488582818214981837091483948852715674397486698993191623691437326810367534539174744730676576899688483818332937015284256914216590954132859606152549643539502640528947204098250035558675377166613289368327473694742950027228622910861935682775168858281463601993739312043653586260774562928228006664872105306675975211706873461441596826029962633694012019004717677409095210338905207060548960675473075405687351475703689585844830927336652308780486247155320913579082233567886685167805679951888752702373965772670484670983716472834439760476327762580351849428354167954203764378312201440817854040816344248861206989345216911796224963542634534791140400451259386533485849647314770568959513421757438025537527054524240760688255136858888043100765198056962062491710958250283409343647088333435731587913075232265676646144044947173178750952922265967096523391295751501068925196316848282803064214633543766633039756740928347597948752771313821601896912949028419658451478276176393996444825122127451640946164388577586376536876270976115130593651190783695270352489841513382935628418741184511528088789672892067850363030288260957351940796012598791770391744401074759590214515289401539373200749597674974014161129593546733195804208177632246216730780530152794815714698366710753955190298002535988598912079907078366975114591305520575908270133879815477796948968817660729247726931849355444543663204242138489693601478564514886249518345051080023775537274266078832062753160079848289666556174654358023517907991619404449038654121941721243075250183573549734702477446710571612346691835271382882777811546678255577615300701615567798080931100162568646829692496452706673060811479173480258178157271071741141723619508412685285013016053794758604627560620549303412548396724512305343066467403385062605367001745682667998229563197180773879758448255925589055718527126274162479048935127189673384970865359714860520613054804941202490632403113402793903945353885561784378324765878838561607720106185869000326075510993335613039161880256465715989343352859555418463736181186130078293689972783117180119145945680093791841848632993555348503111498256525412957019841022647326499911173138995916278606351707779765426538429606625978917477805636148658699762928291716255694711250379357134639805337678835914098551621410681434555734342155277928316805681889194193477665360235798094805606388403597925229577423619639254318266118931718410653078806815010675163628156429933642621044527701921249088189442066705984869841135726576507160527628418344340414663258205941419518867054132937460985782183842657320655411978919335189075180651088745880650015134306090817364347743014283229396257619533004391148750307396165705326404519824768926559889182579988367118550153430006296484785459840862357731208038165514029388080558543431545041543676706791169534260615288675485129210605693267535132807422669396996077127590086358701141839757147425136618923761819742724033661408743580146814581381730783239783798763724766621983228143040680226876983649467042482087005198960096616557313834896219203116178642582426040160877301067343730443071065344943245975387248046167193671839234409630556941231030870801184095253869267089579546449867286793692670531157134724987740642543506980148068757264679494134297085879172080747181172430354777875791546338322155147020170356566784278350393656467955856942365266766266222786671512761597988515789938398087389821339564883276339755791372722062324305487532792234174977932658021946293459503626555625465237188171989874769922143547962572008969833724735857237246291812999272866764983989690736070312237745872378095839858917295791134600114291132797166858823037136627938812017234875779504131535302303279147601338409462968567305247075054060939904259999877167257817065320294039851778265130200780744989149250956412349527738752303932130921640869928978868985135632979379945769336939811243550728024803524495311563107394727427199882558676912409905830668006703032636151848334880062662034438547946037050978973748586780228908772540488777524712614114833156518090747553810268406631737315509060664513877406870147525975886729183872626012175817616333741462457824661956275851687222203128479243824062792160205781804414479621366328931591581739595049185391494067956078178641765145859682594958064857594511586994548328869798163752563044611768339758303988575097107446704674885656840032735412194029153857515187298702646590498135979742606384005656311571589168049031064701287245628679019517018882884337549720113635094686185571650500429048177978030972190922516487431504577187171745697444056813382063035054201432935012287144178540676574497845534796939979616800368523544760607110162130980904869519225851074358408521371809778673790260406933934265378997781019359799866749818692561779265407831894734465676729707740140205840229904992980636312563104593591352045625026363501971564510841657511425315384379418797982823563777475348721403030725089335534315138200316811440890670450895649495786403935293727929395547635547088980903570170485551783343398496450126423347350223505525864707933658450702533958096475597587118401001338652093019650031718792759840013492123477411164290547602617636312037390017801571192223497824435826423339143311979023164623872784289049063302144854838437373279627545801643040960932158426544949974163552350052747161700719226565900606859010447631897444752345082262348088992438353682093528856455866886065715325028916383961500735821420475297511782829807261978913797685253155669752077257774368939666517973291420264674175193396965330625871070089981568962765140815694773019707821293847018788408389781562181525650701169622550351076147252570874077238421531428463745318160395433602791046214371167912382962657264702973246953251358775380074115825134260211020004234758818392118887894813936159269040650064265202549670488294322677719911268796091507168953227267406693020788231192347945108458118054622533663483136466239384683448869564803906455588073602637439900897188085070730968138808325848112158650825215482095304621594876681503470230008016721565425591042409297877773513873175725919919808180849409274198063730506283471950065617813397542072338175432853382169276584608115936073678306440704355652996437540036425558213133390596696444830793106836289942353538955924566978039265543369693941228120848722476382369246546145064102448962586805769708836088804848726063551967400681092234133784669941199991567866236872203707922047488697727526639170013377497974980345600794534521775284783028189785050054835465131257346712574507841447219445693555108702054619653980501980283537626697362119441562718180743958977187169321970582587930735649769166593148222485235334666494181395904587778517769094070017193354973232344902490558749690049931915832930527294921742653361445495864048834459234430037980380571064145747438169511946202755229468883347434969978778312940699259894989626587563718809638313670646237469067899566965821539076492679724655311969512306781869507662186970402347744057570974063199379097755703174277423509106765994016946786695112103712391232256199904326547487762531745026662412061691048084349140458199211791901827215924868343963296487312684582776393153023570446949048099706975438256549767043331875133724888764872465530204078957158208439225668567780268771005424536298839367040844936190970813979035838388876689214344745857075675766944080452723154086341715704306557775863297627997461950287617971860805023821817665003976184111715179992929197385301423570565750927081620395161317094201030167205331310896273469926280589674282041293760670804249707787898751190915381743276431261889062792654682576962163199109371735146782855309500027135695158161869892077498214058756825512317049111257117893834490900212992953381418841822443901203867882584667694263813112405675919019576578885746504607825621641302109710390425557010901966370449035333568236410069397997747128765026719599947635250313168048086558314978106512486711838115988634216215309060737233377986597786668658533748369109171982080632063781269818800650374076159187156307401667706833042566667601615233866504560316607092941123296723131922053127476357727382773952869504321700486459988007937815402948030680470120197627777667199855911603596655856565013669787864760454126211527294283061277695835189829932919416995341459033054922085574901849603708501390529269689990481760065228951963874486697187851810712088491883915293311741003633969578629670105440177315057803686212312221624152004700320751624239668061800700226398888671967161103056258490585511635999605729347804170364434363563276645664834400885011757744779279750925752802908936086289659917218756355037371965756945293512648905275315571862666643167414303510582312429138944912821745632717530984379398536293119858090653955156191781124804562782395030080288603936733273187883342343132605578023324637698776527983585595210922077959157905721886007746581090754524949526766995043340335880971486256803369416666630820057840397716178586601614157045608493357480412303715659996642905169467863128554587635801083278072535845789862680823803709470121262194165305317250076669982684342189979814429841181969302092338405717273424469494953442680229196890881190161584199949527650457856886402737327755831899381885741871205560072597517535570163325957695809243549349169141021216374949313034864799005097506318564048678127126470495541978703261577692545880223339335125109356606376209499822606352561125039857473608873813000959234357585327718182900408692342728391531905087102200443015716245195319960275899829321003891730873893237632661014888730421115199593208463271466079999989220521436587194755186640520292692434995731242004341831554304020818698267602027757610257949438880071741123516333680110987098660735307295068494502903565613894343657847316805155875268946052991054692916503398793969965728887024630552176399572617181577630015448534429051032078539417801055333311123397836078070822316629589656912043752727316456086318279129142570418995727096730995600490513833372913387741474562707118870822569777867204882106566720174660523312646986494018848566860025379919740122683687731193109738959263272280774807571687648053163421688112133858375105952163987097551280010177706976545527684134151425831140874123613961283137881020825618552790943235530155080981575021498088985933116121284719935317428436870789471948966773890431519547961540730694479233614428364970163569946434455691034551151420055387014780667619771532862094935878709879851672099789337648774404753389918657820843488705018746424822429471725984943169785898020998952403429887146217855619051570968445879477131309506027174631513529398655719049952633705457015683546233887608668038616200173180656858786905269413909733540983500505549185445052078100996127154818511029577823695344792469746401975958550614506698885874506051093814686244106994647761478822081487369194876563941031182009426640328596121698101652807582703135775127654026499895276956928945815634754260035909478946590031339805182157015532779678800174279437238575310367841280610851674322869067778322229980747565968040751181320283496108485708821467428187427549672453929571878348637840737014443584707136218520674305872144230624642596513785893067281353925454362407779801865513501807738422388475045281007564242305454961968811796038103240719488269770805132470481258508794649140419410054546715753716563090028822440290105408786429493500673405175588252018815741344933979269842725036158583071581423076150829095920717954980466706313064158670107995725673729389201407355877710645162668053526321436386515958474672311868478162582123641276941978141982356169430289040277418003657022931594031190811531921507310640434660639942548335612032616946007322961476089609191405522679556385262566840729020447932704966412375224872171387579613049756681809980404512280819962223599260990415610659796085143226038934463229533142698650397553176498013796283637498528127448416385984576080875882598345567970751717363069327034824279221995808631195436834325841758028047958030782827702873005063942892614459972567332066249122736581472821919184894759973092303517349101673249576778014322174292702237570809535703016398697851641612945938204247623360758418276027514255246662009616915856270326633265167855131005218985397474976948437725341850719620125381255187963584837417498324836424562318567264577563492066820914657808226271104934898296385988020147802827781783527402998716877832432944987775580435880037487032607903507673386095346435888312045419479241840332866106120412880312893765765901112466353169654450159158663001349349836996791116136182991536663111107900449107775572850302796165323646348482027491851745416506370874763348718881008799526127371060732169077330294337746244709510604198084872376030542665732812152757203988869435668638303931497545177471846858047792889373062444000640305428375293634732064178760694323808705497910973252230659457540788928705979838066699384402639631994063152853291569228681028889397141101090056987714658366068959563778811067986235412786348910439252983154389965302334375455831164127680309448645156344914150985904717856404582358757507603356358099974803347159489123605213595737578019060933460634298800926687828291200898140327191228897761804694619761207980781647169081030897493967619536018022367230146316125966139550841146308780236253247208286873545831409676039711200975114283875868931676595141755116153995867465242168021984602708508886470154174168277322238431117475183866693649724298936053450761516243929850272484851620496596038731646947800284319629022432126209195757931907024903620032223539919214612804779255678175137799313402259413818824512543613728479188988884211193277449701347155144794031262033397666970330917263791848435047970758398317970294781130211127121563702597932080327007936674281792955809478895068264160656280363357028534086231513015210815127356772268051188856199252377381155795438676566119756635182136448205989294609319037720086347044626932224852774523455800467081009359333795530352361556371411249106634144070029813988938240231519297865421979689665231110659411956970859604847133154545816411368096017845509239931535839247847986907516973157162581522429203012833695167534305872930370257268557616162352919599712599988013011673625978769989265482451533411693582698180313932843945896631396652176738269034239882720962431140938150644891198271806995521471579607019243928903247116382072167974251567020459793386928529391781091648801821976261570039965523880333773881131249458530808661430632351734989313834006241441768906548845579314358935376923150107563642154589023197024319757664494030973654935766996055092240290050728299707641657653441025845258700936847215493375705194979832503039776047012139772413259350120473049063939699275715547924176827456982943169810587993030719238573771939138072751740627513806422610282840363439674439376668437389591312280669758377986830404464961975700406425586093100042718929146667827832102228228625241424795475156862250386711520516728192616833183657780491825025907687133349038763158648584368513879080005706328625315914342907260534859123617420031911027129248901570060871637589833610143492992893319454602300583555198129939282283373418748311640961618986322533728541080217697362844504876564466152376202571258574520405708554950798501676090437962622147197483080302712296175226966182351293553675804027539469714802823147374009579983305111535795573491748863839461767697491164796779280339914004823713975199404127880582283629976397862817137649080974041644511673963477923661472004546107751210547503797896024033108534305309406288868475181678913151798824092137993196943772064728574888625067783946251073304711468524855952466694471728725795778854853719565305288458093941437673228234142857140182391828690647445796929878503579738779318632933448568725340525393504145767992044997762464592594490579343269741248261438501217870763900915999318292495590239618622822714703424159565387251065106369063766607079233947866824777946438689863446524501542131690836565987721219812066270078701368431578716148073569744569520335010734840468627951726777496664980302708621348829675741223310809095775736941988142740725033572926214711332695252251896500255486957713529358012969441469827231422797639934242964292843322294579340990524533728328529433911323360851075160663320679762118959305646706855305213672967514416118333217807036126885301263203357433387356328302067913063081051873532659889634396106719685622615576644425683865589685999608597372850514579604572324276121177222996220057871166926664899823474349065662350256940263092410010901783311258734817431369766557023530163637105813775503630228649341873407753800329228515350004947930018865036858365245182057510532258218772179328927772575935777793794231152302956430639984168921890331061667796813032673920601905648171506478712774977658094182841100589076461245605372915390567434323964610438121229412861916896961853464321926247895288345225886991643523809489020459064834031637143735101697730091287152153955905603130996828939823122095926813061974418273014318295914402799736324660220503769230693273775731405076470664352080126158993835037157267216023376734326222245052151671995311120532200234649415236621358559399914429174638361389760316508956888029727840528813369689006218569204358870913166988089940108515530614915821714174788094476190840872214613057930018343867371205977724938215976384246023938123337623261324331463609874982411587405751714625359621968442345878030586973618874388900421344771226034339917484532655972359299860846599572872373404945669398406580600846363520819887604183563570465579982582022500844205914912887560445927410739064843439891302527924940421349966992532147769354905526518006944086438154977377515106835857224492679302535348442567062372543668415908323765189011494462969677823660358021662992687032280114276507767397077793651218807811771112652870161668775662766763919429985830212669788964791156684736459826531791871841416557431764653671002104709513512115545238533756871233009226977326870072211160334339860672834155571032013358824291534761572909329787719833517079252043267989013505385587467370096145184830329196436103834636154607039781153235165160928841753375389747095793457667185642908835788744606352262482060805992904630553089352885348307956531715837898096165534379622973336958357482439567342969375420045284306446554147559356629549725650642143214744722477049867815559224171682747103184552471029611675080322755980901181226917100876624027976289902191296869665584666769464744964062591299295958839196325524078325612384957591754159070532410904061824798703142143223455336471296897251859517465900580948523627357206586697190004451664791816610587340643755190162350325613456459908611698836166486513521256040632759193421737238181973369923616402933730959759392412415234872801334409854830849774452750954400042766092109688128558447182634627752811882469070665960137104627256569358761040034226705198092885875140129293117262144536442030315801800062627509794178725056903401587620043458027278426134239088719842152495020946220763954897011039369661683393694898982481244292782273820037445713767569139194246830716423447988204516687669106197579242990882006732253295729400056756751834483514213872943633126220582661125582614397965929587399483658107388275339344896847503601111779269862546700382869700855161165720874326073224873797282622243314615744714843689391926695961892443958918972234752234176854997144315352840197481426422518114697908973424899706742973143077699539901669502774445051245873136736514986775069551715914360519120293900942617414219104314953646059631569710923226150829484649322397011195410812549483203179663284056421858692195048735037131790051377924839736133376620754560704198621885567187378777498099242655678509591347289924986676593367316022340059863664281686281539707254408876281174975776168494474028832216391501092347696340871586673309665548908404030334030363807939941451778603694813705726286994638322054029441700370429360884541160688999281357826883201739407261019873077101731175655228909736038307320631041211834990861725203514461705980263921306635513976177841969443741638546363017789778478599597239683226402744937712963567915875419022514265700594457411746426047094209629110055803982616815153793376036323772091960671423377797086913488787731431448982035079066420923545569730709773126696701654632099063757479234393684085058971423980195487362918144147721172587611514089204931248080929882872902423720288593797764164595391768594930768698736403381717820556414112743092631875619220495533827260245946231026135859347261880466057404327854280951089422234265802880892193025518283625464264192972115562882025344551010797807026433949249941760486137901321532845222048050417688718881223985467425035597712377263326108669999881603211178677267955124423161022599279376084190604966609903366959283169752513663637659414738487235475701426880228146403378555139122493587638096639777723083014704899958444355815896915727071095022935241387092565656038117218549256169356237363258027494095250111984663918191516946731015600379963082396027337899162812370796148765227455238649511194676582828054732409675650230427665812614239302228931877153211437346230883177574541373456390974598424363325849311298107768792701259803445138325797134381521776649771481544307813071348803536435356547595461993283581177510972250280837042525307477637571359056911006891823320896128349406003281279951987678908635794563002669589061767923322316795900014150305735193603222516027470454485475382533291038631606183786981649545357333591340973812203612782654710744515801980908354720635755810227200128682120273007328619673864813650156964719737818235558540850880865711550649568552646614228400243305056993908507703313638656056907892247295328227364573283386804782094867877094016426918200735387238991053272001755814576379825292156845836925706815004632208615220538073760739320214535059795150357902651229460239254105401875416088532851024584440744910297991978635469332026751866976985552226982484255470877255941425836817567587140275604336509152980636828995424690774837218977161712543144066007867941684827053392789150738876413435448671647319643862736615878036367207989976105380356519174332254156550301643720032356991680004055237188365541988229403928840926421712362823947700895229970137507679311000006352607325896232473794232342701226113097620024443945292942978475905356599618236270392356431430628266570355665171827791198649721355540134722345363283302819545345903103018831550479976759369375114164714681097779631932477513936436844630584206388365154755729030020720844875158868721600802647538630920674240510259243621280504863773762015723570143493642911229307930018869884788027289524187810649517633523577179481089774312384360272561513425717539761313214901073176094756262749925436103128567801498427627657490704963095290504951755983863249471704956321874649752516233343206423819393451931405366595060584765213621998273875302067902445734120942217786258129208480121319906365315924745377603326763802062075555794254372748188067544693686628800761225438328777414017930590355271551871883356855995490226786631495619584816021061648253650566273672261135782972244138476706289149999780302761875751460575293023025792755415869461134098966879457089194618311725301430916366663483023336028554093514801862682715553741261326621059737499087416839851900582713988898983920628051684829103939947738406891792193992741161234604054765846586795106335737505367324382528566742941989624084541896755338439938628251717278691678832032692316680988503958655043048029799480125671451735901141891221607925158908722969338159456557726229021006927443155670626149382536217898400482727006144817869544349981849517554714519721020317279656665434059111256952457138044501602062999597398985256097012062410143350820447710960472215324463700504424529853832276596728507179571133742847710674176727956877881115458457570433341378087801987503893566493014796402714795391525958602179374248754666837039967187970308971020339349413895248050437829489432585141924633118507166423202545794318119303722773539361320574050734603602557363090272881489673756971694201184166774646968756835655086759926837605690835828647065726086114987623576831615246132985056044333661681485618837807921162918650422165724294001884642014085533785702685737578646414860940443495122168195022500267329071144471411564615443159262994880252842132405981466302880911956355417619884262109100618109352421240675509011894419019251530054955116186602523250203059981041248165732849459157821459560984243703806410827385590839653780112818272159181648248449826585114157274363106918138652868725900626946165091252937133244531566241372957452437070122462118748602104748397902121573278257206375056225269510136460948902359571269093523705679754268346942798648350220524999013052577295449543460817330229389045265413744730985637509110298909632738572134559666220614678706714864640909962462826927869977712898946296718849635347873779845730038554563484760001248366818515860219732108780571500842786393108227402422642141789887988286294802909460117875913496521641463716062699545349921058012586133015332834794651814403445585561694908082695854332600691480168994349779419665677130818004506895060894441761712234922756097774732217918198440344241266875143850051458753300383433545031616576344020715832797894347572378262518663368233958030426327263462758836729029650069889945101634151258693611076835740519834283578846311125916327489708812656506563218472250164456871064483066450859323493902699704134336803305979872554387972761699672825365504244637710924018401152408868542233209799592072490820380981519707394570153902476943886584068671429070137761477263094980546340028548315216538768220815708105202304437018344295097898418629252741520550392619364426597778543590569612741685627472721449221804548132978898832760545822621616041406143061426487350462800474218576300629957326087718588923336750433775354580312289699656288017192568855490414193191944667672174482884203623030468816145377955608197145902488558542358288707884758015602908013518820015330860063054305672968897594767058787791045621338480499920370323222665189787595488869736376098224935489793064458104967738843296232911157521603087243982127525538325082884625636564895578516875534885049483966259303093378371841600640190449202082813137852722132650066897632356440602447768907782320306144457614819546933453265338676010086421818437581787404359237654349294685682094480296294307241300737686169924555575338018105653663065720532429631609578419761961755136425475440923122423799922041412456374994527410178931701463291710976618603296106880007765481150683969654635199767013577257979035885061308003271216170957509990912019825398959926153338341651143812890539893877088857552520959544858795025773244379372342374632070494092664863493308462644512530001565878751959188312916170121376776560304674545089583597310790269862012402786344869999005733246066253315482811843566813895253712055877053172561328478150834010765273729355675054513861382907547221288056898159759474433861376867576717517007590800251662253586071524733573602589728910502303598365152653971995262748891132758420988927652356127390808638873796079351188156502727340531048203971673798018924835218356727653969476432047791563956910352003139577683814373374455756355618333579781407791677441712021404760146196923694597896628830664258154216715222071348842301514814763614605122296495142868259190882229175498695332019367481899541637969815476657791634843551859858895065167196472312218615184824533035594635568269725438409117970965522515145430165948518129417408395076622908831675470913963313376994783641782463646609850672352393127158160764661443519095237131315801132328494603742188189339292137750365785955842720764481285688317907471117583382034757198652784886103190999683868331425354812304790234142053014700698215152660249945873817109230752861601267500515286184200897574085271213632946200512812990499858903634102342134723766519073679104048682562897362041361321548297366024806645671805473702926879559459967180822739755420193456973725724815164223403184869408076223048342880834667028267961831156151637264856102279420033367341424638542115480550350216104364620150670204628575398065541821863212477254552339079260547379216619983544613039432330709056978785057855656909031784714870140514481174013660939296197305035643567899294754026637705293105666148323832579294791295007793747286973542209526225835756406580619192611195211455809685268303003770918656157721239202920873671843036864381221537655381869923781349845889696874215918177213517203698143724096080831359020436812347379335475234560
theorem adC16_ok : adGo adC16 c16 0 = true := by decide +kernel
end RH2F

-- ===== from FEA.lean =====
namespace RH2F
open MGraph

/-- **layer 36a**: the far-exchange certificate check and its transfer, the cut-witness exclusion of c4c, the host
    check for digon insertions with 16 vertices, the classification step for c4c, and the data `c16` -/
theorem layer36a :
    (∀ (n : Nat) (el : List (Nat × Nat)) (hn : 0 < n) (L : List FES), feCert n el L = true → FEGood (ofList n el hn)) ∧
    (∀ (X H : MGraph) (P : Fin X.m → Prop), IsoFrom P H → FEGood H → FEAll P) ∧
    (∀ (N : Nat) (el : List (Nat × Nat)) (hN : 0 < N) (W : Nat), elOK N el = true → cutB el W = true →
      NC4 (ofList N el hN)) ∧
    (∀ (q lo hi : Nat) (hq : 0 < q) (el : List (Nat × Nat)) (AUT : List (Nat × List Nat))
      (CS : List (Nat × List FES)), q ≤ 16 → covFE q lo hi el AUT (CS.map Prod.fst) = true →
        certsFE q el CS = true → HostFE q lo hi hq el) ∧
    (∀ (n : Nat) (L L2 : List (List (Nat × Nat))) (hn : 0 < n) (hn2 : 0 < n + 2), 4 ≤ n → repsOK n L = true →
      (∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n →
        ∃ k, k < L.length ∧ IsoFrom P (ofList n (L.getD k []) hn)) →
      (∀ k, k < L.length → HostTabW n L L2 hn hn2 k) →
      ∀ (X : MGraph) (P : Fin X.m → Prop), C4C X P → SimpleP P → vcount P = n + 2 →
        ∃ k, k < L2.length ∧ IsoFrom P (ofList (n + 2) (L2.getD k []) hn2)) ∧
    (repsB 16 24 c16 = true ∧ c16.length = 607 ∧ adGo adC16 c16 0 = true) :=
  ⟨fun _ _ _ _ h => feGood_of_cert h,
   fun _ _ _ hI hG => fe_transfer hI hG,
   fun _ _ _ _ hel h => nc4_of_cutB hel h,
   fun _ _ _ _ _ _ _ hq16 hcov hcs => hostFE_of_parts hq16 hcov hcs,
   fun _ _ _ hn hn2 hn4 hL ih htab => cls_stepC hn4 hn hn2 hL ih htab,
   c16_B, c16_len, adC16_ok⟩

end RH2F
