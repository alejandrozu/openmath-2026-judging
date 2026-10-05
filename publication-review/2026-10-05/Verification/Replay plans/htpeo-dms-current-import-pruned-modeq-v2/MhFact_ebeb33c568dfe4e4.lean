-- Lean proof of fact ebeb33c568dfe4e4 (RH2F.layer7); added by fact_submit, do not edit
import MhFact_6e44d3c2232b5736

-- ===== from SF1.lean =====

/-!
  FS2.lean — a lighter star checker: a neighbour table `nb` (for every vertex, the triples (edge, other end, colour))
  is checked once against the edge list and the colouring; the walk enumeration then only compares literals.
-/

namespace RH2F
open MGraph

section fs2

/-- the table contains, for every edge `e = pq`, the triples `(e, q, c e)` at `p` and `(e, p, c e)` at `q` -/
def nbOK (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (cl : List Nat) : Bool :=
  (List.range el.length).all (fun e =>
    (nb.getD (gE el e).1 []).contains (e, (gE el e).2, colN cl e) &&
    (nb.getD (gE el e).2 []).contains (e, (gE el e).1, colN cl e))

def properNB (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  (List.range n).all (fun v => (nb.getD v []).all (fun a => (nb.getD v []).all (fun b =>
    Nat.beq a.1 b.1 || !Nat.beq a.2.2 b.2.2)))

def walkNB (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  (List.range n).all fun v0 => (nb.getD v0 []).all fun t1 =>
    (nb.getD t1.2.1 []).all fun t2 => Nat.beq t2.2.1 v0 || (nb.getD t2.2.1 []).all fun t3 =>
      !Nat.beq t1.2.2 t3.2.2 || Nat.beq t3.2.1 t1.2.1 || (nb.getD t3.2.1 []).all fun t4 =>
        !(Nat.beq t2.2.2 t4.2.2 && !Nat.beq v0 t3.2.1 &&
          !Nat.beq t1.2.1 t4.2.1 && !Nat.beq t2.2.1 t4.2.1 && !Nat.beq t3.2.1 t4.2.1 &&
          !Nat.beq v0 t1.2.1 && !Nat.beq t1.2.1 t2.2.1 && !Nat.beq t2.2.1 t3.2.1)

def fastStar2 (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (cl : List Nat) : Bool :=
  elOK n el && nbOK el nb cl && properNB n nb && walkNB n nb

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

theorem nbeq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

theorem mem_nb (hel : elOK n el = true) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) {e : Fin (ofList n el hn).m} {x y : Fin n} (h : (ofList n el hn).Joins e x y) :
    (e.val, y.val, colN cl e.val) ∈ nb.getD x.val [] := by
  have h1 := List.all_eq_true.1 hnb e.val (List.mem_range.2 e.isLt)
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h1
  have he := ofList_ends (hn := hn) hel e
  rcases h with h | h <;> rw [h] at he <;> simp only at he <;> obtain ⟨e1, e2⟩ := he
  · rw [e1, e2]; exact h1.1
  · rw [e1, e2]; exact h1.2

/-- **soundness** of the table checker -/
theorem star_of_fast2 {nb : List (List (Nat × Nat × Nat))} {cl : List Nat} (h : fastStar2 n el nb cl = true) :
    StarOn (fun _ => True) 6 (colF (ofList n el hn).m cl) := by
  unfold fastStar2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hel, hnb⟩, hprop⟩, hwalk⟩ := h
  constructor
  · intro a b ⟨hab, x, hax, hbx⟩ _ _ heq
    obtain ⟨ya, hja⟩ := joins_of_inc hax
    obtain ⟨yb, hjb⟩ := joins_of_inc hbx
    have ha := mem_nb (hn := hn) hel hnb hja
    have hb := mem_nb (hn := hn) hel hnb hjb
    have h1 := List.all_eq_true.1 hprop x.val (List.mem_range.2 x.isLt)
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 _ ha) _ hb
    have hc : colN cl a.val = colN cl b.val := congrArg Fin.val heq
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    simp only at h2
    rw [nbeq_false hne, nbeq_true hc] at h2
    exact absurd h2 (by decide)
  · intro w _ _ _ _ hbc
    have m1 := mem_nb (hn := hn) hel hnb w.h1
    have m2 := mem_nb (hn := hn) hel hnb w.h2
    have m3 := mem_nb (hn := hn) hel hnb w.h3
    have m4 := mem_nb (hn := hn) hel hnb w.h4
    have d01 : w.v0.val ≠ w.v1.val := fun h => w.d01 (Fin.ext h)
    have d02 : w.v0.val ≠ w.v2.val := fun h => w.d02 (Fin.ext h)
    have d03 : w.v0.val ≠ w.v3.val := fun h => w.d03 (Fin.ext h)
    have d12 : w.v1.val ≠ w.v2.val := fun h => w.d12 (Fin.ext h)
    have d13 : w.v1.val ≠ w.v3.val := fun h => w.d13 (Fin.ext h)
    have d14 : w.v1.val ≠ w.v4.val := fun h => w.d14 (Fin.ext h)
    have d23 : w.v2.val ≠ w.v3.val := fun h => w.d23 (Fin.ext h)
    have d24 : w.v2.val ≠ w.v4.val := fun h => w.d24 (Fin.ext h)
    have d34 : w.v3.val ≠ w.v4.val := fun h => w.d34 (Fin.ext h)
    have c13 : colN cl w.e1.val = colN cl w.e3.val := congrArg Fin.val hbc.1
    have c24 : colN cl w.e2.val = colN cl w.e4.val := congrArg Fin.val hbc.2
    have k0 := List.all_eq_true.1 hwalk w.v0.val (List.mem_range.2 w.v0.isLt)
    have k1 := List.all_eq_true.1 k0 _ m1
    have k2 := List.all_eq_true.1 k1 _ m2
    simp only at k2
    rw [nbeq_false (Ne.symm d02)] at k2
    simp only [Bool.false_or] at k2
    have k3 := List.all_eq_true.1 k2 _ m3
    simp only at k3
    rw [nbeq_true c13, nbeq_false (Ne.symm d13)] at k3
    simp only [Bool.not_true, Bool.false_or] at k3
    have k4 := List.all_eq_true.1 k3 _ m4
    simp only at k4
    rw [nbeq_false d01, nbeq_false d03, nbeq_false d12, nbeq_false d14,
      nbeq_false d23, nbeq_false d24, nbeq_false d34, nbeq_true c24] at k4
    exact absurd k4 (by decide)

end fs2

end RH2F


namespace RH2F
open MGraph

section pm

/-- every table entry is a real edge at `v` with its colour -/
def nbSound (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (cl : List Nat) : Bool :=
  (List.range n).all (fun v => (nb.getD v []).all (fun t => Nat.blt t.1 el.length &&
    ((Nat.beq (gE el t.1).1 v && Nat.beq (gE el t.1).2 t.2.1) || (Nat.beq (gE el t.1).1 t.2.1 && Nat.beq (gE el t.1).2 v)) &&
    Nat.beq t.2.2 (colN cl t.1)))

/-- every vertex has exactly one table entry of colour `5` -/
def pmNB (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  (List.range n).all (fun v => Nat.beq ((nb.getD v []).filter (fun t => Nat.beq t.2.2 5)).length 1)

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

theorem nb_real (hel : elOK n el = true) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hs : nbSound n el nb cl = true) {v : Nat} (hv : v < n) {t : Nat × Nat × Nat} (ht : t ∈ nb.getD v []) :
    ∃ e : Fin (ofList n el hn).m, e.val = t.1 ∧ (ofList n el hn).Inc e ⟨v, hv⟩ ∧ colN cl e.val = t.2.2 := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hs v (List.mem_range.2 hv)) t ht
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
  obtain ⟨⟨hlt, hj⟩, hc⟩ := h1
  have hlt' : t.1 < el.length := Nat.le_of_ble_eq_true hlt
  refine ⟨⟨t.1, hlt'⟩, rfl, ?_, (Nat.eq_of_beq_eq_true hc).symm⟩
  have he := ofList_ends (hn := hn) hel ⟨t.1, hlt'⟩
  rcases hj with ⟨h2, _⟩ | ⟨_, h2⟩
  · exact Or.inl (Fin.ext (he.1.trans (Nat.eq_of_beq_eq_true h2)))
  · exact Or.inr (Fin.ext (he.2.trans (Nat.eq_of_beq_eq_true h2)))

/-- the colour class `5` is a perfect matching of `ofList n el` -/
theorem pm_of_nb (hel : elOK n el = true) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) (hs : nbSound n el nb cl = true) (hpm : pmNB n nb = true) (x : Fin n) :
    ∃ e : Fin (ofList n el hn).m, colF _ cl e = 5 ∧ (ofList n el hn).Inc e x ∧
      ∀ e', colF _ cl e' = 5 → (ofList n el hn).Inc e' x → e' = e := by
  have h1 := Nat.eq_of_beq_eq_true (List.all_eq_true.1 hpm x.val (List.mem_range.2 x.isLt))
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 h1
  have htm : t ∈ (nb.getD x.val []).filter (fun t => Nat.beq t.2.2 5) := by rw [ht]; simp
  rw [List.mem_filter] at htm
  obtain ⟨e, he, hinc, hcol⟩ := nb_real (hn := hn) hel hs x.isLt htm.1
  have hc5 : colN cl e.val = 5 := hcol.trans (Nat.eq_of_beq_eq_true htm.2)
  refine ⟨e, Fin.ext hc5, hinc, fun e' hc' hi' => ?_⟩
  obtain ⟨y, hj⟩ := joins_of_inc hi'
  have hm := mem_nb (hn := hn) hel hnb hj
  have hc5' : colN cl e'.val = 5 := congrArg Fin.val hc'
  have : (e'.val, y.val, colN cl e'.val) ∈ (nb.getD x.val []).filter (fun t => Nat.beq t.2.2 5) := by
    rw [List.mem_filter]; exact ⟨hm, by simp [hc5']⟩
  rw [ht, List.mem_singleton] at this
  exact Fin.ext ((congrArg Prod.fst this).trans he.symm)

end pm

end RH2F


-- ===== from SF2.lean =====

namespace RH2F
open MGraph

section ex1t
variable {X : MGraph} {P : Fin X.m → Prop}

/-- star colourings pull back along an isomorphism onto a concrete multigraph -/
theorem starOn_of_iso' {H : MGraph} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m}
    (hα : ∀ x y, meets P x → meets P y → α x = α y → x = y) (hβ : ∀ f g, P f → P g → β f = β g → f = g)
    (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {c : Fin H.m → Fin 6}
    (hc : StarOn (fun _ => True) 6 c) : StarOn P 6 (fun f => c (β f)) :=
  starOn_embed α β (fun x y a b ha hb hax hby h => hα x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩ h) hβ (fun _ _ => trivial) hj hc

/-- `H` is EX1-full: for every edge and status, a star 6-colouring whose colour class `5` is a perfect matching
    with that status -/
def EX1FullH (H : MGraph) : Prop :=
  ∀ j : Fin H.m, ∀ t : Bool, ∃ c : Fin H.m → Fin 6, StarOn (fun _ => True) 6 c ∧
    (∀ p : Fin H.n, ∃ e, c e = 5 ∧ H.Inc e p ∧ ∀ e', c e' = 5 → H.Inc e' p → e' = e) ∧ (c j = 5 ↔ t = true)

/-- EX1-goodness transfers along an isomorphism from an EX1-full multigraph -/
theorem ex1On_of_iso {H : MGraph} (h : IsoFrom P H) (hH : EX1FullH H) : EX1On P := by
  intro g hg t _
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := h
  obtain ⟨c, hc, hpm, hct⟩ := hH (β g) t
  have incx : ∀ f x, P f → meets P x → H.Inc (β f) (α x) → X.Inc f x := by
    intro f x hf hx hi
    have hjf := hj f hf
    rcases inc_of_joins hjf hi with h1 | h1
    · exact Or.inl (hα _ _ ⟨f, hf, Or.inl rfl⟩ hx h1.symm)
    · exact Or.inr (hα _ _ ⟨f, hf, Or.inr rfl⟩ hx h1.symm)
  have incH : ∀ f x, P f → X.Inc f x → H.Inc (β f) (α x) := by
    intro f x hf hi
    rcases hi with h1 | h1
    · rw [← h1]; exact joins_inc_left (hj f hf)
    · rw [← h1]; exact joins_inc_right (hj f hf)
  refine ⟨fun f => P f ∧ c (β f) = 5, ⟨fun f hf => hf.1, fun x hx => ?_⟩, ?_, fun f => c (β f),
    starOn_of_iso' hα hβ hj hc, ⟨5, fun f hf => ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩⟩⟩
  · obtain ⟨e, he5, hei, heu⟩ := hpm (α x)
    obtain ⟨f, hf, rfl⟩ := hs e
    refine ⟨f, ⟨hf, he5⟩, incx f x hf hx hei, fun d hd hdx => ?_⟩
    exact hβ _ _ hd.1 hf (heu _ hd.2 (incH d x hd.1 hdx))
  · simp only [hg, true_and]; exact hct

end ex1t

section excert

/-- the Bool check of an EX1 certificate list `cs` (pairs: neighbour table, colouring) for `ofList n el` -/
def exCert (n : Nat) (el : List (Nat × Nat)) (cs : List (List (List (Nat × Nat × Nat)) × List Nat)) : Bool :=
  cs.all (fun q => fastStar2 n el q.1 q.2 && nbSound n el q.1 q.2 && pmNB n q.1) &&
  (List.range el.length).all (fun e => cs.any (fun q => Nat.beq (colN q.2 e) 5) &&
    cs.any (fun q => !Nat.beq (colN q.2 e) 5))

theorem ex1Full_of_cert {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}
    {cs : List (List (List (Nat × Nat × Nat)) × List Nat)} (h : exCert n el cs = true) : EX1FullH (ofList n el hn) := by
  unfold exCert at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hall, hcov⟩ := h
  intro j t
  have hc := List.all_eq_true.1 hcov j.val (List.mem_range.2 j.isLt)
  simp only [Bool.and_eq_true] at hc
  have pick : ∃ q ∈ cs, (colN q.2 j.val = 5 ↔ t = true) := by
    cases t
    · obtain ⟨q, hq, hq5⟩ := List.any_eq_true.1 hc.2
      refine ⟨q, hq, ?_⟩
      simp only [Bool.not_eq_true'] at hq5
      constructor
      · intro h5; rw [h5] at hq5; exact absurd hq5 (by decide)
      · intro h; exact absurd h (by decide)
    · obtain ⟨q, hq, hq5⟩ := List.any_eq_true.1 hc.1
      exact ⟨q, hq, ⟨fun _ => rfl, fun _ => Nat.eq_of_beq_eq_true hq5⟩⟩
  obtain ⟨q, hq, hqt⟩ := pick
  have hqa := List.all_eq_true.1 hall q hq
  simp only [Bool.and_eq_true] at hqa
  obtain ⟨⟨hst, hsd⟩, hpm⟩ := hqa
  have hst' := hst
  unfold fastStar2 at hst'
  simp only [Bool.and_eq_true] at hst'
  refine ⟨colF _ q.2, star_of_fast2 (hn := hn) hst, fun p => pm_of_nb (hn := hn) hst'.1.1.1 hst'.1.1.2 hsd hpm p, ?_⟩
  exact ⟨fun h => hqt.1 (congrArg Fin.val h), fun h => Fin.ext (hqt.2 h)⟩

end excert

end RH2F


-- ===== from SF3.lean =====

namespace RH2F
open MGraph
open Classical

section isomap
variable {X : MGraph} {P : Fin X.m → Prop}

/-- explicit isomorphism maps from `P` onto a concrete multigraph `H` -/
def IsoMap (P : Fin X.m → Prop) (H : MGraph) (α : Fin X.n → Fin H.n) (β : Fin X.m → Fin H.m) : Prop :=
  (∀ x y, meets P x → meets P y → α x = α y → x = y) ∧ (∀ f g, P f → P g → β f = β g → f = g) ∧
  (∀ j, ∃ f, P f ∧ β f = j) ∧ (∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2))

theorem isoFrom_iff {H : MGraph} : IsoFrom P H ↔ ∃ α β, IsoMap P H α β := Iff.rfl

/-- explicit isomorphism maps of concrete multigraphs -/
def ConcMap (H H' : MGraph) (σ : Fin H.n → Fin H'.n) (τ : Fin H.m → Fin H'.m) : Prop :=
  (∀ a b, σ a = σ b → a = b) ∧ (∀ e e', τ e = τ e' → e = e') ∧ (∀ j, ∃ e, τ e = j) ∧
    (∀ e, H'.Joins (τ e) (σ (H.ends e).1) (σ (H.ends e).2))

theorem isoMap_comp {H H' : MGraph} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m} {σ : Fin H.n → Fin H'.n}
    {τ : Fin H.m → Fin H'.m} (h : IsoMap P H α β) (h' : ConcMap H H' σ τ) :
    IsoMap P H' (fun x => σ (α x)) (fun f => τ (β f)) := by
  obtain ⟨hα, hβ, hs, hj⟩ := h
  obtain ⟨hσ, hτ, hτs, hτj⟩ := h'
  refine ⟨fun x y hx hy h => hα x y hx hy (hσ _ _ h), fun f g hf hg h => hβ f g hf hg (hτ _ _ h), fun j => ?_,
    fun f hf => joins_map hτj (hj f hf)⟩
  obtain ⟨e, rfl⟩ := hτs j
  obtain ⟨f, hf, rfl⟩ := hs e
  exact ⟨f, hf, rfl⟩

theorem concMap_of_chk {H H' : MGraph} {hn : 0 < H'.n} {hm : 0 < H'.m} {s t : List Nat}
    (h : isoChk H H' hn hm s t = true) :
    ConcMap H H' (fun a => lget s H'.n hn a.val) (fun e => lget t H'.m hm e.val) := by
  simp only [isoChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun a b hab => ?_, fun e e' hee => ?_, fun j => ?_, fun e => ?_⟩
  · have := allFin_sound (allFin_sound h1 a) b
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hab h
    · exact h
  · have := allFin_sound (allFin_sound h2 e) e'
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hee h
    · exact h
  · have := allFin_sound h3 j
    obtain ⟨e, _, he⟩ := List.any_eq_true.1 this
    exact ⟨e, by simpa using he⟩
  · have := allFin_sound h4 e
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h

end isomap

/-! ### the concrete 2-pole of a closure edge -/

/-- the edge list of the 2-pole `A⁺` of `ofList n el` at edge `j`: edge `j` becomes the pendant `x ℓ1` (`ℓ1 = n`) and
    a new last edge `y ℓ2` (`ℓ2 = n + 1`) is appended, where `(x, y)` are the ends of `j`, in the order given by `o` -/
def poleEl (el : List (Nat × Nat)) (n j : Nat) (o : Bool) : List (Nat × Nat) :=
  el.set j (if o then ((gE el j).2, n) else ((gE el j).1, n)) ++
    [if o then ((gE el j).1, n + 1) else ((gE el j).2, n + 1)]

section poleEl
variable {el : List (Nat × Nat)} {n j : Nat} {o : Bool}

theorem poleEl_length : (poleEl el n j o).length = el.length + 1 := by simp [poleEl]

theorem poleEl_old {i : Nat} (hi : i < el.length) (hij : i ≠ j) : gE (poleEl el n j o) i = gE el i := by
  unfold gE poleEl
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi),
    List.getElem?_set_ne (Ne.symm hij)]

theorem poleEl_j (hj : j < el.length) :
    gE (poleEl el n j o) j = (if o then ((gE el j).2, n) else ((gE el j).1, n)) := by
  rw [show gE (poleEl el n j o) j = (poleEl el n j o).getD j (0, 0) from rfl]
  unfold poleEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj), List.getElem?_set_self hj]
  rfl

theorem poleEl_last : gE (poleEl el n j o) el.length = (if o then ((gE el j).1, n + 1) else ((gE el j).2, n + 1)) := by
  rw [show gE (poleEl el n j o) el.length = (poleEl el n j o).getD el.length (0, 0) from rfl]
  unfold poleEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

end poleEl


theorem elOK_pole {n : Nat} {el : List (Nat × Nat)} {j : Nat} {o : Bool} (hel : elOK n el = true) (hj : j < el.length) :
    elOK (n + 2) (poleEl el n j o) = true := by
  unfold elOK at hel ⊢
  rw [List.all_eq_true] at hel ⊢
  have hjm : gE el j ∈ el := by
    unfold gE; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hb := hel _ hjm
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  intro e he
  unfold poleEl at he
  rw [List.mem_append, List.mem_singleton] at he
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  rcases he with he | rfl
  · rcases List.mem_or_eq_of_mem_set he with he | rfl
    · have := hel e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
      exact ⟨⟨by omega, by omega⟩, this.2⟩
    · cases o <;> simp only [if_true, if_false, Bool.false_eq_true] <;> exact ⟨⟨by omega, by omega⟩, by omega⟩
  · cases o <;> simp only [if_true, if_false, Bool.false_eq_true] <;> exact ⟨⟨by omega, by omega⟩, by omega⟩

section poleiso
variable {X : MGraph} {P : Fin X.m → Prop}

/-- a vertex of the pole is a vertex of the closure on side `A`, or one of the pendant vertices `b1`, `b2` -/
theorem Cut2.pole_vertex (C : Cut2 P) {v : Fin X.n} (h : meets C.pole v) :
    (C.S v = true ∧ meets C.clo v) ∨ v = C.b1 ∨ v = C.b2 := by
  obtain ⟨f, hf, hfv⟩ := h
  rcases hf with hA | hc
  · exact Or.inl ⟨C.side_of_inA hA hfv, ⟨Fin.castSucc f, C.clo_old hA, addEdge_inc_old.2 hfv⟩⟩
  · by_cases hs : C.S v = true
    · refine Or.inl ⟨hs, ⟨Fin.last X.m, C.clo_last, (C.inc_new_iff).2 ?_⟩⟩
      rcases C.cutA hc hfv hs with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases hc with rfl | rfl
      · rcases C.inc_e1 hfv with h | h
        · rw [h, C.sa1] at hs; exact absurd rfl hs
        · exact Or.inr (Or.inl h)
      · rcases C.inc_e2 hfv with h | h
        · rw [h, C.sa2] at hs; exact absurd rfl hs
        · exact Or.inr (Or.inr h)


/-- **the 2-pole isomorphism**: an isomorphism of the edge closure `G_A` onto `ofList n el` sending `g_A` to edge `j`
    gives an isomorphism of the pole `A⁺` onto the concrete pole `ofList (n + 2) (poleEl el n j o)`, sending `e1` to
    the pendant `j` and `e2` to the new last edge; `o` fixes which end of `j` is the image of `a1` -/
theorem Cut2.pole_iso (C : Cut2 P) {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m}
    (hiso : IsoMap C.clo (ofList n el hn) α β) (o : Bool)
    (ho1 : (if o then (gE el (β (Fin.last X.m)).val).2 else (gE el (β (Fin.last X.m)).val).1) = (α C.a1).val)
    (ho2 : (if o then (gE el (β (Fin.last X.m)).val).1 else (gE el (β (Fin.last X.m)).val).2) = (α C.a2).val) :
    ∃ (α' : Fin X.n → Fin (n + 2)) (ψ : Fin X.m → Fin (poleEl el n (β (Fin.last X.m)).val o).length),
      IsoMap C.pole (ofList (n + 2) (poleEl el n (β (Fin.last X.m)).val o) (by omega)) α' ψ ∧
      (ψ C.e1).val = (β (Fin.last X.m)).val ∧ (ψ C.e2).val = el.length ∧
      (∀ f, C.inA f → (ψ f).val ≠ (β (Fin.last X.m)).val ∧ (ψ f).val < el.length) ∧
      (α' C.a1).val = (α C.a1).val ∧ (α' C.a2).val = (α C.a2).val ∧
      (∀ v, C.S v = true → (α' v).val = (α v).val) ∧ (α' C.b1).val = n ∧ (α' C.b2).val = n + 1 := by
  obtain ⟨hα, hβ, hs, hj⟩ := hiso
  let j := (β (Fin.last X.m)).val
  have hjl : j < el.length := (β (Fin.last X.m)).isLt
  have hlen := poleEl_length (el := el) (n := n) (j := j) (o := o)
  let α' : Fin X.n → Fin (n + 2) := fun v =>
    if C.S v = true then ⟨(α v).val, by have : (α v).val < n := (α v).isLt; omega⟩
    else if v = C.b1 then ⟨n, by omega⟩ else ⟨n + 1, by omega⟩
  let ψ : Fin X.m → Fin (poleEl el n j o).length := fun f =>
    if f = C.e1 then ⟨j, by omega⟩ else if f = C.e2 then ⟨el.length, by omega⟩
    else ⟨(β (Fin.castSucc f)).val, by have : (β (Fin.castSucc f)).val < el.length := (β (Fin.castSucc f)).isLt; omega⟩
  have αA : ∀ v, C.S v = true → (α' v).val = (α v).val := fun v hv => by simp [α', hv]
  have αb1 : (α' C.b1).val = n := by simp [α', C.sb1]
  have αb2 : (α' C.b2).val = n + 1 := by simp [α', C.sb2, Ne.symm C.hb]
  have ψe1 : (ψ C.e1).val = j := by simp [ψ]
  have ψe2 : (ψ C.e2).val = el.length := by simp [ψ, Ne.symm C.ne12]
  have ψA : ∀ f, C.inA f → (ψ f).val = (β (Fin.castSucc f)).val := by
    intro f hf
    have h1 : f ≠ C.e1 := fun h => C.not_inA_of_cut (Or.inl h) hf
    have h2 : f ≠ C.e2 := fun h => C.not_inA_of_cut (Or.inr h) hf
    simp [ψ, h1, h2]
  have βne : ∀ f, C.inA f → (β (Fin.castSucc f)).val ≠ j := by
    intro f hf h
    have := hβ _ _ (C.clo_old hf) C.clo_last (Fin.ext h)
    exact castSucc_ne_last f this
  have hel' := elOK_pole (o := o) hel hjl
  -- the ends of the concrete edges
  have endsP := fun (e : Fin (ofList (n + 2) (poleEl el n j o) (by omega)).m) => ofList_ends (hn := by omega) hel' e
  have endsQ := fun (e : Fin (ofList n el hn).m) => ofList_ends (hn := hn) hel e
  refine ⟨α', ψ, ⟨?_, ?_, ?_, ?_⟩, ψe1, ψe2, fun f hf => ⟨by rw [ψA f hf]; exact βne f hf,
    by rw [ψA f hf]; exact (β (Fin.castSucc f)).isLt⟩, αA _ C.sa1, αA _ C.sa2, αA, αb1, αb2⟩
  · -- vertices
    intro x y hx hy hxy
    have hxy' := congrArg Fin.val hxy
    rcases C.pole_vertex hx with ⟨sx, mx⟩ | rfl | rfl <;> rcases C.pole_vertex hy with ⟨sy, my⟩ | rfl | rfl
    · rw [αA x sx, αA y sy] at hxy'; exact hα x y mx my (Fin.ext hxy')
    · rw [αA x sx, αb1] at hxy'; have : (α x).val < n := (α x).isLt; omega
    · rw [αA x sx, αb2] at hxy'; have : (α x).val < n := (α x).isLt; omega
    · rw [αb1, αA y sy] at hxy'; have : (α y).val < n := (α y).isLt; omega
    · rfl
    · rw [αb1, αb2] at hxy'; omega
    · rw [αb2, αA y sy] at hxy'; have : (α y).val < n := (α y).isLt; omega
    · rw [αb2, αb1] at hxy'; omega
    · rfl
  · -- edges
    intro f g hf hg hfg
    have hfg' := congrArg Fin.val hfg
    rcases hf with fA | fc <;> rcases hg with gA | gc
    · rw [ψA f fA, ψA g gA] at hfg'
      exact castSucc_inj' (hβ _ _ (C.clo_old fA) (C.clo_old gA) (Fin.ext hfg'))
    · rw [ψA f fA] at hfg'
      rcases gc with rfl | rfl
      · rw [ψe1] at hfg'; exact absurd hfg' (βne f fA)
      · rw [ψe2] at hfg'; have : (β (Fin.castSucc f)).val < el.length := (β (Fin.castSucc f)).isLt; omega
    · rw [ψA g gA] at hfg'
      rcases fc with rfl | rfl
      · rw [ψe1] at hfg'; exact absurd hfg'.symm (βne g gA)
      · rw [ψe2] at hfg'; have : (β (Fin.castSucc g)).val < el.length := (β (Fin.castSucc g)).isLt; omega
    · rcases fc with rfl | rfl <;> rcases gc with rfl | rfl
      · rfl
      · rw [ψe1, ψe2] at hfg'; omega
      · rw [ψe1, ψe2] at hfg'; omega
      · rfl
  · -- surjective
    intro i
    by_cases hil : i.val = el.length
    · exact ⟨C.e2, Or.inr (Or.inr rfl), Fin.ext (ψe2.trans hil.symm)⟩
    · have hi' : i.val < el.length := by have : i.val < (poleEl el n j o).length := i.isLt; omega
      obtain ⟨g, hg, hgi⟩ := hs ⟨i.val, hi'⟩
      rcases hg with rfl | ⟨d, rfl, hd⟩
      · exact ⟨C.e1, Or.inr (Or.inl rfl), Fin.ext (by rw [ψe1]; exact (congrArg Fin.val hgi))⟩
      · exact ⟨d, Or.inl hd, Fin.ext (by rw [ψA d hd]; exact (congrArg Fin.val hgi))⟩
  · -- incidence
    intro f hf
    have hPe := endsP (ψ f)
    rcases hf with fA | fc
    · have hjf := hj _ (C.clo_old fA)
      have s1 := C.side_of_inA fA (Or.inl rfl)
      have s2 := C.side_of_inA fA (Or.inr rfl)
      rw [addEdge_ends_old] at hjf
      have hQ := endsQ (β (Fin.castSucc f))
      rw [ψA f fA, poleEl_old (β (Fin.castSucc f)).isLt (βne f fA)] at hPe
      rcases hjf with h | h <;> rw [h] at hQ <;> simp only at hQ
      · exact Or.inl (Prod.ext (Fin.ext (by rw [hPe.1, αA _ s1]; exact hQ.1.symm))
          (Fin.ext (by rw [hPe.2, αA _ s2]; exact hQ.2.symm)))
      · exact Or.inr (Prod.ext (Fin.ext (by rw [hPe.1, αA _ s2]; exact hQ.1.symm))
          (Fin.ext (by rw [hPe.2, αA _ s1]; exact hQ.2.symm)))
    · rcases fc with rfl | rfl
      · rw [ψe1, poleEl_j hjl] at hPe
        have ha1 : (α' C.a1).val = (if o then (gE el j).2 else (gE el j).1) := by rw [αA _ C.sa1]; exact ho1.symm
        rcases C.j1 with h | h <;> rw [h]
        · refine Or.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
          · rw [hPe.1, ha1]; cases o <;> rfl
          · rw [hPe.2, αb1]; cases o <;> rfl
        · refine Or.inr (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
          · rw [hPe.1, ha1]; cases o <;> rfl
          · rw [hPe.2, αb1]; cases o <;> rfl
      · rw [ψe2, poleEl_last] at hPe
        have ha2 : (α' C.a2).val = (if o then (gE el j).1 else (gE el j).2) := by rw [αA _ C.sa2]; exact ho2.symm
        rcases C.j2 with h | h <;> rw [h]
        · refine Or.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
          · rw [hPe.1, ha2]; cases o <;> rfl
          · rw [hPe.2, αb2]; cases o <;> rfl
        · refine Or.inr (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
          · rw [hPe.1, ha2]; cases o <;> rfl
          · rw [hPe.2, αb2]; cases o <;> rfl

end poleiso

end RH2F


-- ===== from SF4.lean =====

namespace RH2F
open MGraph
open Classical

section poledata
variable {X : MGraph} {P : Fin X.m → Prop}

/-- an isomorphism of the pole of `C` onto a concrete pole `ofList (n + 2) el` with pendants `j` (at `x`) and `L`
    (at `y`), side `A` going to the vertices `< n` -/
structure PoleData (C : Cut2 P) (n : Nat) (el : List (Nat × Nat)) (j L x y : Nat) where
  α : Fin X.n → Fin (n + 2)
  ψ : Fin X.m → Fin el.length
  hel : elOK (n + 2) el = true
  iso : IsoMap C.pole (ofList (n + 2) el (by omega)) α ψ
  he1 : (ψ C.e1).val = j
  he2 : (ψ C.e2).val = L
  hin : ∀ f, C.inA f → (ψ f).val ≠ j ∧ (ψ f).val ≠ L
  ha1 : (α C.a1).val = x
  ha2 : (α C.a2).val = y
  hA : ∀ v, C.S v = true → (α v).val < n

namespace PoleData
variable {C : Cut2 P} {n : Nat} {el : List (Nat × Nat)} {j L x y : Nat}

/-- the concrete pole graph -/
abbrev Y (_D : PoleData C n el j L x y) : MGraph := ofList (n + 2) el (by omega)

theorem jL (D : PoleData C n el j L x y) : j ≠ L := by
  intro h
  have := D.iso.2.1 C.e1 C.e2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Fin.ext (by rw [D.he1, D.he2]; exact h))
  exact C.ne12 this

theorem _root_.RH2F.Cut2.meets_pole_of_A (C : Cut2 P) {v : Fin X.n} (hv : C.S v = true) (hm : meets P v) :
    meets C.pole v := by
  obtain ⟨f, hf, hfv⟩ := hm
  by_cases hc : C.isCut f
  · exact ⟨f, Or.inr hc, hfv⟩
  · exact ⟨f, Or.inl (C.inA_of_notcut hf hc hfv hv), hfv⟩

/-- incidence of pole edges at pole vertices is reflected -/
theorem inc_iff (D : PoleData C n el j L x y) {f : Fin X.m} (hf : C.pole f) {v : Fin X.n} (hv : meets C.pole v) :
    X.Inc f v ↔ D.Y.Inc (D.ψ f) (D.α v) := by
  have hj := D.iso.2.2.2 f hf
  constructor
  · rintro (h | h)
    · rw [← h]; exact joins_inc_left hj
    · rw [← h]; exact joins_inc_right hj
  · intro hi
    rcases inc_of_joins hj hi with h | h
    · exact Or.inl (D.iso.1 _ _ ⟨f, hf, Or.inl rfl⟩ hv h.symm)
    · exact Or.inr (D.iso.1 _ _ ⟨f, hf, Or.inr rfl⟩ hv h.symm)

/-- a table entry at the image of a side-`A` vertex that is not a pendant comes from an inside edge -/
theorem entry_inside (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hs : nbSound (n + 2) el nb cl = true) {v : Fin X.n} (hv : C.S v = true) (hm : meets P v)
    {t : Nat × Nat × Nat} (ht : t ∈ nb.getD (D.α v).val []) (hj : t.1 ≠ j) (hL : t.1 ≠ L) :
    ∃ f, C.inA f ∧ (D.ψ f).val = t.1 ∧ X.Inc f v ∧ colN cl t.1 = t.2.2 := by
  obtain ⟨e, he, hinc, hc⟩ := nb_real (hn := by omega) D.hel hs (D.α v).isLt ht
  obtain ⟨f, hf, hfe⟩ := D.iso.2.2.1 e
  have hmv := C.meets_pole_of_A hv hm
  have hfv : X.Inc f v := (D.inc_iff hf hmv).2 (by rw [hfe]; exact hinc)
  refine ⟨f, ?_, by rw [hfe]; exact he, hfv, by rw [← he]; exact hc⟩
  rcases hf with hA | hcut
  · exact hA
  · exfalso
    rcases hcut with rfl | rfl
    · exact hj (by rw [← he, ← hfe]; exact D.he1)
    · exact hL (by rw [← he, ← hfe]; exact D.he2)

/-- the table entry of an inside edge at a side-`A` end -/
theorem entry_of_inside (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat} (hnb : nbOK el nb cl = true)
    {f : Fin X.m} (hf : C.inA f) {v : Fin X.n} (hfv : X.Inc f v) :
    ∃ w, ((D.ψ f).val, w, colN cl (D.ψ f).val) ∈ nb.getD (D.α v).val [] := by
  have hj := D.iso.2.2.2 f (Or.inl hf)
  rcases hfv with h | h
  · rw [← h]; exact ⟨_, mem_nb (hn := by omega) D.hel hnb hj⟩
  · rw [← h]; exact ⟨_, mem_nb (hn := by omega) D.hel hnb (Or.symm hj)⟩

end PoleData

end poledata

/-- a perfect-matching check restricted to the vertices `< k` -/
theorem pm_at {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {nb : List (List (Nat × Nat × Nat))} {cl : List Nat} {k : Nat}
    (hnb : nbOK el nb cl = true) (hs : nbSound n el nb cl = true) (hpm : pmNB k nb = true) (x : Fin n) (hx : x.val < k) :
    ∃ e : Fin (ofList n el hn).m, colF _ cl e = 5 ∧ (ofList n el hn).Inc e x ∧
      ∀ e', colF _ cl e' = 5 → (ofList n el hn).Inc e' x → e' = e := by
  have h1 := Nat.eq_of_beq_eq_true (List.all_eq_true.1 hpm x.val (List.mem_range.2 hx))
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 h1
  have htm : t ∈ (nb.getD x.val []).filter (fun t => Nat.beq t.2.2 5) := by rw [ht]; simp
  rw [List.mem_filter] at htm
  obtain ⟨e, he, hinc, hcol⟩ := nb_real (hn := hn) hel hs x.isLt htm.1
  have hc5 : colN cl e.val = 5 := hcol.trans (Nat.eq_of_beq_eq_true htm.2)
  refine ⟨e, Fin.ext hc5, hinc, fun e' hc' hi' => ?_⟩
  obtain ⟨y, hj⟩ := joins_of_inc hi'
  have hm := mem_nb (hn := hn) hel hnb hj
  have hc5' : colN cl e'.val = 5 := congrArg Fin.val hc'
  have : (e'.val, y.val, colN cl e'.val) ∈ (nb.getD x.val []).filter (fun t => Nat.beq t.2.2 5) := by
    rw [List.mem_filter]; exact ⟨hm, by simp [hc5']⟩
  rw [ht, List.mem_singleton] at this
  exact Fin.ext ((congrArg Prod.fst this).trans he.symm)

end RH2F


-- ===== from SF5.lean =====

namespace RH2F
open MGraph
open Classical

section cert

/-- a table entry of an edge other than the pendants `j`, `L` -/
def insideT (j L : Nat) (t : Nat × Nat × Nat) : Bool := !Nat.beq t.1 j && !Nat.beq t.1 L

def meetB (nb : List (List (Nat × Nat × Nat))) (j L x y : Nat) : Bool :=
  (nb.getD x []).any (fun t => insideT j L t && (nb.getD y []).any (fun t' => insideT j L t' && Nat.beq t.2.2 t'.2.2))

def smallB (nb : List (List (Nat × Nat × Nat))) (j L x y : Nat) : Bool :=
  (nb.getD x []).any (fun t => insideT j L t && (nb.getD y []).all (fun t' => !insideT j L t' || !Nat.beq t'.2.2 t.2.2))

def noRungB (nb : List (List (Nat × Nat × Nat))) (j L x y : Nat) : Bool :=
  (nb.getD x []).all (fun t => !(insideT j L t && Nat.beq t.2.1 y && Nat.beq t.2.2 5))

def ncB (nb : List (List (Nat × Nat × Nat))) (j L x γ : Nat) : Bool :=
  (nb.getD x []).all (fun t => !insideT j L t || Nat.beq t.2.2 5 || !Nat.beq t.2.2 γ)

/-- the common part of a pole certificate check -/
def baseB (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (cl : List Nat) : Bool :=
  fastStar2 (n + 2) el nb cl && nbSound (n + 2) el nb cl && pmNB n nb

/-- the type condition: codes `0, 1, 2` (M-type with `t = code`; here `0`: `t ≤ 1`, `1`: `t = 1`, `2`: `t ≥ 1`),
    `3` Feq, `4` Fnc, `5` Fneq -/
def typeB (j L x y : Nat) : Nat → List (List (Nat × Nat × Nat)) → List Nat → Bool
  | 0, nb, cl => Nat.beq (colN cl j) 5 && Nat.beq (colN cl L) 5 && (smallB nb j L x y || smallB nb j L y x)
  | 1, nb, cl => Nat.beq (colN cl j) 5 && Nat.beq (colN cl L) 5 && (smallB nb j L x y || smallB nb j L y x) &&
      meetB nb j L x y
  | 2, nb, cl => Nat.beq (colN cl j) 5 && Nat.beq (colN cl L) 5 && meetB nb j L x y
  | 3, nb, cl => Nat.beq (colN cl j) (colN cl L) && !Nat.beq (colN cl j) 5 && noRungB nb j L x y
  | 4, nb, cl => !Nat.beq (colN cl j) 5 && !Nat.beq (colN cl L) 5 && !Nat.beq (colN cl j) (colN cl L) &&
      ncB nb j L x (colN cl L) && ncB nb j L y (colN cl j)
  | 5, _, cl => !Nat.beq (colN cl j) 5 && !Nat.beq (colN cl L) 5 && !Nat.beq (colN cl j) (colN cl L)
  | _, _, _ => false

def certB (n : Nat) (el : List (Nat × Nat)) (j L x y : Nat)
    (q : Nat × List (List (Nat × Nat × Nat)) × List Nat) : Bool :=
  baseB n el q.2.1 q.2.2 && typeB j L x y q.1 q.2.1 q.2.2

/-- coverage of the inside edges by certificates with codes in `codes` -/
def covB (el : List (Nat × Nat)) (j L : Nat) (codes : List Nat)
    (cs : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)) : Bool :=
  (List.range el.length).all (fun i => Nat.beq i j || Nat.beq i L ||
    (cs.any (fun q => codes.contains q.1 && Nat.beq (colN q.2.2 i) 5) &&
     cs.any (fun q => codes.contains q.1 && !Nat.beq (colN q.2.2 i) 5)))

def recipeDB (n : Nat) (el : List (Nat × Nat)) (j L x y : Nat)
    (cs : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)) : Bool :=
  cs.all (certB n el j L x y) && cs.any (fun q => q.1 == 1 || q.1 == 2) && cs.any (fun q => q.1 == 4) &&
    covB el j L [1, 2, 4] cs

def recipeEB (n : Nat) (el : List (Nat × Nat)) (j L x y : Nat)
    (cs : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)) : Bool :=
  cs.all (certB n el j L x y) && cs.any (fun q => q.1 == 0 || q.1 == 1) && cs.any (fun q => q.1 == 3) &&
    cs.any (fun q => q.1 == 4 || q.1 == 5) && covB el j L [0, 1, 3] cs

end cert

section transport
variable {X : MGraph} {P : Fin X.m → Prop} {C : Cut2 P} {n : Nat} {el : List (Nat × Nat)} {j L x y : Nat}

namespace PoleData

/-- the pole colouring induced by a concrete colouring -/
def φ (D : PoleData C n el j L x y) (cl : List Nat) : Fin X.m → Fin 6 := fun f => colF el.length cl (D.ψ f)

/-- the matching inside `A` induced by a concrete colouring -/
def N (D : PoleData C n el j L x y) (cl : List Nat) : Fin X.m → Prop := fun d => C.inA d ∧ colN cl (D.ψ d).val = 5

theorem φ_val (D : PoleData C n el j L x y) (cl : List Nat) (f : Fin X.m) : (D.φ cl f).val = colN cl (D.ψ f).val := rfl

theorem φ_e1 (D : PoleData C n el j L x y) (cl : List Nat) : (D.φ cl C.e1).val = colN cl j := by
  rw [φ_val, D.he1]

theorem φ_e2 (D : PoleData C n el j L x y) (cl : List Nat) : (D.φ cl C.e2).val = colN cl L := by
  rw [φ_val, D.he2]

theorem star (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hb : fastStar2 (n + 2) el nb cl = true) : StarOn C.pole 6 (D.φ cl) := by
  have hs := star_of_fast2 (hn := (by omega : 0 < n + 2)) hb
  exact starOn_embed (G := X) (H := ofList (n + 2) el (by omega)) D.α D.ψ
    (fun x' y' a b ha hb' hax hby h => D.iso.1 x' y' ⟨a, ha, hax⟩ ⟨b, hb', hby⟩ h) D.iso.2.1
    (fun _ _ => trivial) D.iso.2.2.2 hs

theorem a1_meets : meets P C.a1 := ⟨C.e1, C.P1, joins_inc_left C.j1⟩
theorem a2_meets : meets P C.a2 := ⟨C.e2, C.P2, joins_inc_left C.j2⟩

/-- the colour-`5` edge of the concrete pole at the image of a side-`A` vertex, pulled back -/
theorem five_at (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hb : baseB n el nb cl = true) {w : Fin X.n} (hw : C.S w = true) (hmw : meets P w) :
    ∃ f, C.pole f ∧ colN cl (D.ψ f).val = 5 ∧ X.Inc f w ∧
      ∀ f', C.pole f' → colN cl (D.ψ f').val = 5 → X.Inc f' w → f' = f := by
  unfold baseB at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨hst, hsd⟩, hpm⟩ := hb
  have hst' := hst
  unfold fastStar2 at hst'
  simp only [Bool.and_eq_true] at hst'
  have hmv := C.meets_pole_of_A hw hmw
  obtain ⟨e, he5, hei, heu⟩ := pm_at (hn := by omega) D.hel hst'.1.1.2 hsd hpm (D.α w) (D.hA w hw)
  obtain ⟨f, hf, rfl⟩ := D.iso.2.2.1 e
  refine ⟨f, hf, congrArg Fin.val he5, (D.inc_iff hf hmv).2 hei, fun f' hf' h5 hfw => ?_⟩
  exact D.iso.2.1 _ _ hf' hf (heu _ (Fin.ext h5) ((D.inc_iff hf' hmv).1 hfw))

theorem coverF (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hb : baseB n el nb cl = true) (hj5 : colN cl j ≠ 5) (hL5 : colN cl L ≠ 5) : C.CoverA (D.N cl) False := by
  intro w hw hmw
  refine ⟨fun h => h.1.elim, fun _ => ?_⟩
  obtain ⟨f, hf, h5, hfw, hu⟩ := D.five_at hb hw hmw
  have fA : C.inA f := by
    rcases hf with h | h
    · exact h
    · rcases h with rfl | rfl
      · rw [D.he1] at h5; exact absurd h5 hj5
      · rw [D.he2] at h5; exact absurd h5 hL5
  exact ⟨f, fA, ⟨fA, h5⟩, hfw, fun d hd hNd hdw => hu d (Or.inl hd) hNd.2 hdw⟩

theorem coverM (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hb : baseB n el nb cl = true) (hj5 : colN cl j = 5) (hL5 : colN cl L = 5) : C.CoverA (D.N cl) True := by
  intro w hw hmw
  obtain ⟨f, hf, h5, hfw, hu⟩ := D.five_at hb hw hmw
  refine ⟨fun ⟨_, h12⟩ d hd hNd hdw => ?_, fun h12 => ?_⟩
  · have hdf := hu d (Or.inl hd) hNd.2 hdw
    rcases h12 with rfl | rfl
    · have h1 := hu C.e1 (Or.inr (Or.inl rfl)) (by rw [D.he1]; exact hj5) (joins_inc_left C.j1)
      exact C.not_inA_of_cut (Or.inl rfl) (h1 ▸ hdf ▸ hd)
    · have h2 := hu C.e2 (Or.inr (Or.inr rfl)) (by rw [D.he2]; exact hL5) (joins_inc_left C.j2)
      exact C.not_inA_of_cut (Or.inr rfl) (h2 ▸ hdf ▸ hd)
  · have fA : C.inA f := by
      rcases hf with h | h
      · exact h
      · exfalso
        rcases C.cutA h hfw hw with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact h12 ⟨trivial, Or.inl rfl⟩
        · exact h12 ⟨trivial, Or.inr rfl⟩
    exact ⟨f, fA, ⟨fA, h5⟩, hfw, fun d hd hNd hdw => hu d (Or.inl hd) hNd.2 hdw⟩

theorem certM (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hb : baseB n el nb cl = true) (hj5 : colN cl j = 5) (hL5 : colN cl L = 5) : C.CertM (D.N cl) (D.φ cl) := by
  have hst : fastStar2 (n + 2) el nb cl = true := by unfold baseB at hb; simp only [Bool.and_eq_true] at hb; exact hb.1.1
  refine ⟨D.coverM hb hj5 hL5, D.star hst, fun f hf => ?_⟩
  constructor
  · intro h5
    rcases hf with hA | hc
    · exact Or.inr ⟨hA, hA, by rw [← D.φ_val, h5]; rfl⟩
    · exact Or.inl hc
  · rintro (hc | ⟨_, hN⟩)
    · apply Fin.ext
      rw [D.φ_val]
      rcases hc with rfl | rfl
      · rw [D.he1]; exact hj5
      · rw [D.he2]; exact hL5
    · exact Fin.ext hN.2

theorem certF (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hb : baseB n el nb cl = true) (hj5 : colN cl j ≠ 5) (hL5 : colN cl L ≠ 5) : C.CertF (D.N cl) (D.φ cl) := by
  have hst : fastStar2 (n + 2) el nb cl = true := by unfold baseB at hb; simp only [Bool.and_eq_true] at hb; exact hb.1.1
  refine ⟨D.coverF hb hj5 hL5, D.star hst, fun f hf => ⟨fun h5 => ⟨hf, by rw [← D.φ_val, h5]; rfl⟩,
    fun hN => Fin.ext hN.2⟩, fun h => hj5 ?_, fun h => hL5 ?_⟩
  · rw [← D.φ_e1, h]; rfl
  · rw [← D.φ_e2, h]; rfl

theorem tmeet (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hs : nbSound (n + 2) el nb cl = true) (h : meetB nb j L x y = true) : C.TMeet (D.φ cl) := by
  unfold meetB at h
  obtain ⟨t, ht, h1⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at h1
  obtain ⟨hit, h2⟩ := h1
  obtain ⟨t', ht', h3⟩ := List.any_eq_true.1 h2
  simp only [Bool.and_eq_true] at h3
  obtain ⟨hit', hc⟩ := h3
  unfold insideT at hit hit'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hit hit'
  have ht1 : t ∈ nb.getD (D.α C.a1).val [] := by rw [D.ha1]; exact ht
  have ht2 : t' ∈ nb.getD (D.α C.a2).val [] := by rw [D.ha2]; exact ht'
  obtain ⟨f, fA, hfv, hfa, hfc⟩ := D.entry_inside hs C.sa1 a1_meets ht1
    (fun h => by rw [h] at hit; exact absurd (Nat.beq_refl j) (by rw [hit.1]; decide))
    (fun h => by rw [h] at hit; exact absurd (Nat.beq_refl L) (by rw [hit.2]; decide))
  obtain ⟨f', fA', hfv', hfa', hfc'⟩ := D.entry_inside hs C.sa2 a2_meets ht2
    (fun h => by rw [h] at hit'; exact absurd (Nat.beq_refl j) (by rw [hit'.1]; decide))
    (fun h => by rw [h] at hit'; exact absurd (Nat.beq_refl L) (by rw [hit'.2]; decide))
  refine ⟨D.φ cl f, ⟨f, fA, hfa, rfl⟩, ⟨f', fA', hfa', Fin.ext ?_⟩⟩
  rw [D.φ_val, D.φ_val, hfv, hfv', hfc, hfc', Nat.eq_of_beq_eq_true hc]

theorem tsmall_aux (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) (hs : nbSound (n + 2) el nb cl = true) {u w : Fin X.n}
    (hu : C.S u = true) (hmu : meets P u) (_hw : C.S w = true)
    (h : smallB nb j L (D.α u).val (D.α w).val = true) :
    ∃ κ, C.Pset (D.φ cl) u κ ∧ ¬ C.Pset (D.φ cl) w κ := by
  unfold smallB at h
  obtain ⟨t, ht, h1⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at h1
  obtain ⟨hit, hall⟩ := h1
  unfold insideT at hit
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hit
  obtain ⟨f, fA, hfv, hfa, hfc⟩ := D.entry_inside hs hu hmu ht
    (fun h => by rw [h] at hit; exact absurd (Nat.beq_refl j) (by rw [hit.1]; decide))
    (fun h => by rw [h] at hit; exact absurd (Nat.beq_refl L) (by rw [hit.2]; decide))
  refine ⟨D.φ cl f, ⟨f, fA, hfa, rfl⟩, fun ⟨f', fA', hfw', hc'⟩ => ?_⟩
  obtain ⟨z, hz⟩ := D.entry_of_inside hnb fA' hfw'
  have := List.all_eq_true.1 hall _ hz
  have hin := D.hin f' fA'
  simp only [insideT, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at this
  rcases this with h | h
  · rcases Bool.eq_false_or_eq_true (Nat.beq (D.ψ f').val j) with h1 | h1
    · exact hin.1 (Nat.eq_of_beq_eq_true h1)
    · rcases Bool.eq_false_or_eq_true (Nat.beq (D.ψ f').val L) with h2 | h2
      · exact hin.2 (Nat.eq_of_beq_eq_true h2)
      · simp [h1, h2] at h
  · have hcv : colN cl (D.ψ f').val = t.2.2 := by
      rw [← D.φ_val, hc', D.φ_val, hfv, hfc]
    rw [hcv] at h
    exact absurd (Nat.beq_refl t.2.2) (by rw [h]; decide)

theorem tsmall (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) (hs : nbSound (n + 2) el nb cl = true)
    (h : (smallB nb j L x y || smallB nb j L y x) = true) : C.TSmall (D.φ cl) := by
  intro hall
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have h' : smallB nb j L (D.α C.a1).val (D.α C.a2).val = true := by rw [D.ha1, D.ha2]; exact h
    obtain ⟨κ, h1, h2⟩ := D.tsmall_aux hnb hs C.sa1 a1_meets C.sa2 h'
    exact h2 ((hall κ).1 h1)
  · have h' : smallB nb j L (D.α C.a2).val (D.α C.a1).val = true := by rw [D.ha1, D.ha2]; exact h
    obtain ⟨κ, h1, h2⟩ := D.tsmall_aux hnb hs C.sa2 a2_meets C.sa1 h'
    exact h2 ((hall κ).2 h1)

theorem insideT_true {j L : Nat} {t : Nat × Nat × Nat} (h1 : t.1 ≠ j) (h2 : t.1 ≠ L) : insideT j L t = true := by
  unfold insideT; rw [nbeq_false h1, nbeq_false h2]; rfl

theorem noRung (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) (h : noRungB nb j L x y = true) :
    ∀ r, C.inA r → D.N cl r → ¬ X.Joins r C.a1 C.a2 := by
  intro r hr hN hj12
  have hjr := D.iso.2.2.2 r (Or.inl hr)
  have hj' : D.Y.Joins (D.ψ r) (D.α C.a1) (D.α C.a2) := by
    rcases hj12 with h1 | h1 <;> rw [h1] at hjr
    · exact hjr
    · exact Or.symm hjr
  have hm := mem_nb (hn := by omega) D.hel hnb hj'
  rw [D.ha1, D.ha2] at hm
  have := List.all_eq_true.1 h _ hm
  have hin := D.hin r hr
  dsimp only at this
  rw [insideT_true hin.1 hin.2, Nat.beq_refl, hN.2, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem nc (D : PoleData C n el j L x y) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) {u : Fin X.n} {γ : Nat} (h : ncB nb j L (D.α u).val γ = true) :
    ∀ f, C.inA f → ¬ D.N cl f → X.Inc f u → colN cl (D.ψ f).val ≠ γ := by
  intro f hf hN hfu hc
  obtain ⟨z, hz⟩ := D.entry_of_inside hnb hf hfu
  have := List.all_eq_true.1 h _ hz
  have hin := D.hin f hf
  have h5 : colN cl (D.ψ f).val ≠ 5 := fun h5 => hN ⟨hf, h5⟩
  dsimp only at this
  rw [insideT_true hin.1 hin.2, nbeq_false h5, hc, Nat.beq_refl] at this
  exact absurd this (by decide)

/-- a certificate of type `1` or `2` is `CertM ∧ TMeet`, of type `0` or `1` is `CertM ∧ TSmall` -/
theorem cert_M (D : PoleData C n el j L x y) {q : Nat × List (List (Nat × Nat × Nat)) × List Nat}
    (hq : certB n el j L x y q = true) :
    (q.1 = 1 ∨ q.1 = 2 → C.CertM (D.N q.2.2) (D.φ q.2.2) ∧ C.TMeet (D.φ q.2.2)) ∧
    (q.1 = 0 ∨ q.1 = 1 → C.CertM (D.N q.2.2) (D.φ q.2.2) ∧ C.TSmall (D.φ q.2.2)) := by
  unfold certB at hq
  simp only [Bool.and_eq_true] at hq
  obtain ⟨hb, ht⟩ := hq
  have hb' := hb
  unfold baseB at hb'
  simp only [Bool.and_eq_true] at hb'
  have hst' := hb'.1.1
  unfold fastStar2 at hst'
  simp only [Bool.and_eq_true] at hst'
  have hnb := hst'.1.1.2
  have hs := hb'.1.2
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rcases hc with hc | hc <;> rw [hc] at ht <;> simp only [typeB, Bool.and_eq_true] at ht
    · obtain ⟨⟨⟨h1, h2⟩, _⟩, hm⟩ := ht
      exact ⟨D.certM hb (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2), D.tmeet hs hm⟩
    · obtain ⟨⟨h1, h2⟩, hm⟩ := ht
      exact ⟨D.certM hb (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2), D.tmeet hs hm⟩
  · rcases hc with hc | hc <;> rw [hc] at ht <;> simp only [typeB, Bool.and_eq_true] at ht
    · obtain ⟨⟨h1, h2⟩, hsm⟩ := ht
      exact ⟨D.certM hb (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2), D.tsmall hnb hs hsm⟩
    · obtain ⟨⟨⟨h1, h2⟩, hsm⟩, _⟩ := ht
      exact ⟨D.certM hb (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2), D.tsmall hnb hs hsm⟩

theorem ne_of_nbeq {a b : Nat} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro hab; rw [hab, Nat.beq_refl] at h; exact absurd h (by decide)

/-- certificates of types `3`, `4`, `5` -/
theorem cert_F (D : PoleData C n el j L x y) {q : Nat × List (List (Nat × Nat × Nat)) × List Nat}
    (hq : certB n el j L x y q = true) :
    (q.1 = 3 → C.Feq (D.N q.2.2) (D.φ q.2.2)) ∧ (q.1 = 4 → C.Fnc (D.N q.2.2) (D.φ q.2.2)) ∧
    (q.1 = 4 ∨ q.1 = 5 → C.Fneq (D.N q.2.2) (D.φ q.2.2)) := by
  unfold certB at hq
  simp only [Bool.and_eq_true] at hq
  obtain ⟨hb, ht⟩ := hq
  have hb' := hb
  unfold baseB at hb'
  simp only [Bool.and_eq_true] at hb'
  have hst' := hb'.1.1
  unfold fastStar2 at hst'
  simp only [Bool.and_eq_true] at hst'
  have hnb := hst'.1.1.2
  have e12 : ∀ cl : List Nat, colN cl j ≠ colN cl L → D.φ cl C.e1 ≠ D.φ cl C.e2 := by
    intro cl h he; exact h (by rw [← D.φ_e1, ← D.φ_e2, he])
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · rw [hc] at ht
    simp only [typeB, Bool.and_eq_true] at ht
    obtain ⟨⟨h1, h2⟩, hr⟩ := ht
    have hjL := Nat.eq_of_beq_eq_true h1
    have hj5 := ne_of_nbeq h2
    refine ⟨D.certF hb hj5 (hjL ▸ hj5), Fin.ext ?_, D.noRung hnb hr⟩
    rw [D.φ_e1, D.φ_e2, hjL]
  · rw [hc] at ht
    simp only [typeB, Bool.and_eq_true] at ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    refine ⟨⟨D.certF hb (ne_of_nbeq h1) (ne_of_nbeq h2), e12 _ (ne_of_nbeq h3)⟩, fun f hf hN hfa => ?_,
      fun f hf hN hfa => ?_⟩
    · have h4' : ncB q.2.1 j L (D.α C.a1).val (colN q.2.2 L) = true := by rw [D.ha1]; exact h4
      intro he; exact D.nc hnb h4' f hf hN hfa (by rw [← D.φ_val, he, D.φ_e2])
    · have h5' : ncB q.2.1 j L (D.α C.a2).val (colN q.2.2 j) = true := by rw [D.ha2]; exact h5
      intro he; exact D.nc hnb h5' f hf hN hfa (by rw [← D.φ_val, he, D.φ_e1])
  · rcases hc with hc | hc <;> rw [hc] at ht <;> simp only [typeB, Bool.and_eq_true] at ht
    · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩ := ht
      exact ⟨D.certF hb (ne_of_nbeq h1) (ne_of_nbeq h2), e12 _ (ne_of_nbeq h3)⟩
    · obtain ⟨⟨h1, h2⟩, h3⟩ := ht
      exact ⟨D.certF hb (ne_of_nbeq h1) (ne_of_nbeq h2), e12 _ (ne_of_nbeq h3)⟩

theorem cover_of (D : PoleData C n el j L x y) {cs : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)}
    {codes : List Nat} (hcov : covB el j L codes cs = true) {h : Fin X.m} (hh : C.inA h) (s : Bool) :
    ∃ q ∈ cs, codes.contains q.1 = true ∧ (D.N q.2.2 h ↔ s = true) := by
  have hc := List.all_eq_true.1 hcov (D.ψ h).val (List.mem_range.2 (D.ψ h).isLt)
  have hin := D.hin h hh
  simp only [nbeq_false hin.1, nbeq_false hin.2, Bool.false_or, Bool.and_eq_true] at hc
  cases s
  · obtain ⟨q, hq, hq1⟩ := List.any_eq_true.1 hc.2
    simp only [Bool.and_eq_true] at hq1
    exact ⟨q, hq, hq1.1, ⟨fun hN => absurd hq1.2 (by rw [hN.2, Nat.beq_refl]; decide), fun h => absurd h (by decide)⟩⟩
  · obtain ⟨q, hq, hq1⟩ := List.any_eq_true.1 hc.1
    simp only [Bool.and_eq_true] at hq1
    exact ⟨q, hq, hq1.1, ⟨fun _ => rfl, fun _ => ⟨hh, Nat.eq_of_beq_eq_true hq1.2⟩⟩⟩

theorem recipeD (D : PoleData C n el j L x y) {cs : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)}
    (h : recipeDB n el j L x y cs = true) : C.RecipeD := by
  unfold recipeDB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hall, hM⟩, hF⟩, hcov⟩ := h
  obtain ⟨q1, hq1, hc1⟩ := List.any_eq_true.1 hM
  obtain ⟨q2, hq2, hc2⟩ := List.any_eq_true.1 hF
  simp only [Bool.or_eq_true, beq_iff_eq] at hc1 hc2
  refine ⟨⟨_, _, (D.cert_M (List.all_eq_true.1 hall q1 hq1)).1 hc1⟩,
    ⟨_, _, (D.cert_F (List.all_eq_true.1 hall q2 hq2)).2.1 hc2⟩, fun h hh s => ?_⟩
  obtain ⟨q, hq, hcode, hNs⟩ := D.cover_of hcov hh s
  have hcq := List.all_eq_true.1 hall q hq
  have hm : q.1 ∈ [1, 2, 4] := List.contains_iff_mem.1 hcode
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  refine ⟨D.N q.2.2, D.φ q.2.2, ?_, hNs⟩
  rcases hm with h1 | h2 | h4
  · exact Or.inl ((D.cert_M hcq).1 (Or.inl h1))
  · exact Or.inl ((D.cert_M hcq).1 (Or.inr h2))
  · exact Or.inr ((D.cert_F hcq).2.1 h4)

theorem recipeE (D : PoleData C n el j L x y) {cs : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)}
    (h : recipeEB n el j L x y cs = true) : C.RecipeE := by
  unfold recipeEB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hall, hM⟩, hE⟩, hF⟩, hcov⟩ := h
  obtain ⟨q1, hq1, hc1⟩ := List.any_eq_true.1 hM
  obtain ⟨q2, hq2, hc2⟩ := List.any_eq_true.1 hE
  obtain ⟨q3, hq3, hc3⟩ := List.any_eq_true.1 hF
  simp only [Bool.or_eq_true, beq_iff_eq] at hc1 hc2 hc3
  refine ⟨⟨_, _, (D.cert_M (List.all_eq_true.1 hall q1 hq1)).2 hc1⟩,
    ⟨_, _, (D.cert_F (List.all_eq_true.1 hall q2 hq2)).1 hc2⟩,
    ⟨_, _, (D.cert_F (List.all_eq_true.1 hall q3 hq3)).2.2 hc3⟩, fun h hh s => ?_⟩
  obtain ⟨q, hq, hcode, hNs⟩ := D.cover_of hcov hh s
  have hcq := List.all_eq_true.1 hall q hq
  have hm : q.1 ∈ [0, 1, 3] := List.contains_iff_mem.1 hcode
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  refine ⟨D.N q.2.2, D.φ q.2.2, ?_, hNs⟩
  rcases hm with h0 | h1 | h3
  · exact Or.inl ((D.cert_M hcq).2 (Or.inl h0))
  · exact Or.inl ((D.cert_M hcq).2 (Or.inr h1))
  · exact Or.inr ((D.cert_F hcq).1 h3)

end PoleData

end transport

end RH2F


-- ===== from SF6.lean =====

namespace RH2F
open MGraph
open Classical

section clorec
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the orientation of the image of `g_A` -/
theorem Cut2.orient (C : Cut2 P) {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m}
    (hiso : IsoMap C.clo (ofList n el hn) α β) :
    ∃ o : Bool, (if o then (gE el (β (Fin.last X.m)).val).2 else (gE el (β (Fin.last X.m)).val).1) = (α C.a1).val ∧
      (if o then (gE el (β (Fin.last X.m)).val).1 else (gE el (β (Fin.last X.m)).val).2) = (α C.a2).val := by
  have hj := hiso.2.2.2 _ C.clo_last
  rw [addEdge_ends_new] at hj
  have he := ofList_ends (hn := hn) hel (β (Fin.last X.m))
  rcases hj with h | h <;> rw [h] at he <;> simp only at he
  · exact ⟨false, by simp [he.1], by simp [he.2]⟩
  · exact ⟨true, by simp [he.2], by simp [he.1]⟩

theorem Cut2.poleData_of_clo (C : Cut2 P) {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m}
    (hiso : IsoMap C.clo (ofList n el hn) α β) (o : Bool)
    (ho1 : (if o then (gE el (β (Fin.last X.m)).val).2 else (gE el (β (Fin.last X.m)).val).1) = (α C.a1).val)
    (ho2 : (if o then (gE el (β (Fin.last X.m)).val).1 else (gE el (β (Fin.last X.m)).val).2) = (α C.a2).val) :
    Nonempty (PoleData C n (poleEl el n (β (Fin.last X.m)).val o) (β (Fin.last X.m)).val el.length
      (if o then (gE el (β (Fin.last X.m)).val).2 else (gE el (β (Fin.last X.m)).val).1)
      (if o then (gE el (β (Fin.last X.m)).val).1 else (gE el (β (Fin.last X.m)).val).2)) := by
  obtain ⟨α', ψ, hiso', he1, he2, hin, ha1, ha2, hA, _, _⟩ := C.pole_iso hel hiso o ho1 ho2
  exact ⟨⟨α', ψ, elOK_pole hel (β (Fin.last X.m)).isLt, hiso', he1, he2,
    fun f hf => ⟨(hin f hf).1, Nat.ne_of_lt (hin f hf).2⟩, ha1.trans ho1.symm, ha2.trans ho2.symm,
    fun v hv => by rw [hA v hv]; exact (α v).isLt⟩⟩

/-- recipe D of side `A` from recipe checks of the concrete pole at `j0` in both orientations -/
theorem Cut2.recipeD_of_iso (C : Cut2 P) {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m}
    (hiso : IsoMap C.clo (ofList n el hn) α β) {j0 : Nat} (hj0 : (β (Fin.last X.m)).val = j0)
    {cs0 cs1 : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)}
    (h0 : recipeDB n (poleEl el n j0 false) j0 el.length (gE el j0).1 (gE el j0).2 cs0 = true)
    (h1 : recipeDB n (poleEl el n j0 true) j0 el.length (gE el j0).2 (gE el j0).1 cs1 = true) : C.RecipeD := by
  obtain ⟨o, ho1, ho2⟩ := C.orient hel hiso
  obtain ⟨D⟩ := C.poleData_of_clo hel hiso o ho1 ho2
  revert D
  rw [hj0]
  intro D
  cases o
  · exact D.recipeD h0
  · exact D.recipeD h1

theorem Cut2.recipeE_of_iso (C : Cut2 P) {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m}
    (hiso : IsoMap C.clo (ofList n el hn) α β) {j0 : Nat} (hj0 : (β (Fin.last X.m)).val = j0)
    {cs0 cs1 : List (Nat × List (List (Nat × Nat × Nat)) × List Nat)}
    (h0 : recipeEB n (poleEl el n j0 false) j0 el.length (gE el j0).1 (gE el j0).2 cs0 = true)
    (h1 : recipeEB n (poleEl el n j0 true) j0 el.length (gE el j0).2 (gE el j0).1 cs1 = true) : C.RecipeE := by
  obtain ⟨o, ho1, ho2⟩ := C.orient hel hiso
  obtain ⟨D⟩ := C.poleData_of_clo hel hiso o ho1 ho2
  revert D
  rw [hj0]
  intro D
  cases o
  · exact D.recipeE h0
  · exact D.recipeE h1

end clorec

end RH2F


-- ===== from SF8.lean =====

/-! EX1-full certificates of the representatives (table T5, from TAB-A, fact 22e13cb89bd889df). -/

namespace RH2F
open MGraph

theorem ex1rep_1 : exCert (repN 1) (repL 1) [([[(0, 1, 5), (1, 1, 1), (2, 1, 0)], [(0, 0, 5), (1, 0, 1), (2, 0, 0)]], [5, 1, 0]), ([[(0, 1, 1), (1, 1, 5), (2, 1, 0)], [(0, 0, 1), (1, 0, 5), (2, 0, 0)]], [1, 5, 0]), ([[(0, 1, 1), (1, 1, 0), (2, 1, 5)], [(0, 0, 1), (1, 0, 0), (2, 0, 5)]], [1, 0, 5])] = true := by decide +kernel
theorem ex1rep_2 : exCert (repN 2) (repL 2) [([[(0, 1, 5), (1, 1, 1), (2, 2, 2)], [(0, 0, 5), (1, 0, 1), (5, 3, 0)], [(2, 0, 2), (3, 3, 5), (4, 3, 1)], [(3, 2, 5), (4, 2, 1), (5, 1, 0)]], [5, 1, 2, 5, 1, 0]), ([[(0, 1, 1), (1, 1, 5), (2, 2, 2)], [(0, 0, 1), (1, 0, 5), (5, 3, 0)], [(2, 0, 2), (3, 3, 1), (4, 3, 5)], [(3, 2, 1), (4, 2, 5), (5, 1, 0)]], [1, 5, 2, 1, 5, 0]), ([[(0, 1, 3), (1, 1, 2), (2, 2, 5)], [(0, 0, 3), (1, 0, 2), (5, 3, 5)], [(2, 0, 5), (3, 3, 1), (4, 3, 0)], [(3, 2, 1), (4, 2, 0), (5, 1, 5)]], [3, 2, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_3 : exCert (repN 3) (repL 3) [([[(0, 1, 5), (3, 2, 1), (5, 3, 0)], [(0, 0, 5), (1, 2, 3), (2, 3, 2)], [(1, 1, 3), (3, 0, 1), (4, 3, 5)], [(2, 1, 2), (4, 2, 5), (5, 0, 0)]], [5, 3, 2, 1, 5, 0]), ([[(0, 1, 3), (3, 2, 5), (5, 3, 0)], [(0, 0, 3), (1, 2, 2), (2, 3, 5)], [(1, 1, 2), (3, 0, 5), (4, 3, 1)], [(2, 1, 5), (4, 2, 1), (5, 0, 0)]], [3, 2, 5, 5, 1, 0]), ([[(0, 1, 3), (3, 2, 1), (5, 3, 5)], [(0, 0, 3), (1, 2, 5), (2, 3, 2)], [(1, 1, 5), (3, 0, 1), (4, 3, 0)], [(2, 1, 2), (4, 2, 0), (5, 0, 5)]], [3, 5, 2, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_5 : exCert (repN 5) (repL 5) [([[(0, 1, 5), (1, 2, 3), (5, 4, 2)], [(0, 0, 5), (4, 3, 1), (8, 5, 0)], [(1, 0, 3), (2, 3, 5), (3, 3, 2)], [(2, 2, 5), (3, 2, 2), (4, 1, 1)], [(5, 0, 2), (6, 5, 5), (7, 5, 1)], [(6, 4, 5), (7, 4, 1), (8, 1, 0)]], [5, 3, 5, 2, 1, 2, 5, 1, 0]), ([[(0, 1, 4), (1, 2, 5), (5, 4, 2)], [(0, 0, 4), (4, 3, 5), (8, 5, 0)], [(1, 0, 5), (2, 3, 3), (3, 3, 1)], [(2, 2, 3), (3, 2, 1), (4, 1, 5)], [(5, 0, 2), (6, 5, 1), (7, 5, 5)], [(6, 4, 1), (7, 4, 5), (8, 1, 0)]], [4, 5, 3, 1, 5, 2, 1, 5, 0]), ([[(0, 1, 4), (1, 2, 3), (5, 4, 5)], [(0, 0, 4), (4, 3, 2), (8, 5, 5)], [(1, 0, 3), (2, 3, 0), (3, 3, 5)], [(2, 2, 0), (3, 2, 5), (4, 1, 2)], [(5, 0, 5), (6, 5, 1), (7, 5, 0)], [(6, 4, 1), (7, 4, 0), (8, 1, 5)]], [4, 3, 0, 5, 2, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_9 : exCert (repN 9) (repL 9) [([[(0, 1, 5), (4, 4, 3), (8, 6, 2)], [(0, 0, 5), (3, 3, 1), (11, 7, 0)], [(1, 3, 5), (2, 3, 2), (7, 5, 0)], [(1, 2, 5), (2, 2, 2), (3, 1, 1)], [(4, 0, 3), (5, 5, 5), (6, 5, 1)], [(5, 4, 5), (6, 4, 1), (7, 2, 0)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [5, 5, 2, 1, 3, 5, 1, 0, 2, 5, 1, 0]), ([[(0, 1, 4), (4, 4, 5), (8, 6, 2)], [(0, 0, 4), (3, 3, 5), (11, 7, 0)], [(1, 3, 3), (2, 3, 2), (7, 5, 5)], [(1, 2, 3), (2, 2, 2), (3, 1, 5)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 2, 5)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 1, 0)]], [4, 3, 2, 5, 5, 1, 0, 5, 2, 1, 5, 0]), ([[(0, 1, 3), (4, 4, 2), (8, 6, 5)], [(0, 0, 3), (3, 3, 2), (11, 7, 5)], [(1, 3, 1), (2, 3, 5), (7, 5, 0)], [(1, 2, 1), (2, 2, 5), (3, 1, 2)], [(4, 0, 2), (5, 5, 1), (6, 5, 5)], [(5, 4, 1), (6, 4, 5), (7, 2, 0)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 1, 5)]], [3, 1, 5, 2, 2, 1, 5, 0, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_10 : exCert (repN 10) (repL 10) [([[(0, 1, 5), (1, 1, 1), (4, 4, 2)], [(0, 0, 5), (1, 0, 1), (11, 7, 0)], [(2, 3, 5), (3, 3, 1), (7, 5, 0)], [(2, 2, 5), (3, 2, 1), (8, 6, 2)], [(4, 0, 2), (5, 5, 5), (6, 5, 1)], [(5, 4, 5), (6, 4, 1), (7, 2, 0)], [(8, 3, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [5, 1, 5, 1, 2, 5, 1, 0, 2, 5, 1, 0]), ([[(0, 1, 1), (1, 1, 5), (4, 4, 2)], [(0, 0, 1), (1, 0, 5), (11, 7, 0)], [(2, 3, 1), (3, 3, 5), (7, 5, 0)], [(2, 2, 1), (3, 2, 5), (8, 6, 2)], [(4, 0, 2), (5, 5, 1), (6, 5, 5)], [(5, 4, 1), (6, 4, 5), (7, 2, 0)], [(8, 3, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 1, 0)]], [1, 5, 1, 5, 2, 1, 5, 0, 2, 1, 5, 0]), ([[(0, 1, 3), (1, 1, 2), (4, 4, 5)], [(0, 0, 3), (1, 0, 2), (11, 7, 5)], [(2, 3, 3), (3, 3, 2), (7, 5, 5)], [(2, 2, 3), (3, 2, 2), (8, 6, 5)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 2, 5)], [(8, 3, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 1, 5)]], [3, 2, 3, 2, 5, 1, 0, 5, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_11 : exCert (repN 11) (repL 11) [([[(0, 2, 5), (4, 4, 0), (8, 6, 2)], [(3, 3, 5), (7, 5, 1), (11, 7, 0)], [(0, 0, 5), (1, 3, 4), (2, 3, 3)], [(1, 2, 4), (2, 2, 3), (3, 1, 5)], [(4, 0, 0), (5, 5, 5), (6, 5, 2)], [(5, 4, 5), (6, 4, 2), (7, 1, 1)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [5, 4, 3, 5, 0, 5, 2, 1, 2, 5, 1, 0]), ([[(0, 2, 4), (4, 4, 5), (8, 6, 2)], [(3, 3, 2), (7, 5, 5), (11, 7, 0)], [(0, 0, 4), (1, 3, 5), (2, 3, 0)], [(1, 2, 5), (2, 2, 0), (3, 1, 2)], [(4, 0, 5), (5, 5, 3), (6, 5, 1)], [(5, 4, 3), (6, 4, 1), (7, 1, 5)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 1, 0)]], [4, 5, 0, 2, 5, 3, 1, 5, 2, 1, 5, 0]), ([[(0, 2, 2), (4, 4, 3), (8, 6, 5)], [(3, 3, 3), (7, 5, 2), (11, 7, 5)], [(0, 0, 2), (1, 3, 0), (2, 3, 5)], [(1, 2, 0), (2, 2, 5), (3, 1, 3)], [(4, 0, 3), (5, 5, 0), (6, 5, 5)], [(5, 4, 0), (6, 4, 5), (7, 1, 2)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 1, 5)]], [2, 0, 5, 3, 3, 0, 5, 2, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_12 : exCert (repN 12) (repL 12) [([[(0, 1, 5), (4, 4, 3), (8, 6, 2)], [(0, 0, 5), (3, 3, 1), (7, 5, 0)], [(1, 3, 5), (2, 3, 2), (11, 7, 0)], [(1, 2, 5), (2, 2, 2), (3, 1, 1)], [(4, 0, 3), (5, 5, 5), (6, 5, 1)], [(5, 4, 5), (6, 4, 1), (7, 1, 0)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 2, 0)]], [5, 5, 2, 1, 3, 5, 1, 0, 2, 5, 1, 0]), ([[(0, 1, 3), (4, 4, 5), (8, 6, 2)], [(0, 0, 3), (3, 3, 2), (7, 5, 5)], [(1, 3, 1), (2, 3, 5), (11, 7, 0)], [(1, 2, 1), (2, 2, 5), (3, 1, 2)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 1, 5)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 2, 0)]], [3, 1, 5, 2, 5, 1, 0, 5, 2, 1, 5, 0]), ([[(0, 1, 4), (4, 4, 2), (8, 6, 5)], [(0, 0, 4), (3, 3, 5), (7, 5, 0)], [(1, 3, 3), (2, 3, 2), (11, 7, 5)], [(1, 2, 3), (2, 2, 2), (3, 1, 5)], [(4, 0, 2), (5, 5, 1), (6, 5, 5)], [(5, 4, 1), (6, 4, 5), (7, 1, 0)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 2, 5)]], [4, 3, 2, 5, 2, 1, 5, 0, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_13 : exCert (repN 13) (repL 13) [([[(0, 1, 5), (1, 2, 4), (4, 4, 2)], [(0, 0, 5), (3, 3, 3), (7, 5, 0)], [(1, 0, 4), (2, 3, 5), (8, 6, 2)], [(2, 2, 5), (3, 1, 3), (11, 7, 0)], [(4, 0, 2), (5, 5, 5), (6, 5, 1)], [(5, 4, 5), (6, 4, 1), (7, 1, 0)], [(8, 2, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 3, 0)]], [5, 4, 5, 3, 2, 5, 1, 0, 2, 5, 1, 0]), ([[(0, 1, 3), (1, 2, 5), (4, 4, 0)], [(0, 0, 3), (3, 3, 5), (7, 5, 1)], [(1, 0, 5), (2, 3, 4), (8, 6, 2)], [(2, 2, 4), (3, 1, 5), (11, 7, 0)], [(4, 0, 0), (5, 5, 2), (6, 5, 5)], [(5, 4, 2), (6, 4, 5), (7, 1, 1)], [(8, 2, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 3, 0)]], [3, 5, 4, 5, 0, 2, 5, 1, 2, 1, 5, 0]), ([[(0, 1, 4), (1, 2, 2), (4, 4, 5)], [(0, 0, 4), (3, 3, 2), (7, 5, 5)], [(1, 0, 2), (2, 3, 3), (8, 6, 5)], [(2, 2, 3), (3, 1, 2), (11, 7, 5)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 1, 5)], [(8, 2, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 3, 5)]], [4, 2, 3, 2, 5, 1, 0, 5, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_14 : exCert (repN 14) (repL 14) [([[(2, 2, 5), (4, 3, 0), (8, 6, 2)], [(0, 2, 4), (1, 3, 5), (7, 5, 1)], [(0, 1, 4), (2, 0, 5), (3, 3, 3)], [(1, 1, 5), (3, 2, 3), (4, 0, 0)], [(5, 5, 5), (6, 5, 2), (11, 7, 0)], [(5, 4, 5), (6, 4, 2), (7, 1, 1)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 4, 0)]], [4, 5, 5, 3, 0, 5, 2, 1, 2, 5, 1, 0]), ([[(2, 2, 3), (4, 3, 5), (8, 6, 2)], [(0, 2, 5), (1, 3, 4), (7, 5, 1)], [(0, 1, 5), (2, 0, 3), (3, 3, 0)], [(1, 1, 4), (3, 2, 0), (4, 0, 5)], [(5, 5, 2), (6, 5, 5), (11, 7, 0)], [(5, 4, 2), (6, 4, 5), (7, 1, 1)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 4, 0)]], [5, 4, 3, 0, 5, 2, 5, 1, 2, 1, 5, 0]), ([[(2, 2, 3), (4, 3, 2), (8, 6, 5)], [(0, 2, 1), (1, 3, 0), (7, 5, 5)], [(0, 1, 1), (2, 0, 3), (3, 3, 5)], [(1, 1, 0), (3, 2, 5), (4, 0, 2)], [(5, 5, 3), (6, 5, 2), (11, 7, 5)], [(5, 4, 3), (6, 4, 2), (7, 1, 5)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 4, 5)]], [1, 0, 3, 5, 2, 3, 2, 5, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_15 : exCert (repN 15) (repL 15) [([[(2, 2, 5), (4, 3, 0), (5, 4, 3)], [(0, 2, 4), (1, 3, 5), (7, 5, 1)], [(0, 1, 4), (2, 0, 5), (3, 3, 2)], [(1, 1, 5), (3, 2, 2), (4, 0, 0)], [(5, 0, 3), (6, 5, 5), (8, 6, 2)], [(6, 4, 5), (7, 1, 1), (11, 7, 0)], [(8, 4, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 5, 0)]], [4, 5, 5, 2, 0, 3, 5, 1, 2, 5, 1, 0]), ([[(2, 2, 1), (4, 3, 5), (5, 4, 2)], [(0, 2, 5), (1, 3, 4), (7, 5, 2)], [(0, 1, 5), (2, 0, 1), (3, 3, 0)], [(1, 1, 4), (3, 2, 0), (4, 0, 5)], [(5, 0, 2), (6, 5, 3), (8, 6, 5)], [(6, 4, 3), (7, 1, 2), (11, 7, 5)], [(8, 4, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 5, 5)]], [5, 4, 1, 0, 5, 2, 3, 2, 5, 1, 0, 5]), ([[(2, 2, 3), (4, 3, 0), (5, 4, 5)], [(0, 2, 4), (1, 3, 2), (7, 5, 5)], [(0, 1, 4), (2, 0, 3), (3, 3, 5)], [(1, 1, 2), (3, 2, 5), (4, 0, 0)], [(5, 0, 5), (6, 5, 1), (8, 6, 2)], [(6, 4, 1), (7, 1, 5), (11, 7, 0)], [(8, 4, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 5, 0)]], [4, 2, 3, 5, 0, 5, 1, 5, 2, 1, 5, 0])] = true := by decide +kernel
theorem ex1rep_16 : exCert (repN 16) (repL 16) [([[(2, 2, 5), (3, 3, 3), (4, 4, 0)], [(0, 2, 4), (1, 3, 5), (7, 5, 1)], [(0, 1, 4), (2, 0, 5), (8, 6, 2)], [(1, 1, 5), (3, 0, 3), (11, 7, 0)], [(4, 0, 0), (5, 5, 5), (6, 5, 2)], [(5, 4, 5), (6, 4, 2), (7, 1, 1)], [(8, 2, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 3, 0)]], [4, 5, 5, 3, 0, 5, 2, 1, 2, 5, 1, 0]), ([[(2, 2, 3), (3, 3, 5), (4, 4, 2)], [(0, 2, 5), (1, 3, 4), (7, 5, 0)], [(0, 1, 5), (2, 0, 3), (8, 6, 2)], [(1, 1, 4), (3, 0, 5), (11, 7, 0)], [(4, 0, 2), (5, 5, 1), (6, 5, 5)], [(5, 4, 1), (6, 4, 5), (7, 1, 0)], [(8, 2, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 3, 0)]], [5, 4, 3, 5, 2, 1, 5, 0, 2, 1, 5, 0]), ([[(2, 2, 3), (3, 3, 2), (4, 4, 5)], [(0, 2, 4), (1, 3, 3), (7, 5, 5)], [(0, 1, 4), (2, 0, 3), (8, 6, 5)], [(1, 1, 3), (3, 0, 2), (11, 7, 5)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 1, 5)], [(8, 2, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 3, 5)]], [4, 3, 3, 2, 5, 1, 0, 5, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_17 : exCert (repN 17) (repL 17) [([[(3, 3, 5), (4, 4, 0), (8, 6, 2)], [(0, 2, 5), (1, 3, 4), (7, 5, 1)], [(0, 1, 5), (2, 3, 3), (11, 7, 0)], [(1, 1, 4), (2, 2, 3), (3, 0, 5)], [(4, 0, 0), (5, 5, 5), (6, 5, 2)], [(5, 4, 5), (6, 4, 2), (7, 1, 1)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 2, 0)]], [5, 4, 3, 5, 0, 5, 2, 1, 2, 5, 1, 0]), ([[(3, 3, 3), (4, 4, 5), (8, 6, 2)], [(0, 2, 4), (1, 3, 2), (7, 5, 5)], [(0, 1, 4), (2, 3, 5), (11, 7, 0)], [(1, 1, 2), (2, 2, 5), (3, 0, 3)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 1, 5)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 2, 0)]], [4, 2, 5, 3, 5, 1, 0, 5, 2, 1, 5, 0]), ([[(3, 3, 3), (4, 4, 2), (8, 6, 5)], [(0, 2, 4), (1, 3, 5), (7, 5, 0)], [(0, 1, 4), (2, 3, 2), (11, 7, 5)], [(1, 1, 5), (2, 2, 2), (3, 0, 3)], [(4, 0, 2), (5, 5, 1), (6, 5, 5)], [(5, 4, 1), (6, 4, 5), (7, 1, 0)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 2, 5)]], [4, 5, 2, 3, 2, 1, 5, 0, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_18 : exCert (repN 18) (repL 18) [([[(2, 2, 5), (4, 3, 0), (5, 4, 2)], [(0, 2, 3), (1, 3, 5), (8, 5, 2)], [(0, 1, 3), (2, 0, 5), (3, 3, 1)], [(1, 1, 5), (3, 2, 1), (4, 0, 0)], [(5, 0, 2), (9, 6, 5), (11, 7, 0)], [(6, 6, 3), (7, 7, 5), (8, 1, 2)], [(6, 5, 3), (9, 4, 5), (10, 7, 1)], [(7, 5, 5), (10, 6, 1), (11, 4, 0)]], [3, 5, 5, 1, 0, 2, 3, 5, 2, 5, 1, 0]), ([[(2, 2, 1), (4, 3, 5), (5, 4, 2)], [(0, 2, 5), (1, 3, 3), (8, 5, 2)], [(0, 1, 5), (2, 0, 1), (3, 3, 0)], [(1, 1, 3), (3, 2, 0), (4, 0, 5)], [(5, 0, 2), (9, 6, 1), (11, 7, 5)], [(6, 6, 5), (7, 7, 3), (8, 1, 2)], [(6, 5, 5), (9, 4, 1), (10, 7, 0)], [(7, 5, 3), (10, 6, 0), (11, 4, 5)]], [5, 3, 1, 0, 5, 2, 5, 3, 2, 1, 0, 5]), ([[(2, 2, 3), (4, 3, 2), (5, 4, 5)], [(0, 2, 1), (1, 3, 0), (8, 5, 5)], [(0, 1, 1), (2, 0, 3), (3, 3, 5)], [(1, 1, 0), (3, 2, 5), (4, 0, 2)], [(5, 0, 5), (9, 6, 1), (11, 7, 0)], [(6, 6, 3), (7, 7, 2), (8, 1, 5)], [(6, 5, 3), (9, 4, 1), (10, 7, 5)], [(7, 5, 2), (10, 6, 5), (11, 4, 0)]], [1, 0, 3, 5, 2, 5, 3, 2, 5, 1, 5, 0])] = true := by decide +kernel
theorem ex1rep_19 : exCert (repN 19) (repL 19) [([[(0, 1, 5), (5, 4, 3), (7, 5, 1)], [(0, 0, 5), (1, 3, 2), (11, 7, 0)], [(2, 4, 5), (3, 3, 4), (8, 6, 2)], [(1, 1, 2), (3, 2, 4), (4, 5, 5)], [(2, 2, 5), (5, 0, 3), (6, 5, 0)], [(4, 3, 5), (6, 4, 0), (7, 0, 1)], [(8, 2, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [5, 2, 5, 4, 5, 3, 0, 1, 2, 5, 1, 0]), ([[(0, 1, 5), (5, 4, 2), (7, 5, 1)], [(0, 0, 5), (1, 3, 4), (11, 7, 0)], [(2, 4, 3), (3, 3, 5), (8, 6, 2)], [(1, 1, 4), (3, 2, 5), (4, 5, 0)], [(2, 2, 3), (5, 0, 2), (6, 5, 5)], [(4, 3, 0), (6, 4, 5), (7, 0, 1)], [(8, 2, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 1, 0)]], [5, 4, 3, 5, 0, 2, 5, 1, 2, 1, 5, 0]), ([[(0, 1, 4), (5, 4, 5), (7, 5, 0)], [(0, 0, 4), (1, 3, 3), (11, 7, 5)], [(2, 4, 3), (3, 3, 2), (8, 6, 5)], [(1, 1, 3), (3, 2, 2), (4, 5, 5)], [(2, 2, 3), (5, 0, 5), (6, 5, 1)], [(4, 3, 5), (6, 4, 1), (7, 0, 0)], [(8, 2, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 1, 5)]], [4, 3, 3, 2, 5, 5, 1, 0, 5, 1, 0, 5]), ([[(0, 1, 4), (5, 4, 1), (7, 5, 5)], [(0, 0, 4), (1, 3, 5), (11, 7, 0)], [(2, 4, 5), (3, 3, 3), (8, 6, 2)], [(1, 1, 5), (3, 2, 3), (4, 5, 2)], [(2, 2, 5), (5, 0, 1), (6, 5, 0)], [(4, 3, 2), (6, 4, 0), (7, 0, 5)], [(8, 2, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [4, 5, 5, 3, 2, 1, 0, 5, 2, 5, 1, 0])] = true := by decide +kernel
theorem ex1rep_20 : exCert (repN 20) (repL 20) [([[(5, 4, 5), (7, 5, 0), (8, 6, 2)], [(0, 2, 5), (1, 3, 4), (11, 7, 0)], [(0, 1, 5), (2, 4, 3), (3, 3, 2)], [(1, 1, 4), (3, 2, 2), (4, 5, 5)], [(2, 2, 3), (5, 0, 5), (6, 5, 1)], [(4, 3, 5), (6, 4, 1), (7, 0, 0)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [5, 4, 3, 2, 5, 5, 1, 0, 2, 5, 1, 0]), ([[(5, 4, 1), (7, 5, 5), (8, 6, 2)], [(0, 2, 4), (1, 3, 5), (11, 7, 0)], [(0, 1, 4), (2, 4, 5), (3, 3, 2)], [(1, 1, 5), (3, 2, 2), (4, 5, 3)], [(2, 2, 5), (5, 0, 1), (6, 5, 0)], [(4, 3, 3), (6, 4, 0), (7, 0, 5)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 1, 0)]], [4, 5, 5, 2, 3, 1, 0, 5, 2, 1, 5, 0]), ([[(5, 4, 3), (7, 5, 2), (8, 6, 5)], [(0, 2, 3), (1, 3, 2), (11, 7, 5)], [(0, 1, 3), (2, 4, 1), (3, 3, 5)], [(1, 1, 2), (3, 2, 5), (4, 5, 0)], [(2, 2, 1), (5, 0, 3), (6, 5, 5)], [(4, 3, 0), (6, 4, 5), (7, 0, 2)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 1, 5)]], [3, 2, 1, 5, 0, 3, 5, 2, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_21 : exCert (repN 21) (repL 21) [([[(0, 1, 5), (9, 6, 1), (11, 7, 0)], [(0, 0, 5), (1, 2, 2), (2, 3, 3)], [(1, 1, 2), (3, 4, 5), (4, 3, 1)], [(2, 1, 3), (4, 2, 1), (5, 5, 5)], [(3, 2, 5), (6, 6, 3), (7, 5, 0)], [(5, 3, 5), (7, 4, 0), (8, 7, 2)], [(6, 4, 3), (9, 0, 1), (10, 7, 5)], [(8, 5, 2), (10, 6, 5), (11, 0, 0)]], [5, 2, 3, 5, 1, 5, 3, 0, 2, 1, 5, 0]), ([[(0, 1, 5), (9, 6, 2), (11, 7, 0)], [(0, 0, 5), (1, 2, 3), (2, 3, 1)], [(1, 1, 3), (3, 4, 0), (4, 3, 5)], [(2, 1, 1), (4, 2, 5), (5, 5, 2)], [(3, 2, 0), (6, 6, 5), (7, 5, 3)], [(5, 3, 2), (7, 4, 3), (8, 7, 5)], [(6, 4, 5), (9, 0, 2), (10, 7, 1)], [(8, 5, 5), (10, 6, 1), (11, 0, 0)]], [5, 3, 1, 0, 5, 2, 5, 3, 5, 2, 1, 0]), ([[(0, 1, 2), (9, 6, 5), (11, 7, 0)], [(0, 0, 2), (1, 2, 1), (2, 3, 5)], [(1, 1, 1), (3, 4, 5), (4, 3, 0)], [(2, 1, 5), (4, 2, 0), (5, 5, 3)], [(3, 2, 5), (6, 6, 3), (7, 5, 2)], [(5, 3, 3), (7, 4, 2), (8, 7, 5)], [(6, 4, 3), (9, 0, 5), (10, 7, 1)], [(8, 5, 5), (10, 6, 1), (11, 0, 0)]], [2, 1, 5, 5, 0, 3, 3, 2, 5, 5, 1, 0]), ([[(0, 1, 3), (9, 6, 1), (11, 7, 5)], [(0, 0, 3), (1, 2, 5), (2, 3, 1)], [(1, 1, 5), (3, 4, 2), (4, 3, 0)], [(2, 1, 1), (4, 2, 0), (5, 5, 5)], [(3, 2, 2), (6, 6, 5), (7, 5, 3)], [(5, 3, 5), (7, 4, 3), (8, 7, 2)], [(6, 4, 5), (9, 0, 1), (10, 7, 0)], [(8, 5, 2), (10, 6, 0), (11, 0, 5)]], [3, 5, 1, 2, 0, 5, 5, 3, 2, 1, 0, 5]), ([[(0, 1, 5), (9, 6, 1), (11, 7, 0)], [(0, 0, 5), (1, 2, 2), (2, 3, 3)], [(1, 1, 2), (3, 4, 1), (4, 3, 5)], [(2, 1, 3), (4, 2, 5), (5, 5, 0)], [(3, 2, 1), (6, 6, 3), (7, 5, 5)], [(5, 3, 0), (7, 4, 5), (8, 7, 2)], [(6, 4, 3), (9, 0, 1), (10, 7, 5)], [(8, 5, 2), (10, 6, 5), (11, 0, 0)]], [5, 2, 3, 1, 5, 0, 3, 5, 2, 1, 5, 0])] = true := by decide +kernel
theorem ex1rep_22 : exCert (repN 22) (repL 22) [([[(0, 4, 5), (1, 5, 4), (8, 6, 2)], [(2, 3, 5), (3, 4, 3), (4, 5, 1)], [(5, 3, 2), (6, 4, 0), (7, 5, 5)], [(2, 1, 5), (5, 2, 2), (11, 7, 0)], [(0, 0, 5), (3, 1, 3), (6, 2, 0)], [(1, 0, 4), (4, 1, 1), (7, 2, 5)], [(8, 0, 2), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 3, 0)]], [5, 4, 5, 3, 1, 2, 0, 5, 2, 5, 1, 0]), ([[(0, 4, 4), (1, 5, 5), (8, 6, 2)], [(2, 3, 3), (3, 4, 5), (4, 5, 0)], [(5, 3, 5), (6, 4, 2), (7, 5, 1)], [(2, 1, 3), (5, 2, 5), (11, 7, 0)], [(0, 0, 4), (3, 1, 5), (6, 2, 2)], [(1, 0, 5), (4, 1, 0), (7, 2, 1)], [(8, 0, 2), (9, 7, 1), (10, 7, 5)], [(9, 6, 1), (10, 6, 5), (11, 3, 0)]], [4, 5, 3, 5, 0, 5, 2, 1, 2, 1, 5, 0]), ([[(0, 4, 3), (1, 5, 2), (8, 6, 5)], [(2, 3, 3), (3, 4, 1), (4, 5, 5)], [(5, 3, 2), (6, 4, 5), (7, 5, 0)], [(2, 1, 3), (5, 2, 2), (11, 7, 5)], [(0, 0, 3), (3, 1, 1), (6, 2, 5)], [(1, 0, 2), (4, 1, 5), (7, 2, 0)], [(8, 0, 5), (9, 7, 1), (10, 7, 0)], [(9, 6, 1), (10, 6, 0), (11, 3, 5)]], [3, 2, 3, 1, 5, 2, 5, 0, 5, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_23 : exCert (repN 23) (repL 23) [([[(0, 3, 5), (9, 6, 1), (11, 7, 0)], [(3, 3, 3), (4, 4, 5), (5, 5, 1)], [(6, 3, 2), (7, 4, 0), (8, 5, 5)], [(0, 0, 5), (3, 1, 3), (6, 2, 2)], [(1, 6, 2), (4, 1, 5), (7, 2, 0)], [(2, 7, 3), (5, 1, 1), (8, 2, 5)], [(1, 4, 2), (9, 0, 1), (10, 7, 5)], [(2, 5, 3), (10, 6, 5), (11, 0, 0)]], [5, 2, 3, 3, 5, 1, 2, 0, 5, 1, 5, 0]), ([[(0, 3, 3), (9, 6, 5), (11, 7, 0)], [(3, 3, 5), (4, 4, 0), (5, 5, 4)], [(6, 3, 1), (7, 4, 5), (8, 5, 2)], [(0, 0, 3), (3, 1, 5), (6, 2, 1)], [(1, 6, 4), (4, 1, 0), (7, 2, 5)], [(2, 7, 5), (5, 1, 4), (8, 2, 2)], [(1, 4, 4), (9, 0, 5), (10, 7, 1)], [(2, 5, 5), (10, 6, 1), (11, 0, 0)]], [3, 4, 5, 5, 0, 4, 1, 5, 2, 5, 1, 0]), ([[(0, 3, 3), (9, 6, 1), (11, 7, 5)], [(3, 3, 0), (4, 4, 3), (5, 5, 5)], [(6, 3, 5), (7, 4, 4), (8, 5, 1)], [(0, 0, 3), (3, 1, 0), (6, 2, 5)], [(1, 6, 5), (4, 1, 3), (7, 2, 4)], [(2, 7, 2), (5, 1, 5), (8, 2, 1)], [(1, 4, 5), (9, 0, 1), (10, 7, 0)], [(2, 5, 2), (10, 6, 0), (11, 0, 5)]], [3, 5, 2, 0, 3, 5, 5, 4, 1, 1, 0, 5])] = true := by decide +kernel
theorem ex1rep_24 : exCert (repN 24) (repL 24) [([[(0, 1, 5), (1, 2, 2), (2, 3, 3)], [(0, 0, 5), (6, 6, 1), (7, 7, 0)], [(1, 0, 2), (8, 5, 5), (9, 7, 1)], [(2, 0, 3), (10, 5, 0), (11, 6, 5)], [(3, 5, 3), (4, 6, 2), (5, 7, 5)], [(3, 4, 3), (8, 2, 5), (10, 3, 0)], [(4, 4, 2), (6, 1, 1), (11, 3, 5)], [(5, 4, 5), (7, 1, 0), (9, 2, 1)]], [5, 2, 3, 3, 2, 5, 1, 0, 5, 1, 0, 5]), ([[(0, 1, 3), (1, 2, 5), (2, 3, 2)], [(0, 0, 3), (6, 6, 1), (7, 7, 5)], [(1, 0, 5), (8, 5, 1), (9, 7, 0)], [(2, 0, 2), (10, 5, 5), (11, 6, 0)], [(3, 5, 3), (4, 6, 5), (5, 7, 2)], [(3, 4, 3), (8, 2, 1), (10, 3, 5)], [(4, 4, 5), (6, 1, 1), (11, 3, 0)], [(5, 4, 2), (7, 1, 5), (9, 2, 0)]], [3, 5, 2, 3, 5, 2, 1, 5, 1, 0, 5, 0]), ([[(0, 1, 2), (1, 2, 3), (2, 3, 5)], [(0, 0, 2), (6, 6, 5), (7, 7, 1)], [(1, 0, 3), (8, 5, 0), (9, 7, 5)], [(2, 0, 5), (10, 5, 1), (11, 6, 0)], [(3, 5, 5), (4, 6, 3), (5, 7, 2)], [(3, 4, 5), (8, 2, 0), (10, 3, 1)], [(4, 4, 3), (6, 1, 5), (11, 3, 0)], [(5, 4, 2), (7, 1, 1), (9, 2, 5)]], [2, 3, 5, 5, 3, 2, 5, 1, 0, 5, 1, 0])] = true := by decide +kernel

end RH2F


namespace RH2F
open MGraph

/-- **Layer 7 of the Lean formalization of RH2**: transport of EX1-goodness along isomorphisms from EX1-full concrete
    multigraphs, the EX1-full representatives of table T5 (TAB-A, fact 22e13cb89bd889df), and recipes D and E of a
    side from concrete recipe checks of the 2-pole at the image of `g_A` (both orientations). -/
theorem layer7 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (H : MGraph), IsoFrom P H → EX1FullH H → EX1On P) ∧
    (∀ k, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ (9 ≤ k ∧ k ≤ 24)) →
      ∃ cs, exCert (repN k) (repL k) cs = true) ∧
    (∀ (n : Nat) (el : List (Nat × Nat)) (hn : 0 < n) (cs : List (List (List (Nat × Nat × Nat)) × List Nat)),
      exCert n el cs = true → EX1FullH (ofList n el hn)) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P) (n : Nat) (el : List (Nat × Nat)) (hn : 0 < n)
      (α : Fin X.n → Fin (ofList n el hn).n) (β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m),
      elOK n el = true → IsoMap C.clo (ofList n el hn) α β → ∀ j0, (β (Fin.last X.m)).val = j0 →
      ∀ cs0 cs1 : List (Nat × List (List (Nat × Nat × Nat)) × List Nat),
      recipeDB n (poleEl el n j0 false) j0 el.length (gE el j0).1 (gE el j0).2 cs0 = true →
      recipeDB n (poleEl el n j0 true) j0 el.length (gE el j0).2 (gE el j0).1 cs1 = true → C.RecipeD) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P) (n : Nat) (el : List (Nat × Nat)) (hn : 0 < n)
      (α : Fin X.n → Fin (ofList n el hn).n) (β : Fin (addEdge X C.a1 C.a2).m → Fin (ofList n el hn).m),
      elOK n el = true → IsoMap C.clo (ofList n el hn) α β → ∀ j0, (β (Fin.last X.m)).val = j0 →
      ∀ cs0 cs1 : List (Nat × List (List (Nat × Nat × Nat)) × List Nat),
      recipeEB n (poleEl el n j0 false) j0 el.length (gE el j0).1 (gE el j0).2 cs0 = true →
      recipeEB n (poleEl el n j0 true) j0 el.length (gE el j0).2 (gE el j0).1 cs1 = true → C.RecipeE) := by
  refine ⟨fun _ _ _ h hH => ex1On_of_iso h hH, fun k hk => ?_, fun _ _ hn _ h => ex1Full_of_cert (hn := hn) h,
    fun _ _ C _ _ _ _ _ hel hiso _ hj _ _ h0 h1 => C.recipeD_of_iso hel hiso hj h0 h1,
    fun _ _ C _ _ _ _ _ hel hiso _ hj _ _ h0 h1 => C.recipeE_of_iso hel hiso hj h0 h1⟩
  rcases hk with rfl | rfl | rfl | rfl | ⟨h1, h2⟩
  · exact ⟨_, ex1rep_1⟩
  · exact ⟨_, ex1rep_2⟩
  · exact ⟨_, ex1rep_3⟩
  · exact ⟨_, ex1rep_5⟩
  · rcases (by omega : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
      k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, ex1rep_9⟩
    · exact ⟨_, ex1rep_10⟩
    · exact ⟨_, ex1rep_11⟩
    · exact ⟨_, ex1rep_12⟩
    · exact ⟨_, ex1rep_13⟩
    · exact ⟨_, ex1rep_14⟩
    · exact ⟨_, ex1rep_15⟩
    · exact ⟨_, ex1rep_16⟩
    · exact ⟨_, ex1rep_17⟩
    · exact ⟨_, ex1rep_18⟩
    · exact ⟨_, ex1rep_19⟩
    · exact ⟨_, ex1rep_20⟩
    · exact ⟨_, ex1rep_21⟩
    · exact ⟨_, ex1rep_22⟩
    · exact ⟨_, ex1rep_23⟩
    · exact ⟨_, ex1rep_24⟩

end RH2F
