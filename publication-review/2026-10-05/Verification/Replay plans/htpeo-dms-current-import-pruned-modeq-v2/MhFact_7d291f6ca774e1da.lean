-- Lean proof of fact 7d291f6ca774e1da (RH2F.layer1); added by fact_submit, do not edit
import MhFact_5c1eb3f583cf643f



-- ===== from RH2R.lean =====
/-
  RH2R.lean — Lemma R (fact 8ef6f166623321e6) in Lean 4.20 core: star 6-colourings of an edge set `P` in which a
  perfect matching `N` of `P` is the colour class of the last colour `5`.

  Setting (library style): a loopless ambient multigraph `X`, an edge set `P : Fin X.m → Prop`, a perfect matching
  `N` of `P` (`PMOn P N`), a colouring `c : Fin X.m → Fin 6` with `N f ↔ c f = 5` on `P`.  "F-edges" are the edges
  of `P` not in `N`.

  * `RA P N c` : two distinct F-edges with a common end get different colours            (condition (A))
  * `RB P N c` : for an N-edge joining `y, y'`, an F-edge at `y` and a different F-edge at `y'` get different colours
                                                                                       (condition (B))
  * `RC P N c` : no Walk4 (path with 4 edges, or 4-cycle) of F-edges is bicoloured       (condition (C))

  Theorem `RH2F.lemmaR` : StarOn P 6 c ↔ RA ∧ RB ∧ RC.
  Theorem `RH2F.mc5_of_class` : a star 6-colouring with `N` as some colour class can be recoloured so that `N`
  is the class of colour `5`.
-/

namespace RH2F
open MGraph

section defs
variable {X : MGraph}

/-- `N` is a perfect matching of the edge set `P` -/
def PMOn (P N : Fin X.m → Prop) : Prop :=
  (∀ f, N f → P f) ∧ ∀ x, (∃ f, P f ∧ X.Inc f x) → ∃ a, N a ∧ X.Inc a x ∧ ∀ d, N d → X.Inc d x → d = a

/-- `N` is a colour class of `c` on `P` -/
def ClassOn (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6) : Prop :=
  ∃ μ : Fin 6, ∀ f, P f → (N f ↔ c f = μ)

/-- `c` is a star 6-colouring of `P` whose colour class `5` is `N` -/
def MC5 (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6) : Prop :=
  StarOn P 6 c ∧ ∀ f, P f → (N f ↔ c f = 5)

/-- condition (A) of Lemma R -/
def RA (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6) : Prop :=
  ∀ a b, X.Adj a b → P a → P b → ¬ N a → ¬ N b → c a ≠ c b

/-- condition (B) of Lemma R -/
def RB (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6) : Prop :=
  ∀ e y y' f f', N e → X.Joins e y y' → P f → ¬ N f → X.Inc f y → P f' → ¬ N f' → X.Inc f' y' → f ≠ f' →
    c f ≠ c f'

/-- condition (C) of Lemma R -/
def RC (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6) : Prop :=
  ∀ w : X.Walk4, P w.e1 → P w.e2 → P w.e3 → P w.e4 → ¬ N w.e1 → ¬ N w.e2 → ¬ N w.e3 → ¬ N w.e4 → ¬ Bicol c w

end defs

section basics
variable {X : MGraph}

theorem joins_symm {f : Fin X.m} {x y : Fin X.n} (h : X.Joins f x y) : X.Joins f y x := h.symm

/-- an edge incident with `y` joins `y` to some vertex -/
theorem joins_of_inc {f : Fin X.m} {y : Fin X.n} (h : X.Inc f y) : ∃ z, X.Joins f y z := by
  rcases h with h | h
  · exact ⟨(X.ends f).2, Or.inl (by rw [← h])⟩
  · exact ⟨(X.ends f).1, Or.inr (by rw [← h])⟩

theorem ne_of_joins' (hloop : Loopless X) {f : Fin X.m} {x y : Fin X.n} (h : X.Joins f x y) : x ≠ y :=
  ne_of_joins hloop h

/-- uniqueness of the matching edge at a vertex -/
theorem pm_unique {P N : Fin X.m → Prop} (hN : PMOn P N) {a b : Fin X.m} {x : Fin X.n} (ha : N a) (hb : N b)
    (hax : X.Inc a x) (hbx : X.Inc b x) : a = b := by
  obtain ⟨a0, _, _, hu⟩ := hN.2 x ⟨a, hN.1 a ha, hax⟩
  rw [hu a ha hax, hu b hb hbx]

end basics

section lemmaR
variable {X : MGraph} {P N : Fin X.m → Prop} {c : Fin X.m → Fin 6}

theorem ra_of_star (hc : StarOn P 6 c) : RA P N c :=
  fun a b hab ha hb _ _ => hc.1 a b hab ha hb

theorem rc_of_star (hc : StarOn P 6 c) : RC P N c :=
  fun w h1 h2 h3 h4 _ _ _ _ => hc.2 w h1 h2 h3 h4

theorem rb_of_star (hloop : Loopless X) (hN : PMOn P N) (hcl : ∀ f, P f → (N f ↔ c f = 5))
    (hc : StarOn P 6 c) : RB P N c := by
  classical
  intro e y y' f f' he hj hf hnf hfy hf' hnf' hf'y' hff heq
  by_cases hsh : ∃ x, X.Inc f x ∧ X.Inc f' x
  · obtain ⟨x, hx, hx'⟩ := hsh
    exact hc.1 f f' ⟨hff, x, hx, hx'⟩ hf hf' heq
  · have hsh' : ∀ x, X.Inc f x → X.Inc f' x → False := fun x h1 h2 => hsh ⟨x, h1, h2⟩
    obtain ⟨z, hz⟩ := joins_of_inc hfy
    obtain ⟨w, hw⟩ := joins_of_inc hf'y'
    obtain ⟨a, ha, haw, _⟩ := hN.2 w ⟨f', hf', joins_inc_right hw⟩
    obtain ⟨w', hw'⟩ := joins_of_inc haw
    have hyy' : y ≠ y' := ne_of_joins hloop hj
    have hyz : y ≠ z := ne_of_joins hloop hz
    have hy'w : y' ≠ w := ne_of_joins hloop hw
    have hww' : w ≠ w' := ne_of_joins hloop hw'
    have hzy' : z ≠ y' := fun h => hsh' y' (h ▸ joins_inc_right hz) hf'y'
    have hzw : z ≠ w := fun h => hsh' w (h ▸ joins_inc_right hz) (joins_inc_right hw)
    have hyw : y ≠ w := fun h => hsh' y hfy (h ▸ joins_inc_right hw)
    have hyw' : y ≠ w' := by
      intro h
      have hae : a = e := pm_unique hN ha he (h ▸ joins_inc_right hw') (joins_inc_left hj)
      subst hae
      rcases inc_of_joins hj (joins_inc_left hw') with h1 | h1
      · exact hyw h1.symm
      · exact hy'w h1.symm
    have hy'w' : y' ≠ w' := by
      intro h
      have hae : a = e := pm_unique hN ha he (h ▸ joins_inc_right hw') (joins_inc_right hj)
      subst hae
      rcases inc_of_joins hj (joins_inc_left hw') with h1 | h1
      · exact hyw h1.symm
      · exact hy'w h1.symm
    let W : X.Walk4 :=
      { v0 := z, v1 := y, v2 := y', v3 := w, v4 := w'
        e1 := f, e2 := e, e3 := f', e4 := a
        h1 := joins_symm hz, h2 := hj, h3 := hw, h4 := hw'
        d01 := Ne.symm hyz, d02 := hzy', d03 := hzw, d12 := hyy', d13 := hyw, d14 := hyw'
        d23 := hy'w, d24 := hy'w', d34 := hww' }
    have hPe : P e := hN.1 e he
    have hPa : P a := hN.1 a ha
    exact hc.2 W hf hPe hf' hPa ⟨heq, ((hcl e hPe).1 he).trans ((hcl a hPa).1 ha).symm⟩

/-- (⇐) of Lemma R; only the matching property of `N` is used -/
theorem star_of_rabc (hN : PMOn P N) (hcl : ∀ f, P f → (N f ↔ c f = 5))
    (hA : RA P N c) (hB : RB P N c) (hC : RC P N c) : StarOn P 6 c := by
  have prop : ∀ a b, X.Adj a b → P a → P b → c a ≠ c b := by
    intro a b hab ha hb heq
    obtain ⟨hne, x, hax, hbx⟩ := hab
    by_cases hna : N a <;> by_cases hnb : N b
    · exact hne (pm_unique hN hna hnb hax hbx)
    · exact hnb ((hcl b hb).2 (heq ▸ (hcl a ha).1 hna))
    · exact hna ((hcl a ha).2 (heq.symm ▸ (hcl b hb).1 hnb))
    · exact hA a b ⟨hne, x, hax, hbx⟩ ha hb hna hnb heq
  refine ⟨prop, ?_⟩
  intro w h1 h2 h3 h4 hbc
  obtain ⟨h13, h24⟩ := hbc
  have hne12 : c w.e1 ≠ c w.e2 := prop w.e1 w.e2 ⟨w.e1_ne_e2, w.v1, w.inc_e1_v1, w.inc_e2_v1⟩ h1 h2
  by_cases hn2 : N w.e2
  · -- the F-edges e1 (at v1) and e3 (at v2) around the N-edge e2
    have h5 : c w.e2 = 5 := (hcl _ h2).1 hn2
    have hn1 : ¬ N w.e1 := fun h => hne12 (((hcl _ h1).1 h).trans h5.symm)
    have hn3 : ¬ N w.e3 := fun h => hne12 (h13.trans (((hcl _ h3).1 h).trans h5.symm))
    exact hB w.e2 w.v1 w.v2 w.e1 w.e3 hn2 w.h2 h1 hn1 w.inc_e1_v1 h3 hn3 w.inc_e3_v2 w.e1_ne_e3 h13
  · by_cases hn1 : N w.e1
    · -- the F-edges e2 (at v2) and e4 (at v3) around the N-edge e3
      have h5 : c w.e1 = 5 := (hcl _ h1).1 hn1
      have hn3 : N w.e3 := (hcl _ h3).2 (h13 ▸ h5)
      have hn4 : ¬ N w.e4 := fun h => hn2 ((hcl _ h2).2 (h24.trans ((hcl _ h4).1 h)))
      exact hB w.e3 w.v2 w.v3 w.e2 w.e4 hn3 w.h3 h2 hn2 w.inc_e2_v2 h4 hn4 w.inc_e4_v3 w.e2_ne_e4 h24
    · have hn3 : ¬ N w.e3 := fun h => hn1 ((hcl _ h1).2 (h13.trans ((hcl _ h3).1 h)))
      have hn4 : ¬ N w.e4 := fun h => hn2 ((hcl _ h2).2 (h24.trans ((hcl _ h4).1 h)))
      exact hC w h1 h2 h3 h4 hn1 hn2 hn3 hn4 ⟨h13, h24⟩

/-- **Lemma R** (fact 8ef6f166623321e6).  For a loopless ambient `X`, a perfect matching `N` of `P` and a colouring
    `c` whose colour class `5` on `P` is `N`: `c` is a star 6-colouring of `P` iff (A), (B), (C) hold. -/
theorem lemmaR (hloop : Loopless X) (hN : PMOn P N) (hcl : ∀ f, P f → (N f ↔ c f = 5)) :
    StarOn P 6 c ↔ RA P N c ∧ RB P N c ∧ RC P N c :=
  ⟨fun hc => ⟨ra_of_star hc, rb_of_star hloop hN hcl hc, rc_of_star hc⟩,
   fun h => star_of_rabc hN hcl h.1 h.2.1 h.2.2⟩

/-- the transposition of `μ` and `5` -/
def swap5 (μ : Fin 6) (x : Fin 6) : Fin 6 := if x = μ then 5 else if x = 5 then μ else x

theorem swap5_inj' : ∀ μ x y : Fin 6, swap5 μ x = swap5 μ y → x = y := by decide

theorem swap5_inj (μ : Fin 6) : ∀ x y, swap5 μ x = swap5 μ y → x = y := swap5_inj' μ

theorem swap5_eq5' : ∀ μ x : Fin 6, swap5 μ x = 5 ↔ x = μ := by decide

theorem swap5_eq5 (μ x : Fin 6) : swap5 μ x = 5 ↔ x = μ := swap5_eq5' μ x

/-- a star 6-colouring with `N` as a colour class can be normalised so that `N` is the class of colour `5` -/
theorem mc5_of_class {c : Fin X.m → Fin 6} (hc : StarOn P 6 c) (hcl : ClassOn P N c) :
    ∃ c' : Fin X.m → Fin 6, MC5 P N c' := by
  obtain ⟨μ, hμ⟩ := hcl
  refine ⟨fun f => swap5 μ (c f), starOn_map (swap5 μ) (swap5_inj μ) hc, fun f hf => ?_⟩
  rw [hμ f hf]
  exact (swap5_eq5 μ (c f)).symm

theorem class_of_mc5 {c : Fin X.m → Fin 6} (h : MC5 P N c) : StarOn P 6 c ∧ ClassOn P N c :=
  ⟨h.1, ⟨5, h.2⟩⟩

end lemmaR

end RH2F

-- ===== from RH2Cut.lean =====
/-
  RH2Cut.lean — 2-edge-cuts of an edge set `P` and their closures, in the library's edge-set style.

  A `Cut2 P` is a vertex 2-colouring `S` (side `A` = `true`, side `B` = `false`) such that exactly the two distinct
  `P`-edges `e1 = a1 b1`, `e2 = a2 b2` (`a_i ∈ A`, `b_i ∈ B`) cross it, with `a1 ≠ a2` and `b1 ≠ b2`.
  `C.flip` exchanges the two sides.  `C.inA f` : `f ∈ P` has both ends in `A`.
  The closure `G_A` is the edge set `C.clo` of `addEdge X a1 a2`: the `P`-edges inside `A` and the new edge
  `g_A = Fin.last X.m` joining `a1, a2`; `C.cloN N g` is the matching `(N ∩ E(G[A])) ∪ ({g_A} if g)`.
  The `B`-side objects are those of `C.flip`.
-/

namespace RH2F
open MGraph

section cut
variable {X : MGraph}

/-- a 2-edge-cut of `P` with distinct ends on each side -/
structure Cut2 (P : Fin X.m → Prop) where
  S : Fin X.n → Bool
  e1 : Fin X.m
  e2 : Fin X.m
  a1 : Fin X.n
  a2 : Fin X.n
  b1 : Fin X.n
  b2 : Fin X.n
  P1 : P e1
  P2 : P e2
  j1 : X.Joins e1 a1 b1
  j2 : X.Joins e2 a2 b2
  sa1 : S a1 = true
  sa2 : S a2 = true
  sb1 : S b1 = false
  sb2 : S b2 = false
  ne12 : e1 ≠ e2
  ha : a1 ≠ a2
  hb : b1 ≠ b2
  cut : ∀ f, P f → S (X.ends f).1 ≠ S (X.ends f).2 → f = e1 ∨ f = e2

variable {P : Fin X.m → Prop}

/-- the same cut with the sides exchanged -/
def Cut2.flip (C : Cut2 P) : Cut2 P where
  S := fun v => !C.S v
  e1 := C.e1
  e2 := C.e2
  a1 := C.b1
  a2 := C.b2
  b1 := C.a1
  b2 := C.a2
  P1 := C.P1
  P2 := C.P2
  j1 := Or.symm C.j1
  j2 := Or.symm C.j2
  sa1 := by simp [C.sb1]
  sa2 := by simp [C.sb2]
  sb1 := by simp [C.sa1]
  sb2 := by simp [C.sa2]
  ne12 := C.ne12
  ha := C.hb
  hb := C.ha
  cut := fun f hf h => C.cut f hf (fun h' => h (by simp [h']))

/-- `f ∈ P` has both ends in side `A` -/
def Cut2.inA (C : Cut2 P) (f : Fin X.m) : Prop := P f ∧ C.S (X.ends f).1 = true ∧ C.S (X.ends f).2 = true

/-- `f` is one of the two cut edges -/
def Cut2.isCut (C : Cut2 P) (f : Fin X.m) : Prop := f = C.e1 ∨ f = C.e2

/-- the edge closure `G_A` as an edge set of `addEdge X a1 a2` -/
def Cut2.clo (C : Cut2 P) : Fin (addEdge X C.a1 C.a2).m → Prop :=
  fun i => i = Fin.last X.m ∨ ∃ d, i = Fin.castSucc d ∧ C.inA d

/-- the matching `(N ∩ E(G[A])) ∪ ({g_A} if g)` of the closure -/
def Cut2.cloN (C : Cut2 P) (N : Fin X.m → Prop) (g : Prop) : Fin (addEdge X C.a1 C.a2).m → Prop :=
  fun i => (i = Fin.last X.m ∧ g) ∨ ∃ d, i = Fin.castSucc d ∧ C.inA d ∧ N d

namespace Cut2
variable (C : Cut2 P)

theorem flip_S (v : Fin X.n) : C.flip.S v = !C.S v := rfl
theorem flip_isCut {f : Fin X.m} : C.flip.isCut f ↔ C.isCut f := Iff.rfl

theorem side_of_inA {f : Fin X.m} {x : Fin X.n} (hf : C.inA f) (hx : X.Inc f x) : C.S x = true := by
  rcases hx with hx | hx
  · rw [← hx]; exact hf.2.1
  · rw [← hx]; exact hf.2.2

theorem inc_e1 {x : Fin X.n} (hx : X.Inc C.e1 x) : x = C.a1 ∨ x = C.b1 := inc_of_joins C.j1 hx
theorem inc_e2 {x : Fin X.n} (hx : X.Inc C.e2 x) : x = C.a2 ∨ x = C.b2 := inc_of_joins C.j2 hx

theorem a1_ne_b2 : C.a1 ≠ C.b2 := fun h => by have h1 := C.sa1; rw [h, C.sb2] at h1; exact absurd h1 (by decide)
theorem a2_ne_b1 : C.a2 ≠ C.b1 := fun h => by have h1 := C.sa2; rw [h, C.sb1] at h1; exact absurd h1 (by decide)
theorem a1_ne_b1 : C.a1 ≠ C.b1 := fun h => by have h1 := C.sa1; rw [h, C.sb1] at h1; exact absurd h1 (by decide)
theorem a2_ne_b2 : C.a2 ≠ C.b2 := fun h => by have h1 := C.sa2; rw [h, C.sb2] at h1; exact absurd h1 (by decide)

/-- the two cut edges have no common end -/
theorem e12_disj {x : Fin X.n} (h1 : X.Inc C.e1 x) (h2 : X.Inc C.e2 x) : False := by
  rcases C.inc_e1 h1 with h | h <;> rcases C.inc_e2 h2 with h' | h'
  · exact C.ha (h.symm.trans h')
  · exact C.a1_ne_b2 (h.symm.trans h')
  · exact C.a2_ne_b1 (h'.symm.trans h)
  · exact C.hb (h.symm.trans h')

theorem cut_disj {f f' : Fin X.m} (hf : C.isCut f) (hf' : C.isCut f') (hne : f ≠ f') {x : Fin X.n}
    (h1 : X.Inc f x) (h2 : X.Inc f' x) : False := by
  rcases hf with rfl | rfl <;> rcases hf' with rfl | rfl
  · exact hne rfl
  · exact C.e12_disj h1 h2
  · exact C.e12_disj h2 h1
  · exact hne rfl

/-- every edge of `P` lies inside `A`, inside `B`, or is a cut edge -/
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
  rcases hf with rfl | rfl
  · have h := C.side_of_inA hin (joins_inc_right C.j1); rw [C.sb1] at h; exact absurd h (by decide)
  · have h := C.side_of_inA hin (joins_inc_right C.j2); rw [C.sb2] at h; exact absurd h (by decide)

theorem not_flip_of_inA {f : Fin X.m} (hf : C.inA f) : ¬ C.flip.inA f := by
  intro h
  have h1 := h.2.1
  rw [flip_S, hf.2.1] at h1
  exact absurd h1 (by decide)

/-- a non-cut edge of `P` at a vertex of `A` lies inside `A` -/
theorem inA_of_notcut {f : Fin X.m} {x : Fin X.n} (hf : P f) (hnc : ¬ C.isCut f) (hx : X.Inc f x)
    (hs : C.S x = true) : C.inA f := by
  rcases C.cases_P hf with h | h | h
  · exact h
  · have h' := C.flip.side_of_inA h hx
    rw [flip_S, hs] at h'
    exact absurd h' (by decide)
  · exact absurd h hnc

/-- the end in `A` of a cut edge -/
theorem cutA {f : Fin X.m} (hf : C.isCut f) {x : Fin X.n} (hx : X.Inc f x) (hs : C.S x = true) :
    (f = C.e1 ∧ x = C.a1) ∨ (f = C.e2 ∧ x = C.a2) := by
  rcases hf with rfl | rfl
  · rcases C.inc_e1 hx with h | h
    · exact Or.inl ⟨rfl, h⟩
    · rw [h, C.sb1] at hs; exact absurd hs (by decide)
  · rcases C.inc_e2 hx with h | h
    · exact Or.inr ⟨rfl, h⟩
    · rw [h, C.sb2] at hs; exact absurd hs (by decide)

theorem inc_new_iff {x : Fin X.n} : (addEdge X C.a1 C.a2).Inc (Fin.last X.m) x ↔ x = C.a1 ∨ x = C.a2 :=
  addEdge_inc_new

theorem clo_last : C.clo (Fin.last X.m) := Or.inl rfl
theorem clo_old {d : Fin X.m} (h : C.inA d) : C.clo (Fin.castSucc d) := Or.inr ⟨d, rfl, h⟩

theorem clo_old_iff {d : Fin X.m} : C.clo (Fin.castSucc d) ↔ C.inA d := by
  constructor
  · rintro (h | ⟨d', h, hd'⟩)
    · exact absurd h (castSucc_ne_last d)
    · rw [castSucc_inj' h]; exact hd'
  · exact C.clo_old

theorem cloN_old_iff {N : Fin X.m → Prop} {g : Prop} {d : Fin X.m} :
    C.cloN N g (Fin.castSucc d) ↔ C.inA d ∧ N d := by
  constructor
  · rintro (⟨h, _⟩ | ⟨d', h, hd', hn⟩)
    · exact absurd h (castSucc_ne_last d)
    · rw [castSucc_inj' h]; exact ⟨hd', hn⟩
  · exact fun h => Or.inr ⟨d, rfl, h.1, h.2⟩

theorem cloN_last_iff {N : Fin X.m → Prop} {g : Prop} : C.cloN N g (Fin.last X.m) ↔ g := by
  constructor
  · rintro (⟨_, hg⟩ | ⟨d', h, _, _⟩)
    · exact hg
    · exact absurd h.symm (castSucc_ne_last d')
  · exact fun hg => Or.inl ⟨rfl, hg⟩

end Cut2

/-- at most two edges of `P ∖ M` at a vertex of a cubic `P` with a perfect matching `M` -/
theorem fdeg2 {M : Fin X.m → Prop} (hcub : CubicOn P) (hM : PMOn P M) {x : Fin X.n} {f1 f2 f3 : Fin X.m}
    (h1 : P f1) (h2 : P f2) (h3 : P f3) (n1 : ¬ M f1) (n2 : ¬ M f2) (n3 : ¬ M f3)
    (i1 : X.Inc f1 x) (i2 : X.Inc f2 x) (i3 : X.Inc f3 x) (d12 : f1 ≠ f2) (d13 : f1 ≠ f3) (d23 : f2 ≠ f3) :
    False := by
  obtain ⟨a, ha, hax, _⟩ := hM.2 x ⟨f1, h1, i1⟩
  obtain ⟨p, q, r, _, _, _, _, _, _, _, _, _, hall⟩ := hcub x ⟨f1, h1, i1⟩
  have da1 : a ≠ f1 := fun h => n1 (h ▸ ha)
  have da2 : a ≠ f2 := fun h => n2 (h ▸ ha)
  have da3 : a ≠ f3 := fun h => n3 (h ▸ ha)
  rcases hall f1 h1 i1 with e1 | e1 | e1 <;> rcases hall f2 h2 i2 with e2 | e2 | e2 <;>
    rcases hall f3 h3 i3 with e3 | e3 | e3 <;> rcases hall a (hM.1 a ha) hax with e4 | e4 | e4 <;>
    first
    | exact d12 (e1.trans e2.symm) | exact d13 (e1.trans e3.symm) | exact d23 (e2.trans e3.symm)
    | exact da1 (e4.trans e1.symm) | exact da2 (e4.trans e2.symm) | exact da3 (e4.trans e3.symm)

end cut

end RH2F

-- ===== from RH2G2F.lean =====
/-
  RH2G2F.lean — Lemma G2F (fact 1d175e8252f975b1) in Lean 4.20 core: gluing MC-colourings across a 2-edge-cut
  whose two cut edges are F-edges (not in the perfect matching).
-/

namespace RH2F
open MGraph

/-! ## Colour permutations -/

/-- the transposition of `a` and `b` on `Fin 6` -/
def swapc (a b x : Fin 6) : Fin 6 := if x = a then b else if x = b then a else x

def all6 (p : Fin 6 → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5

theorem fin6_cases : ∀ x : Fin 6, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by decide

theorem all6_sound {p : Fin 6 → Bool} (h : all6 p = true) : ∀ x, p x = true := by
  simp only [all6, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  intro x
  rcases fin6_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem swapc_invol_chk : all6 (fun a => all6 fun b => all6 fun x => swapc a b (swapc a b x) == x) = true := by
  decide +kernel

theorem swapc_invol (a b x : Fin 6) : swapc a b (swapc a b x) = x := by
  have h := all6_sound (all6_sound (all6_sound swapc_invol_chk a) b) x
  simpa using h

theorem swapc_inj (a b : Fin 6) : ∀ x y, swapc a b x = swapc a b y → x = y := by
  intro x y h
  rw [← swapc_invol a b x, h, swapc_invol]

theorem swapc_left (a b : Fin 6) : swapc a b a = b := by simp [swapc]

theorem swapc_right (a b : Fin 6) : swapc a b b = a := by
  unfold swapc; by_cases h : b = a
  · rw [if_pos h, h]
  · rw [if_neg h, if_pos rfl]

theorem swapc_other (a b x : Fin 6) (ha : x ≠ a) (hb : x ≠ b) : swapc a b x = x := by
  simp [swapc, ha, hb]

/-- permutations of `{1,2,3,4}` (as image lists), extended by `0 ↦ 0`, `5 ↦ 5` -/
def p4L : List (List Nat) :=
  [[1,2,3,4],[1,2,4,3],[1,3,2,4],[1,3,4,2],[1,4,2,3],[1,4,3,2],[2,1,3,4],[2,1,4,3],[2,3,1,4],[2,3,4,1],
   [2,4,1,3],[2,4,3,1],[3,1,2,4],[3,1,4,2],[3,2,1,4],[3,2,4,1],[3,4,1,2],[3,4,2,1],[4,1,2,3],[4,1,3,2],
   [4,2,1,3],[4,2,3,1],[4,3,1,2],[4,3,2,1]]

def ap4 (l : List Nat) (x : Fin 6) : Fin 6 :=
  if x.val = 0 ∨ x.val = 5 then x else ⟨l.getD (x.val - 1) 1 % 6, Nat.mod_lt _ (by decide)⟩

def all4 (p : Fin 6 → Bool) : Bool := p 1 && p 2 && p 3 && p 4

theorem all4_sound {p : Fin 6 → Bool} (h : all4 p = true) : ∀ x, x ≠ 0 → x ≠ 5 → p x = true := by
  simp only [all4, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  intro x h0 h5
  rcases fin6_cases x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  all_goals first | assumption | exact absurd rfl h5

def g2fChk : Bool := all4 fun r1 => all4 fun r2 => all4 fun x1 => all4 fun x2 =>
  p4L.any fun l => ap4 l x1 != r1 && ap4 l x1 != r2 && ap4 l x2 != r1 && ap4 l x2 != r2

theorem g2fChk_ok : g2fChk = true := by decide +kernel

def p4Chk : Bool := p4L.all fun l =>
  ap4 l 0 == 0 && ap4 l 5 == 5 && all6 fun x => all6 fun y => !(ap4 l x == ap4 l y) || x == y

theorem p4Chk_ok : p4Chk = true := by decide +kernel

theorem p4_props {l : List Nat} (hl : l ∈ p4L) :
    ap4 l 0 = 0 ∧ ap4 l 5 = 5 ∧ ∀ x y, ap4 l x = ap4 l y → x = y := by
  have h := List.all_eq_true.1 p4Chk_ok l hl
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h5⟩, hi⟩ := h
  refine ⟨h0, h5, fun x y hxy => ?_⟩
  have := all6_sound (all6_sound hi x) y
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd hxy h
  · exact h

theorem swap0_chk : all6 (fun a => all6 fun x =>
    a == 5 || x == a || x == 5 || (swapc a 0 x != 0 && swapc a 0 x != 5)) = true := by decide +kernel

theorem swap0_range {a x : Fin 6} (ha : a ≠ 5) (hxa : x ≠ a) (hx5 : x ≠ 5) :
    swapc a 0 x ≠ 0 ∧ swapc a 0 x ≠ 5 := by
  have h := all6_sound (all6_sound swap0_chk a) x
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with ((h | h) | h) | h
  · exact absurd h ha
  · exact absurd h hxa
  · exact absurd h hx5
  · exact h

/-- **the colour permutation of G2F**: fixes `5`, sends `γ'` to `γ`, and sends `x1, x2` outside `{r1, r2}` -/
theorem perm_g2f (γ γ' r1 r2 x1 x2 : Fin 6) (hγ : γ ≠ 5) (hγ' : γ' ≠ 5) (hr1 : r1 ≠ γ) (hr1' : r1 ≠ 5)
    (hr2 : r2 ≠ γ) (hr2' : r2 ≠ 5) (hx1 : x1 ≠ γ') (hx1' : x1 ≠ 5) (hx2 : x2 ≠ γ') (hx2' : x2 ≠ 5) :
    ∃ σ : Fin 6 → Fin 6, (∀ x y, σ x = σ y → x = y) ∧ σ 5 = 5 ∧ σ γ' = γ ∧
      σ x1 ≠ r1 ∧ σ x1 ≠ r2 ∧ σ x2 ≠ r1 ∧ σ x2 ≠ r2 := by
  have R1 := swap0_range hγ hr1 hr1'
  have R2 := swap0_range hγ hr2 hr2'
  have X1 := swap0_range hγ' hx1 hx1'
  have X2 := swap0_range hγ' hx2 hx2'
  have h := all4_sound (all4_sound (all4_sound (all4_sound g2fChk_ok _ R1.1 R1.2) _ R2.1 R2.2) _ X1.1 X1.2)
    _ X2.1 X2.2
  obtain ⟨l, hl, hgood⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hgood
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hgood
  obtain ⟨l0, l5, linj⟩ := p4_props hl
  refine ⟨fun x => swapc γ 0 (ap4 l (swapc γ' 0 x)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact swapc_inj γ' 0 _ _ (linj _ _ (swapc_inj γ 0 _ _ hxy))
  · show swapc γ 0 (ap4 l (swapc γ' 0 5)) = 5
    rw [swapc_other γ' 0 5 (Ne.symm hγ') (by decide), l5, swapc_other γ 0 5 (Ne.symm hγ) (by decide)]
  · show swapc γ 0 (ap4 l (swapc γ' 0 γ')) = γ
    rw [swapc_left, l0, swapc_right]
  all_goals intro hc
  · exact g1 (by rw [← hc, swapc_invol])
  · exact g2 (by rw [← hc, swapc_invol])
  · exact g3 (by rw [← hc, swapc_invol])
  · exact g4 (by rw [← hc, swapc_invol])

/-! ## Side lemmas for one side of a 2-edge-cut -/

section side
variable {X : MGraph} {P M : Fin X.m → Prop}

/-- the closure matching of an F-type cut is a perfect matching of the closure -/
theorem Cut2.pm_cloF (C : Cut2 P) (hM : PMOn P M) (hF1 : ¬ M C.e1) (hF2 : ¬ M C.e2) :
    PMOn C.clo (C.cloN M False) := by
  constructor
  · intro i hi
    rcases hi with ⟨_, hg⟩ | ⟨d, rfl, hd, _⟩
    · exact hg.elim
    · exact C.clo_old hd
  · intro x ⟨i, hi, hix⟩
    have hxA : C.S x = true ∧ ∃ f, P f ∧ X.Inc f x := by
      rcases hi with rfl | ⟨d, rfl, hd⟩
      · rcases (C.inc_new_iff).1 hix with rfl | rfl
        · exact ⟨C.sa1, C.e1, C.P1, joins_inc_left C.j1⟩
        · exact ⟨C.sa2, C.e2, C.P2, joins_inc_left C.j2⟩
      · have hix' : X.Inc d x := addEdge_inc_old.1 hix
        exact ⟨C.side_of_inA hd hix', d, hd.1, hix'⟩
    obtain ⟨a, ha, hax, hu⟩ := hM.2 x hxA.2
    have hnc : ¬ C.isCut a := fun h => h.elim (fun h' => hF1 (h' ▸ ha)) (fun h' => hF2 (h' ▸ ha))
    have hainA : C.inA a := C.inA_of_notcut (hM.1 a ha) hnc hax hxA.1
    refine ⟨Fin.castSucc a, Or.inr ⟨a, rfl, hainA, ha⟩, addEdge_inc_old.2 hax, ?_⟩
    intro j hj hjx
    rcases hj with ⟨_, hg⟩ | ⟨d, rfl, _, hdM⟩
    · exact hg.elim
    · rw [hu d hdM (addEdge_inc_old.1 hjx)]

theorem Cut2.inc_last_of_cut (C : Cut2 P) {f : Fin X.m} (hf : C.isCut f) {x : Fin X.n} (hx : X.Inc f x)
    (hs : C.S x = true) : (addEdge X C.a1 C.a2).Inc (Fin.last X.m) x := by
  rcases C.cutA hf hx hs with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact (C.inc_new_iff).2 (Or.inl rfl)
  · exact (C.inc_new_iff).2 (Or.inr rfl)

variable (C : Cut2 P) (d : Fin (addEdge X C.a1 C.a2).m → Fin 6) (c : Fin X.m → Fin 6)

/-- properness at a vertex of side `A` -/
theorem side_prop (hd : StarOn C.clo 6 d) (hag : ∀ f, C.inA f → c f = d (Fin.castSucc f))
    (hcut : ∀ f, C.isCut f → c f = d (Fin.last X.m)) {a b : Fin X.m} {x : Fin X.n} (hab : a ≠ b)
    (hax : X.Inc a x) (hbx : X.Inc b x) (hs : C.S x = true) (ha : P a) (hb : P b) : c a ≠ c b := by
  by_cases hca : C.isCut a <;> by_cases hcb : C.isCut b
  · exact (C.cut_disj hca hcb hab hax hbx).elim
  · rw [hcut a hca, hag b (C.inA_of_notcut hb hcb hbx hs)]
    exact hd.1 _ _ ⟨Ne.symm (castSucc_ne_last b), x, C.inc_last_of_cut hca hax hs, addEdge_inc_old.2 hbx⟩
      C.clo_last (C.clo_old (C.inA_of_notcut hb hcb hbx hs))
  · rw [hag a (C.inA_of_notcut ha hca hax hs), hcut b hcb]
    exact hd.1 _ _ ⟨castSucc_ne_last a, x, addEdge_inc_old.2 hax, C.inc_last_of_cut hcb hbx hs⟩
      (C.clo_old (C.inA_of_notcut ha hca hax hs)) C.clo_last
  · rw [hag a (C.inA_of_notcut ha hca hax hs), hag b (C.inA_of_notcut hb hcb hbx hs)]
    exact hd.1 _ _ ⟨fun h => hab (castSucc_inj' h), x, addEdge_inc_old.2 hax, addEdge_inc_old.2 hbx⟩
      (C.clo_old (C.inA_of_notcut ha hca hax hs)) (C.clo_old (C.inA_of_notcut hb hcb hbx hs))

/-- condition (B) at a matching edge inside side `A` -/
theorem side_rb (hrb : RB C.clo (C.cloN M False) d) (hag : ∀ f, C.inA f → c f = d (Fin.castSucc f))
    (hcut : ∀ f, C.isCut f → c f = d (Fin.last X.m)) (hMa : ∀ e, M e → ¬ X.Joins e C.a1 C.a2)
    {e : Fin X.m} {y y' : Fin X.n} (he : M e) (hin : C.inA e) (hj : X.Joins e y y')
    {f f' : Fin X.m} (hf : P f) (hnf : ¬ M f) (hfy : X.Inc f y) (hf' : P f') (hnf' : ¬ M f')
    (hf'y' : X.Inc f' y') (hff : f ≠ f') : c f ≠ c f' := by
  have hy : C.S y = true := C.side_of_inA hin (joins_inc_left hj)
  have hy' : C.S y' = true := C.side_of_inA hin (joins_inc_right hj)
  have hNe : C.cloN M False (Fin.castSucc e) := (C.cloN_old_iff).2 ⟨hin, he⟩
  have hje : (addEdge X C.a1 C.a2).Joins (Fin.castSucc e) y y' := addEdge_joins_old.2 hj
  have nlast : ¬ C.cloN M False (Fin.last X.m) := fun h => (C.cloN_last_iff).1 h
  have nold : ∀ g, ¬ M g → ¬ C.cloN M False (Fin.castSucc g) := fun g hg h => hg ((C.cloN_old_iff).1 h).2
  by_cases hcf : C.isCut f <;> by_cases hcf' : C.isCut f'
  · exfalso
    rcases C.cutA hcf hfy hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases C.cutA hcf' hf'y' hy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hff rfl
    · exact hMa e he hj
    · exact hMa e he (Or.symm hj)
    · exact hff rfl
  · have hinf' := C.inA_of_notcut hf' hcf' hf'y' hy'
    rw [hcut f hcf, hag f' hinf']
    exact hrb _ y y' _ _ hNe hje C.clo_last nlast (C.inc_last_of_cut hcf hfy hy) (C.clo_old hinf') (nold f' hnf')
      (addEdge_inc_old.2 hf'y') (Ne.symm (castSucc_ne_last f'))
  · have hinf := C.inA_of_notcut hf hcf hfy hy
    rw [hag f hinf, hcut f' hcf']
    exact hrb _ y y' _ _ hNe hje (C.clo_old hinf) (nold f hnf) (addEdge_inc_old.2 hfy) C.clo_last nlast
      (C.inc_last_of_cut hcf' hf'y' hy') (castSucc_ne_last f)
  · have hinf := C.inA_of_notcut hf hcf hfy hy
    have hinf' := C.inA_of_notcut hf' hcf' hf'y' hy'
    rw [hag f hinf, hag f' hinf']
    exact hrb _ y y' _ _ hNe hje (C.clo_old hinf) (nold f hnf) (addEdge_inc_old.2 hfy) (C.clo_old hinf')
      (nold f' hnf') (addEdge_inc_old.2 hf'y') (fun h => hff (castSucc_inj' h))

/-- a walk with all four edges inside `A` is not bicoloured -/
theorem side_proj0 (hd : StarOn C.clo 6 d) (hag : ∀ f, C.inA f → c f = d (Fin.castSucc f)) (w : X.Walk4)
    (h1 : C.inA w.e1) (h2 : C.inA w.e2) (h3 : C.inA w.e3) (h4 : C.inA w.e4) : ¬ Bicol c w := by
  intro hb
  let W : (addEdge X C.a1 C.a2).Walk4 :=
    { v0 := w.v0, v1 := w.v1, v2 := w.v2, v3 := w.v3, v4 := w.v4
      e1 := Fin.castSucc w.e1, e2 := Fin.castSucc w.e2, e3 := Fin.castSucc w.e3, e4 := Fin.castSucc w.e4
      h1 := addEdge_joins_old.2 w.h1, h2 := addEdge_joins_old.2 w.h2, h3 := addEdge_joins_old.2 w.h3
      h4 := addEdge_joins_old.2 w.h4
      d01 := w.d01, d02 := w.d02, d03 := w.d03, d12 := w.d12, d13 := w.d13, d14 := w.d14, d23 := w.d23
      d24 := w.d24, d34 := w.d34 }
  apply hd.2 W (C.clo_old h1) (C.clo_old h2) (C.clo_old h3) (C.clo_old h4)
  constructor
  · show d (Fin.castSucc w.e1) = d (Fin.castSucc w.e3)
    rw [← hag _ h1, ← hag _ h3]; exact hb.1
  · show d (Fin.castSucc w.e2) = d (Fin.castSucc w.e4)
    rw [← hag _ h2, ← hag _ h4]; exact hb.2

/-- a walk whose first edge is a cut edge and whose other edges lie inside `A` is not bicoloured -/
theorem side_proj1 (hcub : CubicOn P) (hM : PMOn P M) (hF1 : ¬ M C.e1) (hF2 : ¬ M C.e2)
    (hd : StarOn C.clo 6 d) (hag : ∀ f, C.inA f → c f = d (Fin.castSucc f))
    (hcut : ∀ f, C.isCut f → c f = d (Fin.last X.m)) (w : X.Walk4)
    (hc1 : C.isCut w.e1) (h2 : C.inA w.e2) (h3 : C.inA w.e3) (h4 : C.inA w.e4)
    (n2 : ¬ M w.e2) (n3 : ¬ M w.e3) (n4 : ¬ M w.e4) : ¬ Bicol c w := by
  intro hb
  have hv1 : C.S w.v1 = true := C.side_of_inA h2 w.inc_e2_v1
  -- the other cut edge `e'` with its end `u` in `A`; the new edge joins `u` and `v1`
  have key : ∃ u e', C.isCut e' ∧ X.Inc e' u ∧ ¬ M e' ∧ P e' ∧ u ≠ w.v1 ∧
      (addEdge X C.a1 C.a2).Joins (Fin.last X.m) u w.v1 := by
    rcases C.cutA hc1 w.inc_e1_v1 hv1 with ⟨_, hv⟩ | ⟨_, hv⟩
    · refine ⟨C.a2, C.e2, Or.inr rfl, joins_inc_left C.j2, hF2, C.P2, ?_, ?_⟩
      · rw [hv]; exact Ne.symm C.ha
      · rw [hv]; exact Or.symm addEdge_joins_new
    · refine ⟨C.a1, C.e1, Or.inl rfl, joins_inc_left C.j1, hF1, C.P1, ?_, ?_⟩
      · rw [hv]; exact C.ha
      · rw [hv]; exact addEdge_joins_new
  obtain ⟨u, e', hce', heu, hne', hPe', huv1, hj⟩ := key
  have ne2 : e' ≠ w.e2 := fun h => C.not_inA_of_cut hce' (h ▸ h2)
  have ne3 : e' ≠ w.e3 := fun h => C.not_inA_of_cut hce' (h ▸ h3)
  have ne4 : e' ≠ w.e4 := fun h => C.not_inA_of_cut hce' (h ▸ h4)
  have huv2 : u ≠ w.v2 := by
    intro h
    exact fdeg2 hcub hM hPe' h2.1 h3.1 hne' n2 n3 heu (h ▸ w.inc_e2_v2) (h ▸ w.inc_e3_v2) ne2 ne3 w.e2_ne_e3
  have huv3 : u ≠ w.v3 := by
    intro h
    exact fdeg2 hcub hM hPe' h3.1 h4.1 hne' n3 n4 heu (h ▸ w.inc_e3_v3) (h ▸ w.inc_e4_v3) ne3 ne4 w.e3_ne_e4
  let W : (addEdge X C.a1 C.a2).Walk4 :=
    { v0 := u, v1 := w.v1, v2 := w.v2, v3 := w.v3, v4 := w.v4
      e1 := Fin.last X.m, e2 := Fin.castSucc w.e2, e3 := Fin.castSucc w.e3, e4 := Fin.castSucc w.e4
      h1 := hj, h2 := addEdge_joins_old.2 w.h2, h3 := addEdge_joins_old.2 w.h3, h4 := addEdge_joins_old.2 w.h4
      d01 := huv1, d02 := huv2, d03 := huv3, d12 := w.d12, d13 := w.d13, d14 := w.d14, d23 := w.d23
      d24 := w.d24, d34 := w.d34 }
  apply hd.2 W C.clo_last (C.clo_old h2) (C.clo_old h3) (C.clo_old h4)
  constructor
  · show d (Fin.last X.m) = d (Fin.castSucc w.e3)
    rw [← hcut _ hc1, ← hag _ h3]; exact hb.1
  · show d (Fin.castSucc w.e2) = d (Fin.castSucc w.e4)
    rw [← hag _ h2, ← hag _ h4]; exact hb.2

/-- the colour of the unique F-edge inside `A` at the `A`-end `u` of a cut edge -/
theorem side_r (hcub : CubicOn P) (hM : PMOn P M) (hd : MC5 C.clo (C.cloN M False) d)
    {u : Fin X.n} {e : Fin X.m} (he : C.isCut e) (heu : X.Inc e u) (hnM : ¬ M e) (hPe : P e)
    (hu : C.S u = true) :
    ∃ r, r ≠ d (Fin.last X.m) ∧ r ≠ 5 ∧ ∀ f, C.inA f → ¬ M f → X.Inc f u → d (Fin.castSucc f) = r := by
  classical
  by_cases hex : ∃ f, C.inA f ∧ ¬ M f ∧ X.Inc f u
  · obtain ⟨f0, h0, n0, i0⟩ := hex
    refine ⟨d (Fin.castSucc f0), ?_, ?_, ?_⟩
    · exact hd.1.1 _ _ ⟨castSucc_ne_last f0, u, addEdge_inc_old.2 i0, C.inc_last_of_cut he heu hu⟩
        (C.clo_old h0) C.clo_last
    · intro h5
      exact n0 ((C.cloN_old_iff).1 ((hd.2 _ (C.clo_old h0)).2 h5)).2
    · intro f hf nf hfu
      by_cases hff : f = f0
      · rw [hff]
      · exfalso
        exact fdeg2 hcub hM hf.1 h0.1 hPe nf n0 hnM hfu i0 heu hff
          (fun h => C.not_inA_of_cut he (h ▸ hf)) (fun h => C.not_inA_of_cut he (h ▸ h0))
  · refine ⟨if d (Fin.last X.m) = 0 then 1 else 0, ?_, ?_, ?_⟩
    · by_cases h0 : d (Fin.last X.m) = 0
      · rw [if_pos h0, h0]; decide
      · rw [if_neg h0]; exact Ne.symm h0
    · by_cases h0 : d (Fin.last X.m) = 0
      · rw [if_pos h0]; decide
      · rw [if_neg h0]; decide
    · intro f hf nf hfu
      exact absurd ⟨f, hf, nf, hfu⟩ hex

end side

/-! ## Lemma G2F -/

section g2f
variable {X : MGraph} {P M : Fin X.m → Prop}

/-- the two ends of a cut edge lie on different sides -/
theorem Cut2.cut_sides (C : Cut2 P) {e : Fin X.m} (he : C.isCut e) {u u' : Fin X.n} (hj : X.Joins e u u') :
    (C.S u = true ∧ C.S u' = false) ∨ (C.S u = false ∧ C.S u' = true) := by
  rcases he with rfl | rfl
  · rcases joins_unique hj C.j1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨C.sa1, C.sb1⟩
    · exact Or.inr ⟨C.sb1, C.sa1⟩
  · rcases joins_unique hj C.j2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨C.sa2, C.sb2⟩
    · exact Or.inr ⟨C.sb2, C.sa2⟩

/-- a non-cut edge of `P` has both ends on the same side -/
theorem Cut2.same_side (C : Cut2 P) {f : Fin X.m} (hf : P f) (hnc : ¬ C.isCut f) {x y : Fin X.n}
    (hj : X.Joins f x y) : C.S x = C.S y := by
  rcases C.cases_P hf with h | h | h
  · rw [C.side_of_inA h (joins_inc_left hj), C.side_of_inA h (joins_inc_right hj)]
  · have h1 := C.flip.side_of_inA h (joins_inc_left hj)
    have h2 := C.flip.side_of_inA h (joins_inc_right hj)
    rw [Cut2.flip_S] at h1 h2
    cases hx : C.S x <;> cases hy : C.S y <;> simp_all
  · exact absurd h hnc

theorem Cut2.flip_flip_inA (C : Cut2 P) {f : Fin X.m} : C.flip.flip.inA f ↔ C.inA f := by
  unfold Cut2.inA; simp [Cut2.flip_S]

/-- **Lemma G2F** (fact 1d175e8252f975b1).  Let `P` be a cubic edge set of a loopless multigraph `X`, `M` a perfect
    matching of `P`, and `C` a 2-edge-cut of `P` (sides `A`, `B`, cut edges `e1 = a1 b1`, `e2 = a2 b2`, `a1 ≠ a2`,
    `b1 ≠ b2`) whose cut edges are not in `M`, such that no edge of `M` joins `a1, a2` or `b1, b2`.  If the closure
    `G_A` (with matching `M ∩ E(G[A])`) and the closure `G_B` (with `M ∩ E(G[B])`) have star 6-colourings in which
    these matchings are the colour class `5`, then so does `P` with `M`. -/
theorem g2f (hloop : Loopless X) (hcub : CubicOn P) (hM : PMOn P M) (C : Cut2 P)
    (hF1 : ¬ M C.e1) (hF2 : ¬ M C.e2)
    (hMa : ∀ e, M e → ¬ X.Joins e C.a1 C.a2) (hMb : ∀ e, M e → ¬ X.Joins e C.b1 C.b2)
    (cA : Fin (addEdge X C.a1 C.a2).m → Fin 6) (hA : MC5 C.clo (C.cloN M False) cA)
    (cB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6) (hB : MC5 C.flip.clo (C.flip.cloN M False) cB) :
    ∃ c : Fin X.m → Fin 6, MC5 P M c := by
  classical
  have hlA : Loopless (addEdge X C.a1 C.a2) := addEdge_loopless hloop C.ha
  have hlB : Loopless (addEdge X C.flip.a1 C.flip.a2) := addEdge_loopless hloop C.flip.ha
  have pmA := C.pm_cloF hM hF1 hF2
  have pmB := C.flip.pm_cloF hM hF1 hF2
  have rbA : RB C.clo (C.cloN M False) cA := rb_of_star hlA pmA hA.2 hA.1
  have rbB : RB C.flip.clo (C.flip.cloN M False) cB := rb_of_star hlB pmB hB.2 hB.1
  have hγ : cA (Fin.last X.m) ≠ 5 := fun h => (C.cloN_last_iff).1 ((hA.2 _ C.clo_last).2 h)
  have hγ' : cB (Fin.last X.m) ≠ 5 := fun h => (C.flip.cloN_last_iff).1 ((hB.2 _ C.flip.clo_last).2 h)
  obtain ⟨r1, hr1γ, hr15, hr1⟩ := side_r C cA hcub hM hA (Or.inl rfl) (joins_inc_left C.j1) hF1 C.P1 C.sa1
  obtain ⟨r2, hr2γ, hr25, hr2⟩ := side_r C cA hcub hM hA (Or.inr rfl) (joins_inc_left C.j2) hF2 C.P2 C.sa2
  obtain ⟨x1, hx1γ, hx15, hx1⟩ :=
    side_r C.flip cB hcub hM hB (Or.inl rfl) (joins_inc_left C.flip.j1) hF1 C.P1 C.flip.sa1
  obtain ⟨x2, hx2γ, hx25, hx2⟩ :=
    side_r C.flip cB hcub hM hB (Or.inr rfl) (joins_inc_left C.flip.j2) hF2 C.P2 C.flip.sa2
  obtain ⟨σ, hσi, hσ5, hσγ, s11, s12, s21, s22⟩ :=
    perm_g2f _ _ r1 r2 x1 x2 hγ hγ' hr1γ hr15 hr2γ hr25 hx1γ hx15 hx2γ hx25
  -- the glued colouring
  let c : Fin X.m → Fin 6 := fun f =>
    if C.S (X.ends f).1 = C.S (X.ends f).2 then
      (if C.S (X.ends f).1 = true then cA (Fin.castSucc f) else σ (cB (Fin.castSucc f)))
    else cA (Fin.last X.m)
  have hagA : ∀ f, C.inA f → c f = cA (Fin.castSucc f) := by
    intro f hf
    have e1 : C.S (X.ends f).1 = C.S (X.ends f).2 := hf.2.1.trans hf.2.2.symm
    simp only [c, if_pos e1, if_pos hf.2.1]
  have hagB : ∀ f, C.flip.inA f → c f = σ (cB (Fin.castSucc f)) := by
    intro f hf
    have h1 : C.S (X.ends f).1 = false := by have := hf.2.1; rw [Cut2.flip_S] at this; simpa using this
    have h2 : C.S (X.ends f).2 = false := by have := hf.2.2; rw [Cut2.flip_S] at this; simpa using this
    have e1 : C.S (X.ends f).1 = C.S (X.ends f).2 := h1.trans h2.symm
    have e2 : ¬ C.S (X.ends f).1 = true := by rw [h1]; decide
    simp only [c, if_pos e1, if_neg e2]
  have hcutA : ∀ f, C.isCut f → c f = cA (Fin.last X.m) := by
    intro f hf
    have hne : ¬ C.S (X.ends f).1 = C.S (X.ends f).2 := by
      rcases C.cut_sides hf (joins_ends f) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
    simp only [c, if_neg hne]
  have hcutB : ∀ f, C.flip.isCut f → c f = σ (cB (Fin.last X.m)) := by
    intro f hf; rw [hσγ]; exact hcutA f hf
  -- the side colouring of `B` after the permutation
  let dB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6 := fun i => σ (cB i)
  have hdB : StarOn C.flip.clo 6 dB := starOn_map σ hσi hB.1
  have hσ5' : ∀ y, σ y = 5 ↔ y = 5 := fun y => ⟨fun h => hσi _ _ (h.trans hσ5.symm), fun h => h ▸ hσ5⟩
  have rbB' : RB C.flip.clo (C.flip.cloN M False) dB := by
    intro e y y' f f' h1 h2 h3 h4 h5 h6 h7 h8 h9 heq
    exact rbB e y y' f f' h1 h2 h3 h4 h5 h6 h7 h8 h9 (hσi _ _ heq)
  -- classification of the edges of `P`
  have hclass : ∀ f, P f → (M f ↔ c f = 5) := by
    intro f hf
    rcases C.cases_P hf with h | h | h
    · rw [hagA f h, ← (hA.2 _ (C.clo_old h)), C.cloN_old_iff]
      exact ⟨fun hm => ⟨h, hm⟩, fun hm => hm.2⟩
    · rw [hagB f h, hσ5', ← (hB.2 _ (C.flip.clo_old h)), C.flip.cloN_old_iff]
      exact ⟨fun hm => ⟨h, hm⟩, fun hm => hm.2⟩
    · rw [hcutA f h]
      constructor
      · intro hm; exact absurd hm (h.elim (fun h' => h' ▸ hF1) (fun h' => h' ▸ hF2))
      · intro h5; exact absurd h5 hγ
  -- the edges across a cut edge
  have across : ∀ e u u' f f', C.isCut e → X.Joins e u u' → P f → ¬ M f → ¬ C.isCut f → X.Inc f u →
      P f' → ¬ M f' → ¬ C.isCut f' → X.Inc f' u' → c f ≠ c f' := by
    intro e u u' f f' he hj hf nf cf hfu hf' nf' cf' hf'u'
    rcases C.cut_sides he hj with ⟨hu, hu'⟩ | ⟨hu, hu'⟩
    · have hinA := C.inA_of_notcut hf cf hfu hu
      have hu'B : C.flip.S u' = true := by rw [Cut2.flip_S, hu']; rfl
      have hinB := C.flip.inA_of_notcut hf' cf' hf'u' hu'B
      rw [hagA f hinA, hagB f' hinB]
      rcases C.cutA he (joins_inc_left hj) hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hu'1 : u' = C.b1 := by
          rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h C.a1_ne_b1
        subst hu'1
        rw [hr1 f hinA nf hfu, hx1 f' hinB nf' hf'u']; exact Ne.symm s11
      · have hu'2 : u' = C.b2 := by
          rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h C.a2_ne_b2
        subst hu'2
        rw [hr2 f hinA nf hfu, hx2 f' hinB nf' hf'u']; exact Ne.symm s22
    · have huB : C.flip.S u = true := by rw [Cut2.flip_S, hu]; rfl
      have hinB := C.flip.inA_of_notcut hf cf hfu huB
      have hinA := C.inA_of_notcut hf' cf' hf'u' hu'
      rw [hagB f hinB, hagA f' hinA]
      rcases C.cutA he (joins_inc_right hj) hu' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hu1 : u = C.b1 := by
          rcases joins_unique hj C.j1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h C.a1_ne_b1
          · exact h
        subst hu1
        rw [hr1 f' hinA nf' hf'u', hx1 f hinB nf hfu]; exact s11
      · have hu2 : u = C.b2 := by
          rcases joins_unique hj C.j2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h C.a2_ne_b2
          · exact h
        subst hu2
        rw [hr2 f' hinA nf' hf'u', hx2 f hinB nf hfu]; exact s22
  -- an F-edge next to a cut edge does not have the cut colour
  have nextcut : ∀ e u f, C.isCut e → X.Inc e u → P f → ¬ M f → ¬ C.isCut f → X.Inc f u →
      c f ≠ cA (Fin.last X.m) := by
    intro e u f he heu hf nf cf hfu
    cases hu : C.S u
    · have huB : C.flip.S u = true := by rw [Cut2.flip_S, hu]; rfl
      have hinB := C.flip.inA_of_notcut hf cf hfu huB
      rw [hagB f hinB, ← hσγ]
      intro h
      have h' := hσi _ _ h
      rcases C.flip.cutA he heu huB with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hx1γ ((hx1 f hinB nf hfu).symm.trans h')
      · exact hx2γ ((hx2 f hinB nf hfu).symm.trans h')
    · have hinA := C.inA_of_notcut hf cf hfu hu
      rw [hagA f hinA]
      rcases C.cutA he heu hu with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rw [hr1 f hinA nf hfu]; exact hr1γ
      · rw [hr2 f hinA nf hfu]; exact hr2γ
  refine ⟨c, star_of_rabc hM hclass ?_ ?_ ?_, hclass⟩
  · -- (A)
    intro a b hab ha hb _ _
    obtain ⟨hne, x, hax, hbx⟩ := hab
    cases hs : C.S x
    · have hs' : C.flip.S x = true := by rw [Cut2.flip_S, hs]; rfl
      exact side_prop C.flip dB c hdB hagB hcutB hne hax hbx hs' ha hb
    · exact side_prop C cA c hA.1 hagA hcutA hne hax hbx hs ha hb
  · -- (B)
    intro e y y' f f' he hj hf nf hfy hf' nf' hf'y' hff
    have hnc : ¬ C.isCut e := fun h => h.elim (fun h' => hF1 (h' ▸ he)) (fun h' => hF2 (h' ▸ he))
    rcases C.cases_P (hM.1 e he) with hin | hin | hin
    · exact side_rb C cA c rbA hagA hcutA hMa he hin hj hf nf hfy hf' nf' hf'y' hff
    · exact side_rb C.flip dB c rbB' hagB hcutB hMb he hin hj hf nf hfy hf' nf' hf'y' hff
    · exact absurd hin hnc
  · -- (C)
    intro w h1 h2 h3 h4 n1 n2 n3 n4 hb
    have ncut : ∀ f, M f → ¬ C.isCut f := fun f hm h => h.elim (fun h' => hF1 (h' ▸ hm)) (fun h' => hF2 (h' ▸ hm))
    by_cases c2 : C.isCut w.e2
    · have c1 : ¬ C.isCut w.e1 := fun h => C.cut_disj h c2 w.e1_ne_e2 w.inc_e1_v1 w.inc_e2_v1
      have c3 : ¬ C.isCut w.e3 := fun h => C.cut_disj c2 h w.e2_ne_e3 w.inc_e2_v2 w.inc_e3_v2
      exact across _ _ _ _ _ c2 w.h2 h1 n1 c1 w.inc_e1_v1 h3 n3 c3 w.inc_e3_v2 hb.1
    by_cases c3 : C.isCut w.e3
    · have c4 : ¬ C.isCut w.e4 := fun h => C.cut_disj c3 h w.e3_ne_e4 w.inc_e3_v3 w.inc_e4_v3
      exact across _ _ _ _ _ c3 w.h3 h2 n2 c2 w.inc_e2_v2 h4 n4 c4 w.inc_e4_v3 hb.2
    have s12 : C.S w.v1 = C.S w.v2 := C.same_side h2 c2 w.h2
    have s23 : C.S w.v2 = C.S w.v3 := C.same_side h3 c3 w.h3
    by_cases c1 : C.isCut w.e1 <;> by_cases c4 : C.isCut w.e4
    · -- both end edges are cut edges: e3 is next to the cut edge e4
      have hne := nextcut _ _ _ c4 w.inc_e4_v3 h3 n3 c3 w.inc_e3_v3
      rw [← hb.1, hcutA _ c1] at hne
      exact hne rfl
    · -- only the first edge is a cut edge
      cases hs : C.S w.v1
      · have hs' : ∀ v, C.S v = false → C.flip.S v = true := fun v hv => by rw [Cut2.flip_S, hv]; rfl
        have i2 := C.flip.inA_of_notcut h2 c2 w.inc_e2_v1 (hs' _ hs)
        have i3 := C.flip.inA_of_notcut h3 c3 w.inc_e3_v2 (hs' _ (s12 ▸ hs))
        have i4 := C.flip.inA_of_notcut h4 c4 w.inc_e4_v3 (hs' _ (s23 ▸ s12 ▸ hs))
        exact side_proj1 C.flip dB c hcub hM hF1 hF2 hdB hagB hcutB w c1 i2 i3 i4 n2 n3 n4 hb
      · have i2 := C.inA_of_notcut h2 c2 w.inc_e2_v1 hs
        have i3 := C.inA_of_notcut h3 c3 w.inc_e3_v2 (s12 ▸ hs)
        have i4 := C.inA_of_notcut h4 c4 w.inc_e4_v3 (s23 ▸ s12 ▸ hs)
        exact side_proj1 C cA c hcub hM hF1 hF2 hA.1 hagA hcutA w c1 i2 i3 i4 n2 n3 n4 hb
    · -- only the last edge is a cut edge: read the walk backwards
      have hbr : Bicol c w.reverse := bicol_rev w hb
      cases hs : C.S w.v1
      · have hs' : ∀ v, C.S v = false → C.flip.S v = true := fun v hv => by rw [Cut2.flip_S, hv]; rfl
        have i1 := C.flip.inA_of_notcut h1 c1 w.inc_e1_v1 (hs' _ hs)
        have i2 := C.flip.inA_of_notcut h2 c2 w.inc_e2_v1 (hs' _ hs)
        have i3 := C.flip.inA_of_notcut h3 c3 w.inc_e3_v2 (hs' _ (s12 ▸ hs))
        exact side_proj1 C.flip dB c hcub hM hF1 hF2 hdB hagB hcutB w.reverse c4 i3 i2 i1 n3 n2 n1 hbr
      · have i1 := C.inA_of_notcut h1 c1 w.inc_e1_v1 hs
        have i2 := C.inA_of_notcut h2 c2 w.inc_e2_v1 hs
        have i3 := C.inA_of_notcut h3 c3 w.inc_e3_v2 (s12 ▸ hs)
        exact side_proj1 C cA c hcub hM hF1 hF2 hA.1 hagA hcutA w.reverse c4 i3 i2 i1 n3 n2 n1 hbr
    · -- no cut edge
      cases hs : C.S w.v1
      · have hs' : ∀ v, C.S v = false → C.flip.S v = true := fun v hv => by rw [Cut2.flip_S, hv]; rfl
        have i1 := C.flip.inA_of_notcut h1 c1 w.inc_e1_v1 (hs' _ hs)
        have i2 := C.flip.inA_of_notcut h2 c2 w.inc_e2_v1 (hs' _ hs)
        have i3 := C.flip.inA_of_notcut h3 c3 w.inc_e3_v2 (hs' _ (s12 ▸ hs))
        have i4 := C.flip.inA_of_notcut h4 c4 w.inc_e4_v3 (hs' _ (s23 ▸ s12 ▸ hs))
        exact side_proj0 C.flip dB c hdB hagB w i1 i2 i3 i4 hb
      · have i1 := C.inA_of_notcut h1 c1 w.inc_e1_v1 hs
        have i2 := C.inA_of_notcut h2 c2 w.inc_e2_v1 hs
        have i3 := C.inA_of_notcut h3 c3 w.inc_e3_v2 (s12 ▸ hs)
        have i4 := C.inA_of_notcut h4 c4 w.inc_e4_v3 (s23 ▸ s12 ▸ hs)
        exact side_proj0 C cA c hA.1 hagA w i1 i2 i3 i4 hb

end g2f

end RH2F

-- ===== from RH2G2M.lean =====
/-
  RH2G2M.lean — Lemma G2M (fact 90755fcae2fca4e1) in Lean 4.20 core: gluing MC-colourings across a 2-edge-cut
  whose two cut edges are matching edges.
-/

namespace RH2F
open MGraph

/-! ## The colour permutation of G2M -/

/-- permutations of `{0,…,4}` as image lists, extended by `5 ↦ 5` -/
def p5L : List (List Nat) :=
  [[0,1,2,3,4],[0,1,2,4,3],[0,1,3,2,4],[0,1,3,4,2],[0,1,4,2,3],[0,1,4,3,2],[0,2,1,3,4],[0,2,1,4,3],[0,2,3,1,4],
   [0,2,3,4,1],[0,2,4,1,3],[0,2,4,3,1],[0,3,1,2,4],[0,3,1,4,2],[0,3,2,1,4],[0,3,2,4,1],[0,3,4,1,2],[0,3,4,2,1],
   [0,4,1,2,3],[0,4,1,3,2],[0,4,2,1,3],[0,4,2,3,1],[0,4,3,1,2],[0,4,3,2,1],[1,0,2,3,4],[1,0,2,4,3],[1,0,3,2,4],
   [1,0,3,4,2],[1,0,4,2,3],[1,0,4,3,2],[1,2,0,3,4],[1,2,0,4,3],[1,2,3,0,4],[1,2,3,4,0],[1,2,4,0,3],[1,2,4,3,0],
   [1,3,0,2,4],[1,3,0,4,2],[1,3,2,0,4],[1,3,2,4,0],[1,3,4,0,2],[1,3,4,2,0],[1,4,0,2,3],[1,4,0,3,2],[1,4,2,0,3],
   [1,4,2,3,0],[1,4,3,0,2],[1,4,3,2,0],[2,0,1,3,4],[2,0,1,4,3],[2,0,3,1,4],[2,0,3,4,1],[2,0,4,1,3],[2,0,4,3,1],
   [2,1,0,3,4],[2,1,0,4,3],[2,1,3,0,4],[2,1,3,4,0],[2,1,4,0,3],[2,1,4,3,0],[2,3,0,1,4],[2,3,0,4,1],[2,3,1,0,4],
   [2,3,1,4,0],[2,3,4,0,1],[2,3,4,1,0],[2,4,0,1,3],[2,4,0,3,1],[2,4,1,0,3],[2,4,1,3,0],[2,4,3,0,1],[2,4,3,1,0],
   [3,0,1,2,4],[3,0,1,4,2],[3,0,2,1,4],[3,0,2,4,1],[3,0,4,1,2],[3,0,4,2,1],[3,1,0,2,4],[3,1,0,4,2],[3,1,2,0,4],
   [3,1,2,4,0],[3,1,4,0,2],[3,1,4,2,0],[3,2,0,1,4],[3,2,0,4,1],[3,2,1,0,4],[3,2,1,4,0],[3,2,4,0,1],[3,2,4,1,0],
   [3,4,0,1,2],[3,4,0,2,1],[3,4,1,0,2],[3,4,1,2,0],[3,4,2,0,1],[3,4,2,1,0],[4,0,1,2,3],[4,0,1,3,2],[4,0,2,1,3],
   [4,0,2,3,1],[4,0,3,1,2],[4,0,3,2,1],[4,1,0,2,3],[4,1,0,3,2],[4,1,2,0,3],[4,1,2,3,0],[4,1,3,0,2],[4,1,3,2,0],
   [4,2,0,1,3],[4,2,0,3,1],[4,2,1,0,3],[4,2,1,3,0],[4,2,3,0,1],[4,2,3,1,0],[4,3,0,1,2],[4,3,0,2,1],[4,3,1,0,2],
   [4,3,1,2,0],[4,3,2,0,1],[4,3,2,1,0]]

def ap5 (l : List Nat) (x : Fin 6) : Fin 6 :=
  if x.val = 5 then x else ⟨l.getD x.val 0 % 6, Nat.mod_lt _ (by decide)⟩

def all5 (p : Fin 6 → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4

theorem all5_sound {p : Fin 6 → Bool} (h : all5 p = true) : ∀ x, x ≠ 5 → p x = true := by
  simp only [all5, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  intro x h5
  rcases fin6_cases x with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | assumption | exact absurd rfl h5

def p5Chk : Bool := p5L.all fun l =>
  ap5 l 5 == 5 && all6 fun x => all6 fun y => !(ap5 l x == ap5 l y) || x == y

theorem p5Chk_ok : p5Chk = true := by decide +kernel

theorem p5_props {l : List Nat} (hl : l ∈ p5L) : ap5 l 5 = 5 ∧ ∀ x y, ap5 l x = ap5 l y → x = y := by
  have h := List.all_eq_true.1 p5Chk_ok l hl
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h5, hi⟩ := h
  refine ⟨h5, fun x y hxy => ?_⟩
  have := all6_sound (all6_sound hi x) y
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd hxy h
  · exact h

/-- the normalised G2M problem: `S1 = T1 = {0, 1}` -/
def g2mChk : Bool := all5 fun s2 => all5 fun s2' => all5 fun t2 => all5 fun t2' =>
  s2 == s2' || t2 == t2' || (s2 == 0 && s2' == 1) || (s2 == 1 && s2' == 0) || (t2 == 0 && t2' == 1) ||
  (t2 == 1 && t2' == 0) ||
  p5L.any fun l => ap5 l 0 != 0 && ap5 l 0 != 1 && ap5 l 1 != 0 && ap5 l 1 != 1 &&
    ap5 l t2 != s2 && ap5 l t2 != s2' && ap5 l t2' != s2 && ap5 l t2' != s2'

theorem g2mChk_ok : g2mChk = true := by decide +kernel

theorem swap_norm_chk : all6 (fun a => all6 fun b =>
    a == 5 || b == 5 || a == b ||
    (swapc (swapc a 0 b) 1 (swapc a 0 a) == 0 && swapc (swapc a 0 b) 1 (swapc a 0 b) == 1 &&
     swapc (swapc a 0 b) 1 (swapc a 0 5) == 5)) = true := by decide +kernel

/-- a colour permutation fixing `5` that sends `a ↦ 0`, `b ↦ 1`, with its inverse -/
theorem norm_perm {a b : Fin 6} (ha : a ≠ 5) (hb : b ≠ 5) (hab : a ≠ b) :
    ∃ α α' : Fin 6 → Fin 6, (∀ x, α' (α x) = x) ∧ (∀ x, α (α' x) = x) ∧ α 5 = 5 ∧ α a = 0 ∧ α b = 1 := by
  have h := all6_sound (all6_sound swap_norm_chk a) b
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | ⟨⟨h0, h1⟩, h5⟩
  · exact absurd h ha
  · exact absurd h hb
  · exact absurd h hab
  · refine ⟨fun x => swapc (swapc a 0 b) 1 (swapc a 0 x), fun x => swapc a 0 (swapc (swapc a 0 b) 1 x),
      fun x => by simp only [swapc_invol], fun x => by simp only [swapc_invol], h5, h0, h1⟩

theorem inj_of_linv {α α' : Fin 6 → Fin 6} (h : ∀ x, α' (α x) = x) : ∀ x y, α x = α y → x = y :=
  fun x y hxy => by rw [← h x, hxy, h y]

/-- **the colour permutation of G2M** (the permutation lemma of fact 90755fcae2fca4e1): for 2-sets
    `S_i = {s_i, s_i'}`, `T_i = {t_i, t_i'}` of colours `≠ 5` with `S1 ≠ S2` and `T1 ≠ T2` (as sets), there is a
    permutation `σ` fixing `5` with `σ(T1) ∩ S1 = ∅` and `σ(T2) ∩ S2 = ∅`. -/
theorem perm_g2m (s1 s1' s2 s2' t1 t1' t2 t2' : Fin 6)
    (h1 : s1 ≠ 5) (h1' : s1' ≠ 5) (h2 : s2 ≠ 5) (h2' : s2' ≠ 5)
    (k1 : t1 ≠ 5) (k1' : t1' ≠ 5) (k2 : t2 ≠ 5) (k2' : t2' ≠ 5)
    (hs1 : s1 ≠ s1') (hs2 : s2 ≠ s2') (ht1 : t1 ≠ t1') (ht2 : t2 ≠ t2')
    (hS : ¬ (s1 = s2 ∧ s1' = s2') ∧ ¬ (s1 = s2' ∧ s1' = s2))
    (hT : ¬ (t1 = t2 ∧ t1' = t2') ∧ ¬ (t1 = t2' ∧ t1' = t2)) :
    ∃ σ : Fin 6 → Fin 6, (∀ x y, σ x = σ y → x = y) ∧ σ 5 = 5 ∧
      σ t1 ≠ s1 ∧ σ t1 ≠ s1' ∧ σ t1' ≠ s1 ∧ σ t1' ≠ s1' ∧
      σ t2 ≠ s2 ∧ σ t2 ≠ s2' ∧ σ t2' ≠ s2 ∧ σ t2' ≠ s2' := by
  obtain ⟨α, α', hαα, hα'α, hα5, hαs1, hαs1'⟩ := norm_perm h1 h1' hs1
  obtain ⟨β, β', hββ, _, hβ5, hβt1, hβt1'⟩ := norm_perm k1 k1' ht1
  have αi := inj_of_linv hαα
  have βi := inj_of_linv hββ
  have ne5α : ∀ x, x ≠ 5 → α x ≠ 5 := fun x hx h => hx (αi _ _ (h.trans hα5.symm))
  have ne5β : ∀ x, x ≠ 5 → β x ≠ 5 := fun x hx h => hx (βi _ _ (h.trans hβ5.symm))
  have h := all5_sound (all5_sound (all5_sound (all5_sound g2mChk_ok (α s2) (ne5α _ h2)) (α s2') (ne5α _ h2'))
    (β t2) (ne5β _ k2)) (β t2') (ne5β _ k2')
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  have nS : ¬ (α s2 = 0 ∧ α s2' = 1) ∧ ¬ (α s2 = 1 ∧ α s2' = 0) := by
    refine ⟨fun h => hS.1 ⟨?_, ?_⟩, fun h => hS.2 ⟨?_, ?_⟩⟩
    · exact αi _ _ (hαs1.trans h.1.symm)
    · exact αi _ _ (hαs1'.trans h.2.symm)
    · exact αi _ _ (hαs1.trans h.2.symm)
    · exact αi _ _ (hαs1'.trans h.1.symm)
  have nT : ¬ (β t2 = 0 ∧ β t2' = 1) ∧ ¬ (β t2 = 1 ∧ β t2' = 0) := by
    refine ⟨fun h => hT.1 ⟨?_, ?_⟩, fun h => hT.2 ⟨?_, ?_⟩⟩
    · exact βi _ _ (hβt1.trans h.1.symm)
    · exact βi _ _ (hβt1'.trans h.2.symm)
    · exact βi _ _ (hβt1.trans h.2.symm)
    · exact βi _ _ (hβt1'.trans h.1.symm)
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact absurd (αi _ _ h) hs2
  · exact absurd (βi _ _ h) ht2
  · exact absurd h nS.1
  · exact absurd h nS.2
  · exact absurd h nT.1
  · exact absurd h nT.2
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

/-! ## Side lemmas for an M-type cut -/

section sideM
variable {X : MGraph} {P M : Fin X.m → Prop}

/-- an edge incident with two distinct vertices joins them -/
theorem joins_of_inc2 {f : Fin X.m} {x y : Fin X.n} (hx : X.Inc f x) (hy : X.Inc f y) (hxy : x ≠ y) :
    X.Joins f x y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.symm.trans hy) hxy
  · exact Or.inl (by rw [← hx, ← hy])
  · exact Or.inr (by rw [← hx, ← hy])
  · exact absurd (hx.symm.trans hy) hxy

/-- the closure matching of an M-type cut is a perfect matching of the closure -/
theorem Cut2.pm_cloM (C : Cut2 P) (hM : PMOn P M) (hM1 : M C.e1) (hM2 : M C.e2) :
    PMOn C.clo (C.cloN M True) := by
  constructor
  · intro i hi
    rcases hi with ⟨rfl, _⟩ | ⟨d, rfl, hd, _⟩
    · exact C.clo_last
    · exact C.clo_old hd
  · intro x ⟨i, hi, hix⟩
    by_cases hx : x = C.a1 ∨ x = C.a2
    · refine ⟨Fin.last X.m, Or.inl ⟨rfl, trivial⟩, (C.inc_new_iff).2 hx, ?_⟩
      intro j hj hjx
      rcases hj with ⟨rfl, _⟩ | ⟨d, rfl, hd, hdM⟩
      · rfl
      · exfalso
        have hdx : X.Inc d x := addEdge_inc_old.1 hjx
        rcases hx with rfl | rfl
        · exact C.not_inA_of_cut (Or.inl (pm_unique hM hdM hM1 hdx (joins_inc_left C.j1))) hd
        · exact C.not_inA_of_cut (Or.inr (pm_unique hM hdM hM2 hdx (joins_inc_left C.j2))) hd
    · have hxA : C.S x = true ∧ ∃ f, P f ∧ X.Inc f x := by
        rcases hi with rfl | ⟨d, rfl, hd⟩
        · exact absurd ((C.inc_new_iff).1 hix) hx
        · have hix' : X.Inc d x := addEdge_inc_old.1 hix
          exact ⟨C.side_of_inA hd hix', d, hd.1, hix'⟩
      obtain ⟨a, ha, hax, hu⟩ := hM.2 x hxA.2
      have hnc : ¬ C.isCut a := by
        intro h
        rcases C.cutA h hax hxA.1 with ⟨_, h'⟩ | ⟨_, h'⟩
        · exact hx (Or.inl h')
        · exact hx (Or.inr h')
      have hainA : C.inA a := C.inA_of_notcut (hM.1 a ha) hnc hax hxA.1
      refine ⟨Fin.castSucc a, Or.inr ⟨a, rfl, hainA, ha⟩, addEdge_inc_old.2 hax, ?_⟩
      intro j hj hjx
      rcases hj with ⟨rfl, _⟩ | ⟨d, rfl, _, hdM⟩
      · exact absurd ((C.inc_new_iff).1 hjx) hx
      · rw [hu d hdM (addEdge_inc_old.1 hjx)]

/-- at the `A`-end `u` of a cut edge `e ∈ M` there are exactly two F-edges, both inside `A` -/
theorem Cut2.two_F (C : Cut2 P) (hcub : CubicOn P) (hM : PMOn P M) {e : Fin X.m} {u : Fin X.n}
    (he : C.isCut e) (heM : M e) (heu : X.Inc e u) (hu : C.S u = true) :
    ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ ¬ M f ∧ ¬ M f' ∧ X.Inc f u ∧ X.Inc f' u ∧
      ∀ g, P g → ¬ M g → X.Inc g u → g = f ∨ g = f' := by
  have hPe : P e := hM.1 e heM
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub u ⟨e, hPe, heu⟩
  -- a canonical form: `e` and two further distinct edges `f f'` covering all edges at `u`
  have canon : ∀ f f', P f → P f' → X.Inc f u → X.Inc f' u → f ≠ f' → e ≠ f → e ≠ f' →
      (∀ g, P g → X.Inc g u → g = e ∨ g = f ∨ g = f') →
      ∃ f f', f ≠ f' ∧ C.inA f ∧ C.inA f' ∧ ¬ M f ∧ ¬ M f' ∧ X.Inc f u ∧ X.Inc f' u ∧
        ∀ g, P g → ¬ M g → X.Inc g u → g = f ∨ g = f' := by
    intro f f' hf hf' hfu hf'u hff hef hef' hcov
    have nM : ∀ g, X.Inc g u → e ≠ g → ¬ M g := fun g hg hne hm => hne (pm_unique hM heM hm heu hg)
    have nc : ∀ g, X.Inc g u → e ≠ g → ¬ C.isCut g := by
      intro g hg hne hcg
      exact C.cut_disj he hcg hne heu hg
    refine ⟨f, f', hff, C.inA_of_notcut hf (nc f hfu hef) hfu hu, C.inA_of_notcut hf' (nc f' hf'u hef') hf'u hu,
      nM f hfu hef, nM f' hf'u hef', hfu, hf'u, ?_⟩
    intro g hg hgM hgu
    rcases hcov g hg hgu with h | h | h
    · exact absurd (h ▸ heM) hgM
    · exact Or.inl h
    · exact Or.inr h
  rcases hall e hPe heu with rfl | rfl | rfl
  · exact canon q r hq hr iq ir dqr dpq dpr hall
  · refine canon p r hp hr ip ir dpr (Ne.symm dpq) dqr ?_
    intro g hg hgu
    rcases hall g hg hgu with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · refine canon p q hp hq ip iq dpq (Ne.symm dpr) (Ne.symm dqr) ?_
    intro g hg hgu
    rcases hall g hg hgu with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

variable (C : Cut2 P) (d : Fin (addEdge X C.a1 C.a2).m → Fin 6) (c : Fin X.m → Fin 6)

/-- condition (B) at a matching edge inside side `A` of an M-type cut -/
theorem side_rbM (hM1 : M C.e1) (hM2 : M C.e2) (hrb : RB C.clo (C.cloN M True) d)
    (hag : ∀ f, C.inA f → c f = d (Fin.castSucc f))
    {e : Fin X.m} {y y' : Fin X.n} (he : M e) (hin : C.inA e) (hj : X.Joins e y y')
    {f f' : Fin X.m} (hf : P f) (hnf : ¬ M f) (hfy : X.Inc f y) (hf' : P f') (hnf' : ¬ M f')
    (hf'y' : X.Inc f' y') (hff : f ≠ f') : c f ≠ c f' := by
  have hy : C.S y = true := C.side_of_inA hin (joins_inc_left hj)
  have hy' : C.S y' = true := C.side_of_inA hin (joins_inc_right hj)
  have nc : ∀ g, ¬ M g → ¬ C.isCut g := fun g hg h => h.elim (fun h' => hg (h' ▸ hM1)) (fun h' => hg (h' ▸ hM2))
  have hinf := C.inA_of_notcut hf (nc f hnf) hfy hy
  have hinf' := C.inA_of_notcut hf' (nc f' hnf') hf'y' hy'
  rw [hag f hinf, hag f' hinf']
  exact hrb _ y y' _ _ ((C.cloN_old_iff).2 ⟨hin, he⟩) (addEdge_joins_old.2 hj) (C.clo_old hinf)
    (fun h => hnf ((C.cloN_old_iff).1 h).2) (addEdge_inc_old.2 hfy) (C.clo_old hinf')
    (fun h => hnf' ((C.cloN_old_iff).1 h).2) (addEdge_inc_old.2 hf'y') (fun h => hff (castSucc_inj' h))

/-- the two F-colour sets at `a1` and at `a2` are not equal (fact 90755fcae2fca4e1, Claim) -/
theorem side_sets (hrb : RB C.clo (C.cloN M True) d)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    {f1 f1' f2 f2' : Fin X.m} (d1 : f1 ≠ f1') (i1 : C.inA f1) (i1' : C.inA f1') (i2 : C.inA f2) (i2' : C.inA f2')
    (n1 : ¬ M f1) (n1' : ¬ M f1') (n2 : ¬ M f2) (n2' : ¬ M f2')
    (a1 : X.Inc f1 C.a1) (a1' : X.Inc f1' C.a1) (a2 : X.Inc f2 C.a2) (a2' : X.Inc f2' C.a2) :
    ¬ (d (Fin.castSucc f1) = d (Fin.castSucc f2) ∧ d (Fin.castSucc f1') = d (Fin.castSucc f2')) ∧
    ¬ (d (Fin.castSucc f1) = d (Fin.castSucc f2') ∧ d (Fin.castSucc f1') = d (Fin.castSucc f2)) := by
  have nN : ∀ g, ¬ M g → ¬ C.cloN M True (Fin.castSucc g) := fun g hg h => hg ((C.cloN_old_iff).1 h).2
  -- (B) at the new matching edge `g_A`: equal colours at `a1`, `a2` force equal edges
  have same : ∀ g g', C.inA g → C.inA g' → ¬ M g → ¬ M g' → X.Inc g C.a1 → X.Inc g' C.a2 →
      d (Fin.castSucc g) = d (Fin.castSucc g') → g = g' := by
    intro g g' ig ig' ng ng' ga ga' heq
    apply Classical.byContradiction
    intro hne
    exact hrb (Fin.last X.m) C.a1 C.a2 _ _ ((C.cloN_last_iff).2 trivial) addEdge_joins_new (C.clo_old ig) (nN g ng)
      (addEdge_inc_old.2 ga) (C.clo_old ig') (nN g' ng') (addEdge_inc_old.2 ga') (fun h => hne (castSucc_inj' h)) heq
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := same _ _ i1 i2 n1 n2 a1 a2 h1
    have e2 := same _ _ i1' i2' n1' n2' a1' a2' h2
    subst e1; subst e2
    exact d1 (hpa _ _ i1.1 i1'.1 (joins_of_inc2 a1 a2 C.ha) (joins_of_inc2 a1' a2' C.ha))
  · rintro ⟨h1, h2⟩
    have e1 := same _ _ i1 i2' n1 n2' a1 a2' h1
    have e2 := same _ _ i1' i2 n1' n2 a1' a2 h2
    subst e1; subst e2
    exact d1 (hpa _ _ i1.1 i1'.1 (joins_of_inc2 a1 a2' C.ha) (joins_of_inc2 a1' a2 C.ha))

end sideM

/-! ## Lemma G2M -/

section g2m
variable {X : MGraph} {P M : Fin X.m → Prop}

/-- **Lemma G2M** (fact 90755fcae2fca4e1).  Let `P` be a cubic edge set of a loopless multigraph `X`, `M` a perfect
    matching of `P`, and `C` a 2-edge-cut of `P` whose two cut edges lie in `M`, such that at most one edge of `P`
    joins `a1, a2` and at most one joins `b1, b2`.  If the closures `G_A`, `G_B` with the matchings
    `(M ∩ E(G[A])) ∪ {g_A}` and `(M ∩ E(G[B])) ∪ {g_B}` have star 6-colourings in which these matchings are the
    colour class `5`, then so does `P` with `M`. -/
theorem g2m (hloop : Loopless X) (hcub : CubicOn P) (hM : PMOn P M) (C : Cut2 P)
    (hM1 : M C.e1) (hM2 : M C.e2)
    (hpa : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f')
    (hpb : ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f')
    (cA : Fin (addEdge X C.a1 C.a2).m → Fin 6) (hA : MC5 C.clo (C.cloN M True) cA)
    (cB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6) (hB : MC5 C.flip.clo (C.flip.cloN M True) cB) :
    ∃ c : Fin X.m → Fin 6, MC5 P M c := by
  classical
  have hlA : Loopless (addEdge X C.a1 C.a2) := addEdge_loopless hloop C.ha
  have hlB : Loopless (addEdge X C.flip.a1 C.flip.a2) := addEdge_loopless hloop C.flip.ha
  have pmA := C.pm_cloM hM hM1 hM2
  have pmB := C.flip.pm_cloM hM hM1 hM2
  have rbA : RB C.clo (C.cloN M True) cA := rb_of_star hlA pmA hA.2 hA.1
  have rbB : RB C.flip.clo (C.flip.cloN M True) cB := rb_of_star hlB pmB hB.2 hB.1
  have hA5 : cA (Fin.last X.m) = 5 := (hA.2 _ C.clo_last).1 ((C.cloN_last_iff).2 trivial)
  have hB5 : cB (Fin.last X.m) = 5 := (hB.2 _ C.flip.clo_last).1 ((C.flip.cloN_last_iff).2 trivial)
  have ne5A : ∀ f, C.inA f → ¬ M f → cA (Fin.castSucc f) ≠ 5 :=
    fun f hf hn h => hn ((C.cloN_old_iff).1 ((hA.2 _ (C.clo_old hf)).2 h)).2
  have ne5B : ∀ f, C.flip.inA f → ¬ M f → cB (Fin.castSucc f) ≠ 5 :=
    fun f hf hn h => hn ((C.flip.cloN_old_iff).1 ((hB.2 _ (C.flip.clo_old hf)).2 h)).2
  have propA : ∀ f f' u, C.inA f → C.inA f' → X.Inc f u → X.Inc f' u → f ≠ f' →
      cA (Fin.castSucc f) ≠ cA (Fin.castSucc f') := fun f f' u hf hf' hfu hf'u hne =>
    hA.1.1 _ _ ⟨fun h => hne (castSucc_inj' h), u, addEdge_inc_old.2 hfu, addEdge_inc_old.2 hf'u⟩
      (C.clo_old hf) (C.clo_old hf')
  have propB : ∀ f f' u, C.flip.inA f → C.flip.inA f' → X.Inc f u → X.Inc f' u → f ≠ f' →
      cB (Fin.castSucc f) ≠ cB (Fin.castSucc f') := fun f f' u hf hf' hfu hf'u hne =>
    hB.1.1 _ _ ⟨fun h => hne (castSucc_inj' h), u, addEdge_inc_old.2 hfu, addEdge_inc_old.2 hf'u⟩
      (C.flip.clo_old hf) (C.flip.clo_old hf')
  -- the F-edges at the four cut ends
  obtain ⟨f1, f1', d1, i1, i1', n1, n1', a1, a1', c1⟩ := C.two_F hcub hM (Or.inl rfl) hM1 (joins_inc_left C.j1) C.sa1
  obtain ⟨f2, f2', d2, i2, i2', n2, n2', a2, a2', c2⟩ := C.two_F hcub hM (Or.inr rfl) hM2 (joins_inc_left C.j2) C.sa2
  obtain ⟨g1, g1', e1, j1, j1', m1, m1', b1, b1', k1⟩ :=
    C.flip.two_F hcub hM (Or.inl rfl) hM1 (joins_inc_left C.flip.j1) C.flip.sa1
  obtain ⟨g2, g2', e2, j2, j2', m2, m2', b2, b2', k2⟩ :=
    C.flip.two_F hcub hM (Or.inr rfl) hM2 (joins_inc_left C.flip.j2) C.flip.sa2
  have hS := side_sets C cA rbA hpa d1 i1 i1' i2 i2' n1 n1' n2 n2' a1 a1' a2 a2'
  have hT := side_sets C.flip cB rbB hpb e1 j1 j1' j2 j2' m1 m1' m2 m2' b1 b1' b2 b2'
  obtain ⟨σ, hσi, hσ5, s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    perm_g2m _ _ _ _ _ _ _ _ (ne5A _ i1 n1) (ne5A _ i1' n1') (ne5A _ i2 n2) (ne5A _ i2' n2')
      (ne5B _ j1 m1) (ne5B _ j1' m1') (ne5B _ j2 m2) (ne5B _ j2' m2')
      (propA _ _ _ i1 i1' a1 a1' d1) (propA _ _ _ i2 i2' a2 a2' d2)
      (propB _ _ _ j1 j1' b1 b1' e1) (propB _ _ _ j2 j2' b2 b2' e2) hS hT
  -- the glued colouring
  let c : Fin X.m → Fin 6 := fun f =>
    if C.S (X.ends f).1 = C.S (X.ends f).2 then
      (if C.S (X.ends f).1 = true then cA (Fin.castSucc f) else σ (cB (Fin.castSucc f)))
    else 5
  have hagA : ∀ f, C.inA f → c f = cA (Fin.castSucc f) := by
    intro f hf
    have e1 : C.S (X.ends f).1 = C.S (X.ends f).2 := hf.2.1.trans hf.2.2.symm
    simp only [c, if_pos e1, if_pos hf.2.1]
  have hagB : ∀ f, C.flip.inA f → c f = σ (cB (Fin.castSucc f)) := by
    intro f hf
    have h1 : C.S (X.ends f).1 = false := by have := hf.2.1; rw [Cut2.flip_S] at this; simpa using this
    have h2 : C.S (X.ends f).2 = false := by have := hf.2.2; rw [Cut2.flip_S] at this; simpa using this
    have e1 : C.S (X.ends f).1 = C.S (X.ends f).2 := h1.trans h2.symm
    have e2 : ¬ C.S (X.ends f).1 = true := by rw [h1]; decide
    simp only [c, if_pos e1, if_neg e2]
  have hcut5 : ∀ f, C.isCut f → c f = 5 := by
    intro f hf
    have hne : ¬ C.S (X.ends f).1 = C.S (X.ends f).2 := by
      rcases C.cut_sides hf (joins_ends f) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
    simp only [c, if_neg hne]
  have hcutA : ∀ f, C.isCut f → c f = cA (Fin.last X.m) := fun f hf => by rw [hcut5 f hf, hA5]
  have hcutB : ∀ f, C.flip.isCut f → c f = σ (cB (Fin.last X.m)) := fun f hf => by rw [hcut5 f hf, hB5, hσ5]
  let dB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6 := fun i => σ (cB i)
  have hdB : StarOn C.flip.clo 6 dB := starOn_map σ hσi hB.1
  have hσ5' : ∀ y, σ y = 5 ↔ y = 5 := fun y => ⟨fun h => hσi _ _ (h.trans hσ5.symm), fun h => h ▸ hσ5⟩
  have rbB' : RB C.flip.clo (C.flip.cloN M True) dB := by
    intro e y y' f f' h1 h2 h3 h4 h5 h6 h7 h8 h9 heq
    exact rbB e y y' f f' h1 h2 h3 h4 h5 h6 h7 h8 h9 (hσi _ _ heq)
  have ncut : ∀ f, ¬ M f → ¬ C.isCut f := fun f hf h => h.elim (fun h' => hf (h' ▸ hM1)) (fun h' => hf (h' ▸ hM2))
  have hclass : ∀ f, P f → (M f ↔ c f = 5) := by
    intro f hf
    rcases C.cases_P hf with h | h | h
    · rw [hagA f h, ← (hA.2 _ (C.clo_old h)), C.cloN_old_iff]
      exact ⟨fun hm => ⟨h, hm⟩, fun hm => hm.2⟩
    · rw [hagB f h, hσ5', ← (hB.2 _ (C.flip.clo_old h)), C.flip.cloN_old_iff]
      exact ⟨fun hm => ⟨h, hm⟩, fun hm => hm.2⟩
    · rw [hcut5 f h]
      exact ⟨fun _ => rfl, fun _ => h.elim (fun h' => h' ▸ hM1) (fun h' => h' ▸ hM2)⟩
  -- colours of the F-edges at the cut ends
  have colA1 : ∀ f, P f → ¬ M f → X.Inc f C.a1 → c f = cA (Fin.castSucc f1) ∨ c f = cA (Fin.castSucc f1') := by
    intro f hf nf hfa
    rcases c1 f hf nf hfa with rfl | rfl
    · exact Or.inl (hagA _ i1)
    · exact Or.inr (hagA _ i1')
  have colA2 : ∀ f, P f → ¬ M f → X.Inc f C.a2 → c f = cA (Fin.castSucc f2) ∨ c f = cA (Fin.castSucc f2') := by
    intro f hf nf hfa
    rcases c2 f hf nf hfa with rfl | rfl
    · exact Or.inl (hagA _ i2)
    · exact Or.inr (hagA _ i2')
  have colB1 : ∀ f, P f → ¬ M f → X.Inc f C.b1 →
      c f = σ (cB (Fin.castSucc g1)) ∨ c f = σ (cB (Fin.castSucc g1')) := by
    intro f hf nf hfa
    rcases k1 f hf nf hfa with rfl | rfl
    · exact Or.inl (hagB _ j1)
    · exact Or.inr (hagB _ j1')
  have colB2 : ∀ f, P f → ¬ M f → X.Inc f C.b2 →
      c f = σ (cB (Fin.castSucc g2)) ∨ c f = σ (cB (Fin.castSucc g2')) := by
    intro f hf nf hfa
    rcases k2 f hf nf hfa with rfl | rfl
    · exact Or.inl (hagB _ j2)
    · exact Or.inr (hagB _ j2')
  -- (B) at a cut edge: an F-edge at `a_i` against an F-edge at `b_i`
  have atcut : ∀ f f', P f → ¬ M f → P f' → ¬ M f' →
      ((X.Inc f C.a1 ∧ X.Inc f' C.b1) ∨ (X.Inc f C.a2 ∧ X.Inc f' C.b2)) → c f ≠ c f' := by
    intro f f' hf nf hf' nf' h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases colA1 f hf nf ha with h1 | h1 <;> rcases colB1 f' hf' nf' hb with h2 | h2 <;> rw [h1, h2] <;>
        first | exact Ne.symm s1 | exact Ne.symm s2 | exact Ne.symm s3 | exact Ne.symm s4
    · rcases colA2 f hf nf ha with h1 | h1 <;> rcases colB2 f' hf' nf' hb with h2 | h2 <;> rw [h1, h2] <;>
        first | exact Ne.symm s5 | exact Ne.symm s6 | exact Ne.symm s7 | exact Ne.symm s8
  refine ⟨c, star_of_rabc hM hclass ?_ ?_ ?_, hclass⟩
  · -- (A)
    intro a b hab ha hb _ _
    obtain ⟨hne, x, hax, hbx⟩ := hab
    cases hs : C.S x
    · have hs' : C.flip.S x = true := by rw [Cut2.flip_S, hs]; rfl
      exact side_prop C.flip dB c hdB hagB hcutB hne hax hbx hs' ha hb
    · exact side_prop C cA c hA.1 hagA hcutA hne hax hbx hs ha hb
  · -- (B)
    intro e y y' f f' he hj hf nf hfy hf' nf' hf'y' hff
    rcases C.cases_P (hM.1 e he) with hin | hin | hin
    · exact side_rbM C cA c hM1 hM2 rbA hagA he hin hj hf nf hfy hf' nf' hf'y' hff
    · exact side_rbM C.flip dB c hM1 hM2 rbB' hagB he hin hj hf nf hfy hf' nf' hf'y' hff
    · rcases hin with rfl | rfl
      · rcases joins_unique hj C.j1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact atcut f f' hf nf hf' nf' (Or.inl ⟨hfy, hf'y'⟩)
        · exact Ne.symm (atcut f' f hf' nf' hf nf (Or.inl ⟨hf'y', hfy⟩))
      · rcases joins_unique hj C.j2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact atcut f f' hf nf hf' nf' (Or.inr ⟨hfy, hf'y'⟩)
        · exact Ne.symm (atcut f' f hf' nf' hf nf (Or.inr ⟨hf'y', hfy⟩))
  · -- (C): an F-walk stays on one side
    intro w h1 h2 h3 h4 n1 n2 n3 n4 hb
    have s12 : C.S w.v1 = C.S w.v2 := C.same_side h2 (ncut _ n2) w.h2
    have s23 : C.S w.v2 = C.S w.v3 := C.same_side h3 (ncut _ n3) w.h3
    cases hs : C.S w.v1
    · have hs' : ∀ v, C.S v = false → C.flip.S v = true := fun v hv => by rw [Cut2.flip_S, hv]; rfl
      have i1 := C.flip.inA_of_notcut h1 (ncut _ n1) w.inc_e1_v1 (hs' _ hs)
      have i2 := C.flip.inA_of_notcut h2 (ncut _ n2) w.inc_e2_v1 (hs' _ hs)
      have i3 := C.flip.inA_of_notcut h3 (ncut _ n3) w.inc_e3_v2 (hs' _ (s12 ▸ hs))
      have i4 := C.flip.inA_of_notcut h4 (ncut _ n4) w.inc_e4_v3 (hs' _ (s23 ▸ s12 ▸ hs))
      exact side_proj0 C.flip dB c hdB hagB w i1 i2 i3 i4 hb
    · have i1 := C.inA_of_notcut h1 (ncut _ n1) w.inc_e1_v1 hs
      have i2 := C.inA_of_notcut h2 (ncut _ n2) w.inc_e2_v1 hs
      have i3 := C.inA_of_notcut h3 (ncut _ n3) w.inc_e3_v2 (s12 ▸ hs)
      have i4 := C.inA_of_notcut h4 (ncut _ n4) w.inc_e4_v3 (s23 ▸ s12 ▸ hs)
      exact side_proj0 C cA c hA.1 hagA w i1 i2 i3 i4 hb

end g2m

end RH2F

namespace RH2F
open MGraph

/-- **Layer 1 of the Lean formalization of RH2** (facts 8ef6f166623321e6 Lemma R, 1d175e8252f975b1 G2F,
    90755fcae2fca4e1 G2M): Lemma R, the recolouring to class `5`, the perfect matchings of the closures, and the
    two gluing lemmas G2F (F-type 2-edge-cut) and G2M (M-type 2-edge-cut). -/
theorem layer1 :
    (∀ (X : MGraph) (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6), Loopless X → PMOn P N →
      (∀ f, P f → (N f ↔ c f = 5)) → (StarOn P 6 c ↔ RA P N c ∧ RB P N c ∧ RC P N c)) ∧
    (∀ (X : MGraph) (P N : Fin X.m → Prop) (c : Fin X.m → Fin 6), StarOn P 6 c → ClassOn P N c →
      ∃ c' : Fin X.m → Fin 6, MC5 P N c') ∧
    (∀ (X : MGraph) (P M : Fin X.m → Prop) (C : Cut2 P), PMOn P M → ¬ M C.e1 → ¬ M C.e2 →
      PMOn C.clo (C.cloN M False)) ∧
    (∀ (X : MGraph) (P M : Fin X.m → Prop) (C : Cut2 P), PMOn P M → M C.e1 → M C.e2 →
      PMOn C.clo (C.cloN M True)) ∧
    (∀ (X : MGraph) (P M : Fin X.m → Prop), Loopless X → CubicOn P → PMOn P M → ∀ C : Cut2 P,
      ¬ M C.e1 → ¬ M C.e2 →
      (∀ e, M e → ¬ X.Joins e C.a1 C.a2) → (∀ e, M e → ¬ X.Joins e C.b1 C.b2) →
      ∀ cA : Fin (addEdge X C.a1 C.a2).m → Fin 6, MC5 C.clo (C.cloN M False) cA →
      ∀ cB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6, MC5 C.flip.clo (C.flip.cloN M False) cB →
      ∃ c : Fin X.m → Fin 6, MC5 P M c) ∧
    (∀ (X : MGraph) (P M : Fin X.m → Prop), Loopless X → CubicOn P → PMOn P M → ∀ C : Cut2 P,
      M C.e1 → M C.e2 →
      (∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f') →
      (∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f') →
      ∀ cA : Fin (addEdge X C.a1 C.a2).m → Fin 6, MC5 C.clo (C.cloN M True) cA →
      ∀ cB : Fin (addEdge X C.flip.a1 C.flip.a2).m → Fin 6, MC5 C.flip.clo (C.flip.cloN M True) cB →
      ∃ c : Fin X.m → Fin 6, MC5 P M c) :=
  ⟨fun _ _ _ _ hl hN hcl => lemmaR hl hN hcl,
   fun _ _ _ _ hc hcl => mc5_of_class hc hcl,
   fun _ _ _ C hM h1 h2 => C.pm_cloF hM h1 h2,
   fun _ _ _ C hM h1 h2 => C.pm_cloM hM h1 h2,
   fun _ _ _ hl hc hM C h1 h2 ha hb cA hA cB hB => g2f hl hc hM C h1 h2 ha hb cA hA cB hB,
   fun _ _ _ hl hc hM C h1 h2 ha hb cA hA cB hB => g2m hl hc hM C h1 h2 ha hb cA hA cB hB⟩

end RH2F
