/-
  StarCore.lean — trusted core of the star-edge-colouring development, in core Lean 4 (no Mathlib).

  Objects: multigraphs with vertices `Fin n` and edge indices `Fin m`; colourings `Fin m → Fin k`.
  A star edge-colouring is a proper edge-colouring with no bicoloured walk of four distinct edges whose
  vertices satisfy the path/4-cycle distinctness conditions (a path of length four, or a 4-cycle).

  Fully proved here (no axioms beyond Lean's core, no `sorry`):
  * `starOn_map`     — an injective recolouring map preserves (restricted) star colourings;
  * `glue_bridge`    — bridge gluing: if `e` is a bridge and both sides (each keeping `e`) are star `k`-coloured with
                       the same colour on `e` and disjoint colour sets at the two endpoints of `e`, then the glued
                       colouring is a star `k`-colouring of the whole graph;
  * `pendant_extend` — pendant edges attached at distinct vertices of a star `k`-coloured core can all receive one
                       new colour, giving a star `(k+1)`-colouring.
-/

structure MGraph where
  n : Nat
  m : Nat
  ends : Fin m → Fin n × Fin n

namespace MGraph
variable (G : MGraph)

/-- edge `f` is incident to vertex `x` -/
def Inc (f : Fin G.m) (x : Fin G.n) : Prop := (G.ends f).1 = x ∨ (G.ends f).2 = x

/-- edge `f` joins `x` and `y` (in either orientation) -/
def Joins (f : Fin G.m) (x y : Fin G.n) : Prop := G.ends f = (x, y) ∨ G.ends f = (y, x)

/-- two distinct edges sharing an endpoint -/
def Adj (a b : Fin G.m) : Prop := a ≠ b ∧ ∃ x, G.Inc a x ∧ G.Inc b x

/-- a walk of four edges through vertices v0 v1 v2 v3 v4 with v0..v3 pairwise distinct and v1..v4 pairwise
    distinct (v4 = v0 allowed: a 4-cycle).  These conditions force the four edges to be distinct. -/
structure Walk4 where
  v0 : Fin G.n
  v1 : Fin G.n
  v2 : Fin G.n
  v3 : Fin G.n
  v4 : Fin G.n
  e1 : Fin G.m
  e2 : Fin G.m
  e3 : Fin G.m
  e4 : Fin G.m
  h1 : G.Joins e1 v0 v1
  h2 : G.Joins e2 v1 v2
  h3 : G.Joins e3 v2 v3
  h4 : G.Joins e4 v3 v4
  d01 : v0 ≠ v1
  d02 : v0 ≠ v2
  d03 : v0 ≠ v3
  d12 : v1 ≠ v2
  d13 : v1 ≠ v3
  d14 : v1 ≠ v4
  d23 : v2 ≠ v3
  d24 : v2 ≠ v4
  d34 : v3 ≠ v4

variable {G}

/-- the walk is bicoloured -/
def Bicol {k : Nat} (c : Fin G.m → Fin k) (w : G.Walk4) : Prop := c w.e1 = c w.e3 ∧ c w.e2 = c w.e4

/-- star colouring restricted to the edges satisfying `P` -/
def StarOn (P : Fin G.m → Prop) (k : Nat) (c : Fin G.m → Fin k) : Prop :=
  (∀ a b, G.Adj a b → P a → P b → c a ≠ c b) ∧
  (∀ w : G.Walk4, P w.e1 → P w.e2 → P w.e3 → P w.e4 → ¬ Bicol c w)

/-- star colouring of the whole graph -/
def Star (k : Nat) (c : Fin G.m → Fin k) : Prop := StarOn (fun _ => True) k c

theorem star_iff (k : Nat) (c : Fin G.m → Fin k) :
    Star k c ↔ (∀ a b, G.Adj a b → c a ≠ c b) ∧ (∀ w : G.Walk4, ¬ Bicol c w) := by
  constructor
  · intro h
    exact ⟨fun a b hab => h.1 a b hab trivial trivial, fun w => h.2 w trivial trivial trivial trivial⟩
  · intro h
    exact ⟨fun a b hab _ _ => h.1 a b hab, fun w _ _ _ _ => h.2 w⟩

/-! ### basic facts about incidence and walks -/

theorem joins_inc_left {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : G.Inc f x := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

theorem joins_inc_right {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : G.Inc f y := by
  rcases h with h | h
  · exact Or.inr (by rw [h])
  · exact Or.inl (by rw [h])

theorem joins_ends (f : Fin G.m) : G.Joins f (G.ends f).1 (G.ends f).2 := Or.inl rfl

/-- the two endpoints of an edge are determined up to order -/
theorem joins_unique {f : Fin G.m} {x y x' y' : Fin G.n} (h : G.Joins f x y) (h' : G.Joins f x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  rcases h with h | h <;> rcases h' with h' | h'
  · rw [h] at h'
    exact Or.inl ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
  · rw [h] at h'
    exact Or.inr ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
  · rw [h] at h'
    exact Or.inr ⟨(Prod.mk.inj h').2, (Prod.mk.inj h').1⟩
  · rw [h] at h'
    exact Or.inl ⟨(Prod.mk.inj h').2, (Prod.mk.inj h').1⟩

theorem inc_of_joins {f : Fin G.m} {x y z : Fin G.n} (h : G.Joins f x y) (hz : G.Inc f z) :
    z = x ∨ z = y := by
  rcases h with h | h <;> rcases hz with hz | hz <;> rw [h] at hz
  · exact Or.inl hz.symm
  · exact Or.inr hz.symm
  · exact Or.inr hz.symm
  · exact Or.inl hz.symm

namespace Walk4
variable (w : G.Walk4)

theorem e1_ne_e2 : w.e1 ≠ w.e2 := by
  intro h
  have h2' : G.Joins w.e1 w.v1 w.v2 := by rw [h]; exact w.h2
  rcases joins_unique w.h1 h2' with ⟨h', _⟩ | ⟨h', _⟩
  · exact w.d01 h'
  · exact w.d02 h'

theorem e2_ne_e3 : w.e2 ≠ w.e3 := by
  intro h
  have h3' : G.Joins w.e2 w.v2 w.v3 := by rw [h]; exact w.h3
  rcases joins_unique w.h2 h3' with ⟨h', _⟩ | ⟨h', _⟩
  · exact w.d12 h'
  · exact w.d13 h'

theorem e3_ne_e4 : w.e3 ≠ w.e4 := by
  intro h
  have h4' : G.Joins w.e3 w.v3 w.v4 := by rw [h]; exact w.h4
  rcases joins_unique w.h3 h4' with ⟨h', _⟩ | ⟨h', _⟩
  · exact w.d23 h'
  · exact w.d24 h'

theorem e1_ne_e3 : w.e1 ≠ w.e3 := by
  intro h
  have h3' : G.Joins w.e1 w.v2 w.v3 := by rw [h]; exact w.h3
  rcases joins_unique w.h1 h3' with ⟨h', _⟩ | ⟨h', _⟩
  · exact w.d02 h'
  · exact w.d03 h'

theorem e2_ne_e4 : w.e2 ≠ w.e4 := by
  intro h
  have h4' : G.Joins w.e2 w.v3 w.v4 := by rw [h]; exact w.h4
  rcases joins_unique w.h2 h4' with ⟨h', _⟩ | ⟨h', _⟩
  · exact w.d13 h'
  · exact w.d14 h'

theorem e1_ne_e4 : w.e1 ≠ w.e4 := by
  intro h
  have h4' : G.Joins w.e1 w.v3 w.v4 := by rw [h]; exact w.h4
  rcases joins_unique w.h1 h4' with ⟨h', _⟩ | ⟨_, h'⟩
  · exact w.d03 h'
  · exact w.d13 h'

theorem inc_e1_v0 : G.Inc w.e1 w.v0 := joins_inc_left w.h1
theorem inc_e1_v1 : G.Inc w.e1 w.v1 := joins_inc_right w.h1
theorem inc_e2_v1 : G.Inc w.e2 w.v1 := joins_inc_left w.h2
theorem inc_e2_v2 : G.Inc w.e2 w.v2 := joins_inc_right w.h2
theorem inc_e3_v2 : G.Inc w.e3 w.v2 := joins_inc_left w.h3
theorem inc_e3_v3 : G.Inc w.e3 w.v3 := joins_inc_right w.h3
theorem inc_e4_v3 : G.Inc w.e4 w.v3 := joins_inc_left w.h4
theorem inc_e4_v4 : G.Inc w.e4 w.v4 := joins_inc_right w.h4

end Walk4

/-! ### injective recolouring -/

theorem starOn_map {P : Fin G.m → Prop} {k k' : Nat} (π : Fin k → Fin k')
    (hπ : ∀ x y, π x = π y → x = y) {c : Fin G.m → Fin k} (h : StarOn P k c) :
    StarOn P k' (fun f => π (c f)) := by
  constructor
  · intro a b hab ha hb heq
    exact h.1 a b hab ha hb (hπ _ _ heq)
  · intro w h1 h2 h3 h4 hb
    exact h.2 w h1 h2 h3 h4 ⟨hπ _ _ hb.1, hπ _ _ hb.2⟩

/-! ### bridges and gluing -/

/-- A bridge cut for edge `e`: a two-colouring of the vertices (`true` = the side of the first endpoint of `e`)
    such that every edge other than `e` has both endpoints on the same side. -/
structure BridgeCut (e : Fin G.m) where
  U : Fin G.n → Bool
  hu : U (G.ends e).1 = true
  hv : U (G.ends e).2 = false
  sep : ∀ f, f ≠ e → U (G.ends f).1 = U (G.ends f).2

namespace BridgeCut
variable {e : Fin G.m} (B : G.BridgeCut e)

/-- edge `f` lies on the side of the first endpoint of `e` -/
def onU (f : Fin G.m) : Prop := B.U (G.ends f).1 = true

theorem onU_iff_inc {f : Fin G.m} {x : Fin G.n} (hf : f ≠ e) (hx : G.Inc f x) :
    (B.onU f ↔ B.U x = true) := by
  rcases hx with hx | hx
  · show B.U (G.ends f).1 = true ↔ B.U x = true
    rw [hx]
  · show B.U (G.ends f).1 = true ↔ B.U x = true
    rw [B.sep f hf, hx]

theorem same_side {a b : Fin G.m} {x : Fin G.n} (ha : a ≠ e) (hb : b ≠ e)
    (hax : G.Inc a x) (hbx : G.Inc b x) : (B.onU a ↔ B.onU b) := by
  rw [B.onU_iff_inc ha hax, B.onU_iff_inc hb hbx]

theorem onU_e : B.onU e := B.hu

theorem onU_of_inc_u {f : Fin G.m} (hf : f ≠ e) (hx : G.Inc f (G.ends e).1) : B.onU f :=
  (B.onU_iff_inc hf hx).2 B.hu

theorem not_onU_of_inc_v {f : Fin G.m} (hf : f ≠ e) (hx : G.Inc f (G.ends e).2) : ¬ B.onU f := by
  intro h
  have := (B.onU_iff_inc hf hx).1 h
  rw [B.hv] at this
  exact Bool.false_ne_true this

/-- the glued colouring -/
def glue {k : Nat} (cU cV : Fin G.m → Fin k) (f : Fin G.m) : Fin k :=
  if B.U (G.ends f).1 then cU f else cV f

theorem glue_U {k : Nat} (cU cV : Fin G.m → Fin k) {f : Fin G.m} (h : B.onU f) : B.glue cU cV f = cU f := by
  unfold glue
  have h' : B.U (G.ends f).1 = true := h
  simp [h']

theorem glue_V {k : Nat} (cU cV : Fin G.m → Fin k) {f : Fin G.m} (h : ¬ B.onU f) : B.glue cU cV f = cV f := by
  unfold glue
  have h' : B.U (G.ends f).1 = false := by
    cases hb : B.U (G.ends f).1
    · rfl
    · exact absurd hb h
  simp [h']

end BridgeCut

/-- **Bridge gluing.**  Let `e` be a bridge with cut `B`.  If `cU` is a star `k`-colouring of the edges on the
    side of `u = (ends e).1` together with `e`, `cV` a star `k`-colouring of the other side together with `e`,
    both give `e` the same colour, and no edge at `u` (other than `e`) has a `cU`-colour equal to the `cV`-colour of
    an edge at `v = (ends e).2` (other than `e`), then the glued colouring is a star `k`-colouring of `G`. -/
theorem glue_bridge {e : Fin G.m} (B : G.BridgeCut e) {k : Nat} (cU cV : Fin G.m → Fin k)
    (hU : StarOn (fun f => f = e ∨ B.onU f) k cU)
    (hV : StarOn (fun f => f = e ∨ ¬ B.onU f) k cV)
    (he : cU e = cV e)
    (hdisj : ∀ a b, a ≠ e → b ≠ e → G.Inc a (G.ends e).1 → G.Inc b (G.ends e).2 → cU a ≠ cV b) :
    Star k (B.glue cU cV) := by
  have gU : ∀ {f}, B.onU f → B.glue cU cV f = cU f := fun h => B.glue_U cU cV h
  have gV : ∀ {f}, ¬ B.onU f → B.glue cU cV f = cV f := fun h => B.glue_V cU cV h
  have ge : B.glue cU cV e = cU e := gU B.onU_e
  have ge' : B.glue cU cV e = cV e := by rw [ge, he]
  have hu_or_v : ∀ {x : Fin G.n}, G.Inc e x → x = (G.ends e).1 ∨ x = (G.ends e).2 :=
    fun hx => inc_of_joins (joins_ends e) hx
  constructor
  · -- properness
    intro a b hab _ _ heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    by_cases ha : a = e
    · subst ha
      have hb : b ≠ a := fun h => hne h.symm
      rcases hu_or_v hax with hx | hx
      · -- b is at u, hence on the U side
        have hbU : B.onU b := B.onU_of_inc_u hb (hx ▸ hbx)
        rw [ge, gU hbU] at heq
        exact hU.1 a b ⟨hne, x, hax, hbx⟩ (Or.inl rfl) (Or.inr hbU) heq
      · have hbV : ¬ B.onU b := B.not_onU_of_inc_v hb (hx ▸ hbx)
        rw [ge', gV hbV] at heq
        exact hV.1 a b ⟨hne, x, hax, hbx⟩ (Or.inl rfl) (Or.inr hbV) heq
    · by_cases hb : b = e
      · subst hb
        rcases hu_or_v hbx with hx | hx
        · have haU : B.onU a := B.onU_of_inc_u ha (hx ▸ hax)
          rw [ge, gU haU] at heq
          exact hU.1 a b ⟨hne, x, hax, hbx⟩ (Or.inr haU) (Or.inl rfl) heq
        · have haV : ¬ B.onU a := B.not_onU_of_inc_v ha (hx ▸ hax)
          rw [ge', gV haV] at heq
          exact hV.1 a b ⟨hne, x, hax, hbx⟩ (Or.inr haV) (Or.inl rfl) heq
      · have hss := B.same_side ha hb hax hbx
        by_cases haU : B.onU a
        · have hbU : B.onU b := hss.1 haU
          rw [gU haU, gU hbU] at heq
          exact hU.1 a b ⟨hne, x, hax, hbx⟩ (Or.inr haU) (Or.inr hbU) heq
        · have hbV : ¬ B.onU b := fun h => haU (hss.2 h)
          rw [gV haU, gV hbV] at heq
          exact hV.1 a b ⟨hne, x, hax, hbx⟩ (Or.inr haU) (Or.inr hbV) heq
  · -- no bicoloured walk
    intro w _ _ _ _ hb
    rcases hb with ⟨hb13, hb24⟩
    -- side relations between consecutive edges (when neither is e)
    by_cases h2 : w.e2 = e
    · -- e in position 2: v1 v2 are the endpoints of e; e1 at v1, e3 at v2 lie on opposite sides
      have h1 : w.e1 ≠ e := fun h => w.e1_ne_e2 (h.trans h2.symm)
      have h3 : w.e3 ≠ e := fun h => w.e2_ne_e3 (h2.trans h.symm)
      have hj : G.Joins e w.v1 w.v2 := by rw [← h2]; exact w.h2
      rcases joins_unique (joins_ends e) hj with ⟨hu1, hv2⟩ | ⟨hu2, hv1⟩
      · -- v1 = u, v2 = v
        have h1U : B.onU w.e1 := B.onU_of_inc_u h1 (hu1 ▸ w.inc_e1_v1)
        have h3V : ¬ B.onU w.e3 := B.not_onU_of_inc_v h3 (hv2 ▸ w.inc_e3_v2)
        rw [gU h1U, gV h3V] at hb13
        exact hdisj w.e1 w.e3 h1 h3 (hu1 ▸ w.inc_e1_v1) (hv2 ▸ w.inc_e3_v2) hb13
      · -- v2 = u, v1 = v
        have h3U : B.onU w.e3 := B.onU_of_inc_u h3 (hu2 ▸ w.inc_e3_v2)
        have h1V : ¬ B.onU w.e1 := B.not_onU_of_inc_v h1 (hv1 ▸ w.inc_e1_v1)
        rw [gV h1V, gU h3U] at hb13
        exact hdisj w.e3 w.e1 h3 h1 (hu2 ▸ w.inc_e3_v2) (hv1 ▸ w.inc_e1_v1) hb13.symm
    by_cases h3 : w.e3 = e
    · have h2' : w.e2 ≠ e := h2
      have h4 : w.e4 ≠ e := fun h => w.e3_ne_e4 (h3.trans h.symm)
      have hj : G.Joins e w.v2 w.v3 := by rw [← h3]; exact w.h3
      rcases joins_unique (joins_ends e) hj with ⟨hu2, hv3⟩ | ⟨hu3, hv2⟩
      · have h2U : B.onU w.e2 := B.onU_of_inc_u h2' (hu2 ▸ w.inc_e2_v2)
        have h4V : ¬ B.onU w.e4 := B.not_onU_of_inc_v h4 (hv3 ▸ w.inc_e4_v3)
        rw [gU h2U, gV h4V] at hb24
        exact hdisj w.e2 w.e4 h2' h4 (hu2 ▸ w.inc_e2_v2) (hv3 ▸ w.inc_e4_v3) hb24
      · have h4U : B.onU w.e4 := B.onU_of_inc_u h4 (hu3 ▸ w.inc_e4_v3)
        have h2V : ¬ B.onU w.e2 := B.not_onU_of_inc_v h2' (hv2 ▸ w.inc_e2_v2)
        rw [gV h2V, gU h4U] at hb24
        exact hdisj w.e4 w.e2 h4 h2' (hu3 ▸ w.inc_e4_v3) (hv2 ▸ w.inc_e2_v2) hb24.symm
    -- now e2 ≠ e and e3 ≠ e; e2 and e3 lie on the same side, and so does anything adjacent through v1, v3
    have s23 : (B.onU w.e2 ↔ B.onU w.e3) := B.same_side h2 h3 w.inc_e2_v2 w.inc_e3_v2
    by_cases h1 : w.e1 = e
    · -- e in position 1: e2 e3 e4 all lie on the side of v1 ∈ {u, v}
      have h4 : w.e4 ≠ e := fun h => w.e1_ne_e4 (h1.trans h.symm)
      have s34 : (B.onU w.e3 ↔ B.onU w.e4) := B.same_side h3 h4 w.inc_e3_v3 w.inc_e4_v3
      have hj : G.Joins e w.v0 w.v1 := by rw [← h1]; exact w.h1
      rcases hu_or_v (joins_inc_right hj) with hx | hx
      · have h2U : B.onU w.e2 := B.onU_of_inc_u h2 (hx ▸ w.inc_e2_v1)
        have h3U := s23.1 h2U
        have h4U := s34.1 h3U
        rw [h1, ge, gU h3U] at hb13
        rw [gU h2U, gU h4U] at hb24
        exact hU.2 w (Or.inl h1) (Or.inr h2U) (Or.inr h3U) (Or.inr h4U) ⟨by rw [h1]; exact hb13, hb24⟩
      · have h2V : ¬ B.onU w.e2 := B.not_onU_of_inc_v h2 (hx ▸ w.inc_e2_v1)
        have h3V : ¬ B.onU w.e3 := fun h => h2V (s23.2 h)
        have h4V : ¬ B.onU w.e4 := fun h => h3V (s34.2 h)
        rw [h1, ge', gV h3V] at hb13
        rw [gV h2V, gV h4V] at hb24
        exact hV.2 w (Or.inl h1) (Or.inr h2V) (Or.inr h3V) (Or.inr h4V) ⟨by rw [h1]; exact hb13, hb24⟩
    by_cases h4 : w.e4 = e
    · have s12 : (B.onU w.e1 ↔ B.onU w.e2) := B.same_side h1 h2 w.inc_e1_v1 w.inc_e2_v1
      have hj : G.Joins e w.v3 w.v4 := by rw [← h4]; exact w.h4
      rcases hu_or_v (joins_inc_left hj) with hx | hx
      · have h3U : B.onU w.e3 := B.onU_of_inc_u h3 (hx ▸ w.inc_e3_v3)
        have h2U := s23.2 h3U
        have h1U := s12.2 h2U
        rw [gU h1U, gU h3U] at hb13
        rw [h4, ge, gU h2U] at hb24
        exact hU.2 w (Or.inr h1U) (Or.inr h2U) (Or.inr h3U) (Or.inl h4) ⟨hb13, by rw [h4]; exact hb24⟩
      · have h3V : ¬ B.onU w.e3 := B.not_onU_of_inc_v h3 (hx ▸ w.inc_e3_v3)
        have h2V : ¬ B.onU w.e2 := fun h => h3V (s23.1 h)
        have h1V : ¬ B.onU w.e1 := fun h => h2V (s12.1 h)
        rw [gV h1V, gV h3V] at hb13
        rw [h4, ge', gV h2V] at hb24
        exact hV.2 w (Or.inr h1V) (Or.inr h2V) (Or.inr h3V) (Or.inl h4) ⟨hb13, by rw [h4]; exact hb24⟩
    -- none of the four edges is e: all on one side
    have s12 : (B.onU w.e1 ↔ B.onU w.e2) := B.same_side h1 h2 w.inc_e1_v1 w.inc_e2_v1
    have s34 : (B.onU w.e3 ↔ B.onU w.e4) := B.same_side h3 h4 w.inc_e3_v3 w.inc_e4_v3
    by_cases h1U : B.onU w.e1
    · have h2U := s12.1 h1U
      have h3U := s23.1 h2U
      have h4U := s34.1 h3U
      rw [gU h1U, gU h3U] at hb13
      rw [gU h2U, gU h4U] at hb24
      exact hU.2 w (Or.inr h1U) (Or.inr h2U) (Or.inr h3U) (Or.inr h4U) ⟨hb13, hb24⟩
    · have h2V : ¬ B.onU w.e2 := fun h => h1U (s12.2 h)
      have h3V : ¬ B.onU w.e3 := fun h => h2V (s23.2 h)
      have h4V : ¬ B.onU w.e4 := fun h => h3V (s34.2 h)
      rw [gV h1U, gV h3V] at hb13
      rw [gV h2V, gV h4V] at hb24
      exact hV.2 w (Or.inr h1U) (Or.inr h2V) (Or.inr h3V) (Or.inr h4V) ⟨hb13, hb24⟩

/-! ### pendant edges -/

theorem castSucc_ne_last {k : Nat} (i : Fin k) : Fin.castSucc i ≠ Fin.last k := by
  intro h
  have h' : (Fin.castSucc i).val = (Fin.last k).val := congrArg Fin.val h
  have : i.val = k := h'
  exact absurd this (Nat.ne_of_lt i.isLt)

theorem castSucc_inj' {k : Nat} {i j : Fin k} (h : Fin.castSucc i = Fin.castSucc j) : i = j := by
  apply Fin.ext
  have h' : (Fin.castSucc i).val = (Fin.castSucc j).val := congrArg Fin.val h
  exact h'

/-- **Pendant edges.**  `P` marks pendant edges; `leaf f` is a degree-one endpoint of the pendant edge `f`
    (no other edge is incident to it), and no two pendant edges share a vertex.  If `c` is a star `k`-colouring of
    the non-pendant edges, then colouring all pendant edges with the new colour `k` gives a star `(k+1)`-colouring. -/
theorem pendant_extend {k : Nat} (P : Fin G.m → Bool) (leaf : Fin G.m → Fin G.n) (c : Fin G.m → Fin k)
    (hleafinc : ∀ f, P f = true → G.Inc f (leaf f))
    (hleaf : ∀ f g, P f = true → g ≠ f → ¬ G.Inc g (leaf f))
    (hattach : ∀ f g, P f = true → P g = true → f ≠ g → ∀ x, G.Inc f x → G.Inc g x → False)
    (hcore : StarOn (fun f => P f = false) k c) :
    Star (k + 1) (fun f => if P f then Fin.last k else Fin.castSucc (c f)) := by
  -- an interior edge of a walk cannot be pendant
  have interior : ∀ (f g g' : Fin G.m) (x y : Fin G.n), P f = true → G.Joins f x y →
      g ≠ f → G.Inc g x → g' ≠ f → G.Inc g' y → False := by
    intro f g g' x y hf hj hg hgx hg' hg'y
    rcases inc_of_joins hj (hleafinc f hf) with hl | hl
    · exact hleaf f g hf hg (hl ▸ hgx)
    · exact hleaf f g' hf hg' (hl ▸ hg'y)
  constructor
  · intro a b hab _ _ heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    cases ha : P a <;> cases hb : P b <;> simp [ha, hb] at heq
    · exact hcore.1 a b ⟨hne, x, hax, hbx⟩ ha hb (castSucc_inj' heq)
    · exact castSucc_ne_last (c a) heq
    · exact castSucc_ne_last (c b) heq.symm
    · exact hattach a b ha hb hne x hax hbx
  · intro w _ _ _ _ hb
    rcases hb with ⟨hb13, hb24⟩
    cases h3 : P w.e3
    · cases h2 : P w.e2
      · cases h1 : P w.e1
        · cases h4 : P w.e4
          · simp [h1, h2, h3, h4] at hb13 hb24
            exact hcore.2 w h1 h2 h3 h4 ⟨castSucc_inj' hb13, castSucc_inj' hb24⟩
          · simp [h2, h4] at hb24
            exact castSucc_ne_last (c w.e2) hb24
        · simp [h1, h3] at hb13
          exact castSucc_ne_last (c w.e3) hb13.symm
      · exact interior w.e2 w.e1 w.e3 w.v1 w.v2 h2 w.h2 w.e1_ne_e2 w.inc_e1_v1 (fun h => w.e2_ne_e3 h.symm) w.inc_e3_v2
    · exact interior w.e3 w.e2 w.e4 w.v2 w.v3 h3 w.h3 w.e2_ne_e3 w.inc_e2_v2 (fun h => w.e3_ne_e4 h.symm) w.inc_e4_v3

end MGraph
