/-
  StarLeaf.lean — degree-one vertices in a minimal counterexample.

  Let `P` be a minimal non-star-6-colourable edge set of a subcubic multigraph and `e = uv ∈ P` with `u` a leaf
  (no other edge of `P` at `u`).  Then (`minimal_leaf`):
    `v` carries two further edges `f ≠ g` of `P`, and each of `f`, `g` carries two further edges of `P` at its
    endpoint away from `v`  — i.e. `v` and both of its other neighbours have degree three.
  In particular a leaf can never hang from a vertex of degree ≤ 2, nor from a degree-3 vertex having a neighbour of
  degree ≤ 2.  The reason is a count: a pendant edge is blocked only if all six colours are excluded, and the excluded
  colours are among the colours of the ≤ 2 other edges at `v` and the ≤ 2 further edges beyond each of them.
  Sharper (`minimal_leaf_rainbow`): for EVERY star 6-colouring of `P − e`, the six edges `f, g, f1, f2, g1, g2`
  within distance two of the leaf receive six pairwise distinct colours; hence (`minimal_leaf_six_edges`) they are six
  distinct edges — no parallel edges among them and no edge joining the two far neighbours.
  The remaining configuration (all three vertices of degree three, all six colours spent in every colouring) is NOT
  excluded here — and cannot be without new ideas: excluding it in general is a consequence of the conjecture whose
  direct proof is open (it is exactly the pendant-extension problem attacked by the L3/Swap/BSR computations).

  No `sorry`; the only computation is a kernel `decide` (pigeonhole on `Fin 6`), so no `Lean.ofReduceBool`.
-/
import StarCore
import StarCert
import StarReduce

namespace MGraph
variable {G : MGraph}

/-- `h` is a further edge of `f` beyond `v`: an edge of `P` other than `f` at an endpoint of `f` different from `v` -/
def Further (P : Fin G.m → Prop) (v : Fin G.n) (f h : Fin G.m) : Prop :=
  P h ∧ h ≠ f ∧ ∃ x, x ≠ v ∧ G.Inc f x ∧ G.Inc h x

/-- the endpoint of `f` different from `v` is unique -/
theorem inc_ne_unique {f : Fin G.m} {v x x' : Fin G.n} (hv : G.Inc f v) (hx : G.Inc f x) (hx' : G.Inc f x')
    (hxv : x ≠ v) (hx'v : x' ≠ v) : x = x' := by
  rcases hv with hv | hv
  · rcases hx with hx | hx
    · exact absurd (hx.symm.trans hv) hxv
    · rcases hx' with hx' | hx'
      · exact absurd (hx'.symm.trans hv) hx'v
      · exact hx.symm.trans hx'
  · rcases hx with hx | hx
    · rcases hx' with hx' | hx'
      · exact hx.symm.trans hx'
      · exact absurd (hx'.symm.trans hv) hx'v
    · exact absurd (hx.symm.trans hv) hxv

/-- **Extending a pendant edge.**  If `u` is a leaf of `P` and `φ` is a star `k`-colouring of `P − e`, then any colour
    `y` that differs from the colours of the other edges at `v` and from the colours of their further edges extends
    `φ` to a star `k`-colouring of `P`. -/
theorem pendant_free {P : Fin G.m → Prop} {k : Nat} (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin k) (hφ : StarOn (fun f => P f ∧ f ≠ e) k φ) (y : Fin k)
    (hy1 : ∀ f, P f → f ≠ e → G.Inc f (G.ends e).2 → φ f ≠ y)
    (hy2 : ∀ f h, P f → f ≠ e → G.Inc f (G.ends e).2 → Further P (G.ends e).2 f h → φ h ≠ y) :
    StarOn P k (fun f => if f = e then y else φ f) := by
  have ce : (fun f => if f = e then y else φ f) e = y := by simp
  have cf : ∀ {f}, f ≠ e → (fun f => if f = e then y else φ f) f = φ f := by
    intro f hf; simp [hf]
  have hu_or_v : ∀ {x : Fin G.n}, G.Inc e x → x = (G.ends e).1 ∨ x = (G.ends e).2 :=
    fun hx => inc_of_joins (joins_ends e) hx
  constructor
  · intro a b hab ha hb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    by_cases hae : a = e
    · subst hae
      have hb' : b ≠ a := fun h => hne h.symm
      rw [ce, cf hb'] at heq
      rcases hu_or_v hax with hx | hx
      · exact hleaf b hb hb' (hx ▸ hbx)
      · exact hy1 b hb hb' (hx ▸ hbx) heq.symm
    · by_cases hbe : b = e
      · subst hbe
        rw [ce, cf hae] at heq
        rcases hu_or_v hbx with hx | hx
        · exact hleaf a ha hae (hx ▸ hax)
        · exact hy1 a ha hae (hx ▸ hax) heq
      · rw [cf hae, cf hbe] at heq
        exact hφ.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, hae⟩ ⟨hb, hbe⟩ heq
  · intro w hp1 hp2 hp3 hp4 hb
    rcases hb with ⟨hb13, hb24⟩
    by_cases h2 : w.e2 = e
    · -- e in position 2: one of v1, v2 is the leaf u, carrying another edge
      have h1 : w.e1 ≠ e := fun h => w.e1_ne_e2 (h.trans h2.symm)
      have h3 : w.e3 ≠ e := fun h => w.e2_ne_e3 (h2.trans h.symm)
      have hj : G.Joins e w.v1 w.v2 := by rw [← h2]; exact w.h2
      rcases joins_unique (joins_ends e) hj with ⟨hu1, _⟩ | ⟨hu2, _⟩
      · exact hleaf w.e1 hp1 h1 (hu1 ▸ w.inc_e1_v1)
      · exact hleaf w.e3 hp3 h3 (hu2 ▸ w.inc_e3_v2)
    by_cases h3 : w.e3 = e
    · have h2' : w.e2 ≠ e := h2
      have h4 : w.e4 ≠ e := fun h => w.e3_ne_e4 (h3.trans h.symm)
      have hj : G.Joins e w.v2 w.v3 := by rw [← h3]; exact w.h3
      rcases joins_unique (joins_ends e) hj with ⟨hu2, _⟩ | ⟨hu3, _⟩
      · exact hleaf w.e2 hp2 h2' (hu2 ▸ w.inc_e2_v2)
      · exact hleaf w.e4 hp4 h4 (hu3 ▸ w.inc_e4_v3)
    by_cases h1 : w.e1 = e
    · -- e in position 1: v1 = v (else e2 would be at the leaf), and y = φ e3 with e3 a further edge of e2
      have hj : G.Joins e w.v0 w.v1 := by rw [← h1]; exact w.h1
      rcases joins_unique (joins_ends e) hj with ⟨_, hv1⟩ | ⟨hu1, _⟩
      · rw [h1, ce, cf h3] at hb13
        have hfur : Further P (G.ends e).2 w.e2 w.e3 :=
          ⟨hp3, fun h => w.e2_ne_e3 h.symm, w.v2, fun h => w.d12 (h.trans hv1).symm, w.inc_e2_v2, w.inc_e3_v2⟩
        exact hy2 w.e2 w.e3 hp2 h2 (hv1 ▸ w.inc_e2_v1) hfur hb13.symm
      · exact hleaf w.e2 hp2 h2 (hu1 ▸ w.inc_e2_v1)
    by_cases h4 : w.e4 = e
    · have hj : G.Joins e w.v3 w.v4 := by rw [← h4]; exact w.h4
      rcases joins_unique (joins_ends e) hj with ⟨hu3, _⟩ | ⟨_, hv3⟩
      · exact hleaf w.e3 hp3 h3 (hu3 ▸ w.inc_e3_v3)
      · rw [h4, ce, cf h2] at hb24
        have hfur : Further P (G.ends e).2 w.e3 w.e2 :=
          ⟨hp2, w.e2_ne_e3, w.v2, fun h => w.d23 (h.trans hv3), w.inc_e3_v2, w.inc_e2_v2⟩
        exact hy2 w.e3 w.e2 hp3 h3 (hv3 ▸ w.inc_e3_v3) hfur hb24
    rw [cf h1, cf h3] at hb13
    rw [cf h2, cf h4] at hb24
    exact hφ.2 w ⟨hp1, h1⟩ ⟨hp2, h2⟩ ⟨hp3, h3⟩ ⟨hp4, h4⟩ ⟨hb13, hb24⟩

/-- pigeonhole: five colours never exhaust six -/
theorem pigeon5 : ∀ a b c d e : Fin 6, ∃ y : Fin 6, y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ y ≠ d ∧ y ≠ e := by decide

/-- the further edges of `f` beyond `v` use at most two colours (subcubic) -/
theorem further_two (hsub : Subcubic G) (P : Fin G.m → Prop) (v : Fin G.n) (f : Fin G.m) (hfv : G.Inc f v)
    (φ : Fin G.m → Fin 6) (d : Fin 6) :
    ∃ p1 p2 : Fin 6, ∀ h, Further P v f h → φ h = p1 ∨ φ h = p2 := by
  by_cases h1 : ∃ h1, Further P v f h1
  · obtain ⟨h1, hP1, hne1, x1, hx1v, hfx1, hhx1⟩ := h1
    -- all further edges live at x1
    have at_x1 : ∀ h, Further P v f h → G.Inc h x1 := by
      intro h ⟨_, _, x, hxv, hfx, hhx⟩
      have := inc_ne_unique hfv hfx hfx1 hxv hx1v
      exact this ▸ hhx
    by_cases h2 : ∃ h2, Further P v f h2 ∧ h2 ≠ h1
    · obtain ⟨h2, hf2, h21⟩ := h2
      refine ⟨φ h1, φ h2, ?_⟩
      intro h hh
      by_cases hh1 : h = h1
      · exact Or.inl (by rw [hh1])
      by_cases hh2 : h = h2
      · exact Or.inr (by rw [hh2])
      exact absurd (hsub x1 h h1 h2 f (at_x1 h hh) hhx1 (at_x1 h2 hf2) hfx1 hh1 hh2 hh.2.1
        (fun h' => h21 h'.symm) hne1 hf2.2.1) id
    · refine ⟨φ h1, φ h1, ?_⟩
      intro h hh
      by_cases hh1 : h = h1
      · exact Or.inl (by rw [hh1])
      · exact absurd ⟨h, hh, hh1⟩ h2
  · exact ⟨d, d, fun h hh => absurd ⟨h, hh⟩ h1⟩

/-- if `f` has no two distinct further edges, their colours are a single value -/
theorem further_one (P : Fin G.m → Prop) (v : Fin G.n) (f : Fin G.m)
    (hnot : ¬ ∃ h1 h2, Further P v f h1 ∧ Further P v f h2 ∧ h1 ≠ h2) (φ : Fin G.m → Fin 6) (d : Fin 6) :
    ∃ p : Fin 6, ∀ h, Further P v f h → φ h = p := by
  by_cases h1 : ∃ h1, Further P v f h1
  · obtain ⟨h1, hf1⟩ := h1
    refine ⟨φ h1, ?_⟩
    intro h hh
    by_cases hh1 : h = h1
    · rw [hh1]
    · exact absurd ⟨h, h1, hh, hf1, hh1⟩ hnot
  · exact ⟨d, fun h hh => absurd ⟨h, hh⟩ h1⟩

/-- five colours covering all blocked colours ⇒ the pendant edge can be coloured -/
theorem colourable_of_five {P : Fin G.m → Prop} (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) (a1 a2 a3 a4 a5 : Fin 6)
    (hv : ∀ f, P f → f ≠ e → G.Inc f (G.ends e).2 → φ f = a1 ∨ φ f = a2 ∨ φ f = a3 ∨ φ f = a4 ∨ φ f = a5)
    (hw : ∀ f h, P f → f ≠ e → G.Inc f (G.ends e).2 → Further P (G.ends e).2 f h →
      φ h = a1 ∨ φ h = a2 ∨ φ h = a3 ∨ φ h = a4 ∨ φ h = a5) :
    Colourable P 6 := by
  obtain ⟨y, hy1, hy2, hy3, hy4, hy5⟩ := pigeon5 a1 a2 a3 a4 a5
  have hy : ∀ c : Fin 6, (c = a1 ∨ c = a2 ∨ c = a3 ∨ c = a4 ∨ c = a5) → c ≠ y := by
    intro c hc
    rcases hc with h | h | h | h | h <;> rw [h]
    · exact fun h' => hy1 h'.symm
    · exact fun h' => hy2 h'.symm
    · exact fun h' => hy3 h'.symm
    · exact fun h' => hy4 h'.symm
    · exact fun h' => hy5 h'.symm
  exact ⟨_, pendant_free e hPe hleaf φ hφ y (fun f hf hfe hfv => hy _ (hv f hf hfe hfv))
    (fun f h hf hfe hfv hfh => hy _ (hw f h hf hfe hfv hfh))⟩

/-- **Leaves of a minimal counterexample.**  If `u` is a leaf of a minimal non-star-6-colourable edge set `P` of a
    subcubic multigraph, then its neighbour `v` has two further edges `f ≠ g` in `P`, each of which has two distinct
    further edges of `P` beyond `v`. -/
theorem minimal_leaf (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1) :
    ∃ f g, P f ∧ P g ∧ f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ G.Inc f (G.ends e).2 ∧ G.Inc g (G.ends e).2 ∧
      (∃ h1 h2, Further P (G.ends e).2 f h1 ∧ Further P (G.ends e).2 f h2 ∧ h1 ≠ h2) ∧
      (∃ h1 h2, Further P (G.ends e).2 g h1 ∧ Further P (G.ends e).2 g h2 ∧ h1 ≠ h2) := by
  -- a colouring of P − e
  have hPe' : Colourable (fun f => P f ∧ f ≠ e) 6 := by
    apply hmin.2
    exact ⟨fun f hf => hf.1, e, hPe, fun h => h.2 rfl⟩
  obtain ⟨φ, hφ⟩ := hPe'
  have hev : G.Inc e (G.ends e).2 := joins_inc_right (joins_ends e)
  -- first other edge at v
  by_cases hf : ∃ f, P f ∧ f ≠ e ∧ G.Inc f (G.ends e).2
  · obtain ⟨f, hPf, hfe, hfv⟩ := hf
    obtain ⟨p1, p2, hp⟩ := further_two hsub P (G.ends e).2 f hfv φ (φ f)
    by_cases hg : ∃ g, P g ∧ g ≠ e ∧ G.Inc g (G.ends e).2 ∧ g ≠ f
    · obtain ⟨g, hPg, hge, hgv, hgf⟩ := hg
      obtain ⟨q1, q2, hq⟩ := further_two hsub P (G.ends e).2 g hgv φ (φ g)
      -- every other edge at v is f or g
      have hfg : ∀ f', P f' → f' ≠ e → G.Inc f' (G.ends e).2 → f' = f ∨ f' = g := by
        intro f' hPf' hf'e hf'v
        by_cases h1 : f' = f
        · exact Or.inl h1
        by_cases h2 : f' = g
        · exact Or.inr h2
        exact absurd (hsub (G.ends e).2 f' f g e hf'v hfv hgv hev h1 h2 hf'e (fun h => hgf h.symm) hfe hge) id
      by_cases htf : ∃ h1 h2, Further P (G.ends e).2 f h1 ∧ Further P (G.ends e).2 f h2 ∧ h1 ≠ h2
      · by_cases htg : ∃ h1 h2, Further P (G.ends e).2 g h1 ∧ Further P (G.ends e).2 g h2 ∧ h1 ≠ h2
        · exact ⟨f, g, hPf, hPg, hfe, hge, fun h => hgf h.symm, hfv, hgv, htf, htg⟩
        · -- g has at most one further edge: five colours suffice
          obtain ⟨q, hq1⟩ := further_one P (G.ends e).2 g htg φ (φ g)
          exfalso
          apply hmin.1
          apply colourable_of_five e hPe hleaf φ hφ (φ f) (φ g) p1 p2 q
          · intro f' hPf' hf'e hf'v
            rcases hfg f' hPf' hf'e hf'v with h | h
            · exact Or.inl (by rw [h])
            · exact Or.inr (Or.inl (by rw [h]))
          · intro f' h hPf' hf'e hf'v hfur
            rcases hfg f' hPf' hf'e hf'v with h' | h'
            · subst h'
              rcases hp h hfur with h'' | h''
              · exact Or.inr (Or.inr (Or.inl h''))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
            · subst h'
              exact Or.inr (Or.inr (Or.inr (Or.inr (hq1 h hfur))))
      · obtain ⟨p, hp1⟩ := further_one P (G.ends e).2 f htf φ (φ f)
        exfalso
        apply hmin.1
        apply colourable_of_five e hPe hleaf φ hφ (φ f) (φ g) p q1 q2
        · intro f' hPf' hf'e hf'v
          rcases hfg f' hPf' hf'e hf'v with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (Or.inl (by rw [h]))
        · intro f' h hPf' hf'e hf'v hfur
          rcases hfg f' hPf' hf'e hf'v with h' | h'
          · subst h'
            exact Or.inr (Or.inr (Or.inl (hp1 h hfur)))
          · subst h'
            rcases hq h hfur with h'' | h''
            · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h'')))
    · -- f is the only other edge at v: three colours suffice
      exfalso
      apply hmin.1
      apply colourable_of_five e hPe hleaf φ hφ (φ f) p1 p2 p1 p1
      · intro f' hPf' hf'e hf'v
        by_cases h : f' = f
        · exact Or.inl (by rw [h])
        · exact absurd ⟨f', hPf', hf'e, hf'v, h⟩ hg
      · intro f' h hPf' hf'e hf'v hfur
        by_cases h' : f' = f
        · subst h'
          rcases hp h hfur with h'' | h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr (Or.inl h''))
        · exact absurd ⟨f', hPf', hf'e, hf'v, h'⟩ hg
  · -- no other edge at v: any colour works
    exfalso
    apply hmin.1
    apply colourable_of_five e hPe hleaf φ hφ 0 0 0 0 0
    · intro f' hPf' hf'e hf'v
      exact absurd ⟨f', hPf', hf'e, hf'v⟩ hf
    · intro f' h hPf' hf'e hf'v _
      exact absurd ⟨f', hPf', hf'e, hf'v⟩ hf

/-- **Corollary.**  In a minimal counterexample, a leaf never hangs from a vertex with at most one other edge. -/
theorem minimal_leaf_neighbour_degree (hsub : Subcubic G) (P : Fin G.m → Prop)
    (hmin : MinimalCounterexample P 6) (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1) :
    ∃ f g, P f ∧ P g ∧ f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ G.Inc f (G.ends e).2 ∧ G.Inc g (G.ends e).2 := by
  obtain ⟨f, g, hPf, hPg, hfe, hge, hfg, hfv, hgv, -, -⟩ := minimal_leaf hsub P hmin e hPe hleaf
  exact ⟨f, g, hPf, hPg, hfe, hge, hfg, hfv, hgv⟩

/-! ### the rainbow lemma: the sharp form -/


/-- if the six colours seen from a pendant edge are covered by five values, the edge can be coloured -/
theorem colourable_of_six_cover {P : Fin G.m → Prop} (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) (c1 c2 c3 c4 c5 c6 a1 a2 a3 a4 a5 : Fin 6)
    (hcov : ∀ c : Fin 6, (c = c1 ∨ c = c2 ∨ c = c3 ∨ c = c4 ∨ c = c5 ∨ c = c6) →
      (c = a1 ∨ c = a2 ∨ c = a3 ∨ c = a4 ∨ c = a5))
    (hv : ∀ f, P f → f ≠ e → G.Inc f (G.ends e).2 →
      φ f = c1 ∨ φ f = c2 ∨ φ f = c3 ∨ φ f = c4 ∨ φ f = c5 ∨ φ f = c6)
    (hw : ∀ f h, P f → f ≠ e → G.Inc f (G.ends e).2 → Further P (G.ends e).2 f h →
      φ h = c1 ∨ φ h = c2 ∨ φ h = c3 ∨ φ h = c4 ∨ φ h = c5 ∨ φ h = c6) :
    Colourable P 6 :=
  colourable_of_five e hPe hleaf φ hφ a1 a2 a3 a4 a5
    (fun f hf hfe hfv => hcov _ (hv f hf hfe hfv))
    (fun f h hf hfe hfv hfh => hcov _ (hw f h hf hfe hfv hfh))

/-- six colours seen from a blocked pendant edge are pairwise distinct -/
theorem rainbow_of_blocked {P : Fin G.m → Prop} (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) (c1 c2 c3 c4 c5 c6 : Fin 6)
    (hv : ∀ f, P f → f ≠ e → G.Inc f (G.ends e).2 →
      φ f = c1 ∨ φ f = c2 ∨ φ f = c3 ∨ φ f = c4 ∨ φ f = c5 ∨ φ f = c6)
    (hw : ∀ f h, P f → f ≠ e → G.Inc f (G.ends e).2 → Further P (G.ends e).2 f h →
      φ h = c1 ∨ φ h = c2 ∨ φ h = c3 ∨ φ h = c4 ∨ φ h = c5 ∨ φ h = c6)
    (hnot : ¬ Colourable P 6) :
    c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c4 ∧ c1 ≠ c5 ∧ c1 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c4 ∧ c2 ≠ c5 ∧ c2 ≠ c6 ∧
      c3 ≠ c4 ∧ c3 ≠ c5 ∧ c3 ≠ c6 ∧ c4 ≠ c5 ∧ c4 ≠ c6 ∧ c5 ≠ c6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c2 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c2 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c2 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c2 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c2 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c3 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c2 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c2 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c2 c4 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c2 c3 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c2 c3 c5 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)
  · intro h; exact hnot (colourable_of_six_cover e hPe hleaf φ hφ c1 c2 c3 c4 c5 c6 c1 c2 c3 c4 c6
      (by intro c hc; rcases hc with hc|hc|hc|hc|hc|hc <;> simp [hc, h]) hv hw)


/-- **Rainbow lemma.**  Let `u` be a leaf of a minimal non-star-6-colourable edge set `P` of a subcubic
    multigraph, `e = uv`, and `φ` any star 6-colouring of `P − e`.  Then `v` has two further edges `f, g`, `f` has
    two further edges `f1, f2` beyond `v`, `g` has `g1, g2`, and the six colours `φ f, φ g, φ f1, φ f2, φ g1, φ g2`
    are pairwise distinct.  (In particular the six edges are pairwise distinct: `v`, `w1`, `w2` are three distinct
    vertices of degree three and no two of the six edges are parallel or coincide.) -/
theorem minimal_leaf_rainbow (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) :
    ∃ f g f1 f2 g1 g2, P f ∧ P g ∧ f ≠ e ∧ g ≠ e ∧ G.Inc f (G.ends e).2 ∧ G.Inc g (G.ends e).2 ∧
      Further P (G.ends e).2 f f1 ∧ Further P (G.ends e).2 f f2 ∧
      Further P (G.ends e).2 g g1 ∧ Further P (G.ends e).2 g g2 ∧
      (φ f ≠ φ g ∧ φ f ≠ φ f1 ∧ φ f ≠ φ f2 ∧ φ f ≠ φ g1 ∧ φ f ≠ φ g2 ∧
       φ g ≠ φ f1 ∧ φ g ≠ φ f2 ∧ φ g ≠ φ g1 ∧ φ g ≠ φ g2 ∧
       φ f1 ≠ φ f2 ∧ φ f1 ≠ φ g1 ∧ φ f1 ≠ φ g2 ∧ φ f2 ≠ φ g1 ∧ φ f2 ≠ φ g2 ∧ φ g1 ≠ φ g2) := by
  obtain ⟨f, g, hPf, hPg, hfe, hge, hfg, hfv, hgv, ⟨f1, f2, hf1, hf2, hf12⟩, ⟨g1, g2, hg1, hg2, hg12⟩⟩ :=
    minimal_leaf hsub P hmin e hPe hleaf
  have hev : G.Inc e (G.ends e).2 := joins_inc_right (joins_ends e)
  -- every other edge at v is f or g
  have hatv : ∀ f', P f' → f' ≠ e → G.Inc f' (G.ends e).2 → f' = f ∨ f' = g := by
    intro f' hPf' hf'e hf'v
    by_cases h1 : f' = f
    · exact Or.inl h1
    by_cases h2 : f' = g
    · exact Or.inr h2
    exact absurd (hsub (G.ends e).2 f' f g e hf'v hfv hgv hev h1 h2 hf'e hfg hfe hge) id
  -- the further edges of an edge `a` at `v` with two distinct further edges `a1 ≠ a2` are exactly `a1, a2`
  have hfur : ∀ a a1 a2, G.Inc a (G.ends e).2 → Further P (G.ends e).2 a a1 → Further P (G.ends e).2 a a2 →
      a1 ≠ a2 → ∀ h, Further P (G.ends e).2 a h → h = a1 ∨ h = a2 := by
    intro a a1 a2 hav ha1 ha2 ha12 h hh
    obtain ⟨_, ha1a, x1, hx1v, hax1, ha1x1⟩ := ha1
    obtain ⟨_, ha2a, x2, hx2v, hax2, ha2x2⟩ := ha2
    obtain ⟨_, hha, x, hxv, hax, hhx⟩ := hh
    have e1 : x = x1 := inc_ne_unique hav hax hax1 hxv hx1v
    have e2 : x2 = x1 := inc_ne_unique hav hax2 hax1 hx2v hx1v
    have hhx1 : G.Inc h x1 := e1 ▸ hhx
    have ha2x1 : G.Inc a2 x1 := e2 ▸ ha2x2
    by_cases h1 : h = a1
    · exact Or.inl h1
    by_cases h2 : h = a2
    · exact Or.inr h2
    exact absurd (hsub x1 h a1 a2 a hhx1 ha1x1 ha2x1 hax1 h1 h2 hha ha12 ha1a ha2a) id
  have hfurf := hfur f f1 f2 hfv hf1 hf2 hf12
  have hfurg := hfur g g1 g2 hgv hg1 hg2 hg12
  refine ⟨f, g, f1, f2, g1, g2, hPf, hPg, hfe, hge, hfv, hgv, hf1, hf2, hg1, hg2, ?_⟩
  apply rainbow_of_blocked e hPe hleaf φ hφ (φ f) (φ g) (φ f1) (φ f2) (φ g1) (φ g2) _ _ hmin.1
  · intro f' hPf' hf'e hf'v
    rcases hatv f' hPf' hf'e hf'v with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
  · intro f' h hPf' hf'e hf'v hh
    rcases hatv f' hPf' hf'e hf'v with h' | h'
    · subst h'
      rcases hfurf h hh with h'' | h''
      · exact Or.inr (Or.inr (Or.inl (by rw [h''])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h'']))))
    · subst h'
      rcases hfurg h hh with h'' | h''
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h''])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h''])))))

/-- **Corollary.**  The six edges around a leaf of a minimal counterexample are pairwise distinct; in particular
    `f` and `g` are not parallel (else `g` would be a further edge of `f`) and no edge joins `w1` to `w2`. -/
theorem minimal_leaf_six_edges (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1) :
    ∃ f g f1 f2 g1 g2, P f ∧ P g ∧ f ≠ e ∧ g ≠ e ∧ G.Inc f (G.ends e).2 ∧ G.Inc g (G.ends e).2 ∧
      Further P (G.ends e).2 f f1 ∧ Further P (G.ends e).2 f f2 ∧
      Further P (G.ends e).2 g g1 ∧ Further P (G.ends e).2 g g2 ∧
      (f ≠ g ∧ f ≠ f1 ∧ f ≠ f2 ∧ f ≠ g1 ∧ f ≠ g2 ∧ g ≠ f1 ∧ g ≠ f2 ∧ g ≠ g1 ∧ g ≠ g2 ∧
       f1 ≠ f2 ∧ f1 ≠ g1 ∧ f1 ≠ g2 ∧ f2 ≠ g1 ∧ f2 ≠ g2 ∧ g1 ≠ g2) := by
  have hPe' : Colourable (fun f => P f ∧ f ≠ e) 6 := by
    apply hmin.2
    exact ⟨fun f hf => hf.1, e, hPe, fun h => h.2 rfl⟩
  obtain ⟨φ, hφ⟩ := hPe'
  obtain ⟨f, g, f1, f2, g1, g2, hPf, hPg, hfe, hge, hfv, hgv, hf1, hf2, hg1, hg2,
    d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ :=
    minimal_leaf_rainbow hsub P hmin e hPe hleaf φ hφ
  refine ⟨f, g, f1, f2, g1, g2, hPf, hPg, hfe, hge, hfv, hgv, hf1, hf2, hg1, hg2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact d1 (by rw [h])
  · intro h; exact d2 (by rw [h])
  · intro h; exact d3 (by rw [h])
  · intro h; exact d4 (by rw [h])
  · intro h; exact d5 (by rw [h])
  · intro h; exact d6 (by rw [h])
  · intro h; exact d7 (by rw [h])
  · intro h; exact d8 (by rw [h])
  · intro h; exact d9 (by rw [h])
  · intro h; exact d10 (by rw [h])
  · intro h; exact d11 (by rw [h])
  · intro h; exact d12 (by rw [h])
  · intro h; exact d13 (by rw [h])
  · intro h; exact d14 (by rw [h])
  · intro h; exact d15 (by rw [h])

end MGraph
