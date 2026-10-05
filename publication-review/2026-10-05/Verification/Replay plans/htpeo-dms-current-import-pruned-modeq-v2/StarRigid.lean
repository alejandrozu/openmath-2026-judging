/-
  StarRigid.lean — the exact structure of a leaf in a minimal counterexample ("the rigid leaf configuration").

  `StarLeaf.lean` used a *sufficient* condition for extending a pendant edge.  Here the condition is made *exact*
  (`pendant_exact` / `pendant_blocked`): colour `y` fails at the pendant edge `e = uv` only if `y` is the colour of
  an edge `f` at `v`, or `y` is the colour of an edge `h` beyond `f` that carries a *blocking witness* — an edge `d`
  beyond `h`, on a genuine 3-path `v–x–t–s`, with `φ d = φ f`.

  Consequences, for EVERY star 6-colouring `φ` of `P − e` (`P` minimal non-star-6-colourable, subcubic):
  `RigidLeaf P e φ` (theorem `minimal_leaf_rigid`):
    * `v` has exactly the two other edges `f = v w1`, `g = v w2`, with `w1 ≠ w2`;
    * `w1` has exactly the two further edges `f1 = w1 x1`, `f2 = w1 x2`; `w2` has `g1 = w2 z1`, `g2 = w2 z2`;
    * `v, w1, w2` are distinct, `{x1, x2}` and `{z1, z2}` are disjoint from each other and from `{v, w1, w2}`
      (no triangle or 4-cycle through `v`; `N(w1) ∩ N(w2) = {v}`);
    * the six colours are pairwise distinct and exhaust `Fin 6`;
    * each `x_i` carries a non-loop, non-parallel edge `d_i` (to `s_i ∉ {v, w1, x_i}`) of colour `φ f`, and each `z_j`
      one of colour `φ g`  (so the far neighbours have degree ≥ 2 and the colour of `f` reappears beyond both `f1`
      and `f2`, that of `g` beyond both `g1` and `g2`);
  and (`rigid_no_alt_f`, `rigid_no_alt_g`) the configuration is rigid: neither `f` nor `g` admits any other colour.

  This is exactly the configuration that survives every counting argument; excluding it is a consequence of the
  DMS conjecture with no known independent proof (cf. Lei–Shi–Song, JGT 2018, Lemma 3.1, who keep 1-vertices and
  need mad < 5/2 to finish by discharging).  No `sorry`, no `native_decide`.
-/
import StarLeaf

namespace MGraph
variable {G : MGraph}

theorem joins_symm {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : G.Joins f y x := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- the endpoint of a non-loop edge away from `v` is unique -/
theorem joins_other {f : Fin G.m} {v x x' : Fin G.n} (h : G.Joins f v x) (h' : G.Joins f v x') (hx : x ≠ v) :
    x' = x := by
  rcases joins_unique h h' with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact h2.symm
  · exact absurd h2 hx

/-- an edge with both endpoints away from `v = (ends e).2` is not `e` -/
theorem ne_e_of_far {a e : Fin G.m} {x y : Fin G.n} (h : G.Joins a x y) (hx : x ≠ (G.ends e).2)
    (hy : y ≠ (G.ends e).2) : a ≠ e := by
  intro hae
  rw [hae] at h
  rcases joins_unique h (joins_ends e) with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact hy h2
  · exact hx h1

/-- in a subcubic graph, the edges at `v` other than `e` are `f` and `g` (given three distinct ones) -/
theorem at_v_two (hsub : Subcubic G) {P : Fin G.m → Prop} {v : Fin G.n} {e f g : Fin G.m}
    (hev : G.Inc e v) (hfv : G.Inc f v) (hgv : G.Inc g v) (hfe : f ≠ e) (hge : g ≠ e) (hfg : f ≠ g) :
    ∀ f', P f' → f' ≠ e → G.Inc f' v → f' = f ∨ f' = g := by
  intro f' _ hf'e hf'v
  by_cases h1 : f' = f
  · exact Or.inl h1
  by_cases h2 : f' = g
  · exact Or.inr h2
  exact absurd (hsub v f' f g e hf'v hfv hgv hev h1 h2 hf'e hfg hfe hge) id

/-- the further edges of `a` beyond `v` are exactly `a1, a2` when these are two distinct ones -/
theorem further_eq (hsub : Subcubic G) {P : Fin G.m → Prop} {v : Fin G.n} {a a1 a2 : Fin G.m}
    (hav : G.Inc a v) (ha1 : Further P v a a1) (ha2 : Further P v a a2) (ha12 : a1 ≠ a2) :
    ∀ h, Further P v a h → h = a1 ∨ h = a2 := by
  intro h hh
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

/-! ### the exact extension condition -/

/-- **Blocking witness** for the colour of `h` at the pendant edge at `v`: `f` joins `v` to `x`, `h` joins `x`
    to `t`, `d` joins `t` to `s`, with `v, x, t, s` pairwise distinct, `d ∈ P`, `d ≠ h` and `φ d = φ f`.  With
    `φ h = y` this is precisely a bicoloured walk `u v x t s` once the pendant edge `uv` receives colour `y`. -/
def Witness (P : Fin G.m → Prop) (v : Fin G.n) (φ : Fin G.m → Fin 6) (f h : Fin G.m) : Prop :=
  ∃ x t s d, x ≠ v ∧ t ≠ v ∧ t ≠ x ∧ s ≠ v ∧ s ≠ x ∧ s ≠ t ∧
    G.Joins f v x ∧ G.Joins h x t ∧ G.Joins d t s ∧ P d ∧ d ≠ h ∧ φ d = φ f

/-- **Exact extension.**  A colour `y` extends `φ` to the pendant edge `e` as soon as it differs from the colours
    at `v` and no edge `h` beyond an edge `f` at `v` has both `φ h = y` and a blocking witness. -/
theorem pendant_exact {P : Fin G.m → Prop} (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) (y : Fin 6)
    (hy1 : ∀ f, P f → f ≠ e → G.Inc f (G.ends e).2 → φ f ≠ y)
    (hy2 : ∀ f h, P f → f ≠ e → G.Inc f (G.ends e).2 → P h → h ≠ f → φ h = y →
      ¬ Witness P (G.ends e).2 φ f h) :
    StarOn P 6 (fun f => if f = e then y else φ f) := by
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
    · have h1 : w.e1 ≠ e := fun h => w.e1_ne_e2 (h.trans h2.symm)
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
    · -- e in position 1: v0 = u, v1 = v; the walk continues f = e2, h = e3, d = e4
      have h4 : w.e4 ≠ e := fun h => w.e1_ne_e4 (h1.trans h.symm)
      have hj : G.Joins e w.v0 w.v1 := by rw [← h1]; exact w.h1
      rcases joins_unique (joins_ends e) hj with ⟨_, hv1⟩ | ⟨hu1, _⟩
      · rw [h1, ce, cf h3] at hb13
        rw [cf h2, cf h4] at hb24
        have hjf : G.Joins w.e2 (G.ends e).2 w.v2 := by rw [hv1]; exact w.h2
        apply hy2 w.e2 w.e3 hp2 h2 (hv1 ▸ w.inc_e2_v1) hp3 (fun h => w.e2_ne_e3 h.symm) hb13.symm
        exact ⟨w.v2, w.v3, w.v4, w.e4, fun h => w.d12 (h.trans hv1).symm, fun h => w.d13 (h.trans hv1).symm,
          w.d23.symm, fun h => w.d14 (h.trans hv1).symm, w.d24.symm, w.d34.symm, hjf, w.h3, w.h4, hp4,
          w.e3_ne_e4.symm, hb24.symm⟩
      · exact hleaf w.e2 hp2 h2 (hu1 ▸ w.inc_e2_v1)
    by_cases h4 : w.e4 = e
    · -- e in position 4: v3 = v, v4 = u; the walk read backwards is f = e3, h = e2, d = e1
      have hj : G.Joins e w.v3 w.v4 := by rw [← h4]; exact w.h4
      rcases joins_unique (joins_ends e) hj with ⟨hu3, _⟩ | ⟨_, hv3⟩
      · exact hleaf w.e3 hp3 h3 (hu3 ▸ w.inc_e3_v3)
      · rw [h4, ce, cf h2] at hb24
        rw [cf h1, cf h3] at hb13
        have hjf : G.Joins w.e3 (G.ends e).2 w.v2 := by rw [hv3]; exact joins_symm w.h3
        apply hy2 w.e3 w.e2 hp3 h3 (hv3 ▸ w.inc_e3_v3) hp2 w.e2_ne_e3 hb24
        exact ⟨w.v2, w.v1, w.v0, w.e1, fun h => w.d23 (h.trans hv3), fun h => w.d13 (h.trans hv3),
          w.d12, fun h => w.d03 (h.trans hv3), w.d02, w.d01, hjf, joins_symm w.h2, joins_symm w.h1, hp1,
          w.e1_ne_e2, hb13⟩
    rw [cf h1, cf h3] at hb13
    rw [cf h2, cf h4] at hb24
    exact hφ.2 w ⟨hp1, h1⟩ ⟨hp2, h2⟩ ⟨hp3, h3⟩ ⟨hp4, h4⟩ ⟨hb13, hb24⟩

/-- **Exact blocking.**  If colour `y` does not extend `φ` to the pendant edge, some edge `f` at `v` either has
    colour `y` or has an edge `h` beyond it with `φ h = y` and a blocking witness. -/
theorem pendant_blocked {P : Fin G.m → Prop} (e : Fin G.m) (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) (y : Fin 6)
    (hbad : ¬ StarOn P 6 (fun f => if f = e then y else φ f)) :
    ∃ f, P f ∧ f ≠ e ∧ G.Inc f (G.ends e).2 ∧
      (φ f = y ∨ ∃ h, P h ∧ h ≠ f ∧ φ h = y ∧ Witness P (G.ends e).2 φ f h) := by
  apply Classical.byContradiction
  intro hno
  apply hbad
  apply pendant_exact e hPe hleaf φ hφ y
  · intro f hf hfe hfv hfy
    exact hno ⟨f, hf, hfe, hfv, Or.inl hfy⟩
  · intro f h hf hfe hfv hPh hhf hhy hw
    exact hno ⟨f, hf, hfe, hfv, Or.inr ⟨h, hPh, hhf, hhy, hw⟩⟩

/-- in a minimal counterexample every colour `y` is the colour of `f`, of `g`, or of a witnessed edge beyond them -/
theorem blocked_source (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ)
    {f g : Fin G.m} (hfe : f ≠ e) (hge : g ≠ e) (hfv : G.Inc f (G.ends e).2) (hgv : G.Inc g (G.ends e).2)
    (hfg : f ≠ g) (y : Fin 6) :
    y = φ f ∨ y = φ g ∨
      ∃ f' h, (f' = f ∨ f' = g) ∧ Further P (G.ends e).2 f' h ∧ φ h = y ∧ Witness P (G.ends e).2 φ f' h := by
  have hev : G.Inc e (G.ends e).2 := joins_inc_right (joins_ends e)
  have hbad : ¬ StarOn P 6 (fun x => if x = e then y else φ x) := fun h => hmin.1 ⟨_, h⟩
  obtain ⟨f', hPf', hf'e, hf'v, hcase⟩ := pendant_blocked e hPe hleaf φ hφ y hbad
  have hf'fg : f' = f ∨ f' = g := at_v_two hsub hev hfv hgv hfe hge hfg f' hPf' hf'e hf'v
  rcases hcase with hcol | ⟨h, hPh, hhf', hhy, hw⟩
  · rcases hf'fg with h | h
    · exact Or.inl (by rw [← h]; exact hcol.symm)
    · exact Or.inr (Or.inl (by rw [← h]; exact hcol.symm))
  · refine Or.inr (Or.inr ⟨f', h, hf'fg, ?_, hhy, hw⟩)
    obtain ⟨x, _, _, _, hxv, _, _, _, _, _, hjf, hjh, _, _, _, _⟩ := hw
    exact ⟨hPh, hhf', x, hxv, joins_inc_right hjf, joins_inc_left hjh⟩

/-! ### the rigid leaf configuration -/

/-- **The rigid leaf configuration** around a pendant edge `e = uv` (`v = (ends e).2`), relative to a colouring
    `φ` of the other edges.  `f = v w1`, `g = v w2`; `f1 = w1 x1`, `f2 = w1 x2`; `g1 = w2 z1`, `g2 = w2 z2`;
    `d1 = x1 s1`, `d2 = x2 s2` of colour `φ f`; `d3 = z1 s3`, `d4 = z2 s4` of colour `φ g`. -/
structure RigidLeaf (P : Fin G.m → Prop) (e : Fin G.m) (φ : Fin G.m → Fin 6) where
  f : Fin G.m
  g : Fin G.m
  f1 : Fin G.m
  f2 : Fin G.m
  g1 : Fin G.m
  g2 : Fin G.m
  d1 : Fin G.m
  d2 : Fin G.m
  d3 : Fin G.m
  d4 : Fin G.m
  w1 : Fin G.n
  w2 : Fin G.n
  x1 : Fin G.n
  x2 : Fin G.n
  z1 : Fin G.n
  z2 : Fin G.n
  s1 : Fin G.n
  s2 : Fin G.n
  s3 : Fin G.n
  s4 : Fin G.n
  -- membership
  Pf : P f
  Pg : P g
  Pf1 : P f1
  Pf2 : P f2
  Pg1 : P g1
  Pg2 : P g2
  Pd1 : P d1
  Pd2 : P d2
  Pd3 : P d3
  Pd4 : P d4
  fe : f ≠ e
  ge : g ≠ e
  -- incidences
  jf : G.Joins f (G.ends e).2 w1
  jg : G.Joins g (G.ends e).2 w2
  jf1 : G.Joins f1 w1 x1
  jf2 : G.Joins f2 w1 x2
  jg1 : G.Joins g1 w2 z1
  jg2 : G.Joins g2 w2 z2
  jd1 : G.Joins d1 x1 s1
  jd2 : G.Joins d2 x2 s2
  jd3 : G.Joins d3 z1 s3
  jd4 : G.Joins d4 z2 s4
  -- distinct vertices (x1 = x2 and z1 = z2, i.e. parallel further edges, are not excluded)
  w1v : w1 ≠ (G.ends e).2
  w2v : w2 ≠ (G.ends e).2
  w12 : w1 ≠ w2
  x1v : x1 ≠ (G.ends e).2
  x1w1 : x1 ≠ w1
  x1w2 : x1 ≠ w2
  x2v : x2 ≠ (G.ends e).2
  x2w1 : x2 ≠ w1
  x2w2 : x2 ≠ w2
  z1v : z1 ≠ (G.ends e).2
  z1w1 : z1 ≠ w1
  z1w2 : z1 ≠ w2
  z2v : z2 ≠ (G.ends e).2
  z2w1 : z2 ≠ w1
  z2w2 : z2 ≠ w2
  x1z1 : x1 ≠ z1
  x1z2 : x1 ≠ z2
  x2z1 : x2 ≠ z1
  x2z2 : x2 ≠ z2
  -- the witness edges are neither loops nor parallel to `f_i`/`g_j`, and lead away from `v`
  s1v : s1 ≠ (G.ends e).2
  s1x1 : s1 ≠ x1
  s1w1 : s1 ≠ w1
  s2v : s2 ≠ (G.ends e).2
  s2x2 : s2 ≠ x2
  s2w1 : s2 ≠ w1
  s3v : s3 ≠ (G.ends e).2
  s3z1 : s3 ≠ z1
  s3w2 : s3 ≠ w2
  s4v : s4 ≠ (G.ends e).2
  s4z2 : s4 ≠ z2
  s4w2 : s4 ≠ w2
  d1f1 : d1 ≠ f1
  d2f2 : d2 ≠ f2
  d3g1 : d3 ≠ g1
  d4g2 : d4 ≠ g2
  -- there are no other edges at v, w1, w2
  atv : ∀ h, P h → h ≠ e → G.Inc h (G.ends e).2 → h = f ∨ h = g
  atw1 : ∀ h, P h → h ≠ f → G.Inc h w1 → h = f1 ∨ h = f2
  atw2 : ∀ h, P h → h ≠ g → G.Inc h w2 → h = g1 ∨ h = g2
  -- colours
  cd1 : φ d1 = φ f
  cd2 : φ d2 = φ f
  cd3 : φ d3 = φ g
  cd4 : φ d4 = φ g
  c_fg : φ f ≠ φ g
  c_ff1 : φ f ≠ φ f1
  c_ff2 : φ f ≠ φ f2
  c_fg1 : φ f ≠ φ g1
  c_fg2 : φ f ≠ φ g2
  c_gf1 : φ g ≠ φ f1
  c_gf2 : φ g ≠ φ f2
  c_gg1 : φ g ≠ φ g1
  c_gg2 : φ g ≠ φ g2
  c_f1f2 : φ f1 ≠ φ f2
  c_f1g1 : φ f1 ≠ φ g1
  c_f1g2 : φ f1 ≠ φ g2
  c_f2g1 : φ f2 ≠ φ g1
  c_f2g2 : φ f2 ≠ φ g2
  c_g1g2 : φ g1 ≠ φ g2
  cover : ∀ y : Fin 6, y = φ f ∨ y = φ g ∨ y = φ f1 ∨ y = φ f2 ∨ y = φ g1 ∨ y = φ g2

/-- the configuration is symmetric in the two sides of `v` -/
def RigidLeaf.swap {P : Fin G.m → Prop} {e : Fin G.m} {φ : Fin G.m → Fin 6} (R : RigidLeaf P e φ) :
    RigidLeaf P e φ where
  f := R.g
  g := R.f
  f1 := R.g1
  f2 := R.g2
  g1 := R.f1
  g2 := R.f2
  d1 := R.d3
  d2 := R.d4
  d3 := R.d1
  d4 := R.d2
  w1 := R.w2
  w2 := R.w1
  x1 := R.z1
  x2 := R.z2
  z1 := R.x1
  z2 := R.x2
  s1 := R.s3
  s2 := R.s4
  s3 := R.s1
  s4 := R.s2
  Pf := R.Pg
  Pg := R.Pf
  Pf1 := R.Pg1
  Pf2 := R.Pg2
  Pg1 := R.Pf1
  Pg2 := R.Pf2
  Pd1 := R.Pd3
  Pd2 := R.Pd4
  Pd3 := R.Pd1
  Pd4 := R.Pd2
  fe := R.ge
  ge := R.fe
  jf := R.jg
  jg := R.jf
  jf1 := R.jg1
  jf2 := R.jg2
  jg1 := R.jf1
  jg2 := R.jf2
  jd1 := R.jd3
  jd2 := R.jd4
  jd3 := R.jd1
  jd4 := R.jd2
  w1v := R.w2v
  w2v := R.w1v
  w12 := R.w12.symm
  x1v := R.z1v
  x1w1 := R.z1w2
  x1w2 := R.z1w1
  x2v := R.z2v
  x2w1 := R.z2w2
  x2w2 := R.z2w1
  z1v := R.x1v
  z1w1 := R.x1w2
  z1w2 := R.x1w1
  z2v := R.x2v
  z2w1 := R.x2w2
  z2w2 := R.x2w1
  x1z1 := R.x1z1.symm
  x1z2 := R.x2z1.symm
  x2z1 := R.x1z2.symm
  x2z2 := R.x2z2.symm
  s1v := R.s3v
  s1x1 := R.s3z1
  s1w1 := R.s3w2
  s2v := R.s4v
  s2x2 := R.s4z2
  s2w1 := R.s4w2
  s3v := R.s1v
  s3z1 := R.s1x1
  s3w2 := R.s1w1
  s4v := R.s2v
  s4z2 := R.s2x2
  s4w2 := R.s2w1
  d1f1 := R.d3g1
  d2f2 := R.d4g2
  d3g1 := R.d1f1
  d4g2 := R.d2f2
  atv := fun h hP hne hinc => (R.atv h hP hne hinc).symm
  atw1 := R.atw2
  atw2 := R.atw1
  cd1 := R.cd3
  cd2 := R.cd4
  cd3 := R.cd1
  cd4 := R.cd2
  c_fg := R.c_fg.symm
  c_ff1 := R.c_gg1
  c_ff2 := R.c_gg2
  c_fg1 := R.c_gf1
  c_fg2 := R.c_gf2
  c_gf1 := R.c_fg1
  c_gf2 := R.c_fg2
  c_gg1 := R.c_ff1
  c_gg2 := R.c_ff2
  c_f1f2 := R.c_g1g2
  c_f1g1 := R.c_f1g1.symm
  c_f1g2 := R.c_f2g1.symm
  c_f2g1 := R.c_f1g2.symm
  c_f2g2 := R.c_f2g2.symm
  c_g1g2 := R.c_f1f2
  cover := fun y => by
    rcases R.cover y with h | h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- **Main theorem.**  In a minimal non-star-6-colourable edge set of a subcubic multigraph, every leaf sits in
    the rigid configuration, for every star 6-colouring `φ` of the other edges. -/
theorem minimal_leaf_rigid (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) :
    Nonempty (RigidLeaf P e φ) := by
  obtain ⟨f, g, f1, f2, g1, g2, hPf, hPg, hfe, hge, hfv, hgv, hf1, hf2, hg1, hg2,
    c_fg, c_ff1, c_ff2, c_fg1, c_fg2, c_gf1, c_gf2, c_gg1, c_gg2, c_f1f2, c_f1g1, c_f1g2, c_f2g1, c_f2g2,
    c_g1g2⟩ := minimal_leaf_rainbow hsub P hmin e hPe hleaf φ hφ
  have hev : G.Inc e (G.ends e).2 := joins_inc_right (joins_ends e)
  have hfg : f ≠ g := fun h => c_fg (by rw [h])
  have hf12 : f1 ≠ f2 := fun h => c_f1f2 (by rw [h])
  have hg12 : g1 ≠ g2 := fun h => c_g1g2 (by rw [h])
  have hfurf := further_eq hsub hfv hf1 hf2 hf12
  have hfurg := further_eq hsub hgv hg1 hg2 hg12
  have hsrc := blocked_source hsub P hmin e hPe hleaf φ hφ hfe hge hfv hgv hfg
  -- the four witnesses
  have wf1 : Witness P (G.ends e).2 φ f f1 := by
    rcases hsrc (φ f1) with h | h | ⟨f', h, hf', hfur, hcol, hw⟩
    · exact absurd h.symm c_ff1
    · exact absurd h.symm c_gf1
    · rcases hf' with hf' | hf'
      · rw [hf'] at hfur hw
        rcases hfurf h hfur with hh | hh
        · rw [hh] at hw; exact hw
        · rw [hh] at hcol; exact absurd hcol c_f1f2.symm
      · rw [hf'] at hfur
        rcases hfurg h hfur with hh | hh
        · rw [hh] at hcol; exact absurd hcol c_f1g1.symm
        · rw [hh] at hcol; exact absurd hcol c_f1g2.symm
  have wf2 : Witness P (G.ends e).2 φ f f2 := by
    rcases hsrc (φ f2) with h | h | ⟨f', h, hf', hfur, hcol, hw⟩
    · exact absurd h.symm c_ff2
    · exact absurd h.symm c_gf2
    · rcases hf' with hf' | hf'
      · rw [hf'] at hfur hw
        rcases hfurf h hfur with hh | hh
        · rw [hh] at hcol; exact absurd hcol c_f1f2
        · rw [hh] at hw; exact hw
      · rw [hf'] at hfur
        rcases hfurg h hfur with hh | hh
        · rw [hh] at hcol; exact absurd hcol c_f2g1.symm
        · rw [hh] at hcol; exact absurd hcol c_f2g2.symm
  have wg1 : Witness P (G.ends e).2 φ g g1 := by
    rcases hsrc (φ g1) with h | h | ⟨f', h, hf', hfur, hcol, hw⟩
    · exact absurd h.symm c_fg1
    · exact absurd h.symm c_gg1
    · rcases hf' with hf' | hf'
      · rw [hf'] at hfur
        rcases hfurf h hfur with hh | hh
        · rw [hh] at hcol; exact absurd hcol c_f1g1
        · rw [hh] at hcol; exact absurd hcol c_f2g1
      · rw [hf'] at hfur hw
        rcases hfurg h hfur with hh | hh
        · rw [hh] at hw; exact hw
        · rw [hh] at hcol; exact absurd hcol c_g1g2.symm
  have wg2 : Witness P (G.ends e).2 φ g g2 := by
    rcases hsrc (φ g2) with h | h | ⟨f', h, hf', hfur, hcol, hw⟩
    · exact absurd h.symm c_fg2
    · exact absurd h.symm c_gg2
    · rcases hf' with hf' | hf'
      · rw [hf'] at hfur
        rcases hfurf h hfur with hh | hh
        · rw [hh] at hcol; exact absurd hcol c_f1g2
        · rw [hh] at hcol; exact absurd hcol c_f2g2
      · rw [hf'] at hfur hw
        rcases hfurg h hfur with hh | hh
        · rw [hh] at hcol; exact absurd hcol c_g1g2
        · rw [hh] at hw; exact hw
  -- extract the vertices
  obtain ⟨w1, x1, s1, d1, hw1v, hx1v, hx1w1, hs1v, hs1w1, hs1x1, jf, jf1, jd1, hPd1, hd1f1, cd1⟩ := wf1
  obtain ⟨w1', x2, s2, d2, _, hx2v, hx2w1', hs2v, hs2w1', hs2x2, jf', jf2', jd2, hPd2, hd2f2, cd2⟩ := wf2
  have hw1' : w1' = w1 := joins_other jf jf' hw1v
  have jf2 : G.Joins f2 w1 x2 := by rw [← hw1']; exact jf2'
  have hx2w1 : x2 ≠ w1 := by rw [← hw1']; exact hx2w1'
  have hs2w1 : s2 ≠ w1 := by rw [← hw1']; exact hs2w1'
  obtain ⟨w2, z1, s3, d3, hw2v, hz1v, hz1w2, hs3v, hs3w2, hs3z1, jg, jg1, jd3, hPd3, hd3g1, cd3⟩ := wg1
  obtain ⟨w2', z2, s4, d4, _, hz2v, hz2w2', hs4v, hs4w2', hs4z2, jg', jg2', jd4, hPd4, hd4g2, cd4⟩ := wg2
  have hw2' : w2' = w2 := joins_other jg jg' hw2v
  have jg2 : G.Joins g2 w2 z2 := by rw [← hw2']; exact jg2'
  have hz2w2 : z2 ≠ w2 := by rw [← hw2']; exact hz2w2'
  have hs4w2 : s4 ≠ w2 := by rw [← hw2']; exact hs4w2'
  -- vertex distinctness
  have hw12 : w1 ≠ w2 := by
    intro h
    have hfur : Further P (G.ends e).2 f g :=
      ⟨hPg, fun h' => hfg h'.symm, w1, hw1v, joins_inc_right jf, by rw [h]; exact joins_inc_right jg⟩
    rcases hfurf g hfur with h' | h'
    · exact c_gf1 (by rw [h'])
    · exact c_gf2 (by rw [h'])
  have hx1w2 : x1 ≠ w2 := by
    intro h
    have hfur : Further P (G.ends e).2 g f1 :=
      ⟨hf1.1, fun h' => c_gf1 (by rw [h']), w2, hw2v, joins_inc_right jg, by rw [← h]; exact joins_inc_right jf1⟩
    rcases hfurg f1 hfur with h' | h'
    · exact c_f1g1 (by rw [h'])
    · exact c_f1g2 (by rw [h'])
  have hx2w2 : x2 ≠ w2 := by
    intro h
    have hfur : Further P (G.ends e).2 g f2 :=
      ⟨hf2.1, fun h' => c_gf2 (by rw [h']), w2, hw2v, joins_inc_right jg, by rw [← h]; exact joins_inc_right jf2⟩
    rcases hfurg f2 hfur with h' | h'
    · exact c_f2g1 (by rw [h'])
    · exact c_f2g2 (by rw [h'])
  have hz1w1 : z1 ≠ w1 := by
    intro h
    have hfur : Further P (G.ends e).2 f g1 :=
      ⟨hg1.1, fun h' => c_fg1 (by rw [h']), w1, hw1v, joins_inc_right jf, by rw [← h]; exact joins_inc_right jg1⟩
    rcases hfurf g1 hfur with h' | h'
    · exact c_f1g1 (by rw [h'])
    · exact c_f2g1 (by rw [h'])
  have hz2w1 : z2 ≠ w1 := by
    intro h
    have hfur : Further P (G.ends e).2 f g2 :=
      ⟨hg2.1, fun h' => c_fg2 (by rw [h']), w1, hw1v, joins_inc_right jf, by rw [← h]; exact joins_inc_right jg2⟩
    rcases hfurf g2 hfur with h' | h'
    · exact c_f1g2 (by rw [h'])
    · exact c_f2g2 (by rw [h'])
  -- the far neighbourhoods of w1 and w2 are disjoint: a common vertex would carry four distinct edges
  have far : ∀ (a b da db : Fin G.m) (xa xb sa sb : Fin G.n), G.Joins a w1 xa → G.Joins b w2 xb →
      G.Joins da xa sa → G.Joins db xb sb → φ a ≠ φ b → φ da = φ f → φ db = φ g → φ f ≠ φ a → φ f ≠ φ b →
      φ g ≠ φ a → φ g ≠ φ b → da ≠ a → db ≠ b → xa ≠ xb := by
    intro a b da db xa xb sa sb ja jb jda jdb hab hda hdb hfa hfb hga hgb hdaa hdbb h
    have hab' : a ≠ b := fun h' => hab (by rw [h'])
    have hadb : a ≠ db := fun h' => hga (by rw [h', hdb])
    have hbda : b ≠ da := fun h' => hfb (by rw [h', hda])
    have hdadb : da ≠ db := fun h' => c_fg (by rw [← hda, h', hdb])
    exact hsub xa a b da db (joins_inc_right ja) (by rw [h]; exact joins_inc_right jb) (joins_inc_left jda)
      (by rw [h]; exact joins_inc_left jdb) hab' hdaa.symm hadb hbda hdbb.symm hdadb
  have hx1z1 : x1 ≠ z1 := far f1 g1 d1 d3 x1 z1 s1 s3 jf1 jg1 jd1 jd3 c_f1g1 cd1 cd3 c_ff1 c_fg1 c_gf1 c_gg1 hd1f1 hd3g1
  have hx1z2 : x1 ≠ z2 := far f1 g2 d1 d4 x1 z2 s1 s4 jf1 jg2 jd1 jd4 c_f1g2 cd1 cd4 c_ff1 c_fg2 c_gf1 c_gg2 hd1f1 hd4g2
  have hx2z1 : x2 ≠ z1 := far f2 g1 d2 d3 x2 z1 s2 s3 jf2 jg1 jd2 jd3 c_f2g1 cd2 cd3 c_ff2 c_fg1 c_gf2 c_gg1 hd2f2 hd3g1
  have hx2z2 : x2 ≠ z2 := far f2 g2 d2 d4 x2 z2 s2 s4 jf2 jg2 jd2 jd4 c_f2g2 cd2 cd4 c_ff2 c_fg2 c_gf2 c_gg2 hd2f2 hd4g2
  -- all colours are spent
  have cover : ∀ y : Fin 6, y = φ f ∨ y = φ g ∨ y = φ f1 ∨ y = φ f2 ∨ y = φ g1 ∨ y = φ g2 := by
    intro y
    rcases hsrc y with h | h | ⟨f', h, hf', hfur, hcol, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hf' with hf' | hf'
      · rw [hf'] at hfur
        rcases hfurf h hfur with hh | hh
        · rw [hh] at hcol; exact Or.inr (Or.inr (Or.inl hcol.symm))
        · rw [hh] at hcol; exact Or.inr (Or.inr (Or.inr (Or.inl hcol.symm)))
      · rw [hf'] at hfur
        rcases hfurg h hfur with hh | hh
        · rw [hh] at hcol; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcol.symm))))
        · rw [hh] at hcol; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcol.symm))))
  exact ⟨{
      f := f
      g := g
      f1 := f1
      f2 := f2
      g1 := g1
      g2 := g2
      d1 := d1
      d2 := d2
      d3 := d3
      d4 := d4
      w1 := w1
      w2 := w2
      x1 := x1
      x2 := x2
      z1 := z1
      z2 := z2
      s1 := s1
      s2 := s2
      s3 := s3
      s4 := s4
      Pf := hPf
      Pg := hPg
      Pf1 := hf1.1
      Pf2 := hf2.1
      Pg1 := hg1.1
      Pg2 := hg2.1
      Pd1 := hPd1
      Pd2 := hPd2
      Pd3 := hPd3
      Pd4 := hPd4
      fe := hfe
      ge := hge
      jf := jf
      jg := jg
      jf1 := jf1
      jf2 := jf2
      jg1 := jg1
      jg2 := jg2
      jd1 := jd1
      jd2 := jd2
      jd3 := jd3
      jd4 := jd4
      w1v := hw1v
      w2v := hw2v
      w12 := hw12
      x1v := hx1v
      x1w1 := hx1w1
      x1w2 := hx1w2
      x2v := hx2v
      x2w1 := hx2w1
      x2w2 := hx2w2
      z1v := hz1v
      z1w1 := hz1w1
      z1w2 := hz1w2
      z2v := hz2v
      z2w1 := hz2w1
      z2w2 := hz2w2
      x1z1 := hx1z1
      x1z2 := hx1z2
      x2z1 := hx2z1
      x2z2 := hx2z2
      s1v := hs1v
      s1x1 := hs1x1
      s1w1 := hs1w1
      s2v := hs2v
      s2x2 := hs2x2
      s2w1 := hs2w1
      s3v := hs3v
      s3z1 := hs3z1
      s3w2 := hs3w2
      s4v := hs4v
      s4z2 := hs4z2
      s4w2 := hs4w2
      d1f1 := hd1f1
      d2f2 := hd2f2
      d3g1 := hd3g1
      d4g2 := hd4g2
      atv := at_v_two hsub hev hfv hgv hfe hge hfg
      atw1 := fun h hP hne hinc => hfurf h ⟨hP, hne, w1, hw1v, joins_inc_right jf, hinc⟩
      atw2 := fun h hP hne hinc => hfurg h ⟨hP, hne, w2, hw2v, joins_inc_right jg, hinc⟩
      cd1 := cd1
      cd2 := cd2
      cd3 := cd3
      cd4 := cd4
      c_fg := c_fg
      c_ff1 := c_ff1
      c_ff2 := c_ff2
      c_fg1 := c_fg1
      c_fg2 := c_fg2
      c_gf1 := c_gf1
      c_gf2 := c_gf2
      c_gg1 := c_gg1
      c_gg2 := c_gg2
      c_f1f2 := c_f1f2
      c_f1g1 := c_f1g1
      c_f1g2 := c_f1g2
      c_f2g1 := c_f2g1
      c_f2g2 := c_f2g2
      c_g1g2 := c_g1g2
      cover := cover
    }⟩

/-! ### rigidity: `f` and `g` have no alternative colour -/

/-- In the rigid configuration, recolouring `f` alone (keeping `e` uncoloured) is impossible: the colours at
    `v` and `w1` are excluded by properness, and each of `φ g1`, `φ g2` creates the bicoloured walk
    `w1 v w2 z_j s_j` through the witness `d_j`; and these six colours are all there are. -/
theorem rigid_no_alt_f {P : Fin G.m → Prop} {e : Fin G.m} {φ : Fin G.m → Fin 6}
    (R : RigidLeaf P e φ) (c : Fin 6) (hc : c ≠ φ R.f) :
    ¬ StarOn (fun x => P x ∧ x ≠ e) 6 (fun x => if x = R.f then c else φ x) := by
  intro hS
  have hgf : R.g ≠ R.f := fun h => R.c_fg (by rw [h])
  have hf1f : R.f1 ≠ R.f := fun h => R.c_ff1 (by rw [h])
  have hf2f : R.f2 ≠ R.f := fun h => R.c_ff2 (by rw [h])
  have hg1f : R.g1 ≠ R.f := fun h => R.c_fg1 (by rw [h])
  have hg2f : R.g2 ≠ R.f := fun h => R.c_fg2 (by rw [h])
  have hd3f : R.d3 ≠ R.f := fun h => R.c_fg (by rw [← R.cd3, h])
  have hd4f : R.d4 ≠ R.f := fun h => R.c_fg (by rw [← R.cd4, h])
  rcases R.cover c with h | h | h | h | h | h
  · exact hc h
  · -- c = φ g: f and g are adjacent at v
    have := hS.1 R.f R.g ⟨fun h' => hgf h'.symm, (G.ends e).2, joins_inc_left R.jf, joins_inc_left R.jg⟩
      ⟨R.Pf, R.fe⟩ ⟨R.Pg, R.ge⟩
    exact this (by simp [hgf, h])
  · -- c = φ f1: f and f1 are adjacent at w1
    have := hS.1 R.f R.f1 ⟨fun h' => hf1f h'.symm, R.w1, joins_inc_right R.jf, joins_inc_left R.jf1⟩
      ⟨R.Pf, R.fe⟩ ⟨R.Pf1, ne_e_of_far R.jf1 R.w1v R.x1v⟩
    exact this (by simp [hf1f, h])
  · have := hS.1 R.f R.f2 ⟨fun h' => hf2f h'.symm, R.w1, joins_inc_right R.jf, joins_inc_left R.jf2⟩
      ⟨R.Pf, R.fe⟩ ⟨R.Pf2, ne_e_of_far R.jf2 R.w1v R.x2v⟩
    exact this (by simp [hf2f, h])
  · -- c = φ g1: the walk w1 v w2 z1 s3 with edges f g g1 d3 is bicoloured
    have := hS.2 ⟨R.w1, (G.ends e).2, R.w2, R.z1, R.s3, R.f, R.g, R.g1, R.d3,
        joins_symm R.jf, R.jg, R.jg1, R.jd3, R.w1v, R.w12, R.z1w1.symm, fun h => R.w2v h.symm,
        fun h => R.z1v h.symm, fun h => R.s3v h.symm, fun h => R.z1w2 h.symm, fun h => R.s3w2 h.symm,
        fun h => R.s3z1 h.symm⟩
      ⟨R.Pf, R.fe⟩ ⟨R.Pg, R.ge⟩ ⟨R.Pg1, ne_e_of_far R.jg1 R.w2v R.z1v⟩ ⟨R.Pd3, ne_e_of_far R.jd3 R.z1v R.s3v⟩
    exact this ⟨(by simp [hg1f, h]), (by simp [hgf, hd3f, R.cd3])⟩
  · have := hS.2 ⟨R.w1, (G.ends e).2, R.w2, R.z2, R.s4, R.f, R.g, R.g2, R.d4,
        joins_symm R.jf, R.jg, R.jg2, R.jd4, R.w1v, R.w12, R.z2w1.symm, fun h => R.w2v h.symm,
        fun h => R.z2v h.symm, fun h => R.s4v h.symm, fun h => R.z2w2 h.symm, fun h => R.s4w2 h.symm,
        fun h => R.s4z2 h.symm⟩
      ⟨R.Pf, R.fe⟩ ⟨R.Pg, R.ge⟩ ⟨R.Pg2, ne_e_of_far R.jg2 R.w2v R.z2v⟩ ⟨R.Pd4, ne_e_of_far R.jd4 R.z2v R.s4v⟩
    exact this ⟨(by simp [hg2f, h]), (by simp [hgf, hd4f, R.cd4])⟩

/-- the same for `g` -/
theorem rigid_no_alt_g {P : Fin G.m → Prop} {e : Fin G.m} {φ : Fin G.m → Fin 6}
    (R : RigidLeaf P e φ) (c : Fin 6) (hc : c ≠ φ R.g) :
    ¬ StarOn (fun x => P x ∧ x ≠ e) 6 (fun x => if x = R.g then c else φ x) :=
  rigid_no_alt_f R.swap c hc

/-! ### the exact obstruction, as an equivalence -/

theorem starOn_mono {P P' : Fin G.m → Prop} {k : Nat} {c : Fin G.m → Fin k} (h : ∀ f, P' f → P f)
    (hc : StarOn P k c) : StarOn P' k c :=
  ⟨fun a b hab ha hb => hc.1 a b hab (h a ha) (h b hb),
   fun w h1 h2 h3 h4 => hc.2 w (h _ h1) (h _ h2) (h _ h3) (h _ h4)⟩

/-- the rigid configuration blocks every colour at the pendant edge -/
theorem rigid_blocks {P : Fin G.m → Prop} {e : Fin G.m} {φ : Fin G.m → Fin 6} (hPe : P e)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1) (R : RigidLeaf P e φ) (y : Fin 6) :
    ¬ StarOn P 6 (fun x => if x = e then y else φ x) := by
  intro hS
  have hf1e : R.f1 ≠ e := ne_e_of_far R.jf1 R.w1v R.x1v
  have hf2e : R.f2 ≠ e := ne_e_of_far R.jf2 R.w1v R.x2v
  have hg1e : R.g1 ≠ e := ne_e_of_far R.jg1 R.w2v R.z1v
  have hg2e : R.g2 ≠ e := ne_e_of_far R.jg2 R.w2v R.z2v
  have hd1e : R.d1 ≠ e := ne_e_of_far R.jd1 R.x1v R.s1v
  have hd2e : R.d2 ≠ e := ne_e_of_far R.jd2 R.x2v R.s2v
  have hd3e : R.d3 ≠ e := ne_e_of_far R.jd3 R.z1v R.s3v
  have hd4e : R.d4 ≠ e := ne_e_of_far R.jd4 R.z2v R.s4v
  -- the leaf `u` is none of the other vertices
  have huv : (G.ends e).1 ≠ (G.ends e).2 := fun h => hleaf R.f R.Pf R.fe (by rw [h]; exact joins_inc_left R.jf)
  have huw1 : (G.ends e).1 ≠ R.w1 := fun h => hleaf R.f R.Pf R.fe (by rw [h]; exact joins_inc_right R.jf)
  have huw2 : (G.ends e).1 ≠ R.w2 := fun h => hleaf R.g R.Pg R.ge (by rw [h]; exact joins_inc_right R.jg)
  have hux1 : (G.ends e).1 ≠ R.x1 := fun h => hleaf R.f1 R.Pf1 hf1e (by rw [h]; exact joins_inc_right R.jf1)
  have hux2 : (G.ends e).1 ≠ R.x2 := fun h => hleaf R.f2 R.Pf2 hf2e (by rw [h]; exact joins_inc_right R.jf2)
  have huz1 : (G.ends e).1 ≠ R.z1 := fun h => hleaf R.g1 R.Pg1 hg1e (by rw [h]; exact joins_inc_right R.jg1)
  have huz2 : (G.ends e).1 ≠ R.z2 := fun h => hleaf R.g2 R.Pg2 hg2e (by rw [h]; exact joins_inc_right R.jg2)
  rcases R.cover y with h | h | h | h | h | h
  · have := hS.1 e R.f ⟨R.fe.symm, (G.ends e).2, joins_inc_right (joins_ends e), joins_inc_left R.jf⟩ hPe R.Pf
    exact this (by simp [R.fe, h])
  · have := hS.1 e R.g ⟨R.ge.symm, (G.ends e).2, joins_inc_right (joins_ends e), joins_inc_left R.jg⟩ hPe R.Pg
    exact this (by simp [R.ge, h])
  · have := hS.2 ⟨(G.ends e).1, (G.ends e).2, R.w1, R.x1, R.s1, e, R.f, R.f1, R.d1,
        joins_ends e, R.jf, R.jf1, R.jd1, huv, huw1, hux1, fun h => R.w1v h.symm, fun h => R.x1v h.symm,
        fun h => R.s1v h.symm, fun h => R.x1w1 h.symm, fun h => R.s1w1 h.symm, fun h => R.s1x1 h.symm⟩
      hPe R.Pf R.Pf1 R.Pd1
    exact this ⟨(by simp [hf1e, h]), (by simp [R.fe, hd1e, R.cd1])⟩
  · have := hS.2 ⟨(G.ends e).1, (G.ends e).2, R.w1, R.x2, R.s2, e, R.f, R.f2, R.d2,
        joins_ends e, R.jf, R.jf2, R.jd2, huv, huw1, hux2, fun h => R.w1v h.symm, fun h => R.x2v h.symm,
        fun h => R.s2v h.symm, fun h => R.x2w1 h.symm, fun h => R.s2w1 h.symm, fun h => R.s2x2 h.symm⟩
      hPe R.Pf R.Pf2 R.Pd2
    exact this ⟨(by simp [hf2e, h]), (by simp [R.fe, hd2e, R.cd2])⟩
  · have := hS.2 ⟨(G.ends e).1, (G.ends e).2, R.w2, R.z1, R.s3, e, R.g, R.g1, R.d3,
        joins_ends e, R.jg, R.jg1, R.jd3, huv, huw2, huz1, fun h => R.w2v h.symm, fun h => R.z1v h.symm,
        fun h => R.s3v h.symm, fun h => R.z1w2 h.symm, fun h => R.s3w2 h.symm, fun h => R.s3z1 h.symm⟩
      hPe R.Pg R.Pg1 R.Pd3
    exact this ⟨(by simp [hg1e, h]), (by simp [R.ge, hd3e, R.cd3])⟩
  · have := hS.2 ⟨(G.ends e).1, (G.ends e).2, R.w2, R.z2, R.s4, e, R.g, R.g2, R.d4,
        joins_ends e, R.jg, R.jg2, R.jd4, huv, huw2, huz2, fun h => R.w2v h.symm, fun h => R.z2v h.symm,
        fun h => R.s4v h.symm, fun h => R.z2w2 h.symm, fun h => R.s4w2 h.symm, fun h => R.s4z2 h.symm⟩
      hPe R.Pg R.Pg2 R.Pd4
    exact this ⟨(by simp [hg2e, h]), (by simp [R.ge, hd4e, R.cd4])⟩

/-- "a minimal counterexample has no leaf" -/
def LeafFree (G : MGraph) : Prop :=
  ∀ P : Fin G.m → Prop, MinimalCounterexample P 6 → ∀ e, P e →
    ¬ (∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1)

/-- **The open lemma.**  Whenever `P − e` is star 6-colourable and `e` is a pendant edge of `P`, some star
    6-colouring of `P − e` is not rigid at the leaf. -/
def NonRigidLemma (G : MGraph) : Prop :=
  ∀ (P : Fin G.m → Prop) (e : Fin G.m), P e → (∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1) →
    Colourable (fun f => P f ∧ f ≠ e) 6 →
    ∃ φ, StarOn (fun f => P f ∧ f ≠ e) 6 φ ∧ ¬ Nonempty (RigidLeaf P e φ)

/-- **Exact obstruction.**  In a subcubic multigraph, "no minimal counterexample has a leaf" holds if and only if
    the non-rigid colouring lemma holds. -/
theorem leafFree_iff_nonRigid (hsub : Subcubic G) : LeafFree G ↔ NonRigidLemma G := by
  constructor
  · intro H P e hPe hleaf hcol
    by_cases hP : Colourable P 6
    · obtain ⟨φ', hφ'⟩ := hP
      refine ⟨φ', starOn_mono (fun f hf => hf.1) hφ', ?_⟩
      rintro ⟨R⟩
      apply rigid_blocks hPe hleaf R (φ' e)
      have hfun : (fun x => if x = e then φ' e else φ' x) = φ' :=
        funext (fun x => by by_cases hx : x = e <;> simp [hx])
      rw [hfun]; exact hφ'
    · obtain ⟨P', hsub', hmin'⟩ := exists_minimal 6 P hP
      obtain ⟨φ, hφ⟩ := hcol
      have hP'e : P' e := Classical.byContradiction fun hne =>
        hmin'.1 ⟨φ, starOn_mono (fun f hf => ⟨hsub' f hf, fun h => hne (h ▸ hf)⟩) hφ⟩
      exact absurd (fun f hf hfe => hleaf f (hsub' f hf) hfe) (H P' hmin' e hP'e)
  · intro H P hmin e hPe hleaf
    have hcol : Colourable (fun f => P f ∧ f ≠ e) 6 :=
      hmin.2 _ ⟨fun f hf => hf.1, e, hPe, fun h => h.2 rfl⟩
    obtain ⟨φ, hφ, hnr⟩ := H P e hPe hleaf hcol
    exact hnr (minimal_leaf_rigid hsub P hmin e hPe hleaf φ hφ)

/-! ### what `NonRigidLemma` is: pendant reducibility -/

/-- "adding a pendant edge preserves star 6-colourability" (for edge sets of `G`) -/
def PendantReducible (G : MGraph) : Prop :=
  ∀ (P : Fin G.m → Prop) (e : Fin G.m), P e → (∀ f, P f → f ≠ e → ¬ G.Inc f (G.ends e).1) →
    Colourable (fun f => P f ∧ f ≠ e) 6 → Colourable P 6

/-- `NonRigidLemma` is exactly pendant reducibility: the statement "if `G − u` is star 6-colourable and `u` is
    a leaf then `G` is" — a consequence of the DMS conjecture with no known independent proof. -/
theorem pendantReducible_iff_nonRigid (hsub : Subcubic G) : PendantReducible G ↔ NonRigidLemma G := by
  constructor
  · intro H P e hPe hleaf hcol
    obtain ⟨φ', hφ'⟩ := H P e hPe hleaf hcol
    refine ⟨φ', starOn_mono (fun f hf => hf.1) hφ', ?_⟩
    rintro ⟨R⟩
    apply rigid_blocks hPe hleaf R (φ' e)
    have hfun : (fun x => if x = e then φ' e else φ' x) = φ' :=
      funext (fun x => by by_cases hx : x = e <;> simp [hx])
    rw [hfun]; exact hφ'
  · intro H P e hPe hleaf hcol
    apply Classical.byContradiction
    intro hP
    obtain ⟨P', hsub', hmin'⟩ := exists_minimal 6 P hP
    obtain ⟨φ, hφ⟩ := hcol
    have hP'e : P' e := Classical.byContradiction fun hne =>
      hmin'.1 ⟨φ, starOn_mono (fun f hf => ⟨hsub' f hf, fun h => hne (h ▸ hf)⟩) hφ⟩
    exact (leafFree_iff_nonRigid hsub).2 H P' hmin' e hP'e (fun f hf hfe => hleaf f (hsub' f hf) hfe)

/-- the easy half of the problem: a star **5**-colouring of `P − e` is never rigid (colour `5` is unused, so
    `cover` fails).  The open case is therefore exactly: `P − e` of star chromatic index six. -/
theorem nonRigid_of_five {P : Fin G.m → Prop} {e : Fin G.m} (ψ : Fin G.m → Fin 5)
    (hψ : StarOn (fun f => P f ∧ f ≠ e) 5 ψ) :
    ∃ φ, StarOn (fun f => P f ∧ f ≠ e) 6 φ ∧ ¬ Nonempty (RigidLeaf P e φ) := by
  refine ⟨fun f => Fin.castSucc (ψ f), starOn_map Fin.castSucc (fun x y h => castSucc_inj' h) hψ, ?_⟩
  rintro ⟨R⟩
  rcases R.cover (Fin.last 5) with h | h | h | h | h | h <;> exact castSucc_ne_last _ h.symm

end MGraph
