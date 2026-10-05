/-
  StarBottleneck.lean — where the leaf bottleneck really lives: the bridgeless core.

  A minimal non-star-6-colourable edge set `Q` of a subcubic multigraph splits into its *core* (edges that are not
  pendant) and its pendant edges.  This file proves, with no `sorry` and standard axioms only:

    * `pendants_disjoint`  — no two pendant edges of `Q` share a vertex (a leaf's neighbour needs two further
                             edges with two further edges each: `minimal_leaf_at`, the orientation-free form of
                             `minimal_leaf`);
    * `pendant_extend_on`  — relative form of `pendant_extend`: a star `k`-colouring of the core plus a fresh colour
                             on the pendant edges is a star `(k+1)`-colouring of `Q`;
    * `core_not_five`      — **the core of a minimal counterexample is not star 5-colourable**;
    * `core_colourable_six`— the core is star 6-colourable (when `Q` has a pendant edge, it is a proper subset);
    * `core_no_cut`        — **no core edge admits a bridge cut of `Q`** (the core is 2-edge-connected: a cut with
                             a trivial side would make the edge pendant, a cut with two nontrivial sides is
                             excluded by `minimal_no_bridge`);
    * `leaf_sharp_core`    — all of the above together with the rigid configuration of `StarRigid.lean`: if `Q` has
                             a leaf, its core is a bridgeless subcubic multigraph of star chromatic index exactly
                             six containing the vertex `v` with exactly two core edges, whose neighbours `w₁, w₂` have
                             three core edges each and far neighbourhoods disjoint from each other.

  Reading: rigidity of *every* colouring at a leaf is not a local phenomenon.  If the core were star 5-colourable
  the sixth colour would be free for every pendant edge (`pendant_extend_on`), so a leaf can survive in a minimal
  counterexample only on top of a bridgeless subcubic multigraph of star index exactly six that is none of the four
  known 6-critical gadgets (three are cubic; K₄ with a subdivided edge violates the disjointness of the far
  neighbourhoods).  That is precisely a counterexample to the sharp form L1′ of the conjecture.
-/
import StarRigid

namespace MGraph
variable {G : MGraph}

/-! ### orientation-free versions of the leaf lemmas (`u` the leaf, `v` its neighbour, `Joins e u v`) -/

theorem pendant_free_at {P : Fin G.m → Prop} {k : Nat} (e : Fin G.m) {u v : Fin G.n} (hj : G.Joins e u v)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f u)
    (φ : Fin G.m → Fin k) (hφ : StarOn (fun f => P f ∧ f ≠ e) k φ) (y : Fin k)
    (hy1 : ∀ f, P f → f ≠ e → G.Inc f v → φ f ≠ y)
    (hy2 : ∀ f h, P f → f ≠ e → G.Inc f v → Further P v f h → φ h ≠ y) :
    StarOn P k (fun f => if f = e then y else φ f) := by
  have ce : (fun f => if f = e then y else φ f) e = y := by simp
  have cf : ∀ {f}, f ≠ e → (fun f => if f = e then y else φ f) f = φ f := by
    intro f hf; simp [hf]
  have hu_or_v : ∀ {x : Fin G.n}, G.Inc e x → x = u ∨ x = v := fun hx => inc_of_joins hj hx
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
      have hj' : G.Joins e w.v1 w.v2 := by rw [← h2]; exact w.h2
      rcases joins_unique hj hj' with ⟨hu1, _⟩ | ⟨hu2, _⟩
      · exact hleaf w.e1 hp1 h1 (hu1 ▸ w.inc_e1_v1)
      · exact hleaf w.e3 hp3 h3 (hu2 ▸ w.inc_e3_v2)
    by_cases h3 : w.e3 = e
    · have h2' : w.e2 ≠ e := h2
      have h4 : w.e4 ≠ e := fun h => w.e3_ne_e4 (h3.trans h.symm)
      have hj' : G.Joins e w.v2 w.v3 := by rw [← h3]; exact w.h3
      rcases joins_unique hj hj' with ⟨hu2, _⟩ | ⟨hu3, _⟩
      · exact hleaf w.e2 hp2 h2' (hu2 ▸ w.inc_e2_v2)
      · exact hleaf w.e4 hp4 h4 (hu3 ▸ w.inc_e4_v3)
    by_cases h1 : w.e1 = e
    · have hj' : G.Joins e w.v0 w.v1 := by rw [← h1]; exact w.h1
      rcases joins_unique hj hj' with ⟨_, hv1⟩ | ⟨hu1, _⟩
      · rw [h1, ce, cf h3] at hb13
        have hfur : Further P v w.e2 w.e3 :=
          ⟨hp3, fun h => w.e2_ne_e3 h.symm, w.v2, fun h => w.d12 (h.trans hv1).symm, w.inc_e2_v2, w.inc_e3_v2⟩
        exact hy2 w.e2 w.e3 hp2 h2 (hv1 ▸ w.inc_e2_v1) hfur hb13.symm
      · exact hleaf w.e2 hp2 h2 (hu1 ▸ w.inc_e2_v1)
    by_cases h4 : w.e4 = e
    · have hj' : G.Joins e w.v3 w.v4 := by rw [← h4]; exact w.h4
      rcases joins_unique hj hj' with ⟨hu3, _⟩ | ⟨_, hv3⟩
      · exact hleaf w.e3 hp3 h3 (hu3 ▸ w.inc_e3_v3)
      · rw [h4, ce, cf h2] at hb24
        have hfur : Further P v w.e3 w.e2 :=
          ⟨hp2, w.e2_ne_e3, w.v2, fun h => w.d23 (h.trans hv3), w.inc_e3_v2, w.inc_e2_v2⟩
        exact hy2 w.e3 w.e2 hp3 h3 (hv3 ▸ w.inc_e3_v3) hfur hb24
    rw [cf h1, cf h3] at hb13
    rw [cf h2, cf h4] at hb24
    exact hφ.2 w ⟨hp1, h1⟩ ⟨hp2, h2⟩ ⟨hp3, h3⟩ ⟨hp4, h4⟩ ⟨hb13, hb24⟩

theorem colourable_of_five_at {P : Fin G.m → Prop} (e : Fin G.m) {u v : Fin G.n} (hj : G.Joins e u v)
    (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f u)
    (φ : Fin G.m → Fin 6) (hφ : StarOn (fun f => P f ∧ f ≠ e) 6 φ) (a1 a2 a3 a4 a5 : Fin 6)
    (hv : ∀ f, P f → f ≠ e → G.Inc f v → φ f = a1 ∨ φ f = a2 ∨ φ f = a3 ∨ φ f = a4 ∨ φ f = a5)
    (hw : ∀ f h, P f → f ≠ e → G.Inc f v → Further P v f h →
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
  exact ⟨_, pendant_free_at e hj hleaf φ hφ y (fun f hf hfe hfv => hy _ (hv f hf hfe hfv))
    (fun f h hf hfe hfv hfh => hy _ (hw f h hf hfe hfv hfh))⟩

/-- `minimal_leaf`, orientation-free -/
theorem minimal_leaf_at (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) {u v : Fin G.n} (hj : G.Joins e u v) (hleaf : ∀ f, P f → f ≠ e → ¬ G.Inc f u) :
    ∃ f g, P f ∧ P g ∧ f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ G.Inc f v ∧ G.Inc g v ∧
      (∃ h1 h2, Further P v f h1 ∧ Further P v f h2 ∧ h1 ≠ h2) ∧
      (∃ h1 h2, Further P v g h1 ∧ Further P v g h2 ∧ h1 ≠ h2) := by
  have hPe' : Colourable (fun f => P f ∧ f ≠ e) 6 := by
    apply hmin.2
    exact ⟨fun f hf => hf.1, e, hPe, fun h => h.2 rfl⟩
  obtain ⟨φ, hφ⟩ := hPe'
  have hev : G.Inc e v := joins_inc_right hj
  by_cases hf : ∃ f, P f ∧ f ≠ e ∧ G.Inc f v
  · obtain ⟨f, hPf, hfe, hfv⟩ := hf
    obtain ⟨p1, p2, hp⟩ := further_two hsub P v f hfv φ (φ f)
    by_cases hg : ∃ g, P g ∧ g ≠ e ∧ G.Inc g v ∧ g ≠ f
    · obtain ⟨g, hPg, hge, hgv, hgf⟩ := hg
      obtain ⟨q1, q2, hq⟩ := further_two hsub P v g hgv φ (φ g)
      have hfg : ∀ f', P f' → f' ≠ e → G.Inc f' v → f' = f ∨ f' = g := by
        intro f' hPf' hf'e hf'v
        by_cases h1 : f' = f
        · exact Or.inl h1
        by_cases h2 : f' = g
        · exact Or.inr h2
        exact absurd (hsub v f' f g e hf'v hfv hgv hev h1 h2 hf'e (fun h => hgf h.symm) hfe hge) id
      by_cases htf : ∃ h1 h2, Further P v f h1 ∧ Further P v f h2 ∧ h1 ≠ h2
      · by_cases htg : ∃ h1 h2, Further P v g h1 ∧ Further P v g h2 ∧ h1 ≠ h2
        · exact ⟨f, g, hPf, hPg, hfe, hge, fun h => hgf h.symm, hfv, hgv, htf, htg⟩
        · obtain ⟨q, hq1⟩ := further_one P v g htg φ (φ g)
          exfalso
          apply hmin.1
          apply colourable_of_five_at e hj hleaf φ hφ (φ f) (φ g) p1 p2 q
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
      · obtain ⟨p, hp1⟩ := further_one P v f htf φ (φ f)
        exfalso
        apply hmin.1
        apply colourable_of_five_at e hj hleaf φ hφ (φ f) (φ g) p q1 q2
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
    · exfalso
      apply hmin.1
      apply colourable_of_five_at e hj hleaf φ hφ (φ f) p1 p2 p1 p1
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
  · exfalso
    apply hmin.1
    apply colourable_of_five_at e hj hleaf φ hφ 0 0 0 0 0
    · intro f' hPf' hf'e hf'v
      exact absurd ⟨f', hPf', hf'e, hf'v⟩ hf
    · intro f' h hPf' hf'e hf'v _
      exact absurd ⟨f', hPf', hf'e, hf'v⟩ hf

/-! ### pendant edges and the core -/

/-- a pendant edge of `Q`: some endpoint carries no other edge of `Q` -/
def Pendant (Q : Fin G.m → Prop) (f : Fin G.m) : Prop :=
  Q f ∧ ∃ x, G.Inc f x ∧ ∀ g, Q g → g ≠ f → ¬ G.Inc g x

/-- the core of `Q`: its non-pendant edges -/
def Core (Q : Fin G.m → Prop) : Fin G.m → Prop := fun f => Q f ∧ ¬ Pendant Q f

/-- an edge incident to two vertices `x ≠ y` joins them -/
theorem joins_of_inc_ne {f : Fin G.m} {x y : Fin G.n} (hx : G.Inc f x) (hy : G.Inc f y) (hxy : x ≠ y) :
    G.Joins f x y := by
  rcases inc_of_joins (joins_ends f) hx with h | h <;> rcases inc_of_joins (joins_ends f) hy with h' | h'
  · exact absurd (h.trans h'.symm) hxy
  · rw [h, h']; exact joins_ends f
  · rw [h, h']; exact joins_symm (joins_ends f)
  · exact absurd (h.trans h'.symm) hxy

/-- **No two pendant edges of a minimal counterexample share a vertex.** -/
theorem pendants_disjoint (hsub : Subcubic G) (Q : Fin G.m → Prop) (hmin : MinimalCounterexample Q 6)
    {p1 p2 : Fin G.m} (h1 : Pendant Q p1) (h2 : Pendant Q p2) (hne : p1 ≠ p2) {x : Fin G.n}
    (hx1 : G.Inc p1 x) (hx2 : G.Inc p2 x) : False := by
  obtain ⟨hQ1, l1, hl1, hleaf1⟩ := h1
  obtain ⟨hQ2, l2, hl2, hleaf2⟩ := h2
  have hxl1 : x ≠ l1 := fun h => hleaf1 p2 hQ2 (Ne.symm hne) (h ▸ hx2)
  have hxl2 : x ≠ l2 := fun h => hleaf2 p1 hQ1 hne (h ▸ hx1)
  have hj1 : G.Joins p1 l1 x := joins_of_inc_ne hl1 hx1 (Ne.symm hxl1)
  obtain ⟨f, g, hQf, hQg, hfe, hge, hfg, hfv, hgv, htf, htg⟩ :=
    minimal_leaf_at hsub Q hmin p1 hQ1 hj1 hleaf1
  -- p2 is one of f, g, hence has a further edge beyond x, which lives at the leaf l2
  have hp2 : p2 = f ∨ p2 = g := at_v_two hsub hx1 hfv hgv hfe hge hfg p2 hQ2 (Ne.symm hne) hx2
  have key : ∀ h, Further Q x p2 h → False := by
    intro h ⟨hQh, hhp2, y, hyx, hp2y, hhy⟩
    have hyl2 : y = l2 := inc_ne_unique hx2 hp2y hl2 hyx (Ne.symm hxl2)
    exact hleaf2 h hQh hhp2 (hyl2 ▸ hhy)
  rcases hp2 with h | h
  · subst h
    obtain ⟨h1, _, hf1, _, _⟩ := htf
    exact key h1 hf1
  · subst h
    obtain ⟨h1, _, hg1, _, _⟩ := htg
    exact key h1 hg1

/-- **Pendant extension, relative to an edge set `Q`.**  `Pd` marks pendant edges of `Q`, `leaf f` a private
    degree-one endpoint of the pendant edge `f`, no two pendant edges share a vertex; a star `k`-colouring of the
    non-pendant edges of `Q` extends by the new colour `k` on the pendant edges to a star `(k+1)`-colouring of `Q`. -/
theorem pendant_extend_on {k : Nat} (Q : Fin G.m → Prop) (Pd : Fin G.m → Bool) (leaf : Fin G.m → Fin G.n)
    (c : Fin G.m → Fin k)
    (hleafinc : ∀ f, Q f → Pd f = true → G.Inc f (leaf f))
    (hleaf : ∀ f g, Q f → Pd f = true → Q g → g ≠ f → ¬ G.Inc g (leaf f))
    (hattach : ∀ f g, Q f → Pd f = true → Q g → Pd g = true → f ≠ g → ∀ x, G.Inc f x → G.Inc g x → False)
    (hcore : StarOn (fun f => Q f ∧ Pd f = false) k c) :
    StarOn Q (k + 1) (fun f => if Pd f then Fin.last k else Fin.castSucc (c f)) := by
  have interior : ∀ (f g g' : Fin G.m) (x y : Fin G.n), Q f → Pd f = true → G.Joins f x y →
      Q g → g ≠ f → G.Inc g x → Q g' → g' ≠ f → G.Inc g' y → False := by
    intro f g g' x y hQf hf hj hQg hg hgx hQg' hg' hg'y
    rcases inc_of_joins hj (hleafinc f hQf hf) with hl | hl
    · exact hleaf f g hQf hf hQg hg (hl ▸ hgx)
    · exact hleaf f g' hQf hf hQg' hg' (hl ▸ hg'y)
  constructor
  · intro a b hab hQa hQb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    cases ha : Pd a <;> cases hb : Pd b <;> simp [ha, hb] at heq
    · exact hcore.1 a b ⟨hne, x, hax, hbx⟩ ⟨hQa, ha⟩ ⟨hQb, hb⟩ (castSucc_inj' heq)
    · exact castSucc_ne_last (c a) heq
    · exact castSucc_ne_last (c b) heq.symm
    · exact hattach a b hQa ha hQb hb hne x hax hbx
  · intro w hQ1 hQ2 hQ3 hQ4 hb
    rcases hb with ⟨hb13, hb24⟩
    cases h3 : Pd w.e3
    · cases h2 : Pd w.e2
      · cases h1 : Pd w.e1
        · cases h4 : Pd w.e4
          · simp [h1, h2, h3, h4] at hb13 hb24
            exact hcore.2 w ⟨hQ1, h1⟩ ⟨hQ2, h2⟩ ⟨hQ3, h3⟩ ⟨hQ4, h4⟩ ⟨castSucc_inj' hb13, castSucc_inj' hb24⟩
          · simp [h2, h4] at hb24
            exact castSucc_ne_last (c w.e2) hb24
        · simp [h1, h3] at hb13
          exact castSucc_ne_last (c w.e3) hb13.symm
      · exact interior w.e2 w.e1 w.e3 w.v1 w.v2 hQ2 h2 w.h2 hQ1 w.e1_ne_e2 w.inc_e1_v1 hQ3
          (fun h => w.e2_ne_e3 h.symm) w.inc_e3_v2
    · exact interior w.e3 w.e2 w.e4 w.v2 w.v3 hQ3 h3 w.h3 hQ2 w.e2_ne_e3 w.inc_e2_v2 hQ4
        (fun h => w.e3_ne_e4 h.symm) w.inc_e4_v3

/-- **The core of a minimal counterexample is not star 5-colourable.** -/
theorem core_not_five (hsub : Subcubic G) (Q : Fin G.m → Prop) (hmin : MinimalCounterexample Q 6) :
    ¬ Colourable (Core Q) 5 := by
  classical
  rintro ⟨c, hc⟩
  apply hmin.1
  let Pd : Fin G.m → Bool := fun f => decide (Pendant Q f)
  let leaf : Fin G.m → Fin G.n := fun f =>
    if h : Pendant Q f then Classical.choose h.2 else (G.ends f).1
  have hPd : ∀ f, Pd f = true ↔ Pendant Q f := fun f => by simp [Pd]
  have hleafspec : ∀ f, Pendant Q f → G.Inc f (leaf f) ∧ ∀ g, Q g → g ≠ f → ¬ G.Inc g (leaf f) := by
    intro f hf
    have hs := Classical.choose_spec hf.2
    simp only [leaf, dif_pos hf]
    exact hs
  have hext := pendant_extend_on Q Pd leaf c
    (fun f _ hf => (hleafspec f ((hPd f).1 hf)).1)
    (fun f g _ hf hQg hgf => (hleafspec f ((hPd f).1 hf)).2 g hQg hgf)
    (fun f g _ hf _ hg hfg x hfx hgx =>
      pendants_disjoint hsub Q hmin ((hPd f).1 hf) ((hPd g).1 hg) hfg hfx hgx)
    (starOn_mono (fun f hf => ⟨hf.1, fun hp => by
        have := (hPd f).2 hp
        rw [hf.2] at this
        exact Bool.false_ne_true this⟩) hc)
  exact ⟨_, hext⟩

/-- the core is star 6-colourable as soon as `Q` has a pendant edge (it is then a proper subset) -/
theorem core_colourable_six (Q : Fin G.m → Prop) (hmin : MinimalCounterexample Q 6) {p : Fin G.m}
    (hp : Pendant Q p) : Colourable (Core Q) 6 :=
  hmin.2 _ ⟨fun _ hf => hf.1, p, hp.1, fun h => h.2 hp⟩

/-- **No core edge of a minimal counterexample admits a bridge cut.**  A cut with an empty side makes the edge
    pendant; a cut with both sides nonempty is a two-sided bridge. -/
theorem core_no_cut (hsub : Subcubic G) (Q : Fin G.m → Prop) (hmin : MinimalCounterexample Q 6)
    {c : Fin G.m} (hc : Core Q c) (B : G.CutOn Q c) : False := by
  obtain ⟨hQc, hnp⟩ := hc
  by_cases hU : ∃ a, Q a ∧ a ≠ c ∧ B.onU a
  · by_cases hV : ∃ b, Q b ∧ b ≠ c ∧ ¬ B.onU b
    · exact minimal_no_bridge hsub Q hmin c hQc B hU hV
    · -- nothing on the far side: the second endpoint of `c` is a leaf
      apply hnp
      refine ⟨hQc, (G.ends c).2, joins_inc_right (joins_ends c), ?_⟩
      intro g hQg hgc hgv
      exact hV ⟨g, hQg, hgc, B.not_onU_of_inc_v hQg hgc hgv⟩
  · -- nothing on the near side: the first endpoint of `c` is a leaf
    apply hnp
    refine ⟨hQc, (G.ends c).1, joins_inc_left (joins_ends c), ?_⟩
    intro g hQg hgc hgu
    exact hU ⟨g, hQg, hgc, B.onU_of_inc_u hQg hgc hgu⟩

/-- an edge with a vertex on each side that carries another edge of `Q` is not pendant -/
theorem not_pendant_of_two {Q : Fin G.m → Prop} {f : Fin G.m} {x y : Fin G.n} (hj : G.Joins f x y)
    {a b : Fin G.m} (hQa : Q a) (haf : a ≠ f) (hax : G.Inc a x) (hQb : Q b) (hbf : b ≠ f) (hby : G.Inc b y) :
    ¬ Pendant Q f := by
  rintro ⟨_, z, hz, hleaf⟩
  rcases inc_of_joins hj hz with h | h
  · exact hleaf a hQa haf (h ▸ hax)
  · exact hleaf b hQb hbf (h ▸ hby)

/-- **The leaf bottleneck is a sharp bridgeless core.**  If a minimal counterexample `Q` has a leaf `u` with
    pendant edge `e = uv`, then its core is star 6-colourable but not star 5-colourable, no core edge admits a bridge
    cut of `Q`, `e` is not a core edge, and for every star 6-colouring `φ` of `Q − e` the rigid configuration
    `R : RigidLeaf Q e φ` lies entirely in the core: `v` has exactly the two core edges `f, g`. -/
theorem leaf_sharp_core (hsub : Subcubic G) (Q : Fin G.m → Prop) (hmin : MinimalCounterexample Q 6)
    (e : Fin G.m) (hQe : Q e) (hleaf : ∀ f, Q f → f ≠ e → ¬ G.Inc f (G.ends e).1) :
    Colourable (Core Q) 6 ∧ ¬ Colourable (Core Q) 5 ∧ (∀ c, Core Q c → G.CutOn Q c → False) ∧ ¬ Core Q e ∧
      ∀ φ, StarOn (fun f => Q f ∧ f ≠ e) 6 φ → ∃ R : RigidLeaf Q e φ,
        Core Q R.f ∧ Core Q R.g ∧ Core Q R.f1 ∧ Core Q R.f2 ∧ Core Q R.g1 ∧ Core Q R.g2 ∧
        (∀ h, Core Q h → G.Inc h (G.ends e).2 → h = R.f ∨ h = R.g) := by
  have hpe : Pendant Q e := ⟨hQe, (G.ends e).1, joins_inc_left (joins_ends e), hleaf⟩
  refine ⟨core_colourable_six Q hmin hpe, core_not_five hsub Q hmin,
    fun c hc B => core_no_cut hsub Q hmin hc B, fun h => h.2 hpe, ?_⟩
  intro φ hφ
  obtain ⟨R⟩ := minimal_leaf_rigid hsub Q hmin e hQe hleaf φ hφ
  have hf1e : R.f1 ≠ e := ne_e_of_far R.jf1 R.w1v R.x1v
  have hf2e : R.f2 ≠ e := ne_e_of_far R.jf2 R.w1v R.x2v
  have hg1e : R.g1 ≠ e := ne_e_of_far R.jg1 R.w2v R.z1v
  have hg2e : R.g2 ≠ e := ne_e_of_far R.jg2 R.w2v R.z2v
  have hgf : R.g ≠ R.f := fun h => R.c_fg (by rw [h])
  have hf1f : R.f1 ≠ R.f := fun h => R.c_ff1 (by rw [h])
  have hg1g : R.g1 ≠ R.g := fun h => R.c_gg1 (by rw [h])
  have hff1 : R.f ≠ R.f1 := fun h => R.c_ff1 (by rw [h])
  have hff2 : R.f ≠ R.f2 := fun h => R.c_ff2 (by rw [h])
  have hgg1 : R.g ≠ R.g1 := fun h => R.c_gg1 (by rw [h])
  have hgg2 : R.g ≠ R.g2 := fun h => R.c_gg2 (by rw [h])
  refine ⟨R, ⟨R.Pf, not_pendant_of_two R.jf hQe R.fe.symm (joins_inc_right (joins_ends e)) R.Pf1 hf1f
      (joins_inc_left R.jf1)⟩,
    ⟨R.Pg, not_pendant_of_two R.jg hQe R.ge.symm (joins_inc_right (joins_ends e)) R.Pg1 hg1g
      (joins_inc_left R.jg1)⟩,
    ⟨R.Pf1, not_pendant_of_two R.jf1 R.Pf hff1 (joins_inc_right R.jf) R.Pd1 R.d1f1.symm.symm
      (joins_inc_left R.jd1)⟩,
    ⟨R.Pf2, not_pendant_of_two R.jf2 R.Pf hff2 (joins_inc_right R.jf) R.Pd2 R.d2f2 (joins_inc_left R.jd2)⟩,
    ⟨R.Pg1, not_pendant_of_two R.jg1 R.Pg hgg1 (joins_inc_right R.jg) R.Pd3 R.d3g1 (joins_inc_left R.jd3)⟩,
    ⟨R.Pg2, not_pendant_of_two R.jg2 R.Pg hgg2 (joins_inc_right R.jg) R.Pd4 R.d4g2 (joins_inc_left R.jd4)⟩,
    ?_⟩
  intro h hh hhv
  exact R.atv h hh.1 (fun h' => hh.2 (h' ▸ hpe)) hhv

end MGraph
