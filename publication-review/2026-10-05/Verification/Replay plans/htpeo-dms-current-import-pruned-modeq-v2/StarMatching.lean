/-
  StarMatching.lean — the matching-class scheme ("5 + 1") and the crossing characterisation of star colourings.

  Global structure behind the computations of this round: for a cubic (multi)graph `G` with a perfect matching `M`
  and 2-factor `F = G − M`, a star 6-colouring in which `M` is one colour class is the same thing as a star
  5-colouring of `F` that is *rainbow* at every edge of `M` (the four `F`-edges hanging at the two ends of an
  `M`-edge get four distinct colours).  Rainbow-ness is exactly a proper edge-colouring of the 4-regular
  contraction `G/M`, so the scheme reads: "Vizing's 5 colours on `G/M`, avoiding `abab` along the circuits of the
  transition system, plus one colour on `M`".

    `starOn_compose_rainbow`   star `k`-colouring of `F` + matching `M` with any `j` colours + rainbow  ⟹  star (k+j)
    `six_of_rainbow_five`      the 5 + 1 = 6 instance
    `rainbow_of_star_matching` conversely, a star colouring with a perfect-matching colour class is rainbow at every
                               matching edge (outside triangles), so the two formulations are equivalent
    `star_iff_no_mutual_cross` a proper colouring of a loopless multigraph is star iff no two adjacent edges *cross*
                               each other (the colour of each reappears at the far end of the other)

  No `sorry`, standard axioms only.
-/
import StarCompose

namespace MGraph
variable {G : MGraph}

/-! ### the rainbow condition at a matching -/

/-- `cF` is rainbow at `M`: two distinct `F`-edges hanging at the two ends of an `M`-edge receive different
    colours.  (Adjacent `F`-edges at the same end are already distinct by properness of `cF`, so together the four
    `F`-edges around an `M`-edge are rainbow.) -/
def Rainbow (F M : Fin G.m → Prop) {k : Nat} (cF : Fin G.m → Fin k) : Prop :=
  ∀ b, M b → ∀ y z, G.Joins b y z → ∀ e e', F e → F e' → ¬ M e → ¬ M e' → e ≠ e' →
    G.Inc e y → G.Inc e' z → cF e ≠ cF e'

open Classical in
/-- **Composition with a rainbow matching.**  If `cF` is a star `k`-colouring of `F`, `M` is a matching, and `cF`
    is rainbow at `M`, then giving the edges of `M` any `j` fresh colours yields a star `(k+j)`-colouring of
    `F ∪ M`.  Unlike `starOn_compose`, no condition on the matching colours is needed: the mixed walks
    `(M, F, M, F)` are killed by the `F`-colours. -/
theorem starOn_compose_rainbow {F M : Fin G.m → Prop} {k j : Nat} (cF : Fin G.m → Fin k)
    (cM : Fin G.m → Fin j) (hF : StarOn F k cF)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hrain : Rainbow F M cF) :
    StarOn (fun f => F f ∨ M f) (k + j)
      (fun f => if M f then Fin.natAdd k (cM f) else Fin.castAdd j (cF f)) := by
  constructor
  · intro a b hab ha hb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    by_cases hma : M a <;> by_cases hmb : M b
    · exact hmatch a b hma hmb hne x hax hbx
    · simp only [if_pos hma, if_neg hmb] at heq; exact castAdd_ne_natAdd _ _ heq.symm
    · simp only [if_neg hma, if_pos hmb] at heq; exact castAdd_ne_natAdd _ _ heq
    · simp only [if_neg hma, if_neg hmb] at heq
      exact hF.1 a b ⟨hne, x, hax, hbx⟩ (ha.resolve_right hma) (hb.resolve_right hmb) (castAdd_inj heq)
  · intro w h1 h2 h3 h4 hb
    rcases hb with ⟨hb13, hb24⟩
    by_cases m1 : M w.e1 <;> by_cases m3 : M w.e3
    · -- e1, e3 ∈ M; then e2, e4 ∉ M and they hang at the two ends of e3 with equal colours
      by_cases m2 : M w.e2
      · exact hmatch w.e1 w.e2 m1 m2 w.e1_ne_e2 w.v1 w.inc_e1_v1 w.inc_e2_v1
      by_cases m4 : M w.e4
      · exact hmatch w.e3 w.e4 m3 m4 w.e3_ne_e4 w.v3 w.inc_e3_v3 w.inc_e4_v3
      simp only [if_neg m2, if_neg m4] at hb24
      exact hrain w.e3 m3 w.v2 w.v3 w.h3 w.e2 w.e4 (h2.resolve_right m2) (h4.resolve_right m4) m2 m4
        w.e2_ne_e4 w.inc_e2_v2 w.inc_e4_v3 (castAdd_inj hb24)
    · simp only [if_pos m1, if_neg m3] at hb13; exact castAdd_ne_natAdd _ _ hb13.symm
    · simp only [if_neg m1, if_pos m3] at hb13; exact castAdd_ne_natAdd _ _ hb13
    · simp only [if_neg m1, if_neg m3] at hb13
      by_cases m2 : M w.e2 <;> by_cases m4 : M w.e4
      · -- e2, e4 ∈ M; e1, e3 ∉ M hang at the two ends of e2 with equal colours
        exact hrain w.e2 m2 w.v1 w.v2 w.h2 w.e1 w.e3 (h1.resolve_right m1) (h3.resolve_right m3) m1 m3
          w.e1_ne_e3 w.inc_e1_v1 w.inc_e3_v2 (castAdd_inj hb13)
      · simp only [if_pos m2, if_neg m4] at hb24; exact castAdd_ne_natAdd _ _ hb24.symm
      · simp only [if_neg m2, if_pos m4] at hb24; exact castAdd_ne_natAdd _ _ hb24
      · simp only [if_neg m2, if_neg m4] at hb24
        exact hF.2 w (h1.resolve_right m1) (h2.resolve_right m2) (h3.resolve_right m3)
          (h4.resolve_right m4) ⟨castAdd_inj hb13, castAdd_inj hb24⟩

/-- **5 + 1 = 6.**  A star 5-colouring of `F` that is rainbow at a matching `M` gives a star 6-colouring of
    `F ∪ M` with `M` as a colour class. -/
theorem six_of_rainbow_five {F M : Fin G.m → Prop} (cF : Fin G.m → Fin 5) (hF : StarOn F 5 cF)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hrain : Rainbow F M cF) : Colourable (fun f => F f ∨ M f) 6 :=
  ⟨_, starOn_compose_rainbow cF (fun _ => (0 : Fin 1)) hF hmatch hrain⟩

/-! ### the converse: a star colouring with a perfect-matching colour class is rainbow -/

/-- **Necessity of rainbow-ness.**  Let `c` be a star colouring of `P` in which the edges of `M ⊆ P` all have the
    same colour, `M` a matching covering the vertex `x`.  For an `M`-edge `b = yz`, an `F`-edge `e = xy` and an
    `F`-edge `e' = zw` (with `x ≠ z`, `w ≠ y`, `x ≠ w` — i.e. outside a triangle through `b`), the colours of `e`
    and `e'` differ: otherwise the matching edge at `x`, `e`, `b`, `e'` would be a bicoloured walk. -/
theorem rainbow_of_star_matching {P M : Fin G.m → Prop} {k : Nat} (c : Fin G.m → Fin k) (m₀ : Fin k)
    (hstar : StarOn P k c)
    (hM : ∀ a, M a → P a ∧ c a = m₀)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hloop : ∀ f, (G.ends f).1 ≠ (G.ends f).2)
    {b e e' : Fin G.m} {x y z w : Fin G.n} (hb : M b) (hby : G.Joins b y z)
    (he : P e) (hex : G.Joins e x y) (he' : P e') (he'z : G.Joins e' z w)
    (hxz : x ≠ z) (hwy : w ≠ y) (hxw : x ≠ w)
    {a : Fin G.m} {u : Fin G.n} (ha : M a) (hau : G.Joins a u x) :
    c e ≠ c e' := by
  intro heq
  -- the walk u -a- x -e- y -b- z -e'- w
  have hux : u ≠ x := by
    intro h; rcases hau with h' | h' <;> apply hloop a
    · rw [h']; exact h
    · rw [h']; exact h.symm
  have hxy : x ≠ y := by
    intro h; rcases hex with h' | h' <;> apply hloop e
    · rw [h']; exact h
    · rw [h']; exact h.symm
  have hyz : y ≠ z := by
    intro h; rcases hby with h' | h' <;> apply hloop b
    · rw [h']; exact h
    · rw [h']; exact h.symm
  have hzw : z ≠ w := by
    intro h; rcases he'z with h' | h' <;> apply hloop e'
    · rw [h']; exact h
    · rw [h']; exact h.symm
  have hab : a ≠ b := by
    intro h
    -- a = b joins u x and y z: x ∈ {y, z}
    have hx : G.Inc b x := by rw [← h]; exact joins_inc_right hau
    rcases inc_of_joins hby hx with hx | hx
    · exact hxy hx
    · exact hxz hx
  have huy : u ≠ y := by
    intro h
    -- a is incident to y, b is incident to y, a ≠ b: contradicts the matching
    exact hmatch a b ha hb hab y (by rw [← h]; exact joins_inc_left hau) (joins_inc_left hby)
  have huz : u ≠ z := by
    intro h
    exact hmatch a b ha hb hab z (by rw [← h]; exact joins_inc_left hau) (joins_inc_right hby)
  let W : G.Walk4 :=
    { v0 := u
      v1 := x
      v2 := y
      v3 := z
      v4 := w
      e1 := a
      e2 := e
      e3 := b
      e4 := e'
      h1 := hau
      h2 := hex
      h3 := hby
      h4 := he'z
      d01 := hux
      d02 := huy
      d03 := huz
      d12 := hxy
      d13 := hxz
      d14 := hxw
      d23 := hyz
      d24 := hwy.symm
      d34 := hzw }
  apply hstar.2 W (hM a ha).1 he (hM b hb).1 he'
  exact ⟨by show c a = c b; rw [(hM a ha).2, (hM b hb).2], heq⟩

/-! ### crossing: a local characterisation of star colourings -/

theorem joins_symm' {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : G.Joins f y x := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- every edge incident to `v` joins some `u` to `v` -/
theorem exists_joins_of_inc {g : Fin G.m} {v : Fin G.n} (h : G.Inc g v) : ∃ u, G.Joins g u v := by
  rcases h with h | h
  · exact ⟨(G.ends g).2, Or.inr (by rw [← h])⟩
  · exact ⟨(G.ends g).1, Or.inl (by rw [← h])⟩

/-- `e` and `f` are adjacent at `v` (`e = v v'`, `f = v v''`) and **cross each other**: the colour of `f`
    reappears at the far end `v'` of `e` on a third edge, and the colour of `e` reappears at the far end `v''` of
    `f` on a third edge. -/
def MutualCross {k : Nat} (c : Fin G.m → Fin k) (e f : Fin G.m) (v v' v'' : Fin G.n) : Prop :=
  G.Joins e v v' ∧ G.Joins f v v'' ∧ e ≠ f ∧
    (∃ g, g ≠ e ∧ g ≠ f ∧ G.Inc g v' ∧ c g = c f) ∧ (∃ h, h ≠ e ∧ h ≠ f ∧ G.Inc h v'' ∧ c h = c e)

/-- **Star colourings are exactly the proper colourings without mutual crossings** (loopless multigraphs):
    a bicoloured walk `e1 e2 e3 e4` is the same thing as the adjacent pair `e2, e3` crossing each other. -/
theorem star_iff_no_mutual_cross {k : Nat} (c : Fin G.m → Fin k) (hloop : ∀ f, (G.ends f).1 ≠ (G.ends f).2) :
    Star k c ↔ (∀ a b, G.Adj a b → c a ≠ c b) ∧ (∀ e f v v' v'', ¬ MutualCross c e f v v' v'') := by
  have nl : ∀ {f : Fin G.m} {x y : Fin G.n}, G.Joins f x y → x ≠ y := by
    intro f x y h hxy
    rcases h with h | h <;> apply hloop f
    · rw [h]; exact hxy
    · rw [h]; exact hxy.symm
  constructor
  · intro hs
    refine ⟨fun a b hab => hs.1 a b hab trivial trivial, ?_⟩
    intro e f v v' v'' hm
    rcases hm with ⟨hev, hfv, hef, ⟨g, hge, hgf, hgv', hgc⟩, ⟨h, hhe, hhf, hhv'', hhc⟩⟩
    obtain ⟨v0, hg⟩ := exists_joins_of_inc hgv'
    obtain ⟨v4, hh⟩ := exists_joins_of_inc hhv''
    have proper : ∀ a b, G.Adj a b → c a ≠ c b := fun a b hab => hs.1 a b hab trivial trivial
    -- distinctness of the walk v0 -g- v' -e- v -f- v'' -h- v4
    have d01 : v0 ≠ v' := nl hg
    have d12 : v' ≠ v := (nl hev).symm
    have d23 : v ≠ v'' := nl hfv
    have d34 : v'' ≠ v4 := (nl hh).symm
    have d02 : v0 ≠ v := by
      intro h0
      -- g joins v' and v: g is adjacent to f at v
      exact proper g f ⟨hgf, v, (by rw [← h0]; exact joins_inc_left hg), joins_inc_left hfv⟩ hgc
    have d03 : v0 ≠ v'' := by
      intro h0
      exact proper g f ⟨hgf, v'', (by rw [← h0]; exact joins_inc_left hg), joins_inc_right hfv⟩ hgc
    have d13 : v' ≠ v'' := by
      intro h0
      -- f is at v' = v'', g is at v': adjacent
      exact proper g f ⟨hgf, v', hgv', (by rw [h0]; exact joins_inc_right hfv)⟩ hgc
    have d14 : v' ≠ v4 := by
      intro h0
      -- h joins v'' and v4 = v': h is adjacent to e at v'
      exact proper h e ⟨hhe, v', (by rw [h0]; exact joins_inc_left hh), joins_inc_right hev⟩ hhc
    have d24 : v ≠ v4 := by
      intro h0
      exact proper h e ⟨hhe, v, (by rw [h0]; exact joins_inc_left hh), joins_inc_left hev⟩ hhc
    let W : G.Walk4 :=
      { v0 := v0
        v1 := v'
        v2 := v
        v3 := v''
        v4 := v4
        e1 := g
        e2 := e
        e3 := f
        e4 := h
        h1 := hg
        h2 := joins_symm' hev
        h3 := hfv
        h4 := joins_symm' hh
        d01 := d01
        d02 := d02
        d03 := d03
        d12 := d12
        d13 := d13
        d14 := d14
        d23 := d23
        d24 := d24
        d34 := d34 }
    exact hs.2 W trivial trivial trivial trivial ⟨hgc, hhc.symm⟩
  · intro ⟨hp, hnc⟩
    refine ⟨fun a b hab _ _ => hp a b hab, ?_⟩
    intro w _ _ _ _ hb
    apply hnc w.e2 w.e3 w.v2 w.v1 w.v3
    exact ⟨joins_symm' w.h2, w.h3, w.e2_ne_e3, ⟨w.e1, w.e1_ne_e2, w.e1_ne_e3, w.inc_e1_v1, hb.1⟩,
      ⟨w.e4, fun h => w.e2_ne_e4 h.symm, fun h => w.e3_ne_e4 h.symm, w.inc_e4_v3, hb.2.symm⟩⟩

end MGraph
