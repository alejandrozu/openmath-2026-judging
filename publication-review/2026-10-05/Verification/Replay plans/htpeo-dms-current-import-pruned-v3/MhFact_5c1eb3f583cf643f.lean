-- Lean proof of fact 5c1eb3f583cf643f (MGraph.dms_of_hole); added by fact_submit, do not edit
/-
  HoleDMS.lean — HOLE implies DMS, formally (Lean 4.20 core, project library, standard axioms only).

  Main theorem `MGraph.dms_of_hole : HOLE → ∀ G, Subcubic G → Loopless G → ∀ P, Colourable P 6`.

  HOLE (definition `MGraph.HOLE`): for every connected (`ConnectedOn`), bridgeless (`BridgelessOn`), loopless
  cubic (`CubicOn`) multigraph `P` (an edge set of a loopless ambient multigraph) that is not isomorphic to K₃,₃
  (`¬ IsoTo k33 P`), and every vertex `t` of `P`, there are a star 6-colouring `c` of `P` and a colour `β` that is
  on no edge of `P` incident with a vertex of `N[t]` (`HoleOn`).

  Proof: take a minimal non-star-6-colourable edge set `Q` (library `exists_minimal`).  Its core is connected and
  has no cut (library `core_no_cut`, Route-A lemmas below).  Count the vertices of `Q`-degree one or two:
    * none:        `Q` is cubic, bridgeless and connected; HOLE (or the K₃,₃ certificate) colours it;
    * two or more: double `Q` and join each such vertex to its copy by one rung (two parallel rungs at a leaf);
                   the result is cubic, connected and bridgeless (`dblP_*`), and HOLE colours it;
    * exactly one: suppress the degree-two vertex `y` (new edge `u w`); the result is cubic, connected and
                   bridgeless (`SuppData.supp_*`); HOLE at `w` gives a hole, and the formal hole lemma
                   `hole_extend` colours `Q`; if the suppressed graph is K₃,₃ the nine certificates for
                   `T(K₃,₃, h)` are transported (`k33_supp_colourable`).
  Part 0 is an excerpt of the Route-A module of fact df88bfc269437d45 (definitions `Loopless`, `ConnectedOn`,
  `IsoTo`, `k33`, the K₃,₃ certificate, isomorphism transfer, minimal-counterexample core lemmas), copied verbatim.
-/
import StarBottleneck
import StarChecker
import StarMatching
import StarExtension

/-! ===================== part 0: Route-A definitions and lemmas (from the module of fact df88bfc269437d45) ===================== -/
namespace MGraph

/-! ### the notions in the statement -/

/-- no edge of `G` is a loop -/
def Loopless (G : MGraph) : Prop := ∀ f : Fin G.m, (G.ends f).1 ≠ (G.ends f).2

variable {G : MGraph}

/-- the edge set `P` is connected: every vertex 2-colouring `U` under which no edge of `P` has differently
    coloured ends gives all edges of `P` the same colour -/
def ConnectedOn (P : Fin G.m → Prop) : Prop :=
  ∀ U : Fin G.n → Bool, (∀ f, P f → U (G.ends f).1 = U (G.ends f).2) →
    ∀ f g, P f → P g → U (G.ends f).1 = U (G.ends g).1

/-- the sub-multigraph `P` of `G` is isomorphic to `H` (a multigraph without isolated vertices): an injective vertex
    map `φ` and an injective edge map `ψ` with image exactly `P`, respecting incidence -/
def IsoTo (H : MGraph) (P : Fin G.m → Prop) : Prop :=
  ∃ φ : Fin H.n → Fin G.n, ∃ ψ : Fin H.m → Fin G.m,
    (∀ a b, φ a = φ b → a = b) ∧ (∀ e e', ψ e = ψ e' → e = e') ∧
    (∀ e, G.Joins (ψ e) (φ (H.ends e).1) (φ (H.ends e).2)) ∧ (∀ f, P f ↔ ∃ e, ψ e = f)

/-- a multigraph on `Fin n` from a list of edges -/
def ofList (n : Nat) (l : List (Nat × Nat)) (hn : 0 < n) : MGraph where
  n := n
  m := l.length
  ends := fun i => (⟨(l.get i).1 % n, Nat.mod_lt _ hn⟩, ⟨(l.get i).2 % n, Nat.mod_lt _ hn⟩)


/-- K₃,₃ (graph6 `EFz_`) -/
def k33 : MGraph := ofList 6 [(0,3),(1,3),(2,3),(0,4),(1,4),(2,4),(0,5),(1,5),(2,5)] (by decide)

/-! ### positive star 6-certificates (kernel `decide`) -/

/-- a colouring from a list of numbers -/
def colOf (H : MGraph) (l : List Nat) : Fin H.m → Fin 6 := fun i => ⟨l.getD i.val 0 % 6, Nat.mod_lt _ (by decide)⟩

def k33Col : Fin k33.m → Fin 6 := colOf k33 [0, 1, 2, 1, 3, 4, 2, 4, 5]

theorem k33_check : k33.starCheck (fun _ => true) k33Col = true := by decide

theorem k33_star6 : Star (G := k33) 6 k33Col := k33.star_of_check k33Col k33_check

/-! ### transfer of a colouring along an isomorphism -/

section transfer
variable {H : MGraph} {φ : Fin H.n → Fin G.n} {ψ : Fin H.m → Fin G.m}

theorem iso_inc (hj : ∀ e, G.Joins (ψ e) (φ (H.ends e).1) (φ (H.ends e).2)) {e : Fin H.m} {x : Fin G.n}
    (hx : G.Inc (ψ e) x) : ∃ a, H.Inc e a ∧ φ a = x := by
  rcases inc_of_joins (hj e) hx with h | h
  · exact ⟨(H.ends e).1, Or.inl rfl, h.symm⟩
  · exact ⟨(H.ends e).2, Or.inr rfl, h.symm⟩

theorem iso_inc' (hj : ∀ e, G.Joins (ψ e) (φ (H.ends e).1) (φ (H.ends e).2)) {e : Fin H.m} {a : Fin H.n}
    (ha : H.Inc e a) : G.Inc (ψ e) (φ a) := by
  rcases ha with h | h
  · rw [← h]; exact joins_inc_left (hj e)
  · rw [← h]; exact joins_inc_right (hj e)

theorem iso_joins (hφ : ∀ a b, φ a = φ b → a = b) (hj : ∀ e, G.Joins (ψ e) (φ (H.ends e).1) (φ (H.ends e).2))
    {e : Fin H.m} {a b : Fin H.n} (h : G.Joins (ψ e) (φ a) (φ b)) : H.Joins e a b := by
  rcases joins_unique (hj e) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by rw [← hφ _ _ h1, ← hφ _ _ h2])
  · exact Or.inr (by rw [← hφ _ _ h1, ← hφ _ _ h2])

end transfer

/-- **Transfer.**  If `P ≅ H` and `H` has a star `k`-colouring (`k > 0`), then `P` is star `k`-colourable. -/
theorem colourable_of_iso {H : MGraph} {P : Fin G.m → Prop} {k : Nat} (hiso : IsoTo H P)
    (cH : Fin H.m → Fin k) (hH : Star k cH) (hk : 0 < k) : Colourable P k := by
  classical
  obtain ⟨φ, ψ, hφ, hψ, hj, hP⟩ := hiso
  let c : Fin G.m → Fin k := fun f => if h : ∃ e, ψ e = f then cH (Classical.choose h) else ⟨0, hk⟩
  have hc : ∀ e, c (ψ e) = cH e := by
    intro e
    have hex : ∃ e', ψ e' = ψ e := ⟨e, rfl⟩
    show (if h : ∃ e', ψ e' = ψ e then cH (Classical.choose h) else ⟨0, hk⟩) = cH e
    rw [dif_pos hex, hψ _ _ (Classical.choose_spec hex)]
  refine ⟨c, ?_, ?_⟩
  · intro a b hab ha hb heq
    obtain ⟨ea, rfl⟩ := (hP a).1 ha
    obtain ⟨eb, rfl⟩ := (hP b).1 hb
    obtain ⟨hne, x, hax, hbx⟩ := hab
    obtain ⟨y, hy, hyx⟩ := iso_inc hj hax
    obtain ⟨y', hy', hy'x⟩ := iso_inc hj hbx
    have hyy : y = y' := hφ _ _ (hyx.trans hy'x.symm)
    subst hyy
    have hadj : H.Adj ea eb := ⟨fun h => hne (by rw [h]), y, hy, hy'⟩
    rw [hc, hc] at heq
    exact hH.1 ea eb hadj trivial trivial heq
  · intro w h1 h2 h3 h4 hb
    obtain ⟨ε1, hε1⟩ := (hP _).1 h1
    obtain ⟨ε2, hε2⟩ := (hP _).1 h2
    obtain ⟨ε3, hε3⟩ := (hP _).1 h3
    obtain ⟨ε4, hε4⟩ := (hP _).1 h4
    obtain ⟨u0, -, hu0⟩ := iso_inc hj (hε1 ▸ w.inc_e1_v0)
    obtain ⟨u1, -, hu1⟩ := iso_inc hj (hε1 ▸ w.inc_e1_v1)
    obtain ⟨u2, -, hu2⟩ := iso_inc hj (hε2 ▸ w.inc_e2_v2)
    obtain ⟨u3, -, hu3⟩ := iso_inc hj (hε3 ▸ w.inc_e3_v3)
    obtain ⟨u4, -, hu4⟩ := iso_inc hj (hε4 ▸ w.inc_e4_v4)
    have j1 : H.Joins ε1 u0 u1 := iso_joins hφ hj (by rw [hε1, hu0, hu1]; exact w.h1)
    have j2 : H.Joins ε2 u1 u2 := iso_joins hφ hj (by rw [hε2, hu1, hu2]; exact w.h2)
    have j3 : H.Joins ε3 u2 u3 := iso_joins hφ hj (by rw [hε3, hu2, hu3]; exact w.h3)
    have j4 : H.Joins ε4 u3 u4 := iso_joins hφ hj (by rw [hε4, hu3, hu4]; exact w.h4)
    let w' : H.Walk4 :=
      { v0 := u0, v1 := u1, v2 := u2, v3 := u3, v4 := u4, e1 := ε1, e2 := ε2, e3 := ε3, e4 := ε4,
        h1 := j1, h2 := j2, h3 := j3, h4 := j4,
        d01 := fun h => w.d01 (by rw [← hu0, ← hu1, h])
        d02 := fun h => w.d02 (by rw [← hu0, ← hu2, h])
        d03 := fun h => w.d03 (by rw [← hu0, ← hu3, h])
        d12 := fun h => w.d12 (by rw [← hu1, ← hu2, h])
        d13 := fun h => w.d13 (by rw [← hu1, ← hu3, h])
        d14 := fun h => w.d14 (by rw [← hu1, ← hu4, h])
        d23 := fun h => w.d23 (by rw [← hu2, ← hu3, h])
        d24 := fun h => w.d24 (by rw [← hu2, ← hu4, h])
        d34 := fun h => w.d34 (by rw [← hu3, ← hu4, h]) }
    apply hH.2 w' trivial trivial trivial trivial
    obtain ⟨b13, b24⟩ := hb
    rw [← hε1, ← hε3, hc, hc] at b13
    rw [← hε2, ← hε4, hc, hc] at b24
    exact ⟨b13, b24⟩

theorem k33_colourable {P : Fin G.m → Prop} (h : IsoTo k33 P) : Colourable P 6 :=
  colourable_of_iso h k33Col k33_star6 (by decide)

/-! ### gluing along a side function -/

/-- If `s` gives any two `Q`-edges sharing a vertex the same value, colourings of the two sides glue. -/
theorem colourable_of_sides {Q : Fin G.m → Prop} {k : Nat} (s : Fin G.m → Bool)
    (hs : ∀ a b x, Q a → Q b → a ≠ b → G.Inc a x → G.Inc b x → s a = s b)
    (h1 : Colourable (fun f => Q f ∧ s f = true) k) (h2 : Colourable (fun f => Q f ∧ s f = false) k) :
    Colourable Q k := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨fun f => if s f then c1 f else c2 f, ?_, ?_⟩
  · intro a b hab ha hb heq
    have hsab := hs a b _ ha hb hab.1 hab.2.choose_spec.1 hab.2.choose_spec.2
    cases hsa : s a <;> rw [hsa] at hsab
    · simp only [hsa, ← hsab] at heq
      exact hc2.1 a b hab ⟨ha, hsa⟩ ⟨hb, hsab.symm⟩ (by simpa using heq)
    · simp only [hsa, ← hsab] at heq
      exact hc1.1 a b hab ⟨ha, hsa⟩ ⟨hb, hsab.symm⟩ (by simpa using heq)
  · intro w q1 q2 q3 q4 hb
    have s12 := hs _ _ _ q1 q2 w.e1_ne_e2 w.inc_e1_v1 w.inc_e2_v1
    have s23 := hs _ _ _ q2 q3 w.e2_ne_e3 w.inc_e2_v2 w.inc_e3_v2
    have s34 := hs _ _ _ q3 q4 w.e3_ne_e4 w.inc_e3_v3 w.inc_e4_v3
    obtain ⟨b13, b24⟩ := hb
    cases hs1 : s w.e1
    · have e2 : s w.e2 = false := s12.symm.trans hs1
      have e3 : s w.e3 = false := s23.symm.trans e2
      have e4 : s w.e4 = false := s34.symm.trans e3
      simp only [hs1, e2, e3, e4] at b13 b24
      exact hc2.2 w ⟨q1, hs1⟩ ⟨q2, e2⟩ ⟨q3, e3⟩ ⟨q4, e4⟩ ⟨by simpa using b13, by simpa using b24⟩
    · have e2 : s w.e2 = true := s12.symm.trans hs1
      have e3 : s w.e3 = true := s23.symm.trans e2
      have e4 : s w.e4 = true := s34.symm.trans e3
      simp only [hs1, e2, e3, e4] at b13 b24
      exact hc1.2 w ⟨q1, hs1⟩ ⟨q2, e2⟩ ⟨q3, e3⟩ ⟨q4, e4⟩ ⟨by simpa using b13, by simpa using b24⟩

/-- an endpoint of a non-pendant edge carries another edge -/
theorem exists_other_of_not_pendant {Q : Fin G.m → Prop} {f : Fin G.m} {x : Fin G.n} (hQ : Q f)
    (hnp : ¬ Pendant Q f) (hx : G.Inc f x) : ∃ g, Q g ∧ g ≠ f ∧ G.Inc g x :=
  Classical.byContradiction fun h => hnp ⟨hQ, x, hx, fun g hg hgf hgx => h ⟨g, hg, hgf, hgx⟩⟩

/-! ### the core of a minimal counterexample -/

/-- **The core of a minimal counterexample is connected.** -/
theorem minimal_core_connected {Q : Fin G.m → Prop} {k : Nat} (hmin : MinimalCounterexample Q k) :
    ConnectedOn (Core Q) := by
  classical
  intro U hU f g hf hg
  apply Classical.byContradiction
  intro hne
  let s : Fin G.m → Bool := fun h =>
    if ∃ g, Q g ∧ g ≠ h ∧ G.Inc g (G.ends h).1 then U (G.ends h).1 else U (G.ends h).2
  have key : ∀ h x, Q h → G.Inc h x → (∃ g, Q g ∧ g ≠ h ∧ G.Inc g x) → s h = U x := by
    intro h x hQh hx hoth
    by_cases hA : ∃ g, Q g ∧ g ≠ h ∧ G.Inc g (G.ends h).1
    · have hs : s h = U (G.ends h).1 := if_pos hA
      rw [hs]
      rcases hx with hx | hx
      · rw [hx]
      · have hcore : Core Q h := by
          refine ⟨hQh, ?_⟩
          rintro ⟨-, z, hz, hleaf⟩
          rcases hz with hz | hz
          · obtain ⟨g', hg', hg'h, hg'x⟩ := hA
            exact hleaf g' hg' hg'h (hz ▸ hg'x)
          · obtain ⟨g', hg', hg'h, hg'x⟩ := hoth
            exact hleaf g' hg' hg'h (hz ▸ hx ▸ hg'x)
        rw [hU h hcore, hx]
    · have hs : s h = U (G.ends h).2 := if_neg hA
      rw [hs]
      rcases hx with hx | hx
      · exact absurd (hx ▸ hoth) hA
      · rw [hx]
  have hs : ∀ a b x, Q a → Q b → a ≠ b → G.Inc a x → G.Inc b x → s a = s b := by
    intro a b x ha hb hab hax hbx
    rw [key a x ha hax ⟨b, hb, fun h => hab h.symm, hbx⟩, key b x hb hbx ⟨a, ha, hab, hax⟩]
  have hsf : s f = U (G.ends f).1 :=
    key f _ hf.1 (Or.inl rfl) (exists_other_of_not_pendant hf.1 hf.2 (Or.inl rfl))
  have hsg : s g = U (G.ends g).1 :=
    key g _ hg.1 (Or.inl rfl) (exists_other_of_not_pendant hg.1 hg.2 (Or.inl rfl))
  apply hmin.1
  apply colourable_of_sides s hs
  · apply hmin.2
    refine ⟨fun h hh => hh.1, ?_⟩
    cases hvf : s f
    · exact ⟨f, hf.1, fun h => Bool.false_ne_true (hvf.symm.trans h.2)⟩
    · cases hvg : s g
      · exact ⟨g, hg.1, fun h => Bool.false_ne_true (hvg.symm.trans h.2)⟩
      · exact absurd (hsf.symm.trans (hvf.trans (hvg.symm.trans hsg))) hne
  · apply hmin.2
    refine ⟨fun h hh => hh.1, ?_⟩
    cases hvf : s f
    · cases hvg : s g
      · exact absurd (hsf.symm.trans (hvf.trans (hvg.symm.trans hsg))) hne
      · exact ⟨g, hg.1, fun h => Bool.false_ne_true (hvg.symm.trans h.2).symm⟩
    · exact ⟨f, hf.1, fun h => Bool.false_ne_true (hvf.symm.trans h.2).symm⟩

/-- the attachment vertex of a pendant edge of a minimal counterexample carries two further edges, both in the core -/
theorem pendant_attach (hsub : Subcubic G) {Q : Fin G.m → Prop} (hmin : MinimalCounterexample Q 6) {p : Fin G.m}
    (hp : Pendant Q p) : ∃ l y, G.Joins p l y ∧ (∀ g, Q g → g ≠ p → ¬ G.Inc g l) ∧
      ∃ f g, Core Q f ∧ Core Q g ∧ f ≠ p ∧ g ≠ p ∧ f ≠ g ∧ G.Inc f y ∧ G.Inc g y := by
  obtain ⟨hQp, l, hl, hleaf⟩ := hp
  obtain ⟨y, hj⟩ := exists_joins_of_inc hl
  have hj' : G.Joins p l y := joins_symm' hj
  obtain ⟨f, g, hQf, hQg, hfp, hgp, hfg, hfy, hgy, -⟩ := minimal_leaf_at hsub Q hmin p hQp hj' hleaf
  have hpy : G.Inc p y := joins_inc_right hj'
  have core_of : ∀ h, Q h → h ≠ p → G.Inc h y → Core Q h := fun h hQh hhp hhy =>
    ⟨hQh, fun hph => pendants_disjoint hsub Q hmin ⟨hQp, l, hl, hleaf⟩ hph (fun e => hhp e.symm) hpy hhy⟩
  exact ⟨l, y, hj', hleaf, f, g, core_of f hQf hfp hfy, core_of g hQg hgp hgy, hfp, hgp, hfg, hfy, hgy⟩

end MGraph

/-! ===================== part 1 ===================== -/


namespace MGraph

/-! ## The statement HOLE -/

section defs
variable {G : MGraph}

/-- `P` is cubic: every vertex meeting `P` meets exactly three distinct edges of `P` -/
def CubicOn (P : Fin G.m → Prop) : Prop :=
  ∀ x, (∃ f, P f ∧ G.Inc f x) → ∃ a b c, P a ∧ P b ∧ P c ∧ G.Inc a x ∧ G.Inc b x ∧ G.Inc c x ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ d, P d → G.Inc d x → d = a ∨ d = b ∨ d = c

/-- `P` is bridgeless: for no edge `e` of `P` are the two ends of `e` separated in `P − e` (a `CutOn P e` is a
    vertex 2-colouring separating the ends of `e` under which no other edge of `P` has differently coloured ends) -/
def BridgelessOn (P : Fin G.m → Prop) : Prop := ∀ e, P e → G.CutOn P e → False

/-- colour `β` is on no edge of `P` incident with a vertex of `N[t]` (`t` and every vertex joined to `t` by an edge
    of `P`) -/
def HoleOn (P : Fin G.m → Prop) (c : Fin G.m → Fin 6) (t : Fin G.n) (β : Fin 6) : Prop :=
  ∀ e v, P e → G.Inc e v → (v = t ∨ ∃ f, P f ∧ G.Joins f t v) → c e ≠ β

end defs

/-- **HOLE.** For every connected, bridgeless, loopless cubic multigraph `P` (an edge set of a loopless ambient
    multigraph `X`) that is not isomorphic to K₃,₃, and every vertex `t` of `P`, there are a star 6-colouring `c` of
    `P` and a colour `β` on no edge of `P` incident with a vertex of `N[t]`. -/
def HOLE : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → ConnectedOn P → BridgelessOn P → CubicOn P →
    ¬ IsoTo k33 P → ∀ t : Fin X.n, (∃ f, P f ∧ X.Inc f t) →
      ∃ c : Fin X.m → Fin 6, ∃ β : Fin 6, StarOn P 6 c ∧ HoleOn P c t β

variable {G : MGraph}

/-! ## Generic tools -/

/-- a separating vertex labelling gives a cut (orientation fixed by negating if necessary) -/
theorem cut_of_sep {P : Fin G.m → Prop} {e : Fin G.m} (V : Fin G.n → Bool)
    (he : V (G.ends e).1 ≠ V (G.ends e).2)
    (hsep : ∀ f, P f → f ≠ e → V (G.ends f).1 = V (G.ends f).2) : Nonempty (G.CutOn P e) := by
  cases h1 : V (G.ends e).1 <;> cases h2 : V (G.ends e).2 <;> rw [h1, h2] at he
  · exact absurd rfl he
  · refine ⟨⟨fun x => !V x, ?_, ?_, fun f hf hfe => by simp [hsep f hf hfe]⟩⟩
    · simp [h1]
    · simp [h2]
  · exact ⟨⟨V, h1, h2, hsep⟩⟩
  · exact absurd rfl he

theorem bridgeless_sep {P : Fin G.m → Prop} (hb : BridgelessOn P) {e : Fin G.m} (he : P e) (V : Fin G.n → Bool)
    (hne : V (G.ends e).1 ≠ V (G.ends e).2)
    (hsep : ∀ f, P f → f ≠ e → V (G.ends f).1 = V (G.ends f).2) : False := by
  obtain ⟨B⟩ := cut_of_sep V hne hsep
  exact hb e he B

/-- a labelling that does not separate an edge gives both of its ends the same value -/
theorem lab_inc {U : Fin G.n → Bool} {a : Fin G.m} {x : Fin G.n} (hs : U (G.ends a).1 = U (G.ends a).2)
    (hx : G.Inc a x) : U x = U (G.ends a).1 := by
  rcases hx with h | h
  · rw [h]
  · rw [← h, hs]

theorem lab_joins {U : Fin G.n → Bool} {a : Fin G.m} {x y : Fin G.n} (hs : U (G.ends a).1 = U (G.ends a).2)
    (hj : G.Joins a x y) : U x = U y := by
  rw [lab_inc hs (joins_inc_left hj), lab_inc hs (joins_inc_right hj)]

/-- **A minimal counterexample is connected.** -/
theorem minimal_connected {Q : Fin G.m → Prop} {k : Nat} (hmin : MinimalCounterexample Q k) : ConnectedOn Q := by
  classical
  intro U hU f g hf hg
  apply Classical.byContradiction
  intro hne
  let s : Fin G.m → Bool := fun a => U (G.ends a).1
  have hs : ∀ a b x, Q a → Q b → a ≠ b → G.Inc a x → G.Inc b x → s a = s b := by
    intro a b x ha hb _ hax hbx
    show U (G.ends a).1 = U (G.ends b).1
    rw [← lab_inc (hU a ha) hax, ← lab_inc (hU b hb) hbx]
  apply hmin.1
  cases hsf : s f
  · -- f on the `false` side, g on the `true` side
    have hsg : s g = true := by
      cases h : s g
      · exact absurd (hsf.trans h.symm) hne
      · rfl
    refine colourable_of_sides s hs (hmin.2 _ ⟨fun a ha => ha.1, f, hf, fun h => ?_⟩)
      (hmin.2 _ ⟨fun a ha => ha.1, g, hg, fun h => ?_⟩)
    · exact Bool.false_ne_true (hsf.symm.trans h.2)
    · exact Bool.false_ne_true (h.2.symm.trans hsg)
  · have hsg : s g = false := by
      cases h : s g
      · rfl
      · exact absurd (hsf.trans h.symm) hne
    refine colourable_of_sides s hs (hmin.2 _ ⟨fun a ha => ha.1, g, hg, fun h => ?_⟩)
      (hmin.2 _ ⟨fun a ha => ha.1, f, hf, fun h => ?_⟩)
    · exact Bool.false_ne_true (hsg.symm.trans h.2)
    · exact Bool.false_ne_true (h.2.symm.trans hsf)

/-! ### degrees inside an edge set -/

/-- exactly one edge of `Q` at `v` -/
def QDeg1 (Q : Fin G.m → Prop) (v : Fin G.n) : Prop := ∃ a, Q a ∧ G.Inc a v ∧ ∀ d, Q d → G.Inc d v → d = a
/-- exactly two edges of `Q` at `v` -/
def QDeg2 (Q : Fin G.m → Prop) (v : Fin G.n) : Prop :=
  ∃ a b, Q a ∧ Q b ∧ G.Inc a v ∧ G.Inc b v ∧ a ≠ b ∧ ∀ d, Q d → G.Inc d v → d = a ∨ d = b
/-- exactly three edges of `Q` at `v` -/
def QDeg3 (Q : Fin G.m → Prop) (v : Fin G.n) : Prop :=
  ∃ a b c, Q a ∧ Q b ∧ Q c ∧ G.Inc a v ∧ G.Inc b v ∧ G.Inc c v ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ d, Q d → G.Inc d v → d = a ∨ d = b ∨ d = c

theorem qdeg_cases (hsub : Subcubic G) (Q : Fin G.m → Prop) {v : Fin G.n} (hv : ∃ f, Q f ∧ G.Inc f v) :
    QDeg1 Q v ∨ QDeg2 Q v ∨ QDeg3 Q v := by
  classical
  obtain ⟨a, hQa, hav⟩ := hv
  by_cases h2 : ∃ b, Q b ∧ G.Inc b v ∧ b ≠ a
  · obtain ⟨b, hQb, hbv, hba⟩ := h2
    by_cases h3 : ∃ c, Q c ∧ G.Inc c v ∧ c ≠ a ∧ c ≠ b
    · obtain ⟨c, hQc, hcv, hca, hcb⟩ := h3
      refine Or.inr (Or.inr ⟨a, b, c, hQa, hQb, hQc, hav, hbv, hcv, Ne.symm hba, Ne.symm hca, Ne.symm hcb, ?_⟩)
      intro d hQd hdv
      apply Classical.byContradiction
      intro hd
      simp only [not_or] at hd
      exact hsub v a b c d hav hbv hcv hdv (Ne.symm hba) (Ne.symm hca) (fun h => hd.1 h.symm)
        (Ne.symm hcb) (fun h => hd.2.1 h.symm) (fun h => hd.2.2 h.symm)
    · refine Or.inr (Or.inl ⟨a, b, hQa, hQb, hav, hbv, Ne.symm hba, ?_⟩)
      intro d hQd hdv
      apply Classical.byContradiction
      intro hd
      simp only [not_or] at hd
      exact h3 ⟨d, hQd, hdv, hd.1, hd.2⟩
  · refine Or.inl ⟨a, hQa, hav, ?_⟩
    intro d hQd hdv
    apply Classical.byContradiction
    intro hd
    exact h2 ⟨d, hQd, hdv, hd⟩

theorem qdeg1_not2 {Q : Fin G.m → Prop} {v : Fin G.n} (h1 : QDeg1 Q v) (h2 : QDeg2 Q v) : False := by
  obtain ⟨a, _, _, ha⟩ := h1
  obtain ⟨b, c, hQb, hQc, hbv, hcv, hbc, _⟩ := h2
  exact hbc ((ha b hQb hbv).trans (ha c hQc hcv).symm)

theorem qdeg1_not3 {Q : Fin G.m → Prop} {v : Fin G.n} (h1 : QDeg1 Q v) (h3 : QDeg3 Q v) : False := by
  obtain ⟨a, _, _, ha⟩ := h1
  obtain ⟨b, c, _, hQb, hQc, _, hbv, hcv, _, hbc, _, _, _⟩ := h3
  exact hbc ((ha b hQb hbv).trans (ha c hQc hcv).symm)

theorem qdeg2_not3 {Q : Fin G.m → Prop} {v : Fin G.n} (h2 : QDeg2 Q v) (h3 : QDeg3 Q v) : False := by
  obtain ⟨a, b, _, _, _, _, _, hab⟩ := h2
  obtain ⟨x, y, z, hQx, hQy, hQz, hxv, hyv, hzv, hxy, hxz, hyz, _⟩ := h3
  rcases hab x hQx hxv with hx | hx <;> rcases hab y hQy hyv with hy | hy <;>
    rcases hab z hQz hzv with hz | hz
  all_goals first
    | exact hxy (hx.trans hy.symm) | exact hxz (hx.trans hz.symm) | exact hyz (hy.trans hz.symm)

/-! ### transfer of a star colouring along an embedding -/

section embed
variable {H : MGraph} {Q : Fin G.m → Prop} {P : Fin H.m → Prop}
variable (φ : Fin G.n → Fin H.n) (ψ : Fin G.m → Fin H.m)

theorem embed_joins (hj : ∀ a, Q a → H.Joins (ψ a) (φ (G.ends a).1) (φ (G.ends a).2)) {a : Fin G.m}
    (hQa : Q a) {x y : Fin G.n} (h : G.Joins a x y) : H.Joins (ψ a) (φ x) (φ y) := by
  rcases joins_unique (joins_ends a) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact hj a hQa
  · rw [← h1, ← h2]; exact joins_symm (hj a hQa)

theorem embed_inc (hj : ∀ a, Q a → H.Joins (ψ a) (φ (G.ends a).1) (φ (G.ends a).2)) {a : Fin G.m}
    (hQa : Q a) {x : Fin G.n} (h : G.Inc a x) : H.Inc (ψ a) (φ x) := by
  rcases h with h | h
  · rw [← h]; exact joins_inc_left (hj a hQa)
  · rw [← h]; exact joins_inc_right (hj a hQa)

/-- **Embedding transfer.** Maps of vertices and edges, injective on `Q`, respecting incidence and sending `Q` into
    `P`, pull a star colouring of `P` back to a star colouring of `Q`. -/
theorem starOn_embed {k : Nat}
    (hφ : ∀ x y a b, Q a → Q b → G.Inc a x → G.Inc b y → φ x = φ y → x = y)
    (hψ : ∀ a b, Q a → Q b → ψ a = ψ b → a = b)
    (hP : ∀ a, Q a → P (ψ a))
    (hj : ∀ a, Q a → H.Joins (ψ a) (φ (G.ends a).1) (φ (G.ends a).2))
    {c : Fin H.m → Fin k} (hc : StarOn P k c) : StarOn Q k (fun a => c (ψ a)) := by
  constructor
  · rintro a b ⟨hab, x, hax, hbx⟩ hQa hQb heq
    exact hc.1 (ψ a) (ψ b) ⟨fun h => hab (hψ a b hQa hQb h), φ x, embed_inc φ ψ hj hQa hax,
      embed_inc φ ψ hj hQb hbx⟩ (hP a hQa) (hP b hQb) heq
  · intro w h1 h2 h3 h4 hbic
    have i10 := w.inc_e1_v0
    have i11 := w.inc_e1_v1
    have i21 := w.inc_e2_v1
    have i22 := w.inc_e2_v2
    have i32 := w.inc_e3_v2
    have i33 := w.inc_e3_v3
    have i43 := w.inc_e4_v3
    have i44 := w.inc_e4_v4
    let w' : H.Walk4 :=
      { v0 := φ w.v0, v1 := φ w.v1, v2 := φ w.v2, v3 := φ w.v3, v4 := φ w.v4
        e1 := ψ w.e1, e2 := ψ w.e2, e3 := ψ w.e3, e4 := ψ w.e4
        h1 := embed_joins φ ψ hj h1 w.h1
        h2 := embed_joins φ ψ hj h2 w.h2
        h3 := embed_joins φ ψ hj h3 w.h3
        h4 := embed_joins φ ψ hj h4 w.h4
        d01 := fun h => w.d01 (hφ _ _ _ _ h1 h1 i10 i11 h)
        d02 := fun h => w.d02 (hφ _ _ _ _ h1 h2 i10 i22 h)
        d03 := fun h => w.d03 (hφ _ _ _ _ h1 h3 i10 i33 h)
        d12 := fun h => w.d12 (hφ _ _ _ _ h1 h2 i11 i22 h)
        d13 := fun h => w.d13 (hφ _ _ _ _ h1 h3 i11 i33 h)
        d14 := fun h => w.d14 (hφ _ _ _ _ h1 h4 i11 i44 h)
        d23 := fun h => w.d23 (hφ _ _ _ _ h2 h3 i22 i33 h)
        d24 := fun h => w.d24 (hφ _ _ _ _ h2 h4 i22 i44 h)
        d34 := fun h => w.d34 (hφ _ _ _ _ h3 h4 i33 i44 h) }
    exact hc.2 w' (hP _ h1) (hP _ h2) (hP _ h3) (hP _ h4) hbic

end embed

end MGraph


/-! ===================== part 2 ===================== -/


namespace MGraph

/-! ## Adding one edge `u w` -/

/-- `G` with one new edge (index `G.m`) joining `u` and `w` -/
def addEdge (G : MGraph) (u w : Fin G.n) : MGraph where
  n := G.n
  m := G.m + 1
  ends := fun i => if h : i.val < G.m then G.ends ⟨i.val, h⟩ else (u, w)

variable {G : MGraph}

theorem ne_of_joins (hloop : Loopless G) {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : x ≠ y := by
  intro hxy
  apply hloop f
  rcases h with h | h <;> rw [h, hxy]

section addEdge
variable {u w : Fin G.n}

theorem addEdge_ends_old (d : Fin G.m) :
    (addEdge G u w).ends (Fin.castSucc d) = G.ends d := by
  simp [addEdge]

theorem addEdge_ends_new : (addEdge G u w).ends (Fin.last G.m) = (u, w) := by
  simp [addEdge]

theorem addEdge_joins_old {d : Fin G.m} {x y : Fin G.n} :
    (addEdge G u w).Joins (Fin.castSucc d) x y ↔ G.Joins d x y := by
  unfold Joins; rw [addEdge_ends_old] <;> exact Iff.rfl

theorem addEdge_inc_old {d : Fin G.m} {x : Fin G.n} :
    (addEdge G u w).Inc (Fin.castSucc d) x ↔ G.Inc d x := by
  unfold Inc; rw [addEdge_ends_old] <;> exact Iff.rfl

theorem addEdge_joins_new : (addEdge G u w).Joins (Fin.last G.m) u w := Or.inl addEdge_ends_new

theorem addEdge_inc_new {x : Fin G.n} : (addEdge G u w).Inc (Fin.last G.m) x ↔ x = u ∨ x = w := by
  unfold Inc; rw [addEdge_ends_new]
  exact ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

theorem addEdge_cases (i : Fin (addEdge G u w).m) : i = Fin.last G.m ∨ ∃ d : Fin G.m, i = Fin.castSucc d := by
  by_cases h : i.val < G.m
  · exact Or.inr ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · refine Or.inl (Fin.ext ?_)
    have := i.isLt
    show i.val = G.m
    have : i.val < G.m + 1 := this
    omega

theorem addEdge_loopless (hloop : Loopless G) (huw : u ≠ w) : Loopless (addEdge G u w) := by
  intro i
  rcases addEdge_cases i with rfl | ⟨d, rfl⟩
  · rw [addEdge_ends_new]; exact huw
  · rw [addEdge_ends_old]; exact hloop d

end addEdge

/-- at most three edges of `Q` at a vertex (in a subcubic multigraph), one of them prescribed -/
theorem at_most_three (hsub : Subcubic G) (Q : Fin G.m → Prop) (v : Fin G.n) (f : Fin G.m) (hf : G.Inc f v) :
    ∃ a b, ∀ d, Q d → G.Inc d v → d = f ∨ d = a ∨ d = b := by
  classical
  by_cases h2 : ∃ a, Q a ∧ G.Inc a v ∧ a ≠ f
  · obtain ⟨a, _, hav, haf⟩ := h2
    by_cases h3 : ∃ b, Q b ∧ G.Inc b v ∧ b ≠ f ∧ b ≠ a
    · obtain ⟨b, _, hbv, hbf, hba⟩ := h3
      refine ⟨a, b, fun d _ hdv => ?_⟩
      apply Classical.byContradiction
      intro hd
      simp only [not_or] at hd
      exact hsub v f a b d hf hav hbv hdv (Ne.symm haf) (Ne.symm hbf) (fun h => hd.1 h.symm) (Ne.symm hba)
        (fun h => hd.2.1 h.symm) (fun h => hd.2.2 h.symm)
    · refine ⟨a, a, fun d hQd hdv => ?_⟩
      apply Classical.byContradiction
      intro hd
      simp only [not_or] at hd
      exact h3 ⟨d, hQd, hdv, hd.1, hd.2.1⟩
  · refine ⟨f, f, fun d hQd hdv => ?_⟩
    apply Classical.byContradiction
    intro hd
    simp only [not_or] at hd
    exact h2 ⟨d, hQd, hdv, hd.1⟩

/-! ## The hole lemma, formally

`y` is a vertex of `Q` whose `Q`-edges are `f1 = yu`, `f2 = yw` and possibly one pendant edge `yl` (`l` carries no
other edge of `Q`).  `P2` is `Q` minus the edges at `y` plus the new edge `g = uw` of `addEdge G u w` (the suppression
of `y`).  A star 6-colouring of `P2` with a hole `β` at `w` gives a star 6-colouring of `Q`:
`f1 ↦ c(g)`, `f2 ↦ β`, pendant `↦ γ`. -/

/-- the suppressed edge set: `Q` minus the edges at `y`, plus the new edge -/
def supp (Q : Fin G.m → Prop) (y : Fin G.n) (u w : Fin G.n) : Fin (addEdge G u w).m → Prop :=
  fun i => i = Fin.last G.m ∨ ∃ d, i = Fin.castSucc d ∧ Q d ∧ ¬ G.Inc d y

section Wrev
variable (w : G.Walk4)
theorem rev_e1 : w.reverse.e1 = w.e4 := rfl
theorem rev_e2 : w.reverse.e2 = w.e3 := rfl
theorem rev_e3 : w.reverse.e3 = w.e2 := rfl
theorem rev_e4 : w.reverse.e4 = w.e1 := rfl
theorem bicol_rev {k : Nat} {c : Fin G.m → Fin k} (h : Bicol c w) : Bicol c w.reverse := ⟨h.2.symm, h.1.symm⟩
end Wrev

theorem hole_extend (hsub : Subcubic G) (hloop : Loopless G) {Q : Fin G.m → Prop}
    {y u w l : Fin G.n} {f1 f2 : Fin G.m} (hf1 : G.Joins f1 y u) (hf2 : G.Joins f2 y w) (huw : u ≠ w)
    (hQ1 : Q f1) (hQ2 : Q f2)
    (hy : ∀ d, Q d → G.Inc d y → d = f1 ∨ d = f2 ∨ G.Joins d y l)
    (hl : ∀ d d', Q d → G.Joins d y l → Q d' → G.Inc d' l → d' = d)
    (hlu : l ≠ u) (hlw : l ≠ w)
    (c2 : Fin (addEdge G u w).m → Fin 6) (β : Fin 6)
    (hc2 : StarOn (supp Q y u w) 6 c2)
    (hhole : HoleOn (supp Q y u w) c2 w β) :
    Colourable Q 6 := by
  classical
  have hyu : y ≠ u := ne_of_joins hloop hf1
  have hyw : y ≠ w := ne_of_joins hloop hf2
  have hf12 : f1 ≠ f2 := by
    intro h
    rw [h] at hf1
    exact huw (joins_other hf2 hf1 (Ne.symm hyw) |>.symm |> fun h' => h'.symm)
  -- which `Q`-edges meet `y`
  have hnoty_u : ∀ d, Q d → G.Inc d u → d ≠ f1 → ¬ G.Inc d y := by
    intro d hd hdu hdf1 hdy
    rcases hy d hd hdy with h | h | h
    · exact hdf1 h
    · rw [h] at hdu
      rcases inc_of_joins hf2 hdu with h' | h'
      · exact hyu h'.symm
      · exact huw h'
    · rcases inc_of_joins h hdu with h' | h'
      · exact hyu h'.symm
      · exact hlu h'.symm
  have hnoty_w : ∀ d, Q d → G.Inc d w → d ≠ f2 → ¬ G.Inc d y := by
    intro d hd hdw hdf2 hdy
    rcases hy d hd hdy with h | h | h
    · rw [h] at hdw
      rcases inc_of_joins hf1 hdw with h' | h'
      · exact hyw h'.symm
      · exact huw h'.symm
    · exact hdf2 h
    · rcases inc_of_joins h hdw with h' | h'
      · exact hyw h'.symm
      · exact hlw h'.symm
  have hP2 : ∀ d, Q d → ¬ G.Inc d y → supp Q y u w (Fin.castSucc d) := fun d hd hdy => Or.inr ⟨d, rfl, hd, hdy⟩
  have hP2g : supp Q y u w (Fin.last G.m) := Or.inl rfl
  have hf1y : G.Inc f1 y := joins_inc_left hf1
  have hf2y : G.Inc f2 y := joins_inc_left hf2
  -- the choice of γ
  obtain ⟨a, b, hab⟩ := at_most_three hsub Q u f1 (joins_inc_right hf1)
  obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, -⟩ :=
    pigeon5 (c2 (Fin.last G.m)) β (c2 (Fin.castSucc a)) (c2 (Fin.castSucc b)) β
  let c : Fin G.m → Fin 6 := fun d =>
    if d = f1 then c2 (Fin.last G.m) else if d = f2 then β else if G.Inc d y then γ else c2 (Fin.castSucc d)
  have hc1 : c f1 = c2 (Fin.last G.m) := by simp [c]
  have hcf2 : c f2 = β := by simp [c, Ne.symm hf12]
  have hcp : ∀ d, d ≠ f1 → d ≠ f2 → G.Inc d y → c d = γ := by
    intro d h1 h2 h3; simp [c, h1, h2, h3]
  have hcold : ∀ d, ¬ G.Inc d y → c d = c2 (Fin.castSucc d) := by
    intro d hd
    have h1 : d ≠ f1 := fun h => hd (h ▸ hf1y)
    have h2 : d ≠ f2 := fun h => hd (h ▸ hf2y)
    simp [c, h1, h2, hd]
  -- the facts about `c2` used below
  have F1 : c2 (Fin.last G.m) ≠ β :=
    hhole _ w hP2g (addEdge_inc_new.2 (Or.inr rfl)) (Or.inl rfl)
  have F2 : ∀ d, Q d → G.Inc d u → d ≠ f1 → c2 (Fin.castSucc d) ≠ β := by
    intro d hd hdu hdf1
    exact hhole _ u (hP2 d hd (hnoty_u d hd hdu hdf1)) (addEdge_inc_old.2 hdu)
      (Or.inr ⟨Fin.last G.m, hP2g, joins_symm addEdge_joins_new⟩)
  have F3 : ∀ d, Q d → G.Inc d u → d ≠ f1 → c2 (Fin.castSucc d) ≠ c2 (Fin.last G.m) := by
    intro d hd hdu hdf1
    exact hc2.1 _ _ ⟨castSucc_ne_last' d, u, addEdge_inc_old.2 hdu, addEdge_inc_new.2 (Or.inl rfl)⟩
      (hP2 d hd (hnoty_u d hd hdu hdf1)) hP2g
  have F4 : ∀ d, Q d → G.Inc d u → d ≠ f1 → c2 (Fin.castSucc d) ≠ γ := by
    intro d hd hdu hdf1
    rcases hab d hd hdu with h | h | h
    · exact absurd h hdf1
    · rw [h]; exact Ne.symm hγ3
    · rw [h]; exact Ne.symm hγ4
  have F5 : ∀ d, Q d → G.Inc d w → d ≠ f2 → c2 (Fin.castSucc d) ≠ β := by
    intro d hd hdw hdf2
    exact hhole _ w (hP2 d hd (hnoty_w d hd hdw hdf2)) (addEdge_inc_old.2 hdw) (Or.inl rfl)
  have F5' : ∀ d' d v, Q d' → ¬ G.Inc d' y → G.Joins d' w v → Q d → ¬ G.Inc d y → G.Inc d v →
      c2 (Fin.castSucc d) ≠ β := by
    intro d' d v hd' hd'y hj hd hdy hdv
    exact hhole _ v (hP2 d hd hdy) (addEdge_inc_old.2 hdv) (Or.inr ⟨_, hP2 d' hd' hd'y, addEdge_joins_old.2 hj⟩)
  -- edges at `y`
  have hclass : ∀ d, Q d → G.Inc d y →
      (d = f1 ∧ c d = c2 (Fin.last G.m)) ∨ (d = f2 ∧ c d = β) ∨
        (G.Joins d y l ∧ d ≠ f1 ∧ d ≠ f2 ∧ c d = γ) := by
    intro d hd hdy
    by_cases h1 : d = f1
    · exact Or.inl ⟨h1, h1 ▸ hc1⟩
    by_cases h2 : d = f2
    · exact Or.inr (Or.inl ⟨h2, h2 ▸ hcf2⟩)
    rcases hy d hd hdy with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact Or.inr (Or.inr ⟨h, h1, h2, hcp d h1 h2 hdy⟩)
  -- properness
  have mixed : ∀ a' b' x, Q a' → Q b' → G.Inc a' y → ¬ G.Inc b' y → G.Inc a' x → G.Inc b' x → c a' ≠ c b' := by
    intro a' b' x hQa hQb hay hby hax hbx
    have hxy : x ≠ y := fun h => hby (h ▸ hbx)
    have hja : G.Joins a' y x := joins_of_inc_ne hay hax (Ne.symm hxy)
    rw [hcold b' hby]
    rcases hclass a' hQa hay with ⟨rfl, hca⟩ | ⟨rfl, hca⟩ | ⟨hjl, _, _, _⟩
    · have hx : x = u := joins_other hf1 hja (Ne.symm hyu)
      rw [hca]
      have hb1 : b' ≠ a' := fun h => hby (h ▸ hay)
      exact Ne.symm (F3 b' hQb (hx ▸ hbx) hb1)
    · have hx : x = w := joins_other hf2 hja (Ne.symm hyw)
      rw [hca]
      have hb2 : b' ≠ a' := fun h => hby (h ▸ hay)
      exact Ne.symm (F5 b' hQb (hx ▸ hbx) hb2)
    · have hyl : y ≠ l := ne_of_joins hloop hjl
      have hx : x = l := joins_other hjl hja (Ne.symm hyl)
      have := hl a' b' hQa hjl hQb (hx ▸ hbx)
      exact absurd (this ▸ hay) hby
  have proper : ∀ a' b', G.Adj a' b' → Q a' → Q b' → c a' ≠ c b' := by
    rintro a' b' ⟨hab', x, hax, hbx⟩ hQa hQb
    by_cases hay : G.Inc a' y <;> by_cases hby : G.Inc b' y
    · rcases hclass a' hQa hay with ⟨ha, hca⟩ | ⟨ha, hca⟩ | ⟨hja, ha1, ha2, hca⟩ <;>
        rcases hclass b' hQb hby with ⟨hb, hcb⟩ | ⟨hb, hcb⟩ | ⟨hjb, hb1, hb2, hcb⟩ <;>
        rw [hca, hcb]
      · exact absurd (ha.trans hb.symm) hab'
      · exact F1
      · exact Ne.symm hγ1
      · exact Ne.symm F1
      · exact absurd (ha.trans hb.symm) hab'
      · exact Ne.symm hγ2
      · exact hγ1
      · exact hγ2
      · exact absurd (hl a' b' hQa hja hQb (joins_inc_right hjb)).symm hab'
    · exact mixed a' b' x hQa hQb hay hby hax hbx
    · exact Ne.symm (mixed b' a' x hQb hQa hby hay hbx hax)
    · rw [hcold a' hay, hcold b' hby]
      exact hc2.1 _ _ ⟨fun h => hab' (Fin.castSucc_inj.1 h), x, addEdge_inc_old.2 hax, addEdge_inc_old.2 hbx⟩
        (hP2 a' hQa hay) (hP2 b' hQb hby)
  -- step A: `f2` is not on a bicoloured walk
  have lemA : ∀ (e' e'' : Fin G.m) (v1 v2 : Fin G.n), Q e' → Q e'' → G.Inc f2 v1 → G.Joins e' v1 v2 →
      e' ≠ f2 → e'' ≠ e' → e'' ≠ f2 → G.Inc e'' v2 → v1 ≠ v2 → c e'' ≠ β := by
    intro e' e'' v1 v2 hQ' hQ'' hf2v1 hj' he'f2 he''e' he''f2 he''v2 hv12
    rcases inc_of_joins hf2 hf2v1 with hv1 | hv1
    · -- v1 = y
      rw [hv1] at hj' hv12
      rcases hy e' hQ' (joins_inc_left hj') with h | h | h
      · rw [h] at hj' he''e'
        have hv2 : v2 = u := joins_other hf1 hj' (Ne.symm hyu)
        rw [hv2] at he''v2
        rw [hcold e'' (hnoty_u e'' hQ'' he''v2 he''e')]
        exact F2 e'' hQ'' he''v2 he''e'
      · exact absurd h he'f2
      · have hyl : y ≠ l := ne_of_joins hloop h
        have hv2 : v2 = l := joins_other h hj' (Ne.symm hyl)
        rw [hv2] at he''v2
        exact absurd (hl e' e'' hQ' h hQ'' he''v2) he''e'
    · -- v1 = w
      rw [hv1] at hj'
      have hny' : ¬ G.Inc e' y := hnoty_w e' hQ' (joins_inc_left hj') he'f2
      by_cases he''f1 : e'' = f1
      · rw [he''f1, hc1]; exact F1
      by_cases he''y : G.Inc e'' y
      · rw [hcp e'' he''f1 he''f2 he''y]; exact hγ2
      · rw [hcold e'' he''y]
        exact F5' e' e'' v2 hQ' hny' hj' hQ'' he''y he''v2
  have noF2_12 : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' →
      w'.e1 ≠ f2 ∧ w'.e2 ≠ f2 := by
    intro w' h1 h2 h3 h4 hb
    constructor
    · intro he
      have := lemA w'.e2 w'.e3 w'.v1 w'.v2 h2 h3 (he ▸ w'.inc_e1_v1) w'.h2 (he ▸ (Ne.symm w'.e1_ne_e2))
        (Ne.symm w'.e2_ne_e3) (he ▸ (Ne.symm w'.e1_ne_e3)) w'.inc_e3_v2 w'.d12
      apply this
      rw [← hb.1, he, hcf2]
    · intro he
      have := lemA w'.e3 w'.e4 w'.v2 w'.v3 h3 h4 (he ▸ w'.inc_e2_v2) w'.h3 (he ▸ (Ne.symm w'.e2_ne_e3))
        (Ne.symm w'.e3_ne_e4) (he ▸ (Ne.symm w'.e2_ne_e4)) w'.inc_e4_v3 w'.d23
      apply this
      rw [← hb.2, he, hcf2]
  have noF2 : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' →
      w'.e1 ≠ f2 ∧ w'.e2 ≠ f2 ∧ w'.e3 ≠ f2 ∧ w'.e4 ≠ f2 := by
    intro w' h1 h2 h3 h4 hb
    have a1 := noF2_12 w' h1 h2 h3 h4 hb
    have a2 := noF2_12 w'.reverse h4 h3 h2 h1 (bicol_rev w' hb)
    exact ⟨a1.1, a1.2, a2.2, a2.1⟩
  -- step B: no pendant edge on a bicoloured walk
  have noP_12 : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' →
      ¬ G.Joins w'.e1 y l ∧ ¬ G.Joins w'.e2 y l := by
    intro w' h1 h2 h3 h4 hb
    have nf := noF2 w' h1 h2 h3 h4 hb
    constructor
    · intro hp
      have hyl : y ≠ l := ne_of_joins hloop hp
      rcases joins_unique hp w'.h1 with ⟨hv0, hv1⟩ | ⟨hv0, hv1⟩
      · -- v1 = l: e2 is another edge at the leaf
        exact w'.e1_ne_e2 (hl w'.e1 w'.e2 h1 hp h2 (hv1 ▸ w'.inc_e2_v1)).symm
      · -- v1 = y: e2 = f1, v2 = u, and e3 at u gets a colour ≠ γ
        have he2y : G.Inc w'.e2 y := hv0 ▸ w'.inc_e2_v1
        have hce1 : c w'.e1 = γ := by
          rcases hclass w'.e1 h1 (joins_inc_left hp) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, h⟩
          · exfalso
            rw [h] at hp
            exact hlu (joins_other hf1 hp (Ne.symm hyu))
          · exact absurd h nf.1
          · exact h
        rcases hclass w'.e2 h2 he2y with ⟨he2, _⟩ | ⟨he2, _⟩ | ⟨hj2, _, _, _⟩
        · have hj2 : G.Joins f1 y w'.v2 := he2 ▸ (hv0 ▸ w'.h2)
          have hv2 : w'.v2 = u := joins_other hf1 hj2 (Ne.symm hyu)
          have he3u : G.Inc w'.e3 u := hv2 ▸ w'.inc_e3_v2
          have he3f1 : w'.e3 ≠ f1 := he2 ▸ (Ne.symm w'.e2_ne_e3)
          have hny := hnoty_u w'.e3 h3 he3u he3f1
          have := F4 w'.e3 h3 he3u he3f1
          apply this
          rw [← hcold w'.e3 hny, ← hb.1, hce1]
        · exact absurd he2 nf.2.1
        · exact w'.e1_ne_e2 (hl w'.e1 w'.e2 h1 hp h2 (joins_inc_right hj2)).symm
    · intro hp
      rcases joins_unique hp w'.h2 with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
      · exact w'.e2_ne_e3 (hl w'.e2 w'.e3 h2 hp h3 (hv2 ▸ w'.inc_e3_v2)).symm
      · exact w'.e1_ne_e2 (hl w'.e2 w'.e1 h2 hp h1 (hv2 ▸ w'.inc_e1_v1))
  have noP : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' →
      ¬ G.Joins w'.e1 y l ∧ ¬ G.Joins w'.e2 y l ∧ ¬ G.Joins w'.e3 y l ∧ ¬ G.Joins w'.e4 y l := by
    intro w' h1 h2 h3 h4 hb
    have a1 := noP_12 w' h1 h2 h3 h4 hb
    have a2 := noP_12 w'.reverse h4 h3 h2 h1 (bicol_rev w' hb)
    exact ⟨a1.1, a1.2, a2.2, a2.1⟩
  -- an edge of a bicoloured walk meeting `y` is `f1`
  have atY : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' →
      ∀ e, (e = w'.e1 ∨ e = w'.e2 ∨ e = w'.e3 ∨ e = w'.e4) → G.Inc e y → e = f1 := by
    intro w' h1 h2 h3 h4 hb e he hey
    have nf := noF2 w' h1 h2 h3 h4 hb
    have np := noP w' h1 h2 h3 h4 hb
    have hQe : Q e := by rcases he with rfl | rfl | rfl | rfl <;> assumption
    rcases hy e hQe hey with h | h | h
    · exact h
    · exfalso
      rcases he with rfl | rfl | rfl | rfl
      · exact nf.1 h
      · exact nf.2.1 h
      · exact nf.2.2.1 h
      · exact nf.2.2.2 h
    · exfalso
      rcases he with rfl | rfl | rfl | rfl
      · exact np.1 h
      · exact np.2.1 h
      · exact np.2.2.1 h
      · exact np.2.2.2 h
  -- step C, first case: `f1 = e1`
  have caseE1 : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' → w'.e1 = f1 → False := by
    intro w' h1 h2 h3 h4 hb he1
    have ay := atY w' h1 h2 h3 h4 hb
    have n2 : ¬ G.Inc w'.e2 y := fun h => w'.e1_ne_e2 (he1.trans (ay _ (Or.inr (Or.inl rfl)) h).symm)
    have n3 : ¬ G.Inc w'.e3 y := fun h => w'.e1_ne_e3 (he1.trans (ay _ (Or.inr (Or.inr (Or.inl rfl))) h).symm)
    have n4 : ¬ G.Inc w'.e4 y := fun h => w'.e1_ne_e4 (he1.trans (ay _ (Or.inr (Or.inr (Or.inr rfl))) h).symm)
    have hj1 : G.Joins f1 w'.v0 w'.v1 := he1 ▸ w'.h1
    rcases joins_unique hf1 hj1 with ⟨hv0, hv1⟩ | ⟨hv0, hv1⟩
    · -- v0 = y, v1 = u
      have hc3 : c2 (Fin.castSucc w'.e3) = c2 (Fin.last G.m) := by
        rw [← hcold _ n3, ← hb.1, he1, hc1]
      have hc24 : c2 (Fin.castSucc w'.e2) = c2 (Fin.castSucc w'.e4) := by
        rw [← hcold _ n2, ← hcold _ n4, hb.2]
      by_cases hw2 : w = w'.v2
      · exact hc2.1 _ _ ⟨castSucc_ne_last' _, w, addEdge_inc_old.2 (hw2 ▸ w'.inc_e3_v2),
          addEdge_inc_new.2 (Or.inr rfl)⟩ (hP2 _ h3 n3) hP2g hc3
      by_cases hw3 : w = w'.v3
      · exact hc2.1 _ _ ⟨castSucc_ne_last' _, w, addEdge_inc_old.2 (hw3 ▸ w'.inc_e3_v3),
          addEdge_inc_new.2 (Or.inr rfl)⟩ (hP2 _ h3 n3) hP2g hc3
      -- the walk w, u, v2, v3, v4 in `addEdge G u w`
      let w2 : (addEdge G u w).Walk4 :=
        { v0 := w, v1 := u, v2 := w'.v2, v3 := w'.v3, v4 := w'.v4
          e1 := Fin.last G.m, e2 := Fin.castSucc w'.e2, e3 := Fin.castSucc w'.e3, e4 := Fin.castSucc w'.e4
          h1 := joins_symm addEdge_joins_new
          h2 := addEdge_joins_old.2 (hv1 ▸ w'.h2)
          h3 := addEdge_joins_old.2 w'.h3
          h4 := addEdge_joins_old.2 w'.h4
          d01 := Ne.symm huw
          d02 := hw2
          d03 := hw3
          d12 := hv1 ▸ w'.d12
          d13 := hv1 ▸ w'.d13
          d14 := hv1 ▸ w'.d14
          d23 := w'.d23
          d24 := w'.d24
          d34 := w'.d34 }
      exact hc2.2 w2 hP2g (hP2 _ h2 n2) (hP2 _ h3 n3) (hP2 _ h4 n4) ⟨hc3.symm, hc24⟩
    · -- v1 = y: e2 would be a second walk edge at y
      exact n2 (hv0 ▸ w'.inc_e2_v1)
  -- step C, second case: `f1 = e2`
  have caseE2 : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → Bicol c w' → w'.e2 = f1 → False := by
    intro w' h1 h2 h3 h4 hb he2
    have ay := atY w' h1 h2 h3 h4 hb
    have hj2 : G.Joins f1 w'.v1 w'.v2 := he2 ▸ w'.h2
    rcases joins_unique hf1 hj2 with ⟨hv1, _⟩ | ⟨hv2, _⟩
    · exact w'.e1_ne_e2 ((ay _ (Or.inl rfl) (hv1 ▸ w'.inc_e1_v1)).trans he2.symm)
    · exact w'.e2_ne_e3 (he2.trans (ay _ (Or.inr (Or.inr (Or.inl rfl))) (hv2 ▸ w'.inc_e3_v2)).symm)
  -- all walks
  have walks : ∀ w' : G.Walk4, Q w'.e1 → Q w'.e2 → Q w'.e3 → Q w'.e4 → ¬ Bicol c w' := by
    intro w' h1 h2 h3 h4 hb
    by_cases e1f : w'.e1 = f1
    · exact caseE1 w' h1 h2 h3 h4 hb e1f
    by_cases e2f : w'.e2 = f1
    · exact caseE2 w' h1 h2 h3 h4 hb e2f
    by_cases e3f : w'.e3 = f1
    · exact caseE2 w'.reverse h4 h3 h2 h1 (bicol_rev w' hb) e3f
    by_cases e4f : w'.e4 = f1
    · exact caseE1 w'.reverse h4 h3 h2 h1 (bicol_rev w' hb) e4f
    -- no edge of the walk meets `y`: it lives in `supp`
    have ay := atY w' h1 h2 h3 h4 hb
    have n1 : ¬ G.Inc w'.e1 y := fun h => e1f (ay _ (Or.inl rfl) h)
    have n2 : ¬ G.Inc w'.e2 y := fun h => e2f (ay _ (Or.inr (Or.inl rfl)) h)
    have n3 : ¬ G.Inc w'.e3 y := fun h => e3f (ay _ (Or.inr (Or.inr (Or.inl rfl))) h)
    have n4 : ¬ G.Inc w'.e4 y := fun h => e4f (ay _ (Or.inr (Or.inr (Or.inr rfl))) h)
    let w2 : (addEdge G u w).Walk4 :=
      { v0 := w'.v0, v1 := w'.v1, v2 := w'.v2, v3 := w'.v3, v4 := w'.v4
        e1 := Fin.castSucc w'.e1, e2 := Fin.castSucc w'.e2, e3 := Fin.castSucc w'.e3, e4 := Fin.castSucc w'.e4
        h1 := addEdge_joins_old.2 w'.h1
        h2 := addEdge_joins_old.2 w'.h2
        h3 := addEdge_joins_old.2 w'.h3
        h4 := addEdge_joins_old.2 w'.h4
        d01 := w'.d01, d02 := w'.d02, d03 := w'.d03, d12 := w'.d12, d13 := w'.d13
        d14 := w'.d14, d23 := w'.d23, d24 := w'.d24, d34 := w'.d34 }
    refine hc2.2 w2 (hP2 _ h1 n1) (hP2 _ h2 n2) (hP2 _ h3 n3) (hP2 _ h4 n4) ⟨?_, ?_⟩
    · show c2 (Fin.castSucc w'.e1) = c2 (Fin.castSucc w'.e3)
      rw [← hcold _ n1, ← hcold _ n3]; exact hb.1
    · show c2 (Fin.castSucc w'.e2) = c2 (Fin.castSucc w'.e4)
      rw [← hcold _ n2, ← hcold _ n4]; exact hb.2
  exact ⟨c, fun a' b' hab' hQa hQb => proper a' b' hab' hQa hQb, fun w' h1 h2 h3 h4 => walks w' h1 h2 h3 h4⟩

end MGraph


/-! ===================== part 3 ===================== -/


namespace MGraph

/-! ## The doubled multigraph

`dbl G` has two copies of `G` (vertices `vo x`, `vc x`; edges `eo f`, `ec f`) and, for every vertex `x`, two
parallel "rung" edges `ea x`, `eb x` joining `vo x` and `vc x`. -/

def dbl (G : MGraph) : MGraph where
  n := G.n + G.n
  m := (G.m + G.m) + (G.n + G.n)
  ends := Fin.addCases (motive := fun _ => Fin (G.n + G.n) × Fin (G.n + G.n))
    (Fin.addCases (motive := fun _ => Fin (G.n + G.n) × Fin (G.n + G.n))
      (fun f => (Fin.castAdd G.n (G.ends f).1, Fin.castAdd G.n (G.ends f).2))
      (fun f => (Fin.natAdd G.n (G.ends f).1, Fin.natAdd G.n (G.ends f).2)))
    (Fin.addCases (motive := fun _ => Fin (G.n + G.n) × Fin (G.n + G.n))
      (fun v => (Fin.castAdd G.n v, Fin.natAdd G.n v))
      (fun v => (Fin.castAdd G.n v, Fin.natAdd G.n v)))

variable {G : MGraph}

namespace dbl

def vo (x : Fin G.n) : Fin (dbl G).n := Fin.castAdd G.n x
def vc (x : Fin G.n) : Fin (dbl G).n := Fin.natAdd G.n x
def eo (f : Fin G.m) : Fin (dbl G).m := Fin.castAdd (G.n + G.n) (Fin.castAdd G.m f)
def ec (f : Fin G.m) : Fin (dbl G).m := Fin.castAdd (G.n + G.n) (Fin.natAdd G.m f)
def ea (x : Fin G.n) : Fin (dbl G).m := Fin.natAdd (G.m + G.m) (Fin.castAdd G.n x)
def eb (x : Fin G.n) : Fin (dbl G).m := Fin.natAdd (G.m + G.m) (Fin.natAdd G.n x)

theorem ends_eo (f : Fin G.m) : (dbl G).ends (eo f) = (vo (G.ends f).1, vo (G.ends f).2) := by
  simp only [dbl, eo, vo, Fin.addCases_left, Fin.addCases_right]
theorem ends_ec (f : Fin G.m) : (dbl G).ends (ec f) = (vc (G.ends f).1, vc (G.ends f).2) := by
  simp only [dbl, ec, vc, Fin.addCases_left, Fin.addCases_right]
theorem ends_ea (x : Fin G.n) : (dbl G).ends (ea x) = (vo x, vc x) := by
  simp only [dbl, ea, vo, vc, Fin.addCases_left, Fin.addCases_right]
theorem ends_eb (x : Fin G.n) : (dbl G).ends (eb x) = (vo x, vc x) := by
  simp only [dbl, eb, vo, vc, Fin.addCases_left, Fin.addCases_right]

theorem vo_inj {x y : Fin G.n} (h : vo x = vo y) : x = y := by
  have := congrArg Fin.val h; simp [vo] at this; exact Fin.ext this
theorem vc_inj {x y : Fin G.n} (h : vc x = vc y) : x = y := by
  have := congrArg Fin.val h; simp [vc] at this; exact Fin.ext this
theorem vo_ne_vc (x y : Fin G.n) : vo x ≠ vc y := by
  intro h; have := congrArg Fin.val h; simp [vo, vc] at this; have := x.isLt; omega

theorem eo_inj {f g : Fin G.m} (h : eo f = eo g) : f = g := by
  have := congrArg Fin.val h; simp [eo] at this; exact Fin.ext this
theorem ec_inj {f g : Fin G.m} (h : ec f = ec g) : f = g := by
  have := congrArg Fin.val h; simp [ec] at this; exact Fin.ext this
theorem ea_inj {x y : Fin G.n} (h : ea x = ea y) : x = y := by
  have := congrArg Fin.val h; simp [ea] at this; exact Fin.ext this
theorem eb_inj {x y : Fin G.n} (h : eb x = eb y) : x = y := by
  have := congrArg Fin.val h; simp [eb] at this; exact Fin.ext this
theorem eo_ne_ec (f g : Fin G.m) : eo f ≠ ec g := by
  intro h; have := congrArg Fin.val h; simp [eo, ec] at this; have := f.isLt; omega
theorem eo_ne_ea (f : Fin G.m) (x : Fin G.n) : eo f ≠ ea x := by
  intro h; have := congrArg Fin.val h; simp [eo, ea] at this; have := f.isLt; omega
theorem eo_ne_eb (f : Fin G.m) (x : Fin G.n) : eo f ≠ eb x := by
  intro h; have := congrArg Fin.val h; simp [eo, eb] at this; have := f.isLt; omega
theorem ec_ne_ea (f : Fin G.m) (x : Fin G.n) : ec f ≠ ea x := by
  intro h; have := congrArg Fin.val h; simp [ec, ea] at this; have := f.isLt; omega
theorem ec_ne_eb (f : Fin G.m) (x : Fin G.n) : ec f ≠ eb x := by
  intro h; have := congrArg Fin.val h; simp [ec, eb] at this; have := f.isLt; omega
theorem ea_ne_eb (x y : Fin G.n) : ea x ≠ eb y := by
  intro h; have := congrArg Fin.val h; simp [ea, eb] at this; have := x.isLt; omega

theorem vcases (z : Fin (dbl G).n) : (∃ x, z = vo x) ∨ (∃ x, z = vc x) := by
  refine Fin.addCases (motive := fun z => (∃ x, z = vo x) ∨ (∃ x, z = vc x)) (fun x => ?_) (fun x => ?_) z
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

theorem ecases (i : Fin (dbl G).m) :
    (∃ f, i = eo f) ∨ (∃ f, i = ec f) ∨ (∃ x, i = ea x) ∨ (∃ x, i = eb x) := by
  refine Fin.addCases (motive := fun i => (∃ f, i = eo f) ∨ (∃ f, i = ec f) ∨ (∃ x, i = ea x) ∨ (∃ x, i = eb x))
    (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (motive := fun j => (∃ f, Fin.castAdd (G.n + G.n) j = eo f) ∨
        (∃ f, Fin.castAdd (G.n + G.n) j = ec f) ∨ (∃ x, Fin.castAdd (G.n + G.n) j = ea x) ∨
        (∃ x, Fin.castAdd (G.n + G.n) j = eb x)) (fun f => ?_) (fun f => ?_) j
    · exact Or.inl ⟨f, rfl⟩
    · exact Or.inr (Or.inl ⟨f, rfl⟩)
  · refine Fin.addCases (motive := fun j => (∃ f, Fin.natAdd (G.m + G.m) j = eo f) ∨
        (∃ f, Fin.natAdd (G.m + G.m) j = ec f) ∨ (∃ x, Fin.natAdd (G.m + G.m) j = ea x) ∨
        (∃ x, Fin.natAdd (G.m + G.m) j = eb x)) (fun x => ?_) (fun x => ?_) j
    · exact Or.inr (Or.inr (Or.inl ⟨x, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x, rfl⟩))

/-! incidences -/

theorem inc_eo_vo {f : Fin G.m} {x : Fin G.n} : (dbl G).Inc (eo f) (vo x) ↔ G.Inc f x := by
  unfold Inc; rw [ends_eo]
  constructor
  · rintro (h | h)
    · exact Or.inl (vo_inj h)
    · exact Or.inr (vo_inj h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
theorem not_inc_eo_vc {f : Fin G.m} {x : Fin G.n} : ¬ (dbl G).Inc (eo f) (vc x) := by
  unfold Inc; rw [ends_eo]
  rintro (h | h) <;> exact vo_ne_vc _ _ h
theorem inc_ec_vc {f : Fin G.m} {x : Fin G.n} : (dbl G).Inc (ec f) (vc x) ↔ G.Inc f x := by
  unfold Inc; rw [ends_ec]
  constructor
  · rintro (h | h)
    · exact Or.inl (vc_inj h)
    · exact Or.inr (vc_inj h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
theorem not_inc_ec_vo {f : Fin G.m} {x : Fin G.n} : ¬ (dbl G).Inc (ec f) (vo x) := by
  unfold Inc; rw [ends_ec]
  rintro (h | h) <;> exact vo_ne_vc _ _ h.symm
theorem inc_ea_vo {v x : Fin G.n} : (dbl G).Inc (ea v) (vo x) ↔ v = x := by
  unfold Inc; rw [ends_ea]
  constructor
  · rintro (h | h)
    · exact vo_inj h
    · exact absurd h.symm (vo_ne_vc _ _)
  · intro h; exact Or.inl (by rw [h])
theorem inc_ea_vc {v x : Fin G.n} : (dbl G).Inc (ea v) (vc x) ↔ v = x := by
  unfold Inc; rw [ends_ea]
  constructor
  · rintro (h | h)
    · exact absurd h (vo_ne_vc _ _)
    · exact vc_inj h
  · intro h; exact Or.inr (by rw [h])
theorem inc_eb_vo {v x : Fin G.n} : (dbl G).Inc (eb v) (vo x) ↔ v = x := by
  unfold Inc; rw [ends_eb]
  constructor
  · rintro (h | h)
    · exact vo_inj h
    · exact absurd h.symm (vo_ne_vc _ _)
  · intro h; exact Or.inl (by rw [h])
theorem inc_eb_vc {v x : Fin G.n} : (dbl G).Inc (eb v) (vc x) ↔ v = x := by
  unfold Inc; rw [ends_eb]
  constructor
  · rintro (h | h)
    · exact absurd h (vo_ne_vc _ _)
    · exact vc_inj h
  · intro h; exact Or.inr (by rw [h])

theorem joins_eo {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : (dbl G).Joins (eo f) (vo x) (vo y) := by
  unfold Joins; rw [ends_eo]
  rcases h with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem joins_ec {f : Fin G.m} {x y : Fin G.n} (h : G.Joins f x y) : (dbl G).Joins (ec f) (vc x) (vc y) := by
  unfold Joins; rw [ends_ec]
  rcases h with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem loopless (hloop : Loopless G) : Loopless (dbl G) := by
  intro i
  rcases ecases i with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [ends_eo]; exact fun h => hloop f (vo_inj h)
  · rw [ends_ec]; exact fun h => hloop f (vc_inj h)
  · rw [ends_ea]; exact vo_ne_vc x x
  · rw [ends_eb]; exact vo_ne_vc x x

end dbl

open dbl

/-- the doubled edge set: both copies of `Q`, one rung at every vertex of `Q`-degree one or two, a second rung at
    every vertex of `Q`-degree one -/
def dblP (Q : Fin G.m → Prop) : Fin (dbl G).m → Prop := fun i =>
  (∃ f, i = eo f ∧ Q f) ∨ (∃ f, i = ec f ∧ Q f) ∨ (∃ x, i = ea x ∧ (QDeg1 Q x ∨ QDeg2 Q x)) ∨
    (∃ x, i = eb x ∧ QDeg1 Q x)

theorem dblP_eo {Q : Fin G.m → Prop} {f : Fin G.m} : dblP Q (eo f) ↔ Q f := by
  constructor
  · rintro (⟨g, h, hg⟩ | ⟨g, h, _⟩ | ⟨x, h, _⟩ | ⟨x, h, _⟩)
    · exact (eo_inj h) ▸ hg
    · exact absurd h (eo_ne_ec _ _)
    · exact absurd h (eo_ne_ea _ _)
    · exact absurd h (eo_ne_eb _ _)
  · intro h; exact Or.inl ⟨f, rfl, h⟩
theorem dblP_ec {Q : Fin G.m → Prop} {f : Fin G.m} : dblP Q (ec f) ↔ Q f := by
  constructor
  · rintro (⟨g, h, _⟩ | ⟨g, h, hg⟩ | ⟨x, h, _⟩ | ⟨x, h, _⟩)
    · exact absurd h.symm (eo_ne_ec _ _)
    · exact (ec_inj h) ▸ hg
    · exact absurd h (ec_ne_ea _ _)
    · exact absurd h (ec_ne_eb _ _)
  · intro h; exact Or.inr (Or.inl ⟨f, rfl, h⟩)
theorem dblP_ea {Q : Fin G.m → Prop} {x : Fin G.n} : dblP Q (ea x) ↔ (QDeg1 Q x ∨ QDeg2 Q x) := by
  constructor
  · rintro (⟨g, h, _⟩ | ⟨g, h, _⟩ | ⟨y, h, hy⟩ | ⟨y, h, _⟩)
    · exact absurd h.symm (eo_ne_ea _ _)
    · exact absurd h.symm (ec_ne_ea _ _)
    · exact (ea_inj h) ▸ hy
    · exact absurd h (ea_ne_eb _ _)
  · intro h; exact Or.inr (Or.inr (Or.inl ⟨x, rfl, h⟩))
theorem dblP_eb {Q : Fin G.m → Prop} {x : Fin G.n} : dblP Q (eb x) ↔ QDeg1 Q x := by
  constructor
  · rintro (⟨g, h, _⟩ | ⟨g, h, _⟩ | ⟨y, h, _⟩ | ⟨y, h, hy⟩)
    · exact absurd h.symm (eo_ne_eb _ _)
    · exact absurd h.symm (ec_ne_eb _ _)
    · exact absurd h.symm (ea_ne_eb _ _)
    · exact (eb_inj h) ▸ hy
  · intro h; exact Or.inr (Or.inr (Or.inr ⟨x, rfl, h⟩))

/-- a vertex of positive `Q`-degree -/
theorem meets_of_deg1 {Q : Fin G.m → Prop} {x : Fin G.n} (h : QDeg1 Q x) : ∃ f, Q f ∧ G.Inc f x := by
  obtain ⟨a, ha, hax, _⟩ := h; exact ⟨a, ha, hax⟩
theorem meets_of_deg2 {Q : Fin G.m → Prop} {x : Fin G.n} (h : QDeg2 Q x) : ∃ f, Q f ∧ G.Inc f x := by
  obtain ⟨a, _, ha, _, hax, _⟩ := h; exact ⟨a, ha, hax⟩

/-- **The doubled edge set is cubic.** -/
theorem dblP_cubic (hsub : Subcubic G) (Q : Fin G.m → Prop) : CubicOn (dblP Q) := by
  intro z hz
  rcases vcases z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · -- a vertex of the first copy
    have hx : ∃ f, Q f ∧ G.Inc f x := by
      obtain ⟨i, hi, hiz⟩ := hz
      rcases ecases i with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact ⟨f, dblP_eo.1 hi, inc_eo_vo.1 hiz⟩
      · exact absurd hiz not_inc_ec_vo
      · rw [inc_ea_vo.1 hiz] at hi
        rcases dblP_ea.1 hi with h | h
        · exact meets_of_deg1 h
        · exact meets_of_deg2 h
      · rw [inc_eb_vo.1 hiz] at hi
        exact meets_of_deg1 (dblP_eb.1 hi)
    -- every edge of `dblP Q` at `vo x` is `eo f` (f at x), `ea x` or `eb x`
    have hall : ∀ i, dblP Q i → (dbl G).Inc i (vo x) →
        (∃ f, i = eo f ∧ Q f ∧ G.Inc f x) ∨ (i = ea x ∧ (QDeg1 Q x ∨ QDeg2 Q x)) ∨ (i = eb x ∧ QDeg1 Q x) := by
      intro i hi hiz
      rcases ecases i with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact Or.inl ⟨f, rfl, dblP_eo.1 hi, inc_eo_vo.1 hiz⟩
      · exact absurd hiz not_inc_ec_vo
      · have := inc_ea_vo.1 hiz; subst this; exact Or.inr (Or.inl ⟨rfl, dblP_ea.1 hi⟩)
      · have := inc_eb_vo.1 hiz; subst this; exact Or.inr (Or.inr ⟨rfl, dblP_eb.1 hi⟩)
    rcases qdeg_cases hsub Q hx with h1 | h2 | h3
    · obtain ⟨a, hQa, hax, ha⟩ := h1
      refine ⟨eo a, ea x, eb x, dblP_eo.2 hQa, dblP_ea.2 (Or.inl ⟨a, hQa, hax, ha⟩),
        dblP_eb.2 ⟨a, hQa, hax, ha⟩, inc_eo_vo.2 hax, inc_ea_vo.2 rfl, inc_eb_vo.2 rfl,
        eo_ne_ea _ _, eo_ne_eb _ _, ea_ne_eb _ _, ?_⟩
      intro d hd hdz
      rcases hall d hd hdz with ⟨f, rfl, hQf, hfx⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (by rw [ha f hQf hfx])
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩ := h2
      refine ⟨eo a, eo b, ea x, dblP_eo.2 hQa, dblP_eo.2 hQb,
        dblP_ea.2 (Or.inr ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩), inc_eo_vo.2 hax, inc_eo_vo.2 hbx,
        inc_ea_vo.2 rfl, fun h => hab (eo_inj h), eo_ne_ea _ _, eo_ne_ea _ _, ?_⟩
      intro d hd hdz
      rcases hall d hd hdz with ⟨f, rfl, hQf, hfx⟩ | ⟨rfl, _⟩ | ⟨rfl, h1⟩
      · rcases habd f hQf hfx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩ (fun h2 => qdeg1_not2 h1 h2)
    · obtain ⟨a, b, c, hQa, hQb, hQc, hax, hbx, hcx, hab, hac, hbc, habc⟩ := h3
      have h3' : QDeg3 Q x := ⟨a, b, c, hQa, hQb, hQc, hax, hbx, hcx, hab, hac, hbc, habc⟩
      refine ⟨eo a, eo b, eo c, dblP_eo.2 hQa, dblP_eo.2 hQb, dblP_eo.2 hQc, inc_eo_vo.2 hax,
        inc_eo_vo.2 hbx, inc_eo_vo.2 hcx, fun h => hab (eo_inj h), fun h => hac (eo_inj h),
        fun h => hbc (eo_inj h), ?_⟩
      intro d hd hdz
      rcases hall d hd hdz with ⟨f, rfl, hQf, hfx⟩ | ⟨rfl, h12⟩ | ⟨rfl, h1⟩
      · rcases habc f hQf hfx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exfalso
        rcases h12 with h1 | h2
        · exact qdeg1_not3 h1 h3'
        · exact qdeg2_not3 h2 h3'
      · exact absurd h3' (fun h3 => qdeg1_not3 h1 h3)
  · -- a vertex of the second copy
    have hx : ∃ f, Q f ∧ G.Inc f x := by
      obtain ⟨i, hi, hiz⟩ := hz
      rcases ecases i with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact absurd hiz not_inc_eo_vc
      · exact ⟨f, dblP_ec.1 hi, inc_ec_vc.1 hiz⟩
      · rw [inc_ea_vc.1 hiz] at hi
        rcases dblP_ea.1 hi with h | h
        · exact meets_of_deg1 h
        · exact meets_of_deg2 h
      · rw [inc_eb_vc.1 hiz] at hi
        exact meets_of_deg1 (dblP_eb.1 hi)
    have hall : ∀ i, dblP Q i → (dbl G).Inc i (vc x) →
        (∃ f, i = ec f ∧ Q f ∧ G.Inc f x) ∨ (i = ea x ∧ (QDeg1 Q x ∨ QDeg2 Q x)) ∨ (i = eb x ∧ QDeg1 Q x) := by
      intro i hi hiz
      rcases ecases i with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact absurd hiz not_inc_eo_vc
      · exact Or.inl ⟨f, rfl, dblP_ec.1 hi, inc_ec_vc.1 hiz⟩
      · have := inc_ea_vc.1 hiz; subst this; exact Or.inr (Or.inl ⟨rfl, dblP_ea.1 hi⟩)
      · have := inc_eb_vc.1 hiz; subst this; exact Or.inr (Or.inr ⟨rfl, dblP_eb.1 hi⟩)
    rcases qdeg_cases hsub Q hx with h1 | h2 | h3
    · obtain ⟨a, hQa, hax, ha⟩ := h1
      refine ⟨ec a, ea x, eb x, dblP_ec.2 hQa, dblP_ea.2 (Or.inl ⟨a, hQa, hax, ha⟩),
        dblP_eb.2 ⟨a, hQa, hax, ha⟩, inc_ec_vc.2 hax, inc_ea_vc.2 rfl, inc_eb_vc.2 rfl,
        ec_ne_ea _ _, ec_ne_eb _ _, ea_ne_eb _ _, ?_⟩
      intro d hd hdz
      rcases hall d hd hdz with ⟨f, rfl, hQf, hfx⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (by rw [ha f hQf hfx])
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩ := h2
      refine ⟨ec a, ec b, ea x, dblP_ec.2 hQa, dblP_ec.2 hQb,
        dblP_ea.2 (Or.inr ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩), inc_ec_vc.2 hax, inc_ec_vc.2 hbx,
        inc_ea_vc.2 rfl, fun h => hab (ec_inj h), ec_ne_ea _ _, ec_ne_ea _ _, ?_⟩
      intro d hd hdz
      rcases hall d hd hdz with ⟨f, rfl, hQf, hfx⟩ | ⟨rfl, _⟩ | ⟨rfl, h1⟩
      · rcases habd f hQf hfx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩ (fun h2 => qdeg1_not2 h1 h2)
    · obtain ⟨a, b, c, hQa, hQb, hQc, hax, hbx, hcx, hab, hac, hbc, habc⟩ := h3
      have h3' : QDeg3 Q x := ⟨a, b, c, hQa, hQb, hQc, hax, hbx, hcx, hab, hac, hbc, habc⟩
      refine ⟨ec a, ec b, ec c, dblP_ec.2 hQa, dblP_ec.2 hQb, dblP_ec.2 hQc, inc_ec_vc.2 hax,
        inc_ec_vc.2 hbx, inc_ec_vc.2 hcx, fun h => hab (ec_inj h), fun h => hac (ec_inj h),
        fun h => hbc (ec_inj h), ?_⟩
      intro d hd hdz
      rcases hall d hd hdz with ⟨f, rfl, hQf, hfx⟩ | ⟨rfl, h12⟩ | ⟨rfl, h1⟩
      · rcases habc f hQf hfx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exfalso
        rcases h12 with h1 | h2
        · exact qdeg1_not3 h1 h3'
        · exact qdeg2_not3 h2 h3'
      · exact absurd h3' (fun h3 => qdeg1_not3 h1 h3)

end MGraph


/-! ===================== part 4 ===================== -/


namespace MGraph

variable {G : MGraph}
open dbl

theorem joins_ea (x : Fin G.n) : (dbl G).Joins (ea x) (vo x) (vc x) := Or.inl (ends_ea x)
theorem joins_eb (x : Fin G.n) : (dbl G).Joins (eb x) (vo x) (vc x) := Or.inl (ends_eb x)

/-- **The doubled edge set is connected** (as soon as `Q` is connected and has a vertex of degree one or two). -/
theorem dblP_connected {Q : Fin G.m → Prop} (hQ : ConnectedOn Q) {r : Fin G.n} (hr : QDeg1 Q r ∨ QDeg2 Q r) :
    ConnectedOn (dblP Q) := by
  intro U hU i j hi hj
  have hUo : ∀ f, Q f → U (vo (G.ends f).1) = U (vo (G.ends f).2) := by
    intro f hf; have := hU (eo f) (dblP_eo.2 hf); rw [ends_eo] at this; exact this
  have hUc : ∀ f, Q f → U (vc (G.ends f).1) = U (vc (G.ends f).2) := by
    intro f hf; have := hU (ec f) (dblP_ec.2 hf); rw [ends_ec] at this; exact this
  obtain ⟨a, hQa, har⟩ : ∃ f, Q f ∧ G.Inc f r := hr.elim meets_of_deg1 meets_of_deg2
  have key : ∀ x f, Q f → G.Inc f x → U (vo x) = U (vo (G.ends a).1) := by
    intro x f hf hfx
    have h1 : U (vo x) = U (vo (G.ends f).1) := lab_inc (U := fun z => U (vo z)) (hUo f hf) hfx
    exact h1.trans (hQ (fun z => U (vo z)) hUo f a hf hQa)
  have keyc : ∀ x f, Q f → G.Inc f x → U (vc x) = U (vc (G.ends a).1) := by
    intro x f hf hfx
    have h1 : U (vc x) = U (vc (G.ends f).1) := lab_inc (U := fun z => U (vc z)) (hUc f hf) hfx
    exact h1.trans (hQ (fun z => U (vc z)) hUc f a hf hQa)
  have bridge : U (vo (G.ends a).1) = U (vc (G.ends a).1) := by
    have hra := hU (ea r) (dblP_ea.2 hr); rw [ends_ea] at hra
    rw [← key r a hQa har, hra, keyc r a hQa har]
  have first : ∀ k, dblP Q k → U ((dbl G).ends k).1 = U (vo (G.ends a).1) := by
    intro k hk
    rcases ecases k with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [ends_eo]; exact key _ f (dblP_eo.1 hk) (Or.inl rfl)
    · rw [ends_ec, bridge]; exact keyc _ f (dblP_ec.1 hk) (Or.inl rfl)
    · rw [ends_ea]
      obtain ⟨f, hf, hfx⟩ := (dblP_ea.1 hk).elim meets_of_deg1 meets_of_deg2
      exact key x f hf hfx
    · rw [ends_eb]
      obtain ⟨f, hf, hfx⟩ := meets_of_deg1 (dblP_eb.1 hk)
      exact key x f hf hfx
  rw [first i hi, first j hj]

/-- the unique edge at a vertex of degree one is pendant -/
theorem pendant_of_deg1 {Q : Fin G.m → Prop} {x : Fin G.n} {p : Fin G.m} (h : QDeg1 Q x) (hp : Q p)
    (hpx : G.Inc p x) : Pendant Q p := by
  obtain ⟨a, _, _, ha⟩ := h
  refine ⟨hp, x, hpx, fun g hg hgp hgx => hgp ?_⟩
  rw [ha g hg hgx, ha p hp hpx]

/-- a pendant edge has an end of degree one -/
theorem deg1_of_pendant {Q : Fin G.m → Prop} {p : Fin G.m} (h : Pendant Q p) :
    ∃ x, G.Inc p x ∧ QDeg1 Q x := by
  obtain ⟨hp, x, hpx, hx⟩ := h
  refine ⟨x, hpx, p, hp, hpx, fun d hd hdx => ?_⟩
  apply Classical.byContradiction
  intro hdp
  exact hx d hd hdp hdx

/-- **The doubled edge set is bridgeless**, given: the core of `Q` is connected and admits no cut of `Q`; the far
    end of the edge at a vertex of degree one, and every vertex of degree two, meet the core; and there are two
    distinct vertices of degree one or two. -/
theorem dblP_bridgeless {Q : Fin G.m → Prop} (hcore : ConnectedOn (Core Q))
    (hcut : ∀ f, Core Q f → G.CutOn Q f → False)
    (hleaf : ∀ l p y, QDeg1 Q l → Q p → G.Joins p l y → ∃ f, Core Q f ∧ G.Inc f y)
    (hdeg2 : ∀ x, QDeg2 Q x → ∃ f, Core Q f ∧ G.Inc f x)
    {r1 r2 : Fin G.n} (hr : r1 ≠ r2) (hr1 : QDeg1 Q r1 ∨ QDeg2 Q r1) (hr2 : QDeg1 Q r2 ∨ QDeg2 Q r2) :
    BridgelessOn (dblP Q) := by
  classical
  intro e he B
  obtain ⟨U, hu, hv, hsep⟩ := B
  have hne : U ((dbl G).ends e).1 ≠ U ((dbl G).ends e).2 := by rw [hu, hv]; decide
  have sepj : ∀ i x y, dblP Q i → i ≠ e → (dbl G).Joins i x y → U x = U y :=
    fun i x y hi hie hj => lab_joins (hsep i hi hie) hj
  -- step 1: `e` is not a copy of a core edge
  have nco : ∀ f, Core Q f → e ≠ eo f := by
    intro f hf hef
    rw [hef, ends_eo] at hne
    obtain ⟨C⟩ := cut_of_sep (P := Q) (fun z => U (vo z)) hne (fun g hg hgf => by
      have := hsep (eo g) (dblP_eo.2 hg) (fun h => hgf (eo_inj (h.trans hef))); rw [ends_eo] at this; exact this)
    exact hcut f hf C
  have ncc : ∀ f, Core Q f → e ≠ ec f := by
    intro f hf hef
    rw [hef, ends_ec] at hne
    obtain ⟨C⟩ := cut_of_sep (P := Q) (fun z => U (vc z)) hne (fun g hg hgf => by
      have := hsep (ec g) (dblP_ec.2 hg) (fun h => hgf (ec_inj (h.trans hef))); rw [ends_ec] at this; exact this)
    exact hcut f hf C
  -- a core edge, to name the side values
  obtain ⟨f0, hf0⟩ : ∃ f, Core Q f := by
    rcases hr1 with h | h
    · obtain ⟨p, hp, hpr, _⟩ := id h
      obtain ⟨y, hj⟩ := exists_joins_of_inc hpr
      obtain ⟨f, hf, _⟩ := hleaf r1 p y h hp (joins_symm hj)
      exact ⟨f, hf⟩
    · obtain ⟨f, hf, _⟩ := hdeg2 r1 h
      exact ⟨f, hf⟩
  have hUo : ∀ f, Core Q f → U (vo (G.ends f).1) = U (vo (G.ends f).2) := by
    intro f hf
    have := hsep (eo f) (dblP_eo.2 hf.1) (Ne.symm (nco f hf)); rw [ends_eo] at this; exact this
  have hUc : ∀ f, Core Q f → U (vc (G.ends f).1) = U (vc (G.ends f).2) := by
    intro f hf
    have := hsep (ec f) (dblP_ec.2 hf.1) (Ne.symm (ncc f hf)); rw [ends_ec] at this; exact this
  have Ao : ∀ x f, Core Q f → G.Inc f x → U (vo x) = U (vo (G.ends f0).1) := by
    intro x f hf hfx
    exact (lab_inc (U := fun z => U (vo z)) (hUo f hf) hfx).trans
      (hcore (fun z => U (vo z)) hUo f f0 hf hf0)
  have Ac : ∀ x f, Core Q f → G.Inc f x → U (vc x) = U (vc (G.ends f0).1) := by
    intro x f hf hfx
    exact (lab_inc (U := fun z => U (vc z)) (hUc f hf) hfx).trans
      (hcore (fun z => U (vc z)) hUc f f0 hf hf0)
  -- at a vertex of degree one the two rungs are parallel, so they tie the two copies of the leaf
  have rung1 : ∀ x, QDeg1 Q x → U (vo x) = U (vc x) := by
    intro x hx
    by_cases hea : ea x = e
    · exact sepj (eb x) _ _ (dblP_eb.2 hx) (fun h => ea_ne_eb x x (hea.trans h.symm)) (joins_eb x)
    · exact sepj (ea x) _ _ (dblP_ea.2 (Or.inl hx)) hea (joins_ea x)
  -- step 3: a rung gadget avoiding `e` ties the two sides
  have gad : ∀ r, (QDeg2 Q r ∧ e ≠ ea r) ∨ (∃ p y, QDeg1 Q r ∧ Q p ∧ G.Joins p r y ∧ e ≠ eo p ∧ e ≠ ec p) →
      U (vo (G.ends f0).1) = U (vc (G.ends f0).1) := by
    intro r hr'
    rcases hr' with ⟨h2, hne'⟩ | ⟨p, y, h1, hp, hj, hno, hnc⟩
    · obtain ⟨f, hf, hfr⟩ := hdeg2 r h2
      rw [← Ao r f hf hfr, ← Ac r f hf hfr]
      exact sepj (ea r) _ _ (dblP_ea.2 (Or.inr h2)) (Ne.symm hne') (joins_ea r)
    · obtain ⟨f, hf, hfy⟩ := hleaf r p y h1 hp hj
      rw [← Ao y f hf hfy, ← Ac y f hf hfy]
      have e1 : U (vo r) = U (vo y) := sepj (eo p) _ _ (dblP_eo.2 hp) (Ne.symm hno) (joins_eo hj)
      have e2 : U (vc r) = U (vc y) := sepj (ec p) _ _ (dblP_ec.2 hp) (Ne.symm hnc) (joins_ec hj)
      rw [← e1, ← e2]
      exact rung1 r h1
  -- the data of a rung vertex
  have rdata : ∀ r, (QDeg1 Q r ∨ QDeg2 Q r) →
      QDeg2 Q r ∨ ∃ p y, QDeg1 Q r ∧ Q p ∧ G.Joins p r y := by
    intro r hr'
    rcases hr' with h | h
    · obtain ⟨p, hp, hpr, _⟩ := id h
      obtain ⟨y, hj⟩ := exists_joins_of_inc hpr
      exact Or.inr ⟨p, y, h, hp, joins_symm hj⟩
    · exact Or.inl h
  -- step 4: one of the two gadgets avoids `e`
  have tie : U (vo (G.ends f0).1) = U (vc (G.ends f0).1) := by
    rcases rdata r1 hr1 with h2 | ⟨p1, y1, h1, hp1, hj1⟩ <;> rcases rdata r2 hr2 with h2' | ⟨p2, y2, h1', hp2, hj2⟩
    · by_cases hea : e = ea r1
      · exact gad r2 (Or.inl ⟨h2', fun h => hr (ea_inj (hea.symm.trans h))⟩)
      · exact gad r1 (Or.inl ⟨h2, hea⟩)
    · by_cases hea : e = ea r1
      · exact gad r2 (Or.inr ⟨p2, y2, h1', hp2, hj2, fun h => eo_ne_ea _ _ (h.symm.trans hea),
          fun h => ec_ne_ea _ _ (h.symm.trans hea)⟩)
      · exact gad r1 (Or.inl ⟨h2, hea⟩)
    · by_cases hea : e = ea r2
      · exact gad r1 (Or.inr ⟨p1, y1, h1, hp1, hj1, fun h => eo_ne_ea _ _ (h.symm.trans hea),
          fun h => ec_ne_ea _ _ (h.symm.trans hea)⟩)
      · exact gad r2 (Or.inl ⟨h2', hea⟩)
    · by_cases hp12 : p1 = p2
      · -- one edge with two ends of degree one: impossible, its far end meets the core
        exfalso
        subst hp12
        have hy1 : y1 = r2 := by
          rcases joins_unique hj1 hj2 with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h hr
          · exact h
        obtain ⟨f, hf, hfy⟩ := hleaf r1 p1 y1 h1 hp1 hj1
        obtain ⟨a, _, _, ha⟩ := h1'
        have hpc : ¬ Core Q p1 := fun hc => hc.2 (pendant_of_deg1 h1 hp1 (joins_inc_left hj1))
        have : f = p1 := (ha f hf.1 (hy1 ▸ hfy)).trans (ha p1 hp1 (joins_inc_left hj2)).symm
        exact hpc (this ▸ hf)
      · by_cases hin : e = eo p1 ∨ e = ec p1
        · refine gad r2 (Or.inr ⟨p2, y2, h1', hp2, hj2, ?_, ?_⟩)
          · intro h
            rcases hin with h' | h'
            · exact hp12 (eo_inj (h'.symm.trans h))
            · exact eo_ne_ec _ _ (h.symm.trans h')
          · intro h
            rcases hin with h' | h'
            · exact eo_ne_ec _ _ (h'.symm.trans h)
            · exact hp12 (ec_inj (h'.symm.trans h))
        · simp only [not_or] at hin
          exact gad r1 (Or.inr ⟨p1, y1, h1, hp1, hj1, hin.1, hin.2⟩)
  -- step 5: every possible `e` is tied
  rcases ecases e with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have hQf := dblP_eo.1 he
    by_cases hfc : Core Q f
    · exact nco f hfc rfl
    obtain ⟨x, hfx, hx1⟩ := deg1_of_pendant (Classical.byContradiction fun hp => hfc ⟨hQf, hp⟩)
    obtain ⟨y, hj⟩ := exists_joins_of_inc hfx
    have hj' := joins_symm hj
    obtain ⟨g, hg, hgy⟩ := hleaf x f y hx1 hQf hj'
    have c1 : U (vc x) = U (vc y) :=
      sepj (ec f) _ _ (dblP_ec.2 hQf) (fun h => eo_ne_ec _ _ h.symm) (joins_ec hj')
    have c2 : U (vo x) = U (vo y) := by
      rw [rung1 x hx1, c1, Ac y g hg hgy, ← tie, ← Ao y g hg hgy]
    rw [ends_eo] at hne
    apply hne
    rcases joins_unique (joins_ends f) hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact c2
    · rw [h1, h2]; exact c2.symm
  · have hQf := dblP_ec.1 he
    by_cases hfc : Core Q f
    · exact ncc f hfc rfl
    obtain ⟨x, hfx, hx1⟩ := deg1_of_pendant (Classical.byContradiction fun hp => hfc ⟨hQf, hp⟩)
    obtain ⟨y, hj⟩ := exists_joins_of_inc hfx
    have hj' := joins_symm hj
    obtain ⟨g, hg, hgy⟩ := hleaf x f y hx1 hQf hj'
    have c1 : U (vo x) = U (vo y) :=
      sepj (eo f) _ _ (dblP_eo.2 hQf) (fun h => eo_ne_ec _ _ h) (joins_eo hj')
    have c2 : U (vc x) = U (vc y) := by
      rw [← rung1 x hx1, c1, Ao y g hg hgy, tie, ← Ac y g hg hgy]
    rw [ends_ec] at hne
    apply hne
    rcases joins_unique (joins_ends f) hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact c2
    · rw [h1, h2]; exact c2.symm
  · rw [ends_ea] at hne
    rcases dblP_ea.1 he with h1 | h2
    · exact hne (rung1 x h1)
    · obtain ⟨f, hf, hfx⟩ := hdeg2 x h2
      exact hne (by rw [Ao x f hf hfx, tie, ← Ac x f hf hfx])
  · rw [ends_eb] at hne
    exact hne (rung1 x (dblP_eb.1 he))

end MGraph


/-! ===================== part 5 ===================== -/


namespace MGraph

variable {G : MGraph}

theorem three_minus_one {Q : Fin G.m → Prop} {z : Fin G.n} (h3 : QDeg3 Q z) {f : Fin G.m} (hf : Q f)
    (hfz : G.Inc f z) :
    ∃ x1 x2, Q x1 ∧ Q x2 ∧ G.Inc x1 z ∧ G.Inc x2 z ∧ x1 ≠ x2 ∧ x1 ≠ f ∧ x2 ≠ f ∧
      ∀ d, Q d → G.Inc d z → d = f ∨ d = x1 ∨ d = x2 := by
  obtain ⟨a, b, c, hQa, hQb, hQc, haz, hbz, hcz, hab, hac, hbc, habc⟩ := h3
  rcases habc f hf hfz with rfl | rfl | rfl
  · exact ⟨b, c, hQb, hQc, hbz, hcz, hbc, Ne.symm hab, Ne.symm hac, habc⟩
  · refine ⟨a, c, hQa, hQc, haz, hcz, hac, hab, Ne.symm hbc, fun d hd hdz => ?_⟩
    rcases habc d hd hdz with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · refine ⟨a, b, hQa, hQb, haz, hbz, hab, hac, hbc, fun d hd hdz => ?_⟩
    rcases habc d hd hdz with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- The data of the suppression case: `y` is the only vertex of `Q`-degree two, or the neighbour of the only
    vertex `l` of `Q`-degree one; `f1 = yu`, `f2 = yw` are its other edges; every other vertex has degree three.
    (`l = y` when there is no pendant edge.) -/
structure SuppData (Q : Fin G.m → Prop) where
  y : Fin G.n
  u : Fin G.n
  w : Fin G.n
  l : Fin G.n
  f1 : Fin G.m
  f2 : Fin G.m
  hf1 : G.Joins f1 y u
  hf2 : G.Joins f2 y w
  hQ1 : Q f1
  hQ2 : Q f2
  hf12 : f1 ≠ f2
  hy : ∀ d, Q d → G.Inc d y → d = f1 ∨ d = f2 ∨ G.Joins d y l
  hl : ∀ d d', Q d → G.Joins d y l → Q d' → G.Inc d' l → d' = d
  hlu : l ≠ u
  hlw : l ≠ w
  hlleaf : l = y ∨ ∀ d, Q d → G.Inc d l → G.Joins d y l
  hrest : ∀ x, x ≠ y → x ≠ l → (∃ f, Q f ∧ G.Inc f x) → QDeg3 Q x

namespace SuppData
variable {Q : Fin G.m → Prop} (S : SuppData Q)

theorem y_ne_u (hloop : Loopless G) : S.y ≠ S.u := ne_of_joins hloop S.hf1
theorem y_ne_w (hloop : Loopless G) : S.y ≠ S.w := ne_of_joins hloop S.hf2

/-- an edge of `Q` at `l` meets `y` -/
theorem at_l_at_y {d : Fin G.m} (hd : Q d) (hdl : G.Inc d S.l) : G.Inc d S.y := by
  rcases S.hlleaf with h | h
  · exact h ▸ hdl
  · exact joins_inc_left (h d hd hdl)

/-- an edge of `Q` meeting `y` and a vertex `x ∉ {y, l}` is `f1` (and `x = u`) or `f2` (and `x = w`) -/
theorem at_y_other {d : Fin G.m} {x : Fin G.n} (hd : Q d) (hdy : G.Inc d S.y) (hdx : G.Inc d x)
    (hxy : x ≠ S.y) (hxl : x ≠ S.l) : (d = S.f1 ∧ x = S.u) ∨ (d = S.f2 ∧ x = S.w) := by
  rcases S.hy d hd hdy with h | h | h
  · rw [h] at hdx
    rcases inc_of_joins S.hf1 hdx with h' | h'
    · exact absurd h' hxy
    · exact Or.inl ⟨h, h'⟩
  · rw [h] at hdx
    rcases inc_of_joins S.hf2 hdx with h' | h'
    · exact absurd h' hxy
    · exact Or.inr ⟨h, h'⟩
  · rcases inc_of_joins h hdx with h' | h'
    · exact absurd h' hxy
    · exact absurd h' hxl

/-- **`u ≠ w`**: otherwise the third edge at `u` would be a bridge of `Q`. -/
theorem u_ne_w (hloop : Loopless G) (hcutQ : ∀ f, Q f → ¬ G.Inc f S.y → G.CutOn Q f → False) : S.u ≠ S.w := by
  classical
  intro huw
  have hyu := S.y_ne_u hloop
  have hul : S.u ≠ S.l := Ne.symm S.hlu
  have hf2u : G.Inc S.f2 S.u := huw ▸ joins_inc_right S.hf2
  have h3 : QDeg3 Q S.u := S.hrest S.u (Ne.symm hyu) hul ⟨S.f1, S.hQ1, joins_inc_right S.hf1⟩
  obtain ⟨x1, x2, hQx1, hQx2, hx1u, hx2u, hx12, hx1f, hx2f, hall⟩ := three_minus_one h3 S.hQ1
    (joins_inc_right S.hf1)
  -- `f2` is one of `x1, x2`; call the other one `h`
  obtain ⟨h, hQh, hhu, hhf1, hhf2, hallu⟩ : ∃ h, Q h ∧ G.Inc h S.u ∧ h ≠ S.f1 ∧ h ≠ S.f2 ∧
      ∀ d, Q d → G.Inc d S.u → d = S.f1 ∨ d = S.f2 ∨ d = h := by
    rcases hall S.f2 S.hQ2 hf2u with h | h | h
    · exact absurd h.symm S.hf12
    · refine ⟨x2, hQx2, hx2u, hx2f, fun h' => hx12 (h.symm.trans h'.symm), fun d hd hdu => ?_⟩
      rcases hall d hd hdu with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (h1.trans h.symm))
      · exact Or.inr (Or.inr h1)
    · refine ⟨x1, hQx1, hx1u, hx1f, fun h' => hx12 (h'.trans h), fun d hd hdu => ?_⟩
      rcases hall d hd hdu with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)
      · exact Or.inr (Or.inl (h1.trans h.symm))
  have hhy : ¬ G.Inc h S.y := by
    intro hy'
    rcases S.at_y_other hQh hy' hhu (Ne.symm hyu) hul with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hhf1 h1
    · exact hhf2 h1
  -- the labelling `{y, u, l}` against the rest
  let V : Fin G.n → Bool := fun v => decide (v = S.y ∨ v = S.u ∨ v = S.l)
  obtain ⟨z, hjz⟩ := exists_joins_of_inc hhu
  have hzu : z ≠ S.u := ne_of_joins hloop hjz
  have hzy : z ≠ S.y := fun h' => hhy (h' ▸ joins_inc_left hjz)
  have hzl : z ≠ S.l := fun h' => hhy (S.at_l_at_y hQh (h' ▸ joins_inc_left hjz))
  have hVz : V z = false := by simp [V, hzy, hzu, hzl]
  have hVu : V S.u = true := by simp [V]
  have inS : ∀ d, Q d → d ≠ h → ∀ v, G.Inc d v → V v = true → ∀ v', G.Inc d v' → V v' = true := by
    intro d hd hdh v hdv hv v' hdv'
    simp only [V, decide_eq_true_eq] at hv ⊢
    have hends : ∀ x, G.Inc d x → x = S.y ∨ x = S.u ∨ x = S.l := by
      -- `d` meets `{y, u, l}`, so it is `f1`, `f2` or a pendant edge at `y`
      have hdy : G.Inc d S.y := by
        rcases hv with rfl | rfl | rfl
        · exact hdv
        · rcases hallu d hd hdv with h1 | h1 | h1
          · exact h1 ▸ joins_inc_left S.hf1
          · exact h1 ▸ joins_inc_left S.hf2
          · exact absurd h1 hdh
        · exact S.at_l_at_y hd hdv
      intro x hx
      rcases S.hy d hd hdy with h1 | h1 | h1
      · rw [h1] at hx; rcases inc_of_joins S.hf1 hx with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
      · rw [h1] at hx; rcases inc_of_joins S.hf2 hx with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl (h2.trans huw.symm))
      · rcases inc_of_joins h1 hx with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inr h2)
    exact hends v' hdv'
  have hsep : ∀ d, Q d → d ≠ h → V (G.ends d).1 = V (G.ends d).2 := by
    intro d hd hdh
    cases h1 : V (G.ends d).1 <;> cases h2 : V (G.ends d).2
    · rfl
    · exact absurd (inS d hd hdh _ (Or.inr rfl) h2 _ (Or.inl rfl)) (by rw [h1]; decide)
    · exact absurd (inS d hd hdh _ (Or.inl rfl) h1 _ (Or.inr rfl)) (by rw [h2]; decide)
    · rfl
  have hne : V (G.ends h).1 ≠ V (G.ends h).2 := by
    rcases hjz with h' | h' <;> rw [h'] <;> simp only [hVz, hVu] <;> decide
  obtain ⟨C⟩ := cut_of_sep V hne hsep
  exact hcutQ h hQh hhy C

/-! ### the suppressed edge set -/

theorem supp_old {d : Fin G.m} : supp Q S.y S.u S.w (Fin.castSucc d) ↔ Q d ∧ ¬ G.Inc d S.y := by
  constructor
  · rintro (h | ⟨d', h, hd, hdy⟩)
    · exact absurd h (castSucc_ne_last' d)
    · rw [Fin.castSucc_inj.1 h]; exact ⟨hd, hdy⟩
  · intro h; exact Or.inr ⟨d, rfl, h.1, h.2⟩

theorem supp_new : supp Q S.y S.u S.w (Fin.last G.m) := Or.inl rfl

/-- the labelling that moves `y` and `l` to the value of `u` -/
def lift (U : Fin G.n → Bool) : Fin G.n → Bool := fun v => if v = S.y ∨ v = S.l then U S.u else U v

theorem lift_other {U : Fin G.n → Bool} {v : Fin G.n} (hy : v ≠ S.y) (hl : v ≠ S.l) : S.lift U v = U v := by
  simp [lift, hy, hl]

theorem lift_y (U : Fin G.n → Bool) : S.lift U S.y = U S.u := by simp [lift]
theorem lift_l (U : Fin G.n → Bool) : S.lift U S.l = U S.u := by simp [lift]

/-- an edge of `Q` avoiding `y` avoids `l` too -/
theorem not_l_of_not_y {d : Fin G.m} (hd : Q d) (hdy : ¬ G.Inc d S.y) {x : Fin G.n} (hdx : G.Inc d x) :
    x ≠ S.y ∧ x ≠ S.l :=
  ⟨fun h => hdy (h ▸ hdx), fun h => hdy (S.at_l_at_y hd (h ▸ hdx))⟩

/-- `lift U` does not separate any edge of `Q` if `U` separates neither `u w` nor an edge of `Q` avoiding `y` -/
theorem lift_sep (hloop : Loopless G) {U : Fin G.n → Bool} (huw : U S.u = U S.w)
    {e : Fin G.m} (hU : ∀ d, Q d → ¬ G.Inc d S.y → d ≠ e → U (G.ends d).1 = U (G.ends d).2) :
    ∀ d, Q d → d ≠ e → S.lift U (G.ends d).1 = S.lift U (G.ends d).2 := by
  intro d hd hde
  have hyu := S.y_ne_u hloop
  have hyw := S.y_ne_w hloop
  by_cases hdy : G.Inc d S.y
  · -- `d` is `f1`, `f2` or a pendant edge: all its ends get the value `U u`
    have hval : ∀ x, G.Inc d x → S.lift U x = U S.u := by
      intro x hx
      by_cases hxy : x = S.y
      · rw [hxy, S.lift_y U]
      by_cases hxl : x = S.l
      · rw [hxl, S.lift_l U]
      rcases S.at_y_other hd hdy hx hxy hxl with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact S.lift_other hxy hxl
      · rw [S.lift_other hxy hxl, huw]
    rw [hval _ (Or.inl rfl), hval _ (Or.inr rfl)]
  · have h1 := S.not_l_of_not_y hd hdy (Or.inl rfl)
    have h2 := S.not_l_of_not_y hd hdy (Or.inr rfl)
    rw [S.lift_other (U := U) h1.1 h1.2, S.lift_other (U := U) h2.1 h2.2]
    exact hU d hd hdy hde

theorem supp_connected (hloop : Loopless G) (hconn : ConnectedOn Q) : ConnectedOn (supp Q S.y S.u S.w) := by
  intro U hU i j hi hj
  have huw : U S.u = U S.w := by
    have := hU _ S.supp_new; rw [addEdge_ends_new] at this; exact this
  have hUold : ∀ d, Q d → ¬ G.Inc d S.y → U (G.ends d).1 = U (G.ends d).2 := by
    intro d hd hdy
    have := hU _ (S.supp_old.2 ⟨hd, hdy⟩); rw [addEdge_ends_old] at this; exact this
  -- `lift U` separates no edge of `Q` (use a dummy excluded edge `f1`, which meets `y`)
  have hsep : ∀ d, Q d → S.lift U (G.ends d).1 = S.lift U (G.ends d).2 := by
    intro d hd
    by_cases hdf : d = S.f1
    · rw [hdf]
      have hyu := S.y_ne_u hloop
      rcases S.hf1 with h | h <;> rw [h]
      · show S.lift U S.y = S.lift U S.u
        rw [S.lift_y U, S.lift_other (U := U) (Ne.symm hyu) (Ne.symm S.hlu)]
      · show S.lift U S.u = S.lift U S.y
        rw [S.lift_y U, S.lift_other (U := U) (Ne.symm hyu) (Ne.symm S.hlu)]
    · exact S.lift_sep hloop huw (e := S.f1) (fun d hd hdy _ => hUold d hd hdy) d hd hdf
  have K := hconn (S.lift U) hsep
  -- the first end of every edge of `supp` has the value of `f1`'s first end
  have first : ∀ k, supp Q S.y S.u S.w k → U ((addEdge G S.u S.w).ends k).1 = S.lift U (G.ends S.f1).1 := by
    intro k hk
    rcases addEdge_cases k with rfl | ⟨d, rfl⟩
    · rw [addEdge_ends_new]
      have hyu := S.y_ne_u hloop
      rw [← S.lift_other (U := U) (Ne.symm hyu) (Ne.symm S.hlu)]
      exact lab_inc (U := S.lift U) (hsep S.f1 S.hQ1) (joins_inc_right S.hf1)
    · obtain ⟨hd, hdy⟩ := S.supp_old.1 hk
      rw [addEdge_ends_old]
      have h1 := S.not_l_of_not_y hd hdy (Or.inl rfl)
      rw [← S.lift_other (U := U) h1.1 h1.2]
      exact K d S.f1 hd S.hQ1
  rw [first i hi, first j hj]

theorem supp_bridgeless (hloop : Loopless G)
    (hcutQ : ∀ f, Q f → (f = S.f2 ∨ ¬ G.Inc f S.y) → G.CutOn Q f → False) :
    BridgelessOn (supp Q S.y S.u S.w) := by
  intro e he B
  obtain ⟨U, hu, hv, hsep⟩ := B
  have hne : U ((addEdge G S.u S.w).ends e).1 ≠ U ((addEdge G S.u S.w).ends e).2 := by rw [hu, hv]; decide
  have hyu := S.y_ne_u hloop
  have hyw := S.y_ne_w hloop
  rcases addEdge_cases e with rfl | ⟨d0, rfl⟩
  · -- the new edge: `lift U` separates `f2`
    rw [addEdge_ends_new] at hne
    have hUold : ∀ d, Q d → ¬ G.Inc d S.y → U (G.ends d).1 = U (G.ends d).2 := by
      intro d hd hdy
      have := hsep _ (S.supp_old.2 ⟨hd, hdy⟩) (castSucc_ne_last' d); rw [addEdge_ends_old] at this; exact this
    have hsepL : ∀ d, Q d → d ≠ S.f2 → S.lift U (G.ends d).1 = S.lift U (G.ends d).2 := by
      intro d hd hdf2
      by_cases hdy : G.Inc d S.y
      · have hval : ∀ x, G.Inc d x → S.lift U x = U S.u := by
          intro x hx
          by_cases hxy : x = S.y
          · rw [hxy, S.lift_y U]
          by_cases hxl : x = S.l
          · rw [hxl, S.lift_l U]
          rcases S.at_y_other hd hdy hx hxy hxl with ⟨_, rfl⟩ | ⟨h, _⟩
          · exact S.lift_other hxy hxl
          · exact absurd h hdf2
        rw [hval _ (Or.inl rfl), hval _ (Or.inr rfl)]
      · have h1 := S.not_l_of_not_y hd hdy (Or.inl rfl)
        have h2 := S.not_l_of_not_y hd hdy (Or.inr rfl)
        rw [S.lift_other (U := U) h1.1 h1.2, S.lift_other (U := U) h2.1 h2.2]
        exact hUold d hd hdy
    have hsepf2 : S.lift U (G.ends S.f2).1 ≠ S.lift U (G.ends S.f2).2 := by
      have hw := S.lift_other (U := U) (Ne.symm hyw) (Ne.symm S.hlw)
      rcases S.hf2 with h | h <;> rw [h]
      · show S.lift U S.y ≠ S.lift U S.w
        rw [S.lift_y U, hw]; exact hne
      · show S.lift U S.w ≠ S.lift U S.y
        rw [S.lift_y U, hw]; exact Ne.symm hne
    obtain ⟨C⟩ := cut_of_sep (P := Q) (S.lift U) hsepf2 hsepL
    exact hcutQ S.f2 S.hQ2 (Or.inl rfl) C
  · -- an old edge `d0`
    obtain ⟨hd0, hd0y⟩ := S.supp_old.1 he
    rw [addEdge_ends_old] at hne
    have huw : U S.u = U S.w := by
      have := hsep _ S.supp_new (fun h => castSucc_ne_last' d0 h.symm); rw [addEdge_ends_new] at this; exact this
    have hUold : ∀ d, Q d → ¬ G.Inc d S.y → d ≠ d0 → U (G.ends d).1 = U (G.ends d).2 := by
      intro d hd hdy hdd
      have := hsep _ (S.supp_old.2 ⟨hd, hdy⟩) (fun h => hdd (Fin.castSucc_inj.1 h))
      rw [addEdge_ends_old] at this; exact this
    have hsepL : ∀ d, Q d → d ≠ d0 → S.lift U (G.ends d).1 = S.lift U (G.ends d).2 :=
      fun d hd hdd => S.lift_sep hloop huw hUold d hd hdd
    have h1 := S.not_l_of_not_y hd0 hd0y (Or.inl rfl)
    have h2 := S.not_l_of_not_y hd0 hd0y (Or.inr rfl)
    have hsep0 : S.lift U (G.ends d0).1 ≠ S.lift U (G.ends d0).2 := by
      rw [S.lift_other (U := U) h1.1 h1.2, S.lift_other (U := U) h2.1 h2.2]; exact hne
    obtain ⟨C⟩ := cut_of_sep (P := Q) (S.lift U) hsep0 hsepL
    exact hcutQ d0 hd0 (Or.inr hd0y) C

theorem supp_cubic (hloop : Loopless G) (huw : S.u ≠ S.w) : CubicOn (supp Q S.y S.u S.w) := by
  intro z hz
  have hyu := S.y_ne_u hloop
  have hyw := S.y_ne_w hloop
  -- edges of `supp` at `z`
  have hall : ∀ i, supp Q S.y S.u S.w i → (addEdge G S.u S.w).Inc i z →
      (i = Fin.last G.m ∧ (z = S.u ∨ z = S.w)) ∨
        (∃ d, i = Fin.castSucc d ∧ Q d ∧ ¬ G.Inc d S.y ∧ G.Inc d z) := by
    intro i hi hiz
    rcases addEdge_cases i with rfl | ⟨d, rfl⟩
    · exact Or.inl ⟨rfl, (addEdge_inc_new (G := G)).1 hiz⟩
    · obtain ⟨hd, hdy⟩ := S.supp_old.1 hi
      exact Or.inr ⟨d, rfl, hd, hdy, addEdge_inc_old.1 hiz⟩
  obtain ⟨i0, hi0, hi0z⟩ := hz
  have hzyl : z ≠ S.y ∧ z ≠ S.l ∧ ∃ f, Q f ∧ G.Inc f z := by
    rcases hall i0 hi0 hi0z with ⟨_, rfl | rfl⟩ | ⟨d, _, hd, hdy, hdz⟩
    · exact ⟨Ne.symm hyu, Ne.symm S.hlu, S.f1, S.hQ1, joins_inc_right S.hf1⟩
    · exact ⟨Ne.symm hyw, Ne.symm S.hlw, S.f2, S.hQ2, joins_inc_right S.hf2⟩
    · have := S.not_l_of_not_y hd hdy hdz
      exact ⟨this.1, this.2, d, hd, hdz⟩
  obtain ⟨hzy, hzl, hzQ⟩ := hzyl
  have h3 : QDeg3 Q z := S.hrest z hzy hzl hzQ
  -- an edge of `Q` at `z` meets `y` only if it is `f1` (z = u) or `f2` (z = w)
  have aty : ∀ d, Q d → G.Inc d z → G.Inc d S.y → (d = S.f1 ∧ z = S.u) ∨ (d = S.f2 ∧ z = S.w) :=
    fun d hd hdz hdy => S.at_y_other hd hdy hdz hzy hzl
  by_cases hzu : z = S.u
  · -- at `u`: the two other edges and the new edge
    obtain ⟨x1, x2, hQx1, hQx2, hx1z, hx2z, hx12, hx1f, hx2f, hallz⟩ :=
      three_minus_one h3 S.hQ1 (hzu ▸ joins_inc_right S.hf1)
    have nx : ∀ x, Q x → G.Inc x z → x ≠ S.f1 → ¬ G.Inc x S.y := by
      intro x hx hxz hxf hxy
      rcases aty x hx hxz hxy with ⟨h, _⟩ | ⟨_, h⟩
      · exact hxf h
      · exact huw (hzu.symm.trans h)
    refine ⟨Fin.castSucc x1, Fin.castSucc x2, Fin.last G.m, S.supp_old.2 ⟨hQx1, nx x1 hQx1 hx1z hx1f⟩,
      S.supp_old.2 ⟨hQx2, nx x2 hQx2 hx2z hx2f⟩, S.supp_new, addEdge_inc_old.2 hx1z, addEdge_inc_old.2 hx2z,
      addEdge_inc_new.2 (Or.inl hzu), fun h => hx12 (Fin.castSucc_inj.1 h), castSucc_ne_last' _,
      castSucc_ne_last' _, ?_⟩
    intro k hk hkz
    rcases hall k hk hkz with ⟨rfl, _⟩ | ⟨d, rfl, hd, hdy, hdz⟩
    · exact Or.inr (Or.inr rfl)
    · rcases hallz d hd hdz with h | h | h
      · exact absurd (h ▸ joins_inc_left S.hf1) hdy
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
  by_cases hzw : z = S.w
  · obtain ⟨x1, x2, hQx1, hQx2, hx1z, hx2z, hx12, hx1f, hx2f, hallz⟩ :=
      three_minus_one h3 S.hQ2 (hzw ▸ joins_inc_right S.hf2)
    have nx : ∀ x, Q x → G.Inc x z → x ≠ S.f2 → ¬ G.Inc x S.y := by
      intro x hx hxz hxf hxy
      rcases aty x hx hxz hxy with ⟨_, h⟩ | ⟨h, _⟩
      · exact huw (h.symm.trans hzw)
      · exact hxf h
    refine ⟨Fin.castSucc x1, Fin.castSucc x2, Fin.last G.m, S.supp_old.2 ⟨hQx1, nx x1 hQx1 hx1z hx1f⟩,
      S.supp_old.2 ⟨hQx2, nx x2 hQx2 hx2z hx2f⟩, S.supp_new, addEdge_inc_old.2 hx1z, addEdge_inc_old.2 hx2z,
      addEdge_inc_new.2 (Or.inr hzw), fun h => hx12 (Fin.castSucc_inj.1 h), castSucc_ne_last' _,
      castSucc_ne_last' _, ?_⟩
    intro k hk hkz
    rcases hall k hk hkz with ⟨rfl, _⟩ | ⟨d, rfl, hd, hdy, hdz⟩
    · exact Or.inr (Or.inr rfl)
    · rcases hallz d hd hdz with h | h | h
      · exact absurd (h ▸ joins_inc_left S.hf2) hdy
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
  · -- elsewhere: the three edges of `Q`, none of them at `y`
    obtain ⟨a, b, c, hQa, hQb, hQc, haz, hbz, hcz, hab, hac, hbc, habc⟩ := h3
    have nx : ∀ x, Q x → G.Inc x z → ¬ G.Inc x S.y := by
      intro x hx hxz hxy
      rcases aty x hx hxz hxy with ⟨_, h⟩ | ⟨_, h⟩
      · exact hzu h
      · exact hzw h
    refine ⟨Fin.castSucc a, Fin.castSucc b, Fin.castSucc c, S.supp_old.2 ⟨hQa, nx a hQa haz⟩,
      S.supp_old.2 ⟨hQb, nx b hQb hbz⟩, S.supp_old.2 ⟨hQc, nx c hQc hcz⟩, addEdge_inc_old.2 haz,
      addEdge_inc_old.2 hbz, addEdge_inc_old.2 hcz, fun h => hab (Fin.castSucc_inj.1 h),
      fun h => hac (Fin.castSucc_inj.1 h), fun h => hbc (Fin.castSucc_inj.1 h), ?_⟩
    intro k hk hkz
    rcases hall k hk hkz with ⟨rfl, h | h⟩ | ⟨d, rfl, hd, _, hdz⟩
    · exact absurd h hzu
    · exact absurd h hzw
    · rcases habc d hd hdz with h | h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (by rw [h]))

end SuppData

end MGraph


/-! ===================== part 6 ===================== -/


namespace MGraph

/-! ## The exception `K₃,₃` in the suppression case: nine certificates for `T(K₃,₃, h)` -/

instance decForallFin' {n : Nat} (P : Fin n → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (∀ k (h : k < n), P ⟨k, h⟩) ⟨fun H x => H x.1 x.2, fun H k h => H ⟨k, h⟩⟩

def k33L : List (Nat × Nat) := [(0,3),(1,3),(2,3),(0,4),(1,4),(2,4),(0,5),(1,5),(2,5)]

/-- the edge list of `T(K₃,₃, h)`: delete edge `h = (s,t)`, add `s–6`, `6–t`, `6–7` -/
def tL (h : Nat) : List (Nat × Nat) :=
  let st := k33L.getD h (0, 0)
  k33L.eraseIdx h ++ [(st.1, 6), (6, st.2), (6, 7)]

/-- `T(K₃,₃, h)` on 8 vertices and 11 edges -/
def tG (h : Fin 9) : MGraph where
  n := 8
  m := 11
  ends := fun i => (⟨((tL h.val).getD i.val (0, 0)).1 % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨((tL h.val).getD i.val (0, 0)).2 % 8, Nat.mod_lt _ (by decide)⟩)

def tCs : List (List Nat) :=
  [[0, 1, 0, 2, 3, 1, 3, 4, 3, 5, 2],
   [0, 1, 1, 2, 3, 2, 4, 5, 0, 5, 2],
   [0, 1, 1, 2, 3, 3, 4, 5, 0, 4, 2],
   [0, 1, 2, 0, 3, 2, 3, 4, 3, 5, 0],
   [0, 1, 2, 1, 3, 2, 3, 4, 2, 5, 0],
   [0, 1, 2, 1, 3, 2, 4, 3, 1, 5, 0],
   [0, 1, 2, 1, 3, 4, 2, 5, 2, 4, 1],
   [0, 1, 2, 1, 3, 4, 2, 3, 2, 5, 0],
   [0, 1, 2, 1, 3, 4, 2, 4, 1, 5, 0]]

def tC (h : Fin 9) : Fin 11 → Fin 6 := fun i => ⟨(tCs.getD h.val []).getD i.val 0 % 6, Nat.mod_lt _ (by decide)⟩

theorem tG_check_0 : (tG 0).starCheck (fun _ => true) (tC 0) = true := by decide +kernel
theorem tG_check_1 : (tG 1).starCheck (fun _ => true) (tC 1) = true := by decide +kernel
theorem tG_check_2 : (tG 2).starCheck (fun _ => true) (tC 2) = true := by decide +kernel
theorem tG_check_3 : (tG 3).starCheck (fun _ => true) (tC 3) = true := by decide +kernel
theorem tG_check_4 : (tG 4).starCheck (fun _ => true) (tC 4) = true := by decide +kernel
theorem tG_check_5 : (tG 5).starCheck (fun _ => true) (tC 5) = true := by decide +kernel
theorem tG_check_6 : (tG 6).starCheck (fun _ => true) (tC 6) = true := by decide +kernel
theorem tG_check_7 : (tG 7).starCheck (fun _ => true) (tC 7) = true := by decide +kernel
theorem tG_check_8 : (tG 8).starCheck (fun _ => true) (tC 8) = true := by decide +kernel
theorem tG_check : ∀ h : Fin 9, (tG h).starCheck (fun _ => true) (tC h) = true
  | ⟨0, _⟩ => tG_check_0 | ⟨1, _⟩ => tG_check_1 | ⟨2, _⟩ => tG_check_2 | ⟨3, _⟩ => tG_check_3
  | ⟨4, _⟩ => tG_check_4 | ⟨5, _⟩ => tG_check_5 | ⟨6, _⟩ => tG_check_6 | ⟨7, _⟩ => tG_check_7
  | ⟨8, _⟩ => tG_check_8

theorem tG_star (h : Fin 9) : StarOn (G := tG h) (fun _ => True) 6 (tC h) :=
  (tG h).star_of_check (tC h) (tG_check h)

/-- vertices of `K₃,₃` inside `T(K₃,₃, h)` -/
def emb6 (a : Fin 6) : Fin 8 := ⟨a.val, by have := a.isLt; omega⟩

/-- position of the `K₃,₃` edge `j ≠ h` in `T(K₃,₃, h)` -/
def shift (h j : Fin 9) : Fin 11 := ⟨if j.val < h.val then j.val else j.val - 1, by split <;> omega⟩

theorem k33_ends_eq : ∀ j : Fin 9, k33.ends j = (⟨(k33L.getD j.val (0,0)).1 % 6, Nat.mod_lt _ (by decide)⟩,
    ⟨(k33L.getD j.val (0,0)).2 % 6, Nat.mod_lt _ (by decide)⟩) := by
  have H : ∀ j : Fin k33.m, (k33.ends j : Fin 6 × Fin 6) = (⟨(k33L.getD j.val (0,0)).1 % 6, Nat.mod_lt _ (by decide)⟩,
      ⟨(k33L.getD j.val (0,0)).2 % 6, Nat.mod_lt _ (by decide)⟩) := by decide
  exact H

theorem tG_old : ∀ h j : Fin 9, j ≠ h →
    (tG h).ends (shift h j) = (emb6 (k33.ends j).1, emb6 (k33.ends j).2) := by
  unfold tG; decide

theorem tG_8 : ∀ h : Fin 9, (tG h).ends (8 : Fin 11) = (emb6 (k33.ends h).1, (6 : Fin 8)) := by
  unfold tG; decide
theorem tG_9 : ∀ h : Fin 9, (tG h).ends (9 : Fin 11) = ((6 : Fin 8), emb6 (k33.ends h).2) := by
  unfold tG; decide
theorem tG_10 : ∀ h : Fin 9, (tG h).ends (10 : Fin 11) = ((6 : Fin 8), (7 : Fin 8)) := by
  unfold tG; decide

theorem shift_inj : ∀ h j j' : Fin 9, j ≠ h → j' ≠ h → shift h j = shift h j' → j = j' := by decide
theorem shift_lt : ∀ h j : Fin 9, (shift h j).val < 8 := by decide
theorem emb6_lt (a : Fin 6) : (emb6 a).val < 6 := a.isLt
theorem emb6_inj {a b : Fin 6} (h : emb6 a = emb6 b) : a = b := by
  have h' := congrArg Fin.val h
  exact Fin.ext h'
theorem k33_cover : ∀ a : Fin 6, ∃ e : Fin 9, k33.Inc e a := by
  have H : ∀ a : Fin k33.n, ∃ e : Fin k33.m, k33.Inc e a := by decide
  exact H
theorem k33_loop : ∀ j : Fin 9, (k33.ends j).1 ≠ (k33.ends j).2 := by decide

variable {G : MGraph}

theorem joins_of_ends {H : MGraph} {i : Fin H.m} {x y : Fin H.n} (h : H.ends i = (x, y)) : H.Joins i x y :=
  Or.inl h

/-- **`K₃,₃` exception.** If the suppressed edge set is `K₃,₃`, then `Q` embeds in `T(K₃,₃, h)`. -/
theorem k33_supp_colourable (hloop : Loopless G) {Q : Fin G.m → Prop} (S : SuppData Q)
    (hiso : IsoTo k33 (supp Q S.y S.u S.w)) : Colourable Q 6 := by
  classical
  obtain ⟨φ, ψ, hφ, hψ, hj, hP⟩ := hiso
  have hyu := S.y_ne_u hloop
  have hyw := S.y_ne_w hloop
  obtain ⟨h, hh⟩ := (hP (Fin.last G.m)).1 S.supp_new
  -- the images of the ends of `h` are `u` and `w`
  have hjh : (addEdge G S.u S.w).Joins (Fin.last G.m) (φ (k33.ends h).1) (φ (k33.ends h).2) := hh ▸ hj h
  have huw_or : (S.u = φ (k33.ends h).1 ∧ S.w = φ (k33.ends h).2) ∨
      (S.u = φ (k33.ends h).2 ∧ S.w = φ (k33.ends h).1) := @joins_unique (addEdge G S.u S.w) _ _ _ _ _ addEdge_joins_new hjh
  -- inverses
  let φinv : Fin G.n → Fin k33.n := fun v => if hv : ∃ a, φ a = v then Classical.choose hv else ⟨0, by decide⟩
  have φinv_φ : ∀ a, φinv (φ a) = a := by
    intro a
    simp only [φinv]
    split
    · next hv => exact hφ _ _ (Classical.choose_spec hv)
    · next hv => exact absurd ⟨a, rfl⟩ hv
  let ψinv : Fin (addEdge G S.u S.w).m → Fin k33.m := fun i => if hi : ∃ j, ψ j = i then Classical.choose hi else ⟨0, by decide⟩
  have ψinv_ψ : ∀ j, ψinv (ψ j) = j := by
    intro j
    have hv : ∃ j', ψ j' = ψ j := ⟨j, rfl⟩
    show (if hi : ∃ j', ψ j' = ψ j then Classical.choose hi else ⟨0, by decide⟩) = j
    rw [dif_pos hv]
    exact hψ _ _ (Classical.choose_spec hv)
  -- edges of `supp` avoid `y` and `l`
  have avoid : ∀ i x, supp Q S.y S.u S.w i → (addEdge G S.u S.w).Inc i x → x ≠ S.y ∧ x ≠ S.l := by
    intro i x hi hix
    rcases addEdge_cases i with rfl | ⟨d, rfl⟩
    · rcases (addEdge_inc_new (G := G)).1 hix with rfl | rfl
      · exact ⟨Ne.symm hyu, Ne.symm S.hlu⟩
      · exact ⟨Ne.symm hyw, Ne.symm S.hlw⟩
    · obtain ⟨hd, hdy⟩ := S.supp_old.1 hi
      exact S.not_l_of_not_y hd hdy (addEdge_inc_old.1 hix)
  have φ_avoid : ∀ a, φ a ≠ S.y ∧ φ a ≠ S.l := by
    intro a
    obtain ⟨e, he⟩ := k33_cover a
    exact avoid (ψ e) (φ a) ((hP (ψ e)).2 ⟨e, rfl⟩) (iso_inc' hj he)
  -- the vertex and edge maps
  let φQ : Fin G.n → Fin 8 := fun v => if v = S.y then 6 else if v = S.l then 7 else emb6 (φinv v)
  have φQ_y : φQ S.y = 6 := by simp [φQ]
  have φQ_φ : ∀ a, φQ (φ a) = emb6 a := by
    intro a
    have := φ_avoid a
    simp only [φQ]
    split
    · next h1 => exact absurd h1 this.1
    · split
      · next h2 => exact absurd h2 this.2
      · rw [φinv_φ]
  let A1 : Fin 11 := if S.u = φ (k33.ends h).1 then 8 else 9
  let A2 : Fin 11 := if S.u = φ (k33.ends h).1 then 9 else 8
  let ψQ : Fin G.m → Fin 11 := fun d =>
    if d = S.f1 then A1 else if d = S.f2 then A2 else if G.Inc d S.y then 10
    else shift h (ψinv (Fin.castSucc d))
  -- an old edge of `supp` is `ψ j` for some `j ≠ h`
  have oldj : ∀ d, Q d → ¬ G.Inc d S.y → ∃ j, ψ j = Fin.castSucc d ∧ j ≠ h ∧ ψinv (Fin.castSucc d) = j := by
    intro d hd hdy
    obtain ⟨j, hjd⟩ := (hP _).1 (S.supp_old.2 ⟨hd, hdy⟩)
    refine ⟨j, hjd, fun hjh' => castSucc_ne_last' d (hjd.symm.trans (hjh' ▸ hh)), ?_⟩
    rw [← hjd, ψinv_ψ]
  have hf1y : G.Inc S.f1 S.y := joins_inc_left S.hf1
  have hf2y : G.Inc S.f2 S.y := joins_inc_left S.hf2
  -- joins
  have hJ : ∀ d, Q d → ∀ x1 x2, G.Joins d x1 x2 → (tG h).Joins (ψQ d) (φQ x1) (φQ x2) := by
    intro d hd x1 x2 hdx
    -- reduce to one orientation
    suffices key : ∃ z1 z2, G.Joins d z1 z2 ∧ (tG h).Joins (ψQ d) (φQ z1) (φQ z2) by
      obtain ⟨z1, z2, hz, hT⟩ := key
      rcases joins_unique hz hdx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hT
      · rw [← h1, ← h2]; exact joins_symm hT
    by_cases hd1 : d = S.f1
    · refine ⟨S.y, S.u, hd1 ▸ S.hf1, ?_⟩
      have hψQ : ψQ d = A1 := by
        show (if d = S.f1 then A1 else _) = A1
        rw [if_pos hd1]
      rw [hψQ, φQ_y]
      rcases huw_or with ⟨hu', _⟩ | ⟨hu', _⟩
      · have hA : A1 = 8 := if_pos hu'
        rw [hA, hu', φQ_φ]; exact joins_symm (joins_of_ends (tG_8 h))
      · by_cases hc : S.u = φ (k33.ends h).1
        · -- then both ends of `h` have the same image: impossible
          exact absurd (hφ _ _ (hc.symm.trans hu')) (k33_loop h)
        · have hA : A1 = 9 := by simp [A1, hc]
          rw [hA, hu', φQ_φ]; exact joins_of_ends (tG_9 h)
    by_cases hd2 : d = S.f2
    · refine ⟨S.y, S.w, hd2 ▸ S.hf2, ?_⟩
      have hψQ : ψQ d = A2 := by
        show (if d = S.f1 then A1 else if d = S.f2 then A2 else _) = A2
        rw [if_neg hd1, if_pos hd2]
      rw [hψQ, φQ_y]
      rcases huw_or with ⟨hu', hw'⟩ | ⟨hu', hw'⟩
      · have hA : A2 = 9 := if_pos hu'
        rw [hA, hw', φQ_φ]; exact joins_of_ends (tG_9 h)
      · by_cases hc : S.u = φ (k33.ends h).1
        · exact absurd (hφ _ _ (hc.symm.trans hu')) (k33_loop h)
        · have hA : A2 = 8 := by simp [A2, hc]
          rw [hA, hw', φQ_φ]; exact joins_symm (joins_of_ends (tG_8 h))
    by_cases hdy : G.Inc d S.y
    · -- the pendant edge `y l`
      rcases S.hy d hd hdy with h1 | h1 | hjl
      · exact absurd h1 hd1
      · exact absurd h1 hd2
      refine ⟨S.y, S.l, hjl, ?_⟩
      have hψQ : ψQ d = 10 := by
        show (if d = S.f1 then A1 else if d = S.f2 then A2 else if G.Inc d S.y then 10 else _) = 10
        rw [if_neg hd1, if_neg hd2, if_pos hdy]
      have hly : S.l ≠ S.y := Ne.symm (ne_of_joins hloop hjl)
      have hφl : φQ S.l = 7 := by simp [φQ, hly]
      rw [hψQ, φQ_y, hφl]; exact joins_of_ends (tG_10 h)
    · obtain ⟨j, hjd, hjh', hinv⟩ := oldj d hd hdy
      have hψQ : ψQ d = shift h j := by
        show (if d = S.f1 then A1 else if d = S.f2 then A2 else if G.Inc d S.y then 10
          else shift h (ψinv (Fin.castSucc d))) = shift h j
        rw [if_neg hd1, if_neg hd2, if_neg hdy, hinv]
      refine ⟨φ (k33.ends j).1, φ (k33.ends j).2, addEdge_joins_old.1 (hjd ▸ hj j), ?_⟩
      rw [hψQ, φQ_φ, φQ_φ]; exact joins_of_ends (tG_old h j hjh')
  -- value bookkeeping for the edge map
  have hAv : (A1.val = 8 ∧ A2.val = 9) ∨ (A1.val = 9 ∧ A2.val = 8) := by
    by_cases hc : S.u = φ (k33.ends h).1
    · left; exact ⟨congrArg Fin.val (if_pos hc : A1 = 8), congrArg Fin.val (if_pos hc : A2 = 9)⟩
    · right; simp only [A1, A2, hc, if_false]; exact ⟨rfl, rfl⟩
  have cat : ∀ d, Q d → (d = S.f1 ∧ ψQ d = A1) ∨ (d = S.f2 ∧ ψQ d = A2) ∨
      (G.Joins d S.y S.l ∧ (ψQ d).val = 10) ∨
      (¬ G.Inc d S.y ∧ (ψQ d).val < 8 ∧ ∃ j, ψ j = Fin.castSucc d ∧ j ≠ h ∧ ψQ d = shift h j) := by
    intro d hd
    by_cases hd1 : d = S.f1
    · left; refine ⟨hd1, ?_⟩
      show (if d = S.f1 then A1 else _) = A1
      rw [if_pos hd1]
    by_cases hd2 : d = S.f2
    · right; left; refine ⟨hd2, ?_⟩
      show (if d = S.f1 then A1 else if d = S.f2 then A2 else _) = A2
      rw [if_neg hd1, if_pos hd2]
    by_cases hdy : G.Inc d S.y
    · right; right; left
      rcases S.hy d hd hdy with h1 | h1 | hjl
      · exact absurd h1 hd1
      · exact absurd h1 hd2
      refine ⟨hjl, ?_⟩
      show (if d = S.f1 then A1 else if d = S.f2 then A2 else if G.Inc d S.y then (10 : Fin 11) else _).val = 10
      rw [if_neg hd1, if_neg hd2, if_pos hdy]; rfl
    · right; right; right
      obtain ⟨j, hjd, hjh', hinv⟩ := oldj d hd hdy
      have hψQ : ψQ d = shift h j := by
        show (if d = S.f1 then A1 else if d = S.f2 then A2 else if G.Inc d S.y then 10
          else shift h (ψinv (Fin.castSucc d))) = shift h j
        rw [if_neg hd1, if_neg hd2, if_neg hdy, hinv]
      exact ⟨hdy, hψQ ▸ shift_lt h j, j, hjd, hjh', hψQ⟩
  have hψinj : ∀ a b, Q a → Q b → ψQ a = ψQ b → a = b := by
    intro a b ha hb hab
    have hv := congrArg Fin.val hab
    rcases cat a ha with ⟨ra, pa⟩ | ⟨ra, pa⟩ | ⟨ja, pa⟩ | ⟨na, la, ja, hja, hjah, pa⟩ <;>
      rcases cat b hb with ⟨rb, pb⟩ | ⟨rb, pb⟩ | ⟨jb, pb⟩ | ⟨nb, lb, jb, hjb, hjbh, pb⟩
    all_goals first
      | exact ra.trans rb.symm
      | (rw [pa, pb] at hv; omega)
      | (rw [pa] at hv; omega)
      | (rw [pb] at hv; omega)
      | omega
      | skip
    · exact (S.hl a b ha ja hb (joins_inc_right jb)).symm
    · rw [pa, pb] at hab
      have := shift_inj h ja jb hjah hjbh hab
      rw [this] at hja
      exact Fin.castSucc_inj.1 (hja.symm.trans hjb)
  -- vertices
  have img : ∀ x, x ≠ S.y → x ≠ S.l → (∃ d, Q d ∧ G.Inc d x) → ∃ a, φ a = x := by
    intro x hxy hxl ⟨d, hd, hdx⟩
    by_cases hdy : G.Inc d S.y
    · rcases S.at_y_other hd hdy hdx hxy hxl with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rcases huw_or with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact ⟨_, h1.symm⟩
        · exact ⟨_, h1.symm⟩
      · rcases huw_or with ⟨_, h1⟩ | ⟨_, h1⟩
        · exact ⟨_, h1.symm⟩
        · exact ⟨_, h1.symm⟩
    · obtain ⟨j, hjd, _, _⟩ := oldj d hd hdy
      have hjj : G.Joins d (φ (k33.ends j).1) (φ (k33.ends j).2) := addEdge_joins_old.1 (hjd ▸ hj j)
      rcases inc_of_joins hjj hdx with h1 | h1
      · exact ⟨_, h1.symm⟩
      · exact ⟨_, h1.symm⟩
  have vcat : ∀ x, (∃ d, Q d ∧ G.Inc d x) → (x = S.y ∧ φQ x = 6) ∨ (x = S.l ∧ x ≠ S.y ∧ φQ x = 7) ∨
      (∃ a, φ a = x ∧ φQ x = emb6 a) := by
    intro x hx
    by_cases hxy : x = S.y
    · left; exact ⟨hxy, by rw [hxy]; exact φQ_y⟩
    by_cases hxl : x = S.l
    · right; left; refine ⟨hxl, hxy, ?_⟩
      show (if x = S.y then (6 : Fin 8) else if x = S.l then 7 else _) = 7
      rw [if_neg hxy, if_pos hxl]
    · right; right
      obtain ⟨a, ha⟩ := img x hxy hxl hx
      exact ⟨a, ha, by rw [← ha]; exact φQ_φ a⟩
  have hφinj : ∀ x x' a b, Q a → Q b → G.Inc a x → G.Inc b x' → φQ x = φQ x' → x = x' := by
    intro x x' a b ha hb hax hbx hxx
    rcases vcat x ⟨a, ha, hax⟩ with ⟨rx, px⟩ | ⟨rx, _, px⟩ | ⟨ax, rx, px⟩ <;>
      rcases vcat x' ⟨b, hb, hbx⟩ with ⟨rx', px'⟩ | ⟨rx', _, px'⟩ | ⟨ax', rx', px'⟩ <;>
      rw [px, px'] at hxx
    · exact rx.trans rx'.symm
    · exact absurd hxx (by decide)
    · exact absurd (congrArg Fin.val hxx) (by have := emb6_lt ax'; show 6 ≠ (emb6 ax').val; omega)
    · exact absurd hxx (by decide)
    · exact rx.trans rx'.symm
    · exact absurd (congrArg Fin.val hxx) (by have := emb6_lt ax'; show 7 ≠ (emb6 ax').val; omega)
    · exact absurd (congrArg Fin.val hxx) (by have := emb6_lt ax; show (emb6 ax).val ≠ 6; omega)
    · exact absurd (congrArg Fin.val hxx) (by have := emb6_lt ax; show (emb6 ax).val ≠ 7; omega)
    · rw [← rx, ← rx', emb6_inj hxx]
  have hc := starOn_embed (G := G) (H := tG h) (Q := Q) (P := fun _ => True) φQ ψQ hφinj hψinj
    (fun _ _ => trivial) (fun a ha => hJ a ha _ _ (joins_ends a)) (tG_star h)
  exact ⟨_, hc⟩

end MGraph


/-! ===================== part 7 ===================== -/


namespace MGraph

variable {G : MGraph}

/-- **No minimal counterexample survives HOLE.** -/
theorem minimal_impossible (hH : HOLE) (hsub : Subcubic G) (hloop : Loopless G) {Q : Fin G.m → Prop}
    (hmin : MinimalCounterexample Q 6) : False := by
  classical
  have hconn : ConnectedOn Q := minimal_connected hmin
  have hcoreconn : ConnectedOn (Core Q) := minimal_core_connected hmin
  have hcut : ∀ f, Core Q f → G.CutOn Q f → False := fun f hf B => core_no_cut hsub Q hmin hf B
  -- the far end of the edge at a vertex of degree one meets the core
  have hleaf : ∀ l p y, QDeg1 Q l → Q p → G.Joins p l y → ∃ f, Core Q f ∧ G.Inc f y := by
    intro l p y hl hp hj
    have hpp : Pendant Q p := pendant_of_deg1 hl hp (joins_inc_left hj)
    obtain ⟨l', y', hj', hleaf', f, g, hf, hg, hfp, hgp, hfg, hfy, hgy⟩ := pendant_attach hsub hmin hpp
    rcases joins_unique hj' hj with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact ⟨f, hf, h2 ▸ hfy⟩
    · exfalso
      obtain ⟨a, _, _, ha⟩ := hl
      exact hfp ((ha f hf.1 (h2 ▸ hfy)).trans (ha p hp (joins_inc_left hj)).symm)
  have hdeg2 : ∀ x, QDeg2 Q x → ∃ f, Core Q f ∧ G.Inc f x := by
    intro x hx
    obtain ⟨a, b, hQa, hQb, hax, hbx, hab, habd⟩ := id hx
    by_cases hac : Core Q a
    · exact ⟨a, hac, hax⟩
    · have hpa : Pendant Q a := Classical.byContradiction fun hp => hac ⟨hQa, hp⟩
      obtain ⟨z, haz, hz1⟩ := deg1_of_pendant hpa
      have hzx : z ≠ x := fun h => qdeg1_not2 (h ▸ hz1) hx
      exact hleaf z a x hz1 hQa (joins_of_inc_ne haz hax hzx)
  -- `Q` has an edge
  obtain ⟨e0, he0⟩ : ∃ f, Q f := by
    apply Classical.byContradiction
    intro h
    apply hmin.1
    exact ⟨fun _ => 0, fun a _ _ ha _ => absurd ⟨a, ha⟩ h, fun w h1 _ _ _ => absurd ⟨w.e1, h1⟩ h⟩
  -- the core edges are the edges of `Q` whose ends both have degree three
  have core_of_deg3 : ∀ f, Q f → (∀ x, G.Inc f x → QDeg3 Q x) → Core Q f := by
    intro f hf h3
    refine ⟨hf, fun hp => ?_⟩
    obtain ⟨x, hfx, hx1⟩ := deg1_of_pendant hp
    exact qdeg1_not3 hx1 (h3 x hfx)
  by_cases hR0 : ∃ r, QDeg1 Q r ∨ QDeg2 Q r
  · by_cases hR2 : ∃ r1 r2, r1 ≠ r2 ∧ (QDeg1 Q r1 ∨ QDeg2 Q r1) ∧ (QDeg1 Q r2 ∨ QDeg2 Q r2)
    · -- two vertices of degree ≤ 2: double `Q`
      obtain ⟨r1, r2, hr, hr1, hr2⟩ := hR2
      have hL := dbl.loopless hloop
      have hC := dblP_connected hconn hr1
      have hB := dblP_bridgeless hcoreconn hcut hleaf hdeg2 hr hr1 hr2
      have hK := dblP_cubic hsub Q
      obtain ⟨c, hc⟩ : Colourable (dblP Q) 6 := by
        by_cases hiso : IsoTo k33 (dblP Q)
        · exact k33_colourable hiso
        · have ht : G.Inc e0 (G.ends e0).1 := joins_inc_left (joins_ends e0)
          obtain ⟨c, _, hc, -⟩ := hH (dbl G) (dblP Q) hL hC hB hK hiso (dbl.vo (G.ends e0).1)
            ⟨dbl.eo e0, dblP_eo.2 he0, dbl.inc_eo_vo.2 ht⟩
          exact ⟨c, hc⟩
      apply hmin.1
      exact ⟨_, starOn_embed (G := G) (H := dbl G) (Q := Q) (P := dblP Q) dbl.vo dbl.eo
        (fun _ _ _ _ _ _ _ _ h => dbl.vo_inj h) (fun _ _ _ _ h => dbl.eo_inj h) (fun _ ha => dblP_eo.2 ha)
        (fun a _ => dbl.joins_eo (joins_ends a)) hc⟩
    · -- exactly one vertex `r` of degree ≤ 2: suppress it
      obtain ⟨r, hr⟩ := hR0
      have huniq : ∀ r', (QDeg1 Q r' ∨ QDeg2 Q r') → r' = r := fun r' hr' =>
        Classical.byContradiction fun hne => hR2 ⟨r', r, hne, hr', hr⟩
      have deg3_of : ∀ x, x ≠ r → (∃ f, Q f ∧ G.Inc f x) → QDeg3 Q x := by
        intro x hxr hx
        rcases qdeg_cases hsub Q hx with h1 | h2 | h3
        · exact absurd (huniq x (Or.inl h1)) hxr
        · exact absurd (huniq x (Or.inr h2)) hxr
        · exact h3
      have hS : Nonempty (SuppData Q) := by
        rcases hr with h1 | h2
        · -- `r` is a leaf `l` with pendant edge `p = l y`
          obtain ⟨p, hp, hpl, hpall⟩ := id h1
          obtain ⟨y, hjy⟩ := exists_joins_of_inc hpl
          have hjp : G.Joins p r y := joins_symm hjy
          have hyr : y ≠ r := Ne.symm (ne_of_joins hloop hjp)
          have hy3 : QDeg3 Q y := deg3_of y hyr ⟨p, hp, joins_inc_right hjp⟩
          obtain ⟨x1, x2, hQx1, hQx2, hx1y, hx2y, hx12, hx1p, hx2p, hally⟩ :=
            three_minus_one hy3 hp (joins_inc_right hjp)
          obtain ⟨u, hju⟩ := exists_joins_of_inc hx1y
          obtain ⟨w, hjw⟩ := exists_joins_of_inc hx2y
          have hru : r ≠ u := fun h => hx1p (hpall x1 hQx1 (h ▸ joins_inc_left hju))
          have hrw : r ≠ w := fun h => hx2p (hpall x2 hQx2 (h ▸ joins_inc_left hjw))
          exact ⟨
            { y := y, u := u, w := w, l := r, f1 := x1, f2 := x2
              hf1 := joins_symm hju, hf2 := joins_symm hjw, hQ1 := hQx1, hQ2 := hQx2, hf12 := hx12
              hy := fun d hd hdy => by
                rcases hally d hd hdy with h | h | h
                · exact Or.inr (Or.inr (h ▸ joins_symm hjp))
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
              hl := fun d d' hd hjd hd' hd'l =>
                (hpall d' hd' hd'l).trans (hpall d hd (joins_inc_right hjd)).symm
              hlu := hru, hlw := hrw
              hlleaf := Or.inr fun d hd hdl => (hpall d hd hdl) ▸ joins_symm hjp
              hrest := fun x hxy hxl hx => deg3_of x hxl hx }⟩
        · -- `r` is a vertex `y` of degree two
          obtain ⟨a, b, hQa, hQb, hay, hby, hab, habd⟩ := id h2
          obtain ⟨u, hju⟩ := exists_joins_of_inc hay
          obtain ⟨w, hjw⟩ := exists_joins_of_inc hby
          exact ⟨
            { y := r, u := u, w := w, l := r, f1 := a, f2 := b
              hf1 := joins_symm hju, hf2 := joins_symm hjw, hQ1 := hQa, hQ2 := hQb, hf12 := hab
              hy := fun d hd hdy => by
                rcases habd d hd hdy with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
              hl := fun d _ _ hjd _ _ => absurd rfl (ne_of_joins hloop hjd)
              hlu := ne_of_joins hloop (joins_symm hju)
              hlw := ne_of_joins hloop (joins_symm hjw)
              hlleaf := Or.inl rfl
              hrest := fun x hxy _ hx => deg3_of x hxy hx }⟩
      obtain ⟨S⟩ := hS
      have hyl3 : ∀ x, x ≠ S.y → x ≠ S.l → (∃ f, Q f ∧ G.Inc f x) → QDeg3 Q x := S.hrest
      -- edges of `Q` avoiding `y` are core edges
      have coreNotY : ∀ f, Q f → ¬ G.Inc f S.y → Core Q f := by
        intro f hf hfy
        apply core_of_deg3 f hf
        intro x hfx
        have := S.not_l_of_not_y hf hfy hfx
        exact hyl3 x this.1 this.2 ⟨f, hf, hfx⟩
      have hcutQ' : ∀ f, Q f → ¬ G.Inc f S.y → G.CutOn Q f → False :=
        fun f hf hfy B => hcut f (coreNotY f hf hfy) B
      have huw : S.u ≠ S.w := S.u_ne_w hloop hcutQ'
      have hyw := S.y_ne_w hloop
      have hf2core : Core Q S.f2 := by
        have hw3 : QDeg3 Q S.w := hyl3 S.w (Ne.symm hyw) (Ne.symm S.hlw) ⟨S.f2, S.hQ2, joins_inc_right S.hf2⟩
        obtain ⟨x1, _, hQx1, _, hx1w, _, _, hx1f, _, _⟩ := three_minus_one hw3 S.hQ2 (joins_inc_right S.hf2)
        exact ⟨S.hQ2, not_pendant_of_two S.hf2 S.hQ1 S.hf12 (joins_inc_left S.hf1) hQx1 hx1f hx1w⟩
      have hcutQ'' : ∀ f, Q f → (f = S.f2 ∨ ¬ G.Inc f S.y) → G.CutOn Q f → False := by
        intro f hf hcase B
        rcases hcase with rfl | hfy
        · exact hcut _ hf2core B
        · exact hcut f (coreNotY f hf hfy) B
      have hL := addEdge_loopless hloop huw
      have hC := S.supp_connected hloop hconn
      have hB := S.supp_bridgeless hloop hcutQ''
      have hK := S.supp_cubic hloop huw
      apply hmin.1
      by_cases hiso : IsoTo k33 (supp Q S.y S.u S.w)
      · exact k33_supp_colourable hloop S hiso
      · obtain ⟨c2, β, hc2, hhole⟩ := hH (addEdge G S.u S.w) (supp Q S.y S.u S.w) hL hC hB hK hiso S.w
          ⟨Fin.last G.m, S.supp_new, addEdge_inc_new.2 (Or.inr rfl)⟩
        exact hole_extend hsub hloop S.hf1 S.hf2 huw S.hQ1 S.hQ2 S.hy S.hl S.hlu S.hlw c2 β hc2 hhole
  · -- no vertex of degree ≤ 2: `Q` itself is cubic
    have hK : CubicOn Q := by
      intro x hx
      rcases qdeg_cases hsub Q hx with h1 | h2 | h3
      · exact absurd ⟨x, Or.inl h1⟩ hR0
      · exact absurd ⟨x, Or.inr h2⟩ hR0
      · exact h3
    have hB : BridgelessOn Q := by
      intro f hf B
      by_cases hfc : Core Q f
      · exact hcut f hfc B
      · obtain ⟨x, _, hx1⟩ := deg1_of_pendant (Classical.byContradiction fun hp => hfc ⟨hf, hp⟩)
        exact hR0 ⟨x, Or.inl hx1⟩
    apply hmin.1
    by_cases hiso : IsoTo k33 Q
    · exact k33_colourable hiso
    · obtain ⟨c, _, hc, -⟩ := hH G Q hloop hconn hB hK hiso (G.ends e0).1
        ⟨e0, he0, joins_inc_left (joins_ends e0)⟩
      exact ⟨c, hc⟩

/-- **HOLE implies DMS.** If every connected, bridgeless, loopless cubic multigraph other than K₃,₃ has, at every
    vertex `t`, a star 6-colouring missing some colour on all edges at `N[t]`, then every loopless subcubic
    multigraph is star 6-edge-colourable. -/
theorem dms_of_hole (hH : HOLE) :
    ∀ (G : MGraph), Subcubic G → Loopless G → ∀ P : Fin G.m → Prop, Colourable P 6 := by
  intro G hsub hloop P
  apply Classical.byContradiction
  intro hP
  obtain ⟨Q, -, hmin⟩ := exists_minimal 6 P hP
  exact minimal_impossible hH hsub hloop hmin

end MGraph
