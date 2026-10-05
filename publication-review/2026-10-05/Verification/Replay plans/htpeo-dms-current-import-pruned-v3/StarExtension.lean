/-
  StarExtension.lean — the weakest matching-extension lemma that proves DMS from the minimal-counterexample structure.

  A star 6-colouring is the same thing as a matching `M` (the class of the sixth colour) together with a star
  5-colouring of the rest that is *relatively rainbow* at `M`: the only walks that can be bicoloured across the two
  palettes are `M, F, M, F` walks — two matching edges joined by an edge `b`, with a further edge `d` beyond the
  second — and they are killed iff `c b ≠ c d`.  Compared with `Rainbow` (§ StarMatching) nothing is asked at a
  matching edge whose neighbourhood carries no other matching edge.

    `Walk4.reverse`             a walk read backwards
    `RelRainbow`                the relative rainbow condition (walks `M, F, M, F`)
    `starOn_compose_rel`        StarOn F k cF + matching M + RelRainbow  ⟹  StarOn (F ∪ M) (k+1), M ↦ last colour
    `relRainbow_of_star`        conversely every star (k+1)-colouring whose last class is `M` is relatively rainbow
    `colourable_iff_matching`   Colourable P (k+1) ⟺ ∃ matching M ⊆ P, ∃ star k-colouring of P − M relatively
                                rainbow at M  — the matching-extension lemma with an unrestricted matching is DMS itself
    `dms_of_matching_extension` the form used in the induction: if every edge set without a two-sided bridge admits
                                such a pair (M, cF) with five colours, every subcubic multigraph is star 6-colourable

  No `sorry`, standard axioms only.
-/
import StarVizing
import StarBottleneck

namespace MGraph
variable {G : MGraph}

namespace Walk4
variable (w : G.Walk4)

/-- the walk read backwards -/
def reverse : G.Walk4 :=
  { v0 := w.v4
    v1 := w.v3
    v2 := w.v2
    v3 := w.v1
    v4 := w.v0
    e1 := w.e4
    e2 := w.e3
    e3 := w.e2
    e4 := w.e1
    h1 := joins_symm' w.h4
    h2 := joins_symm' w.h3
    h3 := joins_symm' w.h2
    h4 := joins_symm' w.h1
    d01 := fun h => w.d34 h.symm
    d02 := fun h => w.d24 h.symm
    d03 := fun h => w.d14 h.symm
    d12 := fun h => w.d23 h.symm
    d13 := fun h => w.d13 h.symm
    d14 := fun h => w.d03 h.symm
    d23 := fun h => w.d12 h.symm
    d24 := fun h => w.d02 h.symm
    d34 := fun h => w.d01 h.symm }

end Walk4

/-- **Relative rainbow-ness.**  Only walks `M, F, M, F` are constrained: the two `F`-edges of such a walk get
    different colours. -/
def RelRainbow (F M : Fin G.m → Prop) {k : Nat} (cF : Fin G.m → Fin k) : Prop :=
  ∀ w : G.Walk4, M w.e1 → F w.e2 → ¬ M w.e2 → M w.e3 → F w.e4 → ¬ M w.e4 → cF w.e2 ≠ cF w.e4

theorem castSucc_ne_last' {k : Nat} (i : Fin k) : Fin.castSucc i ≠ Fin.last k := by
  intro h
  have h' : i.val = k := congrArg Fin.val h
  exact absurd h' (Nat.ne_of_lt i.isLt)

theorem castSucc_inj'' {k : Nat} {i j : Fin k} (h : Fin.castSucc i = Fin.castSucc j) : i = j := by
  have h' := congrArg Fin.val h
  exact Fin.ext h'

open Classical in
/-- **The matching-extension composition.**  A star `k`-colouring of `F`, a matching `M` and relative rainbow-ness
    give a star `(k+1)`-colouring of `F ∪ M` with `M` as the last colour class. -/
theorem starOn_compose_rel {F M : Fin G.m → Prop} {k : Nat} (cF : Fin G.m → Fin k)
    (hF : StarOn F k cF)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hrel : RelRainbow F M cF) :
    StarOn (fun f => F f ∨ M f) (k + 1) (fun f => if M f then Fin.last k else Fin.castSucc (cF f)) := by
  constructor
  · intro a b hab ha hb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    by_cases hma : M a <;> by_cases hmb : M b
    · exact hmatch a b hma hmb hne x hax hbx
    · simp only [if_pos hma, if_neg hmb] at heq; exact castSucc_ne_last' _ heq.symm
    · simp only [if_neg hma, if_pos hmb] at heq; exact castSucc_ne_last' _ heq
    · simp only [if_neg hma, if_neg hmb] at heq
      exact hF.1 a b ⟨hne, x, hax, hbx⟩ (ha.resolve_right hma) (hb.resolve_right hmb) (castSucc_inj'' heq)
  · intro w h1 h2 h3 h4 hb
    rcases hb with ⟨hb13, hb24⟩
    by_cases m1 : M w.e1 <;> by_cases m3 : M w.e3
    · by_cases m2 : M w.e2
      · exact hmatch w.e1 w.e2 m1 m2 w.e1_ne_e2 w.v1 w.inc_e1_v1 w.inc_e2_v1
      by_cases m4 : M w.e4
      · exact hmatch w.e3 w.e4 m3 m4 w.e3_ne_e4 w.v3 w.inc_e3_v3 w.inc_e4_v3
      simp only [if_neg m2, if_neg m4] at hb24
      exact hrel w m1 (h2.resolve_right m2) m2 m3 (h4.resolve_right m4) m4 (castSucc_inj'' hb24)
    · simp only [if_pos m1, if_neg m3] at hb13; exact castSucc_ne_last' _ hb13.symm
    · simp only [if_neg m1, if_pos m3] at hb13; exact castSucc_ne_last' _ hb13
    · simp only [if_neg m1, if_neg m3] at hb13
      by_cases m2 : M w.e2 <;> by_cases m4 : M w.e4
      · -- the walk F, M, F, M read backwards is M, F, M, F
        exact hrel w.reverse m4 (h3.resolve_right m3) m3 m2 (h1.resolve_right m1) m1
          (castSucc_inj'' hb13).symm
      · simp only [if_pos m2, if_neg m4] at hb24; exact castSucc_ne_last' _ hb24.symm
      · simp only [if_neg m2, if_pos m4] at hb24; exact castSucc_ne_last' _ hb24
      · simp only [if_neg m2, if_neg m4] at hb24
        exact hF.2 w (h1.resolve_right m1) (h2.resolve_right m2) (h3.resolve_right m3)
          (h4.resolve_right m4) ⟨castSucc_inj'' hb13, castSucc_inj'' hb24⟩

/-- **Necessity.**  Forgetting the last colour of a star `(k+1)`-colouring of `P` gives a colouring of `P − M`
    (`M` = the last colour class) that is relatively rainbow at `M`. -/
theorem relRainbow_of_star {P : Fin G.m → Prop} {k : Nat} (c : Fin G.m → Fin (k + 1))
    (hc : StarOn P (k + 1) c) (cF : Fin G.m → Fin k)
    (hcF : ∀ f, P f → c f ≠ Fin.last k → Fin.castSucc (cF f) = c f) :
    RelRainbow (fun f => P f ∧ c f ≠ Fin.last k) (fun f => P f ∧ c f = Fin.last k) cF := by
  intro w m1 h2 _ m3 h4 _ heq
  apply hc.2 w m1.1 h2.1 m3.1 h4.1
  constructor
  · rw [m1.2, m3.2]
  · rw [← hcF _ h2.1 h2.2, ← hcF _ h4.1 h4.2, heq]

open Classical in
/-- **The matching-extension lemma with an unrestricted matching is colourability itself.**
    `P` is star `(k+1)`-colourable iff some matching `M ⊆ P` admits a star `k`-colouring of `P − M` that is
    relatively rainbow at `M`. -/
theorem colourable_iff_matching (P : Fin G.m → Prop) (k : Nat) (hk : 0 < k) :
    Colourable P (k + 1) ↔
      ∃ M : Fin G.m → Prop, (∀ f, M f → P f) ∧
        (∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False) ∧
        ∃ cF : Fin G.m → Fin k, StarOn (fun f => P f ∧ ¬ M f) k cF ∧ RelRainbow (fun f => P f ∧ ¬ M f) M cF := by
  constructor
  · intro ⟨c, hc⟩
    let M : Fin G.m → Prop := fun f => P f ∧ c f = Fin.last k
    let cF : Fin G.m → Fin k := fun f => ⟨(c f).val % k, Nat.mod_lt _ hk⟩
    have hcF : ∀ f, P f → c f ≠ Fin.last k → Fin.castSucc (cF f) = c f := by
      intro f _ hne
      apply Fin.ext
      show (c f).val % k = (c f).val
      apply Nat.mod_eq_of_lt
      have hlt : (c f).val < k + 1 := (c f).isLt
      have hne' : (c f).val ≠ k := fun h => hne (Fin.ext h)
      omega
    have hne : ∀ f, P f → ¬ M f → c f ≠ Fin.last k := fun f hf hm h => hm ⟨hf, h⟩
    refine ⟨M, fun f hf => hf.1, ?_, cF, ?_, ?_⟩
    · intro a b ha hb hne' x hax hbx
      exact hc.1 a b ⟨hne', x, hax, hbx⟩ ha.1 hb.1 (ha.2.trans hb.2.symm)
    · constructor
      · intro a b hab ha hb heq
        apply hc.1 a b hab ha.1 hb.1
        rw [← hcF a ha.1 (hne a ha.1 ha.2), ← hcF b hb.1 (hne b hb.1 hb.2), heq]
      · intro w h1 h2 h3 h4 hb
        apply hc.2 w h1.1 h2.1 h3.1 h4.1
        exact ⟨by rw [← hcF _ h1.1 (hne _ h1.1 h1.2), ← hcF _ h3.1 (hne _ h3.1 h3.2), hb.1],
          by rw [← hcF _ h2.1 (hne _ h2.1 h2.2), ← hcF _ h4.1 (hne _ h4.1 h4.2), hb.2]⟩
    · -- relative rainbow-ness: the predicates agree with those of `relRainbow_of_star`
      intro w m1 h2 nm2 m3 h4 nm4 heq
      exact relRainbow_of_star c hc cF hcF w m1 ⟨h2.1, hne _ h2.1 h2.2⟩ (fun h => nm2 h) m3
        ⟨h4.1, hne _ h4.1 h4.2⟩ (fun h => nm4 h) heq
  · intro ⟨M, hMP, hmatch, cF, hF, hrel⟩
    exact ⟨_, starOn_mono (fun f hf => by
      by_cases hm : M f
      · exact Or.inr hm
      · exact Or.inl ⟨hf, hm⟩) (starOn_compose_rel cF hF hmatch hrel)⟩

/-- **DMS from the matching-extension lemma.**  If every edge set without a two-sided bridge admits a matching
    `M` and a star 5-colouring of the rest that is relatively rainbow at `M`, then every subcubic multigraph is
    star 6-colourable.  (With `M` unrestricted this hypothesis is just 6-colourability of those edge sets, by
    `colourable_iff_matching`; the content of a matching-extension *lemma* lies in the restriction it puts on `M` —
    for instance that `M` contain the pendant edges, or be a perfect matching.) -/
theorem dms_of_matching_extension (hsub : Subcubic G)
    (L : ∀ P : Fin G.m → Prop, ¬ HasTwoSidedBridge P →
      ∃ M : Fin G.m → Prop, (∀ f, M f → P f) ∧
        (∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False) ∧
        ∃ cF : Fin G.m → Fin 5, StarOn (fun f => P f ∧ ¬ M f) 5 cF ∧ RelRainbow (fun f => P f ∧ ¬ M f) M cF) :
    ∀ P : Fin G.m → Prop, Colourable P 6 :=
  dms_reduction hsub (fun P hP => (colourable_iff_matching P 5 (by decide)).2 (L P hP))

/-- **The weakest pendant-matching form.**  The same, with `M` required to contain every pendant edge of `P`: the
    matching that the minimal-counterexample structure suggests (pendant edges get the sixth colour together). -/
theorem dms_of_pendant_matching (hsub : Subcubic G)
    (L : ∀ P : Fin G.m → Prop, ¬ HasTwoSidedBridge P →
      ∃ M : Fin G.m → Prop, (∀ f, M f → P f) ∧ (∀ f, Pendant P f → M f) ∧
        (∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False) ∧
        ∃ cF : Fin G.m → Fin 5, StarOn (fun f => P f ∧ ¬ M f) 5 cF ∧ RelRainbow (fun f => P f ∧ ¬ M f) M cF) :
    ∀ P : Fin G.m → Prop, Colourable P 6 :=
  dms_of_matching_extension hsub (fun P hP => by
    obtain ⟨M, hMP, _, hmatch, cF, hF, hrel⟩ := L P hP
    exact ⟨M, hMP, hmatch, cF, hF, hrel⟩)

/-- **The rainbow-free form.**  If the matching `M` is *walk-induced* — no walk of `P` has matching edges in
    positions 1 and 3 (no edge of `P − M` joins two `M`-edges that continue beyond) — relative rainbow-ness is
    vacuous, and the lemma asks only that `P − M` be star 5-colourable.  This is the weakest form in which the
    matching costs nothing beyond 5-colourability of what remains. -/
theorem dms_of_induced_matching (hsub : Subcubic G)
    (L : ∀ P : Fin G.m → Prop, ¬ HasTwoSidedBridge P →
      ∃ M : Fin G.m → Prop, (∀ f, M f → P f) ∧ (∀ f, Pendant P f → M f) ∧
        (∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False) ∧
        (∀ w : G.Walk4, M w.e1 → M w.e3 → False) ∧
        Colourable (fun f => P f ∧ ¬ M f) 5) :
    ∀ P : Fin G.m → Prop, Colourable P 6 :=
  dms_of_pendant_matching hsub (fun P hP => by
    obtain ⟨M, hMP, hpend, hmatch, hind, cF, hF⟩ := L P hP
    exact ⟨M, hMP, hpend, hmatch, cF, hF, fun w m1 _ _ m3 _ _ _ => hind w m1 m3⟩)

end MGraph
