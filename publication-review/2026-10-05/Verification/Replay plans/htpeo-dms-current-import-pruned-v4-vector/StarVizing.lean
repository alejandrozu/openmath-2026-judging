/-
  StarVizing.lean — the Vizing-style toolkit for the matching-class scheme: when does a Kempe swap preserve the
  star (straddle) invariant, and how does a partial star colouring extend by one edge.

    `kempe`                the transposition of two colours on a set `S` of edges
    `kempe_swap_starOn`    **safe-swap lemma**: if `S` is a union of components of the `(a,b)`-subgraph and no window
                           is *split* (a walk `e1 e2 e3 e4` with `c e2 = c e4` and `{c e1, c e3} = {a, b}` has `e1`,
                           `e3` both in `S` or both outside, and likewise for the other parity), then the swapped
                           colouring is again star on `P`.  The split-window condition is exactly what the
                           straddle invariant costs beyond Vizing's properness.
    `starOn_extend`        the greedy step: an uncoloured edge takes a colour absent from its neighbours that closes
                           no bicoloured window.

  The certificate `StarVizingCert.lean` shows that these two moves (fan recolouring + one Kempe pair) are not enough
  for an induction: a partial colouring satisfying the invariant that no such move completes.
  No `sorry`, standard axioms only.
-/
import StarMatching

namespace MGraph
variable {G : MGraph}

theorem adj_symm {a b : Fin G.m} (h : G.Adj a b) : G.Adj b a := by
  rcases h with ⟨hne, x, hax, hbx⟩
  exact ⟨fun h' => hne h'.symm, x, hbx, hax⟩

open Classical in
/-- Kempe recolouring: transpose the colours `a`, `b` on the edges of `S`, leave the others alone. -/
noncomputable def kempe {k : Nat} (c : Fin G.m → Fin k) (S : Fin G.m → Prop) (a b : Fin k) : Fin G.m → Fin k :=
  fun f => if S f then swap a b (c f) else c f

open Classical in
/-- two edges receive the same colour after the swap iff they had the same colour, or exactly one of them was
    swapped and their colours were `{a, b}` (a *split* pair). -/
theorem kempe_eq {k : Nat} {c : Fin G.m → Fin k} {S : Fin G.m → Prop} {a b : Fin k}
    (hS : ∀ f, S f → c f = a ∨ c f = b) {p q : Fin G.m}
    (h : kempe c S a b p = kempe c S a b q) :
    c p = c q ∨ ((S p ∧ ¬ S q ∨ ¬ S p ∧ S q) ∧ (c p = a ∧ c q = b ∨ c p = b ∧ c q = a)) := by
  unfold kempe at h
  by_cases sp : S p <;> by_cases sq : S q
  · simp only [if_pos sp, if_pos sq] at h; exact Or.inl (swap_inj h)
  · simp only [if_pos sp, if_neg sq] at h
    rcases hS p sp with hp | hp
    · rw [hp, swap_a] at h; exact Or.inr ⟨Or.inl ⟨sp, sq⟩, Or.inl ⟨hp, h.symm⟩⟩
    · rw [hp, swap_b] at h; exact Or.inr ⟨Or.inl ⟨sp, sq⟩, Or.inr ⟨hp, h.symm⟩⟩
  · simp only [if_neg sp, if_pos sq] at h
    rcases hS q sq with hq | hq
    · rw [hq, swap_a] at h; exact Or.inr ⟨Or.inr ⟨sp, sq⟩, Or.inr ⟨h, hq⟩⟩
    · rw [hq, swap_b] at h; exact Or.inr ⟨Or.inr ⟨sp, sq⟩, Or.inl ⟨h, hq⟩⟩
  · simp only [if_neg sp, if_neg sq] at h; exact Or.inl h

open Classical in
/-- **Safe-swap lemma.**  Let `c` be a star `k`-colouring of `P`, `a ≠ b` two colours, and `S ⊆ P` a set of
    `(a,b)`-coloured edges closed under `(a,b)`-adjacency (a union of Kempe components).  If no window of `P` is
    split by `S` — for every walk `e1 e2 e3 e4` in `P` with `c e2 = c e4` and `{c e1, c e3} = {a, b}` the edges
    `e1`, `e3` are both in `S` or both outside, and symmetrically for `e2`, `e4` when `c e1 = c e3` — then the
    swapped colouring is star on `P`. -/
theorem kempe_swap_starOn {P : Fin G.m → Prop} {k : Nat} (c : Fin G.m → Fin k) (S : Fin G.m → Prop)
    (a b : Fin k) (hc : StarOn P k c)
    (hS : ∀ f, S f → P f ∧ (c f = a ∨ c f = b))
    (hclosed : ∀ f g, S f → P g → G.Adj f g → (c g = a ∨ c g = b) → S g)
    (hsplit13 : ∀ w : G.Walk4, P w.e1 → P w.e2 → P w.e3 → P w.e4 → c w.e2 = c w.e4 →
      (c w.e1 = a ∧ c w.e3 = b ∨ c w.e1 = b ∧ c w.e3 = a) → (S w.e1 ↔ S w.e3))
    (hsplit24 : ∀ w : G.Walk4, P w.e1 → P w.e2 → P w.e3 → P w.e4 → c w.e1 = c w.e3 →
      (c w.e2 = a ∧ c w.e4 = b ∨ c w.e2 = b ∧ c w.e4 = a) → (S w.e2 ↔ S w.e4)) :
    StarOn P k (kempe c S a b) := by
  have hS' : ∀ f, S f → c f = a ∨ c f = b := fun f hf => (hS f hf).2
  constructor
  · intro f g hadj hf hg heq
    rcases kempe_eq hS' heq with h | ⟨hsplit, hcol⟩
    · exact hc.1 f g hadj hf hg h
    · have hga : c g = a ∨ c g = b := by
        rcases hcol with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr h2
        · exact Or.inl h2
      have hfa : c f = a ∨ c f = b := by
        rcases hcol with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1
        · exact Or.inr h1
      rcases hsplit with ⟨sf, sg⟩ | ⟨sf, sg⟩
      · exact sg (hclosed f g sf hg hadj hga)
      · exact sf (hclosed g f sg hf (adj_symm hadj) hfa)
  · intro w h1 h2 h3 h4 hb
    rcases hb with ⟨hb13, hb24⟩
    have c13 := kempe_eq hS' hb13
    have c24 := kempe_eq hS' hb24
    -- membership of the four edges in {a, b} when split
    have inab : ∀ {p q : Fin G.m}, (c p = a ∧ c q = b ∨ c p = b ∧ c q = a) →
        (c p = a ∨ c p = b) ∧ (c q = a ∨ c q = b) := by
      intro p q h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Or.inl h1, Or.inr h2⟩
      · exact ⟨Or.inr h1, Or.inl h2⟩
    rcases c13 with e13 | ⟨s13, col13⟩ <;> rcases c24 with e24 | ⟨s24, col24⟩
    · exact hc.2 w h1 h2 h3 h4 ⟨e13, e24⟩
    · -- e1, e3 equal; e2, e4 split
      have hiff := hsplit24 w h1 h2 h3 h4 e13 col24
      rcases s24 with ⟨sa, sb⟩ | ⟨sa, sb⟩
      · exact sb (hiff.1 sa)
      · exact sa (hiff.2 sb)
    · have hiff := hsplit13 w h1 h2 h3 h4 e24 col13
      rcases s13 with ⟨sa, sb⟩ | ⟨sa, sb⟩
      · exact sb (hiff.1 sa)
      · exact sa (hiff.2 sb)
    · -- both pairs split: all four edges are (a,b)-coloured and consecutive ones are adjacent, so `S` is
      -- constant along the walk by closure — contradicting the split of e1, e3
      have ab1 := (inab col13).1
      have ab2 := (inab col24).1
      have ab3 := (inab col13).2
      have ab4 := (inab col24).2
      have adj12 : G.Adj w.e1 w.e2 := ⟨w.e1_ne_e2, w.v1, w.inc_e1_v1, w.inc_e2_v1⟩
      have adj23 : G.Adj w.e2 w.e3 := ⟨w.e2_ne_e3, w.v2, w.inc_e2_v2, w.inc_e3_v2⟩
      have s12 : S w.e1 → S w.e2 := fun h => hclosed _ _ h h2 adj12 ab2
      have s21 : S w.e2 → S w.e1 := fun h => hclosed _ _ h h1 (adj_symm adj12) ab1
      have s23 : S w.e2 → S w.e3 := fun h => hclosed _ _ h h3 adj23 ab3
      have s32 : S w.e3 → S w.e2 := fun h => hclosed _ _ h h2 (adj_symm adj23) ab2
      have _ := ab4
      rcases s13 with ⟨sa, sb⟩ | ⟨sa, sb⟩
      · exact sb (s23 (s12 sa))
      · exact sa (s21 (s32 sb))

/-- **The greedy step.**  A star colouring of `P` extends to `P ∪ {e}` when the colour of `e` differs from the
    colours of its `P`-neighbours and no walk through `e` (with its other edges in `P`) is bicoloured. -/
theorem starOn_extend {P : Fin G.m → Prop} {k : Nat} (c : Fin G.m → Fin k) (hc : StarOn P k c) (e : Fin G.m)
    (hprop : ∀ f, P f → G.Adj e f → c f ≠ c e)
    (hwalk : ∀ w : G.Walk4, (w.e1 = e ∨ w.e2 = e ∨ w.e3 = e ∨ w.e4 = e) →
      (∀ f, (f = w.e1 ∨ f = w.e2 ∨ f = w.e3 ∨ f = w.e4) → f ≠ e → P f) → ¬ Bicol c w) :
    StarOn (fun f => P f ∨ f = e) k c := by
  constructor
  · intro f g hadj hf hg heq
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact hc.1 f g hadj hf hg heq
    · rw [hg] at hadj heq; exact hprop f hf (adj_symm hadj) heq
    · rw [hf] at hadj heq; exact hprop g hg hadj heq.symm
    · exact hadj.1 (hf.trans hg.symm)
  · intro w h1 h2 h3 h4 hb
    by_cases he : w.e1 = e ∨ w.e2 = e ∨ w.e3 = e ∨ w.e4 = e
    · apply hwalk w he _ hb
      intro f hf hfe
      rcases hf with hf | hf | hf | hf <;> rw [hf] at hfe ⊢
      · exact h1.resolve_right hfe
      · exact h2.resolve_right hfe
      · exact h3.resolve_right hfe
      · exact h4.resolve_right hfe
    · have n1 : w.e1 ≠ e := fun h => he (Or.inl h)
      have n2 : w.e2 ≠ e := fun h => he (Or.inr (Or.inl h))
      have n3 : w.e3 ≠ e := fun h => he (Or.inr (Or.inr (Or.inl h)))
      have n4 : w.e4 ≠ e := fun h => he (Or.inr (Or.inr (Or.inr h)))
      exact hc.2 w (h1.resolve_right n1) (h2.resolve_right n2) (h3.resolve_right n3) (h4.resolve_right n4) hb

/-! ### the shape of a Vizing-type induction -/

/-- `Colourable (fun _ => False) k` for every `k ≥ 1` — the empty edge set. -/
theorem colourable_empty (k : Nat) (hk : 0 < k) : Colourable (G := G) (fun _ => False) k :=
  ⟨fun _ => ⟨0, hk⟩, fun _ _ _ h => h.elim, fun _ h => h.elim⟩

/-- **What a Vizing-type induction needs, exactly.**  An edge set `F` is star `k`-colourable iff every nonempty
    sub-structure `P ⊆ F` has a *good* edge `e`: one for which colourability of `P − e` implies colourability of
    `P`.  (For the full structure of a colourable graph every edge is trivially good; the content of the extension
    lemma lies in the sub-structures.) -/
theorem colourable_iff_good_edge (k : Nat) (hk : 0 < k) (F : Fin G.m → Prop) :
    Colourable F k ↔
      ∀ P : Fin G.m → Prop, (∀ f, P f → F f) → (∃ f, P f) →
        ∃ e, P e ∧ (Colourable (fun f => P f ∧ f ≠ e) k → Colourable P k) := by
  constructor
  · intro ⟨c, hc⟩ P hPF ⟨f, hf⟩
    refine ⟨f, hf, fun _ => ⟨c, ?_⟩⟩
    exact ⟨fun a b hab ha hb => hc.1 a b hab (hPF a ha) (hPF b hb),
      fun w h1 h2 h3 h4 => hc.2 w (hPF _ h1) (hPF _ h2) (hPF _ h3) (hPF _ h4)⟩
  · intro H
    apply Classical.byContradiction
    intro hF
    obtain ⟨P', hsub, hmin⟩ := exists_minimal k F hF
    have hne : ∃ f, P' f := by
      apply Classical.byContradiction
      intro hno
      apply hmin.1
      have : P' = fun _ => False := by
        funext f; apply propext; exact ⟨fun h => hno ⟨f, h⟩, fun h => h.elim⟩
      rw [this]; exact colourable_empty k hk
    obtain ⟨e, he, hext⟩ := H P' hsub hne
    apply hmin.1
    apply hext
    apply hmin.2
    exact ⟨fun f hf => hf.1, e, he, fun h => h.2 rfl⟩

/-! ### the three-colour repair -/

/-- **Three-colour repair.**  Let `c` be a star colouring of `P`, `T` a set of colours, `e ∉ P` a new edge and `c'`
    a colouring that keeps every `P`-edge whose colour is outside `T` and gives colours inside `T` to the *moved*
    edges — the `P`-edges coloured in `T`, and `e`.  Then `c'` is star on `P ∪ {e}` provided
    (1) `c'` is proper on the moved edges,
    (2) no walk of moved edges is bicoloured under `c'`, and
    (3) for a walk whose two odd (resp. even) edges are fixed with equal colours and whose two even (resp. odd) edges
        are moved, the moved edges get different colours.
    Every other walk is handled by `c` or by the separation of the palettes. -/
theorem starOn_triple_repair {P : Fin G.m → Prop} {k : Nat} (c c' : Fin G.m → Fin k) (T : Fin k → Prop)
    (e : Fin G.m) (hc : StarOn P k c)
    (hfix : ∀ f, P f → ¬ T (c f) → c' f = c f)
    (hmov : ∀ f, (P f ∧ T (c f)) ∨ f = e → T (c' f))
    (hprop : ∀ f g, ((P f ∧ T (c f)) ∨ f = e) → ((P g ∧ T (c g)) ∨ g = e) → G.Adj f g → c' f ≠ c' g)
    (hwin : ∀ w : G.Walk4, ((P w.e1 ∧ T (c w.e1)) ∨ w.e1 = e) → ((P w.e2 ∧ T (c w.e2)) ∨ w.e2 = e) →
      ((P w.e3 ∧ T (c w.e3)) ∨ w.e3 = e) → ((P w.e4 ∧ T (c w.e4)) ∨ w.e4 = e) → ¬ Bicol c' w)
    (hmix13 : ∀ w : G.Walk4, P w.e1 → ¬ T (c w.e1) → P w.e3 → ¬ T (c w.e3) → c w.e1 = c w.e3 →
      ((P w.e2 ∧ T (c w.e2)) ∨ w.e2 = e) → ((P w.e4 ∧ T (c w.e4)) ∨ w.e4 = e) → c' w.e2 ≠ c' w.e4)
    (hmix24 : ∀ w : G.Walk4, P w.e2 → ¬ T (c w.e2) → P w.e4 → ¬ T (c w.e4) → c w.e2 = c w.e4 →
      ((P w.e1 ∧ T (c w.e1)) ∨ w.e1 = e) → ((P w.e3 ∧ T (c w.e3)) ∨ w.e3 = e) → c' w.e1 ≠ c' w.e3) :
    StarOn (fun f => P f ∨ f = e) k c' := by
  -- classification of an edge of P ∪ {e}: fixed (in P, colour outside T, colour unchanged) or moved
  have cls : ∀ f, P f ∨ f = e → (P f ∧ ¬ T (c f) ∧ c' f = c f) ∨ ((P f ∧ T (c f)) ∨ f = e) := by
    intro f hf
    rcases hf with hf | hf
    · by_cases ht : T (c f)
      · exact Or.inr (Or.inl ⟨hf, ht⟩)
      · exact Or.inl ⟨hf, ht, hfix f hf ht⟩
    · exact Or.inr (Or.inr hf)
  -- a fixed and a moved edge never share a colour under c'
  have sep : ∀ f g, (P f ∧ ¬ T (c f) ∧ c' f = c f) → ((P g ∧ T (c g)) ∨ g = e) → c' f ≠ c' g := by
    intro f g ⟨_, hnt, hcf⟩ hg heq
    apply hnt
    rw [← hcf, heq]
    exact hmov g hg
  constructor
  · intro f g hadj hf hg heq
    rcases cls f hf with ff | mf <;> rcases cls g hg with fg | mg
    · exact hc.1 f g hadj ff.1 fg.1 (by rw [← ff.2.2, ← fg.2.2]; exact heq)
    · exact sep f g ff mg heq
    · exact sep g f fg mf heq.symm
    · exact hprop f g mf mg hadj heq
  · intro w h1 h2 h3 h4 hb
    rcases hb with ⟨hb13, hb24⟩
    rcases cls w.e1 h1 with f1 | m1 <;> rcases cls w.e3 h3 with f3 | m3
    · -- e1, e3 fixed
      rcases cls w.e2 h2 with f2 | m2 <;> rcases cls w.e4 h4 with f4 | m4
      · exact hc.2 w f1.1 f2.1 f3.1 f4.1
          ⟨by rw [← f1.2.2, ← f3.2.2]; exact hb13, by rw [← f2.2.2, ← f4.2.2]; exact hb24⟩
      · exact sep w.e2 w.e4 f2 m4 hb24
      · exact sep w.e4 w.e2 f4 m2 hb24.symm
      · exact hmix13 w f1.1 f1.2.1 f3.1 f3.2.1 (by rw [← f1.2.2, ← f3.2.2]; exact hb13) m2 m4 hb24
    · exact sep w.e1 w.e3 f1 m3 hb13
    · exact sep w.e3 w.e1 f3 m1 hb13.symm
    · -- e1, e3 moved
      rcases cls w.e2 h2 with f2 | m2 <;> rcases cls w.e4 h4 with f4 | m4
      · exact hmix24 w f2.1 f2.2.1 f4.1 f4.2.1 (by rw [← f2.2.2, ← f4.2.2]; exact hb24) m1 m3 hb13
      · exact sep w.e2 w.e4 f2 m4 hb24
      · exact sep w.e4 w.e2 f4 m2 hb24.symm
      · exact hwin w m1 m2 m3 m4 ⟨hb13, hb24⟩

end MGraph
