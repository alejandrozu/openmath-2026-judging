/-
  StarSix.lean — the bridge reduction for six colours: explicit colour permutation and the corollary that a graph
  with a bridge is star 6-colourable as soon as both sides (each keeping the bridge as a pendant edge) are.
  The permutation is a product of three transpositions and its properties are proved by hand (the only decision
  procedure is a 216-case kernel `decide` choosing two free colours); everything else is proved on top of StarCore.
  No `native_decide`, so nothing here depends on `Lean.ofReduceBool`.
-/
import StarCore

namespace MGraph

/-! ### transpositions of `Fin k` -/

/-- the transposition of `a` and `b` -/
def swap {k : Nat} (a b x : Fin k) : Fin k := if x = a then b else if x = b then a else x

theorem swap_a {k : Nat} (a b : Fin k) : swap a b a = b := by simp [swap]

theorem swap_ne {k : Nat} {a b x : Fin k} (hxa : x ≠ a) (hxb : x ≠ b) : swap a b x = x := by
  simp [swap, hxa, hxb]

theorem swap_swap {k : Nat} (a b x : Fin k) : swap a b (swap a b x) = x := by
  unfold swap
  by_cases hxa : x = a
  · rw [if_pos hxa]
    by_cases hba : b = a
    · rw [if_pos hba]; exact hba.trans hxa.symm
    · rw [if_neg hba, if_pos rfl]; exact hxa.symm
  · rw [if_neg hxa]
    by_cases hxb : x = b
    · rw [if_pos hxb, if_pos rfl]; exact hxb.symm
    · rw [if_neg hxb, if_neg hxa, if_neg hxb]

theorem swap_inj {k : Nat} {a b x y : Fin k} (h : swap a b x = swap a b y) : x = y := by
  rw [← swap_swap a b x, h, swap_swap]

theorem swap_b {k : Nat} (a b : Fin k) : swap a b b = a := by
  have := swap_swap a b a
  rw [swap_a] at this
  exact this

/-- `swap a b x = c → x = swap a b c` -/
theorem eq_swap_of_swap_eq {k : Nat} {a b x c : Fin k} (h : swap a b x = c) : x = swap a b c := by
  rw [← h, swap_swap]

/-! ### two colours outside a set of at most three -/

/-- the first colour outside `{ce, a1, a2}` -/
def pick1 (ce a1 a2 : Fin 6) : Fin 6 :=
  if 0 ≠ ce ∧ 0 ≠ a1 ∧ 0 ≠ a2 then 0 else if 1 ≠ ce ∧ 1 ≠ a1 ∧ 1 ≠ a2 then 1 else
  if 2 ≠ ce ∧ 2 ≠ a1 ∧ 2 ≠ a2 then 2 else 3

/-- a second colour outside `{ce, a1, a2}`, different from the first -/
def pick2 (ce a1 a2 : Fin 6) : Fin 6 :=
  let t := pick1 ce a1 a2
  if 0 ≠ ce ∧ 0 ≠ a1 ∧ 0 ≠ a2 ∧ 0 ≠ t then 0 else if 1 ≠ ce ∧ 1 ≠ a1 ∧ 1 ≠ a2 ∧ 1 ≠ t then 1 else
  if 2 ≠ ce ∧ 2 ≠ a1 ∧ 2 ≠ a2 ∧ 2 ≠ t then 2 else if 3 ≠ ce ∧ 3 ≠ a1 ∧ 3 ≠ a2 ∧ 3 ≠ t then 3 else 4

theorem pick_spec : ∀ ce a1 a2 : Fin 6,
    pick1 ce a1 a2 ≠ ce ∧ pick1 ce a1 a2 ≠ a1 ∧ pick1 ce a1 a2 ≠ a2 ∧
    pick2 ce a1 a2 ≠ ce ∧ pick2 ce a1 a2 ≠ a1 ∧ pick2 ce a1 a2 ≠ a2 ∧ pick1 ce a1 a2 ≠ pick2 ce a1 a2 := by
  decide

/-! ### the recolouring permutation -/

/-- `fixPerm ce a1 a2 ce' b1 b2` is a permutation of `Fin 6` sending `ce'` to `ce` and sending `b1`, `b2`
    (when different from `ce'`) to colours outside `{ce, a1, a2}`: three transpositions, the first moving `ce'` to
    `ce`, the next two moving the images of `b1`, `b2` onto two free colours. -/
def fixPerm (ce a1 a2 ce' b1 b2 : Fin 6) : Fin 6 → Fin 6 :=
  let t1 := pick1 ce a1 a2
  let t2 := pick2 ce a1 a2
  let u2 := swap ce' ce b1
  let u3 := swap u2 t1 (swap ce' ce b2)
  fun x => swap u3 t2 (swap u2 t1 (swap ce' ce x))

/-- the specification of `fixPerm`, proved from the transposition lemmas -/
theorem fixPerm_spec : ∀ ce a1 a2 ce' b1 b2 : Fin 6, b1 ≠ ce' → b2 ≠ ce' →
    (∀ x y, fixPerm ce a1 a2 ce' b1 b2 x = fixPerm ce a1 a2 ce' b1 b2 y → x = y) ∧
    fixPerm ce a1 a2 ce' b1 b2 ce' = ce ∧
    fixPerm ce a1 a2 ce' b1 b2 b1 ≠ a1 ∧ fixPerm ce a1 a2 ce' b1 b2 b1 ≠ a2 ∧
    fixPerm ce a1 a2 ce' b1 b2 b2 ≠ a1 ∧ fixPerm ce a1 a2 ce' b1 b2 b2 ≠ a2 := by
  intro ce a1 a2 ce' b1 b2 hb1 hb2
  obtain ⟨h1c, h1a, h1b, h2c, h2a, h2b, h12⟩ := pick_spec ce a1 a2
  -- names for the pieces
  have hu2 : ce ≠ swap ce' ce b1 := by
    intro h
    have := eq_swap_of_swap_eq h.symm
    rw [swap_b] at this
    exact hb1 this
  have hu3 : ce ≠ swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b2) := by
    intro h
    have h' := eq_swap_of_swap_eq h.symm
    rw [swap_ne hu2 h1c.symm] at h'
    have h'' := eq_swap_of_swap_eq h'
    rw [swap_b] at h''
    exact hb2 h''
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    exact swap_inj (swap_inj (swap_inj h))
  · show swap _ _ (swap _ _ (swap ce' ce ce')) = ce
    rw [swap_a, swap_ne hu2 h1c.symm, swap_ne hu3 h2c.symm]
  · show swap _ (pick2 ce a1 a2) (swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b1)) ≠ a1
    rw [swap_a]
    by_cases h : pick1 ce a1 a2 = swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b2)
    · have e1 := congrArg (swap (swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b2)) (pick2 ce a1 a2)) h
      rw [swap_a] at e1
      rw [e1]; exact h2a
    · rw [swap_ne h h12]; exact h1a
  · show swap _ (pick2 ce a1 a2) (swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b1)) ≠ a2
    rw [swap_a]
    by_cases h : pick1 ce a1 a2 = swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b2)
    · have e1 := congrArg (swap (swap (swap ce' ce b1) (pick1 ce a1 a2) (swap ce' ce b2)) (pick2 ce a1 a2)) h
      rw [swap_a] at e1
      rw [e1]; exact h2b
    · rw [swap_ne h h12]; exact h1b
  · show swap _ (pick2 ce a1 a2) _ ≠ a1
    rw [swap_a]; exact h2a
  · show swap _ (pick2 ce a1 a2) _ ≠ a2
    rw [swap_a]; exact h2b

variable {G : MGraph}

/-- **Bridge reduction, six colours.**  If `e` is a bridge, both sides (each keeping `e`) have star 6-colourings,
    and at each endpoint of `e` the other edges use at most two colours (automatic for subcubic graphs), then `G`
    has a star 6-colouring. -/
theorem glue_bridge_six {e : Fin G.m} (B : G.BridgeCut e) (cU cV : Fin G.m → Fin 6)
    (hU : StarOn (fun f => f = e ∨ B.onU f) 6 cU)
    (hV : StarOn (fun f => f = e ∨ ¬ B.onU f) 6 cV)
    (p q : Fin 6) (hpq : ∀ a, a ≠ e → G.Inc a (G.ends e).1 → cU a = p ∨ cU a = q)
    (r s : Fin 6) (hr : r ≠ cV e) (hs : s ≠ cV e)
    (hrs : ∀ b, b ≠ e → G.Inc b (G.ends e).2 → cV b = r ∨ cV b = s) :
    ∃ c : Fin G.m → Fin 6, Star 6 c := by
  obtain ⟨hinj, hce, hr1, hr2, hs1, hs2⟩ := fixPerm_spec (cU e) p q (cV e) r s hr hs
  refine ⟨B.glue cU (fun f => fixPerm (cU e) p q (cV e) r s (cV f)), ?_⟩
  apply glue_bridge B cU _ hU (starOn_map _ hinj hV)
  · exact hce.symm
  · intro a b ha hb hau hbv heq
    rcases hpq a ha hau with hp | hq <;> rcases hrs b hb hbv with hr' | hs'
    · rw [hp, hr'] at heq; exact hr1 heq.symm
    · rw [hp, hs'] at heq; exact hs1 heq.symm
    · rw [hq, hr'] at heq; exact hr2 heq.symm
    · rw [hq, hs'] at heq; exact hs2 heq.symm

end MGraph
