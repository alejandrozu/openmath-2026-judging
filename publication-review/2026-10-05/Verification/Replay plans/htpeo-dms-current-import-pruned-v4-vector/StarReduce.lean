/-
  StarReduce.lean — the minimal-counterexample reduction, formally.

  Working with edge subsets `P` of a fixed ambient multigraph (so sub-multigraphs need no separate type; a bridge of
  the sub-multigraph `P` is a `CutOn P e`):
  * `glue_bridge_on`      — bridge gluing on an edge set `P`;
  * `glue_bridge_six_on`  — the six-colour version with the explicit permutation of `StarSix`;
  * `minimal_no_bridge`   — in a subcubic multigraph, a minimal non-star-6-colourable edge set has no bridge with
                            edges of the set on both sides;
  * `exists_minimal`      — every non-colourable edge set contains a minimal one;
  * `dms_reduction`       — **main theorem**: if every edge set without a two-sided bridge is star 6-colourable, then
                            every edge set is.  (A pendant bridge — one side carrying no other edge of the set — is not
                            excluded by the gluing argument; that case stays open.)
-/
import StarCore
import StarSix

namespace MGraph
variable {G : MGraph}

/-- no vertex has four distinct incident edges -/
def Subcubic (G : MGraph) : Prop :=
  ∀ x a b c d, G.Inc a x → G.Inc b x → G.Inc c x → G.Inc d x →
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False

/-- the edge set `P` admits a star `k`-colouring -/
def Colourable (P : Fin G.m → Prop) (k : Nat) : Prop := ∃ c : Fin G.m → Fin k, StarOn P k c

/-- `P'` is a proper subset of `P` -/
def ProperSub (P' P : Fin G.m → Prop) : Prop := (∀ f, P' f → P f) ∧ ∃ f, P f ∧ ¬ P' f

/-- a minimal non-colourable edge set: not colourable, every proper subset colourable -/
def MinimalCounterexample (P : Fin G.m → Prop) (k : Nat) : Prop :=
  ¬ Colourable P k ∧ ∀ P', ProperSub P' P → Colourable P' k


/-- a bridge cut of the sub-multigraph `P` at `e`: every edge of `P` other than `e` has both ends on one side -/
structure CutOn (P : Fin G.m → Prop) (e : Fin G.m) where
  U : Fin G.n → Bool
  hu : U (G.ends e).1 = true
  hv : U (G.ends e).2 = false
  sep : ∀ f, P f → f ≠ e → U (G.ends f).1 = U (G.ends f).2

namespace CutOn
variable {P : Fin G.m → Prop} {e : Fin G.m} (B : G.CutOn P e)

def onU (f : Fin G.m) : Prop := B.U (G.ends f).1 = true

theorem onU_iff_inc {f : Fin G.m} {x : Fin G.n} (hf : P f) (hne : f ≠ e) (hx : G.Inc f x) :
    (B.onU f ↔ B.U x = true) := by
  rcases hx with hx | hx
  · show B.U (G.ends f).1 = true ↔ B.U x = true
    rw [hx]
  · show B.U (G.ends f).1 = true ↔ B.U x = true
    rw [B.sep f hf hne, hx]

theorem same_side {a b : Fin G.m} {x : Fin G.n} (ha : P a) (hb : P b) (hae : a ≠ e) (hbe : b ≠ e)
    (hax : G.Inc a x) (hbx : G.Inc b x) : (B.onU a ↔ B.onU b) := by
  rw [B.onU_iff_inc ha hae hax, B.onU_iff_inc hb hbe hbx]

theorem onU_e : B.onU e := B.hu

theorem onU_of_inc_u {f : Fin G.m} (hf : P f) (hne : f ≠ e) (hx : G.Inc f (G.ends e).1) : B.onU f :=
  (B.onU_iff_inc hf hne hx).2 B.hu

theorem not_onU_of_inc_v {f : Fin G.m} (hf : P f) (hne : f ≠ e) (hx : G.Inc f (G.ends e).2) : ¬ B.onU f := by
  intro h
  have := (B.onU_iff_inc hf hne hx).1 h
  rw [B.hv] at this
  exact Bool.false_ne_true this

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

end CutOn

/-! ### gluing on an edge set -/

theorem glue_bridge_on {P : Fin G.m → Prop} {e : Fin G.m} (B : G.CutOn P e) {k : Nat}
    (cU cV : Fin G.m → Fin k)
    (hU : StarOn (fun f => P f ∧ (f = e ∨ B.onU f)) k cU)
    (hV : StarOn (fun f => P f ∧ (f = e ∨ ¬ B.onU f)) k cV)
    (he : cU e = cV e)
    (hdisj : ∀ a b, P a → P b → a ≠ e → b ≠ e → G.Inc a (G.ends e).1 → G.Inc b (G.ends e).2 → cU a ≠ cV b) :
    StarOn P k (B.glue cU cV) := by
  have gU : ∀ {f}, B.onU f → B.glue cU cV f = cU f := fun h => B.glue_U cU cV h
  have gV : ∀ {f}, ¬ B.onU f → B.glue cU cV f = cV f := fun h => B.glue_V cU cV h
  have ge : B.glue cU cV e = cU e := gU B.onU_e
  have ge' : B.glue cU cV e = cV e := by rw [ge, he]
  have hu_or_v : ∀ {x : Fin G.n}, G.Inc e x → x = (G.ends e).1 ∨ x = (G.ends e).2 :=
    fun hx => inc_of_joins (joins_ends e) hx
  constructor
  · intro a b hab ha hb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    by_cases hae : a = e
    · subst hae
      have hb' : b ≠ a := fun h => hne h.symm
      rcases hu_or_v hax with hx | hx
      · have hbU : B.onU b := B.onU_of_inc_u hb hb' (hx ▸ hbx)
        rw [ge, gU hbU] at heq
        exact hU.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, Or.inl rfl⟩ ⟨hb, Or.inr hbU⟩ heq
      · have hbV : ¬ B.onU b := B.not_onU_of_inc_v hb hb' (hx ▸ hbx)
        rw [ge', gV hbV] at heq
        exact hV.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, Or.inl rfl⟩ ⟨hb, Or.inr hbV⟩ heq
    · by_cases hbe : b = e
      · subst hbe
        rcases hu_or_v hbx with hx | hx
        · have haU : B.onU a := B.onU_of_inc_u ha hae (hx ▸ hax)
          rw [ge, gU haU] at heq
          exact hU.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, Or.inr haU⟩ ⟨hb, Or.inl rfl⟩ heq
        · have haV : ¬ B.onU a := B.not_onU_of_inc_v ha hae (hx ▸ hax)
          rw [ge', gV haV] at heq
          exact hV.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, Or.inr haV⟩ ⟨hb, Or.inl rfl⟩ heq
      · have hss := B.same_side ha hb hae hbe hax hbx
        by_cases haU : B.onU a
        · have hbU : B.onU b := hss.1 haU
          rw [gU haU, gU hbU] at heq
          exact hU.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, Or.inr haU⟩ ⟨hb, Or.inr hbU⟩ heq
        · have hbV : ¬ B.onU b := fun h => haU (hss.2 h)
          rw [gV haU, gV hbV] at heq
          exact hV.1 a b ⟨hne, x, hax, hbx⟩ ⟨ha, Or.inr haU⟩ ⟨hb, Or.inr hbV⟩ heq
  · intro w hp1 hp2 hp3 hp4 hb
    rcases hb with ⟨hb13, hb24⟩
    by_cases h2 : w.e2 = e
    · have h1 : w.e1 ≠ e := fun h => w.e1_ne_e2 (h.trans h2.symm)
      have h3 : w.e3 ≠ e := fun h => w.e2_ne_e3 (h2.trans h.symm)
      have hj : G.Joins e w.v1 w.v2 := by rw [← h2]; exact w.h2
      rcases joins_unique (joins_ends e) hj with ⟨hu1, hv2⟩ | ⟨hu2, hv1⟩
      · have h1U : B.onU w.e1 := B.onU_of_inc_u hp1 h1 (hu1 ▸ w.inc_e1_v1)
        have h3V : ¬ B.onU w.e3 := B.not_onU_of_inc_v hp3 h3 (hv2 ▸ w.inc_e3_v2)
        rw [gU h1U, gV h3V] at hb13
        exact hdisj w.e1 w.e3 hp1 hp3 h1 h3 (hu1 ▸ w.inc_e1_v1) (hv2 ▸ w.inc_e3_v2) hb13
      · have h3U : B.onU w.e3 := B.onU_of_inc_u hp3 h3 (hu2 ▸ w.inc_e3_v2)
        have h1V : ¬ B.onU w.e1 := B.not_onU_of_inc_v hp1 h1 (hv1 ▸ w.inc_e1_v1)
        rw [gV h1V, gU h3U] at hb13
        exact hdisj w.e3 w.e1 hp3 hp1 h3 h1 (hu2 ▸ w.inc_e3_v2) (hv1 ▸ w.inc_e1_v1) hb13.symm
    by_cases h3 : w.e3 = e
    · have h2' : w.e2 ≠ e := h2
      have h4 : w.e4 ≠ e := fun h => w.e3_ne_e4 (h3.trans h.symm)
      have hj : G.Joins e w.v2 w.v3 := by rw [← h3]; exact w.h3
      rcases joins_unique (joins_ends e) hj with ⟨hu2, hv3⟩ | ⟨hu3, hv2⟩
      · have h2U : B.onU w.e2 := B.onU_of_inc_u hp2 h2' (hu2 ▸ w.inc_e2_v2)
        have h4V : ¬ B.onU w.e4 := B.not_onU_of_inc_v hp4 h4 (hv3 ▸ w.inc_e4_v3)
        rw [gU h2U, gV h4V] at hb24
        exact hdisj w.e2 w.e4 hp2 hp4 h2' h4 (hu2 ▸ w.inc_e2_v2) (hv3 ▸ w.inc_e4_v3) hb24
      · have h4U : B.onU w.e4 := B.onU_of_inc_u hp4 h4 (hu3 ▸ w.inc_e4_v3)
        have h2V : ¬ B.onU w.e2 := B.not_onU_of_inc_v hp2 h2' (hv2 ▸ w.inc_e2_v2)
        rw [gV h2V, gU h4U] at hb24
        exact hdisj w.e4 w.e2 hp4 hp2 h4 h2' (hu3 ▸ w.inc_e4_v3) (hv2 ▸ w.inc_e2_v2) hb24.symm
    have s23 : (B.onU w.e2 ↔ B.onU w.e3) := B.same_side hp2 hp3 h2 h3 w.inc_e2_v2 w.inc_e3_v2
    by_cases h1 : w.e1 = e
    · have h4 : w.e4 ≠ e := fun h => w.e1_ne_e4 (h1.trans h.symm)
      have s34 : (B.onU w.e3 ↔ B.onU w.e4) := B.same_side hp3 hp4 h3 h4 w.inc_e3_v3 w.inc_e4_v3
      have hj : G.Joins e w.v0 w.v1 := by rw [← h1]; exact w.h1
      rcases hu_or_v (joins_inc_right hj) with hx | hx
      · have h2U : B.onU w.e2 := B.onU_of_inc_u hp2 h2 (hx ▸ w.inc_e2_v1)
        have h3U := s23.1 h2U
        have h4U := s34.1 h3U
        rw [h1, ge, gU h3U] at hb13
        rw [gU h2U, gU h4U] at hb24
        exact hU.2 w ⟨hp1, Or.inl h1⟩ ⟨hp2, Or.inr h2U⟩ ⟨hp3, Or.inr h3U⟩ ⟨hp4, Or.inr h4U⟩
          ⟨by rw [h1]; exact hb13, hb24⟩
      · have h2V : ¬ B.onU w.e2 := B.not_onU_of_inc_v hp2 h2 (hx ▸ w.inc_e2_v1)
        have h3V : ¬ B.onU w.e3 := fun h => h2V (s23.2 h)
        have h4V : ¬ B.onU w.e4 := fun h => h3V (s34.2 h)
        rw [h1, ge', gV h3V] at hb13
        rw [gV h2V, gV h4V] at hb24
        exact hV.2 w ⟨hp1, Or.inl h1⟩ ⟨hp2, Or.inr h2V⟩ ⟨hp3, Or.inr h3V⟩ ⟨hp4, Or.inr h4V⟩
          ⟨by rw [h1]; exact hb13, hb24⟩
    by_cases h4 : w.e4 = e
    · have s12 : (B.onU w.e1 ↔ B.onU w.e2) := B.same_side hp1 hp2 h1 h2 w.inc_e1_v1 w.inc_e2_v1
      have hj : G.Joins e w.v3 w.v4 := by rw [← h4]; exact w.h4
      rcases hu_or_v (joins_inc_left hj) with hx | hx
      · have h3U : B.onU w.e3 := B.onU_of_inc_u hp3 h3 (hx ▸ w.inc_e3_v3)
        have h2U := s23.2 h3U
        have h1U := s12.2 h2U
        rw [gU h1U, gU h3U] at hb13
        rw [h4, ge, gU h2U] at hb24
        exact hU.2 w ⟨hp1, Or.inr h1U⟩ ⟨hp2, Or.inr h2U⟩ ⟨hp3, Or.inr h3U⟩ ⟨hp4, Or.inl h4⟩
          ⟨hb13, by rw [h4]; exact hb24⟩
      · have h3V : ¬ B.onU w.e3 := B.not_onU_of_inc_v hp3 h3 (hx ▸ w.inc_e3_v3)
        have h2V : ¬ B.onU w.e2 := fun h => h3V (s23.1 h)
        have h1V : ¬ B.onU w.e1 := fun h => h2V (s12.1 h)
        rw [gV h1V, gV h3V] at hb13
        rw [h4, ge', gV h2V] at hb24
        exact hV.2 w ⟨hp1, Or.inr h1V⟩ ⟨hp2, Or.inr h2V⟩ ⟨hp3, Or.inr h3V⟩ ⟨hp4, Or.inl h4⟩
          ⟨hb13, by rw [h4]; exact hb24⟩
    have s12 : (B.onU w.e1 ↔ B.onU w.e2) := B.same_side hp1 hp2 h1 h2 w.inc_e1_v1 w.inc_e2_v1
    have s34 : (B.onU w.e3 ↔ B.onU w.e4) := B.same_side hp3 hp4 h3 h4 w.inc_e3_v3 w.inc_e4_v3
    by_cases h1U : B.onU w.e1
    · have h2U := s12.1 h1U
      have h3U := s23.1 h2U
      have h4U := s34.1 h3U
      rw [gU h1U, gU h3U] at hb13
      rw [gU h2U, gU h4U] at hb24
      exact hU.2 w ⟨hp1, Or.inr h1U⟩ ⟨hp2, Or.inr h2U⟩ ⟨hp3, Or.inr h3U⟩ ⟨hp4, Or.inr h4U⟩ ⟨hb13, hb24⟩
    · have h2V : ¬ B.onU w.e2 := fun h => h1U (s12.2 h)
      have h3V : ¬ B.onU w.e3 := fun h => h2V (s23.2 h)
      have h4V : ¬ B.onU w.e4 := fun h => h3V (s34.2 h)
      rw [gV h1U, gV h3V] at hb13
      rw [gV h2V, gV h4V] at hb24
      exact hV.2 w ⟨hp1, Or.inr h1U⟩ ⟨hp2, Or.inr h2V⟩ ⟨hp3, Or.inr h3V⟩ ⟨hp4, Or.inr h4V⟩ ⟨hb13, hb24⟩

/-- six-colour gluing on an edge set, with the colour bookkeeping supplied as `p q r s` -/
theorem glue_bridge_six_on {P : Fin G.m → Prop} {e : Fin G.m} (B : G.CutOn P e) (cU cV : Fin G.m → Fin 6)
    (hU : StarOn (fun f => P f ∧ (f = e ∨ B.onU f)) 6 cU)
    (hV : StarOn (fun f => P f ∧ (f = e ∨ ¬ B.onU f)) 6 cV)
    (p q : Fin 6) (hpq : ∀ a, P a → a ≠ e → G.Inc a (G.ends e).1 → cU a = p ∨ cU a = q)
    (r s : Fin 6) (hr : r ≠ cV e) (hs : s ≠ cV e)
    (hrs : ∀ b, P b → b ≠ e → G.Inc b (G.ends e).2 → cV b = r ∨ cV b = s) :
    Colourable P 6 := by
  obtain ⟨hinj, hce, hr1, hr2, hs1, hs2⟩ := fixPerm_spec (cU e) p q (cV e) r s hr hs
  refine ⟨B.glue cU (fun f => fixPerm (cU e) p q (cV e) r s (cV f)), ?_⟩
  apply glue_bridge_on B cU _ hU (starOn_map _ hinj hV)
  · exact hce.symm
  · intro a b ha hb hae hbe hau hbv heq
    rcases hpq a ha hae hau with hp | hq <;> rcases hrs b hb hbe hbv with hr' | hs'
    · rw [hp, hr'] at heq; exact hr1 heq.symm
    · rw [hp, hs'] at heq; exact hs1 heq.symm
    · rw [hq, hr'] at heq; exact hr2 heq.symm
    · rw [hq, hs'] at heq; exact hs2 heq.symm

/-! ### colour bookkeeping from the degree bound -/

/-- in a subcubic graph, the colours of the edges of `P` at `x` other than `e` are covered by two values -/
theorem two_colours_at (hsub : Subcubic G) (P : Fin G.m → Prop) {k : Nat} (c : Fin G.m → Fin k)
    (e : Fin G.m) (x : Fin G.n) (hex : G.Inc e x) (d : Fin k) :
    ∃ p q : Fin k, (p = d ∨ ∃ a, P a ∧ a ≠ e ∧ G.Inc a x ∧ c a = p) ∧
      (q = d ∨ ∃ a, P a ∧ a ≠ e ∧ G.Inc a x ∧ c a = q) ∧
      ∀ a, P a → a ≠ e → G.Inc a x → c a = p ∨ c a = q := by
  by_cases h1 : ∃ a1, P a1 ∧ a1 ≠ e ∧ G.Inc a1 x
  · obtain ⟨a1, hp1, hne1, hi1⟩ := h1
    by_cases h2 : ∃ a2, P a2 ∧ a2 ≠ e ∧ G.Inc a2 x ∧ a2 ≠ a1
    · obtain ⟨a2, hp2, hne2, hi2, h21⟩ := h2
      refine ⟨c a1, c a2, Or.inr ⟨a1, hp1, hne1, hi1, rfl⟩, Or.inr ⟨a2, hp2, hne2, hi2, rfl⟩, ?_⟩
      intro a ha hae hax
      by_cases ha1 : a = a1
      · exact Or.inl (by rw [ha1])
      by_cases ha2 : a = a2
      · exact Or.inr (by rw [ha2])
      exact absurd (hsub x a a1 a2 e hax hi1 hi2 hex ha1 ha2 hae (fun h => h21 h.symm) hne1 hne2) id
    · refine ⟨c a1, c a1, Or.inr ⟨a1, hp1, hne1, hi1, rfl⟩, Or.inr ⟨a1, hp1, hne1, hi1, rfl⟩, ?_⟩
      intro a ha hae hax
      by_cases ha1 : a = a1
      · exact Or.inl (by rw [ha1])
      · exact absurd ⟨a, ha, hae, hax, ha1⟩ h2
  · refine ⟨d, d, Or.inl rfl, Or.inl rfl, ?_⟩
    intro a ha hae hax
    exact absurd ⟨a, ha, hae, hax⟩ h1

/-- a colour different from a given one (six colours) -/
def other6 (d : Fin 6) : Fin 6 := if d.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

theorem other6_ne (d : Fin 6) : other6 d ≠ d := by
  unfold other6
  by_cases h : d.val = 0
  · rw [if_pos h]
    intro h'
    have := congrArg Fin.val h'
    simp [h] at this
  · rw [if_neg h]
    intro h'
    have := congrArg Fin.val h'
    exact h this.symm

/-! ### the main theorem -/

/-- **A minimal non-star-6-colourable edge set of a subcubic multigraph has no bridge with edges of the set on
    both sides.** -/
theorem minimal_no_bridge (hsub : Subcubic G) (P : Fin G.m → Prop) (hmin : MinimalCounterexample P 6)
    (e : Fin G.m) (hPe : P e) (B : G.CutOn P e)
    (hUne : ∃ a, P a ∧ a ≠ e ∧ B.onU a) (hVne : ∃ b, P b ∧ b ≠ e ∧ ¬ B.onU b) : False := by
  -- both sides are proper subsets, hence colourable
  have hPU : Colourable (fun f => P f ∧ (f = e ∨ B.onU f)) 6 := by
    apply hmin.2
    refine ⟨fun f hf => hf.1, ?_⟩
    obtain ⟨b, hb, hbe, hbU⟩ := hVne
    exact ⟨b, hb, fun h => h.2.elim (fun h' => hbe h') hbU⟩
  have hPV : Colourable (fun f => P f ∧ (f = e ∨ ¬ B.onU f)) 6 := by
    apply hmin.2
    refine ⟨fun f hf => hf.1, ?_⟩
    obtain ⟨a, ha, hae, haU⟩ := hUne
    exact ⟨a, ha, fun h => h.2.elim (fun h' => hae h') (fun h' => h' haU)⟩
  obtain ⟨cU, hU⟩ := hPU
  obtain ⟨cV, hV⟩ := hPV
  -- colours at u
  obtain ⟨p, q, -, -, hpq⟩ := two_colours_at hsub P cU e (G.ends e).1 (joins_inc_left (joins_ends e)) (cU e)
  -- colours at v, chosen different from the colour of e
  obtain ⟨r, s, hr0, hs0, hrs⟩ :=
    two_colours_at hsub P cV e (G.ends e).2 (joins_inc_right (joins_ends e)) (other6 (cV e))
  have hne_v : ∀ b, P b → b ≠ e → G.Inc b (G.ends e).2 → cV b ≠ cV e := by
    intro b hb hbe hbv heq
    exact hV.1 b e ⟨hbe, (G.ends e).2, hbv, joins_inc_right (joins_ends e)⟩
      ⟨hb, Or.inr (B.not_onU_of_inc_v hb hbe hbv)⟩ ⟨hPe, Or.inl rfl⟩ heq
  have hr : r ≠ cV e := by
    rcases hr0 with h | ⟨b, hb, hbe, hbv, hcb⟩
    · rw [h]; exact other6_ne _
    · rw [← hcb]; exact hne_v b hb hbe hbv
  have hs : s ≠ cV e := by
    rcases hs0 with h | ⟨b, hb, hbe, hbv, hcb⟩
    · rw [h]; exact other6_ne _
    · rw [← hcb]; exact hne_v b hb hbe hbv
  exact hmin.1 (glue_bridge_six_on B cU cV hU hV p q hpq r s hr hs hrs)

/-! ### existence of minimal counterexamples and the reduction -/

open Classical in
/-- number of edges in `P` -/
noncomputable def cardP (P : Fin G.m → Prop) : Nat :=
  ((List.finRange G.m).filter (fun f => decide (P f))).length

theorem mem_finRange' {n : Nat} (x : Fin n) : x ∈ List.finRange n := by
  unfold List.finRange
  exact List.mem_ofFn.2 ⟨x, rfl⟩

open Classical in
theorem cardP_lt {P' P : Fin G.m → Prop} (h : ProperSub P' P) : cardP P' < cardP P := by
  unfold cardP
  obtain ⟨hsub, f, hf, hf'⟩ := h
  have hsl : ((List.finRange G.m).filter (fun g => decide (P' g))).Sublist
      ((List.finRange G.m).filter (fun g => decide (P g))) := by
    have heq : (List.finRange G.m).filter (fun g => decide (P' g)) =
        ((List.finRange G.m).filter (fun g => decide (P g))).filter (fun g => decide (P' g)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro g _
      by_cases hg : P' g
      · simp [hg, hsub g hg]
      · simp [hg]
    rw [heq]
    exact List.filter_sublist
  apply Nat.lt_of_le_of_ne hsl.length_le
  intro hlen
  have heq := hsl.eq_of_length hlen
  have hmem : f ∈ (List.finRange G.m).filter (fun g => decide (P g)) :=
    List.mem_filter.2 ⟨mem_finRange' f, by simp [hf]⟩
  rw [← heq] at hmem
  have := (List.mem_filter.1 hmem).2
  simp [hf'] at this

/-- every non-colourable edge set contains a minimal non-colourable one -/
theorem exists_minimal (k : Nat) : ∀ P : Fin G.m → Prop, ¬ Colourable P k →
    ∃ P' : Fin G.m → Prop, (∀ f, P' f → P f) ∧ MinimalCounterexample P' k := by
  suffices h : ∀ n, ∀ P : Fin G.m → Prop, cardP P = n → ¬ Colourable P k →
      ∃ P' : Fin G.m → Prop, (∀ f, P' f → P f) ∧ MinimalCounterexample P' k from
    fun P hP => h (cardP P) P rfl hP
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro P hn hP
    by_cases hall : ∀ P', ProperSub P' P → Colourable P' k
    · exact ⟨P, fun _ h => h, hP, hall⟩
    · have ⟨P', hP'sub, hP'nc⟩ : ∃ P', ProperSub P' P ∧ ¬ Colourable P' k := by
        apply Classical.byContradiction
        intro hcon
        apply hall
        intro P' hP'
        apply Classical.byContradiction
        intro hnc
        exact hcon ⟨P', hP', hnc⟩
      have hlt : cardP P' < n := hn ▸ cardP_lt hP'sub
      obtain ⟨P'', hsub'', hmin''⟩ := ih (cardP P') hlt P' rfl hP'nc
      exact ⟨P'', fun f hf => hP'sub.1 f (hsub'' f hf), hmin''⟩

/-- an edge set has a **two-sided bridge** if some edge `e ∈ P` is a bridge of `P` with edges of `P` other than
    `e` on both sides -/
def HasTwoSidedBridge (P : Fin G.m → Prop) : Prop :=
  ∃ e, P e ∧ ∃ B : G.CutOn P e, (∃ a, P a ∧ a ≠ e ∧ B.onU a) ∧ (∃ b, P b ∧ b ≠ e ∧ ¬ B.onU b)

/-- **Reduction.**  In a subcubic multigraph, if every edge set without a two-sided bridge is star 6-colourable,
    then every edge set is star 6-colourable. -/
theorem dms_reduction (hsub : Subcubic G)
    (H : ∀ P : Fin G.m → Prop, ¬ HasTwoSidedBridge P → Colourable P 6) :
    ∀ P : Fin G.m → Prop, Colourable P 6 := by
  intro P
  apply Classical.byContradiction
  intro hP
  obtain ⟨P', -, hmin⟩ := exists_minimal 6 P hP
  apply hmin.1
  apply H
  rintro ⟨e, hPe, B, hUne, hVne⟩
  exact minimal_no_bridge hsub P' hmin e hPe B hUne hVne

end MGraph
