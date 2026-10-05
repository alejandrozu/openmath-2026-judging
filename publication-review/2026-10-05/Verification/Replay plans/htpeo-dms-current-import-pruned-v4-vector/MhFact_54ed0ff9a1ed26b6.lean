-- Lean proof of fact 54ed0ff9a1ed26b6 (RH2F.layer29a); added by fact_submit, do not edit
import MhFact_2e993e3b07378767
set_option backward.isDefEq.respectTransparency false

-- ===== from SC1.lean =====
/-
  SC1 — cut counting for the classification of 𝒮 (simple 3-edge-connected cubic multigraphs): the crossing count
  `xc`, its invariance under complement, submodularity, and the uncrossing lemma at a minimal nontrivial
  3-edge-cut side (no 3-edge-cut crosses an edge inside a minimal nontrivial side with both sides large).
-/

namespace RH2F
open MGraph
open Classical

section sc1
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the number of edges of `P` crossing `S` -/
noncomputable def xc (P : Fin X.m → Prop) (S : Fin X.n → Bool) : Nat := cntF X.m (RH2F.Crosses P S)

theorem xc_not (S : Fin X.n → Bool) : xc P (fun w => !S w) = xc P S := by
  unfold xc; apply cntF_congr; intro f
  simp only [RH2F.Crosses]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => h2 ?_⟩
    rw [h]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => h2 ?_⟩
    cases a : S (X.ends f).1 <;> cases b : S (X.ends f).2 <;> simp_all

theorem cntF_add_le : ∀ (n : Nat) (A B C D : Fin n → Prop),
    (∀ i, (if A i then 1 else 0) + (if B i then 1 else 0) ≤ (if C i then 1 else 0) + (if D i then 1 else 0)) →
    cntF n A + cntF n B ≤ cntF n C + cntF n D
  | 0, _, _, _, _, _ => Nat.le_refl 0
  | n + 1, A, B, C, D, h => by
    rw [cntF_succ, cntF_succ, cntF_succ, cntF_succ]
    have h1 := cntF_add_le n (fun i => A (Fin.castSucc i)) (fun i => B (Fin.castSucc i))
      (fun i => C (Fin.castSucc i)) (fun i => D (Fin.castSucc i)) (fun i => h _)
    have h2 := h (Fin.last n)
    generalize (if A (Fin.last n) then 1 else 0) = a at *
    generalize (if B (Fin.last n) then 1 else 0) = b at *
    generalize (if C (Fin.last n) then 1 else 0) = c at *
    generalize (if D (Fin.last n) then 1 else 0) = d at *
    omega

/-- **submodularity** of the crossing count -/
theorem xc_submod (S T : Fin X.n → Bool) :
    xc P (fun w => S w && T w) + xc P (fun w => S w || T w) ≤ xc P S + xc P T := by
  unfold xc
  apply cntF_add_le
  intro f
  simp only [RH2F.Crosses]
  by_cases hf : P f
  · simp only [hf, true_and]
    cases S (X.ends f).1 <;> cases S (X.ends f).2 <;> cases T (X.ends f).1 <;> cases T (X.ends f).2 <;> decide
  · simp [hf]

/-! ### side counts -/

theorem scount_not (S : Fin X.n → Bool) (b : Bool) : scount P (fun w => !S w) b = scount P S (!b) := by
  unfold scount; apply cntF_congr; intro w
  cases h : S w <;> cases b <;> simp [h]

theorem scount_pos {S : Fin X.n → Bool} {b : Bool} {w : Fin X.n} (hw : meets P w) (hS : S w = b) :
    1 ≤ scount P S b :=
  cntF_le_of_mem X.n _ (i := w) ⟨hw, hS⟩

theorem scount_uniq {S : Fin X.n → Bool} {b : Bool} (h : scount P S b ≤ 1) {w w' : Fin X.n}
    (hw : meets P w) (hS : S w = b) (hw' : meets P w') (hS' : S w' = b) : w = w' := by
  by_contra hne
  have := cntF_mono X.n (fun k => k = w ∨ k = w') (fun v => meets P v ∧ S v = b)
    (fun k hk => by rcases hk with rfl | rfl
                    · exact ⟨hw, hS⟩
                    · exact ⟨hw', hS'⟩)
  rw [cntF_pair X.n hne] at this
  unfold scount at h
  omega

theorem exists_other {S : Fin X.n → Bool} {b : Bool} (h : 2 ≤ scount P S b) (x : Fin X.n) :
    ∃ w, meets P w ∧ S w = b ∧ w ≠ x := by
  by_contra hno
  push_neg at hno
  have := cntF_mono X.n (fun v => meets P v ∧ S v = b) (fun k => k = x) (fun k hk => hno k hk.1 hk.2)
  rw [cntF_single] at this
  unfold scount at h
  omega

/-- a side contained in `A` and missing a vertex of `A` has fewer vertices -/
theorem scount_lt {A B : Fin X.n → Bool} (hsub : ∀ w, meets P w → B w = true → A w = true) {w0 : Fin X.n}
    (hw0 : meets P w0) (hA0 : A w0 = true) (hB0 : B w0 = false) : scount P B true + 1 ≤ scount P A true := by
  unfold scount
  rw [cntF_split X.n (fun v => meets P v ∧ A v = true) (fun v => B v = true)]
  have e1 : cntF X.n (fun v => (meets P v ∧ A v = true) ∧ B v = true) = cntF X.n (fun v => meets P v ∧ B v = true) := by
    apply cntF_congr; intro v
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub v h.1 h.2⟩, h.2⟩⟩
  have e2 := cntF_le_of_mem X.n (fun v => (meets P v ∧ A v = true) ∧ ¬ B v = true) (i := w0)
    ⟨⟨hw0, hA0⟩, by rw [hB0]; decide⟩
  omega

theorem scount_false_mono {A B : Fin X.n → Bool} (hsub : ∀ w, meets P w → B w = true → A w = true) :
    scount P A false ≤ scount P B false := by
  unfold scount
  apply cntF_mono; intro v hv
  refine ⟨hv.1, ?_⟩
  cases hB : B v
  · rfl
  · have := hsub v hv.1 hB; rw [hv.2] at this; exact absurd this (by decide)

/-! ### minimal nontrivial 3-edge-cut sides and uncrossing -/

/-- `A` is a minimal nontrivial 3-edge-cut side: exactly three edges of `P` cross `A`, both sides have at least two
    vertices of `P`, and no such side has fewer vertices of `P` on side `true` -/
def MinSide (P : Fin X.m → Prop) (A : Fin X.n → Bool) : Prop :=
  xc P A = 3 ∧ 2 ≤ scount P A true ∧ 2 ≤ scount P A false ∧
    ∀ B, xc P B = 3 → 2 ≤ scount P B true → 2 ≤ scount P B false → scount P A true ≤ scount P B true

/-- a 3-edge-cut side properly inside a minimal side is a single vertex -/
theorem minSide_sub {A : Fin X.n → Bool} (hA : MinSide P A) {B : Fin X.n → Bool} (hB : xc P B = 3)
    (hsub : ∀ w, meets P w → B w = true → A w = true) {w0 : Fin X.n} (hw0 : meets P w0) (hA0 : A w0 = true)
    (hB0 : B w0 = false) : scount P B true ≤ 1 := by
  by_contra h
  push_neg at h
  have hf : 2 ≤ scount P B false := le_trans hA.2.2.1 (scount_false_mono hsub)
  have h1 := hA.2.2.2 B hB h hf
  have h2 := scount_lt hsub hw0 hA0 hB0
  omega

theorem xc_ge3 (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (S : Fin X.n → Bool) {u v : Fin X.n}
    (hu : meets P u) (hSu : S u = true) (hv : meets P v) (hSv : S v = false) : 3 ≤ xc P S :=
  three_cross hG h3 S hu hSu hv hSv

variable {A T : Fin X.n → Bool} {u v : Fin X.n}

/-- uncrossing, second half: if `A ∩ T = {u}` then `A ∖ T = {v}` -/
theorem uncross_half (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (hA : MinSide P A)
    (hu : meets P u) (hv : meets P v) (hAu : A u = true) (hAv : A v = true)
    (hT : xc P T = 3) (hTu : T u = true) (hTv : T v = false) (hT1 : 2 ≤ scount P T true)
    (hU : ∀ w, meets P w → A w = true → T w = true → w = u) :
    ∀ w, meets P w → A w = true → T w = false → w = v := by
  obtain ⟨w1, hw1, hTw1, hw1u⟩ := exists_other hT1 u
  have hAw1 : A w1 = false := by
    cases h : A w1
    · rfl
    · exact absurd (hU w1 hw1 h hTw1) hw1u
  let J : Fin X.n → Bool := fun w => T w && !A w
  let K : Fin X.n → Bool := fun w => T w || !A w
  have hsm : xc P J + xc P K ≤ xc P T + xc P A := by
    have := xc_submod (P := P) T (fun w => !A w); rw [xc_not] at this; exact this
  have hA3 : xc P A = 3 := hA.1
  have hJ : 3 ≤ xc P J := xc_ge3 hG h3 J hw1 (by simp [J, hTw1, hAw1]) hv (by simp [J, hTv])
  have hK : 3 ≤ xc P K := xc_ge3 hG h3 K hw1 (by simp [K, hTw1]) hv (by simp [K, hTv, hAv])
  have hK3 : xc P K = 3 := by omega
  let L : Fin X.n → Bool := fun w => !K w
  have hL3 : xc P L = 3 := by rw [xc_not]; exact hK3
  have hsub : ∀ w, meets P w → L w = true → A w = true := by
    intro w _ h
    cases hAw : A w
    · simp [L, K, hAw] at h
    · rfl
  have h1 := minSide_sub hA hL3 hsub hu hAu (by simp [L, K, hTu])
  intro w hw hAw hTw
  exact scount_uniq h1 hw (by simp [L, K, hTw, hAw]) hv (by simp [L, K, hTv, hAv])

/-- uncrossing, first half: `A ∩ T = {u}` or `A ∖ T = {v}` -/
theorem uncross_step1 (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (hA : MinSide P A)
    (hu : meets P u) (hv : meets P v) (hAu : A u = true) (hAv : A v = true)
    (hT : xc P T = 3) (hTu : T u = true) (hTv : T v = false) :
    (∀ w, meets P w → A w = true → T w = true → w = u) ∨ (∀ w, meets P w → A w = true → T w = false → w = v) := by
  by_cases hc : ∃ w, meets P w ∧ A w = false ∧ T w = false
  · obtain ⟨w2, hw2, hAw2, hTw2⟩ := hc
    left
    let I : Fin X.n → Bool := fun w => A w && T w
    let U : Fin X.n → Bool := fun w => A w || T w
    have hsm : xc P I + xc P U ≤ xc P A + xc P T := xc_submod (P := P) A T
    have hA3 : xc P A = 3 := hA.1
    have hU3 : 3 ≤ xc P U := xc_ge3 hG h3 U hu (by simp [U, hAu]) hw2 (by simp [U, hAw2, hTw2])
    have hI3 : 3 ≤ xc P I := xc_ge3 hG h3 I hu (by simp [I, hAu, hTu]) hv (by simp [I, hTv])
    have hI : xc P I = 3 := by omega
    have hsub : ∀ w, meets P w → I w = true → A w = true := by
      intro w _ h
      simp only [I, Bool.and_eq_true] at h
      exact h.1
    have h1 := minSide_sub hA hI hsub hv hAv (by simp [I, hTv])
    intro w hw hAw hTw
    exact scount_uniq h1 hw (by simp [I, hAw, hTw]) hu (by simp [I, hAu, hTu])
  · push_neg at hc
    right
    obtain ⟨w2, hw2, hAw2, _⟩ := exists_other hA.2.2.1 u
    have hTw2 : T w2 = true := by
      cases h : T w2
      · exact absurd h (hc w2 hw2 hAw2)
      · rfl
    let I : Fin X.n → Bool := fun w => A w && !T w
    let U : Fin X.n → Bool := fun w => A w || !T w
    have hsm : xc P I + xc P U ≤ xc P A + xc P T := by
      have := xc_submod (P := P) A (fun w => !T w); rw [xc_not] at this; exact this
    have hA3 : xc P A = 3 := hA.1
    have hU3 : 3 ≤ xc P U := xc_ge3 hG h3 U hu (by simp [U, hAu]) hw2 (by simp [U, hAw2, hTw2])
    have hI3 : 3 ≤ xc P I := xc_ge3 hG h3 I hv (by simp [I, hAv, hTv]) hu (by simp [I, hTu])
    have hI : xc P I = 3 := by omega
    have hsub : ∀ w, meets P w → I w = true → A w = true := by
      intro w _ h
      simp only [I, Bool.and_eq_true] at h
      exact h.1
    have h1 := minSide_sub hA hI hsub hu hAu (by simp [I, hTu])
    intro w hw hAw hTw
    exact scount_uniq h1 hw (by simp [I, hAw, hTw]) hv (by simp [I, hAv, hTv])

/-- **uncrossing**: no 3-edge-cut with at least two vertices of `P` on each side separates the ends `u, v` of an edge
    inside a minimal nontrivial 3-edge-cut side `A` -/
theorem uncross (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (hA : MinSide P A)
    (hu : meets P u) (hv : meets P v) (hAu : A u = true) (hAv : A v = true)
    (hT : xc P T = 3) (hTu : T u = true) (hTv : T v = false)
    (hT1 : 2 ≤ scount P T true) (hT0 : 2 ≤ scount P T false) : False := by
  have both : (∀ w, meets P w → A w = true → T w = true → w = u) ∧
      (∀ w, meets P w → A w = true → T w = false → w = v) := by
    rcases uncross_step1 hG h3 hA hu hv hAu hAv hT hTu hTv with hl | hr
    · exact ⟨hl, uncross_half hG h3 hA hu hv hAu hAv hT hTu hTv hT1 hl⟩
    · refine ⟨?_, hr⟩
      have hT' : xc P (fun w => !T w) = 3 := by rw [xc_not]; exact hT
      have hT1' : 2 ≤ scount P (fun w => !T w) true := by rw [scount_not]; exact hT0
      have h := uncross_half (T := fun w => !T w) hG h3 hA hv hu hAv hAu hT' (by simp [hTv]) (by simp [hTu]) hT1'
        (fun w hw hAw hTw => hr w hw hAw (by simpa using hTw))
      intro w hw hAw hTw
      exact h w hw hAw (by simp [hTw])
  have h2 : scount P A true ≤ 2 := by
    have := cntF_mono X.n (fun v' => meets P v' ∧ A v' = true) (fun k => k = u ∨ k = v)
      (fun k hk => by
        cases hTk : T k
        · exact Or.inr (both.2 k hk.1 hk.2 hTk)
        · exact Or.inl (both.1 k hk.1 hk.2 hTk))
    have h' := cntF_le_two X.n u v
    unfold scount; omega
  have hh := side_handshake hG.1 hG.2.2.2 A true
  have hx : cntF X.m (RH2F.Crosses P A) = 3 := hA.1
  have h2' := hA.2.1
  omega

end sc1

end RH2F

-- ===== from SC2.lean =====
/-
  SC2 — the edge reduction of a simple cubic edge set: delete an edge `e = u v` and suppress `u` and `v` (the other
  edges `a1 = u u1`, `a2 = u u2`, `b1 = v v1`, `b2 = v v2` are replaced by new edges `u1 u2` and `v1 v2`).
  Vertices, vertex count, looplessness, cubicity, the crossing-count identity, and the transfer of 3-edge-
  connectivity and of simplicity.
-/

namespace RH2F
open MGraph
open Classical

section sc2
variable {X : MGraph} {P : Fin X.m → Prop}

theorem sc_joins_of_inc {K : MGraph} {f : Fin K.m} {x : Fin K.n} (h : K.Inc f x) : ∃ y, K.Joins f x y := by
  rcases h with h | h
  · exact ⟨(K.ends f).2, Or.inl (by rw [← h])⟩
  · exact ⟨(K.ends f).1, Or.inr (by rw [← h])⟩

/-- the data of an edge `e = u v` of `P` with the other edges `a1 = u u1`, `a2 = u u2` at `u` and `b1 = v v1`,
    `b2 = v v2` at `v` -/
structure RedData (P : Fin X.m → Prop) where
  u : Fin X.n
  v : Fin X.n
  u1 : Fin X.n
  u2 : Fin X.n
  v1 : Fin X.n
  v2 : Fin X.n
  e : Fin X.m
  a1 : Fin X.m
  a2 : Fin X.m
  b1 : Fin X.m
  b2 : Fin X.m
  he : P e
  ha1 : P a1
  ha2 : P a2
  hb1 : P b1
  hb2 : P b2
  je : X.Joins e u v
  ja1 : X.Joins a1 u u1
  ja2 : X.Joins a2 u u2
  jb1 : X.Joins b1 v v1
  jb2 : X.Joins b2 v v2
  covu : ∀ d, P d → X.Inc d u → d = e ∨ d = a1 ∨ d = a2
  covv : ∀ d, P d → X.Inc d v → d = e ∨ d = b1 ∨ d = b2
  a12 : a1 ≠ a2
  b12 : b1 ≠ b2
  huv : u ≠ v
  u1u : u1 ≠ u
  u1v : u1 ≠ v
  u2u : u2 ≠ u
  u2v : u2 ≠ v
  v1u : v1 ≠ u
  v1v : v1 ≠ v
  v2u : v2 ≠ u
  v2v : v2 ≠ v
  u12 : u1 ≠ u2
  v12 : v1 ≠ v2

/-- the other two edges at an end of an edge of a cubic edge set -/
theorem two_others (hcub : CubicOn P) {e : Fin X.m} {x : Fin X.n} (he : P e) (hex : X.Inc e x) :
    ∃ a1 a2, P a1 ∧ P a2 ∧ X.Inc a1 x ∧ X.Inc a2 x ∧ a1 ≠ a2 ∧ a1 ≠ e ∧ a2 ≠ e ∧
      ∀ d, P d → X.Inc d x → d = e ∨ d = a1 ∨ d = a2 := by
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub x ⟨e, he, hex⟩
  rcases hall e he hex with rfl | rfl | rfl
  · exact ⟨q, r, hq, hr, iq, ir, dqr, Ne.symm dpq, Ne.symm dpr, hall⟩
  · refine ⟨p, r, hp, hr, ip, ir, dpr, dpq, Ne.symm dqr, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · refine ⟨p, q, hp, hq, ip, iq, dpq, dpr, dqr, fun d hd hdx => ?_⟩
    rcases hall d hd hdx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- every edge of a simple member of 𝒢 gives reduction data -/
theorem redData_of (hG : InG X P) (hS : SimpleP P) {e : Fin X.m} (he : P e) : ∃ R : RedData P, R.e = e := by
  have je : X.Joins e (X.ends e).1 (X.ends e).2 := Or.inl rfl
  have huv : (X.ends e).1 ≠ (X.ends e).2 := MGraph.ne_of_joins hG.1 je
  obtain ⟨a1, a2, ha1, ha2, ia1, ia2, a12, a1e, a2e, covu⟩ := two_others hG.2.2.2 he (joins_inc_left je)
  obtain ⟨b1, b2, hb1, hb2, ib1, ib2, b12, b1e, b2e, covv⟩ := two_others hG.2.2.2 he (joins_inc_right je)
  obtain ⟨u1, ja1⟩ := sc_joins_of_inc ia1
  obtain ⟨u2, ja2⟩ := sc_joins_of_inc ia2
  obtain ⟨v1, jb1⟩ := sc_joins_of_inc ib1
  obtain ⟨v2, jb2⟩ := sc_joins_of_inc ib2
  have u1u : u1 ≠ (X.ends e).1 := fun h => MGraph.ne_of_joins hG.1 ja1 h.symm
  have u2u : u2 ≠ (X.ends e).1 := fun h => MGraph.ne_of_joins hG.1 ja2 h.symm
  have v1v : v1 ≠ (X.ends e).2 := fun h => MGraph.ne_of_joins hG.1 jb1 h.symm
  have v2v : v2 ≠ (X.ends e).2 := fun h => MGraph.ne_of_joins hG.1 jb2 h.symm
  have u1v : u1 ≠ (X.ends e).2 := fun h => a1e (hS _ _ _ _ ha1 he (h ▸ ja1) je)
  have u2v : u2 ≠ (X.ends e).2 := fun h => a2e (hS _ _ _ _ ha2 he (h ▸ ja2) je)
  have v1u : v1 ≠ (X.ends e).1 := fun h => b1e (hS _ _ _ _ hb1 he (h ▸ Or.symm jb1) je)
  have v2u : v2 ≠ (X.ends e).1 := fun h => b2e (hS _ _ _ _ hb2 he (h ▸ Or.symm jb2) je)
  have u12 : u1 ≠ u2 := fun h => a12 (hS _ _ _ _ ha1 ha2 ja1 (h ▸ ja2))
  have v12 : v1 ≠ v2 := fun h => b12 (hS _ _ _ _ hb1 hb2 jb1 (h ▸ jb2))
  exact ⟨⟨(X.ends e).1, (X.ends e).2, u1, u2, v1, v2, e, a1, a2, b1, b2, he, ha1, ha2, hb1, hb2, je, ja1, ja2,
    jb1, jb2, covu, covv, a12, b12, huv, u1u, u1v, u2u, u2v, v1u, v1v, v2u, v2v, u12, v12⟩, rfl⟩

namespace RedData
variable (R : RedData P)

/-! ### distinctness of the five special edges -/

theorem e_a1 : R.e ≠ R.a1 := by
  intro h
  have j := R.ja1; rw [← h] at j
  rcases joins_unique R.je j with ⟨_, h'⟩ | ⟨h', _⟩
  · exact R.u1v h'.symm
  · exact R.u1u h'.symm
theorem e_a2 : R.e ≠ R.a2 := by
  intro h
  have j := R.ja2; rw [← h] at j
  rcases joins_unique R.je j with ⟨_, h'⟩ | ⟨h', _⟩
  · exact R.u2v h'.symm
  · exact R.u2u h'.symm
theorem e_b1 : R.e ≠ R.b1 := by
  intro h
  have j := R.jb1; rw [← h] at j
  rcases joins_unique R.je j with ⟨h', _⟩ | ⟨h', _⟩
  · exact R.huv h'
  · exact R.v1u h'.symm
theorem e_b2 : R.e ≠ R.b2 := by
  intro h
  have j := R.jb2; rw [← h] at j
  rcases joins_unique R.je j with ⟨h', _⟩ | ⟨h', _⟩
  · exact R.huv h'
  · exact R.v2u h'.symm

theorem a_not_v {a : Fin X.m} {y : Fin X.n} (ja : X.Joins a R.u y) (hyv : y ≠ R.v) : ¬ X.Inc a R.v := by
  intro h
  rcases inc_of_joins ja h with h' | h'
  · exact R.huv h'.symm
  · exact hyv h'.symm
theorem b_not_u {b : Fin X.m} {y : Fin X.n} (jb : X.Joins b R.v y) (hyu : y ≠ R.u) : ¬ X.Inc b R.u := by
  intro h
  rcases inc_of_joins jb h with h' | h'
  · exact R.huv h'
  · exact hyu h'.symm

theorem a1_b1 : R.a1 ≠ R.b1 := fun h => R.a_not_v R.ja1 R.u1v (h ▸ joins_inc_left R.jb1)
theorem a1_b2 : R.a1 ≠ R.b2 := fun h => R.a_not_v R.ja1 R.u1v (h ▸ joins_inc_left R.jb2)
theorem a2_b1 : R.a2 ≠ R.b1 := fun h => R.a_not_v R.ja2 R.u2v (h ▸ joins_inc_left R.jb1)
theorem a2_b2 : R.a2 ≠ R.b2 := fun h => R.a_not_v R.ja2 R.u2v (h ▸ joins_inc_left R.jb2)

/-- an edge of `P` avoiding `u` and `v` -/
def Avoid (d : Fin X.m) : Prop := ¬ X.Inc d R.u ∧ ¬ X.Inc d R.v

/-- a `P`-edge at a vertex `w ∉ {u, v}` is one of the four side edges (at its far end) or avoids `u, v` -/
theorem at_w {d : Fin X.m} {w : Fin X.n} (hd : P d) (hdw : X.Inc d w) (hwu : w ≠ R.u) (hwv : w ≠ R.v) :
    (d = R.a1 ∧ w = R.u1) ∨ (d = R.a2 ∧ w = R.u2) ∨ (d = R.b1 ∧ w = R.v1) ∨ (d = R.b2 ∧ w = R.v2) ∨ R.Avoid d := by
  by_cases hdu : X.Inc d R.u
  · rcases R.covu d hd hdu with rfl | rfl | rfl
    · rcases inc_of_joins R.je hdw with h | h
      · exact absurd h hwu
      · exact absurd h hwv
    · rcases inc_of_joins R.ja1 hdw with h | h
      · exact absurd h hwu
      · exact Or.inl ⟨rfl, h⟩
    · rcases inc_of_joins R.ja2 hdw with h | h
      · exact absurd h hwu
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
  by_cases hdv : X.Inc d R.v
  · rcases R.covv d hd hdv with rfl | rfl | rfl
    · rcases inc_of_joins R.je hdw with h | h
      · exact absurd h hwu
      · exact absurd h hwv
    · rcases inc_of_joins R.jb1 hdw with h | h
      · exact absurd h hwv
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
    · rcases inc_of_joins R.jb2 hdw with h | h
      · exact absurd h hwv
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hdu, hdv⟩)))

theorem avoid_ne_special {d : Fin X.m} (h : R.Avoid d) :
    d ≠ R.e ∧ d ≠ R.a1 ∧ d ≠ R.a2 ∧ d ≠ R.b1 ∧ d ≠ R.b2 :=
  ⟨fun h' => h.1 (h' ▸ joins_inc_left R.je), fun h' => h.1 (h' ▸ joins_inc_left R.ja1),
   fun h' => h.1 (h' ▸ joins_inc_left R.ja2), fun h' => h.2 (h' ▸ joins_inc_left R.jb1),
   fun h' => h.2 (h' ▸ joins_inc_left R.jb2)⟩

/-! ### the reduced multigraph -/

/-- the ambient multigraph of the reduction: `X` plus the edges `u1 u2` and `v1 v2` -/
def G2 : MGraph := addEdge (addEdge X R.u1 R.u2) R.v1 R.v2

/-- an old edge `d` of `X` in `G2` -/
def oE (d : Fin X.m) : Fin R.G2.m := Fin.castSucc (Fin.castSucc d)
/-- the new edge `u1 u2` -/
def N1 : Fin R.G2.m := Fin.castSucc (Fin.last X.m)
/-- the new edge `v1 v2` -/
def N2 : Fin R.G2.m := Fin.last (X.m + 1)

theorem ends_oE (d : Fin X.m) : R.G2.ends (R.oE d) = X.ends d := by
  show (addEdge (addEdge X R.u1 R.u2) R.v1 R.v2).ends (Fin.castSucc (Fin.castSucc d)) = X.ends d
  rw [addEdge_ends_old, addEdge_ends_old]
theorem ends_N1 : R.G2.ends R.N1 = (R.u1, R.u2) := by
  show (addEdge (addEdge X R.u1 R.u2) R.v1 R.v2).ends (Fin.castSucc (Fin.last X.m)) = (R.u1, R.u2)
  rw [addEdge_ends_old, addEdge_ends_new]
theorem ends_N2 : R.G2.ends R.N2 = (R.v1, R.v2) := by
  show (addEdge (addEdge X R.u1 R.u2) R.v1 R.v2).ends (Fin.last (addEdge X R.u1 R.u2).m) = (R.v1, R.v2)
  exact addEdge_ends_new

theorem inc_oE {d : Fin X.m} {w : Fin X.n} : R.G2.Inc (R.oE d) w ↔ X.Inc d w := by
  unfold Inc; rw [ends_oE]
theorem inc_N1 {w : Fin X.n} : R.G2.Inc R.N1 w ↔ w = R.u1 ∨ w = R.u2 := by
  unfold Inc; rw [ends_N1]; exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
theorem inc_N2 {w : Fin X.n} : R.G2.Inc R.N2 w ↔ w = R.v1 ∨ w = R.v2 := by
  unfold Inc; rw [ends_N2]; exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
theorem joins_oE {d : Fin X.m} {x y : Fin X.n} : R.G2.Joins (R.oE d) x y ↔ X.Joins d x y := by
  unfold Joins; rw [ends_oE]

theorem oE_inj {d d' : Fin X.m} (h : R.oE d = R.oE d') : d = d' := castSucc_inj' (castSucc_inj' h)
theorem oE_ne_N1 (d : Fin X.m) : R.oE d ≠ R.N1 := fun h => castSucc_ne_last d (castSucc_inj' h)
theorem oE_ne_N2 (d : Fin X.m) : R.oE d ≠ R.N2 := castSucc_ne_last _
theorem N1_ne_N2 : R.N1 ≠ R.N2 := castSucc_ne_last _

theorem edge_cases (i : Fin R.G2.m) : i = R.N2 ∨ i = R.N1 ∨ ∃ d, i = R.oE d := by
  show i = Fin.last (X.m + 1) ∨ i = Fin.castSucc (Fin.last X.m) ∨ ∃ d, i = Fin.castSucc (Fin.castSucc d)
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | h
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | h'
    · exact Or.inr (Or.inr ⟨k, rfl⟩)
    · exact Or.inr (Or.inl (by rw [h']))
  · exact Or.inl h

/-- the reduced edge set: the two new edges and the old edges avoiding `u, v` -/
def redP : Fin R.G2.m → Prop := fun i => i = R.N2 ∨ i = R.N1 ∨ ∃ d, i = R.oE d ∧ P d ∧ R.Avoid d

theorem loopless_G2 (hloop : Loopless X) : Loopless R.G2 :=
  addEdge_loopless (addEdge_loopless hloop R.u12) R.v12

/-! ### vertices and vertex count -/

theorem meets_red (w : Fin X.n) : @meets R.G2 R.redP w ↔ meets P w ∧ w ≠ R.u ∧ w ≠ R.v := by
  constructor
  · rintro ⟨i, hi, hiw⟩
    rcases hi with rfl | rfl | ⟨d, rfl, hd, hav⟩
    · rcases R.inc_N2.1 hiw with rfl | rfl
      · exact ⟨⟨R.b1, R.hb1, joins_inc_right R.jb1⟩, R.v1u, R.v1v⟩
      · exact ⟨⟨R.b2, R.hb2, joins_inc_right R.jb2⟩, R.v2u, R.v2v⟩
    · rcases R.inc_N1.1 hiw with rfl | rfl
      · exact ⟨⟨R.a1, R.ha1, joins_inc_right R.ja1⟩, R.u1u, R.u1v⟩
      · exact ⟨⟨R.a2, R.ha2, joins_inc_right R.ja2⟩, R.u2u, R.u2v⟩
    · have hdw := R.inc_oE.1 hiw
      exact ⟨⟨d, hd, hdw⟩, fun h => hav.1 (h ▸ hdw), fun h => hav.2 (h ▸ hdw)⟩
  · rintro ⟨⟨d, hd, hdw⟩, hwu, hwv⟩
    rcases R.at_w hd hdw hwu hwv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hav
    · exact ⟨R.N1, Or.inr (Or.inl rfl), R.inc_N1.2 (Or.inl rfl)⟩
    · exact ⟨R.N1, Or.inr (Or.inl rfl), R.inc_N1.2 (Or.inr rfl)⟩
    · exact ⟨R.N2, Or.inl rfl, R.inc_N2.2 (Or.inl rfl)⟩
    · exact ⟨R.N2, Or.inl rfl, R.inc_N2.2 (Or.inr rfl)⟩
    · exact ⟨R.oE d, Or.inr (Or.inr ⟨d, rfl, hd, hav⟩), R.inc_oE.2 hdw⟩

theorem vcount_red : vcount R.redP + 2 = vcount P := by
  unfold vcount
  show cntF X.n (@meets R.G2 R.redP) + 2 = cntF X.n (meets P)
  rw [cntF_congr X.n _ _ R.meets_red, cntF_split X.n (meets P) (fun w => w = R.u ∨ w = R.v)]
  rw [cntF_congr X.n (fun w => meets P w ∧ (w = R.u ∨ w = R.v)) (fun w => w = R.u ∨ w = R.v)
    (fun w => ⟨fun h => h.2, fun h => ⟨h.elim (fun h' => h' ▸ ⟨R.e, R.he, joins_inc_left R.je⟩)
      (fun h' => h' ▸ ⟨R.e, R.he, joins_inc_right R.je⟩), h⟩⟩)]
  rw [cntF_pair X.n R.huv, cntF_congr X.n (fun w => meets P w ∧ w ≠ R.u ∧ w ≠ R.v)
    (fun w => meets P w ∧ ¬ (w = R.u ∨ w = R.v)) (fun w => by simp only [not_or])]
  omega

/-! ### cubicity -/

theorem cubic_red (hcub : CubicOn P) : CubicOn R.redP := by
  intro w hw
  obtain ⟨hwP, hwu, hwv⟩ := (R.meets_red w).1 hw
  let φ : Fin X.m → Fin R.G2.m := fun d =>
    if d = R.a1 ∨ d = R.a2 then R.N1 else if d = R.b1 ∨ d = R.b2 then R.N2 else R.oE d
  have φa : ∀ d, (d = R.a1 ∨ d = R.a2) → φ d = R.N1 := fun d h => by simp [φ, h]
  have φb : ∀ d, ¬ (d = R.a1 ∨ d = R.a2) → (d = R.b1 ∨ d = R.b2) → φ d = R.N2 := fun d h h' => by simp [φ, h, h']
  have φo : ∀ d, R.Avoid d → φ d = R.oE d := by
    intro d h
    obtain ⟨_, n1, n2, n3, n4⟩ := R.avoid_ne_special h
    simp [φ, n1, n2, n3, n4]
  have nab : ∀ d, (d = R.b1 ∨ d = R.b2) → ¬ (d = R.a1 ∨ d = R.a2) := by
    rintro d (rfl | rfl) (h | h)
    · exact R.a1_b1 h.symm
    · exact R.a2_b1 h.symm
    · exact R.a1_b2 h.symm
    · exact R.a2_b2 h.symm
  apply cubic_at_of_map hcub hwP φ
  · intro d hd hdw
    rcases R.at_w hd hdw hwu hwv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hav
    · rw [φa _ (Or.inl rfl)]; exact ⟨Or.inr (Or.inl rfl), R.inc_N1.2 (Or.inl rfl)⟩
    · rw [φa _ (Or.inr rfl)]; exact ⟨Or.inr (Or.inl rfl), R.inc_N1.2 (Or.inr rfl)⟩
    · rw [φb _ (nab _ (Or.inl rfl)) (Or.inl rfl)]; exact ⟨Or.inl rfl, R.inc_N2.2 (Or.inl rfl)⟩
    · rw [φb _ (nab _ (Or.inr rfl)) (Or.inr rfl)]; exact ⟨Or.inl rfl, R.inc_N2.2 (Or.inr rfl)⟩
    · rw [φo d hav]; exact ⟨Or.inr (Or.inr ⟨d, rfl, hd, hav⟩), R.inc_oE.2 hdw⟩
  · intro d d' hd hd' hdw hd'w heq
    rcases R.at_w hd hdw hwu hwv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hav <;>
      rcases R.at_w hd' hd'w hwu hwv with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | hav'
    all_goals first
      | rfl
      | exact absurd h R.u12 | exact absurd h.symm R.u12 | exact absurd h R.v12 | exact absurd h.symm R.v12
      | (rw [φa _ (Or.inl rfl), φb _ (nab _ (Or.inl rfl)) (Or.inl rfl)] at heq; exact absurd heq R.N1_ne_N2)
      | (rw [φa _ (Or.inl rfl), φb _ (nab _ (Or.inr rfl)) (Or.inr rfl)] at heq; exact absurd heq R.N1_ne_N2)
      | (rw [φa _ (Or.inr rfl), φb _ (nab _ (Or.inl rfl)) (Or.inl rfl)] at heq; exact absurd heq R.N1_ne_N2)
      | (rw [φa _ (Or.inr rfl), φb _ (nab _ (Or.inr rfl)) (Or.inr rfl)] at heq; exact absurd heq R.N1_ne_N2)
      | (rw [φb _ (nab _ (Or.inl rfl)) (Or.inl rfl), φa _ (Or.inl rfl)] at heq; exact absurd heq.symm R.N1_ne_N2)
      | (rw [φb _ (nab _ (Or.inl rfl)) (Or.inl rfl), φa _ (Or.inr rfl)] at heq; exact absurd heq.symm R.N1_ne_N2)
      | (rw [φb _ (nab _ (Or.inr rfl)) (Or.inr rfl), φa _ (Or.inl rfl)] at heq; exact absurd heq.symm R.N1_ne_N2)
      | (rw [φb _ (nab _ (Or.inr rfl)) (Or.inr rfl), φa _ (Or.inr rfl)] at heq; exact absurd heq.symm R.N1_ne_N2)
      | (rw [φa _ (Or.inl rfl), φo _ hav'] at heq; exact absurd heq.symm (R.oE_ne_N1 _))
      | (rw [φa _ (Or.inr rfl), φo _ hav'] at heq; exact absurd heq.symm (R.oE_ne_N1 _))
      | (rw [φb _ (nab _ (Or.inl rfl)) (Or.inl rfl), φo _ hav'] at heq; exact absurd heq.symm (R.oE_ne_N2 _))
      | (rw [φb _ (nab _ (Or.inr rfl)) (Or.inr rfl), φo _ hav'] at heq; exact absurd heq.symm (R.oE_ne_N2 _))
      | (rw [φo _ hav, φa _ (Or.inl rfl)] at heq; exact absurd heq (R.oE_ne_N1 _))
      | (rw [φo _ hav, φa _ (Or.inr rfl)] at heq; exact absurd heq (R.oE_ne_N1 _))
      | (rw [φo _ hav, φb _ (nab _ (Or.inl rfl)) (Or.inl rfl)] at heq; exact absurd heq (R.oE_ne_N2 _))
      | (rw [φo _ hav, φb _ (nab _ (Or.inr rfl)) (Or.inr rfl)] at heq; exact absurd heq (R.oE_ne_N2 _))
      | (rw [φo _ hav, φo _ hav'] at heq; exact R.oE_inj heq)
  · intro j hj hjw
    rcases hj with rfl | rfl | ⟨d, rfl, hd, hav⟩
    · rcases R.inc_N2.1 hjw with rfl | rfl
      · exact ⟨R.b1, R.hb1, joins_inc_right R.jb1, φb _ (nab _ (Or.inl rfl)) (Or.inl rfl)⟩
      · exact ⟨R.b2, R.hb2, joins_inc_right R.jb2, φb _ (nab _ (Or.inr rfl)) (Or.inr rfl)⟩
    · rcases R.inc_N1.1 hjw with rfl | rfl
      · exact ⟨R.a1, R.ha1, joins_inc_right R.ja1, φa _ (Or.inl rfl)⟩
      · exact ⟨R.a2, R.ha2, joins_inc_right R.ja2, φa _ (Or.inr rfl)⟩
    · exact ⟨d, hd, R.inc_oE.1 hjw, φo d hav⟩

end RedData

end sc2

end RH2F

-- ===== from SC2b.lean =====
/-
  SC2b — the crossing-count identity of the edge reduction, transfer of 3-edge-connectivity (when no bad 3-edge-cut
  separates `u` from `v`), the dense 4-set lemma, and transfer of simplicity.
-/

namespace RH2F
open MGraph
open Classical

section sc2b

/-! ### generic facts -/

theorem ite_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then 1 else 0 : Nat) = if q then 1 else 0 := by
  by_cases hq : q
  · rw [if_pos (h.2 hq), if_pos hq]
  · rw [if_neg (fun hp => hq (h.1 hp)), if_neg hq]

theorem cntF_or_le (n : Nat) (A B : Fin n → Prop) : cntF n (fun k => A k ∨ B k) ≤ cntF n A + cntF n B := by
  have := cntF_add_le n (fun k => A k ∨ B k) (fun _ => False) A B (fun i => by
    by_cases ha : A i <;> by_cases hb : B i <;> simp [ha, hb])
  rw [cntF_eq_zero n (fun _ => False) (fun _ h => h)] at this
  omega

theorem cntF_guard3 (n : Nat) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (p q r : Prop)
    [Decidable p] [Decidable q] [Decidable r] :
    cntF n (fun k => (k = a ∧ p) ∨ (k = b ∧ q) ∨ (k = c ∧ r)) =
      (if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) := by
  rw [cntF_split n _ (fun k => k = a)]
  rw [cntF_split n (fun k => ((k = a ∧ p) ∨ (k = b ∧ q) ∨ (k = c ∧ r)) ∧ ¬ k = a) (fun k => k = b)]
  have e1 : cntF n (fun k => ((k = a ∧ p) ∨ (k = b ∧ q) ∨ (k = c ∧ r)) ∧ k = a) = if p then 1 else 0 := by
    by_cases hp : p
    · rw [if_pos hp, ← cntF_single n a]; apply cntF_congr; intro k
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨Or.inl ⟨rfl, hp⟩, rfl⟩
    · rw [if_neg hp]; apply cntF_eq_zero; intro k h
      rcases h with ⟨h | h | h, hk⟩
      · exact hp h.2
      · exact hab (hk.symm.trans h.1)
      · exact hac (hk.symm.trans h.1)
  have e2 : cntF n (fun k => (((k = a ∧ p) ∨ (k = b ∧ q) ∨ (k = c ∧ r)) ∧ ¬ k = a) ∧ k = b) =
      if q then 1 else 0 := by
    by_cases hq : q
    · rw [if_pos hq, ← cntF_single n b]; apply cntF_congr; intro k
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨⟨Or.inr (Or.inl ⟨rfl, hq⟩), Ne.symm hab⟩, rfl⟩
    · rw [if_neg hq]; apply cntF_eq_zero; intro k h
      rcases h with ⟨⟨h | h | h, hna⟩, hkb⟩
      · exact hna h.1
      · exact hq h.2
      · exact hbc (hkb.symm.trans h.1)
  have e3 : cntF n (fun k => (((k = a ∧ p) ∨ (k = b ∧ q) ∨ (k = c ∧ r)) ∧ ¬ k = a) ∧ ¬ k = b) =
      if r then 1 else 0 := by
    by_cases hr : r
    · rw [if_pos hr, ← cntF_single n c]; apply cntF_congr; intro k
      constructor
      · rintro ⟨⟨h | h | h, h1⟩, h2⟩
        · exact absurd h.1 h1
        · exact absurd h.1 h2
        · exact h.1
      · rintro rfl; exact ⟨⟨Or.inr (Or.inr ⟨rfl, hr⟩), Ne.symm hac⟩, Ne.symm hbc⟩
    · rw [if_neg hr]; apply cntF_eq_zero; intro k h
      rcases h with ⟨⟨h | h | h, h1⟩, h2⟩
      · exact h1 h.1
      · exact h2 h.1
      · exact hr h.2
  rw [e1, e2, e3]; omega

variable {Y : MGraph} {Q : Fin Y.m → Prop}

theorem two_le_scount {S : Fin Y.n → Bool} {b : Bool} {w w' : Fin Y.n} (hw : meets Q w) (hw' : meets Q w')
    (hne : w ≠ w') (h1 : S w = b) (h2 : S w' = b) : 2 ≤ scount Q S b := by
  unfold scount
  rw [← cntF_pair Y.n hne]
  apply cntF_mono
  rintro k (rfl | rfl)
  · exact ⟨hw, h1⟩
  · exact ⟨hw', h2⟩

/-- 3-edge-connectivity in counting form: every cut with vertices of `Q` on both sides is crossed by at least three
    edges of `Q` -/
def Conn3 (Q : Fin Y.m → Prop) : Prop :=
  ∀ (S : Fin Y.n → Bool) x y, meets Q x → S x = true → meets Q y → S y = false → 3 ≤ xc Q S

theorem conn3_of (hG : InG Y Q) (h3 : ∀ S, ¬ TwoCut Q S) : Conn3 Q :=
  fun S _ _ hx hSx hy hSy => three_cross hG h3 S hx hSx hy hSy

/-- a separating labelling with vertices on both sides crosses at least three edges, in either orientation -/
theorem conn3_ne (hc : Conn3 Q) (S : Fin Y.n → Bool) {x y : Fin Y.n} (hx : meets Q x) (hy : meets Q y)
    (hxy : S x ≠ S y) : 3 ≤ xc Q S := by
  cases hSx : S x
  · have hSy : S y = true := by cases h : S y <;> simp_all
    have := hc (fun w => !S w) x y hx (by simp [hSx]) hy (by simp [hSy])
    rwa [xc_not] at this
  · have hSy : S y = false := by cases h : S y <;> simp_all
    exact hc S x y hx hSx hy hSy

/-- a loopless cubic 3-edge-connected edge set is a member of 𝒢 without 2-edge-cuts -/
theorem inG_of_conn3 (hloop : Loopless Y) (hcub : CubicOn Q) (hc : Conn3 Q) : InG Y Q ∧ ∀ S, ¬ TwoCut Q S := by
  refine ⟨⟨hloop, ?_, ?_, hcub⟩, ?_⟩
  · intro U hU f g hf hg
    by_contra hne
    have h3 := conn3_ne hc U (x := (Y.ends f).1) (y := (Y.ends g).1) ⟨f, hf, Or.inl rfl⟩ ⟨g, hg, Or.inl rfl⟩ hne
    have h0 : xc Q U = 0 := cntF_eq_zero Y.m _ (fun d hd => hd.2 (hU d hd.1))
    omega
  · intro e he B
    have h3 := conn3_ne hc B.U (x := (Y.ends e).1) (y := (Y.ends e).2) ⟨e, he, Or.inl rfl⟩ ⟨e, he, Or.inr rfl⟩
      (by rw [B.hu, B.hv]; decide)
    have h1 : xc Q B.U ≤ 1 := by
      have := cntF_mono Y.m (RH2F.Crosses Q B.U) (fun k => k = e) (fun d hd => by
        by_contra hde; exact hd.2 (B.sep d hd.1 hde))
      rw [cntF_single] at this; exact this
    omega
  · rintro S ⟨e1, e2, _, c1, _, hall⟩
    have h3 := conn3_ne hc S (x := (Y.ends e1).1) (y := (Y.ends e1).2) ⟨e1, c1.1, Or.inl rfl⟩
      ⟨e1, c1.1, Or.inr rfl⟩ c1.2
    have h2 : xc Q S ≤ 2 := le_trans (cntF_mono Y.m _ _ hall) (cntF_le_two Y.m e1 e2)
    omega

/-- **dense 4-sets**: in a member of 𝒢 without 2-edge-cuts on at least 6 vertices, at most four vertices never span five
    edges -/
theorem small_dense (hG : InG Y Q) (h3 : ∀ S, ¬ TwoCut Q S) (h6 : 6 ≤ vcount Q) (W : Fin Y.n → Bool)
    (hW : scount Q W true ≤ 4) (hin : 5 ≤ cntF Y.m (inner Q W true)) : False := by
  have hh := side_handshake hG.1 hG.2.2.2 W true
  obtain ⟨f, hf⟩ := cntF_pos Y.m _ (by omega : 0 < cntF Y.m (inner Q W true))
  have hsp := vcount_split Q W
  have hout : 1 ≤ scount Q W false := by omega
  obtain ⟨y, hy⟩ := cntF_pos Y.n (fun v => meets Q v ∧ W v = false) (by unfold scount at hout; omega)
  have hx3 := conn3_ne (conn3_of hG h3) W (x := (Y.ends f).1) (y := y) ⟨f, hf.1, Or.inl rfl⟩ hy.1
    (by rw [hf.2.1, hy.2]; decide)
  unfold xc at hx3
  omega

end sc2b

section sc2c
variable {X : MGraph} {P : Fin X.m → Prop}

namespace RedData
variable (R : RedData P)

/-! ### the crossing-count identity -/

/-- a labelling of the reduced vertices extended to `u, v`: `u` gets the value of `u1`, `v` that of `v1` -/
def liftS (S : Fin X.n → Bool) : Fin X.n → Bool :=
  fun w => if w = R.u then S R.u1 else if w = R.v then S R.v1 else S w

theorem liftS_o (S : Fin X.n → Bool) {w : Fin X.n} (hu : w ≠ R.u) (hv : w ≠ R.v) : R.liftS S w = S w := by
  simp [liftS, hu, hv]
theorem liftS_u (S : Fin X.n → Bool) : R.liftS S R.u = S R.u1 := by simp [liftS]
theorem liftS_v (S : Fin X.n → Bool) : R.liftS S R.v = S R.v1 := by simp [liftS, Ne.symm R.huv]

theorem red_oE {d : Fin X.m} : R.redP (R.oE d) ↔ P d ∧ R.Avoid d := by
  constructor
  · rintro (h | h | ⟨d', h, hd, hav⟩)
    · exact absurd h (R.oE_ne_N2 d)
    · exact absurd h (R.oE_ne_N1 d)
    · rw [R.oE_inj h]; exact ⟨hd, hav⟩
  · rintro ⟨hd, hav⟩; exact Or.inr (Or.inr ⟨d, rfl, hd, hav⟩)

theorem crosses_of_joins {d : Fin X.m} {x y : Fin X.n} (hj : X.Joins d x y) (S' : Fin X.n → Bool) :
    RH2F.Crosses P S' d ↔ P d ∧ S' x ≠ S' y := by
  unfold RH2F.Crosses
  rcases hj with h | h <;> rw [h]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h' => h2 h'.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h' => h2 h'.symm⟩

/-- **crossing-count identity**: `xc(red, S) + [S u1 ≠ S v1] = xc(P, liftS S)` -/
theorem xc_red (S : Fin X.n → Bool) :
    xc R.redP S + (if S R.u1 ≠ S R.v1 then 1 else 0) = xc P (R.liftS S) := by
  -- the reduced side
  have hL : xc R.redP S = cntF X.m (fun d => (P d ∧ R.Avoid d) ∧ S (X.ends d).1 ≠ S (X.ends d).2) +
      (if S R.u1 ≠ S R.u2 then 1 else 0) + (if S R.v1 ≠ S R.v2 then 1 else 0) := by
    unfold xc
    show cntF (X.m + 1 + 1) (RH2F.Crosses R.redP S) = _
    rw [cntF_succ, cntF_succ]
    have c0 : ∀ d, RH2F.Crosses R.redP S (Fin.castSucc (Fin.castSucc d)) ↔
        (P d ∧ R.Avoid d) ∧ S (X.ends d).1 ≠ S (X.ends d).2 := by
      intro d
      show R.redP (R.oE d) ∧ S (R.G2.ends (R.oE d)).1 ≠ S (R.G2.ends (R.oE d)).2 ↔ _
      rw [R.red_oE, R.ends_oE]
    have c1 : RH2F.Crosses R.redP S (Fin.castSucc (Fin.last X.m)) ↔ S R.u1 ≠ S R.u2 := by
      show R.redP R.N1 ∧ S (R.G2.ends R.N1).1 ≠ S (R.G2.ends R.N1).2 ↔ _
      rw [R.ends_N1]
      exact ⟨fun h => h.2, fun h => ⟨Or.inr (Or.inl rfl), h⟩⟩
    have c2 : RH2F.Crosses R.redP S (Fin.last (X.m + 1)) ↔ S R.v1 ≠ S R.v2 := by
      show R.redP R.N2 ∧ S (R.G2.ends R.N2).1 ≠ S (R.G2.ends R.N2).2 ↔ _
      rw [R.ends_N2]
      exact ⟨fun h => h.2, fun h => ⟨Or.inl rfl, h⟩⟩
    rw [cntF_congr X.m _ _ c0, ite_iff c1, ite_iff c2]
  -- the original side
  have hR : xc P (R.liftS S) = cntF X.m (fun d => (P d ∧ R.Avoid d) ∧ S (X.ends d).1 ≠ S (X.ends d).2) +
      ((if S R.u1 ≠ S R.v1 then 1 else 0) + (if S R.u1 ≠ S R.u2 then 1 else 0) +
        (if S R.v1 ≠ S R.v2 then 1 else 0)) := by
    unfold xc
    rw [cntF_split X.m _ R.Avoid]
    congr 1
    · apply cntF_congr; intro d
      constructor
      · rintro ⟨⟨hd, hne⟩, hav⟩
        refine ⟨⟨hd, hav⟩, ?_⟩
        rwa [R.liftS_o S (fun h => hav.1 (h ▸ Or.inl rfl)) (fun h => hav.2 (h ▸ Or.inl rfl)),
          R.liftS_o S (fun h => hav.1 (h ▸ Or.inr rfl)) (fun h => hav.2 (h ▸ Or.inr rfl))] at hne
      · rintro ⟨⟨hd, hav⟩, hne⟩
        refine ⟨⟨hd, ?_⟩, hav⟩
        rwa [R.liftS_o S (fun h => hav.1 (h ▸ Or.inl rfl)) (fun h => hav.2 (h ▸ Or.inl rfl)),
          R.liftS_o S (fun h => hav.1 (h ▸ Or.inr rfl)) (fun h => hav.2 (h ▸ Or.inr rfl))]
    · rw [← cntF_guard3 X.m R.e_a2 R.e_b2 R.a2_b2]
      apply cntF_congr; intro d
      have ce := crosses_of_joins (P := P) R.je (R.liftS S)
      have ca1 := crosses_of_joins (P := P) R.ja1 (R.liftS S)
      have ca2 := crosses_of_joins (P := P) R.ja2 (R.liftS S)
      have cb1 := crosses_of_joins (P := P) R.jb1 (R.liftS S)
      have cb2 := crosses_of_joins (P := P) R.jb2 (R.liftS S)
      rw [R.liftS_u, R.liftS_v] at ce
      rw [R.liftS_u, R.liftS_o S R.u1u R.u1v] at ca1
      rw [R.liftS_u, R.liftS_o S R.u2u R.u2v] at ca2
      rw [R.liftS_v, R.liftS_o S R.v1u R.v1v] at cb1
      rw [R.liftS_v, R.liftS_o S R.v2u R.v2v] at cb2
      constructor
      · rintro ⟨hc, hav⟩
        have hd := hc.1
        unfold Avoid at hav
        by_cases hdu : X.Inc d R.u
        · rcases R.covu d hd hdu with rfl | rfl | rfl
          · exact Or.inl ⟨rfl, (ce.1 hc).2⟩
          · exact absurd rfl (ca1.1 hc).2
          · exact Or.inr (Or.inl ⟨rfl, (ca2.1 hc).2⟩)
        · have hdv : X.Inc d R.v := by by_contra h; exact hav ⟨hdu, h⟩
          rcases R.covv d hd hdv with rfl | rfl | rfl
          · exact Or.inl ⟨rfl, (ce.1 hc).2⟩
          · exact absurd rfl (cb1.1 hc).2
          · exact Or.inr (Or.inr ⟨rfl, (cb2.1 hc).2⟩)
      · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
        · exact ⟨ce.2 ⟨R.he, h⟩, fun hav => hav.1 (joins_inc_left R.je)⟩
        · exact ⟨ca2.2 ⟨R.ha2, h⟩, fun hav => hav.1 (joins_inc_left R.ja2)⟩
        · exact ⟨cb2.2 ⟨R.hb2, h⟩, fun hav => hav.2 (joins_inc_left R.jb2)⟩
  rw [hL, hR]; omega

/-! ### 3-edge-connectivity of the reduction -/

/-- no 3-edge-cut with at least two vertices of `P` on each side separates `u` from `v` -/
def NoBad : Prop :=
  ∀ T : Fin X.n → Bool, xc P T = 3 → T R.u = true → T R.v = false → 2 ≤ scount P T true → 2 ≤ scount P T false →
    False

theorem conn3_red (hc : Conn3 P) (hnb : R.NoBad) : Conn3 R.redP := by
  intro S x y hx hSx hy hSy
  obtain ⟨hxP, hxu, hxv⟩ := (R.meets_red x).1 hx
  obtain ⟨hyP, hyu, hyv⟩ := (R.meets_red y).1 hy
  have hid := R.xc_red S
  have h3 := conn3_ne hc (R.liftS S) hxP hyP (by rw [R.liftS_o S hxu hxv, R.liftS_o S hyu hyv, hSx, hSy]; decide)
  by_contra hlt
  push_neg at hlt
  have hne : S R.u1 ≠ S R.v1 := by
    intro h; rw [if_neg (fun h' => h' h)] at hid; omega
  rw [if_pos hne] at hid
  have hx3 : xc P (R.liftS S) = 3 := by omega
  have mu : meets P R.u := ⟨R.e, R.he, joins_inc_left R.je⟩
  have mv : meets P R.v := ⟨R.e, R.he, joins_inc_right R.je⟩
  cases hu1 : S R.u1
  · -- `T = ¬ liftS S`
    have hv1 : S R.v1 = true := by cases h : S R.v1 <;> simp_all
    apply hnb (fun w => !R.liftS S w) (by rw [xc_not]; exact hx3) (by simp [R.liftS_u, hu1])
      (by simp [R.liftS_v, hv1])
    · exact two_le_scount mu hyP (Ne.symm hyu) (by simp [R.liftS_u, hu1]) (by simp [R.liftS_o S hyu hyv, hSy])
    · exact two_le_scount mv hxP (Ne.symm hxv) (by simp [R.liftS_v, hv1]) (by simp [R.liftS_o S hxu hxv, hSx])
  · have hv1 : S R.v1 = false := by cases h : S R.v1 <;> simp_all
    apply hnb (R.liftS S) hx3 (by rw [R.liftS_u, hu1]) (by rw [R.liftS_v, hv1])
    · exact two_le_scount mu hxP (Ne.symm hxu) (by rw [R.liftS_u, hu1]) (by rw [R.liftS_o S hxu hxv, hSx])
    · exact two_le_scount mv hyP (Ne.symm hyv) (by rw [R.liftS_v, hv1]) (by rw [R.liftS_o S hyu hyv, hSy])

/-! ### simplicity of the reduction -/

theorem joins_N1 {x y : Fin X.n} (h : R.G2.Joins R.N1 x y) : (x = R.u1 ∧ y = R.u2) ∨ (x = R.u2 ∧ y = R.u1) := by
  unfold Joins at h; rw [R.ends_N1] at h
  rcases h with h | h
  · exact Or.inl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩
  · exact Or.inr ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩
theorem joins_N2 {x y : Fin X.n} (h : R.G2.Joins R.N2 x y) : (x = R.v1 ∧ y = R.v2) ∨ (x = R.v2 ∧ y = R.v1) := by
  unfold Joins at h; rw [R.ends_N2] at h
  rcases h with h | h
  · exact Or.inl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩
  · exact Or.inr ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩

theorem simple_red (hS : SimpleP P) (hN1 : ∀ f, P f → R.Avoid f → ¬ X.Joins f R.u1 R.u2)
    (hN2 : ∀ f, P f → R.Avoid f → ¬ X.Joins f R.v1 R.v2)
    (h12 : ¬ ((R.u1 = R.v1 ∧ R.u2 = R.v2) ∨ (R.u1 = R.v2 ∧ R.u2 = R.v1))) : SimpleP R.redP := by
  intro f g x y hf hg jf jg
  have n1o : ∀ d, P d → R.Avoid d → R.G2.Joins R.N1 x y → R.G2.Joins (R.oE d) x y → False := by
    intro d hd hav j1 jo
    have jd := R.joins_oE.1 jo
    rcases R.joins_N1 j1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hN1 d hd hav jd
    · exact hN1 d hd hav (Or.symm jd)
  have n2o : ∀ d, P d → R.Avoid d → R.G2.Joins R.N2 x y → R.G2.Joins (R.oE d) x y → False := by
    intro d hd hav j1 jo
    have jd := R.joins_oE.1 jo
    rcases R.joins_N2 j1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hN2 d hd hav jd
    · exact hN2 d hd hav (Or.symm jd)
  have n12 : R.G2.Joins R.N1 x y → R.G2.Joins R.N2 x y → False := by
    intro j1 j2
    rcases R.joins_N1 j1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases R.joins_N2 j2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 (Or.inl ⟨h1, h2⟩)
    · exact h12 (Or.inr ⟨h1, h2⟩)
    · exact h12 (Or.inr ⟨h2, h1⟩)
    · exact h12 (Or.inl ⟨h2, h1⟩)
  rcases hf with rfl | rfl | ⟨d, rfl, hd, hav⟩ <;> rcases hg with rfl | rfl | ⟨d', rfl, hd', hav'⟩
  · rfl
  · exact absurd (n12 jg jf) id
  · exact absurd (n2o d' hd' hav' jf jg) id
  · exact absurd (n12 jf jg) id
  · rfl
  · exact absurd (n1o d' hd' hav' jf jg) id
  · exact absurd (n2o d hd hav jg jf) id
  · exact absurd (n1o d hd hav jg jf) id
  · rw [hS d d' x y hd hd' (R.joins_oE.1 jf) (R.joins_oE.1 jg)]

/-- **the reduction is in 𝒮** when no bad 3-edge-cut separates `u, v` and no parallel pair appears -/
theorem inS_red (hG : InG X P) (hS : SimpleP P) (h3 : ∀ S, ¬ TwoCut P S) (hnb : R.NoBad)
    (hN1 : ∀ f, P f → R.Avoid f → ¬ X.Joins f R.u1 R.u2) (hN2 : ∀ f, P f → R.Avoid f → ¬ X.Joins f R.v1 R.v2)
    (h12 : ¬ ((R.u1 = R.v1 ∧ R.u2 = R.v2) ∨ (R.u1 = R.v2 ∧ R.u2 = R.v1))) : InS R.G2 R.redP := by
  obtain ⟨hG', h3'⟩ := inG_of_conn3 (R.loopless_G2 hG.1) (R.cubic_red hG.2.2.2) (R.conn3_red (conn3_of hG h3) hnb)
  exact ⟨hG', R.simple_red hS hN1 hN2 h12, h3'⟩

/-! ### the parallel-pair conditions -/

/-- the four vertices `u, v, x, y` as a side -/
def side4 (x y : Fin X.n) : Fin X.n → Bool := fun w => decide (w = R.u ∨ w = R.v ∨ w = x ∨ w = y)

theorem side4_le (x y : Fin X.n) : scount P (R.side4 x y) true ≤ 4 := by
  unfold scount
  have h1 := cntF_mono X.n (fun w => meets P w ∧ R.side4 x y w = true)
    (fun w => (w = R.u ∨ w = R.v) ∨ (w = x ∨ w = y)) (fun w hw => by
      have := hw.2; simp only [side4, decide_eq_true_eq] at this
      rcases this with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  have h2 := cntF_or_le X.n (fun w => w = R.u ∨ w = R.v) (fun w => w = x ∨ w = y)
  have h3 := cntF_le_two X.n R.u R.v
  have h4 := cntF_le_two X.n x y
  omega

theorem inner4 {x y : Fin X.n} {d : Fin X.m} (hd : P d) {p q : Fin X.n} (hj : X.Joins d p q)
    (hp : p = R.u ∨ p = R.v ∨ p = x ∨ p = y) (hq : q = R.u ∨ q = R.v ∨ q = x ∨ q = y) :
    inner P (R.side4 x y) true d := by
  refine ⟨hd, ?_, ?_⟩ <;> rcases hj with h | h <;> rw [h] <;> simp [side4, hp, hq]

/-- five distinct edges inside `{u, v, x, y}` are impossible -/
theorem five_in {x y : Fin X.n} (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (h6 : 6 ≤ vcount P)
    {f1 f2 : Fin X.m} (hf1 : inner P (R.side4 x y) true f1) (hf2 : inner P (R.side4 x y) true f2) (h12 : f1 ≠ f2)
    (e1 : f1 ≠ R.e ∧ f1 ≠ R.a1 ∧ f1 ≠ R.a2) (e2 : f2 ≠ R.e ∧ f2 ≠ R.a1 ∧ f2 ≠ R.a2)
    (ha1 : inner P (R.side4 x y) true R.a1) (ha2 : inner P (R.side4 x y) true R.a2)
    (hee : inner P (R.side4 x y) true R.e) : False := by
  apply small_dense hG h3 h6 (R.side4 x y) (R.side4_le x y)
  rw [cntF_split X.m _ (fun k => k = R.e ∨ k = R.a1 ∨ k = R.a2)]
  have c1 : 3 ≤ cntF X.m (fun k => inner P (R.side4 x y) true k ∧ (k = R.e ∨ k = R.a1 ∨ k = R.a2)) := by
    rw [← cntF_triple X.m R.e_a1 R.e_a2 R.a12]
    apply cntF_mono
    rintro k (rfl | rfl | rfl)
    · exact ⟨hee, Or.inl rfl⟩
    · exact ⟨ha1, Or.inr (Or.inl rfl)⟩
    · exact ⟨ha2, Or.inr (Or.inr rfl)⟩
  have c2 : 2 ≤ cntF X.m (fun k => inner P (R.side4 x y) true k ∧ ¬ (k = R.e ∨ k = R.a1 ∨ k = R.a2)) := by
    rw [← cntF_pair X.m h12]
    apply cntF_mono
    rintro k (rfl | rfl)
    · exact ⟨hf1, by rintro (h | h | h); exact e1.1 h; exact e1.2.1 h; exact e1.2.2 h⟩
    · exact ⟨hf2, by rintro (h | h | h); exact e2.1 h; exact e2.2.1 h; exact e2.2.2 h⟩
  omega

theorem h12_of (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (h6 : 6 ≤ vcount P) :
    ¬ ((R.u1 = R.v1 ∧ R.u2 = R.v2) ∨ (R.u1 = R.v2 ∧ R.u2 = R.v1)) := by
  have iE : inner P (R.side4 R.u1 R.u2) true R.e := R.inner4 R.he R.je (by simp) (by simp)
  have iA1 : inner P (R.side4 R.u1 R.u2) true R.a1 := R.inner4 R.ha1 R.ja1 (by simp) (by simp)
  have iA2 : inner P (R.side4 R.u1 R.u2) true R.a2 := R.inner4 R.ha2 R.ja2 (by simp) (by simp)
  have ne1 : R.b1 ≠ R.e ∧ R.b1 ≠ R.a1 ∧ R.b1 ≠ R.a2 := ⟨Ne.symm R.e_b1, Ne.symm R.a1_b1, Ne.symm R.a2_b1⟩
  have ne2 : R.b2 ≠ R.e ∧ R.b2 ≠ R.a1 ∧ R.b2 ≠ R.a2 := ⟨Ne.symm R.e_b2, Ne.symm R.a1_b2, Ne.symm R.a2_b2⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact R.five_in hG h3 h6 (R.inner4 R.hb1 R.jb1 (by simp) (by simp [← h1]))
      (R.inner4 R.hb2 R.jb2 (by simp) (by simp [← h2])) R.b12 ne1 ne2 iA1 iA2 iE
  · exact R.five_in hG h3 h6 (R.inner4 R.hb1 R.jb1 (by simp) (by simp [← h2]))
      (R.inner4 R.hb2 R.jb2 (by simp) (by simp [← h1])) R.b12 ne1 ne2 iA1 iA2 iE

/-- a common neighbour `c ∈ {u1, u2} ∩ {v1, v2}` excludes an edge `u1 u2` avoiding `u, v` -/
theorem hN1_of_common (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (h6 : 6 ≤ vcount P) {c : Fin X.n}
    (hcu : c = R.u1 ∨ c = R.u2) (hcv : c = R.v1 ∨ c = R.v2) : ∀ f, P f → R.Avoid f → ¬ X.Joins f R.u1 R.u2 := by
  intro f hf hav jf
  obtain ⟨ne1, ne2, ne3, ne4, ne5⟩ := R.avoid_ne_special hav
  have iE : inner P (R.side4 R.u1 R.u2) true R.e := R.inner4 R.he R.je (by simp) (by simp)
  have iA1 : inner P (R.side4 R.u1 R.u2) true R.a1 := R.inner4 R.ha1 R.ja1 (by simp) (by simp)
  have iA2 : inner P (R.side4 R.u1 R.u2) true R.a2 := R.inner4 R.ha2 R.ja2 (by simp) (by simp)
  have iF : inner P (R.side4 R.u1 R.u2) true f := R.inner4 hf jf (by simp) (by simp)
  have hc4 : c = R.u ∨ c = R.v ∨ c = R.u1 ∨ c = R.u2 := by
    rcases hcu with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hcv with rfl | rfl
  · exact R.five_in hG h3 h6 iF (R.inner4 R.hb1 R.jb1 (by simp) hc4)
      (fun h => ne4 h) ⟨ne1, ne2, ne3⟩ ⟨Ne.symm R.e_b1, Ne.symm R.a1_b1, Ne.symm R.a2_b1⟩ iA1 iA2 iE
  · exact R.five_in hG h3 h6 iF (R.inner4 R.hb2 R.jb2 (by simp) hc4)
      (fun h => ne5 h) ⟨ne1, ne2, ne3⟩ ⟨Ne.symm R.e_b2, Ne.symm R.a1_b2, Ne.symm R.a2_b2⟩
      iA1 iA2 iE

end RedData

end sc2c

end RH2F

-- ===== from SC3.lean =====
/-
  SC3 — the edge insertion `Ins(H, i, j)` (subdivide the distinct edges `i`, `j` by new vertices `N0`, `N1` and join
  `N0 N1`) and the lifting lemma: an isomorphism of the edge reduction of `P` onto `H` extends to an isomorphism of
  `P` onto `Ins(H, i, j)`, where `i`, `j` are the images of the new edges `u1 u2`, `v1 v2`.
-/

namespace RH2F
open MGraph
open Classical

section sc3

/-! ### `Ins(H, i, j)` -/

/-- `Ins(H, i, j)`: edge `i = x y` becomes `x N0` and the new edge `N0 y` (index `m`) is added; edge `j = x' y'`
    becomes `x' N1` and the new edge `N1 y'` (index `m + 1`) is added; the new edge `N0 N1` has index `m + 2` -/
def insG (H : MGraph) (i j : Fin H.m) : MGraph where
  n := H.n + 2
  m := H.m + 3
  ends := fun e =>
    if h : e.val < H.m then
      (if e.val = i.val then (ov H (H.ends i).1, nv0 H)
       else if e.val = j.val then (ov H (H.ends j).1, nv1 H)
       else (ov H (H.ends ⟨e.val, h⟩).1, ov H (H.ends ⟨e.val, h⟩).2))
    else if e.val = H.m then (nv0 H, ov H (H.ends i).2)
    else if e.val = H.m + 1 then (nv1 H, ov H (H.ends j).2)
    else (nv0 H, nv1 H)

section insends
variable (H : MGraph) (i j : Fin H.m)

def xe (e : Fin H.m) : Fin (insG H i j).m := Fin.castAdd 3 e
def xm0 : Fin (insG H i j).m := ⟨H.m, by show H.m < H.m + 3; omega⟩
def xm1 : Fin (insG H i j).m := ⟨H.m + 1, by show H.m + 1 < H.m + 3; omega⟩
def xm2 : Fin (insG H i j).m := ⟨H.m + 2, by show H.m + 2 < H.m + 3; omega⟩

theorem insG_ends_i : (insG H i j).ends (xe H i j i) = (ov H (H.ends i).1, nv0 H) := by
  simp [insG, xe]

theorem insG_ends_j (hij : i ≠ j) : (insG H i j).ends (xe H i j j) = (ov H (H.ends j).1, nv1 H) := by
  have h' : j.val ≠ i.val := fun h'' => hij (Fin.ext h''.symm)
  simp [insG, xe, h']

theorem insG_ends_old {e : Fin H.m} (hi : e ≠ i) (hj : e ≠ j) :
    (insG H i j).ends (xe H i j e) = (ov H (H.ends e).1, ov H (H.ends e).2) := by
  have hi' : e.val ≠ i.val := fun h'' => hi (Fin.ext h'')
  have hj' : e.val ≠ j.val := fun h'' => hj (Fin.ext h'')
  simp [insG, xe, hi', hj']

theorem insG_ends_m0 : (insG H i j).ends (xm0 H i j) = (nv0 H, ov H (H.ends i).2) := by simp [insG, xm0]
theorem insG_ends_m1 : (insG H i j).ends (xm1 H i j) = (nv1 H, ov H (H.ends j).2) := by
  simp [insG, xm1]
theorem insG_ends_m2 : (insG H i j).ends (xm2 H i j) = (nv0 H, nv1 H) := by
  simp [insG, xm2]

theorem ins_edge_cases (k : Fin (insG H i j).m) :
    (∃ e, k = xe H i j e) ∨ k = xm0 H i j ∨ k = xm1 H i j ∨ k = xm2 H i j := by
  have hk : k.val < H.m + 3 := k.isLt
  by_cases h : k.val < H.m
  · exact Or.inl ⟨⟨k.val, h⟩, Fin.ext rfl⟩
  · by_cases h0 : k.val = H.m
    · exact Or.inr (Or.inl (Fin.ext h0))
    · by_cases h1 : k.val = H.m + 1
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h1)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by show k.val = H.m + 2; omega))))

theorem xe_inj {e e' : Fin H.m} (h : xe H i j e = xe H i j e') : e = e' := by
  have := congrArg Fin.val h; exact Fin.ext (by simpa [xe] using this)
theorem xe_ne_m0 (e : Fin H.m) : xe H i j e ≠ xm0 H i j := fun h => by
  have := congrArg Fin.val h; simp [xe, xm0] at this; omega
theorem xe_ne_m1 (e : Fin H.m) : xe H i j e ≠ xm1 H i j := fun h => by
  have := congrArg Fin.val h; simp [xe, xm1] at this; omega
theorem xe_ne_m2 (e : Fin H.m) : xe H i j e ≠ xm2 H i j := fun h => by
  have := congrArg Fin.val h; simp [xe, xm2] at this; omega
theorem xm01 : xm0 H i j ≠ xm1 H i j := fun h => by have := congrArg Fin.val h; simp [xm0, xm1] at this
theorem xm02 : xm0 H i j ≠ xm2 H i j := fun h => by have := congrArg Fin.val h; simp [xm0, xm2] at this
theorem xm12 : xm1 H i j ≠ xm2 H i j := fun h => by have := congrArg Fin.val h; simp [xm1, xm2] at this

end insends

variable {X : MGraph} {P : Fin X.m → Prop}

theorem ne_edge_uv {u v p q : Fin X.n} (huv : u ≠ v) {f g : Fin X.m} (jf : X.Joins f u p) (jg : X.Joins g v q)
    (hpv : p ≠ v) : f ≠ g := by
  intro h; subst h
  rcases joins_unique jf jg with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact huv h1
  · exact hpv h2

theorem ne_edge_e {u v p : Fin X.n} (huv : u ≠ v) {e f : Fin X.m} (je : X.Joins e u v) (jf : X.Joins f u p)
    (hpv : p ≠ v) : e ≠ f := by
  intro h; subst h
  rcases joins_unique je jf with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact hpv h2.symm
  · exact huv h2.symm

/-- **lifting through an edge insertion** -/
theorem insLift {H : MGraph} {u v x1 y1 x2 y2 : Fin X.n} {e g1 h1 g2 h2 : Fin X.m}
    (he : P e) (hg1 : P g1) (hh1 : P h1) (hg2 : P g2) (hh2 : P h2)
    (je : X.Joins e u v) (jg1 : X.Joins g1 u x1) (jh1 : X.Joins h1 u y1) (jg2 : X.Joins g2 v x2)
    (jh2 : X.Joins h2 v y2)
    (covu : ∀ d, P d → X.Inc d u → d = e ∨ d = g1 ∨ d = h1)
    (covv : ∀ d, P d → X.Inc d v → d = e ∨ d = g2 ∨ d = h2)
    (gh1 : g1 ≠ h1) (gh2 : g2 ≠ h2) (huv : u ≠ v)
    (x1u : x1 ≠ u) (x1v : x1 ≠ v) (y1u : y1 ≠ u) (y1v : y1 ≠ v)
    (x2u : x2 ≠ u) (x2v : x2 ≠ v) (y2u : y2 ≠ u) (y2v : y2 ≠ v)
    (α' : Fin X.n → Fin H.n) (γ : Fin X.m → Fin H.m) (i j : Fin H.m) (hij : i ≠ j)
    (ha : ∀ x y, meets P x → meets P y → x ≠ u → x ≠ v → y ≠ u → y ≠ v → α' x = α' y → x = y)
    (hb : ∀ f g, P f → P g → ¬ X.Inc f u → ¬ X.Inc f v → ¬ X.Inc g u → ¬ X.Inc g v → γ f = γ g → f = g)
    (hbi : ∀ f, P f → ¬ X.Inc f u → ¬ X.Inc f v → γ f ≠ i ∧ γ f ≠ j)
    (hs : ∀ k, k ≠ i → k ≠ j → ∃ f, P f ∧ ¬ X.Inc f u ∧ ¬ X.Inc f v ∧ γ f = k)
    (hj : ∀ f, P f → ¬ X.Inc f u → ¬ X.Inc f v → H.Joins (γ f) (α' (X.ends f).1) (α' (X.ends f).2))
    (hi : H.ends i = (α' x1, α' y1)) (hjj : H.ends j = (α' x2, α' y2)) :
    IsoFrom P (insG H i j) := by
  -- distinctness of the five special edges
  have eg1 : e ≠ g1 := ne_edge_e huv je jg1 x1v
  have eh1 : e ≠ h1 := ne_edge_e huv je jh1 y1v
  have eg2 : e ≠ g2 := ne_edge_e (Ne.symm huv) (Or.symm je) jg2 x2u
  have eh2 : e ≠ h2 := ne_edge_e (Ne.symm huv) (Or.symm je) jh2 y2u
  have g1g2 : g1 ≠ g2 := ne_edge_uv huv jg1 jg2 x1v
  have g1h2 : g1 ≠ h2 := ne_edge_uv huv jg1 jh2 x1v
  have h1g2 : h1 ≠ g2 := ne_edge_uv huv jh1 jg2 y1v
  have h1h2 : h1 ≠ h2 := ne_edge_uv huv jh1 jh2 y1v
  have away : ∀ f, P f → f ≠ e → f ≠ g1 → f ≠ h1 → f ≠ g2 → f ≠ h2 → ¬ X.Inc f u ∧ ¬ X.Inc f v := by
    intro f hf n0 n1 n2 n3 n4
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases covu f hf h with h' | h' | h'
      · exact n0 h'
      · exact n1 h'
      · exact n2 h'
    · rcases covv f hf h with h' | h' | h'
      · exact n0 h'
      · exact n3 h'
      · exact n4 h'
  let α : Fin X.n → Fin (insG H i j).n := fun w => if w = u then nv0 H else if w = v then nv1 H else ov H (α' w)
  let β : Fin X.m → Fin (insG H i j).m := fun f =>
    if f = e then xm2 H i j else if f = g1 then xe H i j i else if f = h1 then xm0 H i j
    else if f = g2 then xe H i j j else if f = h2 then xm1 H i j else xe H i j (γ f)
  have αu : α u = nv0 H := by simp [α]
  have αv : α v = nv1 H := by simp [α, Ne.symm huv]
  have αo : ∀ w, w ≠ u → w ≠ v → α w = ov H (α' w) := fun w h1 h2 => by simp [α, h1, h2]
  have βe : β e = xm2 H i j := by simp [β]
  have βg1 : β g1 = xe H i j i := by simp [β, Ne.symm eg1]
  have βh1 : β h1 = xm0 H i j := by simp [β, Ne.symm eh1, Ne.symm gh1]
  have βg2 : β g2 = xe H i j j := by simp [β, Ne.symm eg2, Ne.symm g1g2, Ne.symm h1g2]
  have βh2 : β h2 = xm1 H i j := by simp [β, Ne.symm eh2, Ne.symm g1h2, Ne.symm h1h2, Ne.symm gh2]
  have βo : ∀ f, f ≠ e → f ≠ g1 → f ≠ h1 → f ≠ g2 → f ≠ h2 → β f = xe H i j (γ f) :=
    fun f n0 n1 n2 n3 n4 => by simp [β, n0, n1, n2, n3, n4]
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · -- injectivity of `α` on the vertices of `P`
    intro a b ha' hb' hab
    by_cases hau : a = u
    · by_cases hbu : b = u
      · rw [hau, hbu]
      · by_cases hbv : b = v
        · rw [hau, αu, hbv, αv] at hab; exact absurd hab (nv01 H)
        · rw [hau, αu, αo b hbu hbv] at hab; exact absurd hab.symm (ov_ne0 H _)
    · by_cases hav : a = v
      · by_cases hbu : b = u
        · rw [hav, αv, hbu, αu] at hab; exact absurd hab.symm (nv01 H)
        · by_cases hbv : b = v
          · rw [hav, hbv]
          · rw [hav, αv, αo b hbu hbv] at hab; exact absurd hab.symm (ov_ne1 H _)
      · by_cases hbu : b = u
        · rw [αo a hau hav, hbu, αu] at hab; exact absurd hab (ov_ne0 H _)
        · by_cases hbv : b = v
          · rw [αo a hau hav, hbv, αv] at hab; exact absurd hab (ov_ne1 H _)
          · rw [αo a hau hav, αo b hbu hbv] at hab
            exact ha a b ha' hb' hau hav hbu hbv (ov_inj H hab)
  · -- injectivity of `β` on `P`
    have img : ∀ f, P f → (f = e ∧ β f = xm2 H i j) ∨ (f = g1 ∧ β f = xe H i j i) ∨ (f = h1 ∧ β f = xm0 H i j) ∨
        (f = g2 ∧ β f = xe H i j j) ∨ (f = h2 ∧ β f = xm1 H i j) ∨
        (¬ X.Inc f u ∧ ¬ X.Inc f v ∧ β f = xe H i j (γ f)) := by
      intro f hf
      by_cases n0 : f = e
      · exact Or.inl ⟨n0, n0 ▸ βe⟩
      by_cases n1 : f = g1
      · exact Or.inr (Or.inl ⟨n1, n1 ▸ βg1⟩)
      by_cases n2 : f = h1
      · exact Or.inr (Or.inr (Or.inl ⟨n2, n2 ▸ βh1⟩))
      by_cases n3 : f = g2
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n3, n3 ▸ βg2⟩)))
      by_cases n4 : f = h2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n4, n4 ▸ βh2⟩))))
      obtain ⟨a1, a2⟩ := away f hf n0 n1 n2 n3 n4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, βo f n0 n1 n2 n3 n4⟩))))
    intro f g hf hg hfg
    rcases img f hf with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨fu, fv, e1⟩ <;>
    rcases img g hg with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨gu, gv, e2⟩ <;>
    first
    | rfl
    | (rw [e1, e2] at hfg; first
    | exact absurd hfg (xe_ne_m0 H i j _) | exact absurd hfg (xe_ne_m1 H i j _) | exact absurd hfg (xe_ne_m2 H i j _)
    | exact absurd hfg.symm (xe_ne_m0 H i j _) | exact absurd hfg.symm (xe_ne_m1 H i j _)
    | exact absurd hfg.symm (xe_ne_m2 H i j _)
    | exact absurd hfg (xm01 H i j) | exact absurd hfg (xm02 H i j) | exact absurd hfg (xm12 H i j)
    | exact absurd hfg.symm (xm01 H i j) | exact absurd hfg.symm (xm02 H i j) | exact absurd hfg.symm (xm12 H i j)
    | exact absurd (xe_inj H i j hfg) hij | exact absurd (xe_inj H i j hfg).symm hij
    | exact absurd (xe_inj H i j hfg).symm (hbi _ hg gu gv).1 | exact absurd (xe_inj H i j hfg) (hbi _ hf fu fv).1
    | exact absurd (xe_inj H i j hfg).symm (hbi _ hg gu gv).2 | exact absurd (xe_inj H i j hfg) (hbi _ hf fu fv).2
    | exact hb f g hf hg fu fv gu gv (xe_inj H i j hfg))
  · -- surjectivity
    intro k
    rcases ins_edge_cases H i j k with ⟨k', rfl⟩ | rfl | rfl | rfl
    · by_cases hki : k' = i
      · subst hki; exact ⟨g1, hg1, βg1⟩
      · by_cases hkj : k' = j
        · subst hkj; exact ⟨g2, hg2, βg2⟩
        · obtain ⟨f, hf, fu, fv, rfl⟩ := hs k' hki hkj
          have n0 : f ≠ e := fun h => fu (h ▸ joins_inc_left je)
          have n1 : f ≠ g1 := fun h => fu (h ▸ joins_inc_left jg1)
          have n2 : f ≠ h1 := fun h => fu (h ▸ joins_inc_left jh1)
          have n3 : f ≠ g2 := fun h => fv (h ▸ joins_inc_left jg2)
          have n4 : f ≠ h2 := fun h => fv (h ▸ joins_inc_left jh2)
          exact ⟨f, hf, βo f n0 n1 n2 n3 n4⟩
    · exact ⟨h1, hh1, βh1⟩
    · exact ⟨h2, hh2, βh2⟩
    · exact ⟨e, he, βe⟩
  · -- incidences
    intro f hf
    by_cases n0 : f = e
    · subst n0; rw [βe]; apply joins_ends_of je; rw [αu, αv]; exact Or.inl (insG_ends_m2 H i j)
    by_cases n1 : f = g1
    · subst n1; rw [βg1]; apply joins_ends_of jg1; rw [αu, αo x1 x1u x1v]
      exact Or.inr (by rw [insG_ends_i, hi])
    by_cases n2 : f = h1
    · subst n2; rw [βh1]; apply joins_ends_of jh1; rw [αu, αo y1 y1u y1v]
      exact Or.inl (by rw [insG_ends_m0, hi])
    by_cases n3 : f = g2
    · subst n3; rw [βg2]; apply joins_ends_of jg2; rw [αv, αo x2 x2u x2v]
      exact Or.inr (by rw [insG_ends_j H i j hij, hjj])
    by_cases n4 : f = h2
    · subst n4; rw [βh2]; apply joins_ends_of jh2; rw [αv, αo y2 y2u y2v]
      exact Or.inl (by rw [insG_ends_m1, hjj])
    obtain ⟨fu, fv⟩ := away f hf n0 n1 n2 n3 n4
    rw [βo f n0 n1 n2 n3 n4]
    have e1u : (X.ends f).1 ≠ u := fun h => fu (Or.inl h)
    have e1v : (X.ends f).1 ≠ v := fun h => fv (Or.inl h)
    have e2u : (X.ends f).2 ≠ u := fun h => fu (Or.inr h)
    have e2v : (X.ends f).2 ≠ v := fun h => fv (Or.inr h)
    rw [αo _ e1u e1v, αo _ e2u e2v]
    obtain ⟨hni, hnj⟩ := hbi f hf fu fv
    rcases hj f hf fu fv with h | h
    · exact Or.inl (by rw [insG_ends_old H i j hni hnj, h])
    · exact Or.inr (by rw [insG_ends_old H i j hni hnj, h])

namespace RedData
variable (R : RedData P)

/-- **lifting**: an isomorphism of the reduction onto `H` gives `P ≅ Ins(H, i, j)` for some `i ≠ j` -/
theorem lift {H : MGraph} (h : IsoFrom R.redP H) : ∃ i j, i ≠ j ∧ IsoFrom P (insG H i j) := by
  obtain ⟨α', β', hα, hβ, hs, hj⟩ := h
  let i := β' R.N1
  let j := β' R.N2
  have rN1 : R.redP R.N1 := Or.inr (Or.inl rfl)
  have rN2 : R.redP R.N2 := Or.inl rfl
  have hij : i ≠ j := fun h => R.N1_ne_N2 (hβ _ _ rN1 rN2 h)
  have mred : ∀ w, meets P w → w ≠ R.u → w ≠ R.v → @meets R.G2 R.redP w :=
    fun w hw h1 h2 => (R.meets_red w).2 ⟨hw, h1, h2⟩
  have pred : ∀ f, P f → ¬ X.Inc f R.u → ¬ X.Inc f R.v → R.redP (R.oE f) :=
    fun f hf h1 h2 => Or.inr (Or.inr ⟨f, rfl, hf, h1, h2⟩)
  have ha : ∀ a b, meets P a → meets P b → a ≠ R.u → a ≠ R.v → b ≠ R.u → b ≠ R.v → α' a = α' b → a = b :=
    fun a b ha' hb' h1 h2 h3 h4 h => hα a b (mred a ha' h1 h2) (mred b hb' h3 h4) h
  have hb : ∀ f g, P f → P g → ¬ X.Inc f R.u → ¬ X.Inc f R.v → ¬ X.Inc g R.u → ¬ X.Inc g R.v →
      β' (R.oE f) = β' (R.oE g) → f = g :=
    fun f g hf hg h1 h2 h3 h4 h => R.oE_inj (hβ _ _ (pred f hf h1 h2) (pred g hg h3 h4) h)
  have hbi : ∀ f, P f → ¬ X.Inc f R.u → ¬ X.Inc f R.v → β' (R.oE f) ≠ i ∧ β' (R.oE f) ≠ j :=
    fun f hf h1 h2 => ⟨fun h => R.oE_ne_N1 f (hβ _ _ (pred f hf h1 h2) rN1 h),
      fun h => R.oE_ne_N2 f (hβ _ _ (pred f hf h1 h2) rN2 h)⟩
  have hsur : ∀ k, k ≠ i → k ≠ j → ∃ f, P f ∧ ¬ X.Inc f R.u ∧ ¬ X.Inc f R.v ∧ β' (R.oE f) = k := by
    intro k hki hkj
    obtain ⟨r, hr, rfl⟩ := hs k
    rcases hr with rfl | rfl | ⟨f, rfl, hf, h1, h2⟩
    · exact absurd rfl hkj
    · exact absurd rfl hki
    · exact ⟨f, hf, h1, h2, rfl⟩
  have hjo : ∀ f, P f → ¬ X.Inc f R.u → ¬ X.Inc f R.v →
      H.Joins (β' (R.oE f)) (α' (X.ends f).1) (α' (X.ends f).2) := by
    intro f hf h1 h2
    have := hj _ (pred f hf h1 h2)
    rwa [R.ends_oE] at this
  have hji : H.Joins i (α' R.u1) (α' R.u2) := by
    have := hj _ rN1; rwa [R.ends_N1] at this
  have hjj : H.Joins j (α' R.v1) (α' R.v2) := by
    have := hj _ rN2; rwa [R.ends_N2] at this
  have covu' : ∀ d, P d → X.Inc d R.u → d = R.e ∨ d = R.a2 ∨ d = R.a1 := fun d hd hdu => by
    rcases R.covu d hd hdu with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have covv' : ∀ d, P d → X.Inc d R.v → d = R.e ∨ d = R.b2 ∨ d = R.b1 := fun d hd hdv => by
    rcases R.covv d hd hdv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  refine ⟨i, j, hij, ?_⟩
  rcases hji with hi | hi <;> rcases hjj with hj' | hj'
  · exact insLift R.he R.ha1 R.ha2 R.hb1 R.hb2 R.je R.ja1 R.ja2 R.jb1 R.jb2 R.covu R.covv R.a12 R.b12 R.huv
      R.u1u R.u1v R.u2u R.u2v R.v1u R.v1v R.v2u R.v2v α' (fun f => β' (R.oE f)) i j hij ha hb hbi hsur hjo hi hj'
  · exact insLift R.he R.ha1 R.ha2 R.hb2 R.hb1 R.je R.ja1 R.ja2 R.jb2 R.jb1 R.covu covv' R.a12 (Ne.symm R.b12) R.huv
      R.u1u R.u1v R.u2u R.u2v R.v2u R.v2v R.v1u R.v1v α' (fun f => β' (R.oE f)) i j hij ha hb hbi hsur hjo hi hj'
  · exact insLift R.he R.ha2 R.ha1 R.hb1 R.hb2 R.je R.ja2 R.ja1 R.jb1 R.jb2 covu' R.covv (Ne.symm R.a12) R.b12 R.huv
      R.u2u R.u2v R.u1u R.u1v R.v1u R.v1v R.v2u R.v2v α' (fun f => β' (R.oE f)) i j hij ha hb hbi hsur hjo hi hj'
  · exact insLift R.he R.ha2 R.ha1 R.hb2 R.hb1 R.je R.ja2 R.ja1 R.jb2 R.jb1 covu' covv' (Ne.symm R.a12)
      (Ne.symm R.b12) R.huv R.u2u R.u2v R.u1u R.u1v R.v2u R.v2v R.v1u R.v1v α' (fun f => β' (R.oE f)) i j hij
      ha hb hbi hsur hjo hi hj'

end RedData

end sc3

end RH2F

-- ===== from SC4.lean =====
/-
  SC4 — **Theorem R** (removable edges): every member of 𝒮 (simple 3-edge-connected cubic) with at least six vertices
  has an edge `e = u v` such that deleting `e` and suppressing `u` and `v` gives a member of 𝒮.
  The edge is a triangle edge if `P` has a triangle; otherwise an edge inside a minimal nontrivial 3-edge-cut side,
  or any edge if there is no nontrivial 3-edge-cut.
-/

namespace RH2F
open MGraph
open Classical

section sc4
variable {X : MGraph} {P : Fin X.m → Prop}

namespace RedData
variable (R : RedData P)

/-- the reduction data with the roles of `u` and `v` exchanged -/
def flip : RedData P where
  u := R.v
  v := R.u
  u1 := R.v1
  u2 := R.v2
  v1 := R.u1
  v2 := R.u2
  e := R.e
  a1 := R.b1
  a2 := R.b2
  b1 := R.a1
  b2 := R.a2
  he := R.he
  ha1 := R.hb1
  ha2 := R.hb2
  hb1 := R.ha1
  hb2 := R.ha2
  je := Or.symm R.je
  ja1 := R.jb1
  ja2 := R.jb2
  jb1 := R.ja1
  jb2 := R.ja2
  covu := R.covv
  covv := R.covu
  a12 := R.b12
  b12 := R.a12
  huv := Ne.symm R.huv
  u1u := R.v1v
  u1v := R.v1u
  u2u := R.v2v
  u2v := R.v2u
  v1u := R.u1v
  v1v := R.u1u
  v2u := R.u2v
  v2v := R.u2u
  u12 := R.v12
  v12 := R.u12

theorem hN2_of_common (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (h6 : 6 ≤ vcount P) {c : Fin X.n}
    (hcu : c = R.u1 ∨ c = R.u2) (hcv : c = R.v1 ∨ c = R.v2) : ∀ f, P f → R.Avoid f → ¬ X.Joins f R.v1 R.v2 :=
  fun f hf hav => R.flip.hN1_of_common hG h3 h6 hcv hcu f hf ⟨hav.2, hav.1⟩

/-- a neighbour of `u` other than `v` is `u1` or `u2` -/
theorem nbr_u {x : Fin X.n} {g : Fin X.m} (hg : P g) (jg : X.Joins g R.u x) (hxv : x ≠ R.v) :
    x = R.u1 ∨ x = R.u2 := by
  rcases R.covu g hg (joins_inc_left jg) with rfl | rfl | rfl
  · rcases joins_unique R.je jg with ⟨_, h⟩ | ⟨_, h⟩
    · exact absurd h.symm hxv
    · exact absurd h.symm R.huv
  · rcases joins_unique R.ja1 jg with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h.symm
    · exact absurd h R.u1u
  · rcases joins_unique R.ja2 jg with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h.symm
    · exact absurd h R.u2u

theorem nbr_v {x : Fin X.n} {g : Fin X.m} (hg : P g) (jg : X.Joins g R.v x) (hxu : x ≠ R.u) :
    x = R.v1 ∨ x = R.v2 :=
  R.flip.nbr_u hg jg hxu

/-- in a triangle-free `P` no edge avoiding `u, v` joins `u1, u2` -/
theorem hN1_of_trifree (htf : ∀ a b c f g h, P f → P g → P h → X.Joins f a b → X.Joins g b c → X.Joins h c a → False) :
    ∀ f, P f → R.Avoid f → ¬ X.Joins f R.u1 R.u2 :=
  fun _ hf _ jf => htf _ _ _ _ _ _ R.ha1 hf R.ha2 R.ja1 jf (Or.symm R.ja2)

theorem hN2_of_trifree (htf : ∀ a b c f g h, P f → P g → P h → X.Joins f a b → X.Joins g b c → X.Joins h c a → False) :
    ∀ f, P f → R.Avoid f → ¬ X.Joins f R.v1 R.v2 :=
  fun f hf hav => R.flip.hN1_of_trifree htf f hf ⟨hav.2, hav.1⟩

end RedData

/-- the ends of an edge given by `Joins` agree with the reduction data up to order -/
theorem red_ends (R : RedData P) {e : Fin X.m} (hRe : R.e = e) {a b : Fin X.n} (j : X.Joins e a b) :
    (R.u = a ∧ R.v = b) ∨ (R.u = b ∧ R.v = a) := by
  subst hRe; exact joins_unique R.je j

/-! ### minimal sides exist -/

theorem exists_minSide : ∀ (N : Nat) (B : Fin X.n → Bool), scount P B true ≤ N → xc P B = 3 →
    2 ≤ scount P B true → 2 ≤ scount P B false → ∃ A, MinSide P A
  | 0, _, hN, _, h1, _ => by omega
  | N + 1, B, hN, h3, h1, h0 => by
    by_cases hmin : ∀ B', xc P B' = 3 → 2 ≤ scount P B' true → 2 ≤ scount P B' false →
        scount P B true ≤ scount P B' true
    · exact ⟨B, h3, h1, h0, hmin⟩
    · push_neg at hmin
      obtain ⟨B', h3', h1', h0', hlt⟩ := hmin
      exact exists_minSide N B' (by omega) h3' h1' h0'

/-! ### the triangle side -/

/-- the side `{a, b, c}` of a triangle is a minimal nontrivial 3-edge-cut side -/
theorem tri_minSide (hG : InG X P) (hS : SimpleP P) (h6 : 6 ≤ vcount P) {a b c : Fin X.n} {f g h : Fin X.m}
    (hf : P f) (hg : P g) (hh : P h) (jf : X.Joins f a b) (jg : X.Joins g b c) (jh : X.Joins h c a) :
    MinSide P (fun w => decide (w = a ∨ w = b ∨ w = c)) := by
  have hab : a ≠ b := MGraph.ne_of_joins hG.1 jf
  have hbc : b ≠ c := MGraph.ne_of_joins hG.1 jg
  have hca : c ≠ a := MGraph.ne_of_joins hG.1 jh
  have fg : f ≠ g := by
    intro e; subst e
    rcases joins_unique jf jg with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hca h1.symm
  have fh : f ≠ h := by
    intro e; subst e
    rcases joins_unique jf jh with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hca h1.symm
    · exact hbc h2
  have gh : g ≠ h := by
    intro e; subst e
    rcases joins_unique jg jh with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hbc h1
    · exact hab h1.symm
  let A : Fin X.n → Bool := fun w => decide (w = a ∨ w = b ∨ w = c)
  have hsc : scount P A true = 3 := by
    unfold scount
    rw [← cntF_triple X.n hab (Ne.symm hca) hbc]
    apply cntF_congr; intro w
    constructor
    · intro hw; simpa [A] using hw.2
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨f, hf, joins_inc_left jf⟩, by simp [A]⟩
      · exact ⟨⟨f, hf, joins_inc_right jf⟩, by simp [A]⟩
      · exact ⟨⟨g, hg, joins_inc_right jg⟩, by simp [A]⟩
  have hin : cntF X.m (inner P A true) = 3 := by
    rw [← cntF_triple X.m fg fh gh]
    apply cntF_congr; intro d
    constructor
    · rintro ⟨hd, h1, h2⟩
      simp only [A, decide_eq_true_eq] at h1 h2
      have jd : X.Joins d (X.ends d).1 (X.ends d).2 := Or.inl rfl
      have hne : (X.ends d).1 ≠ (X.ends d).2 := MGraph.ne_of_joins hG.1 jd
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] at jd hne
      · exact absurd rfl hne
      · exact Or.inl (hS d f a b hd hf jd jf)
      · exact Or.inr (Or.inr (hS d h a c hd hh jd (Or.symm jh)))
      · exact Or.inl (hS d f b a hd hf jd (Or.symm jf))
      · exact absurd rfl hne
      · exact Or.inr (Or.inl (hS d g b c hd hg jd jg))
      · exact Or.inr (Or.inr (hS d h c a hd hh jd jh))
      · exact Or.inr (Or.inl (hS d g c b hd hg jd (Or.symm jg)))
      · exact absurd rfl hne
    · have inn : ∀ d p q, P d → X.Joins d p q → (p = a ∨ p = b ∨ p = c) → (q = a ∨ q = b ∨ q = c) →
          inner P A true d := by
        intro d p q hd jd hp hq
        refine ⟨hd, ?_, ?_⟩ <;> rcases jd with e | e <;> rw [e] <;> simp [A, hp, hq]
      rintro (rfl | rfl | rfl)
      · exact inn _ _ _ hf jf (Or.inl rfl) (Or.inr (Or.inl rfl))
      · exact inn _ _ _ hg jg (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      · exact inn _ _ _ hh jh (Or.inr (Or.inr rfl)) (Or.inl rfl)
  have hhs := side_handshake hG.1 hG.2.2.2 A true
  have hxc : xc P A = 3 := by unfold xc; omega
  have hsp := vcount_split P A
  show MinSide P A
  refine ⟨hxc, by omega, by omega, fun B hB3 hB1 _ => ?_⟩
  have hhB := side_handshake hG.1 hG.2.2.2 B true
  have : cntF X.m (RH2F.Crosses P B) = 3 := hB3
  omega

/-! ### Theorem R -/

theorem exists_edge (h6 : 6 ≤ vcount P) : ∃ e, P e := by
  unfold vcount at h6
  obtain ⟨w, f, hf, _⟩ := cntF_pos X.n (meets P) (by omega)
  exact ⟨f, hf⟩

/-- **Theorem R** (removable edges) -/
theorem removable (hS : InS X P) (h6 : 6 ≤ vcount P) : ∃ R : RedData P, InS R.G2 R.redP := by
  obtain ⟨hG, hSimp, h3⟩ := hS
  by_cases htri : ∃ a b c f g h, P f ∧ P g ∧ P h ∧ X.Joins f a b ∧ X.Joins g b c ∧ X.Joins h c a
  · obtain ⟨a, b, c, f, g, h, hf, hg, hh, jf, jg, jh⟩ := htri
    have hA := tri_minSide hG hSimp h6 hf hg hh jf jg jh
    obtain ⟨R, hRe⟩ := redData_of hG hSimp hf
    have hab : a ≠ b := MGraph.ne_of_joins hG.1 jf
    have hbc : b ≠ c := MGraph.ne_of_joins hG.1 jg
    have hca : c ≠ a := MGraph.ne_of_joins hG.1 jh
    have mu : meets P R.u := ⟨R.e, R.he, joins_inc_left R.je⟩
    have mv : meets P R.v := ⟨R.e, R.he, joins_inc_right R.je⟩
    -- `c` is a common neighbour of `u` and `v`
    have hcom : (c = R.u1 ∨ c = R.u2) ∧ (c = R.v1 ∨ c = R.v2) := by
      rcases red_ends R hRe jf with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact ⟨R.nbr_u hh (by rw [hu]; exact Or.symm jh) (by rw [hv]; exact Ne.symm hbc),
          R.nbr_v hg (by rw [hv]; exact jg) (by rw [hu]; exact hca)⟩
      · exact ⟨R.nbr_u hg (by rw [hu]; exact jg) (by rw [hv]; exact hca),
          R.nbr_v hh (by rw [hv]; exact Or.symm jh) (by rw [hu]; exact Ne.symm hbc)⟩
    have hAuv : (decide (R.u = a ∨ R.u = b ∨ R.u = c)) = true ∧ (decide (R.v = a ∨ R.v = b ∨ R.v = c)) = true := by
      rcases red_ends R hRe jf with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> simp [hu, hv]
    have hnb : R.NoBad := fun T hT hTu hTv hT1 hT0 =>
      uncross hG h3 hA mu mv hAuv.1 hAuv.2 hT hTu hTv hT1 hT0
    exact ⟨R, R.inS_red hG hSimp h3 hnb (R.hN1_of_common hG h3 h6 hcom.1 hcom.2)
      (R.hN2_of_common hG h3 h6 hcom.1 hcom.2) (R.h12_of hG h3 h6)⟩
  · have htf : ∀ a b c f g h, P f → P g → P h → X.Joins f a b → X.Joins g b c → X.Joins h c a → False :=
      fun a b c f g h hf hg hh jf jg jh => htri ⟨a, b, c, f, g, h, hf, hg, hh, jf, jg, jh⟩
    by_cases hnt : ∃ B, xc P B = 3 ∧ 2 ≤ scount P B true ∧ 2 ≤ scount P B false
    · obtain ⟨B, hB3, hB1, hB0⟩ := hnt
      obtain ⟨A, hA⟩ := exists_minSide _ B (le_refl _) hB3 hB1 hB0
      -- an edge inside `A`
      have hhs := side_handshake hG.1 hG.2.2.2 A true
      have hx : cntF X.m (RH2F.Crosses P A) = 3 := hA.1
      have h2 := hA.2.1
      obtain ⟨e, he, heA1, heA2⟩ := cntF_pos X.m (inner P A true) (by omega)
      obtain ⟨R, hRe⟩ := redData_of hG hSimp he
      have mu : meets P R.u := ⟨R.e, R.he, joins_inc_left R.je⟩
      have mv : meets P R.v := ⟨R.e, R.he, joins_inc_right R.je⟩
      have hAuv : A R.u = true ∧ A R.v = true := by
        rcases red_ends R hRe (Or.inl rfl : X.Joins e (X.ends e).1 (X.ends e).2) with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · rw [hu, hv]; exact ⟨heA1, heA2⟩
        · rw [hu, hv]; exact ⟨heA2, heA1⟩
      have hnb : R.NoBad := fun T hT hTu hTv hT1 hT0 =>
        uncross hG h3 hA mu mv hAuv.1 hAuv.2 hT hTu hTv hT1 hT0
      exact ⟨R, R.inS_red hG hSimp h3 hnb (R.hN1_of_trifree htf) (R.hN2_of_trifree htf) (R.h12_of hG h3 h6)⟩
    · obtain ⟨e, he⟩ := exists_edge h6
      obtain ⟨R, _⟩ := redData_of hG hSimp he
      have hnb : R.NoBad := fun T hT _ _ hT1 hT0 => hnt ⟨T, hT, hT1, hT0⟩
      exact ⟨R, R.inS_red hG hSimp h3 hnb (R.hN1_of_trifree htf) (R.hN2_of_trifree htf) (R.h12_of hG h3 h6)⟩

end sc4

end RH2F

-- ===== from SC5.lean =====
/-
  SC5 — insertion tables and the classification step.
  * `insL n el i j`: the edge list of `Ins(ofList n el, i, j)`; `ins_conc`: the identity isomorphism.
  * `isoC`: a kernel-efficient isomorphism check between two edge lists given by Nat codes (vertex map `S` with
    inverse `SI`, edge map `T` with inverse `TI`, as base-16 / base-32 digit strings); `isoC_sound`.
  * `tabC`, `tabRangeC`: Bool checks of insertion tables; `scl_step`: if every member of 𝒮 with `n` vertices is
    isomorphic to a listed graph and the tables are complete, the same holds at `n + 2` vertices.
-/

namespace RH2F
open MGraph
open Classical

section sc5

theorem gE_mem {n : Nat} {el : List (Nat × Nat)} (hel : elOK n el = true) {e : Nat} (he : e < el.length) :
    (gE el e).1 < n ∧ (gE el e).2 < n ∧ (gE el e).1 ≠ (gE el e).2 := by
  have hg : gE el e = el[e] := by simp [gE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]
  have hb := List.all_eq_true.1 hel _ (List.getElem_mem he)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  rw [hg]; exact ⟨hb.1.1, hb.1.2, hb.2⟩

/-! ### the edge list of an insertion (recursor form) -/

theorem gE_cons_zero (p : Nat × Nat) (l : List (Nat × Nat)) : gE (p :: l) 0 = p := rfl
theorem gE_cons_succ (p : Nat × Nat) (l : List (Nat × Nat)) (e : Nat) : gE (p :: l) (e + 1) = gE l e := by
  simp [gE]

/-- walk along the edge list from position `q`, moving the edge at position `i` to `N0 = n` and the edge at position
    `j` to `N1 = n + 1`, and append `T` -/
def insGo (n i j : Nat) (T : List (Nat × Nat)) (l : List (Nat × Nat)) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => T)
    (fun p _ ih q => cond (Nat.beq q i) (p.1, n) (cond (Nat.beq q j) (p.1, n + 1) p) :: ih (q + 1)) l

theorem insGo_length (n i j : Nat) (T : List (Nat × Nat)) :
    ∀ (l : List (Nat × Nat)) (q : Nat), (insGo n i j T l q).length = l.length + T.length
  | [], _ => by simp [insGo]
  | p :: l, q => by
    show (_ :: insGo n i j T l (q + 1)).length = (p :: l).length + T.length
    rw [List.length_cons, insGo_length n i j T l (q + 1), List.length_cons]; omega

theorem gE_insGo_lo (n i j : Nat) (T : List (Nat × Nat)) :
    ∀ (l : List (Nat × Nat)) (q e : Nat), e < l.length →
      gE (insGo n i j T l q) e = cond (Nat.beq (q + e) i) ((gE l e).1, n) (cond (Nat.beq (q + e) j) ((gE l e).1, n + 1) (gE l e))
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | p :: l, q, 0, _ => rfl
  | p :: l, q, e + 1, h => by
    show gE (_ :: insGo n i j T l (q + 1)) (e + 1) = _
    rw [gE_cons_succ, gE_insGo_lo n i j T l (q + 1) e (by simp at h; omega), gE_cons_succ]
    have : q + 1 + e = q + (e + 1) := by omega
    rw [this]

theorem gE_insGo_hi (n i j : Nat) (T : List (Nat × Nat)) :
    ∀ (l : List (Nat × Nat)) (q r : Nat), gE (insGo n i j T l q) (l.length + r) = T.getD r (0, 0)
  | [], _, r => by simp [insGo, gE]
  | p :: l, q, r => by
    show gE (_ :: insGo n i j T l (q + 1)) ((p :: l).length + r) = _
    have : (p :: l).length + r = (l.length + r) + 1 := by simp; omega
    rw [this, gE_cons_succ, gE_insGo_hi n i j T l (q + 1) r]

/-- the edge list of `Ins(ofList n el, i, j)` -/
def insL (n : Nat) (el : List (Nat × Nat)) (i j : Nat) : List (Nat × Nat) :=
  insGo n i j [(n, (gER el i).2), (n + 1, (gER el j).2), (n, n + 1)] el 0

theorem length_insL (n : Nat) (el : List (Nat × Nat)) (i j : Nat) : (insL n el i j).length = el.length + 3 := by
  unfold insL; rw [insGo_length]; rfl

theorem cond_beq {α : Type} (e i : Nat) (a b : α) : cond (Nat.beq e i) a b = if e = i then a else b := by
  by_cases h : e = i
  · subst h; rw [if_pos rfl, Nat.beq_refl]; rfl
  · rw [if_neg h]
    have : Nat.beq e i = false := by
      cases hb : Nat.beq e i
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [this]; rfl

theorem gE_insL_lo {n : Nat} {el : List (Nat × Nat)} {i j e : Nat} (he : e < el.length) :
    gE (insL n el i j) e = if e = i then ((gE el i).1, n) else if e = j then ((gE el j).1, n + 1) else gE el e := by
  unfold insL
  rw [gE_insGo_lo _ _ _ _ _ _ _ he, Nat.zero_add, cond_beq, cond_beq]
  by_cases h1 : e = i
  · subst h1; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : e = j
    · subst h2; simp
    · rw [if_neg h2, if_neg h2]

theorem gE_insL_hi {n : Nat} {el : List (Nat × Nat)} {i j : Nat} (r : Nat) :
    gE (insL n el i j) (el.length + r) = [(n, (gE el i).2), (n + 1, (gE el j).2), (n, n + 1)].getD r (0, 0) := by
  unfold insL
  rw [gE_insGo_hi]
  simp only [gER, getR_eq, gE]

theorem elOK_of_gE {N : Nat} {L : List (Nat × Nat)}
    (h : ∀ e, e < L.length → (gE L e).1 < N ∧ (gE L e).2 < N ∧ (gE L e).1 ≠ (gE L e).2) : elOK N L = true := by
  unfold elOK
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hx
  have hg : gE L e = L[e] := by simp [gE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]
  have := h e he
  rw [hg] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩

theorem elOK_insL {n : Nat} {el : List (Nat × Nat)} (hel : elOK n el = true) {i j : Nat} (hi : i < el.length)
    (hj : j < el.length) : elOK (n + 2) (insL n el i j) = true := by
  have hi' := gE_mem hel hi
  have hj' := gE_mem hel hj
  apply elOK_of_gE
  intro e he
  rw [length_insL] at he
  by_cases hlo : e < el.length
  · have hm := gE_mem hel hlo
    rw [gE_insL_lo hlo]
    split
    · refine ⟨by omega, by omega, by omega⟩
    · split
      · refine ⟨by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, hm.2.2⟩
  · obtain ⟨r, rfl⟩ : ∃ r, e = el.length + r := ⟨e - el.length, by omega⟩
    rw [gE_insL_hi]
    have hr : r < 3 := by omega
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp <;> omega

/-- **`Ins(ofList n el, i, j)` is the multigraph of the edge list `insL n el i j`** -/
theorem ins_conc {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    (i j : Fin (ofList n el hn).m) (hij : i ≠ j) (h2 : 0 < n + 2) :
    ConcIso (insG (ofList n el hn) i j) (ofList (n + 2) (insL n el i.val j.val) h2) := by
  have hL := elOK_insL hel i.isLt j.isLt
  have hlen := length_insL n el i.val j.val
  have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  refine ⟨fun a => ⟨a.val, a.isLt⟩,
    fun e => ⟨e.val, by show e.val < (insL n el i.val j.val).length; rw [hlen]; exact e.isLt⟩, ?_, ?_, ?_, ?_⟩
  · intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro k
    have hk := k.isLt
    change k.val < (insL n el i.val j.val).length at hk
    rw [hlen] at hk
    exact ⟨⟨k.val, hk⟩, rfl⟩
  · intro e
    left
    have ho := ofList_ends (hn := h2) hL ⟨e.val, by show e.val < (insL n el i.val j.val).length; rw [hlen]; exact e.isLt⟩
    have hH := fun (x : Fin (ofList n el hn).m) => ofList_ends (hn := hn) hel x
    apply Prod.ext <;> apply Fin.ext
    · rw [ho.1]
      rcases ins_edge_cases (ofList n el hn) i j e with ⟨e', rfl⟩ | rfl | rfl | rfl
      · have he' : e'.val < el.length := e'.isLt
        show (gE (insL n el i.val j.val) e'.val).1 = _
        rw [gE_insL_lo he']
        by_cases h1 : e' = i
        · subst h1
          rw [if_pos rfl, insG_ends_i]
          show _ = ((ofList n el hn).ends e').1.val
          rw [(hH e').1]
        · by_cases h2' : e' = j
          · subst h2'
            rw [if_neg (fun h => hij (Fin.ext h).symm), if_pos rfl, insG_ends_j _ _ _ hij]
            show _ = ((ofList n el hn).ends e').1.val
            rw [(hH e').1]
          · rw [if_neg (fun h => h1 (Fin.ext h)), if_neg (fun h => h2' (Fin.ext h)),
              insG_ends_old _ _ _ h1 h2']
            show _ = ((ofList n el hn).ends e').1.val
            rw [(hH e').1]
      · show (gE (insL n el i.val j.val) (el.length + 0)).1 = _
        rw [gE_insL_hi, insG_ends_m0]; rfl
      · show (gE (insL n el i.val j.val) (el.length + 1)).1 = _
        rw [gE_insL_hi, insG_ends_m1]; rfl
      · show (gE (insL n el i.val j.val) (el.length + 2)).1 = _
        rw [gE_insL_hi, insG_ends_m2]; rfl
    · rw [ho.2]
      rcases ins_edge_cases (ofList n el hn) i j e with ⟨e', rfl⟩ | rfl | rfl | rfl
      · have he' : e'.val < el.length := e'.isLt
        show (gE (insL n el i.val j.val) e'.val).2 = _
        rw [gE_insL_lo he']
        by_cases h1 : e' = i
        · subst h1
          rw [if_pos rfl, insG_ends_i]; rfl
        · by_cases h2' : e' = j
          · subst h2'
            rw [if_neg (fun h => hij (Fin.ext h).symm), if_pos rfl, insG_ends_j _ _ _ hij]; rfl
          · rw [if_neg (fun h => h1 (Fin.ext h)), if_neg (fun h => h2' (Fin.ext h)),
              insG_ends_old _ _ _ h1 h2']
            show _ = ((ofList n el hn).ends e').2.val
            rw [(hH e').2]
      · show (gE (insL n el i.val j.val) (el.length + 0)).2 = _
        rw [gE_insL_hi, insG_ends_m0]
        show _ = ((ofList n el hn).ends i).2.val
        rw [(hH i).2]; rfl
      · show (gE (insL n el i.val j.val) (el.length + 1)).2 = _
        rw [gE_insL_hi, insG_ends_m1]
        show _ = ((ofList n el hn).ends j).2.val
        rw [(hH j).2]; rfl
      · show (gE (insL n el i.val j.val) (el.length + 2)).2 = _
        rw [gE_insL_hi, insG_ends_m2]; rfl

theorem concIso_trans {H1 H2 H3 : MGraph} (h1 : ConcIso H1 H2) (h2 : ConcIso H2 H3) : ConcIso H1 H3 := by
  obtain ⟨σ1, τ1, hσ1, hτ1, hs1, hj1⟩ := h1
  obtain ⟨σ2, τ2, hσ2, hτ2, hs2, hj2⟩ := h2
  refine ⟨fun a => σ2 (σ1 a), fun e => τ2 (τ1 e), fun a b h => hσ1 _ _ (hσ2 _ _ h),
    fun e e' h => hτ1 _ _ (hτ2 _ _ h), fun k => ?_, fun e => joins_map hj2 (hj1 e)⟩
  obtain ⟨e2, rfl⟩ := hs2 k
  obtain ⟨e1, rfl⟩ := hs1 e2
  exact ⟨e1, rfl⟩

/-- **swap symmetry**: `Ins(ofList n el, i, j) ≅ Ins(ofList n el, j, i)` (exchange `N0 ↔ N1`) -/
theorem insL_swap {n : Nat} {el : List (Nat × Nat)} (hel : elOK n el = true) {i j : Nat} (hi : i < el.length)
    (hj : j < el.length) (hij : i ≠ j) (h2 : 0 < n + 2) :
    ConcIso (ofList (n + 2) (insL n el i j) h2) (ofList (n + 2) (insL n el j i) h2) := by
  have hL := elOK_insL hel hi hj
  have hL' := elOK_insL hel hj hi
  have hlen := length_insL n el i j
  have hlen' := length_insL n el j i
  have gi := gE_mem hel hi
  have gj := gE_mem hel hj
  let sv : Nat → Nat := fun x => if x = n then n + 1 else if x = n + 1 then n else x
  let se : Nat → Nat := fun e => if e = el.length then el.length + 1 else if e = el.length + 1 then el.length else e
  have svlt : ∀ x, x < n + 2 → sv x < n + 2 := by
    intro x hx; simp only [sv]; split <;> [omega; split <;> omega]
  have selt : ∀ e, e < el.length + 3 → se e < el.length + 3 := by
    intro e he; simp only [se]; split <;> [omega; split <;> omega]
  have svinv : ∀ x, sv (sv x) = x := by
    intro x; simp only [sv]; split <;> split <;> (try split) <;> omega
  have seinv : ∀ e, se (se e) = e := by
    intro e; simp only [se]; split <;> split <;> (try split) <;> omega
  have svlo : ∀ x, x < n → sv x = x := by intro x hx; simp only [sv]; split <;> [omega; split <;> omega]
  have tlt : ∀ e : Fin (ofList (n + 2) (insL n el i j) h2).m, se e.val < (ofList (n + 2) (insL n el j i) h2).m := by
    intro e
    have he := e.isLt
    change e.val < (insL n el i j).length at he
    change se e.val < (insL n el j i).length
    rw [hlen] at he; rw [hlen']
    exact selt _ he
  refine ⟨fun x => ⟨sv x.val, svlt x.val x.isLt⟩, fun e => ⟨se e.val, tlt e⟩, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have h' : sv a.val = sv b.val := congrArg Fin.val h
    have := congrArg sv h'
    rw [svinv, svinv] at this
    exact Fin.ext this
  · intro a b h
    have h' : se a.val = se b.val := congrArg Fin.val h
    have := congrArg se h'
    rw [seinv, seinv] at this
    exact Fin.ext this
  · intro k
    have hk := k.isLt
    change k.val < (insL n el j i).length at hk
    rw [hlen'] at hk
    refine ⟨⟨se k.val, by change se k.val < (insL n el i j).length; rw [hlen]; exact selt _ hk⟩, ?_⟩
    exact Fin.ext (seinv k.val)
  · intro e
    have he := e.isLt
    change e.val < (insL n el i j).length at he
    rw [hlen] at he
    have hse : se e.val < (insL n el j i).length := by rw [hlen']; exact selt _ he
    have ho := ofList_ends (hn := h2) hL e
    have ho' := ofList_ends (hn := h2) hL' ⟨se e.val, hse⟩
    by_cases hlo : e.val < el.length
    · have hsee : se e.val = e.val := by simp only [se]; split <;> [omega; split <;> omega]
      have hg := gE_insL_lo (n := n) (i := i) (j := j) hlo
      have hg' := gE_insL_lo (n := n) (i := j) (j := i) hlo
      have hm := gE_mem hel hlo
      left
      apply Prod.ext <;> apply Fin.ext
      · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).1.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).1.val
        rw [ho'.1, ho.1]; dsimp only; rw [hsee, hg, hg']
        split_ifs <;> (try dsimp only) <;> first
          | exact (svlo _ gi.1).symm | exact (svlo _ gj.1).symm | exact (svlo _ hm.1).symm | (exfalso; omega)
      · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).2.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).2.val
        rw [ho'.2, ho.2]; dsimp only; rw [hsee, hg, hg']
        split_ifs <;> (try dsimp only) <;> first
          | exact (svlo _ hm.2.1).symm | (exfalso; omega) | (simp [sv])
    · obtain ⟨r, hr⟩ : ∃ r, e.val = el.length + r := ⟨e.val - el.length, by omega⟩
      have hr3 : r < 3 := by omega
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
      · have hsee : se e.val = el.length + 1 := by simp only [se]; rw [if_pos (by omega)]
        left
        apply Prod.ext <;> apply Fin.ext
        · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).1.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).1.val
          rw [ho'.1, ho.1]; dsimp only; rw [hsee, hr, gE_insL_hi, gE_insL_hi]; simp [sv]
        · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).2.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).2.val
          rw [ho'.2, ho.2]; dsimp only; rw [hsee, hr, gE_insL_hi, gE_insL_hi]; simp [svlo _ gi.2.1]
      · have hsee : se e.val = el.length + 0 := by simp only [se]; rw [if_neg (by omega), if_pos (by omega)]; rfl
        left
        apply Prod.ext <;> apply Fin.ext
        · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).1.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).1.val
          rw [ho'.1, ho.1]; dsimp only; rw [hsee, hr, gE_insL_hi, gE_insL_hi]; simp [sv]
        · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).2.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).2.val
          rw [ho'.2, ho.2]; dsimp only; rw [hsee, hr, gE_insL_hi, gE_insL_hi]; simp [svlo _ gj.2.1]
      · have hsee : se e.val = el.length + 2 := by simp only [se]; rw [if_neg (by omega), if_neg (by omega)]; omega
        right
        apply Prod.ext <;> apply Fin.ext
        · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).1.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).2.val
          rw [ho'.1, ho.2]; dsimp only; rw [hsee, hr, gE_insL_hi, gE_insL_hi]; simp [sv]
        · show ((ofList (n + 2) (insL n el j i) h2).ends ⟨se e.val, hse⟩).2.val = sv ((ofList (n + 2) (insL n el i j) h2).ends e).1.val
          rw [ho'.2, ho.1]; dsimp only; rw [hsee, hr, gE_insL_hi, gE_insL_hi]; simp [sv]

/-! ### the Nat-coded isomorphism check -/

/-- digit `i` of `c` in base `B` -/
def dgt (c B i : Nat) : Nat := c / B ^ i % B

/-- the code of an edge list: edge `e = (a, b)` is the base-256 digit `a + 16 b` at position `e` -/
def encE (L : List (Nat × Nat)) : Nat := List.rec (motive := fun _ => Nat) 0 (fun p _ ih => (p.1 + 16 * p.2) + 256 * ih) L

theorem dgt_zero (x y B : Nat) (hx : x < B) : dgt (x + B * y) B 0 = x := by
  unfold dgt; rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem dgt_succ (x y B i : Nat) (hB : 0 < B) (hx : x < B) : dgt (x + B * y) B (i + 1) = dgt y B i := by
  unfold dgt
  rw [Nat.pow_succ, Nat.mul_comm (B ^ i) B, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
    Nat.div_eq_of_lt hx, Nat.zero_add]

/-- the digits of the code of an edge list with ends `< 16` -/
theorem dgt_encE : ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.1 < 16 ∧ p.2 < 16) → ∀ e, e < L.length →
    dgt (encE L) 256 e % 16 = (gE L e).1 ∧ dgt (encE L) 256 e / 16 = (gE L e).2
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | p :: L, hL, e, he => by
    have hp := hL p List.mem_cons_self
    have hx : p.1 + 16 * p.2 < 256 := by omega
    show dgt ((p.1 + 16 * p.2) + 256 * encE L) 256 e % 16 = _ ∧ dgt ((p.1 + 16 * p.2) + 256 * encE L) 256 e / 16 = _
    cases e with
    | zero =>
      rw [dgt_zero _ _ _ hx, gE_cons_zero]
      constructor <;> omega
    | succ e =>
      rw [dgt_succ _ _ _ _ (by decide) hx, gE_cons_succ]
      exact dgt_encE L (fun q hq => hL q (List.mem_cons_of_mem _ hq)) e (by simp at he; omega)

theorem small_of_elOK {N : Nat} {L : List (Nat × Nat)} (h : elOK N L = true) (hN : N ≤ 16) :
    ∀ p ∈ L, p.1 < 16 ∧ p.2 < 16 := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- vertex map `S` (inverse `SI`, base 16) and edge map `T` (inverse `TI`, base 32) form an isomorphism of the edge
    lists with codes `E` (`m` edges) and `E2` (`m2` edges) on `N` vertices -/
def isoC (N m m2 E E2 S SI T TI : Nat) : Bool :=
  rangeAll N (fun x => Nat.blt (dgt S 16 x) N && Nat.beq (dgt SI 16 (dgt S 16 x)) x) &&
  rangeAll m (fun e => Nat.blt (dgt T 32 e) m2 && Nat.beq (dgt TI 32 (dgt T 32 e)) e) &&
  rangeAll m2 (fun e => Nat.blt (dgt TI 32 e) m && Nat.beq (dgt T 32 (dgt TI 32 e)) e) &&
  rangeAll m (fun e =>
    (Nat.beq (dgt E2 256 (dgt T 32 e) % 16) (dgt S 16 (dgt E 256 e % 16)) &&
      Nat.beq (dgt E2 256 (dgt T 32 e) / 16) (dgt S 16 (dgt E 256 e / 16))) ||
    (Nat.beq (dgt E2 256 (dgt T 32 e) % 16) (dgt S 16 (dgt E 256 e / 16)) &&
      Nat.beq (dgt E2 256 (dgt T 32 e) / 16) (dgt S 16 (dgt E 256 e % 16))))

theorem isoC_sound {N : Nat} {L L2 : List (Nat × Nat)} {S SI T TI : Nat} {hN : 0 < N} (hN16 : N ≤ 16)
    (hL : elOK N L = true) (hL2 : elOK N L2 = true)
    (h : isoC N L.length L2.length (encE L) (encE L2) S SI T TI = true) :
    ConcIso (ofList N L hN) (ofList N L2 hN) := by
  unfold isoC at h
  simp only [Bool.and_eq_true, rangeAll_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hv, ht⟩, hti⟩, hj⟩ := h
  have dL := dgt_encE L (small_of_elOK hL hN16)
  have dL2 := dgt_encE L2 (small_of_elOK hL2 hN16)
  have hvlt : ∀ x, x < N → dgt S 16 x < N := fun x hx => Nat.le_of_ble_eq_true (hv x hx).1
  have htlt : ∀ e, e < L.length → dgt T 32 e < L2.length := fun e he => Nat.le_of_ble_eq_true (ht e he).1
  refine ⟨fun x => ⟨dgt S 16 x.val, hvlt x.val x.isLt⟩, fun e => ⟨dgt T 32 e.val, htlt e.val e.isLt⟩,
    ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have e1 := Nat.eq_of_beq_eq_true (hv a.val a.isLt).2
    have e2 := Nat.eq_of_beq_eq_true (hv b.val b.isLt).2
    have hab' : dgt S 16 a.val = dgt S 16 b.val := congrArg Fin.val hab
    rw [hab'] at e1
    exact Fin.ext (e1.symm.trans e2)
  · intro a b hab
    have e1 := Nat.eq_of_beq_eq_true (ht a.val a.isLt).2
    have e2 := Nat.eq_of_beq_eq_true (ht b.val b.isLt).2
    have hab' : dgt T 32 a.val = dgt T 32 b.val := congrArg Fin.val hab
    rw [hab'] at e1
    exact Fin.ext (e1.symm.trans e2)
  · intro k
    have hk : k.val < L2.length := k.isLt
    exact ⟨⟨dgt TI 32 k.val, Nat.le_of_ble_eq_true (hti k.val hk).1⟩,
      Fin.ext (Nat.eq_of_beq_eq_true (hti k.val hk).2)⟩
  · intro e
    have he : e.val < L.length := e.isLt
    have hte := htlt e.val he
    have hs := ofList_ends (hn := hN) hL e
    have ht2 := ofList_ends (hn := hN) hL2 ⟨dgt T 32 e.val, hte⟩
    have d1 := dL e.val he
    have d2 := dL2 _ hte
    rcases hj e.val he with h' | h'
    · left
      apply Prod.ext <;> apply Fin.ext
      · show ((ofList N L2 hN).ends ⟨dgt T 32 e.val, _⟩).1.val = dgt S 16 ((ofList N L hN).ends e).1.val
        rw [ht2.1, hs.1, ← d2.1, ← d1.1]; exact Nat.eq_of_beq_eq_true h'.1
      · show ((ofList N L2 hN).ends ⟨dgt T 32 e.val, _⟩).2.val = dgt S 16 ((ofList N L hN).ends e).2.val
        rw [ht2.2, hs.2, ← d2.2, ← d1.2]; exact Nat.eq_of_beq_eq_true h'.2
    · right
      apply Prod.ext <;> apply Fin.ext
      · show ((ofList N L2 hN).ends ⟨dgt T 32 e.val, _⟩).1.val = dgt S 16 ((ofList N L hN).ends e).2.val
        rw [ht2.1, hs.2, ← d2.1, ← d1.2]; exact Nat.eq_of_beq_eq_true h'.1
      · show ((ofList N L2 hN).ends ⟨dgt T 32 e.val, _⟩).2.val = dgt S 16 ((ofList N L hN).ends e).1.val
        rw [ht2.2, hs.1, ← d2.2, ← d1.1]; exact Nat.eq_of_beq_eq_true h'.2

/-! ### insertion tables -/

/-- walk along the rows of the table of host `el` (row at position `q` belongs to the pair `(q / m, q % m)`) -/
def walkC (n : Nat) (el : List (Nat × Nat)) (R2 : List (List (Nat × Nat))) (rows : List (Nat × Nat × Nat × Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun r _ ih q =>
    (Nat.ble (q % el.length) (q / el.length) ||
      (Nat.blt r.1 R2.length && isoC (n + 2) (el.length + 3) (getR R2 r.1 []).length
        (encE (insL n el (q / el.length) (q % el.length))) (encE (getR R2 r.1 [])) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2))
    && ih (q + 1)) rows

/-- the insertion table of host `el` -/
def tabC (n : Nat) (el : List (Nat × Nat)) (R2 : List (List (Nat × Nat))) (rows : List (Nat × Nat × Nat × Nat × Nat)) :
    Bool :=
  Nat.beq rows.length (el.length * el.length) && walkC n el R2 rows 0

theorem walkC_get (n : Nat) (el : List (Nat × Nat)) (R2 : List (List (Nat × Nat))) :
    ∀ (rows : List (Nat × Nat × Nat × Nat × Nat)) (q0 : Nat), walkC n el R2 rows q0 = true →
      ∀ r, r < rows.length → (Nat.ble ((q0 + r) % el.length) ((q0 + r) / el.length) ||
        (Nat.blt (rows.getD r (0, 0, 0, 0, 0)).1 R2.length && isoC (n + 2) (el.length + 3)
          (getR R2 (rows.getD r (0, 0, 0, 0, 0)).1 []).length
          (encE (insL n el ((q0 + r) / el.length) ((q0 + r) % el.length)))
          (encE (getR R2 (rows.getD r (0, 0, 0, 0, 0)).1 [])) (rows.getD r (0, 0, 0, 0, 0)).2.1
          (rows.getD r (0, 0, 0, 0, 0)).2.2.1 (rows.getD r (0, 0, 0, 0, 0)).2.2.2.1
          (rows.getD r (0, 0, 0, 0, 0)).2.2.2.2)) = true
  | [], _, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | x :: rows, q0, h, r, hr => by
    have h' : ((Nat.ble (q0 % el.length) (q0 / el.length) ||
      (Nat.blt x.1 R2.length && isoC (n + 2) (el.length + 3) (getR R2 x.1 []).length
        (encE (insL n el (q0 / el.length) (q0 % el.length))) (encE (getR R2 x.1 [])) x.2.1 x.2.2.1 x.2.2.2.1
        x.2.2.2.2)) && walkC n el R2 rows (q0 + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases r with
    | zero => simpa using h'.1
    | succ r =>
      have := walkC_get n el R2 rows (q0 + 1) h'.2 r (by simp at hr; omega)
      have e : q0 + 1 + r = q0 + (r + 1) := by omega
      rw [e] at this
      simpa using this

/-- all listed graphs are loopless edge lists on `N` vertices -/
def repsOK (N : Nat) (L : List (List (Nat × Nat))) : Bool := allR (fun el => elOK N el) L

theorem repsOK_get {N : Nat} {L : List (List (Nat × Nat))} (h : repsOK N L = true) {k : Nat} (hk : k < L.length) :
    elOK N (L.getD k []) = true := by
  unfold repsOK at h
  rw [allR_eq, List.all_eq_true] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact h _ (List.getElem_mem hk)

/-- the row of the pair `i < j` of a passed table -/
theorem tabC_row {n : Nat} {el : List (Nat × Nat)} {R2 : List (List (Nat × Nat))}
    {rows : List (Nat × Nat × Nat × Nat × Nat)} (h : tabC n el R2 rows = true)
    (hel : elOK n el = true) (hR2 : repsOK (n + 2) R2 = true) (h16 : n + 2 ≤ 16) (hn2 : 0 < n + 2)
    {i j : Nat} (hi : i < el.length) (hj : j < el.length) (hij : i < j) : ∃ k', k' < R2.length ∧
      ConcIso (ofList (n + 2) (insL n el i j) hn2) (ofList (n + 2) (R2.getD k' []) hn2) := by
  unfold tabC at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlen, hw⟩ := h
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hq : i * el.length + j < rows.length := by
    rw [hlen']
    have : i * el.length + j < (i + 1) * el.length := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hi)
  have h1 := walkC_get n el R2 rows 0 hw _ hq
  have hpos : 0 < el.length := by omega
  have hdiv : (0 + (i * el.length + j)) / el.length = i := by
    rw [Nat.zero_add, Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (0 + (i * el.length + j)) % el.length = j := by
    rw [Nat.zero_add, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod] at h1
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨hk, hiso⟩
  · exact absurd (Nat.le_of_ble_eq_true h1) (by omega)
  · have hk' := Nat.le_of_ble_eq_true hk
    refine ⟨_, hk', ?_⟩
    rw [getR_eq] at hiso
    have hL := elOK_insL hel hi hj
    have hL2 := repsOK_get hR2 hk'
    rw [← length_insL n el i j] at hiso
    exact isoC_sound h16 hL hL2 hiso

theorem tabC_sound {n : Nat} {el : List (Nat × Nat)} {R2 : List (List (Nat × Nat))}
    {rows : List (Nat × Nat × Nat × Nat × Nat)} (h : tabC n el R2 rows = true)
    (hel : elOK n el = true) (hR2 : repsOK (n + 2) R2 = true) (h16 : n + 2 ≤ 16) {hn : 0 < n} (hn2 : 0 < n + 2) :
    ∀ i j : Fin (ofList n el hn).m, i ≠ j → ∃ k', k' < R2.length ∧
      ConcIso (ofList (n + 2) (insL n el i.val j.val) hn2) (ofList (n + 2) (R2.getD k' []) hn2) := by
  intro i j hij
  have hi : i.val < el.length := i.isLt
  have hj : j.val < el.length := j.isLt
  have hne : i.val ≠ j.val := fun h' => hij (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact tabC_row h hel hR2 h16 hn2 hi hj hlt
  · obtain ⟨k', hk', hc⟩ := tabC_row h hel hR2 h16 hn2 hj hi hgt
    exact ⟨k', hk', concIso_trans (insL_swap hel hi hj hne hn2) hc⟩

/-- the tables of the hosts `k0, k0 + 1, …` (entry `r` of `TD` is the table of host `k0 + r`) -/
def tabRangeC (n : Nat) (L L2 : List (List (Nat × Nat))) (k0 : Nat)
    (TD : List (List (Nat × Nat × Nat × Nat × Nat))) : Bool :=
  rangeAll TD.length (fun r => tabC n (getR L (k0 + r) []) L2 (getR TD r []))

theorem tabRangeC_sound {n : Nat} {L L2 : List (List (Nat × Nat))} {k0 : Nat}
    {TD : List (List (Nat × Nat × Nat × Nat × Nat))} (h : tabRangeC n L L2 k0 TD = true)
    (hL : repsOK n L = true) (hL2 : repsOK (n + 2) L2 = true) (h16 : n + 2 ≤ 16) {hn : 0 < n} (hn2 : 0 < n + 2) :
    ∀ k, k0 ≤ k → k < k0 + TD.length → k < L.length → ∀ i j : Fin (ofList n (L.getD k []) hn).m, i ≠ j →
      ∃ k', k' < L2.length ∧
        ConcIso (ofList (n + 2) (insL n (L.getD k []) i.val j.val) hn2) (ofList (n + 2) (L2.getD k' []) hn2) := by
  intro k hk0 hk1 hkL
  unfold tabRangeC at h
  rw [rangeAll_eq, List.all_eq_true] at h
  have h1 := h (k - k0) (List.mem_range.2 (by omega))
  have e : k0 + (k - k0) = k := by omega
  rw [e, getR_eq, getR_eq] at h1
  exact tabC_sound h1 (repsOK_get hL hkL) hL2 h16 hn2

/-! ### the classification step -/

/-- **classification step**: a classification of 𝒮 at `n ≥ 4` vertices by the list `L` and complete insertion
    tables give the classification at `n + 2` vertices by the list `L2` -/
theorem scl_step {n : Nat} (hn4 : 4 ≤ n) {L L2 : List (List (Nat × Nat))} (hn : 0 < n) (hn2 : 0 < n + 2)
    (hL : repsOK n L = true)
    (ih : ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n →
      ∃ k, k < L.length ∧ IsoFrom P (ofList n (L.getD k []) hn))
    (htab : ∀ k, k < L.length → ∀ i j : Fin (ofList n (L.getD k []) hn).m, i ≠ j → ∃ k', k' < L2.length ∧
      ConcIso (ofList (n + 2) (insL n (L.getD k []) i.val j.val) hn2) (ofList (n + 2) (L2.getD k' []) hn2)) :
    ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n + 2 →
      ∃ k, k < L2.length ∧ IsoFrom P (ofList (n + 2) (L2.getD k []) hn2) := by
  intro X P hS hv
  obtain ⟨R, hR⟩ := removable hS (by omega)
  have hvr : vcount R.redP = n := by have := R.vcount_red; omega
  obtain ⟨k, hk, hiso⟩ := ih _ _ hR hvr
  obtain ⟨i, j, hij, hiso2⟩ := R.lift hiso
  obtain ⟨k', hk', hc⟩ := htab k hk i j hij
  exact ⟨k', hk', isoFrom_trans (isoFrom_trans hiso2 (ins_conc (repsOK_get hL hk) i j hij hn2)) hc⟩

end sc5

end RH2F

-- ===== from SC6.lean =====
/-
  SC6 — a kernel-cheap insertion-table check by adjacency bitsets, and the base case 𝒮_4 = {K4}.
  * `sv S x`: digit `x` of `S` in base 16 (the vertex map of a table row); `permB N S`: `x ↦ sv S x` is a
    permutation of `{0, …, N − 1}` (the OR of the bits `2 ^ sv S x` is `2 ^ N − 1`).
  * `adjF f L`: the adjacency bitset of the edge list `L` under the vertex map `f` (bits `16 f(a) + f(b)` and
    `16 f(b) + f(a)` of every edge `(a, b)`); `freshGo L 0`: no two edges of `L` join the same two vertices.
  * `concIso_of_adj`: equal bitsets, a vertex permutation, a simple target and equal edge counts give a `ConcIso`.
  * `tabA`: the table of one host, rows `(k', S)`; the target adjacency bitsets are packed into one number `AD`
    (256 bits per target) whose slices are checked once (`adGo`); `hostTab_of_tabA` gives the interface
    `HostTab` used by `scl_step`.
-/

namespace RH2F
open MGraph

section sc6

/-! ### digits, permutations, adjacency bitsets -/

/-- digit `x` of `S` in base 16 -/
def sv (S x : Nat) : Nat := (S >>> (4 * x)) &&& 15

theorem sv_lt (S x : Nat) : sv S x < 16 := by
  unfold sv; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- the adjacency bitset of the edge list `L` under the vertex map `f` -/
def adjF (f : Nat → Nat) (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => ih ||| 2 ^ (16 * f p.1 + f p.2) ||| 2 ^ (16 * f p.2 + f p.1)) L

theorem testBit_adjF (f : Nat → Nat) : ∀ (L : List (Nat × Nat)) (b : Nat),
    (adjF f L).testBit b = true ↔
      ∃ e, e < L.length ∧ (b = 16 * f (gE L e).1 + f (gE L e).2 ∨ b = 16 * f (gE L e).2 + f (gE L e).1)
  | [], b => by simp [adjF, Nat.zero_testBit]
  | p :: L, b => by
    show (adjF f L ||| 2 ^ (16 * f p.1 + f p.2) ||| 2 ^ (16 * f p.2 + f p.1)).testBit b = true ↔ _
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, Bool.or_eq_true,
      Bool.or_eq_true, testBit_adjF f L b]
    constructor
    · rintro ((⟨e, he, h⟩ | h) | h)
      · exact ⟨e + 1, by simp; omega, by rw [gE_cons_succ]; exact h⟩
      · exact ⟨0, by simp, Or.inl (by rw [gE_cons_zero]; exact (of_decide_eq_true h).symm)⟩
      · exact ⟨0, by simp, Or.inr (by rw [gE_cons_zero]; exact (of_decide_eq_true h).symm)⟩
    · rintro ⟨e, he, h⟩
      cases e with
      | zero =>
        rw [gE_cons_zero] at h
        rcases h with h | h
        · exact Or.inl (Or.inr (decide_eq_true h.symm))
        · exact Or.inr (decide_eq_true h.symm)
      | succ e =>
        rw [gE_cons_succ] at h
        exact Or.inl (Or.inl ⟨e, by simp at he; omega, h⟩)

/-- walk along `L`, refusing an edge whose code `16 a + b` is already set in `acc` -/
def freshGo (L : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih acc => !(acc.testBit (16 * p.1 + p.2)) &&
      ih (acc ||| 2 ^ (16 * p.1 + p.2) ||| 2 ^ (16 * p.2 + p.1))) L

theorem freshGo_sound : ∀ (L : List (Nat × Nat)) (acc : Nat), freshGo L acc = true →
    (∀ e, e < L.length → acc.testBit (16 * (gE L e).1 + (gE L e).2) = false) ∧
    (∀ e f, e < L.length → f < L.length → e < f →
      ¬ (gE L e = gE L f ∨ gE L e = ((gE L f).2, (gE L f).1)))
  | [], _, _ => ⟨fun e he => absurd he (Nat.not_lt_zero _), fun e _ he => absurd he (Nat.not_lt_zero _)⟩
  | p :: L, acc, h => by
    have h' : (!(acc.testBit (16 * p.1 + p.2)) &&
        freshGo L (acc ||| 2 ^ (16 * p.1 + p.2) ||| 2 ^ (16 * p.2 + p.1))) = true := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h'
    obtain ⟨h1, h2⟩ := h'
    obtain ⟨ih1, ih2⟩ := freshGo_sound L _ h2
    have hbit : ∀ e, e < L.length → acc.testBit (16 * (gE L e).1 + (gE L e).2) = false ∧
        16 * (gE L e).1 + (gE L e).2 ≠ 16 * p.1 + p.2 ∧ 16 * (gE L e).1 + (gE L e).2 ≠ 16 * p.2 + p.1 := by
      intro e he
      have := ih1 e he
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow] at this
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
      exact ⟨this.1.1, fun h => this.1.2 h.symm, fun h => this.2 h.symm⟩
    constructor
    · intro e he
      cases e with
      | zero => rw [gE_cons_zero]; exact h1
      | succ e => rw [gE_cons_succ]; exact (hbit e (by simp at he; omega)).1
    · intro e f he hf hef
      cases f with
      | zero => exact absurd hef (Nat.not_lt_zero _)
      | succ f =>
        have hf' : f < L.length := by simp at hf; omega
        cases e with
        | zero =>
          rw [gE_cons_zero, gE_cons_succ]
          obtain ⟨_, n1, n2⟩ := hbit f hf'
          rintro (h | h)
          · exact n1 (by rw [← h])
          · exact n2 (by rw [h])
        | succ e =>
          rw [gE_cons_succ, gE_cons_succ]
          exact ih2 e f (by simp at he; omega) hf' (by omega)

/-- the OR of the bits `2 ^ sv S x` over `x < N` -/
def orPerm (S : Nat) (N : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun x ih => ih ||| 2 ^ sv S x) N

/-- `x ↦ sv S x` permutes `{0, …, N − 1}` -/
def permB (N S : Nat) : Bool := Nat.beq (orPerm S N) (2 ^ N - 1)

theorem testBit_orPerm (S : Nat) : ∀ (N b : Nat), (orPerm S N).testBit b = true ↔ ∃ x, x < N ∧ sv S x = b
  | 0, b => by simp [orPerm, Nat.zero_testBit]
  | N + 1, b => by
    show (orPerm S N ||| 2 ^ sv S N).testBit b = true ↔ _
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, testBit_orPerm S N b, decide_eq_true_iff]
    constructor
    · rintro (⟨x, hx, h⟩ | h)
      · exact ⟨x, by omega, h⟩
      · exact ⟨N, by omega, h⟩
    · rintro ⟨x, hx, h⟩
      by_cases hxN : x = N
      · subst hxN; exact Or.inr h
      · exact Or.inl ⟨x, by omega, h⟩

theorem permB_sound {N S : Nat} (h : permB N S = true) :
    (∀ x, x < N → sv S x < N) ∧ (∀ b, b < N → ∃ x, x < N ∧ sv S x = b) := by
  have he : orPerm S N = 2 ^ N - 1 := Nat.eq_of_beq_eq_true h
  constructor
  · intro x hx
    have h1 : (orPerm S N).testBit (sv S x) = true := (testBit_orPerm S N _).2 ⟨x, hx, rfl⟩
    rw [he, Nat.testBit_two_pow_sub_one] at h1
    exact of_decide_eq_true h1
  · intro b hb
    apply (testBit_orPerm S N b).1
    rw [he, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hb

theorem gE_small {K : List (Nat × Nat)} (hK : ∀ p ∈ K, p.1 < 16 ∧ p.2 < 16) {e : Nat} (he : e < K.length) :
    (gE K e).1 < 16 ∧ (gE K e).2 < 16 := by
  have hg : gE K e = K[e] := by simp [gE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]
  rw [hg]; exact hK _ (List.getElem_mem he)

/-- **equal adjacency bitsets give an isomorphism**: a vertex permutation `sv S`, a simple target `L2`, equal edge
    counts and `adjF (sv S) L = adjF id L2` give `ofList N L ≅ ofList N L2` -/
theorem concIso_of_adj {N : Nat} {hN : 0 < N} (hN16 : N ≤ 16) {L L2 : List (Nat × Nat)} {S : Nat}
    (hL : elOK N L = true) (hL2 : elOK N L2 = true) (hfr : freshGo L2 0 = true) (hlen : L.length = L2.length)
    (hp : permB N S = true) (hA : adjF (sv S) L = adjF id L2) :
    ConcIso (ofList N L hN) (ofList N L2 hN) := by
  classical
  obtain ⟨hlt, hsurj⟩ := permB_sound hp
  have bL := small_of_elOK hL hN16
  have bL2 := small_of_elOK hL2 hN16
  have hsim := (freshGo_sound L2 0 hfr).2
  -- the images of the edges of `L`
  have himg : ∀ e, e < L.length → ∃ t, t < L2.length ∧
      (gE L2 t = (sv S (gE L e).1, sv S (gE L e).2) ∨ gE L2 t = (sv S (gE L e).2, sv S (gE L e).1)) := by
    intro e he
    have hb : (adjF (sv S) L).testBit (16 * sv S (gE L e).1 + sv S (gE L e).2) = true :=
      (testBit_adjF _ L _).2 ⟨e, he, Or.inl rfl⟩
    rw [hA] at hb
    obtain ⟨t, ht, h⟩ := (testBit_adjF id L2 _).1 hb
    have gt := gE_small bL2 ht
    have s1 := sv_lt S (gE L e).1
    have s2 := sv_lt S (gE L e).2
    simp only [id] at h
    refine ⟨t, ht, ?_⟩
    rcases h with h | h
    · left; apply Prod.ext <;> simp only <;> omega
    · right; apply Prod.ext <;> simp only <;> omega
  -- the targets are hit
  have hpre : ∀ t, t < L2.length → ∃ e, e < L.length ∧
      (gE L2 t = (sv S (gE L e).1, sv S (gE L e).2) ∨ gE L2 t = (sv S (gE L e).2, sv S (gE L e).1)) := by
    intro t ht
    have hb : (adjF id L2).testBit (16 * (gE L2 t).1 + (gE L2 t).2) = true :=
      (testBit_adjF id L2 _).2 ⟨t, ht, Or.inl rfl⟩
    rw [← hA] at hb
    obtain ⟨e, he, h⟩ := (testBit_adjF _ L _).1 hb
    have gt := gE_small bL2 ht
    have s1 := sv_lt S (gE L e).1
    have s2 := sv_lt S (gE L e).2
    refine ⟨e, he, ?_⟩
    rcases h with h | h
    · left; apply Prod.ext <;> simp only <;> omega
    · right; apply Prod.ext <;> simp only <;> omega
  -- uniqueness of a target edge with given ends
  have huniq : ∀ t t', t < L2.length → t' < L2.length →
      (gE L2 t = gE L2 t' ∨ gE L2 t = ((gE L2 t').2, (gE L2 t').1)) → t = t' := by
    intro t t' ht ht' h
    rcases Nat.lt_trichotomy t t' with h1 | h1 | h1
    · exact absurd h (hsim t t' ht ht' h1)
    · exact h1
    · exfalso
      apply hsim t' t ht' ht h1
      rcases h with h | h
      · exact Or.inl h.symm
      · right; rw [h]
  let σ : Fin N → Fin N := fun x => ⟨sv S x.val, hlt x.val x.isLt⟩
  have σsurj : Function.Surjective σ := fun b => by
    obtain ⟨x, hx, h⟩ := hsurj b.val b.isLt
    exact ⟨⟨x, hx⟩, Fin.ext h⟩
  have σinj : Function.Injective σ := Finite.injective_iff_surjective.2 σsurj
  let τ : Fin (ofList N L hN).m → Fin (ofList N L2 hN).m := fun e =>
    ⟨Classical.choose (himg e.val e.isLt), (Classical.choose_spec (himg e.val e.isLt)).1⟩
  have hτ : ∀ e : Fin (ofList N L hN).m, gE L2 (τ e).val = (sv S (gE L e.val).1, sv S (gE L e.val).2) ∨
      gE L2 (τ e).val = (sv S (gE L e.val).2, sv S (gE L e.val).1) :=
    fun e => (Classical.choose_spec (himg e.val e.isLt)).2
  have τsurj : Function.Surjective τ := by
    intro t
    have ht : t.val < L2.length := t.isLt
    obtain ⟨e, he, h⟩ := hpre t.val ht
    refine ⟨⟨e, he⟩, Fin.ext ?_⟩
    apply huniq _ _ (τ ⟨e, he⟩).isLt ht
    rcases hτ ⟨e, he⟩ with h1 | h1 <;> rcases h with h2 | h2
    · left; rw [h1, h2]
    · right; rw [h1, h2]
    · right; rw [h1, h2]
    · left; rw [h1, h2]
  have τinj : Function.Injective τ := by
    have hb := (Fintype.bijective_iff_surjective_and_card τ).2 ⟨τsurj, by
      simp only [Fintype.card_fin]; exact hlen⟩
    exact hb.1
  refine ⟨σ, τ, fun a b h => σinj h, fun e e' h => τinj h, fun j => τsurj j, fun e => ?_⟩
  have hs := ofList_ends (hn := hN) hL e
  have ht := ofList_ends (hn := hN) hL2 (τ e)
  rcases hτ e with h | h
  · left
    apply Prod.ext <;> apply Fin.ext
    · rw [ht.1, h]; show sv S (gE L e.val).1 = sv S ((ofList N L hN).ends e).1.val; rw [hs.1]
    · rw [ht.2, h]; show sv S (gE L e.val).2 = sv S ((ofList N L hN).ends e).2.val; rw [hs.2]
  · right
    apply Prod.ext <;> apply Fin.ext
    · rw [ht.1, h]; show sv S (gE L e.val).2 = sv S ((ofList N L hN).ends e).2.val; rw [hs.2]
    · rw [ht.2, h]; show sv S (gE L e.val).1 = sv S ((ofList N L hN).ends e).1.val; rw [hs.1]

/-! ### the fused adjacency bitset of an insertion -/

/-- the pair at position `q` of `insGo n i j T l` -/
def insP (n i j q : Nat) (p : Nat × Nat) : Nat × Nat := cond (Nat.beq q i) (p.1, n) (cond (Nat.beq q j) (p.1, n + 1) p)

/-- `adjF (sv S) (insGo n i j T l q)`, computed without building the list -/
def mapGo (S n i j : Nat) (T : List (Nat × Nat)) (l : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => adjF (sv S) T)
    (fun p _ ih q => ih (q + 1) ||| 2 ^ (16 * sv S (insP n i j q p).1 + sv S (insP n i j q p).2) |||
      2 ^ (16 * sv S (insP n i j q p).2 + sv S (insP n i j q p).1)) l

theorem mapGo_eq (S n i j : Nat) (T : List (Nat × Nat)) :
    ∀ (l : List (Nat × Nat)) (q : Nat), mapGo S n i j T l q = adjF (sv S) (insGo n i j T l q)
  | [], _ => rfl
  | p :: l, q => by
    show mapGo S n i j T l (q + 1) ||| _ ||| _ = adjF (sv S) (insP n i j q p :: insGo n i j T l (q + 1))
    rw [mapGo_eq S n i j T l (q + 1)]
    rfl

/-! ### target data -/

/-- every listed graph is a loopless simple edge list on `N` vertices with `m` edges -/
def repsB (N m : Nat) (L : List (List (Nat × Nat))) : Bool :=
  allR (fun el => elOK N el && Nat.beq el.length m && freshGo el 0) L

theorem repsB_get {N m : Nat} {L : List (List (Nat × Nat))} (h : repsB N m L = true) {k : Nat}
    (hk : k < L.length) : elOK N (L.getD k []) = true ∧ (L.getD k []).length = m ∧ freshGo (L.getD k []) 0 = true := by
  unfold repsB at h
  rw [allR_eq, List.all_eq_true] at h
  have hg : L.getD k [] = L[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have := h _ (List.getElem_mem hk)
  rw [← hg] at this
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, Nat.eq_of_beq_eq_true this.1.2, this.2⟩

theorem repsOK_of_repsB {N m : Nat} {L : List (List (Nat × Nat))} (h : repsB N m L = true) : repsOK N L = true := by
  unfold repsB at h; unfold repsOK
  rw [allR_eq, List.all_eq_true] at h
  rw [allR_eq, List.all_eq_true]
  intro el hel
  have := h el hel
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- the 256-bit slice `k` of the packed number `AD` -/
def slice (AD k : Nat) : Nat := (AD >>> (256 * k)) &&& (2 ^ 256 - 1)

/-- slice `k0 + r` of `AD` is the adjacency bitset of the `r`-th listed graph -/
def adGo (AD : Nat) (L : List (List (Nat × Nat))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun el _ ih k => Nat.beq (slice AD k) (adjF id el) && ih (k + 1)) L

theorem adGo_sound (AD : Nat) : ∀ (L : List (List (Nat × Nat))) (k0 : Nat), adGo AD L k0 = true →
    ∀ k, k < L.length → slice AD (k0 + k) = adjF id (L.getD k [])
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | el :: L, k0, h, k, hk => by
    have h' : (Nat.beq (slice AD k0) (adjF id el) && adGo AD L (k0 + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases k with
    | zero => exact Nat.eq_of_beq_eq_true h'.1
    | succ k =>
      have := adGo_sound AD L (k0 + 1) h'.2 k (by simp at hk; omega)
      rw [show k0 + (k + 1) = k0 + 1 + k by omega, this]
      simp

/-! ### the table of one host -/

/-- walk along the rows (row at position `q` belongs to the pair `(q / m, q % m)`, used only if `q / m < q % m`):
    row `(k', S)` says `Ins(el, i, j) ≅ L2[k']` via the vertex permutation `sv S` -/
def walkA (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) (rows : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun r _ ih q =>
    (Nat.ble (q % el.length) (q / el.length) ||
      (Nat.blt r.1 K2 && permB (n + 2) r.2 &&
        Nat.beq (mapGo r.2 n (q / el.length) (q % el.length)
          [(n, (gER el (q / el.length)).2), (n + 1, (gER el (q % el.length)).2), (n, n + 1)] el 0)
          (slice AD r.1)))
    && ih (q + 1)) rows

/-- the insertion table of host `el` -/
def tabA (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) (rows : List (Nat × Nat)) : Bool :=
  Nat.beq rows.length (el.length * el.length) && walkA n el K2 AD rows 0

theorem walkA_get (n : Nat) (el : List (Nat × Nat)) (K2 AD : Nat) :
    ∀ (rows : List (Nat × Nat)) (q0 : Nat), walkA n el K2 AD rows q0 = true → ∀ r, r < rows.length →
      (Nat.ble ((q0 + r) % el.length) ((q0 + r) / el.length) ||
        (Nat.blt (rows.getD r (0, 0)).1 K2 && permB (n + 2) (rows.getD r (0, 0)).2 &&
          Nat.beq (mapGo (rows.getD r (0, 0)).2 n ((q0 + r) / el.length) ((q0 + r) % el.length)
            [(n, (gER el ((q0 + r) / el.length)).2), (n + 1, (gER el ((q0 + r) % el.length)).2), (n, n + 1)] el 0)
            (slice AD (rows.getD r (0, 0)).1))) = true
  | [], _, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | row :: rows, q0, h, r, hr => by
    have h' : ((Nat.ble (q0 % el.length) (q0 / el.length) ||
        (Nat.blt row.1 K2 && permB (n + 2) row.2 &&
          Nat.beq (mapGo row.2 n (q0 / el.length) (q0 % el.length)
            [(n, (gER el (q0 / el.length)).2), (n + 1, (gER el (q0 % el.length)).2), (n, n + 1)] el 0)
            (slice AD row.1)))
        && walkA n el K2 AD rows (q0 + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases r with
    | zero => simpa using h'.1
    | succ r =>
      have := walkA_get n el K2 AD rows (q0 + 1) h'.2 r (by simp at hr; omega)
      rw [show q0 + 1 + r = q0 + (r + 1) by omega] at this
      simpa using this

/-- the row of the pair `i < j` of a passed table -/
theorem tabA_row {n : Nat} {el : List (Nat × Nat)} {L2 : List (List (Nat × Nat))} {K2 AD m2 : Nat}
    {rows : List (Nat × Nat)} (h : tabA n el K2 AD rows = true) (hel : elOK n el = true)
    (hL2 : repsB (n + 2) m2 L2 = true) (hm2 : el.length + 3 = m2) (hK2 : L2.length = K2)
    (hAD : adGo AD L2 0 = true) (h16 : n + 2 ≤ 16) (hn2 : 0 < n + 2)
    {i j : Nat} (hi : i < el.length) (hj : j < el.length) (hij : i < j) : ∃ k', k' < L2.length ∧
      ConcIso (ofList (n + 2) (insL n el i j) hn2) (ofList (n + 2) (L2.getD k' []) hn2) := by
  unfold tabA at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlen, hw⟩ := h
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hq : i * el.length + j < rows.length := by
    rw [hlen']
    have : i * el.length + j < (i + 1) * el.length := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hi)
  have h1 := walkA_get n el K2 AD rows 0 hw _ hq
  have hpos : 0 < el.length := by omega
  have hdiv : (0 + (i * el.length + j)) / el.length = i := by
    rw [Nat.zero_add, Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (0 + (i * el.length + j)) % el.length = j := by
    rw [Nat.zero_add, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod] at h1
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨⟨hk, hp⟩, hA⟩
  · exact absurd (Nat.le_of_ble_eq_true h1) (by omega)
  · have hk' : (rows.getD (i * el.length + j) (0, 0)).1 < L2.length := hK2 ▸ Nat.le_of_ble_eq_true hk
    refine ⟨_, hk', ?_⟩
    obtain ⟨hel2, hlen2, hfr2⟩ := repsB_get hL2 hk'
    have hA' := Nat.eq_of_beq_eq_true hA
    rw [mapGo_eq] at hA'
    have hs := adGo_sound AD L2 0 hAD _ hk'
    rw [Nat.zero_add] at hs
    rw [hs] at hA'
    have hins : insGo n i j [(n, (gER el i).2), (n + 1, (gER el j).2), (n, n + 1)] el 0 = insL n el i j := rfl
    rw [hins] at hA'
    exact concIso_of_adj h16 (elOK_insL hel hi hj) hel2 hfr2 (by rw [length_insL, hlen2, hm2]) hp hA'

/-- the property of host `k` of `L` delivered by its table -/
def HostTab (n : Nat) (L L2 : List (List (Nat × Nat))) (hn : 0 < n) (hn2 : 0 < n + 2) (k : Nat) : Prop :=
  ∀ i j : Fin (ofList n (L.getD k []) hn).m, i ≠ j → ∃ k', k' < L2.length ∧
    ConcIso (ofList (n + 2) (insL n (L.getD k []) i.val j.val) hn2) (ofList (n + 2) (L2.getD k' []) hn2)

theorem hostTab_of_tabA {n : Nat} {L L2 : List (List (Nat × Nat))} {K2 AD m2 : Nat} {k : Nat}
    {rows : List (Nat × Nat)} (h : tabA n (L.getD k []) K2 AD rows = true) (hel : elOK n (L.getD k []) = true)
    (hL2 : repsB (n + 2) m2 L2 = true) (hm2 : (L.getD k []).length + 3 = m2) (hK2 : L2.length = K2)
    (hAD : adGo AD L2 0 = true) (h16 : n + 2 ≤ 16) (hn : 0 < n) (hn2 : 0 < n + 2) : HostTab n L L2 hn hn2 k := by
  intro i j hij
  have hi : i.val < (L.getD k []).length := i.isLt
  have hj : j.val < (L.getD k []).length := j.isLt
  have hne : i.val ≠ j.val := fun h' => hij (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact tabA_row h hel hL2 hm2 hK2 hAD h16 hn2 hi hj hlt
  · obtain ⟨k', hk', hc⟩ := tabA_row h hel hL2 hm2 hK2 hAD h16 hn2 hj hi hgt
    exact ⟨k', hk', concIso_trans (insL_swap hel hi hj hne hn2) hc⟩

/-- the tables of the hosts `k0, k0 + 1, …` (entry `r` of `TD` is the table of host `k0 + r`) -/
def tabRangeA (n : Nat) (L : List (List (Nat × Nat))) (K2 AD : Nat) (k0 : Nat) (TD : List (List (Nat × Nat))) : Bool :=
  rangeAll TD.length (fun r => tabA n (getR L (k0 + r) []) K2 AD (getR TD r []))

theorem hostTab_of_range {n : Nat} {L L2 : List (List (Nat × Nat))} {K2 AD m m2 : Nat} {k0 : Nat}
    {TD : List (List (Nat × Nat))} (h : tabRangeA n L K2 AD k0 TD = true)
    (hL : repsB n m L = true) (hL2 : repsB (n + 2) m2 L2 = true) (hm2 : m + 3 = m2) (hK2 : L2.length = K2)
    (hAD : adGo AD L2 0 = true) (h16 : n + 2 ≤ 16) (hn : 0 < n) (hn2 : 0 < n + 2) :
    ∀ k, k0 ≤ k → k < k0 + TD.length → k < L.length → HostTab n L L2 hn hn2 k := by
  intro k hk0 hk1 hkL
  unfold tabRangeA at h
  rw [rangeAll_eq, List.all_eq_true] at h
  have h1 := h (k - k0) (List.mem_range.2 (by omega))
  have e : k0 + (k - k0) = k := by omega
  rw [e, getR_eq, getR_eq] at h1
  obtain ⟨hel, hlen, _⟩ := repsB_get hL hkL
  exact hostTab_of_tabA h1 hel hL2 (by rw [hlen, hm2]) hK2 hAD h16 hn hn2

/-- the classification step in the `HostTab` form -/
theorem scl_stepA {n : Nat} (hn4 : 4 ≤ n) {L L2 : List (List (Nat × Nat))} (hn : 0 < n) (hn2 : 0 < n + 2)
    (hL : repsOK n L = true)
    (ih : ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n →
      ∃ k, k < L.length ∧ IsoFrom P (ofList n (L.getD k []) hn))
    (htab : ∀ k, k < L.length → HostTab n L L2 hn hn2 k) :
    ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n + 2 →
      ∃ k, k < L2.length ∧ IsoFrom P (ofList (n + 2) (L2.getD k []) hn2) :=
  scl_step hn4 hn hn2 hL ih htab

/-! ### the base case: 𝒮_4 = {K4} -/

/-- an isomorphic image of a simple edge set is simple -/
theorem simple_of_isoFrom {X : MGraph} {P : Fin X.m → Prop} {H : MGraph} (hS : SimpleP P) (h : IsoFrom P H)
    (e f : Fin H.m) (x y : Fin H.n) (he : H.Joins e x y) (hf : H.Joins f x y) : e = f := by
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := h
  obtain ⟨f1, hP1, rfl⟩ := hs e
  obtain ⟨f2, hP2, rfl⟩ := hs f
  have m1 : meets P (X.ends f1).1 := ⟨f1, hP1, Or.inl rfl⟩
  have m1' : meets P (X.ends f1).2 := ⟨f1, hP1, Or.inr rfl⟩
  have m2 : meets P (X.ends f2).1 := ⟨f2, hP2, Or.inl rfl⟩
  have m2' : meets P (X.ends f2).2 := ⟨f2, hP2, Or.inr rfl⟩
  have j1 := hj f1 hP1
  have j2 := hj f2 hP2
  rcases joins_unique j1 he with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases joins_unique j2 hf with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · have e1 := hα _ _ m1 m2 (a1.trans a2.symm)
    have e2 := hα _ _ m1' m2' (b1.trans b2.symm)
    have : f1 = f2 := hS f1 f2 _ _ hP1 hP2 (Or.inl rfl) (Or.inl (Prod.ext e1.symm e2.symm))
    rw [this]
  · have e1 := hα _ _ m1 m2' (a1.trans b2.symm)
    have e2 := hα _ _ m1' m2 (b1.trans a2.symm)
    have : f1 = f2 := hS f1 f2 _ _ hP1 hP2 (Or.inl rfl) (Or.inr (Prod.ext e2.symm e1.symm))
    rw [this]
  · have e1 := hα _ _ m1 m2' (a1.trans b2.symm)
    have e2 := hα _ _ m1' m2 (b1.trans a2.symm)
    have : f1 = f2 := hS f1 f2 _ _ hP1 hP2 (Or.inl rfl) (Or.inr (Prod.ext e2.symm e1.symm))
    rw [this]
  · have e1 := hα _ _ m1 m2 (a1.trans a2.symm)
    have e2 := hα _ _ m1' m2' (b1.trans b2.symm)
    have : f1 = f2 := hS f1 f2 _ _ hP1 hP2 (Or.inl rfl) (Or.inl (Prod.ext e1.symm e2.symm))
    rw [this]

end sc6

end RH2F

namespace RH2F
open MGraph

/-- **Layer 29a**: (1) Theorem R (removable edge) for 𝒮; (2) the lifting of an isomorphism of the reduction to an
    insertion; (3) the classification step from verified insertion tables -/
theorem layer29a :
    (∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → 6 ≤ vcount P →
      ∃ R : RedData P, InS R.G2 R.redP ∧ vcount R.redP + 2 = vcount P) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (R : RedData P) (H : MGraph), IsoFrom R.redP H →
      ∃ i j, i ≠ j ∧ IsoFrom P (insG H i j)) ∧
    (∀ (n : Nat), 4 ≤ n → ∀ (L L2 : List (List (Nat × Nat))) (hn : 0 < n) (hn2 : 0 < n + 2), repsOK n L = true →
      (∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n →
        ∃ k, k < L.length ∧ IsoFrom P (ofList n (L.getD k []) hn)) →
      (∀ k, k < L.length → HostTab n L L2 hn hn2 k) →
      ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = n + 2 →
        ∃ k, k < L2.length ∧ IsoFrom P (ofList (n + 2) (L2.getD k []) hn2)) := by
  refine ⟨fun X P hS h6 => ?_, fun X P R H h => R.lift h, fun n hn4 L L2 hn hn2 hL ih htab =>
    scl_stepA hn4 hn hn2 hL ih htab⟩
  obtain ⟨R, hR⟩ := removable hS h6
  exact ⟨R, hR, R.vcount_red⟩

end RH2F
