-- Lean proof of fact 341b6e5e1be16205 (RH2F.layer4); added by fact_submit, do not edit
import MhFact_657e581f1145250f
import MhFact_974f7197c1be8069



-- ===== from RH2Count.lean =====
/-
  RH2Count.lean — counting vertices (Lean 4.20 core): `cntF n W` is the number of `i : Fin n` with `W i`,
  defined by recursion on `n`.  Parity: a set with a fixed-point-free involution has even size.
-/

namespace RH2F
open MGraph
open Classical

/-- the number of `i : Fin n` with `W i` -/
noncomputable def cntF : (n : Nat) → (Fin n → Prop) → Nat
  | 0, _ => 0
  | n + 1, W => cntF n (fun i => W (Fin.castSucc i)) + (if W (Fin.last n) then 1 else 0)

section cnt

theorem cntF_zero (W : Fin 0 → Prop) : cntF 0 W = 0 := rfl

theorem cntF_succ (n : Nat) (W : Fin (n + 1) → Prop) :
    cntF (n + 1) W = cntF n (fun i => W (Fin.castSucc i)) + (if W (Fin.last n) then 1 else 0) := by
  simp [cntF]

theorem cntF_congr : ∀ (n : Nat) (W W' : Fin n → Prop), (∀ i, W i ↔ W' i) → cntF n W = cntF n W'
  | 0, _, _, _ => rfl
  | n + 1, W, W', h => by
    rw [cntF_succ, cntF_succ, cntF_congr n _ _ (fun i => h _)]
    by_cases hw : W (Fin.last n)
    · rw [if_pos hw, if_pos ((h _).1 hw)]
    · rw [if_neg hw, if_neg (fun h' => hw ((h _).2 h'))]

theorem cntF_mono : ∀ (n : Nat) (W W' : Fin n → Prop), (∀ i, W i → W' i) → cntF n W ≤ cntF n W'
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, W, W', h => by
    rw [cntF_succ, cntF_succ]
    have := cntF_mono n (fun i => W (Fin.castSucc i)) (fun i => W' (Fin.castSucc i)) (fun i => h _)
    by_cases hw : W (Fin.last n)
    · rw [if_pos hw, if_pos (h _ hw)]; omega
    · rw [if_neg hw]
      by_cases hw' : W' (Fin.last n)
      · rw [if_pos hw']; omega
      · rw [if_neg hw']; omega

theorem cntF_split : ∀ (n : Nat) (W S : Fin n → Prop),
    cntF n W = cntF n (fun i => W i ∧ S i) + cntF n (fun i => W i ∧ ¬ S i)
  | 0, _, _ => rfl
  | n + 1, W, S => by
    rw [cntF_succ, cntF_succ, cntF_succ, cntF_split n _ (fun i => S (Fin.castSucc i))]
    by_cases hw : W (Fin.last n) <;> by_cases hs : S (Fin.last n)
    · rw [if_pos hw, if_pos ⟨hw, hs⟩, if_neg (fun h => h.2 hs)]; omega
    · rw [if_pos hw, if_neg (fun h => hs h.2), if_pos ⟨hw, hs⟩]; omega
    · rw [if_neg hw, if_neg (fun h => hw h.1), if_neg (fun h => hw h.1)]; omega
    · rw [if_neg hw, if_neg (fun h => hw h.1), if_neg (fun h => hw h.1)]; omega

theorem cntF_eq_zero : ∀ (n : Nat) (W : Fin n → Prop), (∀ i, ¬ W i) → cntF n W = 0
  | 0, _, _ => rfl
  | n + 1, W, h => by
    rw [cntF_succ, cntF_eq_zero n _ (fun i => h _), if_neg (h _)]

theorem cntF_pos : ∀ (n : Nat) (W : Fin n → Prop), 0 < cntF n W → ∃ i, W i
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, W, h => by
    rw [cntF_succ] at h
    by_cases hw : W (Fin.last n)
    · exact ⟨_, hw⟩
    · rw [if_neg hw] at h
      obtain ⟨i, hi⟩ := cntF_pos n (fun i => W (Fin.castSucc i)) (by omega)
      exact ⟨_, hi⟩

/-- the count of a single element is 1 -/
theorem cntF_single : ∀ (n : Nat) (j : Fin n), cntF n (fun k => k = j) = 1
  | 0, j => j.elim0
  | n + 1, j => by
    rw [cntF_succ]
    by_cases hj : Fin.last n = j
    · rw [if_pos hj]
      have : cntF n (fun i => Fin.castSucc i = j) = 0 :=
        cntF_eq_zero n _ (fun i h => castSucc_ne_last i (h.trans hj.symm))
      omega
    · rw [if_neg hj]
      have : ∃ j' : Fin n, Fin.castSucc j' = j := by
        refine ⟨⟨j.val, ?_⟩, Fin.ext rfl⟩
        have := j.isLt
        have hne : j.val ≠ n := fun h' => hj (Fin.ext h'.symm)
        omega
      obtain ⟨j', rfl⟩ := this
      rw [cntF_congr n _ (fun k => k = j') (fun i => ⟨fun h => castSucc_inj' h, fun h => h ▸ rfl⟩)]
      rw [cntF_single n j']

theorem cntF_le_of_mem (n : Nat) (W : Fin n → Prop) {i : Fin n} (hi : W i) : 1 ≤ cntF n W := by
  have := cntF_mono n (fun k => k = i) W (fun k hk => hk ▸ hi)
  rw [cntF_single] at this
  exact this

/-- the count of two distinct elements is 2 -/
theorem cntF_pair (n : Nat) {a b : Fin n} (hab : a ≠ b) : cntF n (fun k => k = a ∨ k = b) = 2 := by
  rw [cntF_split n _ (fun k => k = a)]
  rw [cntF_congr n (fun i => (i = a ∨ i = b) ∧ i = a) (fun k => k = a) (fun i => ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩)]
  rw [cntF_congr n (fun i => (i = a ∨ i = b) ∧ ¬ i = a) (fun k => k = b)
    (fun i => ⟨fun h => h.1.resolve_left h.2, fun h => ⟨Or.inr h, fun h' => hab (h'.symm.trans h)⟩⟩)]
  rw [cntF_single, cntF_single]

/-- **parity**: a set with a fixed-point-free involution has an even number of elements -/
theorem cntF_even (n : Nat) : ∀ (k : Nat) (W : Fin n → Prop) (π : Fin n → Fin n), cntF n W = k →
    (∀ i, W i → W (π i) ∧ π (π i) = i ∧ π i ≠ i) → k % 2 = 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro W π hk hπ
    by_cases h0 : k = 0
    · rw [h0]
    obtain ⟨v, hv⟩ := cntF_pos n W (by omega)
    obtain ⟨hvπ, hππ, hne⟩ := hπ v hv
    let W' : Fin n → Prop := fun i => W i ∧ ¬ (i = v ∨ i = π v)
    have hsplit : cntF n W = cntF n (fun i => W i ∧ (i = v ∨ i = π v)) + cntF n W' :=
      cntF_split n W (fun i => i = v ∨ i = π v)
    have h2 : cntF n (fun i => W i ∧ (i = v ∨ i = π v)) = 2 := by
      rw [cntF_congr n _ (fun i => i = v ∨ i = π v) (fun i => ⟨fun h => h.2, fun h => ⟨h.elim (fun h' => h' ▸ hv)
        (fun h' => h' ▸ hvπ), h⟩⟩)]
      exact cntF_pair n (Ne.symm hne)
    have hW' : ∀ i, W' i → W' (π i) ∧ π (π i) = i ∧ π i ≠ i := by
      intro i ⟨hi, hni⟩
      obtain ⟨h1, h2', h3⟩ := hπ i hi
      refine ⟨⟨h1, ?_⟩, h2', h3⟩
      rintro (h | h)
      · apply hni; right; rw [← h, h2']
      · apply hni; left
        have := congrArg π h
        rw [h2', hππ] at this
        exact this
    have := ih (cntF n W') (by omega) W' π rfl hW'
    omega

end cnt

end RH2F

-- ===== from RH2Vert.lean =====
/-
  RH2Vert.lean — vertex counts of edge sets and of the sides of a 2-edge-cut; parity; 2-edge-cuts as `Cut2`.
-/

namespace RH2F
open MGraph
open Classical

section vert
variable {X : MGraph}

/-- `v` is a vertex of `P` (meets an edge of `P`) -/
def meets (P : Fin X.m → Prop) (v : Fin X.n) : Prop := ∃ f, P f ∧ X.Inc f v

/-- the number of vertices of `P` -/
noncomputable def vcount (P : Fin X.m → Prop) : Nat := cntF X.n (meets P)

/-- the number of vertices of `P` with `S`-value `b` -/
noncomputable def scount (P : Fin X.m → Prop) (S : Fin X.n → Bool) (b : Bool) : Nat :=
  cntF X.n (fun v => meets P v ∧ S v = b)

/-- edge `f` of `P` crosses `S` -/
def Crosses (P : Fin X.m → Prop) (S : Fin X.n → Bool) (f : Fin X.m) : Prop :=
  P f ∧ S (X.ends f).1 ≠ S (X.ends f).2

/-- exactly two edges of `P` cross `S` -/
def TwoCut (P : Fin X.m → Prop) (S : Fin X.n → Bool) : Prop :=
  ∃ e1 e2, e1 ≠ e2 ∧ Crosses P S e1 ∧ Crosses P S e2 ∧ ∀ d, Crosses P S d → d = e1 ∨ d = e2

/-- 2-cut-reduced: every 2-edge-cut has a side with exactly two vertices -/
def TwoCutReducedOn (P : Fin X.m → Prop) : Prop :=
  ∀ S, TwoCut P S → scount P S true = 2 ∨ scount P S false = 2

theorem vcount_split (P : Fin X.m → Prop) (S : Fin X.n → Bool) :
    vcount P = scount P S true + scount P S false := by
  unfold vcount scount
  rw [cntF_split X.n (meets P) (fun v => S v = true)]
  congr 1
  apply cntF_congr
  intro v
  cases S v <;> simp

theorem scount_flip {P : Fin X.m → Prop} (C : Cut2 P) (b : Bool) : scount P C.flip.S b = scount P C.S (!b) := by
  unfold scount
  apply cntF_congr
  intro v
  rw [Cut2.flip_S]
  cases C.S v <;> cases b <;> simp

/-- the other end of an edge at `v` -/
noncomputable def other (f : Fin X.m) (v : Fin X.n) : Fin X.n :=
  if (X.ends f).1 = v then (X.ends f).2 else (X.ends f).1

theorem joins_other {f : Fin X.m} {v : Fin X.n} (h : X.Inc f v) : X.Joins f v (other f v) := by
  unfold other
  by_cases h1 : (X.ends f).1 = v
  · rw [if_pos h1]; exact Or.inl (by rw [← h1])
  · rw [if_neg h1]
    rcases h with h | h
    · exact absurd h h1
    · exact Or.inr (by rw [← h])

theorem other_eq {f : Fin X.m} {x y : Fin X.n} (h : X.Joins f x y) (hxy : x ≠ y) : other f x = y := by
  unfold other
  rcases h with h | h <;> rw [h]
  · simp
  · simp [Ne.symm hxy]

/-- **parity**: an edge set with a perfect matching has an even number of vertices -/
theorem vcount_even_of_pm (hloop : Loopless X) {P N : Fin X.m → Prop} (hN : PMOn P N) : vcount P % 2 = 0 := by
  let ch : (v : Fin X.n) → meets P v → Fin X.m := fun v h => Classical.choose (hN.2 v h)
  have key : ∀ v (h : meets P v), N (ch v h) ∧ X.Inc (ch v h) v ∧ ∀ d, N d → X.Inc d v → d = ch v h :=
    fun v h => Classical.choose_spec (hN.2 v h)
  let π : Fin X.n → Fin X.n := fun v => if h : meets P v then other (ch v h) v else v
  have hπ : ∀ v (h : meets P v), π v = other (ch v h) v := fun v h => by simp only [π, dif_pos h]
  apply cntF_even X.n _ (meets P) π rfl
  intro v hv
  obtain ⟨ha, hav, hu⟩ := key v hv
  have hj : X.Joins (ch v hv) v (π v) := by rw [hπ v hv]; exact joins_other hav
  have hne : v ≠ π v := ne_of_joins hloop hj
  have hw : meets P (π v) := ⟨ch v hv, hN.1 _ ha, joins_inc_right hj⟩
  refine ⟨hw, ?_, Ne.symm hne⟩
  obtain ⟨ha', _, hu'⟩ := key (π v) hw
  have heq : ch v hv = ch (π v) hw := hu' _ ha (joins_inc_right hj)
  rw [hπ (π v) hw, ← heq]
  exact other_eq (Or.symm hj) (Ne.symm hne)

/-- the vertices of the edge closure are those of side `A` -/
theorem Cut2.meets_clo {P : Fin X.m → Prop} (C : Cut2 P) (v : Fin X.n) :
    meets C.clo v ↔ meets P v ∧ C.S v = true := by
  constructor
  · rintro ⟨i, hi, hiv⟩
    refine ⟨?_, C.clo_side hi hiv⟩
    rcases hi with rfl | ⟨d, rfl, hd⟩
    · rcases (C.inc_new_iff).1 hiv with rfl | rfl
      · exact ⟨C.e1, C.P1, joins_inc_left C.j1⟩
      · exact ⟨C.e2, C.P2, joins_inc_left C.j2⟩
    · exact ⟨d, hd.1, addEdge_inc_old.1 hiv⟩
  · rintro ⟨⟨f, hf, hfv⟩, hs⟩
    obtain ⟨h1, h2⟩ := C.toClo_props hf hfv hs
    exact ⟨_, h1, h2⟩

theorem Cut2.vcount_clo {P : Fin X.m → Prop} (C : Cut2 P) : vcount C.clo = scount P C.S true :=
  cntF_congr X.n _ _ C.meets_clo

/-- the vertices of the digon closure are those of side `A` and `b1`, `b2` -/
theorem Cut2.meets_cloD {P : Fin X.m → Prop} (C : Cut2 P) (v : Fin X.n) :
    meets C.cloD v ↔ (meets P v ∧ C.S v = true) ∨ v = C.b1 ∨ v = C.b2 := by
  constructor
  · rintro ⟨i, hi, hiv⟩
    rcases C.cloD_vertex hi hiv with hs | h | h
    · refine Or.inl ⟨?_, hs⟩
      rcases hi with rfl | rfl | ⟨d, rfl, hd⟩
      · exact absurd ((C.XD_inc_dl1).1 hiv) (C.dl_ne_A hs)
      · exact absurd ((C.XD_inc_dl2).1 hiv) (C.dl_ne_A hs)
      · exact ⟨d, C.pole_P hd, (C.XD_inc_old).1 hiv⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨⟨f, hf, hfv⟩, hs⟩ | h)
    · exact ⟨C.oD f, (C.cloD_old_iff).2 (C.pole_of_inc hf hfv hs), (C.XD_inc_old).2 hfv⟩
    · exact ⟨C.dl1, Or.inl rfl, (C.XD_inc_dl1).2 h⟩

theorem Cut2.vcount_cloD {P : Fin X.m → Prop} (C : Cut2 P) : vcount C.cloD = scount P C.S true + 2 := by
  unfold vcount scount
  show cntF X.n (@meets C.XD C.cloD) = cntF X.n (fun v => meets P v ∧ C.S v = true) + 2
  rw [cntF_congr X.n (@meets C.XD C.cloD) _ C.meets_cloD, cntF_split X.n _ (fun v => C.S v = true)]
  congr 1
  · apply cntF_congr
    intro v
    constructor
    · rintro ⟨h | h | h, hs⟩
      · exact h
      · rw [h, C.sb1] at hs; exact absurd hs (by decide)
      · rw [h, C.sb2] at hs; exact absurd hs (by decide)
    · intro h; exact ⟨Or.inl h, h.2⟩
  · rw [cntF_congr X.n _ (fun v => v = C.b1 ∨ v = C.b2)]
    · exact cntF_pair X.n C.hb
    · intro v
      constructor
      · rintro ⟨h | h, hs⟩
        · exact absurd h.2 hs
        · exact h
      · intro h
        refine ⟨Or.inr h, ?_⟩
        rcases h with rfl | rfl
        · rw [C.sb1]; decide
        · rw [C.sb2]; decide

/-- a vertex set with at least three elements has an element different from two given ones -/
theorem cntF_other {n : Nat} {W : Fin n → Prop} (h : 3 ≤ cntF n W) (a b : Fin n) :
    ∃ v, W v ∧ v ≠ a ∧ v ≠ b := by
  have hs := cntF_split n W (fun v => v = a ∨ v = b)
  have h2 : cntF n (fun v => W v ∧ (v = a ∨ v = b)) ≤ 2 := by
    by_cases hab : a = b
    · have := cntF_mono n (fun v => W v ∧ (v = a ∨ v = b)) (fun v => v = a) (fun v hv => by
        rcases hv.2 with h | h
        · exact h
        · exact h.trans hab.symm)
      rw [cntF_single] at this; omega
    · have := cntF_mono n (fun v => W v ∧ (v = a ∨ v = b)) (fun v => v = a ∨ v = b) (fun v hv => hv.2)
      rw [cntF_pair n hab] at this; exact this
  obtain ⟨v, hv, hne⟩ := cntF_pos n (fun v => W v ∧ ¬ (v = a ∨ v = b)) (by omega)
  exact ⟨v, hv, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩

/-- the end of `f` on side `true` of `S` (for a crossing edge) -/
noncomputable def endT (S : Fin X.n → Bool) (f : Fin X.m) : Fin X.n :=
  if S (X.ends f).1 = true then (X.ends f).1 else (X.ends f).2
noncomputable def endF (S : Fin X.n → Bool) (f : Fin X.m) : Fin X.n :=
  if S (X.ends f).1 = true then (X.ends f).2 else (X.ends f).1

theorem endTF {P : Fin X.m → Prop} {S : Fin X.n → Bool} {f : Fin X.m} (h : Crosses P S f) :
    X.Joins f (endT S f) (endF S f) ∧ S (endT S f) = true ∧ S (endF S f) = false := by
  obtain ⟨_, hne⟩ := h
  unfold endT endF
  cases h1 : S (X.ends f).1 <;> cases h2 : S (X.ends f).2 <;> rw [h1, h2] at hne
  · exact absurd rfl hne
  · simp only [Bool.false_eq_true, if_false]; exact ⟨Or.inr rfl, h2, h1⟩
  · simp only [if_true]; exact ⟨Or.inl rfl, h1, h2⟩
  · exact absurd rfl hne

/-- a 2-edge-cut of a connected bridgeless loopless cubic `P` has distinct ends on each side: it is a `Cut2` -/
theorem cut2_of_twoCut {P : Fin X.m → Prop} (hG : InG X P) {S : Fin X.n → Bool} (hS : TwoCut P S) :
    ∃ C : Cut2 P, C.S = S := by
  obtain ⟨e1, e2, hne, c1, c2, hall⟩ := hS
  obtain ⟨j1, sa1, sb1⟩ := endTF c1
  obtain ⟨j2, sa2, sb2⟩ := endTF c2
  have hcut : ∀ f, P f → S (X.ends f).1 ≠ S (X.ends f).2 → f = e1 ∨ f = e2 := fun f hf h => hall f ⟨hf, h⟩
  -- a common end of both cut edges on one side gives a bridge
  have distinct : ∀ (b : Bool) (u : Fin X.n), S u = b → X.Inc e1 u → X.Inc e2 u → False := by
    intro b u hu i1 i2
    obtain ⟨h, hh, ih, he1, he2, hcov⟩ := third_edge hG.2.2.2 c1.1 c2.1 i1 i2 hne
    obtain ⟨w, hw⟩ := joins_of_inc ih
    have huw : u ≠ w := ne_of_joins hG.1 hw
    -- `w` is on the side of `u` (otherwise `h` would be a third crossing edge)
    have hsw : S w = b := by
      apply Classical.byContradiction
      intro hsw
      have hcr : S (X.ends h).1 ≠ S (X.ends h).2 := by
        rcases hw with hw | hw <;> rw [hw] <;> simp only [hu] <;>
          intro heq <;> apply hsw <;> first | exact heq.symm | exact heq
      rcases hcut h hh hcr with h' | h'
      · exact he1 h'
      · exact he2 h'
    -- move `u` to the other side: only `h` crosses
    let V : Fin X.n → Bool := fun v => if v = u then !b else S v
    have Vu : V u = !b := by simp [V]
    have Vo : ∀ v, v ≠ u → V v = S v := fun v hv => by simp [V, hv]
    apply bridgeless_sep hG.2.2.1 hh V
    · rcases hw with hw | hw <;> rw [hw] <;> simp only [Vu, Vo w (Ne.symm huw), hsw] <;> cases b <;> decide
    · intro d hd hdh
      by_cases hdu : X.Inc d u
      · rcases hcov d hd hdu with rfl | rfl | rfl
        · -- `e1`: joins `u` (moved) and a vertex of the other side
          obtain ⟨y, hy⟩ := joins_of_inc hdu
          have hyu : y ≠ u := Ne.symm (ne_of_joins hG.1 hy)
          have hys : S y = !b := by
            have hc := c1.2
            rcases hy with hy | hy <;> rw [hy] at hc <;> rw [hu] at hc <;> cases b <;> cases h' : S y <;>
              simp_all
          rcases hy with hy | hy <;> rw [hy] <;> simp only [Vu, Vo y hyu, hys]
        · obtain ⟨y, hy⟩ := joins_of_inc hdu
          have hyu : y ≠ u := Ne.symm (ne_of_joins hG.1 hy)
          have hys : S y = !b := by
            have hc := c2.2
            rcases hy with hy | hy <;> rw [hy] at hc <;> rw [hu] at hc <;> cases b <;> cases h' : S y <;>
              simp_all
          rcases hy with hy | hy <;> rw [hy] <;> simp only [Vu, Vo y hyu, hys]
        · exact absurd rfl hdh
      · have h1 : (X.ends d).1 ≠ u := fun h' => hdu (Or.inl h')
        have h2 : (X.ends d).2 ≠ u := fun h' => hdu (Or.inr h')
        rw [Vo _ h1, Vo _ h2]
        apply Classical.byContradiction
        intro hcr
        rcases hcut d hd hcr with rfl | rfl
        · exact hdu i1
        · exact hdu i2
  have ha : endT S e1 ≠ endT S e2 := fun h =>
    distinct true _ sa1 (joins_inc_left j1) (h ▸ joins_inc_left j2)
  have hb : endF S e1 ≠ endF S e2 := fun h =>
    distinct false _ sb1 (joins_inc_right j1) (h ▸ joins_inc_right j2)
  exact ⟨⟨S, e1, e2, endT S e1, endT S e2, endF S e1, endF S e2, c1.1, c2.1, j1, j2, sa1, sa2, sb1, sb2, hne,
    ha, hb, hcut⟩, rfl⟩

end vert

end RH2F

-- ===== from RH2Red1.lean =====
/-
  RH2Red1.lean — ingredients of the induction of Theorem EX1-RED (fact 0e90cbc9a9e79513): parity of 2-edge-cut
  sides, a minimal side, and (m1).
-/

namespace RH2F
open MGraph
open Classical

section red1
variable {X : MGraph} {P : Fin X.m → Prop}

/-- under (P), a member of 𝒢 has an even number of vertices -/
theorem vcount_even (hPS : PStat) {Y : MGraph} {Q : Fin Y.m → Prop} (hG : InG Y Q) : vcount Q % 2 = 0 := by
  by_cases hne : ∃ h, Q h
  · obtain ⟨h, hh⟩ := hne
    obtain ⟨N, hN, _⟩ := hPS Y Q hG h hh true
    exact vcount_even_of_pm hG.1 hN
  · have : vcount Q = 0 := cntF_eq_zero _ _ (fun v ⟨f, hf, _⟩ => hne ⟨f, hf⟩)
    rw [this]

/-- the sides of a 2-edge-cut have an even number of vertices -/
theorem Cut2.side_even (hPS : PStat) (C : Cut2 P) (hG : InG X P) : scount P C.S true % 2 = 0 := by
  rw [← C.vcount_clo]; exact vcount_even hPS (C.clo_inG hG)

/-- side `A` is nonempty -/
theorem Cut2.side_pos (C : Cut2 P) : 1 ≤ scount P C.S true :=
  cntF_le_of_mem X.n _ (i := C.a1) ⟨⟨C.e1, C.P1, joins_inc_left C.j1⟩, C.sa1⟩

/-- a side with more than 2 vertices has at least 4 -/
theorem Cut2.side_ge4 (hPS : PStat) (C : Cut2 P) (hG : InG X P) (h : scount P C.S true ≠ 2) :
    4 ≤ scount P C.S true := by
  have he := C.side_even hPS hG
  have hp := C.side_pos
  omega

/-- a big cut: both sides have at least 4 vertices -/
def BigCut (P : Fin X.m → Prop) (S : Fin X.n → Bool) : Prop :=
  TwoCut P S ∧ 4 ≤ scount P S true ∧ 4 ≤ scount P S false

/-- minimal elements exist -/
theorem exists_min_nat {α : Type} (p : α → Prop) (f : α → Nat) (h : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → f a ≤ f b := by
  apply Classical.byContradiction
  intro hno
  have step : ∀ a, p a → ∃ b, p b ∧ f b < f a := by
    intro a ha
    apply Classical.byContradiction
    intro hb
    apply hno
    refine ⟨a, ha, fun b hpb => ?_⟩
    apply Classical.byContradiction
    intro hlt
    exact hb ⟨b, hpb, by omega⟩
  have : ∀ m, ∀ a, p a → f a ≠ m := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro a ha hfa
      obtain ⟨b, hb, hlt⟩ := step a ha
      exact ih (f b) (by omega) b hb rfl
  obtain ⟨a, ha⟩ := h
  exact this (f a) a ha rfl

/-- (m1) of EX1-RED: if side `B` has at least 4 vertices then at most one edge joins `b1` and `b2` -/
theorem Cut2.m1 (C : Cut2 P) (hG : InG X P) (hB : 4 ≤ scount P C.S false) :
    ∀ f f', P f → P f' → X.Joins f C.b1 C.b2 → X.Joins f' C.b1 C.b2 → f = f' := by
  intro r r' hr hr' hj hj'
  apply Classical.byContradiction
  intro hne
  -- a vertex of `B` other than `b1`, `b2`
  obtain ⟨w, ⟨⟨g, hg, hgw⟩, hwS⟩, hw1, hw2⟩ := cntF_other (W := fun v => meets P v ∧ C.S v = false)
    (by unfold scount at hB; omega) C.b1 C.b2
  -- the labelling of `A ∪ {b1, b2}`
  let U : Fin X.n → Bool := fun v => C.S v || decide (v = C.b1) || decide (v = C.b2)
  have hUA : ∀ v, C.S v = true → U v = true := fun v hv => by simp [U, hv]
  have hU1 : U C.b1 = true := by simp [U]
  have hU2 : U C.b2 = true := by simp [U]
  have hUB : ∀ v, C.S v = false → v ≠ C.b1 → v ≠ C.b2 → U v = false := fun v hv h1 h2 => by simp [U, hv, h1, h2]
  -- the edges at `b1` and `b2` are the cut edge and the two edges joining `b1, b2`
  have hr_e1 : r ≠ C.e1 := by
    intro h; subst h
    rcases joins_unique hj C.j1 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact C.a1_ne_b1 h1.symm
    · exact C.a1_ne_b2 h2.symm
  have hr'_e1 : r' ≠ C.e1 := by
    intro h; subst h
    rcases joins_unique hj' C.j1 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact C.a1_ne_b1 h1.symm
    · exact C.a1_ne_b2 h2.symm
  have hr_e2 : r ≠ C.e2 := by
    intro h; subst h
    rcases joins_unique hj C.j2 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact C.a2_ne_b1 h1.symm
    · exact C.hb h1
  have hr'_e2 : r' ≠ C.e2 := by
    intro h; subst h
    rcases joins_unique hj' C.j2 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact C.a2_ne_b1 h1.symm
    · exact C.hb h1
  have at_b1 := third_edge hG.2.2.2 hr hr' (joins_inc_left hj) (joins_inc_left hj') hne
  have at_b2 := third_edge hG.2.2.2 hr hr' (joins_inc_right hj) (joins_inc_right hj') hne
  obtain ⟨t1, _, _, _, _, cov1⟩ := at_b1
  obtain ⟨t2, _, _, _, _, cov2⟩ := at_b2
  have e1_at_b1 : C.e1 = r ∨ C.e1 = r' ∨ C.e1 = t1 := cov1 _ C.P1 (joins_inc_right C.j1)
  have e2_at_b2 : C.e2 = r ∨ C.e2 = r' ∨ C.e2 = t2 := cov2 _ C.P2 (joins_inc_right C.j2)
  -- no edge of `P` crosses `U`
  have hsep : ∀ d, P d → U (X.ends d).1 = U (X.ends d).2 := by
    intro d hd
    rcases C.cases_P hd with h | h | h
    · rw [hUA _ h.2.1, hUA _ h.2.2]
    · -- an edge inside `B`: if it meets `b1` or `b2` it is `r`, `r'`
      have s1 : C.S (X.ends d).1 = false := by have := h.2.1; rw [Cut2.flip_S] at this; simpa using this
      have s2 : C.S (X.ends d).2 = false := by have := h.2.2; rw [Cut2.flip_S] at this; simpa using this
      have ne_cut : d ≠ C.e1 ∧ d ≠ C.e2 := ⟨fun h' => C.flip.not_inA_of_cut (Or.inl h') h,
        fun h' => C.flip.not_inA_of_cut (Or.inr h') h⟩
      have rr : ∀ v, X.Inc d v → (v = C.b1 ∨ v = C.b2) → d = r ∨ d = r' := by
        intro v hv hv12
        rcases hv12 with rfl | rfl
        · rcases cov1 d hd hv with h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
          · exfalso; rcases e1_at_b1 with h'' | h'' | h''
            · exact hr_e1 h''.symm
            · exact hr'_e1 h''.symm
            · exact ne_cut.1 (h'.trans h''.symm)
        · rcases cov2 d hd hv with h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
          · exfalso; rcases e2_at_b2 with h'' | h'' | h''
            · exact hr_e2 h''.symm
            · exact hr'_e2 h''.symm
            · exact ne_cut.2 (h'.trans h''.symm)
      have both : ∀ d', (d' = r ∨ d' = r') → U (X.ends d').1 = true ∧ U (X.ends d').2 = true := by
        rintro d' (rfl | rfl)
        · rcases hj with h' | h' <;> rw [h'] <;> exact ⟨by first | exact hU1 | exact hU2, by first | exact hU1 | exact hU2⟩
        · rcases hj' with h' | h' <;> rw [h'] <;> exact ⟨by first | exact hU1 | exact hU2, by first | exact hU1 | exact hU2⟩
      by_cases h1 : (X.ends d).1 = C.b1 ∨ (X.ends d).1 = C.b2
      · have := both d (rr _ (Or.inl rfl) h1); rw [this.1, this.2]
      by_cases h2 : (X.ends d).2 = C.b1 ∨ (X.ends d).2 = C.b2
      · have := both d (rr _ (Or.inr rfl) h2); rw [this.1, this.2]
      simp only [not_or] at h1 h2
      rw [hUB _ s1 h1.1 h1.2, hUB _ s2 h2.1 h2.2]
    · rcases h with rfl | rfl
      · rcases C.j1 with h' | h' <;> rw [h'] <;> simp only [hUA _ C.sa1, hU1]
      · rcases C.j2 with h' | h' <;> rw [h'] <;> simp only [hUA _ C.sa2, hU2]
  -- connectivity is violated
  have hc := hG.2.1 U hsep g C.e1 hg C.P1
  have hge : U (X.ends g).1 = false := by
    have hgB : C.flip.inA g ∨ C.isCut g := by
      rcases C.cases_P hg with h | h | h
      · have := C.side_of_inA h hgw; rw [hwS] at this; exact absurd this (by decide)
      · exact Or.inl h
      · exact Or.inr h
    rcases hgB with h | h
    · have hsep' := hsep g hg
      rcases hgw with h' | h'
      · rw [h']; exact hUB w hwS hw1 hw2
      · rw [hsep', h']; exact hUB w hwS hw1 hw2
    · rcases h with rfl | rfl
      · rcases C.inc_e1 hgw with h' | h'
        · rw [h', C.sa1] at hwS; exact absurd hwS (by decide)
        · exact absurd h' hw1
      · rcases C.inc_e2 hgw with h' | h'
        · rw [h', C.sa2] at hwS; exact absurd hwS (by decide)
        · exact absurd h' hw2
  have he1 : U (X.ends C.e1).1 = true := by
    rcases C.j1 with h' | h' <;> rw [h']
    · exact hUA _ C.sa1
    · exact hU1
  rw [hge, he1] at hc
  exact absurd hc (by decide)

/-- the side `true` of a 2-edge-cut is even (general `S`, via `cut2_of_twoCut`) -/
theorem twoCut_even (hPS : PStat) (hG : InG X P) {S : Fin X.n → Bool} (hS : TwoCut P S) :
    scount P S true % 2 = 0 := by
  obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS
  exact C.side_even hPS hG

theorem twoCut_pos (hG : InG X P) {S : Fin X.n → Bool} (hS : TwoCut P S) (b : Bool) : 1 ≤ scount P S b := by
  obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS
  cases b
  · have := C.flip.side_pos
    rw [scount_flip] at this; exact this
  · exact C.side_pos

/-- the labelling `S ∧ (S' = β)`: the vertices of `A` on side `β` of `S'` -/
def Cut2.sub (C : Cut2 P) (S' : Fin X.n → Bool) (β : Bool) : Fin X.n → Bool :=
  fun v => C.S v && (S' v == β)

theorem Cut2.sub_true {C : Cut2 P} {S' : Fin X.n → Bool} {β : Bool} {v : Fin X.n} :
    C.sub S' β v = true ↔ C.S v = true ∧ S' v = β := by
  simp [Cut2.sub]

theorem Cut2.scount_sub (C : Cut2 P) (S' : Fin X.n → Bool) (β : Bool) :
    scount P (C.sub S' β) true = scount C.clo S' β := by
  unfold scount
  apply cntF_congr
  intro v
  rw [C.sub_true]
  show meets P v ∧ C.S v = true ∧ S' v = β ↔ @meets (addEdge X C.a1 C.a2) C.clo v ∧ S' v = β
  rw [C.meets_clo]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- a 2-edge-cut side smaller than a minimal big side, with a large complement, has exactly two vertices -/
theorem small_side (hPS : PStat) (hG : InG X P) {k : Nat}
    (hmin : ∀ S', BigCut P S' → k ≤ scount P S' true) {V : Fin X.n → Bool} (hV : TwoCut P V)
    (hlt : scount P V true < k) (hf : 4 ≤ scount P V false) : scount P V true = 2 := by
  apply Classical.byContradiction
  intro h2
  have he := twoCut_even hPS hG hV
  have hp := twoCut_pos hG hV true
  have := hmin V ⟨hV, by omega, hf⟩
  omega

theorem bne_of_ne {x y β : Bool} (h : x ≠ y) : (x == β) ≠ (y == β) := by
  cases x <;> cases y <;> cases β <;> simp_all

/-- **(m2) of EX1-RED**: for a side `A` of minimum size among the big 2-edge-cut sides, the edge closure `G_A` is
    2-cut-reduced -/
theorem Cut2.m2 (hPS : PStat) (C : Cut2 P) (hG : InG X P)
    (hmin : ∀ S', BigCut P S' → scount P C.S true ≤ scount P S' true) (hB : 4 ≤ scount P C.S false) :
    TwoCutReducedOn C.clo := by
  intro S' hS'
  have hsplitP := vcount_split P C.S
  have hsplitC := vcount_split C.clo S'
  rw [C.vcount_clo] at hsplitC
  -- the vertices `a1`, `a2` of the closure
  have ma1 : @meets (addEdge X C.a1 C.a2) C.clo C.a1 := (C.meets_clo C.a1).2 ⟨⟨C.e1, C.P1, joins_inc_left C.j1⟩, C.sa1⟩
  have ma2 : @meets (addEdge X C.a1 C.a2) C.clo C.a2 := (C.meets_clo C.a2).2 ⟨⟨C.e2, C.P2, joins_inc_left C.j2⟩, C.sa2⟩
  -- counting: a side `V = A ∩ {S' = β}` avoiding `a_i` is smaller than `A`
  have count : ∀ β (u : Fin X.n), @meets (addEdge X C.a1 C.a2) C.clo u → S' u = !β →
      TwoCut P (C.sub S' β) → scount C.clo S' β = 2 := by
    intro β u hu hSu hV
    have h1 : 1 ≤ scount C.clo S' (!β) := cntF_le_of_mem _ _ (i := u) ⟨hu, hSu⟩
    have hsp := vcount_split P (C.sub S' β)
    have hsum : scount C.clo S' β + scount C.clo S' (!β) = scount P C.S true := by
      cases β
      · simp only [Bool.not_false] at h1 ⊢; omega
      · simp only [Bool.not_true] at h1 ⊢; omega
    refine (C.scount_sub S' β).symm.trans ?_
    apply small_side hPS hG hmin hV
    · have hss := C.scount_sub S' β; omega
    · have hss := C.scount_sub S' β; omega
  obtain ⟨d1, d2, hne, c1, c2, hall⟩ := hS'
  -- crossing P-edges of `C.sub S' β` inside `A` are the old edges crossing `S'`
  have inside : ∀ β d, C.inA d → (Crosses P (C.sub S' β) d ↔ Crosses C.clo S' (Fin.castSucc d)) := by
    intro β d hd
    unfold Crosses Cut2.sub
    rw [addEdge_ends_old, hd.2.1, hd.2.2]
    simp only [Bool.true_and]
    constructor
    · intro h; refine ⟨C.clo_old hd, fun heq => h.2 (by rw [heq])⟩
    · intro h; exact ⟨hd.1, bne_of_ne h.2⟩
  have outsideB : ∀ β d, C.flip.inA d → ¬ Crosses P (C.sub S' β) d := by
    intro β d hd h
    have s1 : C.S (X.ends d).1 = false := by have := hd.2.1; rw [Cut2.flip_S] at this; simpa using this
    have s2 : C.S (X.ends d).2 = false := by have := hd.2.2; rw [Cut2.flip_S] at this; simpa using this
    apply h.2
    simp [Cut2.sub, s1, s2]
  have cutV : ∀ β (e : Fin X.m) (a b : Fin X.n), X.Joins e a b → C.S b = false →
      (Crosses P (C.sub S' β) e ↔ P e ∧ C.S a = true ∧ S' a = β) := by
    intro β e a b hj hb
    unfold Crosses
    have hvb : C.sub S' β b = false := by simp [Cut2.sub, hb]
    rcases hj with h | h <;> rw [h] <;> simp only [hvb] <;>
      constructor <;> intro hh
    · exact ⟨hh.1, (C.sub_true).1 (by cases hx : C.sub S' β a <;> simp_all)⟩
    · exact ⟨hh.1, by rw [(C.sub_true).2 hh.2]; decide⟩
    · exact ⟨hh.1, (C.sub_true).1 (by cases hx : C.sub S' β a <;> simp_all)⟩
    · exact ⟨hh.1, by rw [(C.sub_true).2 hh.2]; decide⟩
  have lastC : Crosses C.clo S' (Fin.last X.m) ↔ S' C.a1 ≠ S' C.a2 := by
    unfold Crosses; rw [addEdge_ends_new]; exact ⟨fun h => h.2, fun h => ⟨C.clo_last, h⟩⟩
  have oldE : ∀ i, Crosses C.clo S' i → i ≠ Fin.last X.m → ∃ d, i = Fin.castSucc d ∧ C.inA d := by
    intro i hi hil
    rcases addEdge_cases i with rfl | ⟨d, rfl⟩
    · exact absurd rfl hil
    · exact ⟨d, rfl, (C.clo_old_iff).1 hi.1⟩
  by_cases hl : S' C.a1 = S' C.a2
  · -- (i) `g_A` does not cross `S'`: the side not containing `a1, a2`
    have nl : ¬ Crosses C.clo S' (Fin.last X.m) := fun h => (lastC.1 h) hl
    obtain ⟨d1', rfl, h1A⟩ := oldE d1 c1 (fun h => nl (h ▸ c1))
    obtain ⟨d2', rfl, h2A⟩ := oldE d2 c2 (fun h => nl (h ▸ c2))
    let β := !(S' C.a1)
    have hV : TwoCut P (C.sub S' β) := by
      refine ⟨d1', d2', fun h => hne (h ▸ rfl), (inside β _ h1A).2 c1, (inside β _ h2A).2 c2, ?_⟩
      intro d hd
      rcases C.cases_P hd.1 with h | h | h
      · rcases hall _ ((inside β d h).1 hd) with h' | h'
        · exact Or.inl (castSucc_inj' h')
        · exact Or.inr (castSucc_inj' h')
      · exact absurd hd (outsideB β d h)
      · exfalso
        rcases h with rfl | rfl
        · have := ((cutV β _ _ _ C.j1 C.sb1).1 hd).2.2
          simp [β] at this
        · have := ((cutV β _ _ _ C.j2 C.sb2).1 hd).2.2
          simp [β, hl] at this
    have := count β C.a1 ma1 (by simp [β]) hV
    cases hβ : S' C.a1
    · simp only [β, hβ, Bool.not_false] at this; exact Or.inl this
    · simp only [β, hβ, Bool.not_true] at this; exact Or.inr this
  · -- (ii) `g_A` crosses `S'`: the side containing `a1`
    have hlc : Crosses C.clo S' (Fin.last X.m) := lastC.2 hl
    have hother : ∃ h, C.inA h ∧ Crosses C.clo S' (Fin.castSucc h) ∧
        ∀ i, Crosses C.clo S' i → i = Fin.last X.m ∨ i = Fin.castSucc h := by
      rcases hall _ hlc with h' | h'
      · obtain ⟨h, rfl, hA⟩ := oldE d2 c2 (fun h => hne (h'.symm.trans h.symm))
        refine ⟨h, hA, c2, fun i hi => ?_⟩
        rcases hall i hi with h'' | h''
        · exact Or.inl (h''.trans h'.symm)
        · exact Or.inr h''
      · obtain ⟨h, rfl, hA⟩ := oldE d1 c1 (fun h => hne (h.trans h'))
        refine ⟨h, hA, c1, fun i hi => ?_⟩
        rcases hall i hi with h'' | h''
        · exact Or.inr h''
        · exact Or.inl (h''.trans h'.symm)
    obtain ⟨h, hA, hc, hall'⟩ := hother
    let β := S' C.a1
    have hV : TwoCut P (C.sub S' β) := by
      refine ⟨C.e1, h, fun h' => C.not_inA_of_cut (Or.inl rfl) (by rw [h']; exact hA),
        (cutV β _ _ _ C.j1 C.sb1).2 ⟨C.P1, C.sa1, rfl⟩, (inside β _ hA).2 hc, ?_⟩
      intro d hd
      rcases C.cases_P hd.1 with h' | h' | h'
      · rcases hall' _ ((inside β d h').1 hd) with h'' | h''
        · exact absurd h'' (castSucc_ne_last d)
        · exact Or.inr (castSucc_inj' h'')
      · exact absurd hd (outsideB β d h')
      · rcases h' with rfl | rfl
        · exact Or.inl rfl
        · exfalso
          have := ((cutV β _ _ _ C.j2 C.sb2).1 hd).2.2
          exact hl this.symm
    have hSa2 : S' C.a2 = !β := by
      simp only [β]; cases h1 : S' C.a1 <;> cases h2 : S' C.a2 <;> simp_all
    have := count β C.a2 ma2 hSa2 hV
    cases hβ : S' C.a1
    · simp only [β, hβ] at this; exact Or.inr this
    · simp only [β, hβ] at this; exact Or.inl this

end red1

end RH2F

-- ===== from RH2Red.lean =====
/-
  RH2Red.lean — Theorem EX1-RED (fact 0e90cbc9a9e79513) in Lean 4.20 core, from (P), hypothesis (H) and the small-side
  facts `SmallFacts` (classification of fact 7922314679f8733d with the Lean tables TAB-A/B/C, facts 22e13cb8,
  6729360b, 1cbbdf1f, and (R1)–(R3), (T6) of EX1-RED), by strong induction on the number of vertices.
-/

namespace RH2F
open MGraph
open Classical

/-- Hypothesis (H) of RH2 (fact 4ad4824af78b0300): every connected bridgeless loopless cubic multigraph on at least
    10 vertices that is 2-cut-reduced is EX1-good -/
def Hyp : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → TwoCutReducedOn P → EX1On P

/-- the facts about sides with at most 8 vertices used by EX1-RED -/
structure SmallFacts : Prop where
  /-- a 6-vertex side is digon-good (its digon closure has 8 vertices and a digon, so it is not in BAD) -/
  s2 : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 6 → EX1On C.cloD
  /-- a 4-vertex side is closed-good and has recipe D or E ((R3)) -/
  s3 : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 4 →
    EX1On C.clo ∧ (C.RecipeD ∨ C.RecipeE)
  /-- a side with at most 8 vertices that is not closed-good is in BAD: recipe D ((R1)) and at least 6 vertices -/
  s4 : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true ≤ 8 → ¬ EX1On C.clo →
    C.RecipeD ∧ 6 ≤ scount P C.S true
  /-- an 8-vertex side that is not closed-good is Rep25: recipe E ((R2)) -/
  s5 : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 8 → ¬ EX1On C.clo →
    C.RecipeE
  /-- the 10-vertex gluings of table T6 -/
  tabc : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 4 →
    scount P C.S false = 6 → ¬ EX1On C.flip.clo → ¬ EX1On C.cloD → ¬ C.RecipeD → EX1On P

section red
variable {X : MGraph} {P : Fin X.m → Prop}

theorem Cut2.flip_flip_cloD (C : Cut2 P) (i : Fin C.XD.m) : C.flip.flip.cloD i ↔ C.cloD i := by
  unfold Cut2.cloD
  rw [C.flip_flip_pole_eq]
  exact Iff.rfl

theorem Cut2.twoCut_self (C : Cut2 P) : TwoCut P C.S :=
  ⟨C.e1, C.e2, C.ne12, ⟨C.P1, by rcases C.cut_sides (Or.inl rfl) (joins_ends C.e1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> decide⟩, ⟨C.P2, by rcases C.cut_sides (Or.inr rfl) (joins_ends C.e2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> decide⟩, fun d hd => C.cut d hd.1 hd.2⟩

/-- **Theorem EX1-RED** (fact 0e90cbc9a9e79513). -/
theorem ex1red (hPS : PStat) (hSF : SmallFacts) (hH : Hyp) :
    ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → EX1On P := by
  suffices h : ∀ n, ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P = n → 10 ≤ n → EX1On P from
    fun X P hG h10 => h _ X P hG rfl h10
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro X P hG hn h10
  have IH : ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InG Y Q → 10 ≤ vcount Q → vcount Q < n → EX1On Q :=
    fun Y Q hGQ h1 h2 => ih _ h2 Y Q hGQ rfl h1
  by_cases hred : TwoCutReducedOn P
  · exact hH X P hG (hn ▸ h10) hred
  -- a big 2-edge-cut, and one with a smallest side
  have hbig : ∃ S, BigCut P S := by
    simp only [TwoCutReducedOn, not_forall] at hred
    obtain ⟨S, hS, hno⟩ := hred
    obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS
    refine ⟨C.S, hS, C.side_ge4 hPS hG (fun h => hno (Or.inl h)), ?_⟩
    have := C.flip.side_ge4 hPS hG (by rw [scount_flip]; exact fun h => hno (Or.inr h))
    rwa [scount_flip] at this
  obtain ⟨S0, hS0, hmin⟩ := exists_min_nat (BigCut P) (fun S => scount P S true) hbig
  obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS0.1
  have hA4 : 4 ≤ scount P C.S true := hS0.2.1
  have hB4 : 4 ≤ scount P C.S false := hS0.2.2
  -- the minimal side is not larger than the other side
  have hAB : scount P C.S true ≤ scount P C.S false := by
    have := hmin C.flip.S ⟨C.flip.twoCut_self, by rw [scount_flip]; exact hB4, by rw [scount_flip]; exact hA4⟩
    rw [scount_flip] at this; exact this
  have hn' : n = scount P C.S true + scount P C.S false := by rw [← hn]; exact vcount_split P C.S
  have evA := C.side_even hPS hG
  have evB : scount P C.S false % 2 = 0 := by have := C.flip.side_even hPS hG; rwa [scount_flip] at this
  -- (m1), (m2) and the closures
  have m1b := C.m1 hG hB4
  have m1a : ∀ f f', P f → P f' → X.Joins f C.a1 C.a2 → X.Joins f' C.a1 C.a2 → f = f' :=
    C.flip.m1 hG (by rw [scount_flip]; exact hA4)
  have m2 := C.m2 hPS hG hmin hB4
  have GA := C.clo_inG hG
  have GB := C.flip.clo_inG hG
  have GDA := C.cloD_inG hG
  have GDB := C.flip.cloD_inG hG
  have vA : vcount C.clo = scount P C.S true := C.vcount_clo
  have vB : vcount C.flip.clo = scount P C.S false := by rw [C.flip.vcount_clo, scount_flip]; rfl
  have vDA : vcount C.cloD = scount P C.S true + 2 := C.vcount_cloD
  have vDB : vcount C.flip.cloD = scount P C.S false + 2 := by rw [C.flip.vcount_cloD, scount_flip]; rfl
  -- the gluing lemmas
  have twoC : EX1On C.clo → EX1On C.flip.clo → ((∃ r, P r ∧ X.Joins r C.b1 C.b2) → EX1On C.cloD) →
      ((∃ r, P r ∧ X.Joins r C.a1 C.a2) → EX1On C.flip.cloD) → EX1On P :=
    fun h1 h2 h3 h4 => ex1_2c'' hPS C hG m1a m1b h1 h2 h3 h4
  have srA : C.RecipeD → EX1On C.flip.cloD → EX1On P := fun h1 h2 => C.sr_a hPS hG h1 h2
  have srB : C.RecipeE → EX1On C.flip.clo → EX1On P := fun h1 h2 => C.sr_b hPS hG m1b h1 h2
  have srA' : C.flip.RecipeD → EX1On C.cloD → EX1On P := fun h1 h2 =>
    C.flip.sr_a hPS hG h1 (ex1On_congr (fun i => (C.flip_flip_cloD i).symm) h2)
  have srB' : C.flip.RecipeE → EX1On C.clo → EX1On P := fun h1 h2 =>
    C.flip.sr_b hPS hG m1a h1 (ex1On_congr (fun i => (C.flip_flip_clo i).symm) h2)
  have sB : ∀ k, scount P C.flip.S true = k ↔ scount P C.S false = k := fun k => by rw [scount_flip]; rfl
  by_cases hA10 : 10 ≤ scount P C.S true
  · -- Case 1: both sides have at least 10 vertices
    exact twoC (hH _ _ GA (vA ▸ hA10) m2) (IH _ _ GB (by omega) (by omega)) (fun _ => IH _ _ GDA (by omega) (by omega))
      (fun _ => IH _ _ GDB (by omega) (by omega))
  by_cases hB10 : 10 ≤ scount P C.S false
  · -- Case 2: `|A| ∈ {4, 6, 8}`, `|B| ≥ 10`
    have CGB : EX1On C.flip.clo := IH _ _ GB (by omega) (by omega)
    have DGB : EX1On C.flip.cloD := IH _ _ GDB (by omega) (by omega)
    by_cases hCGA : EX1On C.clo
    · by_cases hr : ∃ r, P r ∧ X.Joins r C.b1 C.b2
      · by_cases hDGA : EX1On C.cloD
        · exact twoC hCGA CGB (fun _ => hDGA) (fun _ => DGB)
        · -- (2c): `|A| = 4`
          have h4 : scount P C.S true = 4 := by
            apply Classical.byContradiction
            intro h4
            have h68 : scount P C.S true = 6 ∨ scount P C.S true = 8 := by omega
            rcases h68 with h6 | h8
            · exact hDGA (hSF.s2 _ _ C hG h6)
            · exact hDGA (IH _ _ GDA (by omega) (by omega))
          rcases (hSF.s3 _ _ C hG h4).2 with hD | hE
          · exact srA hD DGB
          · exact srB hE CGB
      · exact twoC hCGA CGB (fun h => absurd h hr) (fun _ => DGB)
    · -- (2b)
      exact srA (hSF.s4 _ _ C hG (by omega) hCGA).1 DGB
  · -- Case 3: `|A| ≤ |B| ≤ 8`
    have DG6 : ∀ (D : Cut2 P), scount P D.S true = scount P C.S true ∨ scount P D.S true = scount P C.S false →
        (scount P D.S true = 6 ∨ scount P D.S true = 8) → EX1On D.cloD := by
      intro D hD h68
      rcases h68 with h6 | h8
      · exact hSF.s2 _ _ D hG h6
      · have hv := D.vcount_cloD
        exact IH _ _ (D.cloD_inG hG) (by omega) (by omega)
    have DGA : scount P C.S true ≠ 4 → EX1On C.cloD := fun h => DG6 C (Or.inl rfl) (by omega)
    have DGB : scount P C.S false ≠ 4 → EX1On C.flip.cloD := fun h =>
      DG6 C.flip (Or.inr ((sB _).2 rfl))
        (by rw [scount_flip]; show scount P C.S false = 6 ∨ scount P C.S false = 8; omega)
    by_cases hCGA : EX1On C.clo
    · by_cases hCGB : EX1On C.flip.clo
      · by_cases h3a : ((∃ r, P r ∧ X.Joins r C.b1 C.b2) → EX1On C.cloD) ∧
            ((∃ r, P r ∧ X.Joins r C.a1 C.a2) → EX1On C.flip.cloD)
        · -- (3a)
          exact twoC hCGA hCGB h3a.1 h3a.2
        · -- (3d)
          by_cases hfirst : (∃ r, P r ∧ X.Joins r C.b1 C.b2) → EX1On C.cloD
          · exfalso
            have hsecond : ¬ ((∃ r, P r ∧ X.Joins r C.a1 C.a2) → EX1On C.flip.cloD) := fun h => h3a ⟨hfirst, h⟩
            have hB4' : scount P C.S false = 4 := by
              apply Classical.byContradiction; intro h; exact hsecond (fun _ => DGB h)
            omega
          · have hA4' : scount P C.S true = 4 := by
              apply Classical.byContradiction; intro h; exact hfirst (fun _ => DGA h)
            rcases (hSF.s3 _ _ C hG hA4').2 with hD | hE
            · exact srA hD (DGB (by omega))
            · exact srB hE hCGB
      · -- (3c): side `B` is in BAD
        obtain ⟨hDB, hB6⟩ := hSF.s4 _ _ C.flip hG (by rw [scount_flip]; show scount P C.S false ≤ 8; omega) hCGB
        rw [scount_flip] at hB6
        by_cases hDGA : EX1On C.cloD
        · exact srA' hDB hDGA
        · have hA4' : scount P C.S true = 4 := by
            apply Classical.byContradiction; intro h; exact hDGA (DGA h)
          by_cases hRDA : C.RecipeD
          · exact srA hRDA (DGB (by show ¬ _ = 4; omega))
          · by_cases hB8 : scount P C.S false = 8
            · exact srB' (hSF.s5 _ _ C.flip hG ((sB 8).2 hB8) hCGB) hCGA
            · have hB6' : scount P C.S false = 6 := by show _ = 6; omega
              exact hSF.tabc _ _ C hG hA4' hB6' hCGB hDGA hRDA
    · -- (3b): side `A` is in BAD
      obtain ⟨hDA, hA6⟩ := hSF.s4 _ _ C hG (by omega) hCGA
      exact srA hDA (DGB (by omega))

end red

end RH2F

-- ===== from RH2Main.lean =====
/-
  RH2Main.lean — Theorem RH2 (fact 6bfcd4d52c94468a) in Lean 4.20 core: (H) → (II) → DMS, from part (P) of fact
  f6e8c173bef4cfa1 (`PStat`), the small-side facts of EX1-RED (`SmallFacts`) and Theorem B8 (fact 7922314679f8733d,
  `B8S`).  Builds on `DmsIILean.dms_of_I_II` (fact 974f7197c1be8069) and `RH2F.ex1red`.
-/

namespace RH2F
open MGraph DmsIILean
open Classical

/-! ## The leaf graph T(P, g) -/

/-- old vertex `v` of `X` as a vertex of the leaf graph -/
def lv {X : MGraph} (v : Fin X.n) : Fin (X.n + 2) := Fin.castAdd 2 v
/-- the new vertices `x` and `ℓ` -/
def vx (X : MGraph) : Fin (X.n + 2) := Fin.natAdd X.n ⟨0, by decide⟩
def vl (X : MGraph) : Fin (X.n + 2) := Fin.natAdd X.n ⟨1, by decide⟩

/-- the leaf graph: all old edges (the old edge `g` stays in the ambient graph but not in `leafSet`), then
    `sx`, `xt`, `xℓ` with `s, t` the ends of `g` -/
def leafG (X : MGraph) (g : Fin X.m) : MGraph where
  n := X.n + 2
  m := X.m + 3
  ends := fun e =>
    if h : e.val < X.m then (lv (X.ends ⟨e.val, h⟩).1, lv (X.ends ⟨e.val, h⟩).2)
    else if e.val = X.m then (lv (X.ends g).1, vx X)
    else if e.val = X.m + 1 then (vx X, lv (X.ends g).2)
    else (vx X, vl X)

/-- the edge set of T(P, g): the edges of `P` other than `g`, and the three new edges -/
def leafSet {X : MGraph} (P : Fin X.m → Prop) (g : Fin X.m) : Fin (leafG X g).m → Prop :=
  fun e => if h : e.val < X.m then P ⟨e.val, h⟩ ∧ (⟨e.val, h⟩ : Fin X.m) ≠ g else True

/-- Hypothesis (II) of RH2 (fact a13aecc60d13394c): for every bridgeless loopless cubic multigraph `P` and every edge
    `g` of `P`, the leaf graph T(P, g) has a star edge colouring with 6 colours -/
def II : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → BridgelessOn P → CubicOn P → ∀ g, P g →
    Colourable (leafSet P g) 6

/-- the conclusion DMS: every loopless multigraph of maximum degree at most 3 is star 6-edge-colourable -/
def DMS : Prop :=
  ∀ (G : MGraph), Subcubic G → Loopless G → ∀ P : Fin G.m → Prop, Colourable P 6

/-- the translation of (II) into the suppression form used by `dms_of_I_II` -/
def IItoDMSII : Prop := II → DMS_II

/-! ## Discharging `IItoDMSII`: the suppression configuration embeds into the leaf graph -/

section trans

/-- old edge `e` of `X` as an edge of the leaf graph -/
def oldE {X : MGraph} (g : Fin X.m) (e : Fin X.m) : Fin (leafG X g).m := ⟨e.val, by show e.val < X.m + 3; omega⟩
def newE {X : MGraph} (g : Fin X.m) (i : Nat) (hi : i < 3) : Fin (leafG X g).m := ⟨X.m + i, by show X.m + i < X.m + 3; omega⟩

theorem ends_old {X : MGraph} (g e : Fin X.m) : (leafG X g).ends (oldE g e) = (lv (X.ends e).1, lv (X.ends e).2) := by
  simp [leafG, oldE, e.isLt]
theorem ends_new0 {X : MGraph} (g : Fin X.m) : (leafG X g).ends (newE g 0 (by decide)) = (lv (X.ends g).1, vx X) := by
  simp [leafG, newE]
theorem ends_new1 {X : MGraph} (g : Fin X.m) : (leafG X g).ends (newE g 1 (by decide)) = (vx X, lv (X.ends g).2) := by
  simp [leafG, newE]; intro h; omega
theorem ends_new2 {X : MGraph} (g : Fin X.m) : (leafG X g).ends (newE g 2 (by decide)) = (vx X, vl X) := by
  simp [leafG, newE]; intro h; omega
theorem set_old {X : MGraph} (P : Fin X.m → Prop) (g e : Fin X.m) : leafSet P g (oldE g e) ↔ P e ∧ e ≠ g := by
  simp [leafSet, oldE, e.isLt]
theorem set_new {X : MGraph} (P : Fin X.m → Prop) (g : Fin X.m) (i : Nat) (hi : i < 3) : leafSet P g (newE g i hi) := by
  have h : ¬ ((newE g i hi).val < X.m) := by show ¬ (X.m + i < X.m); omega
  exact cast (dif_neg h).symm trivial

theorem lv_inj {X : MGraph} {a b : Fin X.n} (h : (lv a : Fin (X.n + 2)) = lv b) : a = b := by
  simp [lv] at h; exact Fin.ext (by simpa using congrArg Fin.val h)
theorem lv_ne_vx {X : MGraph} (a : Fin X.n) : (lv a : Fin (X.n + 2)) ≠ vx X := by
  intro h; have := congrArg Fin.val h; simp [lv, vx] at this; omega
theorem lv_ne_vl {X : MGraph} (a : Fin X.n) : (lv a : Fin (X.n + 2)) ≠ vl X := by
  intro h; have := congrArg Fin.val h; simp [lv, vl] at this; omega
theorem vx_ne_vl (X : MGraph) : vx X ≠ vl X := by
  intro h; have := congrArg Fin.val h; simp [vx, vl] at this

theorem leaf_addEdge_ends_old {G : MGraph} (u w : Fin G.n) (d : Fin G.m) :
    (addEdge G u w).ends ⟨d.val, by show d.val < G.m + 1; omega⟩ = G.ends d := by
  simp [addEdge, d.isLt]
theorem leaf_addEdge_ends_last {G : MGraph} (u w : Fin G.n) : (addEdge G u w).ends (Fin.last G.m) = (u, w) := by
  simp [addEdge]

variable {G : MGraph} {Q : Fin G.m → Prop} (S : SuppData Q)

/-- vertex map: `y ↦ x`, `l ↦ ℓ`, every other vertex to itself -/
def phiT (v : Fin G.n) : Fin (leafG (addEdge G S.u S.w) (Fin.last G.m)).n :=
  if v = S.y then vx (addEdge G S.u S.w) else if v = S.l then vl (addEdge G S.u S.w) else lv (X := addEdge G S.u S.w) v

/-- edge map: `f1 ↦ sx`, `f2 ↦ xt`, the edge `yl ↦ xℓ`, every other edge to itself -/
def psiT (d : Fin G.m) : Fin (leafG (addEdge G S.u S.w) (Fin.last G.m)).m :=
  if d = S.f1 then newE (Fin.last G.m) 0 (by decide)
  else if d = S.f2 then newE (Fin.last G.m) 1 (by decide)
  else if G.Joins d S.y S.l then newE (Fin.last G.m) 2 (by decide)
  else oldE (Fin.last G.m) ⟨d.val, by show d.val < G.m + 1; omega⟩

end trans

section trans2
variable {G : MGraph} {Q : Fin G.m → Prop} (S : SuppData Q)

theorem phiT_y : phiT S S.y = vx (addEdge G S.u S.w) := by simp [phiT]; rfl
theorem phiT_l (h : S.l ≠ S.y) : phiT S S.l = vl (addEdge G S.u S.w) := by simp [phiT, h]; rfl
theorem phiT_other {v : Fin G.n} (h1 : v ≠ S.y) (h2 : v ≠ S.l) : phiT S v = lv (X := addEdge G S.u S.w) v := by
  simp [phiT, h1, h2]
  rfl

theorem phiT_inj (a b : Fin G.n) (h : phiT S a = phiT S b) : a = b := by
  by_cases ha : a = S.y
  · by_cases hb : b = S.y
    · rw [ha, hb]
    · by_cases hbl : b = S.l
      · subst ha; subst hbl
        rw [phiT_y, phiT_l S (fun e => hb e)] at h; exact absurd h (vx_ne_vl _)
      · subst ha; rw [phiT_y, phiT_other S hb hbl] at h; exact absurd h.symm (lv_ne_vx _)
  · by_cases hal : a = S.l
    · by_cases hb : b = S.y
      · subst hal; subst hb; rw [phiT_l S ha, phiT_y] at h; exact absurd h.symm (vx_ne_vl _)
      · by_cases hbl : b = S.l
        · rw [hal, hbl]
        · subst hal; rw [phiT_l S ha, phiT_other S hb hbl] at h; exact absurd h.symm (lv_ne_vl _)
    · by_cases hb : b = S.y
      · subst hb; rw [phiT_other S ha hal, phiT_y] at h; exact absurd h (lv_ne_vx _)
      · by_cases hbl : b = S.l
        · subst hbl; rw [phiT_other S ha hal, phiT_l S hb] at h; exact absurd h (lv_ne_vl _)
        · rw [phiT_other S ha hal, phiT_other S hb hbl] at h; exact lv_inj h

theorem psiT_f1 : psiT S S.f1 = newE (Fin.last G.m) 0 (by decide) := by simp [psiT]
theorem psiT_f2 : psiT S S.f2 = newE (Fin.last G.m) 1 (by decide) := by
  unfold psiT; rw [if_neg (fun h => S.hf12 h.symm), if_pos rfl]
theorem psiT_f3 {d : Fin G.m} (h1 : d ≠ S.f1) (h2 : d ≠ S.f2) (h3 : G.Joins d S.y S.l) :
    psiT S d = newE (Fin.last G.m) 2 (by decide) := by
  unfold psiT; rw [if_neg h1, if_neg h2, if_pos h3]
theorem psiT_old {d : Fin G.m} (h1 : d ≠ S.f1) (h2 : d ≠ S.f2) (h3 : ¬ G.Joins d S.y S.l) :
    psiT S d = oldE (Fin.last G.m) ⟨d.val, by show d.val < G.m + 1; omega⟩ := by
  unfold psiT; rw [if_neg h1, if_neg h2, if_neg h3]

/-- the four cases of the edge map -/
theorem psiT_cases (d : Fin G.m) :
    (d = S.f1 ∧ psiT S d = newE (Fin.last G.m) 0 (by decide)) ∨
    (d ≠ S.f1 ∧ d = S.f2 ∧ psiT S d = newE (Fin.last G.m) 1 (by decide)) ∨
    (d ≠ S.f1 ∧ d ≠ S.f2 ∧ G.Joins d S.y S.l ∧ psiT S d = newE (Fin.last G.m) 2 (by decide)) ∨
    (d ≠ S.f1 ∧ d ≠ S.f2 ∧ ¬ G.Joins d S.y S.l ∧
      psiT S d = oldE (Fin.last G.m) ⟨d.val, by show d.val < G.m + 1; omega⟩) := by
  by_cases h1 : d = S.f1
  · exact Or.inl ⟨h1, h1 ▸ psiT_f1 S⟩
  by_cases h2 : d = S.f2
  · exact Or.inr (Or.inl ⟨h1, h2, h2 ▸ psiT_f2 S⟩)
  by_cases h3 : G.Joins d S.y S.l
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, psiT_f3 S h1 h2 h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, psiT_old S h1 h2 h3⟩))

theorem joins_of_ends {H : MGraph} {e : Fin H.m} {p q : Fin H.n} (h : H.ends e = (p, q)) : H.Joins e p q := Or.inl h
theorem joins_of_ends' {H : MGraph} {e : Fin H.m} {p q : Fin H.n} (h : H.ends e = (p, q)) : H.Joins e q p := Or.inr h

/-- an edge of `Q` that is none of `f1`, `f2`, `yl` avoids `y` and `l` -/
theorem other_avoid {d : Fin G.m} (hQ : Q d) (h1 : d ≠ S.f1) (h2 : d ≠ S.f2) (h3 : ¬ G.Joins d S.y S.l)
    {v : Fin G.n} (hv : G.Inc d v) : v ≠ S.y ∧ v ≠ S.l := by
  constructor
  · rintro rfl
    rcases S.hy d hQ hv with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  · rintro rfl
    rcases S.hlleaf with h | h
    · rcases S.hy d hQ (h ▸ hv) with h' | h' | h'
      · exact h1 h'
      · exact h2 h'
      · exact h3 h'
    · exact h3 (h d hQ hv)

theorem l_ne_y_of (hloop : Loopless G) {d : Fin G.m} (h3 : G.Joins d S.y S.l) : S.l ≠ S.y := by
  intro h; exact ne_of_joins hloop h3 h.symm

theorem psiT_joins (hloop : Loopless G) (a : Fin G.m) (hQa : Q a) :
    (leafG (addEdge G S.u S.w) (Fin.last G.m)).Joins (psiT S a) (phiT S (G.ends a).1) (phiT S (G.ends a).2) := by
  have hlast := leaf_addEdge_ends_last (G := G) S.u S.w
  have hyu := S.y_ne_u hloop
  have hyw := S.y_ne_w hloop
  rcases psiT_cases S a with ⟨h1, hp⟩ | ⟨_, h2, hp⟩ | ⟨h1, h2, h3, hp⟩ | ⟨h1, h2, h3, hp⟩
  · subst h1
    rw [hp]
    have e0 := ends_new0 (X := addEdge G S.u S.w) (Fin.last G.m)
    rw [hlast] at e0
    have pu : phiT S S.u = lv (X := addEdge G S.u S.w) S.u :=
      phiT_other S (fun h => hyu h.symm) (fun h => S.hlu h.symm)
    rcases S.hf1 with h | h
    · rw [h]; simp only; rw [phiT_y, pu]; exact joins_of_ends' e0
    · rw [h]; simp only; rw [phiT_y, pu]; exact joins_of_ends e0
  · subst h2
    rw [hp]
    have e1 := ends_new1 (X := addEdge G S.u S.w) (Fin.last G.m)
    rw [hlast] at e1
    have pw : phiT S S.w = lv (X := addEdge G S.u S.w) S.w :=
      phiT_other S (fun h => hyw h.symm) (fun h => S.hlw h.symm)
    rcases S.hf2 with h | h
    · rw [h]; simp only; rw [phiT_y, pw]; exact joins_of_ends e1
    · rw [h]; simp only; rw [phiT_y, pw]; exact joins_of_ends' e1
  · rw [hp]
    have e2 := ends_new2 (X := addEdge G S.u S.w) (Fin.last G.m)
    have hly := l_ne_y_of S hloop h3
    rcases h3 with h | h
    · rw [h]; simp only; rw [phiT_y, phiT_l S hly]; exact joins_of_ends e2
    · rw [h]; simp only; rw [phiT_y, phiT_l S hly]; exact joins_of_ends' e2
  · rw [hp]
    have eo := ends_old (X := addEdge G S.u S.w) (Fin.last G.m) ⟨a.val, by show a.val < G.m + 1; omega⟩
    rw [leaf_addEdge_ends_old] at eo
    have hA := other_avoid S hQa h1 h2 h3 (Or.inl rfl)
    have hB := other_avoid S hQa h1 h2 h3 (Or.inr rfl)
    rw [phiT_other S hA.1 hA.2, phiT_other S hB.1 hB.2]
    exact joins_of_ends eo

theorem psiT_set (a : Fin G.m) (hQa : Q a) :
    leafSet (supp Q S.y S.u S.w) (Fin.last G.m) (psiT S a) := by
  rcases psiT_cases S a with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, _, _, hp⟩ | ⟨h1, h2, h3, hp⟩
  · rw [hp]; exact set_new _ _ _ _
  · rw [hp]; exact set_new _ _ _ _
  · rw [hp]; exact set_new _ _ _ _
  · rw [hp]; refine (set_old _ _ _).mpr ?_
    refine ⟨Or.inr ⟨a, Fin.ext rfl, hQa, fun hy => ?_⟩, ?_⟩
    · rcases S.hy a hQa hy with h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
    · intro h; have := congrArg Fin.val h; simp at this; omega

theorem psiT_inj (a b : Fin G.m) (hQa : Q a) (hQb : Q b) (h : psiT S a = psiT S b) : a = b := by
  have hv := congrArg Fin.val h
  rcases psiT_cases S a with ⟨ha1, hpa⟩ | ⟨ha1, ha2, hpa⟩ | ⟨ha1, ha2, ha3, hpa⟩ | ⟨ha1, ha2, ha3, hpa⟩ <;>
  rcases psiT_cases S b with ⟨hb1, hpb⟩ | ⟨hb1, hb2, hpb⟩ | ⟨hb1, hb2, hb3, hpb⟩ | ⟨hb1, hb2, hb3, hpb⟩ <;>
  rw [hpa, hpb] at hv <;> simp [newE, oldE] at hv
  all_goals first
    | exact ha1.trans hb1.symm
    | exact ha2.trans hb2.symm
    | exact (S.hl a b hQa ha3 hQb (joins_inc_right hb3)).symm
    | exact Fin.ext hv
    | (have hm : (addEdge G S.u S.w).m = G.m + 1 := rfl
       have := a.isLt; have := b.isLt; omega)

end trans2

/-- **(II) implies the suppression form `DMS_II`.** The configuration `Q` (edges `f1 = yu`, `f2 = yw`, possibly a
    pendant `yl`, all other edges of degree-3 vertices) embeds into the leaf graph T(supp Q y u w, g) with g the new
    edge `uw`; a star 6-colouring of the leaf graph given by (II) pulls back along the embedding. -/
theorem iiToDMSII : IItoDMSII := by
  intro hII G Q S _ hloop huw _ hB hK _
  have hXl : Loopless (addEdge G S.u S.w) := by
    intro f
    by_cases h : f.val < G.m
    · have := hloop ⟨f.val, h⟩
      simpa [addEdge, h] using this
    · simp [addEdge, h]; exact huw
  obtain ⟨c', hc'⟩ := hII (addEdge G S.u S.w) (supp Q S.y S.u S.w) hXl hB hK (Fin.last G.m) (Or.inl rfl)
  exact ⟨fun a => c' (psiT S a), starOn_embed (phiT S) (psiT S)
    (fun x y _ _ _ _ _ _ h => phiT_inj S x y h) (fun a b ha hb h => psiT_inj S a b ha hb h)
    (fun a ha => psiT_set S a ha) (fun a ha => psiT_joins S hloop a ha) hc'⟩

/-- Theorem B8 (fact 7922314679f8733d): every connected bridgeless loopless cubic multigraph on at most 8 vertices is
    star 6-edge-colourable -/
def B8S : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P ≤ 8 → Colourable P 6

/-- (I) from (H): the part `DMS_I` of `dms_of_I_II` -/
theorem dmsI_of_parts (hPS : PStat) (hSF : SmallFacts) (hB8 : B8S) (hH : Hyp) : DMS_I := by
  intro X P hL hC hB hK _
  have hG : InG X P := ⟨hL, hC, hB, hK⟩
  by_cases h10 : 10 ≤ vcount P
  · have hex := ex1red hPS hSF hH X P hG h10
    by_cases hne : ∃ g, P g
    · obtain ⟨g, hg⟩ := hne
      obtain ⟨_, _, _, c, hc, _⟩ := hex g hg true (hPS X P hG g hg true)
      exact ⟨c, hc⟩
    · exact ⟨fun _ => 0, fun a _ _ ha _ => absurd ⟨a, ha⟩ hne, fun w h1 _ _ _ => absurd ⟨w.e1, h1⟩ hne⟩
  · have hev := vcount_even hPS hG
    exact hB8 X P hG (by omega)

/-- **Theorem RH2** (fact 6bfcd4d52c94468a), with part (P) of fact f6e8c173bef4cfa1, the small-side facts of EX1-RED
    and Theorem B8 as named hypotheses: (H) and (II) imply DMS. -/
theorem rh2 (hPS : PStat) (hSF : SmallFacts) (hB8 : B8S) : Hyp → II → DMS :=
  fun hH hII => dms_of_I_II (dmsI_of_parts hPS hSF hB8 hH) (iiToDMSII hII)

end RH2F

namespace RH2F
open MGraph

/-- **Layer 4 of the Lean formalization of RH2**: Theorem EX1-RED (fact 0e90cbc9a9e79513) and Theorem RH2 (fact
    6bfcd4d52c94468a), with part (P) of fact f6e8c173bef4cfa1 (`PStat`), the small-side facts of EX1-RED
    (`SmallFacts`) and Theorem B8 (fact 7922314679f8733d, `B8S`) as named hypotheses. -/
theorem layer4 :
    (PStat → SmallFacts → Hyp → ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → EX1On P) ∧
    (PStat → SmallFacts → B8S → Hyp → II → DMS) :=
  ⟨fun hPS hSF hH => ex1red hPS hSF hH, fun hPS hSF hB8 => rh2 hPS hSF hB8⟩

end RH2F
