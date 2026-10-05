/-
  BlockStar.lean — star edge colourings of cyclic block graphs (Lean 4.33.1 + Mathlib v4.33.1, on top of `StarCore`).

  A *cyclic block graph* `BG Wr n ω` has `n` blocks `0, …, n-1` (indices modulo `n`), `r` vertices and `q` edges
  per block:
    vertex `(J, t)`  (block `J < n`, type `t < r`)        has number `J * r + t`   in `Fin (n * r)`,
    edge   `(J, s)`  (block `J < n`, edge type `s < q`)   has number `J * q + s`   in `Fin (n * q)`,
  and edge `(J, s)` joins  `(J, src w s)`  to  `((J + jmp w s) mod n, dst w s)`,  where `w = ω J` is the
  wiring kind of block `J`.

  A colouring is given block-wise: edge `(J, s)` gets colour `ct (χ J) s`, where `χ J` is the colour pattern
  of block `J`.

  Main theorem `star_of_windows`: if for every window of `3 D + 1` cyclically consecutive blocks the Boolean
  check `winOK` succeeds (`D` bounds the jumps), then the colouring is a star edge colouring (`MGraph.Star`).
  `winOK` checks, in the window (read as a piece of the *line* of blocks), every vertex `v` of the block at
  position `2 D`:  any two edges `e2 ≠ e3` at `v` have different colours, and there are no edges `e1` at the
  other end of `e2` and `e4` at the other end of `e3` with `c e1 = c e3` and `c e4 = c e2`.
  This is a sufficient condition for all `n ≥ 1` (no assumption that the blocks of a window are distinct).
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import StarCore

namespace BlockStar

/-- wiring template: for a wiring kind `w` and an edge type `s`, the edge `(J, s)` of a block `J` of kind `w`
    joins `(J, src w s)` to `(J + jmp w s, dst w s)` -/
structure Wir (W : Type) (r q : Nat) where
  D : Nat
  src : W → Nat → Nat
  jmp : W → Nat → Nat
  dst : W → Nat → Nat
  hsrc : ∀ w s, src w s < r
  hdst : ∀ w s, dst w s < r
  hjmp : ∀ w s, jmp w s ≤ D
  /-- the list of all jump values (only used to shorten the window check) -/
  jumps : List Nat
  hjmps : ∀ w s, jmp w s ∈ jumps

variable {W C : Type} {r q : Nat}

theorem blk_lt {n q : Nat} (e : Fin (n * q)) : e.val / q < n :=
  Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq e.isLt (Nat.mul_comm n q))

theorem vtx_lt {n r J t : Nat} (hJ : J < n) (ht : t < r) : J * r + t < n * r := by
  have h : J * r + r ≤ n * r := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right r hJ
  omega

theorem npos {n q : Nat} (e : Fin (n * q)) : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (blk_lt e)

/-- the cyclic block graph -/
def BG (Wr : Wir W r q) (n : Nat) (ω : Nat → W) : MGraph where
  n := n * r
  m := n * q
  ends e :=
    (⟨(e.val / q) * r + Wr.src (ω (e.val / q)) (e.val % q), vtx_lt (blk_lt e) (Wr.hsrc _ _)⟩,
     ⟨((e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n) * r + Wr.dst (ω (e.val / q)) (e.val % q),
        vtx_lt (Nat.mod_lt _ (npos e)) (Wr.hdst _ _)⟩)

/-- the block-wise colouring: edge `(J, s)` gets colour `ct (χ J) s` -/
def bcol (q : Nat) (ct : C → Nat → Nat) {k : Nat} (hct : ∀ c s, ct c s < k) (χ : Nat → C) {m : Nat} :
    Fin m → Fin k := fun e => ⟨ct (χ (e.val / q)) (e.val % q), hct _ _⟩

/-- bounded universal quantifier, as a Boolean -/
def allB : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | m+1, f => f m && allB m f

theorem allB_spec {m : Nat} {f : Nat → Bool} (h : allB m f = true) : ∀ i, i < m → f i = true := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    simp only [allB, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · exact ih h.2 i h'
    · rw [h']; exact h.1

section Check
variable (Wr : Wir W r q) (ct : C → Nat → Nat) (wk : Nat → W) (ck : Nat → C)

/-- in the window: the edge `(o, s)` (owner position `o`) has its head (`hd = true`) resp. its tail
    (`hd = false`) at the vertex `(p, t)` -/
def atB (o s : Nat) (hd : Bool) (p t : Nat) : Bool :=
  bif hd then (o + Wr.jmp (wk o) s == p && Wr.dst (wk o) s == t) else (o == p && Wr.src (wk o) s == t)

/-- position of the other end -/
def othP (o s : Nat) (hd : Bool) : Nat := bif hd then o else o + Wr.jmp (wk o) s
/-- type of the other end -/
def othT (o s : Nat) (hd : Bool) : Nat := bif hd then Wr.src (wk o) s else Wr.dst (wk o) s

/-- `f` holds for all half-edges at the vertex `(p, t)` of the window -/
def allHE (p t : Nat) (f : Nat → Nat → Bool → Bool) : Bool :=
  allB q fun s =>
    (bif atB Wr wk p s false p t then f p s false else true) &&
    Wr.jumps.all fun d =>
      bif decide (d ≤ p) then (bif atB Wr wk (p - d) s true p t then f (p - d) s true else true) else true

/-- the window check -/
def winOK : Bool :=
  allB r fun t =>
    allHE Wr wk (2 * Wr.D) t fun o2 s2 h2 =>
      allHE Wr wk (2 * Wr.D) t fun o3 s3 h3 =>
        (o2 == o3 && s2 == s3) ||
        ((ct (ck o2) s2 != ct (ck o3) s3) &&
          allHE Wr wk (othP Wr wk o2 s2 h2) (othT Wr wk o2 s2 h2) fun o1 s1 _ =>
            (ct (ck o1) s1 != ct (ck o3) s3) ||
            allHE Wr wk (othP Wr wk o3 s3 h3) (othT Wr wk o3 s3 h3) fun o4 s4 _ =>
              ct (ck o4) s4 != ct (ck o2) s2)

theorem allHE_spec {p t : Nat} {f : Nat → Nat → Bool → Bool} (h : allHE Wr wk p t f = true)
    {s : Nat} (hs : s < q) {o : Nat} {hd : Bool}
    (hm : (hd = false ∧ o = p) ∨ (hd = true ∧ o ≤ p ∧ p - o ∈ Wr.jumps))
    (hat : atB Wr wk o s hd p t = true) : f o s hd = true := by
  have h1 := allB_spec h s hs
  simp only [Bool.and_eq_true] at h1
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, ho, hD⟩
  · have h2 := h1.1
    rw [hat] at h2
    exact h2
  · have h3 := List.all_eq_true.mp h1.2 (p - o) hD
    have e1 : p - (p - o) = o := by omega
    have e2 : decide (p - o ≤ p) = true := decide_eq_true (by omega)
    simp only [e1, e2] at h3
    rw [hat] at h3
    exact h3

end Check

theorem dm {J t r : Nat} (ht : t < r) : (J * r + t) / r = J ∧ (J * r + t) % r = t := by
  have hr : 0 < r := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem mod_cancel {n a a' d : Nat} (ha : a < n) (ha' : a' < n) (h : (a + d) % n = (a' + d) % n) : a = a' := by
  have h1 : a ≡ a' [MOD n] := Nat.ModEq.add_right_cancel' d h
  unfold Nat.ModEq at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1

theorem edge_ext {m q : Nat} {a b : Fin m} (h1 : a.val / q = b.val / q) (h2 : a.val % q = b.val % q) : a = b := by
  apply Fin.ext
  rw [← Nat.div_add_mod a.val q, ← Nat.div_add_mod b.val q, h1, h2]

section Lift
variable (Wr : Wir W r q) (n : Nat) (ω : Nat → W) (b : Nat → Nat) (wk : Nat → W)

/-- an edge `e` joining `x` and `y`, with `y` in the block at window position `p`, read in the window -/
theorem liftJ (hb : ∀ p, b p < n) (hs : ∀ p d, (b p + d) % n = b (p + d))
    (e : Fin (BG Wr n ω).m) (x y : Fin (BG Wr n ω).n) (hj : (BG Wr n ω).Joins e x y)
    (p : Nat) (hp : Wr.D ≤ p) (hwk : ∀ o, o ≤ p → wk o = ω (b o)) (hy : y.val / r = b p) :
    ∃ o hd, ((hd = false ∧ o = p) ∨ (hd = true ∧ o ≤ p ∧ p - o ∈ Wr.jumps)) ∧
      atB Wr wk o (e.val % q) hd p (y.val % r) = true ∧ e.val / q = b o ∧
      x.val / r = b (othP Wr wk o (e.val % q) hd) ∧ x.val % r = othT Wr wk o (e.val % q) hd ∧
      p ≤ othP Wr wk o (e.val % q) hd + Wr.D ∧ othP Wr wk o (e.val % q) hd ≤ p + Wr.D := by
  have ht : ((BG Wr n ω).ends e).1.val = (e.val / q) * r + Wr.src (ω (e.val / q)) (e.val % q) := rfl
  have hh : ((BG Wr n ω).ends e).2.val =
      ((e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n) * r + Wr.dst (ω (e.val / q)) (e.val % q) := rfl
  have dt := dm (J := e.val / q) (Wr.hsrc (ω (e.val / q)) (e.val % q))
  have dh := dm (J := (e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n)
    (Wr.hdst (ω (e.val / q)) (e.val % q))
  have hJ : e.val / q < n := blk_lt e
  have hjm := Wr.hjmp (ω (e.val / q)) (e.val % q)
  rcases hj with h | h
  · -- x is the tail, y the head
    have hx : x.val = (e.val / q) * r + Wr.src (ω (e.val / q)) (e.val % q) := by
      rw [← ht, h]
    have hyv : y.val =
        ((e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n) * r + Wr.dst (ω (e.val / q)) (e.val % q) := by
      rw [← hh, h]
    have hyb : (e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n = b p := by
      rw [← hy, hyv]; exact dh.1.symm
    have hyt : y.val % r = Wr.dst (ω (e.val / q)) (e.val % q) := by rw [hyv]; exact dh.2
    have hxb : x.val / r = e.val / q := by rw [hx]; exact dt.1
    have hxt : x.val % r = Wr.src (ω (e.val / q)) (e.val % q) := by rw [hx]; exact dt.2
    have ho : p - Wr.jmp (ω (e.val / q)) (e.val % q) + Wr.jmp (ω (e.val / q)) (e.val % q) = p := by omega
    have hJo : e.val / q = b (p - Wr.jmp (ω (e.val / q)) (e.val % q)) := by
      apply mod_cancel (d := Wr.jmp (ω (e.val / q)) (e.val % q)) hJ (hb _)
      rw [hyb, hs, ho]
    have hw : wk (p - Wr.jmp (ω (e.val / q)) (e.val % q)) = ω (e.val / q) := by
      rw [hwk _ (by omega), ← hJo]
    have hmem : p - (p - Wr.jmp (ω (e.val / q)) (e.val % q)) ∈ Wr.jumps := by
      rw [show p - (p - Wr.jmp (ω (e.val / q)) (e.val % q)) = Wr.jmp (ω (e.val / q)) (e.val % q) by omega]
      exact Wr.hjmps _ _
    refine ⟨p - Wr.jmp (ω (e.val / q)) (e.val % q), true, Or.inr ⟨rfl, by omega, hmem⟩, ?_, hJo, ?_, ?_, ?_, ?_⟩
    · simp only [atB, cond_true, hw, ho, hyt, beq_self_eq_true, Bool.and_self]
    · simp only [othP, cond_true]; rw [hxb]; exact hJo
    · simp only [othT, cond_true, hw]; exact hxt
    · simp only [othP, cond_true]; omega
    · simp only [othP, cond_true]; omega
  · -- y is the tail, x the head
    have hyv : y.val = (e.val / q) * r + Wr.src (ω (e.val / q)) (e.val % q) := by
      rw [← ht, h]
    have hx : x.val =
        ((e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n) * r + Wr.dst (ω (e.val / q)) (e.val % q) := by
      rw [← hh, h]
    have hyb : e.val / q = b p := by rw [← hy, hyv]; exact dt.1.symm
    have hyt : y.val % r = Wr.src (ω (e.val / q)) (e.val % q) := by rw [hyv]; exact dt.2
    have hxb : x.val / r = (e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n := by rw [hx]; exact dh.1
    have hxt : x.val % r = Wr.dst (ω (e.val / q)) (e.val % q) := by rw [hx]; exact dh.2
    have hw : wk p = ω (e.val / q) := by rw [hwk _ (Nat.le_refl _), ← hyb]
    refine ⟨p, false, Or.inl ⟨rfl, rfl⟩, ?_, hyb, ?_, ?_, ?_, ?_⟩
    · simp only [atB, cond_false, hw, hyt, beq_self_eq_true, Bool.and_self]
    · simp only [othP, cond_false, hw]; rw [hxb, hyb, hs]
    · simp only [othT, cond_false, hw]; exact hxt
    · simp only [othP, cond_false]; omega
    · simp only [othP, cond_false, hw]; omega

/-- an edge `e` incident with `x`, with `x` in the block at window position `p`, read in the window -/
theorem liftI (hb : ∀ p, b p < n) (hs : ∀ p d, (b p + d) % n = b (p + d))
    (e : Fin (BG Wr n ω).m) (x : Fin (BG Wr n ω).n) (hi : (BG Wr n ω).Inc e x)
    (p : Nat) (hp : Wr.D ≤ p) (hwk : ∀ o, o ≤ p → wk o = ω (b o)) (hx : x.val / r = b p) :
    ∃ o hd, ((hd = false ∧ o = p) ∨ (hd = true ∧ o ≤ p ∧ p - o ∈ Wr.jumps)) ∧
      atB Wr wk o (e.val % q) hd p (x.val % r) = true ∧ e.val / q = b o := by
  have hj : ∃ z, (BG Wr n ω).Joins e z x := by
    rcases hi with h | h
    · exact ⟨((BG Wr n ω).ends e).2, Or.inr (by rw [← h])⟩
    · exact ⟨((BG Wr n ω).ends e).1, Or.inl (by rw [← h])⟩
  obtain ⟨z, hz⟩ := hj
  obtain ⟨o, hd, h1, h2, h3, _⟩ := liftJ Wr n ω b wk hb hs e z x hz p hp hwk hx
  exact ⟨o, hd, h1, h2, h3⟩

end Lift

/-- **Window criterion.** If every window of `3 D + 1` cyclically consecutive blocks passes `winOK`, the
    block-wise colouring is a star edge colouring of the cyclic block graph. -/
theorem star_of_windows (Wr : Wir W r q) (ct : C → Nat → Nat) {k : Nat} (hct : ∀ c s, ct c s < k)
    (n : Nat) (ω : Nat → W) (χ : Nat → C)
    (H : ∀ j, j < n → ∃ (wk : Nat → W) (ck : Nat → C),
      (∀ p, p ≤ 3 * Wr.D → wk p = ω ((j + p) % n) ∧ ck p = χ ((j + p) % n)) ∧ winOK Wr ct wk ck = true) :
    (BG Wr n ω).Star k (bcol q ct hct χ) := by
  -- the window around a vertex
  have key : ∀ y : Fin (BG Wr n ω).n, ∃ (b : Nat → Nat) (wk : Nat → W) (ck : Nat → C),
      (∀ p, b p < n) ∧ (∀ p d, (b p + d) % n = b (p + d)) ∧ y.val / r = b (2 * Wr.D) ∧
      (∀ p, p ≤ 3 * Wr.D → wk p = ω (b p) ∧ ck p = χ (b p)) ∧ winOK Wr ct wk ck = true ∧ y.val % r < r := by
    intro y
    have hy : y.val < n * r := y.isLt
    have hJ : y.val / r < n := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hy (Nat.mul_comm n r))
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hJ
    have hr : 0 < r := Nat.pos_of_ne_zero (fun h => by
      have h2 : n * r = 0 := by simp [h]
      omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨wk, ck, hag, hok⟩ := H ((y.val / r + m * (2 * Wr.D)) % (m + 1)) (Nat.mod_lt _ hn)
    refine ⟨fun p => ((y.val / r + m * (2 * Wr.D)) % (m + 1) + p) % (m + 1), wk, ck,
      fun p => Nat.mod_lt _ hn, ?_, ?_, hag, hok, Nat.mod_lt _ hr⟩
    · intro p d
      show (((y.val / r + m * (2 * Wr.D)) % (m + 1) + p) % (m + 1) + d) % (m + 1) =
        ((y.val / r + m * (2 * Wr.D)) % (m + 1) + (p + d)) % (m + 1)
      rw [Nat.mod_add_mod, Nat.add_assoc]
    · show y.val / r = ((y.val / r + m * (2 * Wr.D)) % (m + 1) + 2 * Wr.D) % (m + 1)
      rw [Nat.mod_add_mod, Nat.add_assoc, ← Nat.succ_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJ]
  -- colour of an edge read in the window
  have hcol : ∀ (e : Fin (BG Wr n ω).m) (b : Nat → Nat) (ck : Nat → C) (o : Nat), e.val / q = b o →
      ck o = χ (b o) → (bcol q ct hct χ e).val = ct (ck o) (e.val % q) := by
    intro e b ck o h1 h2
    show ct (χ (e.val / q)) (e.val % q) = ct (ck o) (e.val % q)
    rw [h1, h2]
  have hsq : ∀ e : Fin (BG Wr n ω).m, e.val % q < q := by
    intro e
    have he : e.val < n * q := e.isLt
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by
      have h2 : n * q = 0 := by simp [h]
      omega))
  rw [MGraph.star_iff]
  constructor
  · -- properness
    intro a a' hadj hc
    obtain ⟨hne, x, hia, hia'⟩ := hadj
    obtain ⟨b, wk, ck, hb, hs, hx, hag, hok, htr⟩ := key x
    have hwk : ∀ o, o ≤ 2 * Wr.D → wk o = ω (b o) := fun o ho => (hag o (by omega)).1
    obtain ⟨o2, h2, m2, at2, q2⟩ := liftI Wr n ω b wk hb hs a x hia (2 * Wr.D) (by omega) hwk hx
    obtain ⟨o3, h3, m3, at3, q3⟩ := liftI Wr n ω b wk hb hs a' x hia' (2 * Wr.D) (by omega) hwk hx
    have ho2 : o2 ≤ 3 * Wr.D := by rcases m2 with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have ho3 : o3 ≤ 3 * Wr.D := by rcases m3 with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have c2 := hcol a b ck o2 q2 (hag o2 ho2).2
    have c3 := hcol a' b ck o3 q3 (hag o3 ho3).2
    have k1 := allB_spec hok (x.val % r) htr
    have k2 := allHE_spec Wr wk k1 (hsq a) m2 at2
    have k3 := allHE_spec Wr wk k2 (hsq a') m3 at3
    have hne' : (o2 == o3 && a.val % q == a'.val % q) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact hne (edge_ext (q := q) (by rw [q2, q3, h.1]) h.2)
    simp only [hne', Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq] at k3
    apply k3.1
    rw [← c2, ← c3, hc]
  · -- no bicoloured walk
    intro w hbic
    obtain ⟨hb13, hb24⟩ := hbic
    obtain ⟨b, wk, ck, hb, hs, hx, hag, hok, htr⟩ := key w.v2
    have hwk : ∀ P, P ≤ 3 * Wr.D → ∀ o, o ≤ P → wk o = ω (b o) := fun P hP o ho => (hag o (by omega)).1
    have hj3 : (BG Wr n ω).Joins w.e3 w.v3 w.v2 := Or.symm w.h3
    obtain ⟨o2, h2, m2, at2, q2, x1, t1, l1, u1⟩ :=
      liftJ Wr n ω b wk hb hs w.e2 w.v1 w.v2 w.h2 (2 * Wr.D) (by omega) (hwk _ (by omega)) hx
    obtain ⟨o3, h3, m3, at3, q3, x3, t3, l3, u3⟩ :=
      liftJ Wr n ω b wk hb hs w.e3 w.v3 w.v2 hj3 (2 * Wr.D) (by omega) (hwk _ (by omega)) hx
    obtain ⟨o1, h1, m1, at1, q1⟩ :=
      liftI Wr n ω b wk hb hs w.e1 w.v1 (MGraph.joins_inc_right w.h1) _ (by omega) (hwk _ (by omega)) x1
    obtain ⟨o4, h4, m4, at4, q4⟩ :=
      liftI Wr n ω b wk hb hs w.e4 w.v3 (MGraph.joins_inc_left w.h4) _ (by omega) (hwk _ (by omega)) x3
    rw [t1] at at1
    rw [t3] at at4
    have ho2 : o2 ≤ 3 * Wr.D := by rcases m2 with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have ho3 : o3 ≤ 3 * Wr.D := by rcases m3 with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have ho1 : o1 ≤ 3 * Wr.D := by rcases m1 with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have ho4 : o4 ≤ 3 * Wr.D := by rcases m4 with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have c1 := hcol w.e1 b ck o1 q1 (hag o1 ho1).2
    have c2 := hcol w.e2 b ck o2 q2 (hag o2 ho2).2
    have c3 := hcol w.e3 b ck o3 q3 (hag o3 ho3).2
    have c4 := hcol w.e4 b ck o4 q4 (hag o4 ho4).2
    have k1 := allB_spec hok (w.v2.val % r) htr
    have k2 := allHE_spec Wr wk k1 (hsq w.e2) m2 at2
    have k3 := allHE_spec Wr wk k2 (hsq w.e3) m3 at3
    have hne' : (o2 == o3 && w.e2.val % q == w.e3.val % q) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact w.e2_ne_e3 (edge_ext (q := q) (by rw [q2, q3, h.1]) h.2)
    simp only [hne', Bool.false_or, Bool.and_eq_true] at k3
    have k4 := allHE_spec Wr wk k3.2 (hsq w.e1) m1 at1
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at k4
    rcases k4 with k4 | k4
    · apply k4
      rw [← c1, ← c3, hb13]
    · have k5 := allHE_spec Wr wk k4 (hsq w.e4) m4 at4
      simp only [bne_iff_ne, ne_eq] at k5
      apply k5
      rw [← c4, ← c2, hb24]

end BlockStar
