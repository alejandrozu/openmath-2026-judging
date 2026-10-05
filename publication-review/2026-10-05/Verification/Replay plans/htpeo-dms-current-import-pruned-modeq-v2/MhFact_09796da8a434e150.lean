-- Lean proof of fact 09796da8a434e150 (RH2F.layer6a); added by fact_submit, do not edit
import MhFact_643ccea3769075c0
import MhFact_046773df0a672922
import Mathlib.Algebra.BigOperators.Fin

-- ===== from TF1.lean =====

namespace RH2F
open MGraph Finset
open Classical

section tf
variable {X : MGraph} {P : Fin X.m → Prop}

/-! ### counting -/

theorem cntF_eq_card : ∀ (n : Nat) (W : Fin n → Prop), cntF n W = (univ.filter W).card
  | 0, W => by simp [cntF_zero]
  | n + 1, W => by
    rw [cntF_succ, cntF_eq_card n, card_filter, card_filter, Fin.sum_univ_castSucc]

theorem vcount_eq_card (P : Fin X.m → Prop) : vcount P = (univ.filter (meets P)).card :=
  cntF_eq_card _ _

theorem vcount_even' (hG : InG X P) : vcount P % 2 = 0 := by
  rw [vcount_eq_card]; exact RH2P.mt_even hG

/-! ### adjacency in a simple cubic edge set -/

/-- `x` and `y` are joined by an edge of `P` -/
def Adjq (P : Fin X.m → Prop) (x y : Fin X.n) : Prop := ∃ f, P f ∧ X.Joins f x y

theorem adjq_symm {x y : Fin X.n} (h : Adjq P x y) : Adjq P y x := by
  obtain ⟨f, hf, hj⟩ := h; exact ⟨f, hf, Or.symm hj⟩

theorem adjq_ne (hloop : Loopless X) {x y : Fin X.n} (h : Adjq P x y) : x ≠ y := by
  obtain ⟨f, _, hj⟩ := h; exact ne_of_joins hloop hj

theorem adjq_meets {x y : Fin X.n} (h : Adjq P x y) : meets P x := by
  obtain ⟨f, hf, hj⟩ := h; exact ⟨f, hf, joins_inc_left hj⟩

/-- no triangle -/
def TriFree (P : Fin X.m → Prop) : Prop := ∀ a b c : Fin X.n, Adjq P a b → Adjq P b c → Adjq P c a → False

/-- the three neighbours of a vertex of a simple cubic edge set -/
theorem nbrs3 (hG : InG X P) (hS : SimpleP P) {x : Fin X.n} (hx : meets P x) :
    ∃ y1 y2 y3, y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 ∧ Adjq P x y1 ∧ Adjq P x y2 ∧ Adjq P x y3 ∧
      ∀ y, Adjq P x y → y = y1 ∨ y = y2 ∨ y = y3 := by
  obtain ⟨p, q, r, hp, hq, hr, hpx, hqx, hrx, hpq, hpr, hqr, hall⟩ := hG.2.2.2 x hx
  have jp := joins_other hpx
  have jq := joins_other hqx
  have jr := joins_other hrx
  refine ⟨other p x, other q x, other r x, fun h => hpq (hS p q x _ hp hq jp (h ▸ jq)),
    fun h => hpr (hS p r x _ hp hr jp (h ▸ jr)), fun h => hqr (hS q r x _ hq hr jq (h ▸ jr)),
    ⟨p, hp, jp⟩, ⟨q, hq, jq⟩, ⟨r, hr, jr⟩, ?_⟩
  intro y ⟨f, hf, hj⟩
  have hne : x ≠ y := ne_of_joins hG.1 hj
  rcases hall f hf (joins_inc_left hj) with rfl | rfl | rfl
  · exact Or.inl (other_eq hj hne).symm
  · exact Or.inr (Or.inl (other_eq hj hne).symm)
  · exact Or.inr (Or.inr (other_eq hj hne).symm)

/-- the two neighbours of `x` other than a given neighbour `a` -/
theorem nbrs_other (hG : InG X P) (hS : SimpleP P) {x a : Fin X.n} (ha : Adjq P x a) :
    ∃ z1 z2, z1 ≠ z2 ∧ z1 ≠ a ∧ z2 ≠ a ∧ Adjq P x z1 ∧ Adjq P x z2 ∧
      ∀ y, Adjq P x y → y = a ∨ y = z1 ∨ y = z2 := by
  obtain ⟨y1, y2, y3, h12, h13, h23, a1, a2, a3, hall⟩ := nbrs3 hG hS (adjq_meets ha)
  rcases hall a ha with rfl | rfl | rfl
  · refine ⟨y2, y3, h23, fun h => h12 h.symm, fun h => h13 h.symm, a2, a3, fun y hy => ?_⟩
    rcases hall y hy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · refine ⟨y1, y3, h13, h12, fun h => h23 h.symm, a1, a3, fun y hy => ?_⟩
    rcases hall y hy with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · refine ⟨y1, y2, h12, h13, h23, a1, a2, fun y hy => ?_⟩
    rcases hall y hy with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-! ### from an adjacency correspondence to an isomorphism -/

/-- `H` is simple -/
def SimpleH (H : MGraph) : Prop := ∀ e e' p q, H.Joins e p q → H.Joins e' p q → e = e'

/-- an isomorphism from a simple `P` onto a simple concrete `H`, given by a vertex enumeration `φ` of `P` and a
    permutation `π` under which adjacency corresponds -/
theorem isoFrom_of_adj (_hG : InG X P) (hS : SimpleP P) {H : MGraph} (hH : SimpleH H) (hm : 0 < H.m)
    (φ : Fin H.n → Fin X.n) (hφi : ∀ i j, φ i = φ j → i = j) (hφs : ∀ x, meets P x → ∃ i, φ i = x)
    (π : Fin H.n → Fin H.n) (hπ : ∀ i j, π i = π j → i = j)
    (hadj : ∀ i j, Adjq P (φ i) (φ j) ↔ ∃ e, H.Joins e (π i) (π j)) : IsoFrom P H := by
  have hπs : ∀ p, ∃ i, π i = p := by
    have : Function.Surjective π := Finite.surjective_of_injective (fun i j h => hπ i j h)
    exact this
  -- vertex map
  let α : Fin X.n → Fin H.n := fun x => if h : ∃ i, φ i = x then π (Classical.choose h) else π ⟨0, by
    obtain ⟨p, _⟩ := hπs ⟨0, by
      have := (H.ends ⟨0, hm⟩).1.isLt; omega⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (H.ends ⟨0, hm⟩).1.isLt⟩
  have hα : ∀ i, α (φ i) = π i := by
    intro i
    have h : ∃ j, φ j = φ i := ⟨i, rfl⟩
    simp only [α, dif_pos h]
    rw [hφi _ _ (Classical.choose_spec h)]
  -- edge map
  let β : Fin X.m → Fin H.m := fun f =>
    if h : ∃ e, H.Joins e (α (X.ends f).1) (α (X.ends f).2) then Classical.choose h else ⟨0, hm⟩
  have hβ : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2) := by
    intro f hf
    obtain ⟨i, hi⟩ := hφs _ ⟨f, hf, Or.inl rfl⟩
    obtain ⟨j, hj⟩ := hφs _ ⟨f, hf, Or.inr rfl⟩
    have hex : ∃ e, H.Joins e (α (X.ends f).1) (α (X.ends f).2) := by
      rw [← hi, ← hj, hα, hα]
      exact (hadj i j).1 ⟨f, hf, by rw [hi, hj]; exact joins_ends f⟩
    simp only [β, dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨α, β, ?_, ?_, ?_, hβ⟩
  · intro x y hx hy hxy
    obtain ⟨i, rfl⟩ := hφs x hx
    obtain ⟨j, rfl⟩ := hφs y hy
    rw [hα, hα] at hxy
    rw [hπ _ _ hxy]
  · intro f g hf hg hfg
    have jf := hβ f hf
    have jg := hβ g hg
    rw [hfg] at jf
    -- the ends of `f` and `g` have the same images, so they are the same pairs
    obtain ⟨i1, hi1⟩ := hφs _ ⟨f, hf, Or.inl rfl⟩
    obtain ⟨j1, hj1⟩ := hφs _ ⟨f, hf, Or.inr rfl⟩
    obtain ⟨i2, hi2⟩ := hφs _ ⟨g, hg, Or.inl rfl⟩
    obtain ⟨j2, hj2⟩ := hφs _ ⟨g, hg, Or.inr rfl⟩
    rw [← hi1, ← hj1, hα, hα] at jf
    rw [← hi2, ← hj2, hα, hα] at jg
    have key : (φ i1 = φ i2 ∧ φ j1 = φ j2) ∨ (φ i1 = φ j2 ∧ φ j1 = φ i2) := by
      rcases jf with h1 | h1 <;> rcases jg with h2 | h2 <;> rw [h1] at h2 <;>
        simp only [Prod.mk.injEq] at h2 <;> obtain ⟨e1, e2⟩ := h2
      · exact Or.inl ⟨congrArg φ (hπ _ _ e1), congrArg φ (hπ _ _ e2)⟩
      · exact Or.inr ⟨congrArg φ (hπ _ _ e1), congrArg φ (hπ _ _ e2)⟩
      · exact Or.inr ⟨congrArg φ (hπ _ _ e2), congrArg φ (hπ _ _ e1)⟩
      · exact Or.inl ⟨congrArg φ (hπ _ _ e2), congrArg φ (hπ _ _ e1)⟩
    rw [hi1, hj1, hi2, hj2] at key
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact hS f g _ _ hf hg (joins_ends f) (by rw [k1, k2]; exact joins_ends g)
    · exact hS f g _ _ hf hg (joins_ends f) (by rw [k1, k2]; exact Or.symm (joins_ends g))
  · intro e
    obtain ⟨i, hi⟩ := hπs (H.ends e).1
    obtain ⟨j, hj⟩ := hπs (H.ends e).2
    obtain ⟨f, hf, hjf⟩ := (hadj i j).2 ⟨e, by rw [hi, hj]; exact Or.inl rfl⟩
    refine ⟨f, hf, ?_⟩
    have h1 := hβ f hf
    have h2 : H.Joins e (α (φ i)) (α (φ j)) := by rw [hα, hα, hi, hj]; exact Or.inl rfl
    rcases hjf with h | h <;> rw [h] at h1
    · exact hH _ _ _ _ h1 h2
    · exact hH _ _ _ _ (Or.symm h1) h2

end tf

end RH2F


-- ===== from TF2.lean =====

namespace RH2F
open MGraph Finset
open Classical

/-! ### Bool checkers for Lemma 4 of fact 7922314679f8733d (simple triangle-free members of 𝒢 on 6 or 8 vertices) -/

def forallB (f : Bool → Bool) : Bool := f true && f false

theorem forallB_sound {f : Bool → Bool} (h : forallB f = true) : ∀ b, f b = true := by
  intro b; unfold forallB at h; simp only [Bool.and_eq_true] at h; cases b
  · exact h.2
  · exact h.1

/-- the number of `true` entries -/
def cntB : List Bool → Nat
  | [] => 0
  | b :: bs => cond b (cntB bs + 1) (cntB bs)

/-- entry `(i, j)` of a matrix given by its rows -/
def getB (M : List (List Bool)) (i j : Nat) : Bool := (M.getD i []).getD j false

def xnor (a b : Bool) : Bool := cond a b (!b)

def eqL : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => xnor a b && eqL as bs
  | _, _ => false

def eqLL : List (List Bool) → List (List Bool) → Bool
  | [], [] => true
  | a :: as, b :: bs => eqL a b && eqLL as bs
  | _, _ => false

/-- every row has exactly three `true` entries -/
def rowsOK (M : List (List Bool)) : Bool := M.all (fun r => cntB r == 3)

/-- no triangle among the listed triples -/
def triOK (T : List (Nat × Nat × Nat)) (M : List (List Bool)) : Bool :=
  T.all (fun t => !(getB M t.1 t.2.1 && getB M t.2.1 t.2.2 && getB M t.1 t.2.2))

/-- adjacency in an edge list -/
def adjN (el : List (Nat × Nat)) (p q : Nat) : Bool :=
  el.any (fun e => (e.1 == p && e.2 == q) || (e.1 == q && e.2 == p))

/-- `π` (a list) is an injective map `[0, n) → [0, n)` -/
def permOK (n : Nat) (π : List Nat) : Bool :=
  (List.range n).all (fun i => π.getD i 0 < n) &&
  (List.range n).all (fun i => (List.range n).all (fun j => !(π.getD i 0 == π.getD j 0) || i == j))

/-- each table entry `(k, π, B)`: `B` is the adjacency matrix of `Rep k` pulled back along `π` -/
def pbOK (n : Nat) (tab : List (Nat × List Nat × List (List Bool))) : Bool :=
  tab.all (fun t => repN t.1 == n && permOK n t.2.1 &&
    (repL t.1).all (fun e => e.1 < n && e.2 < n) &&
    (List.range n).all (fun i => (List.range n).all (fun j =>
      getB t.2.2 i j == adjN (repL t.1) (t.2.1.getD i 0) (t.2.1.getD j 0))))

def mat8 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : List (List Bool) :=
  [[false, true, true, true, false, false, false, false],
   [true, false, false, false, true, true, false, false],
   [true, false, false, false, b0, b1, b2, b3],
   [true, false, false, false, b4, b5, b6, b7],
   [false, true, b0, b4, false, b8, b9, b10],
   [false, true, b1, b5, b8, false, b11, b12],
   [false, false, b2, b6, b9, b11, false, b13],
   [false, false, b3, b7, b10, b12, b13, false]]

def PB8 : List (Nat × List Nat × List (List Bool)) := [(24, [0, 1, 2, 3, 6, 7, 4, 5], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, true, false, true], [true, false, false, false, true, false, false, true], [false, true, false, true, false, false, true, false], [false, true, true, false, false, false, true, false], [false, false, false, false, true, true, false, true], [false, false, true, true, false, false, true, false]]),
  (24, [0, 1, 2, 3, 6, 7, 5, 4], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, true, true, false], [true, false, false, false, true, false, true, false], [false, true, false, true, false, false, false, true], [false, true, true, false, false, false, false, true], [false, false, true, true, false, false, false, true], [false, false, false, false, true, true, true, false]]),
  (24, [0, 1, 2, 3, 7, 6, 4, 5], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, true, false, false, true], [true, false, false, false, false, true, false, true], [false, true, true, false, false, false, true, false], [false, true, false, true, false, false, true, false], [false, false, false, false, true, true, false, true], [false, false, true, true, false, false, true, false]]),
  (24, [0, 1, 2, 3, 7, 6, 5, 4], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, true, false, true, false], [true, false, false, false, false, true, true, false], [false, true, true, false, false, false, false, true], [false, true, false, true, false, false, false, true], [false, false, true, true, false, false, false, true], [false, false, false, false, true, true, true, false]]),
  (25, [0, 1, 2, 3, 5, 7, 4, 6], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, false, true, true], [true, false, false, false, false, true, true, false], [false, true, false, false, false, false, true, true], [false, true, false, true, false, false, false, true], [false, false, true, true, true, false, false, false], [false, false, true, false, true, true, false, false]]),
  (25, [0, 1, 2, 3, 5, 7, 6, 4], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, false, true, true], [true, false, false, false, false, true, false, true], [false, true, false, false, false, false, true, true], [false, true, false, true, false, false, true, false], [false, false, true, false, true, true, false, false], [false, false, true, true, true, false, false, false]]),
  (25, [0, 1, 2, 3, 7, 5, 4, 6], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, false, true, true], [true, false, false, false, true, false, true, false], [false, true, false, true, false, false, false, true], [false, true, false, false, false, false, true, true], [false, false, true, true, false, true, false, false], [false, false, true, false, true, true, false, false]]),
  (25, [0, 1, 2, 3, 7, 5, 6, 4], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, false, true, true], [true, false, false, false, true, false, false, true], [false, true, false, true, false, false, true, false], [false, true, false, false, false, false, true, true], [false, false, true, false, true, true, false, false], [false, false, true, true, false, true, false, false]]),
  (25, [0, 1, 3, 2, 5, 7, 4, 6], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, true, true, false], [true, false, false, false, false, false, true, true], [false, true, false, false, false, false, true, true], [false, true, true, false, false, false, false, true], [false, false, true, true, true, false, false, false], [false, false, false, true, true, true, false, false]]),
  (25, [0, 1, 3, 2, 5, 7, 6, 4], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, true, false, true], [true, false, false, false, false, false, true, true], [false, true, false, false, false, false, true, true], [false, true, true, false, false, false, true, false], [false, false, false, true, true, true, false, false], [false, false, true, true, true, false, false, false]]),
  (25, [0, 1, 3, 2, 7, 5, 4, 6], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, true, false, true, false], [true, false, false, false, false, false, true, true], [false, true, true, false, false, false, false, true], [false, true, false, false, false, false, true, true], [false, false, true, true, false, true, false, false], [false, false, false, true, true, true, false, false]]),
  (25, [0, 1, 3, 2, 7, 5, 6, 4], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, true, false, false, true], [true, false, false, false, false, false, true, true], [false, true, true, false, false, false, true, false], [false, true, false, false, false, false, true, true], [false, false, false, true, true, true, false, false], [false, false, true, true, false, true, false, false]]),
  (25, [0, 3, 1, 2, 4, 7, 5, 6], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, true, true, false], [true, false, false, false, true, false, false, true], [false, true, false, true, false, false, true, false], [false, true, true, false, false, false, false, true], [false, false, true, false, true, false, false, true], [false, false, false, true, false, true, true, false]]),
  (25, [0, 3, 1, 2, 4, 7, 6, 5], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, false, true, false, true], [true, false, false, false, true, false, true, false], [false, true, false, true, false, false, false, true], [false, true, true, false, false, false, true, false], [false, false, false, true, false, true, false, true], [false, false, true, false, true, false, true, false]]),
  (25, [0, 3, 1, 2, 7, 4, 5, 6], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, true, false, true, false], [true, false, false, false, false, true, false, true], [false, true, true, false, false, false, false, true], [false, true, false, true, false, false, true, false], [false, false, true, false, false, true, false, true], [false, false, false, true, true, false, true, false]]),
  (25, [0, 3, 1, 2, 7, 4, 6, 5], [[false, true, true, true, false, false, false, false], [true, false, false, false, true, true, false, false], [true, false, false, false, true, false, false, true], [true, false, false, false, false, true, true, false], [false, true, true, false, false, false, true, false], [false, true, false, true, false, false, false, true], [false, false, false, true, true, false, false, true], [false, false, true, false, false, true, true, false]])]

def TRI8 : List (Nat × Nat × Nat) := [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 1, 6), (0, 1, 7), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 2, 6), (0, 2, 7), (0, 3, 4), (0, 3, 5), (0, 3, 6), (0, 3, 7), (0, 4, 5), (0, 4, 6), (0, 4, 7), (0, 5, 6), (0, 5, 7), (0, 6, 7), (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 2, 6), (1, 2, 7), (1, 3, 4), (1, 3, 5), (1, 3, 6), (1, 3, 7), (1, 4, 5), (1, 4, 6), (1, 4, 7), (1, 5, 6), (1, 5, 7), (1, 6, 7), (2, 3, 4), (2, 3, 5), (2, 3, 6), (2, 3, 7), (2, 4, 5), (2, 4, 6), (2, 4, 7), (2, 5, 6), (2, 5, 7), (2, 6, 7), (3, 4, 5), (3, 4, 6), (3, 4, 7), (3, 5, 6), (3, 5, 7), (3, 6, 7), (4, 5, 6), (4, 5, 7), (4, 6, 7), (5, 6, 7)]

def leaf8 (M : List (List Bool)) : Bool :=
  !(rowsOK M && triOK TRI8 M) || PB8.any (fun t => eqLL M t.2.2)

def check8 : Bool :=
  forallB fun b0 => forallB fun b1 => forallB fun b2 => forallB fun b3 => forallB fun b4 => forallB fun b5 => forallB fun b6 => forallB fun b7 => forallB fun b8 => forallB fun b9 => forallB fun b10 => forallB fun b11 => forallB fun b12 => forallB fun b13 =>
  leaf8 (mat8 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13)

theorem check8_ok : check8 = true := by decide +kernel

theorem pb8_ok : pbOK 8 PB8 = true := by decide +kernel

def mat6 (b0 b1 b2 b3 b4 : Bool) : List (List Bool) :=
  [[false, true, true, true, false, false],
   [true, false, false, false, true, true],
   [true, false, false, false, b0, b1],
   [true, false, false, false, b2, b3],
   [false, true, b0, b2, false, b4],
   [false, true, b1, b3, b4, false]]

def PB6 : List (Nat × List Nat × List (List Bool)) := [(8, [0, 3, 4, 5, 1, 2], [[false, true, true, true, false, false], [true, false, false, false, true, true], [true, false, false, false, true, true], [true, false, false, false, true, true], [false, true, true, true, false, false], [false, true, true, true, false, false]])]

def TRI6 : List (Nat × Nat × Nat) := [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5), (0, 4, 5), (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5), (1, 4, 5), (2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)]

def leaf6 (M : List (List Bool)) : Bool :=
  !(rowsOK M && triOK TRI6 M) || PB6.any (fun t => eqLL M t.2.2)

def check6 : Bool :=
  forallB fun b0 => forallB fun b1 => forallB fun b2 => forallB fun b3 => forallB fun b4 =>
  leaf6 (mat6 b0 b1 b2 b3 b4)

theorem check6_ok : check6 = true := by decide +kernel

theorem pb6_ok : pbOK 6 PB6 = true := by decide +kernel

end RH2F


-- ===== from TF3.lean =====

namespace RH2F
open MGraph Finset
open Classical

section sound

theorem xnor_eq {a b : Bool} (h : xnor a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [xnor]

theorem eqL_sound : ∀ {a b : List Bool}, eqL a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [xnor_eq h.1, eqL_sound h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem eqLL_sound : ∀ {a b : List (List Bool)}, eqLL a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqLL, Bool.and_eq_true] at h
    rw [eqL_sound h.1, eqLL_sound h.2]
  | [], _ :: _, h => by simp [eqLL] at h
  | _ :: _, [], h => by simp [eqLL] at h

/-- the matrix of a Bool function on `Fin k × Fin k`, by rows -/
def matL {k : Nat} (M : Fin k → Fin k → Bool) : List (List Bool) := List.ofFn (fun i => List.ofFn (fun j => M i j))

theorem getB_matL {k : Nat} (M : Fin k → Fin k → Bool) {i j : Nat} (hi : i < k) (hj : j < k) :
    getB (matL M) i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [getB, matL, List.getD_eq_getElem?_getD, hi, hj]

theorem cntB_ofFn : ∀ {k : Nat} (r : Fin k → Bool), cntB (List.ofFn r) = (univ.filter (fun j => r j = true)).card
  | 0, r => by simp [cntB]
  | k + 1, r => by
    rw [List.ofFn_succ, card_filter, Fin.sum_univ_succ, ← card_filter, ← cntB_ofFn (fun j => r j.succ)]
    cases h : r 0 <;> simp [cntB, h, Nat.add_comm]

theorem rowsOK_matL {k : Nat} (M : Fin k → Fin k → Bool)
    (h : ∀ i, (univ.filter (fun j => M i j = true)).card = 3) : rowsOK (matL M) = true := by
  unfold rowsOK matL
  rw [List.all_eq_true]
  intro r hr
  rw [List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  rw [cntB_ofFn, h i]; rfl

theorem triOK_matL {k : Nat} (M : Fin k → Fin k → Bool) (T : List (Nat × Nat × Nat))
    (hT : T.all (fun t => t.1 < k && t.2.1 < k && t.2.2 < k) = true)
    (h : ∀ i j l, M i j = true → M j l = true → M i l = true → False) : triOK T (matL M) = true := by
  unfold triOK
  rw [List.all_eq_true] at hT ⊢
  intro t ht
  have hb := hT t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb
  rw [getB_matL M h1 h2, getB_matL M h2 h3, getB_matL M h1 h3]
  cases e1 : M ⟨t.1, h1⟩ ⟨t.2.1, h2⟩ <;> cases e2 : M ⟨t.2.1, h2⟩ ⟨t.2.2, h3⟩ <;>
    cases e3 : M ⟨t.1, h1⟩ ⟨t.2.2, h3⟩ <;> simp
  exact h _ _ _ e1 e2 e3

/-- adjacency in `ofList n el` for an edge list with entries `< n` -/
theorem adjN_iff {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : el.all (fun e => e.1 < n && e.2 < n) = true)
    (p q : Fin n) : adjN el p.val q.val = true ↔ ∃ e, (ofList n el hn).Joins e p q := by
  unfold adjN
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxb⟩
    obtain ⟨e, rfl⟩ := List.get_of_mem hx
    have hb := List.all_eq_true.1 hel _ hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    refine ⟨e, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hxb
    unfold MGraph.Joins
    simp only [ofList, Prod.mk.injEq, Fin.ext_iff, Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb.2]
    rcases hxb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro ⟨e, he⟩
    refine ⟨el.get e, List.get_mem el e, ?_⟩
    have hb := List.all_eq_true.1 hel _ (List.get_mem el e)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    unfold MGraph.Joins at he
    simp only [ofList, Prod.mk.injEq, Fin.ext_iff, Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb.2] at he
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

end sound

section graph
variable {X : MGraph} {P : Fin X.m → Prop}

/-- rows of the adjacency matrix of an enumeration have three `true` entries -/
theorem rows_of (hG : InG X P) (hS : SimpleP P) {k : Nat} (φ : Fin k → Fin X.n)
    (hφi : ∀ i j, φ i = φ j → i = j) (hφs : ∀ x, meets P x → ∃ i, φ i = x) (hφm : ∀ i, meets P (φ i)) (i : Fin k) :
    (univ.filter (fun j => decide (Adjq P (φ i) (φ j)) = true)).card = 3 := by
  obtain ⟨y1, y2, y3, h12, h13, h23, a1, a2, a3, hall⟩ := nbrs3 hG hS (hφm i)
  obtain ⟨j1, rfl⟩ := hφs y1 (adjq_meets (adjq_symm a1))
  obtain ⟨j2, rfl⟩ := hφs y2 (adjq_meets (adjq_symm a2))
  obtain ⟨j3, rfl⟩ := hφs y3 (adjq_meets (adjq_symm a3))
  have : univ.filter (fun j => decide (Adjq P (φ i) (φ j)) = true) = {j1, j2, j3} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_insert, mem_singleton]
    constructor
    · intro hj
      rcases hall _ hj with h | h | h
      · exact Or.inl (hφi _ _ h)
      · exact Or.inr (Or.inl (hφi _ _ h))
      · exact Or.inr (Or.inr (hφi _ _ h))
    · rintro (rfl | rfl | rfl)
      · exact a1
      · exact a2
      · exact a3
  rw [this, card_insert_of_notMem (by simp only [mem_insert, mem_singleton, not_or]; exact
      ⟨fun h => h12 (congrArg φ h), fun h => h13 (congrArg φ h)⟩),
    card_insert_of_notMem (by simp only [mem_singleton]; exact fun h => h23 (congrArg φ h)), card_singleton]

theorem tri_of (hT : TriFree P) {k : Nat} (φ : Fin k → Fin X.n) (i j l : Fin k)
    (h1 : decide (Adjq P (φ i) (φ j)) = true) (h2 : decide (Adjq P (φ j) (φ l)) = true)
    (h3 : decide (Adjq P (φ i) (φ l)) = true) : False := by
  simp only [decide_eq_true_eq] at h1 h2 h3
  exact hT _ _ _ h1 h2 (adjq_symm h3)

end graph

end RH2F


-- ===== from TF4.lean =====

namespace RH2F
open MGraph Finset
open Classical

section tf4
variable {X : MGraph} {P : Fin X.m → Prop}

theorem pbT8 : PB8.all (fun t => t.1 == 24 ∨ t.1 == 25) = true := by decide
theorem tf8 (hG : InG X P) (hS : SimpleP P) (hT : TriFree P) (φ : Fin 8 → Fin X.n)
    (hφi : ∀ i j, φ i = φ j → i = j) (hφs : ∀ x, meets P x → ∃ i, φ i = x) (hφm : ∀ i, meets P (φ i))
    (h01 : Adjq P (φ 0) (φ 1)) (h02 : Adjq P (φ 0) (φ 2)) (h03 : Adjq P (φ 0) (φ 3))
    (h14 : Adjq P (φ 1) (φ 4)) (h15 : Adjq P (φ 1) (φ 5))
    (hv : ∀ y, Adjq P (φ 0) y → y = φ 1 ∨ y = φ 2 ∨ y = φ 3)
    (ha : ∀ y, Adjq P (φ 1) y → y = φ 0 ∨ y = φ 4 ∨ y = φ 5) :
    IsoFrom P (repG 24) ∨ IsoFrom P (repG 25) := by
  let M : Fin 8 → Fin 8 → Bool := fun i j => decide (Adjq P (φ i) (φ j))
  have nv : ∀ j : Fin 8, j ≠ 1 → j ≠ 2 → j ≠ 3 → M 0 j = false := by
    intro j h1 h2 h3
    simp only [M, decide_eq_false_iff_not]
    intro hj
    rcases hv _ hj with h | h | h
    · exact h1 (hφi _ _ h)
    · exact h2 (hφi _ _ h)
    · exact h3 (hφi _ _ h)
  have na : ∀ j : Fin 8, j ≠ 0 → j ≠ 4 → j ≠ 5 → M 1 j = false := by
    intro j h1 h2 h3
    simp only [M, decide_eq_false_iff_not]
    intro hj
    rcases ha _ hj with h | h | h
    · exact h1 (hφi _ _ h)
    · exact h2 (hφi _ _ h)
    · exact h3 (hφi _ _ h)
  have symm : ∀ i j : Fin 8, M i j = M j i := by
    intro i j
    simp only [M]
    exact decide_eq_decide.2 ⟨adjq_symm, adjq_symm⟩
  have diag : ∀ i : Fin 8, M i i = false := by
    intro i
    simp only [M, decide_eq_false_iff_not]
    exact fun h => adjq_ne hG.1 h rfl
  have t12 : M 1 2 = false := by
    simp only [M, decide_eq_false_iff_not]; exact fun h => hT _ _ _ h01 h (adjq_symm h02)
  have t13 : M 1 3 = false := by
    simp only [M, decide_eq_false_iff_not]; exact fun h => hT _ _ _ h01 h (adjq_symm h03)
  have t23 : M 2 3 = false := by
    simp only [M, decide_eq_false_iff_not]; exact fun h => hT _ _ _ h02 h (adjq_symm h03)
  have f01 : M 0 1 = true := decide_eq_true h01
  have f02 : M 0 2 = true := decide_eq_true h02
  have f03 : M 0 3 = true := decide_eq_true h03
  have f14 : M 1 4 = true := decide_eq_true h14
  have f15 : M 1 5 = true := decide_eq_true h15
  have e0_0 : M 0 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 0 := diag 0
  have e0_1 : M 0 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 1 := f01
  have e0_2 : M 0 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 2 := f02
  have e0_3 : M 0 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 3 := f03
  have e0_4 : M 0 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 4 := nv 4 (by decide) (by decide) (by decide)
  have e0_5 : M 0 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 5 := nv 5 (by decide) (by decide) (by decide)
  have e0_6 : M 0 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 6 := nv 6 (by decide) (by decide) (by decide)
  have e0_7 : M 0 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 0 7 := nv 7 (by decide) (by decide) (by decide)
  have e1_0 : M 1 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 0 := (symm 1 0).trans f01
  have e1_1 : M 1 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 1 := diag 1
  have e1_2 : M 1 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 2 := t12
  have e1_3 : M 1 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 3 := t13
  have e1_4 : M 1 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 4 := f14
  have e1_5 : M 1 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 5 := f15
  have e1_6 : M 1 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 6 := na 6 (by decide) (by decide) (by decide)
  have e1_7 : M 1 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 1 7 := na 7 (by decide) (by decide) (by decide)
  have e2_0 : M 2 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 0 := (symm 2 0).trans f02
  have e2_1 : M 2 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 1 := (symm 2 1).trans t12
  have e2_2 : M 2 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 2 := diag 2
  have e2_3 : M 2 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 3 := t23
  have e2_4 : M 2 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 4 := rfl
  have e2_5 : M 2 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 5 := rfl
  have e2_6 : M 2 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 6 := rfl
  have e2_7 : M 2 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 2 7 := rfl
  have e3_0 : M 3 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 0 := (symm 3 0).trans f03
  have e3_1 : M 3 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 1 := (symm 3 1).trans t13
  have e3_2 : M 3 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 2 := (symm 3 2).trans t23
  have e3_3 : M 3 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 3 := diag 3
  have e3_4 : M 3 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 4 := rfl
  have e3_5 : M 3 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 5 := rfl
  have e3_6 : M 3 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 6 := rfl
  have e3_7 : M 3 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 3 7 := rfl
  have e4_0 : M 4 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 0 := (symm 4 0).trans (nv 4 (by decide) (by decide) (by decide))
  have e4_1 : M 4 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 1 := (symm 4 1).trans f14
  have e4_2 : M 4 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 2 := symm 4 2
  have e4_3 : M 4 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 3 := symm 4 3
  have e4_4 : M 4 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 4 := diag 4
  have e4_5 : M 4 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 5 := rfl
  have e4_6 : M 4 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 6 := rfl
  have e4_7 : M 4 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 4 7 := rfl
  have e5_0 : M 5 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 0 := (symm 5 0).trans (nv 5 (by decide) (by decide) (by decide))
  have e5_1 : M 5 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 1 := (symm 5 1).trans f15
  have e5_2 : M 5 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 2 := symm 5 2
  have e5_3 : M 5 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 3 := symm 5 3
  have e5_4 : M 5 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 4 := symm 5 4
  have e5_5 : M 5 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 5 := diag 5
  have e5_6 : M 5 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 6 := rfl
  have e5_7 : M 5 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 5 7 := rfl
  have e6_0 : M 6 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 0 := (symm 6 0).trans (nv 6 (by decide) (by decide) (by decide))
  have e6_1 : M 6 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 1 := (symm 6 1).trans (na 6 (by decide) (by decide) (by decide))
  have e6_2 : M 6 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 2 := symm 6 2
  have e6_3 : M 6 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 3 := symm 6 3
  have e6_4 : M 6 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 4 := symm 6 4
  have e6_5 : M 6 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 5 := symm 6 5
  have e6_6 : M 6 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 6 := diag 6
  have e6_7 : M 6 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 6 7 := rfl
  have e7_0 : M 7 0 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 0 := (symm 7 0).trans (nv 7 (by decide) (by decide) (by decide))
  have e7_1 : M 7 1 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 1 := (symm 7 1).trans (na 7 (by decide) (by decide) (by decide))
  have e7_2 : M 7 2 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 2 := symm 7 2
  have e7_3 : M 7 3 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 3 := symm 7 3
  have e7_4 : M 7 4 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 4 := symm 7 4
  have e7_5 : M 7 5 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 5 := symm 7 5
  have e7_6 : M 7 6 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 6 := symm 7 6
  have e7_7 : M 7 7 = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) 7 7 := diag 7
  have hM : ∀ i j : Fin 8, M i j = getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  have hmat : matL M = mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7) := by
    have : matL M = matL (fun i j : Fin 8 => getB (mat8 (M 2 4) (M 2 5) (M 2 6) (M 2 7) (M 3 4) (M 3 5) (M 3 6) (M 3 7) (M 4 5) (M 4 6) (M 4 7) (M 5 6) (M 5 7) (M 6 7)) i j) := by
      unfold matL; congr 1; funext i; congr 1; funext j; exact hM i j
    rw [this]; rfl
  have hrows := rowsOK_matL M (rows_of hG hS φ hφi hφs hφm)
  have htri := triOK_matL M TRI8 (by decide) (tri_of hT φ)
  have c0 := forallB_sound check8_ok (M 2 4)
  have c1 := forallB_sound c0 (M 2 5)
  have c2 := forallB_sound c1 (M 2 6)
  have c3 := forallB_sound c2 (M 2 7)
  have c4 := forallB_sound c3 (M 3 4)
  have c5 := forallB_sound c4 (M 3 5)
  have c6 := forallB_sound c5 (M 3 6)
  have c7 := forallB_sound c6 (M 3 7)
  have c8 := forallB_sound c7 (M 4 5)
  have c9 := forallB_sound c8 (M 4 6)
  have c10 := forallB_sound c9 (M 4 7)
  have c11 := forallB_sound c10 (M 5 6)
  have c12 := forallB_sound c11 (M 5 7)
  have c13 := forallB_sound c12 (M 6 7)
  have hleaf : leaf8 (matL M) = true := by rw [hmat]; exact c13
  unfold leaf8 at hleaf
  rw [hrows, htri] at hleaf
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hleaf
  obtain ⟨t, ht, hte⟩ := List.any_eq_true.1 hleaf
  have hMt := eqLL_sound hte
  have hpb := List.all_eq_true.1 pb8_ok t ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hpb
  obtain ⟨⟨⟨hn, hperm⟩, hbd⟩, hent⟩ := hpb
  simp only [List.all_eq_true, List.mem_range] at hent
  have hk := List.all_eq_true.1 pbT8 t ht
  have hn' : (repG t.1).n = 8 := hn
  simp only [permOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hperm
  obtain ⟨hlt, hinj⟩ := hperm
  let π : Fin (repG t.1).n → Fin (repG t.1).n := fun i => Fin.cast hn'.symm ⟨t.2.1.getD (Fin.cast hn' i) 0, hlt _ (Fin.cast hn' i).isLt⟩
  have hπ : ∀ i j, π i = π j → i = j := by
    intro i j hij
    have hv' : t.2.1.getD (Fin.cast hn' i) 0 = t.2.1.getD (Fin.cast hn' j) 0 := by
      have := congrArg Fin.val hij; simpa [π] using this
    have := hinj _ (Fin.cast hn' i).isLt _ (Fin.cast hn' j).isLt
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hv' h
    · exact Fin.ext (by simpa using h)
  have hH : SimpleH (repG t.1) := by
    rcases (by simpa using hk : t.1 = 24 ∨ t.1 = 25) with h | h <;> rw [h] <;> intro e e' p q <;> revert e e' p q <;> decide
  have hm : 0 < (repG t.1).m := by
    rcases (by simpa using hk : t.1 = 24 ∨ t.1 = 25) with h | h <;> rw [h] <;> decide
  have hbd' : (repL t.1).all (fun e => e.1 < repN t.1 && e.2 < repN t.1) = true := by rw [hn]; exact hbd
  have hadj : ∀ i j, Adjq P (φ (Fin.cast hn' i)) (φ (Fin.cast hn' j)) ↔ ∃ e, (repG t.1).Joins e (π i) (π j) := by
    intro i j
    have h1 : Adjq P (φ (Fin.cast hn' i)) (φ (Fin.cast hn' j)) ↔ M (Fin.cast hn' i) (Fin.cast hn' j) = true := by
      simp only [M, decide_eq_true_eq]
    have h2 := getB_matL M (Fin.cast hn' i).isLt (Fin.cast hn' j).isLt
    rw [hMt] at h2
    have h3 := hent _ (Fin.cast hn' i).isLt _ (Fin.cast hn' j).isLt
    rw [beq_iff_eq] at h3
    rw [h1, ← h2, h3]
    exact adjN_iff (n := repN t.1) (hn := repN_pos t.1) hbd' (π i) (π j)
  have hiso : IsoFrom P (repG t.1) :=
    isoFrom_of_adj hG hS hH hm (fun i => φ (Fin.cast hn' i))
      (fun i j h => Fin.ext (by have := congrArg Fin.val (hφi _ _ h); simpa using this))
      (fun x hx => by obtain ⟨i, hi⟩ := hφs x hx; exact ⟨Fin.cast hn'.symm i, by simpa using hi⟩)
      π hπ hadj
  rcases (by simpa using hk : t.1 = 24 ∨ t.1 = 25) with h | h
  · exact Or.inl (h ▸ hiso)
  · exact Or.inr (h ▸ hiso)

theorem pbT6 : PB6.all (fun t => t.1 == 8) = true := by decide
theorem tf6 (hG : InG X P) (hS : SimpleP P) (hT : TriFree P) (φ : Fin 6 → Fin X.n)
    (hφi : ∀ i j, φ i = φ j → i = j) (hφs : ∀ x, meets P x → ∃ i, φ i = x) (hφm : ∀ i, meets P (φ i))
    (h01 : Adjq P (φ 0) (φ 1)) (h02 : Adjq P (φ 0) (φ 2)) (h03 : Adjq P (φ 0) (φ 3))
    (h14 : Adjq P (φ 1) (φ 4)) (h15 : Adjq P (φ 1) (φ 5))
    (hv : ∀ y, Adjq P (φ 0) y → y = φ 1 ∨ y = φ 2 ∨ y = φ 3)
    (ha : ∀ y, Adjq P (φ 1) y → y = φ 0 ∨ y = φ 4 ∨ y = φ 5) :
    IsoFrom P (repG 8) := by
  let M : Fin 6 → Fin 6 → Bool := fun i j => decide (Adjq P (φ i) (φ j))
  have nv : ∀ j : Fin 6, j ≠ 1 → j ≠ 2 → j ≠ 3 → M 0 j = false := by
    intro j h1 h2 h3
    simp only [M, decide_eq_false_iff_not]
    intro hj
    rcases hv _ hj with h | h | h
    · exact h1 (hφi _ _ h)
    · exact h2 (hφi _ _ h)
    · exact h3 (hφi _ _ h)
  have na : ∀ j : Fin 6, j ≠ 0 → j ≠ 4 → j ≠ 5 → M 1 j = false := by
    intro j h1 h2 h3
    simp only [M, decide_eq_false_iff_not]
    intro hj
    rcases ha _ hj with h | h | h
    · exact h1 (hφi _ _ h)
    · exact h2 (hφi _ _ h)
    · exact h3 (hφi _ _ h)
  have symm : ∀ i j : Fin 6, M i j = M j i := by
    intro i j
    simp only [M]
    exact decide_eq_decide.2 ⟨adjq_symm, adjq_symm⟩
  have diag : ∀ i : Fin 6, M i i = false := by
    intro i
    simp only [M, decide_eq_false_iff_not]
    exact fun h => adjq_ne hG.1 h rfl
  have t12 : M 1 2 = false := by
    simp only [M, decide_eq_false_iff_not]; exact fun h => hT _ _ _ h01 h (adjq_symm h02)
  have t13 : M 1 3 = false := by
    simp only [M, decide_eq_false_iff_not]; exact fun h => hT _ _ _ h01 h (adjq_symm h03)
  have t23 : M 2 3 = false := by
    simp only [M, decide_eq_false_iff_not]; exact fun h => hT _ _ _ h02 h (adjq_symm h03)
  have f01 : M 0 1 = true := decide_eq_true h01
  have f02 : M 0 2 = true := decide_eq_true h02
  have f03 : M 0 3 = true := decide_eq_true h03
  have f14 : M 1 4 = true := decide_eq_true h14
  have f15 : M 1 5 = true := decide_eq_true h15
  have e0_0 : M 0 0 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 0 0 := diag 0
  have e0_1 : M 0 1 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 0 1 := f01
  have e0_2 : M 0 2 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 0 2 := f02
  have e0_3 : M 0 3 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 0 3 := f03
  have e0_4 : M 0 4 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 0 4 := nv 4 (by decide) (by decide) (by decide)
  have e0_5 : M 0 5 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 0 5 := nv 5 (by decide) (by decide) (by decide)
  have e1_0 : M 1 0 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 1 0 := (symm 1 0).trans f01
  have e1_1 : M 1 1 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 1 1 := diag 1
  have e1_2 : M 1 2 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 1 2 := t12
  have e1_3 : M 1 3 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 1 3 := t13
  have e1_4 : M 1 4 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 1 4 := f14
  have e1_5 : M 1 5 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 1 5 := f15
  have e2_0 : M 2 0 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 2 0 := (symm 2 0).trans f02
  have e2_1 : M 2 1 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 2 1 := (symm 2 1).trans t12
  have e2_2 : M 2 2 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 2 2 := diag 2
  have e2_3 : M 2 3 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 2 3 := t23
  have e2_4 : M 2 4 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 2 4 := rfl
  have e2_5 : M 2 5 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 2 5 := rfl
  have e3_0 : M 3 0 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 3 0 := (symm 3 0).trans f03
  have e3_1 : M 3 1 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 3 1 := (symm 3 1).trans t13
  have e3_2 : M 3 2 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 3 2 := (symm 3 2).trans t23
  have e3_3 : M 3 3 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 3 3 := diag 3
  have e3_4 : M 3 4 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 3 4 := rfl
  have e3_5 : M 3 5 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 3 5 := rfl
  have e4_0 : M 4 0 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 4 0 := (symm 4 0).trans (nv 4 (by decide) (by decide) (by decide))
  have e4_1 : M 4 1 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 4 1 := (symm 4 1).trans f14
  have e4_2 : M 4 2 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 4 2 := symm 4 2
  have e4_3 : M 4 3 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 4 3 := symm 4 3
  have e4_4 : M 4 4 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 4 4 := diag 4
  have e4_5 : M 4 5 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 4 5 := rfl
  have e5_0 : M 5 0 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 5 0 := (symm 5 0).trans (nv 5 (by decide) (by decide) (by decide))
  have e5_1 : M 5 1 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 5 1 := (symm 5 1).trans f15
  have e5_2 : M 5 2 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 5 2 := symm 5 2
  have e5_3 : M 5 3 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 5 3 := symm 5 3
  have e5_4 : M 5 4 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 5 4 := symm 5 4
  have e5_5 : M 5 5 = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) 5 5 := diag 5
  have hM : ∀ i j : Fin 6, M i j = getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  have hmat : matL M = mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5) := by
    have : matL M = matL (fun i j : Fin 6 => getB (mat6 (M 2 4) (M 2 5) (M 3 4) (M 3 5) (M 4 5)) i j) := by
      unfold matL; congr 1; funext i; congr 1; funext j; exact hM i j
    rw [this]; rfl
  have hrows := rowsOK_matL M (rows_of hG hS φ hφi hφs hφm)
  have htri := triOK_matL M TRI6 (by decide) (tri_of hT φ)
  have c0 := forallB_sound check6_ok (M 2 4)
  have c1 := forallB_sound c0 (M 2 5)
  have c2 := forallB_sound c1 (M 3 4)
  have c3 := forallB_sound c2 (M 3 5)
  have c4 := forallB_sound c3 (M 4 5)
  have hleaf : leaf6 (matL M) = true := by rw [hmat]; exact c4
  unfold leaf6 at hleaf
  rw [hrows, htri] at hleaf
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hleaf
  obtain ⟨t, ht, hte⟩ := List.any_eq_true.1 hleaf
  have hMt := eqLL_sound hte
  have hpb := List.all_eq_true.1 pb6_ok t ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hpb
  obtain ⟨⟨⟨hn, hperm⟩, hbd⟩, hent⟩ := hpb
  simp only [List.all_eq_true, List.mem_range] at hent
  have hk := List.all_eq_true.1 pbT6 t ht
  have hn' : (repG t.1).n = 6 := hn
  simp only [permOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hperm
  obtain ⟨hlt, hinj⟩ := hperm
  let π : Fin (repG t.1).n → Fin (repG t.1).n := fun i => Fin.cast hn'.symm ⟨t.2.1.getD (Fin.cast hn' i) 0, hlt _ (Fin.cast hn' i).isLt⟩
  have hπ : ∀ i j, π i = π j → i = j := by
    intro i j hij
    have hv' : t.2.1.getD (Fin.cast hn' i) 0 = t.2.1.getD (Fin.cast hn' j) 0 := by
      have := congrArg Fin.val hij; simpa [π] using this
    have := hinj _ (Fin.cast hn' i).isLt _ (Fin.cast hn' j).isLt
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hv' h
    · exact Fin.ext (by simpa using h)
  have hH : SimpleH (repG t.1) := by
    rcases (by simpa using hk : t.1 = 8 ∨ t.1 = 8) with h | h <;> rw [h] <;> intro e e' p q <;> revert e e' p q <;> decide
  have hm : 0 < (repG t.1).m := by
    rcases (by simpa using hk : t.1 = 8 ∨ t.1 = 8) with h | h <;> rw [h] <;> decide
  have hbd' : (repL t.1).all (fun e => e.1 < repN t.1 && e.2 < repN t.1) = true := by rw [hn]; exact hbd
  have hadj : ∀ i j, Adjq P (φ (Fin.cast hn' i)) (φ (Fin.cast hn' j)) ↔ ∃ e, (repG t.1).Joins e (π i) (π j) := by
    intro i j
    have h1 : Adjq P (φ (Fin.cast hn' i)) (φ (Fin.cast hn' j)) ↔ M (Fin.cast hn' i) (Fin.cast hn' j) = true := by
      simp only [M, decide_eq_true_eq]
    have h2 := getB_matL M (Fin.cast hn' i).isLt (Fin.cast hn' j).isLt
    rw [hMt] at h2
    have h3 := hent _ (Fin.cast hn' i).isLt _ (Fin.cast hn' j).isLt
    rw [beq_iff_eq] at h3
    rw [h1, ← h2, h3]
    exact adjN_iff (n := repN t.1) (hn := repN_pos t.1) hbd' (π i) (π j)
  have hiso : IsoFrom P (repG t.1) :=
    isoFrom_of_adj hG hS hH hm (fun i => φ (Fin.cast hn' i))
      (fun i j h => Fin.ext (by have := congrArg Fin.val (hφi _ _ h); simpa using this))
      (fun x hx => by obtain ⟨i, hi⟩ := hφs x hx; exact ⟨Fin.cast hn'.symm i, by simpa using hi⟩)
      π hπ hadj
  rcases (by simpa using hk : t.1 = 8 ∨ t.1 = 8) with h | h
  · exact h ▸ hiso
  · exact h ▸ hiso

end tf4

end RH2F


-- ===== from TF5.lean =====

namespace RH2F
open MGraph Finset
open Classical

section inj

theorem inj6 {α : Type} (x0 x1 x2 x3 x4 x5 : α) (h : [x0, x1, x2, x3, x4, x5].Nodup) :
    ∀ i j : Fin 6, ![x0, x1, x2, x3, x4, x5] i = ![x0, x1, x2, x3, x4, x5] j → i = j := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> simp_all

theorem inj8 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 : α) (h : [x0, x1, x2, x3, x4, x5, x6, x7].Nodup) :
    ∀ i j : Fin 8, ![x0, x1, x2, x3, x4, x5, x6, x7] i = ![x0, x1, x2, x3, x4, x5, x6, x7] j → i = j := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> simp_all

end inj

section tf5
variable {X : MGraph} {P : Fin X.m → Prop}

/-- **Lemma 4 of fact 7922314679f8733d** (B8 §5): a simple triangle-free member of 𝒢 with at most 8 vertices is
    isomorphic to `K₃,₃ = Rep08`, the cube `Rep24` or the Wagner graph `Rep25`. -/
theorem tf_iso (hG : InG X P) (hS : SimpleP P) (hT : TriFree P) (h8 : vcount P ≤ 8) (hpos : 0 < vcount P) :
    IsoFrom P (repG 8) ∨ IsoFrom P (repG 24) ∨ IsoFrom P (repG 25) := by
  have lp := hG.1
  obtain ⟨v, hv⟩ := cntF_pos _ _ hpos
  obtain ⟨a, b, c, hab, hac, hbc, hva, hvb, hvc, hvall⟩ := nbrs3 hG hS hv
  obtain ⟨a1, a2, h12, h1v, h2v, ha1, ha2, haall⟩ := nbrs_other hG hS (adjq_symm hva)
  have dva : v ≠ a := adjq_ne lp hva
  have dvb : v ≠ b := adjq_ne lp hvb
  have dvc : v ≠ c := adjq_ne lp hvc
  have daa1 : a ≠ a1 := adjq_ne lp ha1
  have daa2 : a ≠ a2 := adjq_ne lp ha2
  have dba1 : b ≠ a1 := fun h => hT v a b hva (by rw [h]; exact ha1) (adjq_symm hvb)
  have dba2 : b ≠ a2 := fun h => hT v a b hva (by rw [h]; exact ha2) (adjq_symm hvb)
  have dca1 : c ≠ a1 := fun h => hT v a c hva (by rw [h]; exact ha1) (adjq_symm hvc)
  have dca2 : c ≠ a2 := fun h => hT v a c hva (by rw [h]; exact ha2) (adjq_symm hvc)
  have dva1 : v ≠ a1 := fun h => h1v h.symm
  have dva2 : v ≠ a2 := fun h => h2v h.symm
  have mv : meets P v := hv
  have ma : meets P a := adjq_meets (adjq_symm hva)
  have mb : meets P b := adjq_meets (adjq_symm hvb)
  have mc : meets P c := adjq_meets (adjq_symm hvc)
  have ma1 : meets P a1 := adjq_meets (adjq_symm ha1)
  have ma2 : meets P a2 := adjq_meets (adjq_symm ha2)
  let T := univ.filter (meets P)
  have hT' : vcount P = T.card := vcount_eq_card P
  let S6 : Finset (Fin X.n) := {v, a, b, c, a1, a2}
  have hS6 : S6.card = 6 := by
    simp only [S6]
    rw [card_insert_of_notMem (by simp [dva, dvb, dvc, dva1, dva2]),
      card_insert_of_notMem (by simp [hab, hac, daa1, daa2]),
      card_insert_of_notMem (by simp [hbc, dba1, dba2]),
      card_insert_of_notMem (by simp [dca1, dca2]),
      card_insert_of_notMem (by simp [h12]), card_singleton]
  have hsub : S6 ⊆ T := by
    intro x hx
    simp only [S6, mem_insert, mem_singleton] at hx
    simp only [T, mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have h6 : 6 ≤ vcount P := by rw [hT', ← hS6]; exact card_le_card hsub
  have hev := vcount_even' hG
  have h68 : vcount P = 6 ∨ vcount P = 8 := by omega
  rcases h68 with h6' | h8'
  · -- six vertices: `K₃,₃`
    have hTS : T = S6 := (eq_of_subset_of_card_le hsub (by rw [hS6, ← hT', h6'])).symm
    let φ : Fin 6 → Fin X.n := ![v, a, b, c, a1, a2]
    have hφi : ∀ i j, φ i = φ j → i = j := inj6 v a b c a1 a2 (by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact ⟨⟨dva, dvb, dvc, dva1, dva2⟩, ⟨hab, hac, daa1, daa2⟩, ⟨hbc, dba1, dba2⟩, ⟨dca1, dca2⟩, h12⟩)
    have hφs : ∀ x, meets P x → ∃ i, φ i = x := by
      intro x hx
      have : x ∈ S6 := by rw [← hTS]; simp [T, hx]
      simp only [S6, mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    have hφm : ∀ i, meets P (φ i) := by
      intro i; fin_cases i <;> assumption
    exact Or.inl (tf6 hG hS hT φ hφi hφs hφm hva hvb hvc ha1 ha2 hvall haall)
  · -- eight vertices: the cube or the Wagner graph
    have h2 : (T \ S6).card = 2 := by rw [card_sdiff_of_subset hsub, ← hT', h8', hS6]
    obtain ⟨r, s, hrs, hrs'⟩ := card_eq_two.1 h2
    have hr : r ∈ T \ S6 := by rw [hrs']; simp
    have hs : s ∈ T \ S6 := by rw [hrs']; simp
    simp only [T, S6, mem_sdiff, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, not_or] at hr hs
    obtain ⟨mr, drv, dra, drb, drc, dra1, dra2⟩ := hr
    obtain ⟨ms, dsv, dsa, dsb, dsc, dsa1, dsa2⟩ := hs
    let φ : Fin 8 → Fin X.n := ![v, a, b, c, a1, a2, r, s]
    have hφi : ∀ i j, φ i = φ j → i = j := inj8 v a b c a1 a2 r s (by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact ⟨⟨dva, dvb, dvc, dva1, dva2, fun h => drv h.symm, fun h => dsv h.symm⟩,
        ⟨hab, hac, daa1, daa2, fun h => dra h.symm, fun h => dsa h.symm⟩,
        ⟨hbc, dba1, dba2, fun h => drb h.symm, fun h => dsb h.symm⟩,
        ⟨dca1, dca2, fun h => drc h.symm, fun h => dsc h.symm⟩,
        ⟨h12, fun h => dra1 h.symm, fun h => dsa1 h.symm⟩, ⟨fun h => dra2 h.symm, fun h => dsa2 h.symm⟩, hrs⟩)
    have hφs : ∀ x, meets P x → ∃ i, φ i = x := by
      intro x hx
      by_cases hx6 : x ∈ S6
      · simp only [S6, mem_insert, mem_singleton] at hx6
        rcases hx6 with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
      · have : x ∈ T \ S6 := by simp only [mem_sdiff]; exact ⟨by simp [T, hx], hx6⟩
        rw [hrs'] at this
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl
        · exact ⟨6, rfl⟩
        · exact ⟨7, rfl⟩
    have hφm : ∀ i, meets P (φ i) := by
      intro i; fin_cases i <;> assumption
    exact Or.inr (tf8 hG hS hT φ hφi hφs hφm hva hvb hvc ha1 ha2 hvall haall)

end tf5

end RH2F

namespace RH2F
open MGraph

/-- **Layer 6a of the Lean formalization of RH2**: Lemma 4 of Theorem B8 (fact 7922314679f8733d, §5) — a simple
    triangle-free member of 𝒢 with at most 8 vertices is `K₃,₃ = Rep08`, the cube `Rep24` or the Wagner graph
    `Rep25`. -/
theorem layer6a : ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → SimpleP P → TriFree P → vcount P ≤ 8 →
    0 < vcount P → IsoFrom P (repG 8) ∨ IsoFrom P (repG 24) ∨ IsoFrom P (repG 25) :=
  fun _ _ hG hS hT h8 hpos => tf_iso hG hS hT h8 hpos

end RH2F
