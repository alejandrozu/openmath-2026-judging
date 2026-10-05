import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000

/-!
# Clique-cluster lifting theorem

Scratch header is `import Mathlib` only for daemon speed; narrowed on collation.
-/

namespace Lea.RamseyLifting

open Finset

variable {m : ℕ}

/-! ## 1. Template, `P`, blow-up -/

/-- All six template entries determined by four block indices equal `col`.
Repeated indices are allowed and the DIAGONAL of `A` supplies their colour. -/
def sixEq (A : Fin m → Fin m → Bool) (col : Bool) (i j k l : Fin m) : Bool :=
  (A i j == col) && (A i k == col) && (A i l == col) &&
  (A j k == col) && (A j l == col) && (A k l == col)

/-- README's `[all six red] + [all six blue]`. -/
def monoW (A : Fin m → Fin m → Bool) (i j k l : Fin m) : ℕ :=
  (sixEq A true i j k l).toNat + (sixEq A false i j k l).toNat

/-- `Q = ∑ wᵢ`. -/
def Qw (w : Fin m → ℕ) : ℕ := ∑ i, w i

/-- Numerator of `P`: literal sum over ALL ordered four-tuples, repetitions included. -/
def Pnum (A : Fin m → Fin m → Bool) (w : Fin m → ℕ) : ℕ :=
  ∑ i, ∑ j, ∑ k, ∑ l, w i * w j * w k * w l * monoW A i j k l

/-- `P(A,w) = Pnum / Q⁴`: the only ℕ → ℚ boundary. -/
def Pval (A : Fin m → Fin m → Bool) (w : Fin m → ℕ) : ℚ :=
  (Pnum A w : ℚ) / (Qw w : ℚ) ^ 4

/-- Blow-up vertex type: block `i` contributes `v i` vertices. -/
abbrev Blow (v : Fin m → ℕ) := Σ i : Fin m, Fin (v i)

lemma card_blow (v : Fin m → ℕ) : Fintype.card (Blow v) = Qw v := by
  simp [Blow, Qw]

/-- A four-set of blow-up vertices is monochromatic.  Only pairs of DISTINCT vertices
are coloured, so the diagonal is never a self-loop. -/
def MonoSet (A : Fin m → Fin m → Bool) {v : Fin m → ℕ} (S : Finset (Blow v)) : Prop :=
  ∃ c : Bool, ∀ u ∈ S, ∀ x ∈ S, u ≠ x → A u.1 x.1 = c

instance decMonoSet (A : Fin m → Fin m → Bool) (v : Fin m → ℕ) :
    DecidablePred (MonoSet A (v := v)) := fun _ => by unfold MonoSet; infer_instance

/-- `M₄`: number of monochromatic four-element vertex subsets. -/
def M4 (A : Fin m → Fin m → Bool) (v : Fin m → ℕ) : ℕ :=
  (((univ : Finset (Blow v)).powersetCard 4).filter (MonoSet A)).card


/-! ## 2. Ordered tuples of a symmetric function: the multiplicities 1,4,6,12,24

A general fact about a four-argument function invariant under the three adjacent
transpositions: the sum over all ordered four-tuples regroups as the sum over the five
index-multiplicity patterns weighted by `4!/∏(mult!)`.  This is the whole mathematical
content of the evaluator's optimised counter. -/

section SymSum
variable {ι : Type*} [DecidableEq ι] [LinearOrder ι]

omit [DecidableEq ι] in
private lemma max_not_mem {s : Finset ι} {x : ι}
    (hmax : ∀ y ∈ s, y < x) : x ∉ s := by
  intro hx
  exact (lt_irrefl x) (hmax x hx)

private lemma filter_insert_lt {s : Finset ι} {x a : ι} (hax : a < x) :
    (insert x s).filter (fun b => a < b) =
      insert x (s.filter (fun b => a < b)) := by
  ext b
  by_cases hb : b = x
  · subst b
    simp [hax]
  · simp [hb]

private lemma filter_insert_max {s : Finset ι} {x : ι}
    (hmax : ∀ y ∈ s, y < x) :
    (insert x s).filter (fun b => x < b) = ∅ := by
  apply Finset.filter_false_of_mem
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb'
  · exact lt_irrefl _
  · exact asymm (hmax b hb')

omit [LinearOrder ι] in
private lemma erase_insert_max {s : Finset ι} {x : ι} (hx : x ∉ s) :
    (insert x s).erase x = s := by
  ext b
  by_cases hb : b = x
  · subst b
    simp [hx]
  · simp [hb]

omit [LinearOrder ι] in
private lemma erase_insert_other {s : Finset ι} {x a : ι} (hax : a ≠ x) :
    (insert x s).erase a = insert x (s.erase a) := by
  ext b
  by_cases hb : b = x
  · subst b
    simp [Ne.symm hax]
  · simp [hb]

private lemma sum_lt_two_insert_max (s : Finset ι) (x : ι)
    (G : ι → ι → ℕ) (hmax : ∀ y ∈ s, y < x) :
    (∑ a ∈ insert x s, ∑ b ∈ (insert x s).filter (fun b => a < b), G a b)
      =
    (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), G a b)
      + ∑ a ∈ s, G a x := by
  have hx : x ∉ s := max_not_mem hmax
  rw [sum_insert hx, filter_insert_max hmax]
  simp only [sum_empty, zero_add]
  calc
    (∑ a ∈ s, ∑ b ∈ (insert x s).filter (fun b => a < b), G a b)
        =
        ∑ a ∈ s, (G a x + ∑ b ∈ s.filter (fun b => a < b), G a b) := by
          apply sum_congr rfl
          intro a ha
          rw [filter_insert_lt (hmax a ha), sum_insert (by simp [hx])]
          try simp [hx]
    _ = (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), G a b)
          + ∑ a ∈ s, G a x := by
          simp only [sum_add_distrib]
          ring

private lemma sum_erase_two_insert_max (s : Finset ι) (x : ι)
    (G : ι → ι → ℕ) (hmax : ∀ y ∈ s, y < x) :
    (∑ a ∈ insert x s, ∑ b ∈ (insert x s).erase a, G a b)
      =
    (∑ a ∈ s, ∑ b ∈ s.erase a, G a b)
      + (∑ b ∈ s, G x b) + ∑ a ∈ s, G a x := by
  have hx : x ∉ s := max_not_mem hmax
  rw [sum_insert hx, erase_insert_max hx]
  have htail :
      (∑ a ∈ s, ∑ b ∈ (insert x s).erase a, G a b)
        =
      (∑ a ∈ s, G a x) + ∑ a ∈ s, ∑ b ∈ s.erase a, G a b := by
    calc
      (∑ a ∈ s, ∑ b ∈ (insert x s).erase a, G a b)
          =
          ∑ a ∈ s, (G a x + ∑ b ∈ s.erase a, G a b) := by
            apply sum_congr rfl
            intro a ha
            have hax : a ≠ x := by
              intro h
              subst a
              exact hx ha
            rw [erase_insert_other hax, sum_insert (by simp [hx])]
            try simp [hx]
      _ = (∑ a ∈ s, G a x) + ∑ a ∈ s, ∑ b ∈ s.erase a, G a b := by
            simp only [sum_add_distrib]
  rw [htail]
  ring

private lemma sum_lt_three_insert_max (s : Finset ι) (x : ι)
    (G : ι → ι → ι → ℕ) (hmax : ∀ y ∈ s, y < x) :
    (∑ a ∈ insert x s,
      ∑ b ∈ (insert x s).filter (fun b => a < b),
      ∑ c ∈ (insert x s).filter (fun c => b < c), G a b c)
      =
    (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
      ∑ c ∈ s.filter (fun c => b < c), G a b c)
      +
    (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), G a b x) := by
  have hx : x ∉ s := max_not_mem hmax
  rw [sum_insert hx, filter_insert_max hmax]
  simp only [sum_empty, zero_add]
  have hone (a : ι) (ha : a ∈ s) :
      (∑ b ∈ (insert x s).filter (fun b => a < b),
        ∑ c ∈ (insert x s).filter (fun c => b < c), G a b c)
        =
      (∑ b ∈ s.filter (fun b => a < b),
        ∑ c ∈ s.filter (fun c => b < c), G a b c)
        + ∑ b ∈ s.filter (fun b => a < b), G a b x := by
    rw [filter_insert_lt (hmax a ha), sum_insert (by simp [hx])]
    rw [filter_insert_max hmax]
    simp only [sum_empty, zero_add]
    calc
      (∑ b ∈ s.filter (fun b => a < b),
        ∑ c ∈ (insert x s).filter (fun c => b < c), G a b c)
          =
        ∑ b ∈ s.filter (fun b => a < b),
          (G a b x + ∑ c ∈ s.filter (fun c => b < c), G a b c) := by
            apply sum_congr rfl
            intro b hb
            have hbs : b ∈ s := (mem_filter.mp hb).1
            rw [filter_insert_lt (hmax b hbs), sum_insert (by simp [hx])]
            try simp [hx]
      _ = (∑ b ∈ s.filter (fun b => a < b),
            ∑ c ∈ s.filter (fun c => b < c), G a b c)
            + ∑ b ∈ s.filter (fun b => a < b), G a b x := by
            simp only [sum_add_distrib]
            ring
  calc
    (∑ a ∈ s, ∑ b ∈ (insert x s).filter (fun b => a < b),
      ∑ c ∈ (insert x s).filter (fun c => b < c), G a b c)
        =
      ∑ a ∈ s,
        ((∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), G a b c)
          + ∑ b ∈ s.filter (fun b => a < b), G a b x) := by
            apply sum_congr rfl
            intro a ha
            exact hone a ha
    _ = (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), G a b c)
          + (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), G a b x) := by
            simp only [sum_add_distrib]

private lemma sum_lt_tail_two_insert_max (s : Finset ι) (x a : ι)
    (G : ι → ι → ℕ) (hmax : ∀ y ∈ s, y < x) (ha : a ∈ s) :
    (∑ b ∈ (insert x s).filter (fun b => a < b),
      ∑ c ∈ (insert x s).filter (fun c => b < c), G b c)
      =
    (∑ b ∈ s.filter (fun b => a < b),
      ∑ c ∈ s.filter (fun c => b < c), G b c)
      + ∑ b ∈ s.filter (fun b => a < b), G b x := by
  have hx : x ∉ s := max_not_mem hmax
  rw [filter_insert_lt (hmax a ha), sum_insert (by simp [hx])]
  rw [filter_insert_max hmax]
  simp only [sum_empty, zero_add]
  calc
    (∑ b ∈ s.filter (fun b => a < b),
      ∑ c ∈ (insert x s).filter (fun c => b < c), G b c)
        =
      ∑ b ∈ s.filter (fun b => a < b),
        (G b x + ∑ c ∈ s.filter (fun c => b < c), G b c) := by
          apply sum_congr rfl
          intro b hb
          have hbs : b ∈ s := (mem_filter.mp hb).1
          rw [filter_insert_lt (hmax b hbs), sum_insert (by simp [hx])]
          try simp [hx]
    _ = (∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), G b c)
          + ∑ b ∈ s.filter (fun b => a < b), G b x := by
          simp only [sum_add_distrib]
          ring

private lemma sum_lt_four_insert_max (s : Finset ι) (x : ι)
    (G : ι → ι → ι → ι → ℕ) (hmax : ∀ y ∈ s, y < x) :
    (∑ a ∈ insert x s,
      ∑ b ∈ (insert x s).filter (fun b => a < b),
      ∑ c ∈ (insert x s).filter (fun c => b < c),
      ∑ d ∈ (insert x s).filter (fun d => c < d), G a b c d)
      =
    (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
      ∑ c ∈ s.filter (fun c => b < c),
      ∑ d ∈ s.filter (fun d => c < d), G a b c d)
      +
    (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
      ∑ c ∈ s.filter (fun c => b < c), G a b c x) := by
  have hx : x ∉ s := max_not_mem hmax
  rw [sum_insert hx, filter_insert_max hmax]
  simp only [sum_empty, zero_add]
  have hone (a : ι) (ha : a ∈ s) :
      (∑ b ∈ (insert x s).filter (fun b => a < b),
        ∑ c ∈ (insert x s).filter (fun c => b < c),
        ∑ d ∈ (insert x s).filter (fun d => c < d), G a b c d)
        =
      (∑ b ∈ s.filter (fun b => a < b),
        ∑ c ∈ s.filter (fun c => b < c),
        ∑ d ∈ s.filter (fun d => c < d), G a b c d)
        +
      (∑ b ∈ s.filter (fun b => a < b),
        ∑ c ∈ s.filter (fun c => b < c), G a b c x) := by
    rw [filter_insert_lt (hmax a ha), sum_insert (by simp [hx])]
    rw [filter_insert_max hmax]
    simp only [sum_empty, zero_add]
    calc
      (∑ b ∈ s.filter (fun b => a < b),
        ∑ c ∈ (insert x s).filter (fun c => b < c),
        ∑ d ∈ (insert x s).filter (fun d => c < d), G a b c d)
          =
        ∑ b ∈ s.filter (fun b => a < b),
          ((∑ c ∈ s.filter (fun c => b < c),
            ∑ d ∈ s.filter (fun d => c < d), G a b c d)
            + ∑ c ∈ s.filter (fun c => b < c), G a b c x) := by
              apply sum_congr rfl
              intro b hb
              have hbs : b ∈ s := (mem_filter.mp hb).1
              exact sum_lt_tail_two_insert_max s x b
                (fun c d => G a b c d) hmax hbs
      _ = (∑ b ∈ s.filter (fun b => a < b),
            ∑ c ∈ s.filter (fun c => b < c),
            ∑ d ∈ s.filter (fun d => c < d), G a b c d)
            +
          (∑ b ∈ s.filter (fun b => a < b),
            ∑ c ∈ s.filter (fun c => b < c), G a b c x) := by
              simp only [sum_add_distrib]
  calc
    (∑ a ∈ s, ∑ b ∈ (insert x s).filter (fun b => a < b),
      ∑ c ∈ (insert x s).filter (fun c => b < c),
      ∑ d ∈ (insert x s).filter (fun d => c < d), G a b c d)
        =
      ∑ a ∈ s,
        ((∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c),
          ∑ d ∈ s.filter (fun d => c < d), G a b c d)
          +
        (∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), G a b c x)) := by
            apply sum_congr rfl
            intro a ha
            exact hone a ha
    _ = (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c),
          ∑ d ∈ s.filter (fun d => c < d), G a b c d)
          +
        (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), G a b c x) := by
            simp only [sum_add_distrib]

private lemma sum_repeat_pair_insert_max (s : Finset ι) (x : ι)
    (G : ι → ι → ι → ℕ) (hmax : ∀ y ∈ s, y < x) :
    (∑ a ∈ insert x s, ∑ b ∈ (insert x s).erase a,
      ∑ c ∈ ((insert x s).erase a).filter (fun c => b < c), G a b c)
      =
    (∑ a ∈ s, ∑ b ∈ s.erase a,
      ∑ c ∈ (s.erase a).filter (fun c => b < c), G a b c)
      +
    (∑ b ∈ s, ∑ c ∈ s.filter (fun c => b < c), G x b c)
      + (∑ a ∈ s, ∑ b ∈ s.erase a, G a b x) := by
  have hx : x ∉ s := max_not_mem hmax
  rw [sum_insert hx, erase_insert_max hx]
  have htail :
      (∑ a ∈ s, ∑ b ∈ (insert x s).erase a,
        ∑ c ∈ ((insert x s).erase a).filter (fun c => b < c), G a b c)
        =
      (∑ a ∈ s, ∑ b ∈ s.erase a,
        ∑ c ∈ (s.erase a).filter (fun c => b < c), G a b c)
        + ∑ a ∈ s, ∑ b ∈ s.erase a, G a b x := by
    calc
      (∑ a ∈ s, ∑ b ∈ (insert x s).erase a,
        ∑ c ∈ ((insert x s).erase a).filter (fun c => b < c), G a b c)
          =
        ∑ a ∈ s,
          ((∑ b ∈ s.erase a,
            ∑ c ∈ (s.erase a).filter (fun c => b < c), G a b c)
            + ∑ b ∈ s.erase a, G a b x) := by
              apply sum_congr rfl
              intro a ha
              have hax : a ≠ x := by
                intro h
                subst a
                exact hx ha
              rw [erase_insert_other hax]
              have hm : ∀ y ∈ s.erase a, y < x := by
                intro y hy
                exact hmax y (mem_erase.mp hy).2
              exact sum_lt_two_insert_max (s.erase a) x (fun b c => G a b c) hm
      _ = (∑ a ∈ s, ∑ b ∈ s.erase a,
            ∑ c ∈ (s.erase a).filter (fun c => b < c), G a b c)
            + ∑ a ∈ s, ∑ b ∈ s.erase a, G a b x := by
              simp only [sum_add_distrib]
  rw [htail]
  ring

theorem sum_sym_two (s : Finset ι) (F : ι → ι → ℕ)
    (h12 : ∀ a b, F a b = F b a) :
    (∑ a ∈ s, ∑ b ∈ s, F a b)
      = (∑ a ∈ s, F a a)
      + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (a < ·), F a b) := by
  classical
  refine Finset.induction_on_max s ?_ ?_
  · simp
  · intro x s hmax ih
    have hx : x ∉ s := max_not_mem hmax
    have hcross : (∑ a ∈ s, F x a) = ∑ a ∈ s, F a x := by
      apply sum_congr rfl
      intro a ha
      exact h12 x a
    have hlhs :
        (∑ a ∈ insert x s, ∑ b ∈ insert x s, F a b)
          =
        (∑ a ∈ s, ∑ b ∈ s, F a b)
          + F x x + 2 * ∑ a ∈ s, F a x := by
      simp only [sum_insert hx, sum_add_distrib]
      rw [hcross]
      ring
    have hlt := sum_lt_two_insert_max s x F hmax
    rw [hlhs, hlt, ih, sum_insert hx]
    ring

theorem sum_sym_three (s : Finset ι) (F : ι → ι → ι → ℕ)
    (h12 : ∀ a b c, F a b c = F b a c)
    (h23 : ∀ a b c, F a b c = F a c b) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b c)
      = (∑ a ∈ s, F a a a)
      + 3 * (∑ a ∈ s, ∑ b ∈ s.erase a, F a a b)
      + 6 * (∑ a ∈ s, ∑ b ∈ s.filter (a < ·), ∑ c ∈ s.filter (b < ·), F a b c) := by
  classical
  refine Finset.induction_on_max s ?_ ?_
  · simp
  · intro x s hmax ih
    have hx : x ∉ s := max_not_mem hmax
    have hA₁ : (∑ a ∈ s, F x a x) = ∑ a ∈ s, F x x a := by
      apply sum_congr rfl
      intro a ha
      exact h23 x a x
    have hA₂ : (∑ a ∈ s, F a x x) = ∑ a ∈ s, F x x a := by
      apply sum_congr rfl
      intro a ha
      exact (h12 a x x).trans (h23 x a x)
    have hB₁ :
        (∑ a ∈ s, ∑ b ∈ s, F a x b)
          = ∑ a ∈ s, ∑ b ∈ s, F x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact h12 a x b
    have hB₂ :
        (∑ a ∈ s, ∑ b ∈ s, F a b x)
          = ∑ a ∈ s, ∑ b ∈ s, F x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h23 a b x).trans (h12 a x b)
    have hlhs :
        (∑ a ∈ insert x s, ∑ b ∈ insert x s, ∑ c ∈ insert x s, F a b c)
          =
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b c)
          + F x x x
          + 3 * (∑ a ∈ s, F x x a)
          + 3 * (∑ a ∈ s, ∑ b ∈ s, F x a b) := by
      simp only [sum_insert hx, sum_add_distrib]
      rw [hA₁, hA₂, hB₁, hB₂]
      ring
    have herase :=
      sum_erase_two_insert_max s x (fun a b => F a a b) hmax
    have hstrict := sum_lt_three_insert_max s x F hmax
    have hdiag :
        (∑ a ∈ s, F x a a) = ∑ a ∈ s, F a a x := by
      apply sum_congr rfl
      intro a ha
      exact (h12 x a a).trans (h23 a x a)
    have hstrict_perm :
        (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F x a b)
          =
        ∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F a b x := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h12 x a b).trans (h23 a x b)
    have htwo :
        (∑ a ∈ s, ∑ b ∈ s, F x a b)
          =
        (∑ a ∈ s, F a a x)
          + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F a b x) := by
      calc
        (∑ a ∈ s, ∑ b ∈ s, F x a b)
            =
          (∑ a ∈ s, F x a a)
            + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F x a b) :=
              sum_sym_two s (fun a b => F x a b) (fun a b => h23 x a b)
        _ = (∑ a ∈ s, F a a x)
              + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F a b x) := by
              rw [hdiag, hstrict_perm]
    rw [hlhs, ih, sum_insert hx, herase, hstrict, htwo]
    ring

theorem sum_sym_four (s : Finset ι) (F : ι → ι → ι → ι → ℕ)
    (h12 : ∀ a b c d, F a b c d = F b a c d)
    (h23 : ∀ a b c d, F a b c d = F a c b d)
    (h34 : ∀ a b c d, F a b c d = F a b d c) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F a b c d)
      = (∑ a ∈ s, F a a a a)
      + 4 * (∑ a ∈ s, ∑ b ∈ s.erase a, F a a a b)
      + 6 * (∑ a ∈ s, ∑ b ∈ s.filter (a < ·), F a a b b)
      + 12 * (∑ a ∈ s, ∑ b ∈ s.erase a, ∑ c ∈ (s.erase a).filter (b < ·), F a a b c)
      + 24 * (∑ a ∈ s, ∑ b ∈ s.filter (a < ·), ∑ c ∈ s.filter (b < ·),
                ∑ d ∈ s.filter (c < ·), F a b c d) := by
  classical
  refine Finset.induction_on_max s ?_ ?_
  · simp
  · intro x s hmax ih
    have hx : x ∉ s := max_not_mem hmax
    have hA₁ : (∑ a ∈ s, F x x a x) = ∑ a ∈ s, F x x x a := by
      apply sum_congr rfl
      intro a ha
      exact h34 x x a x
    have hA₂ : (∑ a ∈ s, F x a x x) = ∑ a ∈ s, F x x x a := by
      apply sum_congr rfl
      intro a ha
      exact (h23 x a x x).trans (h34 x x a x)
    have hA₃ : (∑ a ∈ s, F a x x x) = ∑ a ∈ s, F x x x a := by
      apply sum_congr rfl
      intro a ha
      exact (h12 a x x x).trans ((h23 x a x x).trans (h34 x x a x))
    have hB₁ :
        (∑ a ∈ s, ∑ b ∈ s, F x a x b)
          = ∑ a ∈ s, ∑ b ∈ s, F x x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact h23 x a x b
    have hB₂ :
        (∑ a ∈ s, ∑ b ∈ s, F x a b x)
          = ∑ a ∈ s, ∑ b ∈ s, F x x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h34 x a b x).trans (h23 x a x b)
    have hB₃ :
        (∑ a ∈ s, ∑ b ∈ s, F a x x b)
          = ∑ a ∈ s, ∑ b ∈ s, F x x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h12 a x x b).trans (h23 x a x b)
    have hB₄ :
        (∑ a ∈ s, ∑ b ∈ s, F a x b x)
          = ∑ a ∈ s, ∑ b ∈ s, F x x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h12 a x b x).trans
        ((h34 x a b x).trans (h23 x a x b))
    have hB₅ :
        (∑ a ∈ s, ∑ b ∈ s, F a b x x)
          = ∑ a ∈ s, ∑ b ∈ s, F x x a b := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h23 a b x x).trans
        ((h12 a x b x).trans
          ((h34 x a b x).trans (h23 x a x b)))
    have hC₁ :
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a x b c)
          = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F x a b c := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      exact h12 a x b c
    have hC₂ :
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b x c)
          = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F x a b c := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      exact (h23 a b x c).trans (h12 a x b c)
    have hC₃ :
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b c x)
          = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F x a b c := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      exact (h34 a b c x).trans
        ((h23 a b x c).trans (h12 a x b c))
    have hlhs :
        (∑ a ∈ insert x s, ∑ b ∈ insert x s,
          ∑ c ∈ insert x s, ∑ d ∈ insert x s, F a b c d)
          =
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F a b c d)
          + F x x x x
          + 4 * (∑ a ∈ s, F x x x a)
          + 6 * (∑ a ∈ s, ∑ b ∈ s, F x x a b)
          + 4 * (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F x a b c) := by
      simp only [sum_insert hx, sum_add_distrib]
      rw [hA₁, hA₂, hA₃, hB₁, hB₂, hB₃, hB₄, hB₅, hC₁, hC₂, hC₃]
      ring
    have herase :=
      sum_erase_two_insert_max s x (fun a b => F a a a b) hmax
    have hpair :=
      sum_lt_two_insert_max s x (fun a b => F a a b b) hmax
    have hrepeat :=
      sum_repeat_pair_insert_max s x (fun a b c => F a a b c) hmax
    have hstrict := sum_lt_four_insert_max s x F hmax
    have hpair_diag :
        (∑ a ∈ s, F x x a a) = ∑ a ∈ s, F a a x x := by
      apply sum_congr rfl
      intro a ha
      exact (h23 x x a a).trans
        ((h12 x a x a).trans
          ((h34 a x x a).trans (h23 a x a x)))
    have htwo :
        (∑ a ∈ s, ∑ b ∈ s, F x x a b)
          =
        (∑ a ∈ s, F a a x x)
          + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F x x a b) := by
      calc
        (∑ a ∈ s, ∑ b ∈ s, F x x a b)
            =
          (∑ a ∈ s, F x x a a)
            + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F x x a b) :=
              sum_sym_two s (fun a b => F x x a b) (fun a b => h34 x x a b)
        _ = (∑ a ∈ s, F a a x x)
              + 2 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), F x x a b) := by
              rw [hpair_diag]
    have htriple_diag :
        (∑ a ∈ s, F x a a a) = ∑ a ∈ s, F a a a x := by
      apply sum_congr rfl
      intro a ha
      exact (h12 x a a a).trans
        ((h23 a x a a).trans (h34 a a x a))
    have htriple_erase :
        (∑ a ∈ s, ∑ b ∈ s.erase a, F x a a b)
          = ∑ a ∈ s, ∑ b ∈ s.erase a, F a a b x := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact (h12 x a a b).trans
        ((h23 a x a b).trans (h34 a a x b))
    have htriple_strict :
        (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), F x a b c)
          =
        ∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
          ∑ c ∈ s.filter (fun c => b < c), F a b c x := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      exact (h12 x a b c).trans
        ((h23 a x b c).trans (h34 a b x c))
    have hthree :
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F x a b c)
          =
        (∑ a ∈ s, F a a a x)
          + 3 * (∑ a ∈ s, ∑ b ∈ s.erase a, F a a b x)
          + 6 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
            ∑ c ∈ s.filter (fun c => b < c), F a b c x) := by
      calc
        (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F x a b c)
            =
          (∑ a ∈ s, F x a a a)
            + 3 * (∑ a ∈ s, ∑ b ∈ s.erase a, F x a a b)
            + 6 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
              ∑ c ∈ s.filter (fun c => b < c), F x a b c) :=
                sum_sym_three s (fun a b c => F x a b c)
                  (fun a b c => h23 x a b c) (fun a b c => h34 x a b c)
        _ = (∑ a ∈ s, F a a a x)
              + 3 * (∑ a ∈ s, ∑ b ∈ s.erase a, F a a b x)
              + 6 * (∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b),
                ∑ c ∈ s.filter (fun c => b < c), F a b c x) := by
                rw [htriple_diag, htriple_erase, htriple_strict]
    rw [hlhs, ih, sum_insert hx, herase, hpair, hrepeat, hstrict, htwo, hthree]
    ring

end SymSum

/-! ## 2b. Ordered injective four-tuples versus four-element subsets -/

section Fibre
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a four-element subset `S`, exactly `24` injective maps `Fin 4 → V` have image `S`. -/
theorem card_fibre_four (S : Finset V) (hS : S.card = 4) :
    ((univ : Finset (Fin 4 → V)).filter
        (fun f => Function.Injective f ∧ univ.image f = S)).card = 24 := by
  have hmem : ∀ f : Fin 4 → V, univ.image f = S → ∀ i, f i ∈ S := by
    intro f himg i
    rw [← himg]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hback : ∀ e : Fin 4 ↪ ↥S,
      Function.Injective (fun i => ((e i : V))) ∧
        univ.image (fun i => ((e i : V))) = S := by
    intro e
    have hinj : Function.Injective (fun i => ((e i : V))) :=
      Subtype.val_injective.comp e.injective
    have hc : (univ.image (fun i => ((e i : V)))).card = 4 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    refine ⟨hinj, Finset.eq_of_subset_of_card_le ?_ ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (e i).2
    · omega
  have key : {f : Fin 4 → V // Function.Injective f ∧ univ.image f = S} ≃ (Fin 4 ↪ ↥S) :=
    ⟨fun f => ⟨fun i => ⟨f.1 i, hmem f.1 f.2.2 i⟩,
        fun i j hij => f.2.1 (congrArg Subtype.val hij)⟩,
     fun e => ⟨fun i => ((e i : V)), hback e⟩,
     fun f => Subtype.ext (funext fun i => rfl),
     fun e => Function.Embedding.ext fun i => Subtype.ext rfl⟩
  have h24 : Nat.descFactorial 4 4 = 24 := by decide
  have hemb : Fintype.card (Fin 4 ↪ ↥S) = 24 := by
    rw [Fintype.card_embedding_eq, Fintype.card_coe, hS, Fintype.card_fin, h24]
  have hcard : Fintype.card {f : Fin 4 → V // Function.Injective f ∧ univ.image f = S} = 24 :=
    (Fintype.card_congr key).trans hemb
  have hsub : Fintype.card {f : Fin 4 → V // Function.Injective f ∧ univ.image f = S}
      = ((univ : Finset (Fin 4 → V)).filter
          (fun f => Function.Injective f ∧ univ.image f = S)).card :=
    Fintype.card_subtype _
  exact hsub.symm.trans hcard

/-- Summing a function of the image over injective four-tuples is `24` times the sum
over four-element subsets. -/
theorem sum_inj_four (h : Finset V → ℕ) :
    (∑ f ∈ (univ : Finset (Fin 4 → V)).filter (fun f => Function.Injective f),
        h (univ.image f))
      = 24 * ∑ S ∈ (univ : Finset V).powersetCard 4, h S := by
  have hmaps : ∀ f ∈ (univ : Finset (Fin 4 → V)).filter (fun f => Function.Injective f),
      univ.image f ∈ (univ : Finset V).powersetCard 4 := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hf.2, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps h, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro S hS
  rw [Finset.mem_powersetCard] at hS
  rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.filter_filter, card_fibre_four S hS.2]

/-- At `h = 1`: the number of injective four-tuples is `24 · C(N,4)`. -/
theorem card_inj_four :
    ((univ : Finset (Fin 4 → V)).filter (fun f => Function.Injective f)).card
      = 24 * (Fintype.card V).choose 4 := by
  have h := sum_inj_four (V := V) (fun _ => 1)
  simpa [Finset.card_powersetCard, Finset.card_univ] using h

end Fibre

/-! ## 3. Symmetry of the six-pair predicate -/

variable {A : Fin m → Fin m → Bool}

lemma sixEq_swap12 (hA : ∀ i j, A i j = A j i) (col : Bool) (a b c d : Fin m) :
    sixEq A col a b c d = sixEq A col b a c d := by
  simp only [sixEq, hA b a, Bool.and_comm, Bool.and_left_comm]

lemma sixEq_swap23 (hA : ∀ i j, A i j = A j i) (col : Bool) (a b c d : Fin m) :
    sixEq A col a b c d = sixEq A col a c b d := by
  simp only [sixEq, hA c b, Bool.and_comm, Bool.and_left_comm]

lemma sixEq_swap34 (hA : ∀ i j, A i j = A j i) (col : Bool) (a b c d : Fin m) :
    sixEq A col a b c d = sixEq A col a b d c := by
  simp only [sixEq, hA d c, Bool.and_comm, Bool.and_left_comm]

/-! ## 4. Result 1 — checker correctness -/

/-- The evaluator's grouped count for one colour: the five index-multiplicity patterns
`4`, `3+1`, `2+2`, `2+1+1`, `1+1+1+1` with multiplicities `1, 4, 6, 12, 24`. -/
def grouped (A : Fin m → Fin m → Bool) (w : Fin m → ℕ) (col : Bool) : ℕ :=
      (∑ i, w i ^ 4 * (sixEq A col i i i i).toNat)
  +  4 * (∑ i, ∑ j ∈ univ.erase i, w i ^ 3 * w j * (sixEq A col i i i j).toNat)
  +  6 * (∑ i, ∑ j ∈ univ.filter (i < ·), w i ^ 2 * w j ^ 2 * (sixEq A col i i j j).toNat)
  + 12 * (∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).filter (j < ·),
            w i ^ 2 * w j * w k * (sixEq A col i i j k).toNat)
  + 24 * (∑ i, ∑ j ∈ univ.filter (i < ·), ∑ k ∈ univ.filter (j < ·),
            ∑ l ∈ univ.filter (k < ·), w i * w j * w k * w l * (sixEq A col i j k l).toNat)

/-- **Checker correctness, one colour.**  The grouped count equals the literal sum over
all ordered four-tuples of block indices. -/
theorem literal_eq_grouped (hA : ∀ i j, A i j = A j i) (w : Fin m → ℕ) (col : Bool) :
    (∑ i, ∑ j, ∑ k, ∑ l, w i * w j * w k * w l * (sixEq A col i j k l).toNat)
      = grouped A w col := by
  have key := sum_sym_four (univ : Finset (Fin m))
    (fun a b c d => w a * w b * w c * w d * (sixEq A col a b c d).toNat)
    (by intro a b c d; simp only [sixEq_swap12 hA col a b c d]; ring)
    (by intro a b c d; simp only [sixEq_swap23 hA col a b c d]; ring)
    (by intro a b c d; simp only [sixEq_swap34 hA col a b c d]; ring)
  rw [key]
  unfold grouped
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · congr 1
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
      · congr 1
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    · congr 1
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring

/-- **Checker correctness.**  `Pnum` — README's literal ordered four-tuple sum with
repetitions included — equals the evaluator's grouped red count plus grouped blue count. -/
theorem Pnum_eq_grouped (hA : ∀ i j, A i j = A j i) (w : Fin m → ℕ) :
    Pnum A w = grouped A w true + grouped A w false := by
  rw [← literal_eq_grouped hA w true, ← literal_eq_grouped hA w false]
  unfold Pnum monoW
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## 5. Tuple bookkeeping -/

/-- `Fin 4 → V` is `V⁴`. -/
def tup4 {V : Type*} : (Fin 4 → V) ≃ V × V × V × V where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv := by
    intro f
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨a, b, c, d⟩
    rfl

lemma sum_fun_fin4 {V M : Type*} [Fintype V] [AddCommMonoid M] (g : V → V → V → V → M) :
    (∑ f : Fin 4 → V, g (f 0) (f 1) (f 2) (f 3))
      = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  have h := Equiv.sum_comp (tup4 (V := V))
    (fun p : V × V × V × V => g p.1 p.2.1 p.2.2.1 p.2.2.2)
  rw [show (∑ f : Fin 4 → V, g (f 0) (f 1) (f 2) (f 3))
        = ∑ f : Fin 4 → V, (fun p : V × V × V × V => g p.1 p.2.1 p.2.2.1 p.2.2.2)
            (tup4 f) from rfl, h]
  simp [Fintype.sum_prod_type]

/-- Fibre sum over a blow-up. -/
lemma sum_blow_nat (v : Fin m → ℕ) (g : Fin m → ℕ) :
    (∑ u : Blow v, g u.1) = ∑ i, v i * g i := by
  rw [Fintype.sum_sigma]
  simp

/-! ## 6. L1 : the full ordered vertex sum is `Pnum` -/

lemma sum_all_tuples (A : Fin m → Fin m → Bool) (v : Fin m → ℕ) :
    (∑ f : Fin 4 → Blow v, monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1) = Pnum A v := by
  rw [sum_fun_fin4 (fun a b c d : Blow v => monoW A a.1 b.1 c.1 d.1)]
  unfold Pnum
  rw [sum_blow_nat v
    (fun i => ∑ b : Blow v, ∑ c : Blow v, ∑ d : Blow v, monoW A i b.1 c.1 d.1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_blow_nat v (fun j => ∑ c : Blow v, ∑ d : Blow v, monoW A i j c.1 d.1),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_blow_nat v (fun k => ∑ d : Blow v, monoW A i j k d.1),
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_blow_nat v (fun l => monoW A i j k l),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## 7. L2 : injective tuples count monochromatic four-sets, 24 to 1 -/

lemma monoW_le_one (A : Fin m → Fin m → Bool) (i j k l : Fin m) :
    monoW A i j k l ≤ 1 := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  unfold monoW sixEq
  cases A i j <;> simp <;> exact hb _

lemma monoW_eq_ite (hA : ∀ i j, A i j = A j i) {v : Fin m → ℕ}
    (f : Fin 4 → Blow v) (hf : Function.Injective f) :
    monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1
      = if MonoSet A (univ.image f) then 1 else 0 := by
  have hmem : ∀ a : Fin 4, f a ∈ univ.image f := fun a =>
    Finset.mem_image_of_mem f (Finset.mem_univ a)
  by_cases hmono : MonoSet A (univ.image f)
  · rw [if_pos hmono]
    obtain ⟨c, hc⟩ := hmono
    have key : ∀ a b : Fin 4, a ≠ b → A (f a).1 (f b).1 = c := by
      intro a b hab
      exact hc (f a) (hmem a) (f b) (hmem b) (fun hh => hab (hf hh))
    have k01 := key 0 1 (by decide)
    have k02 := key 0 2 (by decide)
    have k03 := key 0 3 (by decide)
    have k12 := key 1 2 (by decide)
    have k13 := key 1 3 (by decide)
    have k23 := key 2 3 (by decide)
    unfold monoW sixEq
    cases c <;> simp [k01, k02, k03, k12, k13, k23]
  · rw [if_neg hmono]
    have hfalse : ∀ col : Bool, sixEq A col (f 0).1 (f 1).1 (f 2).1 (f 3).1 = false := by
      intro col
      by_contra hcon
      apply hmono
      refine ⟨col, ?_⟩
      have hsix : sixEq A col (f 0).1 (f 1).1 (f 2).1 (f 3).1 = true := by
        cases hh : sixEq A col (f 0).1 (f 1).1 (f 2).1 (f 3).1
        · exact absurd hh hcon
        · rfl
      unfold sixEq at hsix
      simp only [Bool.and_eq_true, beq_iff_eq] at hsix
      obtain ⟨⟨⟨⟨⟨p01, p02⟩, p03⟩, p12⟩, p13⟩, p23⟩ := hsix
      have p10 : A (f 1).1 (f 0).1 = col := by rw [hA]; exact p01
      have p20 : A (f 2).1 (f 0).1 = col := by rw [hA]; exact p02
      have p30 : A (f 3).1 (f 0).1 = col := by rw [hA]; exact p03
      have p21 : A (f 2).1 (f 1).1 = col := by rw [hA]; exact p12
      have p31 : A (f 3).1 (f 1).1 = col := by rw [hA]; exact p13
      have p32 : A (f 3).1 (f 2).1 = col := by rw [hA]; exact p23
      intro u hu x hx hux
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      have hab : a ≠ b := fun h => hux (by rw [h])
      fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption
    unfold monoW
    rw [hfalse true, hfalse false]
    rfl

lemma sum_inj_tuples (hA : ∀ i j, A i j = A j i) (v : Fin m → ℕ) :
    (∑ f ∈ (univ : Finset (Fin 4 → Blow v)).filter (fun f => Function.Injective f),
        monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1)
      = 24 * M4 A v := by
  have step : (∑ f ∈ (univ : Finset (Fin 4 → Blow v)).filter
        (fun f => Function.Injective f), monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1)
      = ∑ f ∈ (univ : Finset (Fin 4 → Blow v)).filter (fun f => Function.Injective f),
          (fun S : Finset (Blow v) => if MonoSet A S then 1 else 0) (univ.image f) := by
    refine Finset.sum_congr rfl fun f hf => ?_
    exact monoW_eq_ite hA f (Finset.mem_filter.1 hf).2
  rw [step, sum_inj_four (V := Blow v) (fun S => if MonoSet A S then 1 else 0)]
  congr 1
  unfold M4
  rw [Finset.card_filter]

/-! ## 8. Counting arithmetic -/

lemma choose4_poly (M : ℕ) :
    24 * (M + 4).choose 4 = (M + 1) * (M + 2) * (M + 3) * (M + 4) := by
  have e1 : (M + 2).choose 2 * 2 = (M + 2) * (M + 1).choose 1 := by
    have h : (M + 1 + 1) * (M + 1).choose 1 = (M + 1 + 1).choose (1 + 1) * (1 + 1) := by
      exact Nat.add_one_mul_choose_eq (M + 1) 1
    simpa using h.symm
  have e2 : (M + 3).choose 3 * 3 = (M + 3) * (M + 2).choose 2 := by
    have h : (M + 2 + 1) * (M + 2).choose 2 = (M + 2 + 1).choose (2 + 1) * (2 + 1) := by
      exact Nat.add_one_mul_choose_eq (M + 2) 2
    simpa using h.symm
  have e3 : (M + 4).choose 4 * 4 = (M + 4) * (M + 3).choose 3 := by
    have h : (M + 3 + 1) * (M + 3).choose 3 = (M + 3 + 1).choose (3 + 1) * (3 + 1) := by
      exact Nat.add_one_mul_choose_eq (M + 3) 3
    simpa using h.symm
  have e0 : (M + 1).choose 1 = M + 1 := Nat.choose_one_right _
  rw [e0] at e1
  calc 24 * (M + 4).choose 4 = 6 * ((M + 4).choose 4 * 4) := by ring
    _ = 6 * ((M + 4) * (M + 3).choose 3) := by rw [e3]
    _ = 2 * (M + 4) * ((M + 3).choose 3 * 3) := by ring
    _ = 2 * (M + 4) * ((M + 3) * (M + 2).choose 2) := by rw [e2]
    _ = (M + 4) * (M + 3) * ((M + 2).choose 2 * 2) := by ring
    _ = (M + 4) * (M + 3) * ((M + 2) * (M + 1)) := by rw [e1]
    _ = (M + 1) * (M + 2) * (M + 3) * (M + 4) := by ring

/-- The number of four-tuples with a repeated entry is at most `6 N³` — the source's
union bound over the six pairs, obtained here from the exact injective count. -/
lemma coll_bound {N D E : ℕ} (hQ : 4 ≤ N) (hDval : D = 24 * N.choose 4)
    (hsum : D + E = N ^ 4) : E ≤ 6 * N ^ 3 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 4 := ⟨N - 4, by omega⟩
  rw [choose4_poly] at hDval
  subst hDval
  nlinarith [hsum]

/-! ## 9. The rational core of the bound -/

lemma ratio_bound {x y d e n : ℚ} (hd : 0 < d) (hn : 0 < n)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxd : x ≤ d) (hye : y ≤ e)
    (hsum : d + e = n ^ 4) (hb : e ≤ 6 * n ^ 3) :
    |x / d - (x + y) / n ^ 4| ≤ 6 / n := by
  have hn4 : (0 : ℚ) < n ^ 4 := by positivity
  have he0 : (0 : ℚ) ≤ e := le_trans hy0 hye
  have hde : (0 : ℚ) < d + e := by rw [hsum]; exact hn4
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hn0 : n ≠ 0 := ne_of_gt hn
  have key : x / d - (x + y) / n ^ 4 = (x * e - d * y) / (d * n ^ 4) := by
    rw [← hsum]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℚ) < d * n ^ 4)]
  have h1 : |x * e - d * y| ≤ d * e := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hx0 he0, mul_nonneg hd.le hy0,
      mul_le_mul_of_nonneg_right hxd he0, mul_le_mul_of_nonneg_left hye hd.le]
  calc |x * e - d * y| / (d * n ^ 4) ≤ (d * e) / (d * n ^ 4) := by gcongr
    _ = e / n ^ 4 := by field_simp
    _ ≤ (6 * n ^ 3) / n ^ 4 := by gcongr
    _ = 6 / n := by field_simp; try ring

/-! ## 10. Result 2 — the lifting bound -/

/-- **Lifting bound, general weights.**  For any weight vector `v` with `Q = ∑ vᵢ ≥ 4`,
the monochromatic `K₄` density of the weighted complete blow-up is within `6/Q` of
`P(A,v)`. -/
theorem density_sub_P_abs_le (hA : ∀ i j, A i j = A j i) (v : Fin m → ℕ)
    (hQ : 4 ≤ Qw v) :
    |(M4 A v : ℚ) / ((Qw v).choose 4 : ℚ) - Pval A v| ≤ 6 / (Qw v : ℚ) := by
  classical
  have hcard : Fintype.card (Blow v) = Qw v := card_blow v
  -- integer counts
  set injs : Finset (Fin 4 → Blow v) :=
    (univ : Finset (Fin 4 → Blow v)).filter (fun f => Function.Injective f) with hinjs
  set nis : Finset (Fin 4 → Blow v) :=
    (univ : Finset (Fin 4 → Blow v)).filter (fun f => ¬ Function.Injective f) with hnis
  set D : ℕ := injs.card with hD
  set E : ℕ := nis.card with hE
  set Sinj : ℕ := ∑ f ∈ injs, monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1 with hSinj
  set Scoll : ℕ := ∑ f ∈ nis, monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1 with hScoll
  -- D = 24 * C(N,4)
  have hDval : D = 24 * (Qw v).choose 4 := by
    rw [hD, hinjs, card_inj_four, hcard]
  -- Sinj = 24 * M4
  have hSinjval : Sinj = 24 * M4 A v := sum_inj_tuples hA v
  -- splitting
  have hsplit : Sinj + Scoll = Pnum A v := by
    rw [hSinj, hScoll, hinjs, hnis, Finset.sum_filter_add_sum_filter_not]
    exact sum_all_tuples A v
  have hcardsplit : D + E = (Qw v) ^ 4 := by
    rw [hD, hE, hinjs, hnis, Finset.card_filter_add_card_filter_not]
    simp [hcard]
  have hSinjle : Sinj ≤ D := by
    rw [hSinj, hD]
    calc (∑ f ∈ injs, monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1)
        ≤ ∑ _f ∈ injs, 1 := Finset.sum_le_sum fun f _ => monoW_le_one A _ _ _ _
      _ = injs.card := by simp
  have hScollle : Scoll ≤ E := by
    rw [hScoll, hE]
    calc (∑ f ∈ nis, monoW A (f 0).1 (f 1).1 (f 2).1 (f 3).1)
        ≤ ∑ _f ∈ nis, 1 := Finset.sum_le_sum fun f _ => monoW_le_one A _ _ _ _
      _ = nis.card := by simp
  have hEle : E ≤ 6 * (Qw v) ^ 3 := coll_bound hQ hDval hcardsplit
  have hchoosepos : 0 < (Qw v).choose 4 := Nat.choose_pos hQ
  have hDpos : 0 < D := by rw [hDval]; omega
  -- move to ℚ
  have hqpos : 0 < Qw v := by omega
  have hq : (0 : ℚ) < ((Qw v : ℕ) : ℚ) := by exact_mod_cast hqpos
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hDpos
  have hsumq : (D : ℚ) + (E : ℚ) = ((Qw v : ℕ) : ℚ) ^ 4 := by exact_mod_cast hcardsplit
  have hbq : (E : ℚ) ≤ 6 * ((Qw v : ℕ) : ℚ) ^ 3 := by exact_mod_cast hEle
  have hxd : (Sinj : ℚ) ≤ (D : ℚ) := by exact_mod_cast hSinjle
  have hye : (Scoll : ℚ) ≤ (E : ℚ) := by exact_mod_cast hScollle
  have main := ratio_bound (x := (Sinj : ℚ)) (y := (Scoll : ℚ)) (d := (D : ℚ))
    (e := (E : ℚ)) (n := ((Qw v : ℕ) : ℚ)) hDq hq (by positivity) (by positivity)
    hxd hye hsumq hbq
  -- rewrite the two ratios
  have hP : ((Sinj : ℚ) + (Scoll : ℚ)) / ((Qw v : ℕ) : ℚ) ^ 4 = Pval A v := by
    have h : ((Sinj : ℚ) + (Scoll : ℚ)) = ((Pnum A v : ℕ) : ℚ) := by exact_mod_cast hsplit
    rw [h]
    rfl
  have hM : (Sinj : ℚ) / (D : ℚ) = (M4 A v : ℚ) / (((Qw v).choose 4 : ℕ) : ℚ) := by
    have hc : (0 : ℚ) < ((((Qw v).choose 4 : ℕ)) : ℚ) := by exact_mod_cast hchoosepos
    rw [hSinjval, hDval]
    push_cast
    field_simp
    try ring
  rw [← hP, ← hM]
  exact main

/-! ## 11. Homogeneity and the blow-up statement -/

lemma Qw_smul (t : ℕ) (w : Fin m → ℕ) : Qw (fun i => t * w i) = t * Qw w := by
  unfold Qw
  rw [Finset.mul_sum]

lemma Pnum_smul (t : ℕ) (w : Fin m → ℕ) :
    Pnum A (fun i => t * w i) = t ^ 4 * Pnum A w := by
  unfold Pnum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma Pval_smul (t : ℕ) (w : Fin m → ℕ) (ht : 0 < t) (hQ : 0 < Qw w) :
    Pval A (fun i => t * w i) = Pval A w := by
  unfold Pval
  rw [Pnum_smul, Qw_smul]
  have htq : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have h1 : ((t : ℚ)) ≠ 0 := ne_of_gt htq
  have h2 : ((Qw w : ℕ) : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (Qw w : ℚ) := by exact_mod_cast hQ
    exact ne_of_gt this
  push_cast
  field_simp
  try ring

/-- **The lifting bound, as stated in `LIFTING.md`.**  For the blow-up `G_t` of the
template with weights `w` — block `i` expanded to `t * wᵢ` vertices —
`|M₄(G_t)/C(tQ,4) − P| ≤ 6/(tQ)` whenever `tQ ≥ 4`. -/
theorem lifting_bound (hA : ∀ i j, A i j = A j i) (w : Fin m → ℕ) (t : ℕ)
    (ht : 0 < t) (hQ : 0 < Qw w) (hN : 4 ≤ t * Qw w) :
    |(M4 A (fun i => t * w i) : ℚ) / (((t * Qw w).choose 4 : ℕ) : ℚ) - Pval A w|
      ≤ 6 / ((t * Qw w : ℕ) : ℚ) := by
  have h := density_sub_P_abs_le hA (fun i => t * w i) (by rw [Qw_smul]; exact hN)
  rw [Qw_smul] at h
  rw [Pval_smul t w ht hQ] at h
  exact h

/-- **Convergence, with no topology.**  The blow-up density converges to `P(A,w)`. -/
theorem density_tendsto (hA : ∀ i j, A i j = A j i) (w : Fin m → ℕ) (hQ : 0 < Qw w)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ T : ℕ, 0 < T ∧ ∀ t ≥ T,
      |(M4 A (fun i => t * w i) : ℚ) / (((t * Qw w).choose 4 : ℕ) : ℚ) - Pval A w| ≤ ε := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  obtain ⟨T0, hT0⟩ := exists_nat_gt (6 / ε)
  have hkey : (6 : ℚ) < (T0 : ℚ) * ε := by
    have h1 : 6 / ε * ε < (T0 : ℚ) * ε := mul_lt_mul_of_pos_right hT0 hε
    have h2 : 6 / ε * ε = (6 : ℚ) := by field_simp
    linarith
  refine ⟨max 4 T0 + 1, by omega, ?_⟩
  intro t ht
  have ht4 : 4 ≤ t := by omega
  have htpos : 0 < t := by omega
  have hNle : 4 ≤ t * Qw w := le_trans ht4 (Nat.le_mul_of_pos_right t hQ)
  have hmain := lifting_bound hA w t htpos hQ hNle
  refine le_trans hmain ?_
  have hNq : (0 : ℚ) < ((t * Qw w : ℕ) : ℚ) := by
    have : 0 < t * Qw w := by omega
    exact_mod_cast this
  have hT0t : (T0 : ℚ) ≤ (t : ℚ) := by
    have : T0 ≤ t := by omega
    exact_mod_cast this
  have hle : (t : ℚ) ≤ ((t * Qw w : ℕ) : ℚ) := by
    have : t ≤ t * Qw w := Nat.le_mul_of_pos_right t hQ
    exact_mod_cast this
  have h6 : (6 : ℚ) ≤ ε * ((t * Qw w : ℕ) : ℚ) := by nlinarith [hkey, hT0t, hle, hε.le]
  have hNne : ((t * Qw w : ℕ) : ℚ) ≠ 0 := ne_of_gt hNq
  calc (6 : ℚ) / ((t * Qw w : ℕ) : ℚ)
      ≤ (ε * ((t * Qw w : ℕ) : ℚ)) / ((t * Qw w : ℕ) : ℚ) := by gcongr
    _ = ε := by field_simp


/-! ## 12. End-to-end sanity checks against the source documents -/

section Validation

/-- The README's illustrative certificate: `weights = [1,1]`, `red_rows = ["01","10"]`.
The diagonal is `0` (each block is a blue clique) and the single inter-block edge is red. -/
def exA : Fin 2 → Fin 2 → Bool := ![![false, true], ![true, false]]

/-- Its weights. -/
def exW : Fin 2 → ℕ := ![1, 1]

example : ∀ i j, exA i j = exA j i := by decide

/-- README: "The example above has `P = 1/8`." -/
example : Pnum exA exW = 2 := by decide

example : Qw exW = 2 := by decide

/-- README: "The example above has `P = 1/8`."  This ties `sixEq`, `monoW`, `Pnum`, `Qw`
and `Pval` together and checks them against the number the source states. -/
theorem readme_example_P : Pval exA exW = 1 / 8 := by
  unfold Pval
  rw [show Pnum exA exW = 2 from by decide, show Qw exW = 2 from by decide]
  norm_num

/-- The grouped counter agrees with the literal sum on this certificate, both colours. -/
example : grouped exA exW true = 0 := by decide
example : grouped exA exW false = 2 := by decide

end Validation


/-! ### Non-vacuity of `M₄`

These pin down that `M4` counts four-element SUBSETS (not ordered tuples), and that the
DIAGONAL really does colour edges between distinct vertices of one block. -/

/-- A single block, declared a red clique by its diagonal. -/
def redA : Fin 1 → Fin 1 → Bool := ![![true]]

example : ∀ i j, redA i j = redA j i := by decide

/-- Five vertices inside one red-clique block: every one of the `C(5,4) = 5` four-subsets
is monochromatic.  If `M4` were counting ordered tuples this would be `120`; if the
diagonal were ignored (treated as a non-edge) it would be `0`. -/
example : M4 redA ![5] = 5 := by decide

/-- Four vertices in one red-clique block: the unique four-subset is monochromatic. -/
example : M4 redA ![4] = 1 := by decide

/-- The README example blown up to two vertices per block has NO monochromatic four-set:
each block is a blue clique but the inter-block edges are red. -/
example : M4 exA ![2, 2] = 0 := by decide

end Lea.RamseyLifting
