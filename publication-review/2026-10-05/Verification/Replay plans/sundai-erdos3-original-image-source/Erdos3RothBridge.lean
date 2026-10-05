import Erdos3ThreeCase

/-!
# Bridge: Formal Conjectures' `maxCard 3` is Mathlib's `rothNumberNat`

Formal Conjectures measures three-term-progression-free sets with
`Set.IsAPOfLengthFree.maxCard 3 N` (subsets of `{1, …, N}`), while Mathlib and
the APAP project use `ThreeAPFree` and `rothNumberNat` (subsets of
`{0, …, N - 1}`). This module proves the two notions agree, so a Roth-number
bound stated in Mathlib's terms transfers to `erdos_3.variants.kelley_meka` and
then, via `Erdos3ThreeCase`, to `erdos_3.variants.three`. No bound is proved here.
-/

namespace Erdos3RothBridge

open Asymptotics Filter Erdos3ThreeCase

-- ## the predicates

theorem a_three_term_ap {s : Set ℕ} (hs : s.IsAPOfLengthFree 3) {x d : ℕ} (hd : d ≠ 0)
    (h0 : x ∈ s) (h1 : x + d ∈ s) (h2 : x + 2 * d ∈ s) : False := by
  classical
  let f : Fin 3 → ℕ := fun i => x + i.val • d
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f, Nat.nsmul_eq_mul] at hij
    have hij' : i.val = j.val := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd)
      (by omega)
    exact Fin.ext hij'
  have hsubA : Set.range f ⊆ s := by
    rintro y ⟨i, rfl⟩
    fin_cases i
    · simpa [f] using h0
    · simpa [f] using h1
    · simpa [f] using h2
  have : Fintype (Set.range f) := Fintype.ofFinite _
  have hcard3 : ENat.card (Set.range f) = ((3 : ℕ) : ℕ∞) := by
    simp only [ENat.card_eq_coe_fintype_card, Set.card_range_of_injective hf,
      Fintype.card_fin]
  have heq3 : Set.range f = {y | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < ((3 : ℕ) : ℕ∞), x + n • d = y} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      have hn' : n < 3 := by exact_mod_cast hn
      exact ⟨⟨n, hn'⟩, rfl⟩
  have hAP : (Set.range f).IsAPOfLength ((3 : ℕ) : ℕ∞) := ⟨x, d, hcard3, heq3⟩
  have hle := hs (Set.range f) hsubA hAP
  exact absurd hle (by norm_num)

/-- Avoiding non-trivial three-term progressions in the Formal Conjectures sense is
Mathlib's `ThreeAPFree`. -/
theorem isAPOfLengthFree_three_iff {s : Set ℕ} : s.IsAPOfLengthFree 3 ↔ ThreeAPFree s := by
  constructor
  · intro hs a ha b hb c hc habc
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine a_three_term_ap hs (x := a) (d := b - a) (by omega) ha ?_ ?_
      · have : a + (b - a) = b := by omega
        rwa [this]
      · have : a + 2 * (b - a) = c := by omega
        rwa [this]
    · refine a_three_term_ap hs (x := c) (d := b - c) (by omega) hc ?_ ?_
      · have : c + (b - c) = b := by omega
        rwa [this]
      · have : c + 2 * (b - c) = a := by omega
        rwa [this]
  · intro hs t ht hAP
    obtain ⟨a, d, hcard, heq⟩ := hAP
    exfalso
    rcases eq_or_ne d 0 with hd0 | hd
    · subst hd0
      have hsub : t ⊆ ({a} : Set ℕ) := by
        rw [heq]; rintro x ⟨n, hn, rfl⟩; simp
      have h1 : t.encard ≤ 1 := (Set.encard_mono hsub).trans_eq (Set.encard_singleton a)
      rw [show t.encard = (3 : ℕ∞) from hcard] at h1
      exact absurd h1 (by norm_num)
    · have hmem : ∀ n : ℕ, n < 3 → a + n * d ∈ s := by
        intro n hn
        apply ht
        rw [heq]
        exact ⟨n, by exact_mod_cast hn, by simp⟩
      have h0 := hmem 0 (by norm_num)
      have h1 := hmem 1 (by norm_num)
      have h2 := hmem 2 (by norm_num)
      have key := hs h0 h1 h2 (by ring)
      omega

-- ## the extremal functions

/-- `maxCard 3 N` is Mathlib's Roth number of `{1, …, N}`. -/
theorem maxCard_three_eq_addRothNumber (N : ℕ) :
    Set.IsAPOfLengthFree.maxCard 3 N = addRothNumber (Finset.Icc 1 N) := by
  unfold Set.IsAPOfLengthFree.maxCard
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨t, ht, hcard, hfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
    exact ⟨t, ht, isAPOfLengthFree_three_iff.mpr hfree, hcard⟩
  · rintro n ⟨S, hS, hSfree, rfl⟩
    exact (isAPOfLengthFree_three_iff.mp hSfree).le_addRothNumber hS

/-- `maxCard 3 N = rothNumberNat N`: shifting `{1, …, N}` to `{0, …, N - 1}`. -/
theorem maxCard_three_eq_rothNumberNat (N : ℕ) :
    Set.IsAPOfLengthFree.maxCard 3 N = rothNumberNat N := by
  rw [maxCard_three_eq_addRothNumber]
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x; simp
  rw [hset, addRothNumber_Ico]
  simp

-- ## transfer to the Formal Conjectures variants

/-- Formal Conjectures' `kelley_meka` variant, restated with Mathlib's `rothNumberNat`. -/
theorem kelleyMeka_iff_rothNumberNat : KelleyMeka ↔ ∃ β > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun N ↦ (rothNumberNat N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β) := by
  unfold KelleyMeka
  have c_hfun : (fun N : ℕ ↦ (r 3 N : ℝ)) = fun N : ℕ ↦ (rothNumberNat N : ℝ) := by
    funext N
    exact_mod_cast maxCard_three_eq_rothNumberNat N
  rw [c_hfun]

/-- A Kelley–Meka bound stated with Mathlib's `rothNumberNat` gives `erdos_3.variants.three`. -/
theorem three_of_rothNumberNat (h : ∃ β > (0 : ℝ), ∃ c > (0 : ℝ),
    (fun N ↦ (rothNumberNat N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.exp (-c * Real.log N ^ β)) :
    ThreeCase :=
  three_of_kelleyMeka (kelleyMeka_iff_rothNumberNat.mpr h)

/-- The shape of a corrected APAP integer theorem, with the constants fixed before `A`
and `N`, gives `erdos_3.variants.three`. -/
theorem three_of_uniform_finset_bound (h : ∃ β > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C : ℝ,
    ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.range N → ThreeAPFree (A : Set ℕ) →
      (A.card : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ β)) :
    ThreeCase := by
  obtain ⟨β, hβ, c, hc, C, hC⟩ := h
  apply three_of_rothNumberNat
  refine ⟨β, hβ, c, hc, ?_⟩
  refine Asymptotics.IsBigO.of_bound |C| (Filter.Eventually.of_forall fun N => ?_)
  obtain ⟨A, hAsub, hAcard, hAfree⟩ := rothNumberNat_spec N
  have hbound := hC N A hAsub hAfree
  rw [hAcard] at hbound
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log N ^ β) := by positivity
  have hcard_nonneg : (0 : ℝ) ≤ (rothNumberNat N : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hcard_nonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc (rothNumberNat N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ β) := hbound
    _ = C * ((N : ℝ) * Real.exp (-c * Real.log N ^ β)) := by ring
    _ ≤ |C| * ((N : ℝ) * Real.exp (-c * Real.log N ^ β)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hnonneg

#print axioms a_three_term_ap
#print axioms isAPOfLengthFree_three_iff
#print axioms maxCard_three_eq_addRothNumber
#print axioms maxCard_three_eq_rothNumberNat
#print axioms kelleyMeka_iff_rothNumberNat
#print axioms three_of_rothNumberNat
#print axioms three_of_uniform_finset_bound

end Erdos3RothBridge
