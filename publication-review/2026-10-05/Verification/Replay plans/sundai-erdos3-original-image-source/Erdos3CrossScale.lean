import Erdos3Dyadic

/-!
# Separated blocks and the extremal-function form of Erdős 3

This module does not prove Erdős 3. For every fixed length `k ≥ 4` it proves
that reciprocal summability of all `k`-AP-free sets is equivalent to
summability of the imported extremal function `maxCard k` along powers of two.
It then shows the exact elaborated hill is equivalent to that family of
summability statements; `hill_statement_iff_extremal` restates the left side
verbatim from the frozen hill, including `answer(sorry)`. The extremal
summability itself remains open. Helper names beginning `a_` and `e_` are
local lemmas for the separated-block and lower-bound arguments.
-/

namespace Erdos3CrossScale

open Erdos3Blocks

/-- The imported extremal function: the largest `k`-AP-free subset of `{1, …, N}`. -/
noncomputable abbrev r (k N : ℕ) : ℕ := Set.IsAPOfLengthFree.maxCard k N

/-- The separated factor-four block `[4^j, 2·4^j)`. -/
def sepBlock (j : ℕ) : Set ℕ := Set.Ico (4 ^ j) (2 * 4 ^ j)

/-- Fixed-length reciprocal statement for sets avoiding `k`-term progressions. -/
def FreeSummable (k : ℕ) : Prop :=
  ∀ A : Set ℕ, A.IsAPOfLengthFree k → Summable (fun a : A ↦ 1 / (a : ℝ))

-- ## progression algebra

/-- Subsets of progression-free sets are progression-free. -/
theorem free_mono {S T : Set ℕ} {k : ℕ} (hST : S ⊆ T) (hT : T.IsAPOfLengthFree k) :
    S.IsAPOfLengthFree k := by
  exact fun t ht hAP => hT t (ht.trans hST) hAP

/-- Shifting a set to the right preserves progression-freeness. -/
theorem free_image_add {S : Set ℕ} {k : ℕ} (c : ℕ) (hS : S.IsAPOfLengthFree k) :
    ((· + c) '' S).IsAPOfLengthFree k := by
  intro t ht hAP
  by_cases hk1 : k ≤ 1
  · exact_mod_cast hk1
  push_neg at hk1
  obtain ⟨a, d, hcard, heq⟩ := hAP
  have h0k : ((0 : ℕ) : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (show (0 : ℕ) < k by omega)
  have ha_mem : a ∈ t := by
    rw [heq]; exact ⟨0, h0k, by simp⟩
  obtain ⟨s, hsS, hsa⟩ := ht ha_mem
  have hac : s + c = a := hsa
  have hinj : Function.Injective (fun x : ℕ => x + c) := add_left_injective c
  have ht'sub : (· + c) ⁻¹' t ⊆ S := by
    intro x hx
    have hxt : x + c ∈ t := hx
    obtain ⟨s', hs'S, hs'eq⟩ := ht hxt
    have hsx : s' = x := hinj hs'eq
    rwa [hsx] at hs'S
  have himg : (· + c) '' ((· + c) ⁻¹' t) = t :=
    Set.image_preimage_eq_of_subset (ht.trans (Set.image_subset_range _ _))
  have hcard' : ENat.card ((· + c) ⁻¹' t) = (k : ℕ∞) := by
    have h1 := ENat.card_image_of_injective (· + c) ((· + c) ⁻¹' t) hinj
    rw [himg] at h1
    rw [← h1, hcard]
  have heq' : (· + c) ⁻¹' t = {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), s + n • d = x} := by
    ext x
    constructor
    · intro hx
      have hxt : x + c ∈ t := hx
      rw [heq] at hxt
      obtain ⟨n, hn, hnx⟩ := hxt
      simp only [Nat.nsmul_eq_mul] at hnx ⊢
      refine ⟨n, hn, ?_⟩
      omega
    · rintro ⟨n, hn, rfl⟩
      show s + n • d + c ∈ t
      rw [heq]
      refine ⟨n, hn, ?_⟩
      rw [← hac]; ring
  exact hS _ ht'sub ⟨s, d, hcard', heq'⟩

/-- Shifting a set to the left, as a preimage, preserves progression-freeness. -/
theorem free_preimage_add {S : Set ℕ} {k : ℕ} (c : ℕ) (hS : S.IsAPOfLengthFree k) :
    ((· + c) ⁻¹' S).IsAPOfLengthFree k := by
  intro t ht hAP
  obtain ⟨a, d, hcard, heq⟩ := hAP
  have hinj : Function.Injective (fun x : ℕ => x + c) := add_left_injective c
  refine hS ((· + c) '' t) ?_ ⟨a + c, d, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ht hx
  · rw [ENat.card_image_of_injective (· + c) t hinj, hcard]
  · rw [heq]
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨n, hn, by ring⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨a + n • d, ⟨n, hn, rfl⟩, by ring⟩

/-- Avoiding length `k ≥ 2` implies avoiding every longer length. -/
theorem free_mono_length {A : Set ℕ} {k m : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m)
    (hA : A.IsAPOfLengthFree k) : A.IsAPOfLengthFree m := by
  intro t ht hAP
  obtain ⟨a, d, hcard, heq⟩ := hAP
  rcases eq_or_ne d 0 with hd0 | hd
  · exfalso
    subst hd0
    have hsub : t ⊆ ({a} : Set ℕ) := by
      rw [heq]; rintro x ⟨n, hn, rfl⟩; simp
    have h1 : t.encard ≤ 1 := (Set.encard_mono hsub).trans_eq (Set.encard_singleton a)
    rw [show t.encard = (m : ℕ∞) from hcard] at h1
    have h2 : (2 : ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast hk.trans hkm
    exact absurd (h2.trans h1) (by norm_num)
  · classical
    let f : Fin k → ℕ := fun i => a + i.val • d
    have hf : Function.Injective f := by
      intro i j hij
      simp only [f, Nat.nsmul_eq_mul] at hij
      have hij' : i.val = j.val := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd)
        (by omega)
      exact Fin.ext hij'
    have hsub : Set.range f ⊆ t := by
      rintro x ⟨i, rfl⟩
      rw [heq]
      refine ⟨i.val, ?_, rfl⟩
      have hlt : i.val < m := lt_of_lt_of_le i.isLt hkm
      exact_mod_cast hlt
    have hsubA : Set.range f ⊆ A := hsub.trans ht
    have : Fintype (Set.range f) := Fintype.ofFinite _
    have hcardk : ENat.card (Set.range f) = (k : ℕ∞) := by
      simp only [ENat.card_eq_coe_fintype_card, Set.card_range_of_injective hf,
        Fintype.card_fin]
    have heqk : Set.range f = {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), a + n • d = x} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, by exact_mod_cast i.isLt, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        have hn' : n < k := by exact_mod_cast hn
        exact ⟨⟨n, hn'⟩, rfl⟩
    have hAP' : (Set.range f).IsAPOfLength (k : ℕ∞) := ⟨a, d, hcardk, heqk⟩
    have hle := hA (Set.range f) hsubA hAP'
    exact absurd hle (by exact_mod_cast (show ¬ k ≤ 1 by omega))

-- ## separated blocks

theorem a_sepBlock_disjoint {x i j : ℕ} (hi : x ∈ sepBlock i) (hj : x ∈ sepBlock j) :
    i = j := by
  unfold sepBlock at hi hj
  rw [Set.mem_Ico] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · have h4 : 4 ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h4
    omega
  · exact h
  · have h4 : 4 ^ (j + 1) ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h4
    omega

theorem a_dichot {t i m : ℕ} (ht : t ∈ sepBlock i) (htm : t < 2 * 4 ^ m) :
    4 ^ m ≤ t ∨ 2 * t < 4 ^ m := by
  unfold sepBlock at ht
  rw [Set.mem_Ico] at ht
  rcases lt_trichotomy i m with h | h | h
  · have h4 : 4 ^ (i + 1) ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h4
    omega
  · subst h
    omega
  · have h4 : 4 ^ (m + 1) ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h4
    omega

theorem a_window {x d m : ℕ} (h0 : ∃ i, x ∈ sepBlock i) (h1 : ∃ i, x + d ∈ sepBlock i)
    (h2 : ∃ i, x + 2 * d ∈ sepBlock i) (h3 : x + 3 * d ∈ sepBlock m) :
    x ∈ sepBlock m ∧ x + d ∈ sepBlock m ∧ x + 2 * d ∈ sepBlock m := by
  obtain ⟨i0, h0⟩ := h0
  obtain ⟨i1, h1⟩ := h1
  obtain ⟨i2, h2⟩ := h2
  have h3' := h3
  unfold sepBlock at h3'
  rw [Set.mem_Ico] at h3'
  have c0 := a_dichot h0 (by omega : x < 2 * 4 ^ m)
  have c1 := a_dichot h1 (by omega : x + d < 2 * 4 ^ m)
  have c2 := a_dichot h2 (by omega : x + 2 * d < 2 * 4 ^ m)
  simp only [sepBlock, Set.mem_Ico]
  generalize 4 ^ m = N at *
  omega

/-- For `k ≥ 4`, independently chosen `k`-AP-free subsets of the separated
blocks have a `k`-AP-free union: no four-term progression meets two blocks. -/
theorem sepBlock_union_free {k : ℕ} (hk : 4 ≤ k) (B : ℕ → Set ℕ)
    (hsub : ∀ j, B j ⊆ sepBlock j) (hfree : ∀ j, (B j).IsAPOfLengthFree k) :
    (⋃ j, B j).IsAPOfLengthFree k := by
  intro t ht hAP
  obtain ⟨a, d, hcard, heq⟩ := hAP
  have hterm : ∀ n : ℕ, n < k → a + n * d ∈ t := by
    intro n hn
    rw [heq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  have hblk : ∀ n : ℕ, n < k → ∃ i, a + n * d ∈ sepBlock i := by
    intro n hn
    have hmem := ht (hterm n hn)
    rw [Set.mem_iUnion] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, hsub i hi⟩
  obtain ⟨j0, hj0⟩ : ∃ j0, a ∈ B j0 := by
    have hmem := ht (hterm 0 (by omega))
    rw [Set.mem_iUnion] at hmem
    simpa using hmem
  have hall : ∀ n : ℕ, n < k → a + n * d ∈ sepBlock j0 := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using hsub j0 hj0
    | succ n ih =>
      intro hn
      have ihn := ih (by omega)
      obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s, s ≤ n ∧ n ≤ s + 2 ∧ s + 3 < k := by
        by_cases h : n + 3 < k
        · exact ⟨n, le_refl n, by omega, h⟩
        · exact ⟨k - 4, by omega, by omega, by omega⟩
      obtain ⟨m, hm⟩ := hblk (s + 3) hs3
      have e1 : a + (s + 1) * d = a + s * d + d := by ring
      have e2 : a + (s + 2) * d = a + s * d + 2 * d := by ring
      have e3 : a + (s + 3) * d = a + s * d + 3 * d := by ring
      have b1 := hblk (s + 1) (by omega)
      have b2 := hblk (s + 2) (by omega)
      rw [e1] at b1
      rw [e2] at b2
      rw [e3] at hm
      have w := a_window (hblk s (by omega)) b1 b2 hm
      have hw : ∀ r, r ≤ 3 → a + (s + r) * d ∈ sepBlock m := by
        intro r hr
        interval_cases r
        · simpa using w.1
        · rw [e1]; exact w.2.1
        · rw [e2]; exact w.2.2
        · rw [e3]; exact hm
      have hn1 : a + n * d ∈ sepBlock m := by
        have hh := hw (n - s) (by omega)
        rwa [show s + (n - s) = n by omega] at hh
      have hn2 : a + (n + 1) * d ∈ sepBlock m := by
        have hh := hw (n + 1 - s) (by omega)
        rwa [show s + (n + 1 - s) = n + 1 by omega] at hh
      have hmj := a_sepBlock_disjoint hn1 ihn
      rw [← hmj]
      exact hn2
  have htsub : t ⊆ B j0 := by
    intro x hx
    have hx' := ht hx
    rw [Set.mem_iUnion] at hx'
    obtain ⟨i, hi⟩ := hx'
    rw [heq] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    have hn' : n < k := by exact_mod_cast hn
    have hin := hall n hn'
    rw [smul_eq_mul] at hi
    have hij := a_sepBlock_disjoint (hsub i hi) hin
    rw [hij] at hi
    rw [smul_eq_mul]
    exact hi
  exact hfree j0 t htsub ⟨a, d, hcard, heq⟩

-- ## the extremal function

/-- The extremal function is attained by a finite progression-free set. -/
theorem r_attained (k N : ℕ) : ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
    (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  have hbdd : BddAbove {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} := by
    refine ⟨N, ?_⟩
    rintro m ⟨S, hS, -, rfl⟩
    calc S.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hS
      _ = N := by rw [Nat.card_Icc]; omega
  have hemptyfree : ((∅ : Finset ℕ) : Set ℕ).IsAPOfLengthFree k := by
    intro t ht hAP
    simp only [Finset.coe_empty] at ht
    have ht' : t = ∅ := Set.subset_empty_iff.mp ht
    subst ht'
    by_contra hcon
    push_neg at hcon
    exact Set.not_isAPOfLength_empty (lt_of_lt_of_le zero_lt_one hcon.le) hAP
  have hne : (∅ : Finset ℕ).card ∈ {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} :=
    ⟨∅, Finset.empty_subset _, hemptyfree, rfl⟩
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem ⟨_, hne⟩ hbdd
  exact ⟨S, hS, hfree, hcard⟩

/-- Every progression-free subset of `{1, …, N}` has at most `r k N` elements. -/
theorem card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  have hbdd : BddAbove {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} := by
    refine ⟨N, ?_⟩
    rintro m ⟨S', hS', -, rfl⟩
    calc S'.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hS'
      _ = N := by rw [Nat.card_Icc]; omega
  have hmem : S.card ∈ {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} := ⟨S, hS, hfree, rfl⟩
  exact le_csSup hbdd hmem

/-- Splitting `{1, …, 2n}` into two translated halves gives `r k (2n) ≤ 2 r k n`. -/
theorem r_two_mul_le (k n : ℕ) : r k (2 * n) ≤ 2 * r k n := by
  classical
  obtain ⟨S, hSicc, hSfree, hScard⟩ := r_attained k (2 * n)
  set S1 := S.filter (fun x => x ≤ n) with hS1def
  set S3 := S.filter (fun x => ¬ x ≤ n) with hS3def
  set S2 := (Finset.Icc 1 n).filter (fun x => x + n ∈ S) with hS2def
  have hS1_icc : S1 ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [hS1def, Finset.mem_filter] at hx
    obtain ⟨hxS, hxn⟩ := hx
    have hxIcc := hSicc hxS
    rw [Finset.mem_Icc] at hxIcc ⊢
    exact ⟨hxIcc.1, hxn⟩
  have hS1_sub : (↑S1 : Set ℕ) ⊆ (↑S : Set ℕ) := by
    rw [hS1def]; exact Finset.coe_subset.mpr (Finset.filter_subset _ _)
  have hS1_free : (↑S1 : Set ℕ).IsAPOfLengthFree k := free_mono hS1_sub hSfree
  have hS1_le : S1.card ≤ r k n := card_le_r hS1_icc hS1_free
  have hS2_icc : S2 ⊆ Finset.Icc 1 n := by rw [hS2def]; exact Finset.filter_subset _ _
  have hS2_pre : (↑S2 : Set ℕ) ⊆ (· + n) ⁻¹' (↑S : Set ℕ) := by
    intro x hx
    rw [Finset.mem_coe, hS2def, Finset.mem_filter] at hx
    show x + n ∈ (↑S : Set ℕ)
    exact_mod_cast hx.2
  have hS2_free : (↑S2 : Set ℕ).IsAPOfLengthFree k :=
    free_mono hS2_pre (free_preimage_add n hSfree)
  have hS2_le : S2.card ≤ r k n := card_le_r hS2_icc hS2_free
  have hS3_le : S3.card ≤ S2.card := by
    apply Finset.card_le_card_of_injOn (fun x => x - n)
    · intro x hx
      rw [Finset.mem_coe, hS3def, Finset.mem_filter] at hx
      obtain ⟨hxS, hxn⟩ := hx
      have hxIcc := hSicc hxS
      rw [Finset.mem_Icc] at hxIcc
      have h1 : 1 ≤ x - n := by omega
      have h2 : x - n ≤ n := by omega
      have h3 : x - n + n = x := by omega
      rw [Finset.mem_coe, hS2def, Finset.mem_filter, Finset.mem_Icc, h3]
      exact ⟨⟨h1, h2⟩, hxS⟩
    · intro x1 hx1 x2 hx2 heq
      rw [Finset.mem_coe, hS3def, Finset.mem_filter] at hx1 hx2
      obtain ⟨hx1S, hx1n⟩ := hx1
      obtain ⟨hx2S, hx2n⟩ := hx2
      have hxIcc1 := hSicc hx1S
      have hxIcc2 := hSicc hx2S
      rw [Finset.mem_Icc] at hxIcc1 hxIcc2
      have heq' : x1 - n = x2 - n := heq
      omega
  have hsplit : S1.card + S3.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun x => x ≤ n)
  calc r k (2 * n) = S.card := hScard.symm
    _ = S1.card + S3.card := hsplit.symm
    _ ≤ r k n + S2.card := by omega
    _ ≤ r k n + r k n := by omega
    _ = 2 * r k n := by ring

-- ## extremal summability implies reciprocal summability

/-- A positive dyadic block of a progression-free set translates into `{1, …, 2^ℓ}`. -/
theorem logBlock_ncard_le_r {A : Set ℕ} {k : ℕ} (hA : A.IsAPOfLengthFree k)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : (logBlock A ℓ).ncard ≤ r k (2 ^ ℓ) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ ℓ := ⟨_, rfl⟩
  have hM2 : 2 ^ (ℓ + 1) = 2 * M := by rw [pow_succ, mul_comm, hM]
  have hMpos : 1 ≤ M := by rw [hM]; exact Nat.one_le_two_pow
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = M - 1 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ, E = (Finset.Icc 1 M).filter (fun x => x + c ∈ A) :=
    ⟨_, rfl⟩
  have hEsub : (E : Set ℕ) ⊆ (· + c) ⁻¹' A := by
    intro x hx
    rw [hE, Finset.coe_filter] at hx
    exact hx.2
  have hEfree : (E : Set ℕ).IsAPOfLengthFree k := free_mono hEsub (free_preimage_add c hA)
  have hEIcc : E ⊆ Finset.Icc 1 (2 ^ ℓ) := by
    rw [hE, ← hM]; exact Finset.filter_subset _ _
  have hEcard : E.card ≤ r k (2 ^ ℓ) := card_le_r hEIcc hEfree
  have hbounds : ∀ a : A, a ∈ logBlock A ℓ → M ≤ (a : ℕ) ∧ (a : ℕ) < 2 * M := by
    intro a ha
    have hlog : Nat.log 2 (a : ℕ) = ℓ := ha
    have hne : (a : ℕ) ≠ 0 := by
      intro h0
      rw [h0, Nat.log_zero_right] at hlog
      omega
    refine ⟨?_, ?_⟩
    · rw [hM]
      simpa only [hlog] using Nat.pow_log_le_self 2 hne
    · rw [← hM2]; exact logBlock_lt_upper A ℓ ha
  have hle : (logBlock A ℓ).ncard ≤ (E : Set ℕ).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun a : A => (a : ℕ) - c)
    · intro a ha
      obtain ⟨h1, h2⟩ := hbounds a ha
      rw [hE, Finset.coe_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have hac : (a : ℕ) - c + c = (a : ℕ) := by omega
      rw [hac]; exact a.property
    · intro a ha b hb hab
      obtain ⟨ha1, _⟩ := hbounds a ha
      obtain ⟨hb1, _⟩ := hbounds b hb
      apply Subtype.ext
      have hab' : (a : ℕ) - c = (b : ℕ) - c := hab
      omega
  rw [Set.ncard_coe_finset] at hle
  omega

/-- Dyadic extremal summability gives reciprocal summability for every `k`-AP-free set. -/
theorem freeSummable_of_dyadic {k : ℕ}
    (h : Summable fun j : ℕ ↦ (r k (2 ^ j) : ℝ) / 2 ^ j) : FreeSummable k := by
  intro A hA
  apply Erdos3Dyadic.reciprocal_summable_of_dyadic_counts
  apply (summable_nat_add_iff 1).mp
  have h1 := (summable_nat_add_iff 1).mpr h
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1
  · show (0 : ℝ) ≤ ((logBlock A (j + 1)).ncard : ℝ) / (2 : ℝ) ^ (j + 1)
    positivity
  · show ((logBlock A (j + 1)).ncard : ℝ) / (2 : ℝ) ^ (j + 1) ≤
      (r k (2 ^ (j + 1)) : ℝ) / 2 ^ (j + 1)
    have hc : (logBlock A (j + 1)).ncard ≤ r k (2 ^ (j + 1)) :=
      logBlock_ncard_le_r hA (by omega)
    have hcR : ((logBlock A (j + 1)).ncard : ℝ) ≤ (r k (2 ^ (j + 1)) : ℝ) := by
      exact_mod_cast hc
    exact div_le_div_of_nonneg_right hcR (by positivity)

/-- The factor-four extremal series controls the dyadic one. -/
theorem dyadic_of_quart {k : ℕ}
    (h : Summable fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / 4 ^ j) :
    Summable fun j : ℕ ↦ (r k (2 ^ j) : ℝ) / 2 ^ j := by
  have hpow : ∀ j : ℕ, (2 : ℕ) ^ (2 * j) = 4 ^ j := by
    intro j; rw [pow_mul]; norm_num
  have hpowR : ∀ j : ℕ, (2 : ℝ) ^ (2 * j) = 4 ^ j := by
    intro j; rw [pow_mul]; norm_num
  apply Summable.even_add_odd
  · refine h.congr (fun j => ?_)
    show (r k (4 ^ j) : ℝ) / 4 ^ j = (r k (2 ^ (2 * j)) : ℝ) / 2 ^ (2 * j)
    rw [hpow, hpowR]
  · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h
    · show (0 : ℝ) ≤ (r k (2 ^ (2 * j + 1)) : ℝ) / 2 ^ (2 * j + 1)
      positivity
    · show (r k (2 ^ (2 * j + 1)) : ℝ) / 2 ^ (2 * j + 1) ≤ (r k (4 ^ j) : ℝ) / 4 ^ j
      have h1 : (2 : ℕ) ^ (2 * j + 1) = 2 * 4 ^ j := by rw [pow_succ, hpow, mul_comm]
      have h1R : (2 : ℝ) ^ (2 * j + 1) = 2 * 4 ^ j := by rw [pow_succ, hpowR, mul_comm]
      rw [h1, h1R]
      have hle : (r k (2 * 4 ^ j) : ℝ) ≤ 2 * (r k (4 ^ j) : ℝ) := by
        exact_mod_cast r_two_mul_le k (4 ^ j)
      have hpos : (0 : ℝ) < 4 ^ j := by positivity
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith

-- ## reciprocal summability forces extremal summability

/-- Translate one extremizer into each separated block. Their union is
`k`-AP-free for `k ≥ 4`, so reciprocal summability bounds the extremal series. -/
theorem e_sepBlock_eq {i j x : ℕ} (hi : x ∈ sepBlock i) (hj : x ∈ sepBlock j) : i = j := by
  simp only [sepBlock, Set.mem_Ico] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h4 : 4 ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h4
    generalize 4 ^ i = a at *
    generalize 4 ^ j = b at *
    omega
  · have h4 : 4 ^ (j + 1) ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h4
    generalize 4 ^ i = a at *
    generalize 4 ^ j = b at *
    omega

theorem e_shift_mem {j e : ℕ} (he : e ∈ Finset.Icc 1 (4 ^ j)) :
    e + (4 ^ j - 1) ∈ sepBlock j := by
  rw [Finset.mem_Icc] at he
  simp only [sepBlock, Set.mem_Ico]
  generalize 4 ^ j = N at *
  omega

theorem e_block_lower {j : ℕ} (E : Finset ℕ) (hE : E ⊆ Finset.Icc 1 (4 ^ j)) :
    (E.card : ℝ) / (2 * 4 ^ j) ≤
      ∑ e ∈ E, 1 / (((e + (4 ^ j - 1) : ℕ)) : ℝ) := by
  have hbound : ∀ e ∈ E, 1 / (2 * (4 : ℝ) ^ j) ≤ 1 / (((e + (4 ^ j - 1) : ℕ)) : ℝ) := by
    intro e he
    have he' := Finset.mem_Icc.mp (hE he)
    have hpos : 0 < e + (4 ^ j - 1) := by omega
    have hle : e + (4 ^ j - 1) ≤ 2 * 4 ^ j := by
      generalize 4 ^ j = N at *
      omega
    have hposR : (0 : ℝ) < ((e + (4 ^ j - 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    have hleR : ((e + (4 ^ j - 1) : ℕ) : ℝ) ≤ 2 * (4 : ℝ) ^ j := by exact_mod_cast hle
    exact one_div_le_one_div_of_le hposR hleR
  calc (E.card : ℝ) / (2 * 4 ^ j) = ∑ _e ∈ E, 1 / (2 * (4 : ℝ) ^ j) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ e ∈ E, 1 / (((e + (4 ^ j - 1) : ℕ)) : ℝ) := Finset.sum_le_sum hbound

theorem quart_of_freeSummable {k : ℕ} (hk : 4 ≤ k) (h : FreeSummable k) :
    Summable fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / 4 ^ j := by
  classical
  choose E hEsub hEfree hEcard using fun j : ℕ ↦ r_attained k (4 ^ j)
  let B : ℕ → Set ℕ := fun j ↦ (· + (4 ^ j - 1)) '' (E j : Set ℕ)
  have hBsub : ∀ j, B j ⊆ sepBlock j := by
    rintro j _ ⟨e, he, rfl⟩
    exact e_shift_mem (hEsub j he)
  have hBfree : ∀ j, (B j).IsAPOfLengthFree k := fun j ↦ free_image_add _ (hEfree j)
  let U : Set ℕ := ⋃ j, B j
  have hUfree : U.IsAPOfLengthFree k := sepBlock_union_free hk B hBsub hBfree
  have hsum := h U hUfree
  let s : ℕ → Set U := fun j ↦ {u | (u : ℕ) ∈ B j}
  have hs : ∀ u : U, ∃! j, u ∈ s j := by
    intro u
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp u.2
    exact ⟨j, hj, fun i hi ↦ e_sepBlock_eq (hBsub i hi) (hBsub j hj)⟩
  have hnonneg : 0 ≤ fun u : U ↦ 1 / (u : ℝ) := fun u ↦ by positivity
  have hpart := ((summable_partition hnonneg hs).mp hsum).2
  have hlow : ∀ j, (r k (4 ^ j) : ℝ) / (2 * 4 ^ j) ≤
      ∑' u : s j, 1 / (((u : U) : ℕ) : ℝ) := by
    intro j
    have h1 : ∑' u : s j, 1 / (((u : U) : ℕ) : ℝ) =
        ∑' x : (Subtype.val '' s j : Set ℕ), 1 / (x : ℝ) :=
      (tsum_image (fun x : ℕ ↦ 1 / (x : ℝ)) Subtype.val_injective.injOn).symm
    have h2 : (Subtype.val '' s j : Set ℕ) = B j := by
      show Subtype.val '' (Subtype.val ⁻¹' B j : Set U) = B j
      rw [Subtype.image_preimage_coe]
      exact Set.inter_eq_right.mpr (Set.subset_iUnion B j)
    rw [h1, h2]
    have h3 : ∑' x : B j, 1 / (x : ℝ) =
        ∑' e : (E j : Set ℕ), 1 / (((e : ℕ) + (4 ^ j - 1) : ℕ) : ℝ) :=
      tsum_image (fun x : ℕ ↦ 1 / (x : ℝ)) (add_left_injective _).injOn
    rw [h3, Finset.tsum_subtype' (E j) (fun e : ℕ ↦ 1 / (((e + (4 ^ j - 1) : ℕ)) : ℝ)),
      ← hEcard j]
    exact e_block_lower (E j) (hEsub j)
  have hsum2 : Summable fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (2 * 4 ^ j) :=
    Summable.of_nonneg_of_le (fun j ↦ by positivity) hlow hpart
  refine (hsum2.mul_left 2).congr (fun j ↦ ?_)
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  field_simp

-- ## the equivalences

/-- For `k ≥ 4`, fixed-length reciprocal summability is the factor-four extremal series. -/
theorem freeSummable_iff_quart {k : ℕ} (hk : 4 ≤ k) :
    FreeSummable k ↔ Summable fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / 4 ^ j :=
  ⟨quart_of_freeSummable hk, fun h ↦ freeSummable_of_dyadic (dyadic_of_quart h)⟩

/-- For `k ≥ 4`, fixed-length reciprocal summability is the dyadic extremal series. -/
theorem freeSummable_iff_dyadic {k : ℕ} (hk : 4 ≤ k) :
    FreeSummable k ↔ Summable fun j : ℕ ↦ (r k (2 ^ j) : ℝ) / 2 ^ j :=
  ⟨fun h ↦ dyadic_of_quart (quart_of_freeSummable hk h), freeSummable_of_dyadic⟩

/-- The exact elaborated hill is equivalent to dyadic summability of the imported
extremal function for every progression length at least four. Neither side is
proved here. -/
theorem hill_iff_extremal :
    (True ↔ ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    ∀ k : ℕ, 4 ≤ k → Summable fun j : ℕ ↦ (r k (2 ^ j) : ℝ) / 2 ^ j := by
  constructor
  · intro hIff k hk
    have hP : ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
        ∃ᶠ (m : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength m := hIff.mp trivial
    have hFS : FreeSummable k := by
      intro A hA
      by_contra hns
      obtain ⟨m, hm, S, hSA, hSAP⟩ := Filter.frequently_atTop.mp (hP A hns) k
      have hAm : A.IsAPOfLengthFree m := free_mono_length (by omega) hm hA
      have hle : (m : ℕ∞) ≤ 1 := hAm S hSA hSAP
      have hle' : m ≤ 1 := by exact_mod_cast hle
      omega
    exact (freeSummable_iff_dyadic hk).mp hFS
  · intro h
    have hAPFS : Erdos3Reduction.APFreeSummability := by
      intro k hk3 A hA
      rcases lt_or_ge k 4 with hlt | hge
      · have hk3' : k = 3 := by omega
        subst hk3'
        have hA4 : A.IsAPOfLengthFree 4 := free_mono_length (by norm_num) (by norm_num) hA
        exact freeSummable_of_dyadic (h 4 (by norm_num)) A hA4
      · exact freeSummable_of_dyadic (h k hge) A hA
    exact Erdos3Reduction.hill_of_apFreeSummability hAPFS

/-- Fidelity anchor: the frozen hill's proposition, copied verbatim including
`answer(sorry)`, is definitionally the left side of `hill_iff_extremal`. -/
theorem hill_statement_iff_extremal :
    (answer(sorry) ↔ ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    ∀ k : ℕ, 4 ≤ k → Summable fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (2 ^ j) : ℝ) / 2 ^ j :=
  hill_iff_extremal

#print axioms free_mono
#print axioms free_image_add
#print axioms free_preimage_add
#print axioms free_mono_length
#print axioms a_sepBlock_disjoint
#print axioms a_dichot
#print axioms a_window
#print axioms sepBlock_union_free
#print axioms r_attained
#print axioms card_le_r
#print axioms r_two_mul_le
#print axioms logBlock_ncard_le_r
#print axioms freeSummable_of_dyadic
#print axioms dyadic_of_quart
#print axioms e_sepBlock_eq
#print axioms e_shift_mem
#print axioms e_block_lower
#print axioms quart_of_freeSummable
#print axioms freeSummable_iff_quart
#print axioms freeSummable_iff_dyadic
#print axioms hill_iff_extremal
#print axioms hill_statement_iff_extremal

end Erdos3CrossScale
