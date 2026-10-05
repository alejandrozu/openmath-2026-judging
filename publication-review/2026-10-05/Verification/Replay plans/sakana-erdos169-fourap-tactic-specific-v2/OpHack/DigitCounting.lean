import OpHack.BaseDigitAP
import OpHack.SixFibreAP

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false

namespace Erdos3Candidate

/-- Walker's digit alphabet as a finite set of integers. -/
def walkerFinset : Finset ℤ := ErdosSingletonIndependent.D.image Int.ofNat

theorem mem_walkerFinset (z : ℤ) : z ∈ walkerFinset ↔ z ∈ walkerDigits := by
  simp only [walkerFinset, walkerDigits, Finset.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨Int.natCast_nonneg _, by simpa using hd⟩
  · rintro ⟨hz, hd⟩
    exact ⟨z.toNat, hd, Int.toNat_of_nonneg hz⟩

theorem walkerFinset_bound {d : ℤ} (hd : d ∈ walkerFinset) :
    0 ≤ d ∧ d < 55 := walkerDigits_bound d ((mem_walkerFinset d).mp hd)

theorem walkerFinset_card : walkerFinset.card = 21 := by
  have hi : Set.InjOn (Int.ofNat) ErdosSingletonIndependent.D := by
    intro a ha b hb hab
    exact Int.ofNat_injective hab
  rw [walkerFinset, Finset.card_image_of_injOn hi]
  exact ErdosSingletonIndependent.base_size_and_sum.1

theorem walkerFinset_sum : ∑ d ∈ walkerFinset, d = 433 := by
  have hi : Set.InjOn (Int.ofNat) ErdosSingletonIndependent.D := by
    intro a ha b hb hab
    exact Int.ofNat_injective hab
  rw [walkerFinset, Finset.sum_image hi]
  simpa only [Int.ofNat_eq_natCast, Nat.cast_sum, Nat.cast_ofNat] using
    congrArg (fun k : ℕ => (k : ℤ)) ErdosSingletonIndependent.base_size_and_sum.2

/-- Base-55 digit strings of length `n`, including leading zero. -/
def digitFinset : ℕ → Finset ℤ
  | 0 => {0}
  | n + 1 => (walkerFinset.product (digitFinset n)).image
      (fun p => p.1 + 55 * p.2)

theorem mem_digitFinset (n : ℕ) (z : ℤ) :
    z ∈ digitFinset n ↔ z ∈ digitSet walkerDigits n := by
  induction n generalizing z with
  | zero => simp [digitFinset, digitSet]
  | succ n ih =>
      simp only [digitFinset, digitSet, Finset.mem_image]
      constructor
      · rintro ⟨⟨d, t⟩, hdt, rfl⟩
        have ⟨hd, ht⟩ := Finset.mem_product.mp hdt
        exact ⟨d, (mem_walkerFinset d).mp hd, t, (ih t).mp ht, rfl⟩
      · rintro ⟨d, hd, t, ht, rfl⟩
        exact ⟨(d, t), Finset.mem_product.mpr
          ⟨(mem_walkerFinset d).mpr hd, (ih t).mpr ht⟩, rfl⟩

theorem digitFinset_bound (n : ℕ) :
    ∀ z ∈ digitFinset n, 0 ≤ z ∧ z < 55 ^ n := by
  induction n with
  | zero =>
      intro z hz
      simp [digitFinset] at hz
      omega
  | succ n ih =>
      intro z hz
      obtain ⟨⟨d, t⟩, hdt, rfl⟩ := Finset.mem_image.mp hz
      have ⟨hd, ht⟩ := Finset.mem_product.mp hdt
      have hd' := walkerFinset_bound hd
      have ht' := ih t ht
      have hp : 0 < (55 : ℤ) ^ n := pow_pos (by omega) _
      constructor
      · omega
      · calc
          d + 55 * t < 55 * (55 : ℤ) ^ n := by omega
          _ = 55 ^ (n + 1) := by ring

theorem digitFinset_step_inj (n : ℕ) :
    Set.InjOn (fun p : ℤ × ℤ => p.1 + 55 * p.2)
      (walkerFinset.product (digitFinset n)) := by
  rintro ⟨d, t⟩ hp ⟨e, s⟩ hq heq
  have ⟨hd, _⟩ := Finset.mem_product.mp hp
  have ⟨he, _⟩ := Finset.mem_product.mp hq
  have hd' := walkerFinset_bound hd
  have he' := walkerFinset_bound he
  dsimp at heq
  have : d = e ∧ t = s := by omega
  exact Prod.ext this.1 this.2

theorem digitFinset_card (n : ℕ) : (digitFinset n).card = 21 ^ n := by
  induction n with
  | zero => simp [digitFinset]
  | succ n ih =>
      rw [digitFinset, Finset.card_image_of_injOn (digitFinset_step_inj n),
        Finset.product_eq_sprod, Finset.card_product, walkerFinset_card, ih, pow_succ]
      ring

private theorem sum_affine_product (s t : Finset ℤ) (b : ℤ) :
    Finset.sum s (fun d => Finset.sum t (fun u => d + b * u)) =
      (t.card : ℤ) * (∑ d ∈ s, d) +
        (s.card : ℤ) * b * (∑ u ∈ t, u) := by
  simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_comm, mul_left_comm]

theorem digitFinset_sum_step (n : ℕ) :
    (∑ z ∈ digitFinset (n + 1), z) =
      ((digitFinset n).card : ℤ) * (∑ d ∈ walkerFinset, d) +
      (walkerFinset.card : ℤ) * 55 * (∑ t ∈ digitFinset n, t) := by
  rw [digitFinset, Finset.sum_image (digitFinset_step_inj n),
    Finset.product_eq_sprod, Finset.sum_product]
  exact sum_affine_product walkerFinset (digitFinset n) 55

theorem digitFinset_sum (n : ℕ) :
    (∑ t ∈ digitFinset n, (t : ℚ)) =
      (21 ^ n : ℚ) * (433 / 1134) * ((55 ^ n : ℚ) - 1) := by
  induction n with
  | zero => simp [digitFinset]
  | succ n ih =>
      have hs :
          (∑ t ∈ digitFinset (n + 1), (t : ℚ)) =
            ((digitFinset n).card : ℚ) *
                (∑ d ∈ walkerFinset, (d : ℚ)) +
              (walkerFinset.card : ℚ) * 55 *
                (∑ t ∈ digitFinset n, (t : ℚ)) := by
        have hc := congrArg (fun x : ℤ => (x : ℚ)) (digitFinset_sum_step n)
        simpa only [Int.cast_sum, Int.cast_add, Int.cast_mul,
          Int.cast_natCast, Int.cast_ofNat] using hc
      simp only [digitFinset_card, walkerFinset_card] at hs
      have hds : (∑ d ∈ walkerFinset, (d : ℚ)) = 433 := by
        have hc := congrArg (fun x : ℤ => (x : ℚ)) walkerFinset_sum
        simpa only [Int.cast_sum, Int.cast_ofNat] using hc
      rw [hds, ih] at hs
      rw [hs, pow_succ, pow_succ]
      simp only [Nat.cast_pow]
      ring

/-- Split a digit string after its `m` least significant digits. -/
theorem mem_digitFinset_append (m n : ℕ) (z : ℤ) :
    z ∈ digitFinset (m + n) ↔
      ∃ low ∈ digitFinset m, ∃ high ∈ digitFinset n,
        z = low + 55 ^ m * high := by
  induction m generalizing z with
  | zero =>
      simp only [zero_add, digitFinset, pow_zero, one_mul, Finset.mem_singleton]
      constructor
      · intro hz
        exact ⟨0, rfl, z, hz, by ring⟩
      · rintro ⟨low, rfl, high, hh, rfl⟩
        simpa using hh
  | succ m ih =>
      have hm : (m + 1) + n = (m + n) + 1 := by omega
      rw [hm]
      change z ∈ (walkerFinset.product (digitFinset (m + n))).image
        (fun p => p.1 + 55 * p.2) ↔ _
      rw [Finset.mem_image]
      constructor
      · rintro ⟨⟨d, t⟩, hdt, hz⟩
        have ⟨hd, ht⟩ := Finset.mem_product.mp hdt
        obtain ⟨low, hl, high, hh, htEq⟩ := (ih t).mp ht
        have hlow : d + 55 * low ∈ digitFinset (m + 1) := by
          change d + 55 * low ∈ (walkerFinset.product (digitFinset m)).image
            (fun p => p.1 + 55 * p.2)
          exact Finset.mem_image.mpr ⟨(d, low), Finset.mem_product.mpr ⟨hd, hl⟩, rfl⟩
        refine ⟨d + 55 * low, hlow, high, hh, ?_⟩
        rw [← hz, htEq, pow_succ]
        ring
      · rintro ⟨low, hl, high, hh, hz⟩
        have hl' : low ∈ (walkerFinset.product (digitFinset m)).image
            (fun p => p.1 + 55 * p.2) := hl
        obtain ⟨⟨d, t⟩, hdt, hlow⟩ := Finset.mem_image.mp hl'
        have ⟨hd, ht⟩ := Finset.mem_product.mp hdt
        have htail : t + 55 ^ m * high ∈ digitFinset (m + n) :=
          (ih _).mpr ⟨t, ht, high, hh, rfl⟩
        refine ⟨(d, t + 55 ^ m * high),
          Finset.mem_product.mpr ⟨hd, htail⟩, ?_⟩
        rw [hz, ← hlow, pow_succ]
        ring

theorem walkerFinset_zero : (0 : ℤ) ∈ walkerFinset := by
  apply (mem_walkerFinset 0).mpr
  refine ⟨by omega, ?_⟩
  decide

theorem digitFinset_one : digitFinset 1 = walkerFinset := by
  ext z
  rw [mem_digitFinset 1 z, mem_walkerFinset z]
  change (∃ d ∈ walkerDigits, ∃ t ∈ ({0} : Set ℤ), z = d + 55 * t) ↔
    z ∈ walkerDigits
  constructor
  · rintro ⟨d, hd, t, ht, hEq⟩
    have ht0 : t = 0 := ht
    subst t
    have hzd : z = d := by simpa using hEq
    rw [hzd]
    exact hd
  · intro hz
    exact ⟨z, hz, 0, rfl, by ring⟩

theorem mem_digitFinset_high (n : ℕ) (z : ℤ) :
    z ∈ digitFinset (n + 1) ↔
      ∃ t ∈ digitFinset n, ∃ d ∈ walkerFinset, z = t + 55 ^ n * d := by
  simpa only [digitFinset_one] using mem_digitFinset_append n 1 z

theorem digitFinset_mono_step (n : ℕ) : digitFinset n ⊆ digitFinset (n + 1) := by
  intro t ht
  exact (mem_digitFinset_high n t).mpr
    ⟨t, ht, 0, walkerFinset_zero, by simp⟩

/-- The new numbers at length `n+1` grouped by their nonzero leading digit. -/
def leadingBlock (n : ℕ) (d : ℤ) : Finset ℤ :=
  (digitFinset n).image (fun t => t + 55 ^ n * d)

def leadingBlocks (n : ℕ) : Finset ℤ :=
  (walkerFinset.erase 0).biUnion (leadingBlock n)

theorem mem_leadingBlocks (n : ℕ) (z : ℤ) :
    z ∈ leadingBlocks n ↔
      ∃ d ∈ walkerFinset, d ≠ 0 ∧
        ∃ t ∈ digitFinset n, z = t + 55 ^ n * d := by
  simp only [leadingBlocks, leadingBlock, Finset.mem_biUnion,
    Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨d, ⟨hd0, hd⟩, t, ht, hEq⟩
    exact ⟨d, hd, hd0, t, ht, hEq.symm⟩
  · rintro ⟨d, hd, hd0, t, ht, hEq⟩
    exact ⟨d, ⟨hd0, hd⟩, t, ht, hEq.symm⟩

theorem digitFinset_leading_partition (n : ℕ) :
    digitFinset (n + 1) = digitFinset n ∪ leadingBlocks n := by
  ext z
  rw [Finset.mem_union, mem_digitFinset_high, mem_leadingBlocks]
  constructor
  · rintro ⟨t, ht, d, hd, hEq⟩
    by_cases hzero : d = 0
    · left
      have hzt : z = t := by simpa [hzero] using hEq
      rw [hzt]
      exact ht
    · right
      exact ⟨d, hd, hzero, t, ht, hEq⟩
  · rintro (h | ⟨d, hd, hd0, t, ht, hEq⟩)
    · exact ⟨z, h, 0, walkerFinset_zero, by simp⟩
    · exact ⟨t, ht, d, hd, hEq⟩

theorem digitFinset_disjoint_leading (n : ℕ) :
    Disjoint (digitFinset n) (leadingBlocks n) := by
  apply Finset.disjoint_left.mpr
  intro z hz hb
  obtain ⟨d, hd, hd0, t, ht, hEq⟩ := (mem_leadingBlocks n z).mp hb
  have ⟨hz0, hz1⟩ := digitFinset_bound n z hz
  have ⟨ht0, ht1⟩ := digitFinset_bound n t ht
  have ⟨hd0', _⟩ := walkerFinset_bound hd
  have hd1 : 1 ≤ d := by omega
  have hp : 0 < (55 : ℤ) ^ n := pow_pos (by omega) _
  have hnonneg : 0 ≤ (55 : ℤ) ^ n * (d - 1) :=
    mul_nonneg (le_of_lt hp) (by omega)
  have hmul : 55 ^ n ≤ 55 ^ n * d := by nlinarith
  omega

theorem digitFinset_leading_sum (k : ℕ) (f : ℤ → ℚ) :
    (∑ z ∈ digitFinset (k + 1), f z) =
      (∑ z ∈ digitFinset 1, f z) +
        ∑ i ∈ Finset.range k, ∑ z ∈ leadingBlocks (i + 1), f z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs : (∑ z ∈ digitFinset ((k + 1) + 1), f z) =
          (∑ z ∈ digitFinset (k + 1), f z) +
            (∑ z ∈ leadingBlocks (k + 1), f z) := by
        rw [digitFinset_leading_partition, Finset.sum_union
          (digitFinset_disjoint_leading (k + 1))]
      calc
        (∑ z ∈ digitFinset ((k + 1) + 1), f z) =
            (∑ z ∈ digitFinset (k + 1), f z) +
              (∑ z ∈ leadingBlocks (k + 1), f z) := hs
        _ = (∑ z ∈ digitFinset 1, f z) +
              ∑ i ∈ Finset.range (k + 1), ∑ z ∈ leadingBlocks (i + 1), f z := by
          rw [ih, Finset.sum_range_succ]
          ring

/-- Uniqueness of a low digit block and its higher suffix. -/
theorem digitFinset_append_inj (m n : ℕ) :
    Set.InjOn (fun p : ℤ × ℤ => p.1 + 55 ^ m * p.2)
      ((digitFinset m).product (digitFinset n)) := by
  rintro ⟨t, d⟩ htd ⟨s, e⟩ hse hEq
  have ⟨ht, _⟩ := Finset.mem_product.mp htd
  have ⟨hs, _⟩ := Finset.mem_product.mp hse
  have ⟨ht0, ht1⟩ := digitFinset_bound m t ht
  have ⟨hs0, hs1⟩ := digitFinset_bound m s hs
  have hp : 0 < (55 : ℤ) ^ m := pow_pos (by omega) _
  dsimp at hEq
  have hmod := congrArg (fun z : ℤ => z % 55 ^ m) hEq
  rw [Int.add_mul_emod_self_left, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt ht0 ht1, Int.emod_eq_of_lt hs0 hs1] at hmod
  have hmul : 55 ^ m * d = 55 ^ m * e := by omega
  have hde : d = e := mul_left_cancel₀ (ne_of_gt hp) hmul
  exact Prod.ext hmod hde

/-- The 420 two-digit prefixes whose leading digit is nonzero. -/
def leadingPrefix : Finset ℤ :=
  ((walkerFinset.erase 0).product walkerFinset).image
    (fun p => 55 * p.1 + p.2)

theorem mem_leadingPrefix (p : ℤ) :
    p ∈ leadingPrefix ↔
      ∃ a ∈ walkerFinset, a ≠ 0 ∧
        ∃ b ∈ walkerFinset, p = 55 * a + b := by
  unfold leadingPrefix
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hpair, hEq⟩
    have ⟨ha, hb⟩ := Finset.mem_product.mp hpair
    have ⟨ha0, haD⟩ := Finset.mem_erase.mp ha
    exact ⟨a, haD, ha0, b, hb, hEq.symm⟩
  · rintro ⟨a, ha, ha0, b, hb, hEq⟩
    exact ⟨(a, b), Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨ha0, ha⟩, hb⟩, hEq.symm⟩

theorem mem_leadingPrefix_iff_blocks (p : ℤ) :
    p ∈ leadingPrefix ↔ p ∈ leadingBlocks 1 := by
  rw [mem_leadingPrefix, mem_leadingBlocks]
  simp only [digitFinset_one]
  constructor
  · rintro ⟨a, ha, ha0, b, hb, hEq⟩
    refine ⟨a, ha, ha0, b, hb, ?_⟩
    norm_num at hEq ⊢
    omega
  · rintro ⟨a, ha, ha0, b, hb, hEq⟩
    refine ⟨a, ha, ha0, b, hb, ?_⟩
    norm_num at hEq ⊢
    omega

theorem leadingPrefix_mem_two {p : ℤ} (hp : p ∈ leadingPrefix) :
    p ∈ digitFinset 2 := by
  rw [digitFinset_leading_partition 1]
  exact Finset.mem_union.mpr (Or.inr ((mem_leadingPrefix_iff_blocks p).mp hp))

theorem leadingPrefix_lower {p : ℤ} (hp : p ∈ leadingPrefix) : 55 ≤ p := by
  obtain ⟨a, ha, ha0, b, hb, hEq⟩ := (mem_leadingPrefix p).mp hp
  have ⟨ha0', _⟩ := walkerFinset_bound ha
  have ⟨hb0, _⟩ := walkerFinset_bound hb
  have ha1 : 1 ≤ a := by omega
  omega

/-- The new two-digit-prefix layer above all strings of length at most `j+1`. -/
def twoDigitLayer (j : ℕ) : Finset ℤ :=
  (leadingPrefix.product (digitFinset j)).image
    (fun p => 55 ^ j * p.1 + p.2)

theorem mem_twoDigitLayer (j : ℕ) (z : ℤ) :
    z ∈ twoDigitLayer j ↔
      ∃ p ∈ leadingPrefix, ∃ t ∈ digitFinset j,
        z = t + 55 ^ j * p := by
  unfold twoDigitLayer
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨p, t⟩, hpair, hEq⟩
    have ⟨hp, ht⟩ := Finset.mem_product.mp hpair
    refine ⟨p, hp, t, ht, ?_⟩
    calc
      z = 55 ^ j * p + t := hEq.symm
      _ = t + 55 ^ j * p := add_comm _ _
  · rintro ⟨p, hp, t, ht, hEq⟩
    refine ⟨(p, t), Finset.mem_product.mpr ⟨hp, ht⟩, ?_⟩
    calc
      55 ^ j * p + t = t + 55 ^ j * p := add_comm _ _
      _ = z := hEq.symm

theorem digitFinset_twoDigit_partition (j : ℕ) :
    digitFinset (j + 2) = digitFinset (j + 1) ∪ twoDigitLayer j := by
  ext z
  rw [Finset.mem_union, mem_digitFinset_append j 2 z, mem_twoDigitLayer]
  constructor
  · rintro ⟨t, ht, p, hp, hEq⟩
    rw [digitFinset_leading_partition 1] at hp
    rcases Finset.mem_union.mp hp with hpOld | hpNew
    · left
      exact (mem_digitFinset_append j 1 z).mpr ⟨t, ht, p, hpOld, hEq⟩
    · right
      exact ⟨p, (mem_leadingPrefix_iff_blocks p).mpr hpNew, t, ht, hEq⟩
  · rintro (hOld | ⟨p, hp, t, ht, hEq⟩)
    · obtain ⟨t, ht, d, hd, hEq⟩ := (mem_digitFinset_append j 1 z).mp hOld
      exact ⟨t, ht, d, digitFinset_mono_step 1 (by simpa [digitFinset_one] using hd), hEq⟩
    · exact ⟨t, ht, p, leadingPrefix_mem_two hp, hEq⟩

theorem digitFinset_disjoint_twoDigit (j : ℕ) :
    Disjoint (digitFinset (j + 1)) (twoDigitLayer j) := by
  apply Finset.disjoint_left.mpr
  intro z hz hLayer
  obtain ⟨p, hp, t, ht, hEq⟩ := (mem_twoDigitLayer j z).mp hLayer
  have hzlt := (digitFinset_bound (j + 1) z hz).2
  have ht0 := (digitFinset_bound j t ht).1
  have hpl := leadingPrefix_lower hp
  have hpow : 0 ≤ (55 : ℤ) ^ j := le_of_lt (pow_pos (by omega) _)
  have hmul : 55 ^ j * 55 ≤ 55 ^ j * p :=
    mul_le_mul_of_nonneg_left hpl hpow
  rw [pow_succ] at hzlt
  omega

theorem digitFinset_prefix_sum (k : ℕ) (f : ℤ → ℚ) :
    (∑ z ∈ digitFinset (k + 2), f z) =
      (∑ z ∈ digitFinset 2, f z) +
        ∑ i ∈ Finset.range k, ∑ z ∈ twoDigitLayer (i + 1), f z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs : (∑ z ∈ digitFinset ((k + 1) + 2), f z) =
          (∑ z ∈ digitFinset ((k + 1) + 1), f z) +
            (∑ z ∈ twoDigitLayer (k + 1), f z) := by
        rw [digitFinset_twoDigit_partition, Finset.sum_union
          (digitFinset_disjoint_twoDigit (k + 1))]
      calc
        (∑ z ∈ digitFinset ((k + 1) + 2), f z) =
            (∑ z ∈ digitFinset (k + 2), f z) +
              (∑ z ∈ twoDigitLayer (k + 1), f z) := by simpa [Nat.add_assoc] using hs
        _ = (∑ z ∈ digitFinset 2, f z) +
              ∑ i ∈ Finset.range (k + 1), ∑ z ∈ twoDigitLayer (i + 1), f z := by
          rw [ih, Finset.sum_range_succ]
          ring

theorem leadingBlocks_sum (n : ℕ) (f : ℤ → ℚ) :
    (∑ z ∈ leadingBlocks n, f z) =
      ∑ d ∈ walkerFinset.erase 0, ∑ t ∈ digitFinset n,
        f (t + 55 ^ n * d) := by
  have hEq : leadingBlocks n =
      ((walkerFinset.erase 0).product (digitFinset n)).image
        (fun p => p.2 + 55 ^ n * p.1) := by
    ext z
    rw [mem_leadingBlocks, Finset.mem_image]
    constructor
    · rintro ⟨d, hd, hd0, t, ht, hEq⟩
      exact ⟨(d, t), Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨hd0, hd⟩, ht⟩, hEq.symm⟩
    · rintro ⟨⟨d, t⟩, hpair, hEq⟩
      have ⟨hd, ht⟩ := Finset.mem_product.mp hpair
      have ⟨hd0, hdD⟩ := Finset.mem_erase.mp hd
      exact ⟨d, hdD, hd0, t, ht, hEq.symm⟩
  have hi : Set.InjOn (fun p : ℤ × ℤ => p.2 + 55 ^ n * p.1)
      ((walkerFinset.erase 0).product (digitFinset n)) := by
    rintro ⟨d, t⟩ hp ⟨e, s⟩ hq hval
    have ⟨hd, ht⟩ := Finset.mem_product.mp hp
    have ⟨he, hs⟩ := Finset.mem_product.mp hq
    have hp' : (t, d) ∈ (digitFinset n).product (digitFinset 1) :=
      Finset.mem_product.mpr ⟨ht, by
        rw [digitFinset_one]
        exact (Finset.mem_erase.mp hd).2⟩
    have hq' : (s, e) ∈ (digitFinset n).product (digitFinset 1) :=
      Finset.mem_product.mpr ⟨hs, by
        rw [digitFinset_one]
        exact (Finset.mem_erase.mp he).2⟩
    have hswap := digitFinset_append_inj n 1 hp' hq' hval
    exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
  rw [hEq, Finset.sum_image hi, Finset.product_eq_sprod, Finset.sum_product]

theorem twoDigitLayer_sum (j : ℕ) (f : ℤ → ℚ) :
    (∑ z ∈ twoDigitLayer j, f z) =
      ∑ p ∈ leadingPrefix, ∑ t ∈ digitFinset j,
        f (55 ^ j * p + t) := by
  have hi : Set.InjOn (fun p : ℤ × ℤ => 55 ^ j * p.1 + p.2)
      (leadingPrefix.product (digitFinset j)) := by
    rintro ⟨p, t⟩ hp ⟨q, s⟩ hq hval
    have ⟨hpP, ht⟩ := Finset.mem_product.mp hp
    have ⟨hqP, hs⟩ := Finset.mem_product.mp hq
    have hp' : (t, p) ∈ (digitFinset j).product (digitFinset 2) :=
      Finset.mem_product.mpr ⟨ht, leadingPrefix_mem_two hpP⟩
    have hq' : (s, q) ∈ (digitFinset j).product (digitFinset 2) :=
      Finset.mem_product.mpr ⟨hs, leadingPrefix_mem_two hqP⟩
    have hswap := digitFinset_append_inj j 2 hp' hq' (by simpa only [add_comm] using hval)
    exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
  rw [twoDigitLayer, Finset.sum_image hi,
    Finset.product_eq_sprod, Finset.sum_product]

/-- Finite realization of the unshifted old block and six new fibres. -/
def sixEFinset : Finset ℤ :=
  digitFinset 22 ∪
    (ErdosSixIndependent.U.product (digitFinset 21)).image
      (fun p => (p.1 : ℤ) + 166375 * p.2)

/-- The positive finite set used in the `4.44` reciprocal bound. -/
def sixAFinset : Finset ℤ := sixEFinset.image (· + 1)

theorem mem_sixEFinset (z : ℤ) : z ∈ sixEFinset ↔ z ∈ sixE := by
  unfold sixEFinset sixE
  rw [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl ((mem_digitFinset 22 z).mp h)
    · obtain ⟨⟨u, t⟩, hpair, hEq⟩ := Finset.mem_image.mp h
      have ⟨hu, ht⟩ := Finset.mem_product.mp hpair
      exact Or.inr ⟨u, hu, t, (mem_digitFinset 21 t).mp ht, hEq.symm⟩
  · rintro (h | ⟨u, hu, t, ht, hEq⟩)
    · exact Or.inl ((mem_digitFinset 22 z).mpr h)
    · exact Or.inr <| Finset.mem_image.mpr
        ⟨(u, t), Finset.mem_product.mpr ⟨hu, (mem_digitFinset 21 t).mpr ht⟩,
          hEq.symm⟩

theorem mem_sixAFinset (z : ℤ) : z ∈ sixAFinset ↔ z ∈ sixA := by
  unfold sixAFinset sixA
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e, he, hEq⟩
    have hE := (mem_sixEFinset e).mp he
    have hz : z - 1 = e := by omega
    change z - 1 ∈ sixE
    rwa [hz]
  · intro hz
    change z - 1 ∈ sixE at hz
    exact ⟨z - 1, (mem_sixEFinset _).mpr hz, by omega⟩

end Erdos3Candidate
