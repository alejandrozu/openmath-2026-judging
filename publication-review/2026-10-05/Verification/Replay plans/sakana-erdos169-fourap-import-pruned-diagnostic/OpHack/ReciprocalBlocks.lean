import OpHack.FiniteHarmonicMean

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos3Candidate

/-- A suffix block lower bound from its exact cardinality and digit sum. -/
theorem old_suffix_block_lower (s : Finset ℤ) (j : ℕ) (p : ℕ)
    (hj : 1 ≤ j)
    (hcard : s.card = 21 ^ j)
    (hsum : (∑ x ∈ s, (x : ℚ)) =
      (s.card : ℚ) * (433 / 1134) * ((55 : ℚ) ^ j - 1))
    (hnonneg : ∀ x ∈ s, 0 ≤ x) :
    ((21 / 55 : ℚ) ^ j) / ((p : ℚ) + 454 / 1155) ≤
      ∑ x ∈ s, 1 / ((p : ℚ) * (55 : ℚ) ^ j + x + 1) := by
  let P : ℚ := (55 : ℚ) ^ j
  let C : ℚ := (p : ℚ) + 454 / 1155
  let B : ℚ := P * C
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPle : (55 : ℚ) ≤ P := by
    dsimp [P]
    exact le_self_pow₀ (by norm_num) (by omega)
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hBpos : 0 < B := mul_pos hPpos hCpos
  have hNpos : (0 : ℚ) ≤ s.card := by positivity
  have hsne : s.Nonempty := Finset.card_pos.mp (by rw [hcard]; positivity)
  have hcoeff : 1 + (433 / 1134 : ℚ) * (P - 1) ≤ P * (454 / 1155 : ℚ) := by
    nlinarith
  have hsumF :
      (∑ x ∈ s, ((p : ℚ) * P + (x : ℚ) + 1)) =
        (s.card : ℚ) * ((p : ℚ) * P + 1) + ∑ x ∈ s, (x : ℚ) := by
    simp [Finset.sum_add_distrib]
    ring
  have hmean :
      (∑ x ∈ s, ((p : ℚ) * P + (x : ℚ) + 1)) ≤ (s.card : ℚ) * B := by
    rw [hsumF, hsum]
    dsimp [B, C]
    nlinarith [mul_nonneg hNpos (sub_nonneg.mpr hcoeff)]
  have hpos : ∀ x ∈ s, 0 < (p : ℚ) * P + (x : ℚ) + 1 := by
    intro x hx
    have hx0 : (0 : ℚ) ≤ x := by exact_mod_cast hnonneg x hx
    positivity
  have hh := finite_harmonic_mean_bound s
    (fun x : ℤ => (p : ℚ) * P + x + 1) hsne B hBpos hpos hmean
  dsimp [B, C, P] at hh
  rw [hcard] at hh
  convert hh using 1
  · rw [div_pow]
    field_simp
    norm_cast


end Erdos3Candidate
