import OpHack.FloorBounds
import OpHack.HarmonicCertificate
import OpHack.SixHarmonicCertificate

namespace Erdos3Candidate

theorem floor_flatmap_le (us ds : List ℕ) (Q N : ℕ)
    (D : ℕ → ℕ → ℕ) (hQ : 0 < Q)
    (hD : ∀ u ∈ us, ∀ d ∈ ds, 0 < D u d) :
    (((us.flatMap fun u => ds.map fun d => N * Q / D u d).sum : ℕ) : ℚ) / Q ≤
      (us.flatMap fun u => ds.map fun d => (N : ℚ) / D u d).sum := by
  induction us with
  | nil => simp
  | cons u us ih =>
      have hDu : ∀ d ∈ ds, 0 < D u d := hD u (by simp)
      have hDus : ∀ v ∈ us, ∀ d ∈ ds, 0 < D v d := by
        intro v hv d hd
        exact hD v (by simp [hv]) d hd
      simp only [List.flatMap_cons, List.sum_append, Nat.cast_add, add_div]
      exact add_le_add (floor_list_le ds Q N (D u) hQ hDu) (ih hDus)

open HarmonicCertificate SixHarmonicCertificate

set_option maxRecDepth 100000 in
theorem old_prefixes_nodup : HarmonicCertificate.prefixes.Nodup := by decide

set_option maxRecDepth 100000 in
theorem old_leading_prefix_nodup :
    HarmonicCertificate.leadingPrefix.Nodup := by decide

set_option maxRecDepth 100000 in
theorem six_extensions_nodup :
    SixHarmonicCertificate.extensions.Nodup := by decide

set_option maxRecDepth 100000 in
theorem six_digits_nodup :
    SixHarmonicCertificate.digits.Nodup := by decide

/-- The exact old two-digit singleton sum dominates its downward floor. -/
theorem old_prefix_floor_le :
    (3875802807082000 : ℚ) / 10^15 ≤
      (HarmonicCertificate.prefixes.map fun (p : ℕ) =>
        (1 : ℚ) / ((p + 1 : ℕ) : ℚ)).sum := by
  have h := floor_list_le HarmonicCertificate.prefixes (10^12) 1
    (fun p => p + 1) (by norm_num) (by intro p hp; omega)
  change ((HarmonicCertificate.prefixFloorSum : ℚ) / 10^12) ≤ _ at h
  rw [HarmonicCertificate.prefixFloorSum_value] at h
  have hs : (3875802807082000 : ℚ) / 10^15 = 3875802807082 / 10^12 := by
    norm_num
  rw [hs]
  exact h

/-- The exact old two-digit tail coefficient dominates its downward floor. -/
theorem old_tail_floor_le :
    (913030252293000 : ℚ) / 10^15 ≤
      (HarmonicCertificate.leadingPrefix.map
        fun (p : ℕ) => (1 : ℚ) / ((p : ℚ) + 454 / 1155)).sum := by
  have h := floor_list_le HarmonicCertificate.leadingPrefix (10^12) 1155
    (fun p => 1155 * p + 454) (by norm_num) (by intro p hp; omega)
  change ((HarmonicCertificate.tailFloorSum : ℚ) / 10^12) ≤ _ at h
  rw [HarmonicCertificate.tailFloorSum_value] at h
  have hterm (p : ℕ) :
      (1155 : ℚ) / ((1155 * p + 454 : ℕ) : ℚ) =
        1 / ((p : ℚ) + 454 / 1155) := by
    push_cast
    have hp : (0 : ℚ) ≤ p := Nat.cast_nonneg p
    have hden : (0 : ℚ) < 1155 * (p : ℚ) + 454 := by positivity
    have hden' : (0 : ℚ) < (p : ℚ) + 454 / 1155 := by positivity
    field_simp [ne_of_gt hden, ne_of_gt hden']
  have hs : (913030252293000 : ℚ) / 10^15 = 913030252293 / 10^12 := by
    norm_num
  rw [hs]
  have hlist :
      (HarmonicCertificate.leadingPrefix.map fun (p : ℕ) =>
        (1155 : ℚ) / ((1155 * p + 454 : ℕ) : ℚ)) =
      (HarmonicCertificate.leadingPrefix.map fun (p : ℕ) =>
        (1 : ℚ) / ((p : ℚ) + 454 / 1155)) := by
    apply List.map_congr_left
    intro p hp
    exact hterm p
  exact h.trans (le_of_eq (congrArg List.sum hlist))

/-- The six new fibre singleton sums dominate their integer floor certificate. -/
theorem new_prefix_floor_le :
    (222203111618 : ℚ) / 10^15 ≤
      (SixHarmonicCertificate.extensions.flatMap fun (u : ℕ) =>
        SixHarmonicCertificate.digits.map fun (d : ℕ) =>
          (1 : ℚ) / ((166375*d+u+1 : ℕ) : ℚ)).sum := by
  have h := floor_flatmap_le SixHarmonicCertificate.extensions
    SixHarmonicCertificate.digits (10^15) 1
    (fun u d => 166375*d+u+1) (by norm_num)
    (by intro u hu d hd; omega)
  change ((SixHarmonicCertificate.newPrefixFloor : ℚ) / 10^15) ≤ _ at h
  rw [SixHarmonicCertificate.newPrefixFloor_value] at h
  exact h

/-- The new-fibre tail coefficient, using the common unshifted suffix bound. -/
def simpleNewTailFloor : ℕ :=
  (SixHarmonicCertificate.extensions.flatMap fun _u =>
    (SixHarmonicCertificate.digits.filter (fun d => d != 0)).map fun d =>
      1155 * 10^15 / (166375 * (1155*d+454))).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem simpleNewTailFloor_value : simpleNewTailFloor = 84575370288 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem simple_six_lower_certificate_gt :
    ((3875802807082000 + 222203111618 : ℚ) / 10^15) +
      ((913030252293000 + 84575370288 : ℚ) / 10^15) *
        (∑ j ∈ Finset.range 20, (21 / 55 : ℚ)^(j+1)) > 111 / 25 := by
  norm_num [Finset.sum_range_succ]

/-- Each common tail coefficient exceeds its downward floor. -/
theorem simple_new_tail_floor_le :
    (84575370288 : ℚ) / 10^15 ≤
      (SixHarmonicCertificate.extensions.flatMap fun (_u : ℕ) =>
        (SixHarmonicCertificate.digits.filter (fun d => d != 0)).map
          fun (d : ℕ) => (1 : ℚ) / (166375 * ((d : ℚ) + 454/1155))).sum := by
  have h := floor_flatmap_le SixHarmonicCertificate.extensions
    (SixHarmonicCertificate.digits.filter (fun d => d != 0)) (10^15) 1155
    (fun _u d => 166375*(1155*d+454)) (by norm_num)
    (by intro u hu d hd; omega)
  change ((simpleNewTailFloor : ℚ) / 10^15) ≤ _ at h
  rw [simpleNewTailFloor_value] at h
  have hterm (d : ℕ) :
      (1155 : ℚ) / ((166375*(1155*d+454) : ℕ) : ℚ) =
        1 / (166375 * ((d : ℚ) + 454/1155)) := by
    push_cast
    have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d
    have hden : (0 : ℚ) < 166375 * (1155 * (d : ℚ) + 454) := by positivity
    have hden' : (0 : ℚ) < 166375 * ((d : ℚ) + 454 / 1155) := by positivity
    field_simp [ne_of_gt hden, ne_of_gt hden']
  have hlist :
      (SixHarmonicCertificate.extensions.flatMap fun (_u : ℕ) =>
        (SixHarmonicCertificate.digits.filter (fun d => d != 0)).map
          fun (d : ℕ) =>
            (1155 : ℚ) / ((166375 * (1155*d+454) : ℕ) : ℚ)) =
      (SixHarmonicCertificate.extensions.flatMap fun (_u : ℕ) =>
        (SixHarmonicCertificate.digits.filter (fun d => d != 0)).map
          fun (d : ℕ) =>
            (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155))) := by
    apply List.flatMap_congr
    intro u hu
    apply List.map_congr_left
    intro d hd
    exact hterm d
  exact h.trans (le_of_eq (congrArg List.sum hlist))

end Erdos3Candidate
