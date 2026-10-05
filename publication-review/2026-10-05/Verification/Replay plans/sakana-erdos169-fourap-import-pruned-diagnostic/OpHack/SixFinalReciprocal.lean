import OpHack.SixListBridge
import OpHack.SixHarmonicAggregation

/-! The exact finite six-fibre reciprocal sum exceeds `111/25`.
The singleton prefix terms keep their actual six residue offsets. Only
positive-length suffix layers use the uniform comparison. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Erdos3Candidate

theorem old_prefix_finset_floor_le :
    (3875802807082000 : ℚ) / 10^15 ≤
      ∑ t ∈ digitFinset 2, (1 : ℚ) / ((t : ℚ) + 1) := by
  rw [← old_prefix_list_sum]
  simpa only [Nat.cast_add, Nat.cast_one] using old_prefix_floor_le

theorem old_tail_finset_floor_le :
    (913030252293000 : ℚ) / 10^15 ≤
      ∑ p ∈ leadingPrefix, (1 : ℚ) / ((p : ℚ) + 454 / 1155) := by
  rw [← old_tail_list_sum]
  exact old_tail_floor_le

theorem six_new_prefix_finset_floor_le :
    (222203111618 : ℚ) / 10^15 ≤
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset,
          (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1) := by
  rw [← new_prefix_list_sum]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    new_prefix_floor_le

theorem six_new_tail_finset_floor_le :
    (84575370288 : ℚ) / 10^15 ≤
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset.erase 0,
          (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155)) := by
  rw [← new_tail_list_sum]
  exact simple_new_tail_floor_le

/-- The actual finite reciprocal sum dominates a kernel-checked rational certificate. -/
theorem six_reciprocal_certificate_lower :
    ((3875802807082000 + 222203111618 : ℚ) / 10^15) +
      ((913030252293000 + 84575370288 : ℚ) / 10^15) *
        (∑ j ∈ Finset.range 20, (21 / 55 : ℚ)^(j+1)) ≤
      ∑ a ∈ sixAFinset, (1 : ℚ) / (a : ℚ) := by
  have hprefix := add_le_add old_prefix_finset_floor_le six_new_prefix_finset_floor_le
  have htail := add_le_add old_tail_finset_floor_le six_new_tail_finset_floor_le
  have hweight : (0 : ℚ) ≤
      ∑ j ∈ Finset.range 20, (21 / 55 : ℚ)^(j+1) := by
    exact Finset.sum_nonneg (fun j _ => by positivity)
  have hcombined := add_le_add hprefix (mul_le_mul_of_nonneg_right htail hweight)
  apply le_trans ?_ six_reciprocal_weighted_lower
  convert hcombined using 1 <;> ring

/-- Unconditional reciprocal bound for the explicit positive finite six-fibre set. -/
theorem sixA_reciprocal_gt_unconditional :
    (∑ a ∈ sixAFinset, (1 : ℚ) / (a : ℚ)) > 111 / 25 := by
  exact lt_of_lt_of_le simple_six_lower_certificate_gt six_reciprocal_certificate_lower

#print axioms six_reciprocal_certificate_lower
#print axioms sixA_reciprocal_gt_unconditional

end Erdos3Candidate
