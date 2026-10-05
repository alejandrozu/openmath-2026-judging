import OpHack.ErdosSixFinite

/-! A direct comparison of every new-fibre reciprocal with an unshifted
    base-55 digit reciprocal. No block counting assumptions are used here. -/
namespace Erdos3Candidate

/-- Each new-fibre denominator is at most `166375` times the denominator
    obtained by replacing its residue by the maximal canonical offset. -/
theorem six_new_termwise (u : ℕ) (t : ℤ)
    (ht : 0 ≤ t) (hu : u + 1 ≤ 166375) :
    (1 : ℚ) / 166375 / ((t : ℚ) + 1) ≤
      1 / (166375 * (t : ℚ) + (u : ℚ) + 1) := by
  have htq : (0 : ℚ) ≤ t := by exact_mod_cast ht
  have huq : (u : ℚ) + 1 ≤ 166375 := by exact_mod_cast hu
  have hden : (0 : ℚ) < 166375 * (t : ℚ) + (u : ℚ) + 1 := by
    have hu0 : (0 : ℚ) ≤ u := Nat.cast_nonneg u
    nlinarith
  have hle : 166375 * (t : ℚ) + (u : ℚ) + 1 ≤
      166375 * ((t : ℚ) + 1) := by nlinarith
  calc
    (1 : ℚ) / 166375 / ((t : ℚ) + 1) =
        1 / (166375 * ((t : ℚ) + 1)) := by simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
    _ ≤ 1 / (166375 * (t : ℚ) + (u : ℚ) + 1) :=
      one_div_le_one_div_of_le hden hle

/-- The six concrete residues all satisfy the canonical-offset bound. -/
theorem six_new_termwise_of_mem (u : ℕ) (hu : u ∈ ErdosSixIndependent.U)
    (t : ℤ) (ht : 0 ≤ t) :
    (1 : ℚ) / 166375 / ((t : ℚ) + 1) ≤
      1 / (166375 * (t : ℚ) + (u : ℚ) + 1) := by
  apply six_new_termwise u t ht
  have hbound : u < ErdosSixIndependent.M :=
    (ErdosSixIndependent.new_residue_data u hu).1
  change u < 166375 at hbound
  omega

#print axioms six_new_termwise
#print axioms six_new_termwise_of_mem

end Erdos3Candidate
