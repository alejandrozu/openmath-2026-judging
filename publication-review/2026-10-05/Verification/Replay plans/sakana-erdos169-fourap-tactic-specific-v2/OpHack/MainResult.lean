import OpHack.SixFinalAP
import OpHack.SixFinalReciprocal

namespace Erdos3Candidate

/-- The finite realization is exactly the set used by the AP proof. -/
theorem sixAFinset_coe : (sixAFinset : Set ℤ) = sixA := by
  ext a
  exact mem_sixAFinset a

theorem sixAFinset_apFree : APFree 4 (sixAFinset : Set ℤ) := by
  rw [sixAFinset_coe]
  exact sixA_apFree_unconditional

/-- The explicit positive finite construction is four-AP-free and its rational
    reciprocal sum exceeds `111/25`. Every hypothesis is discharged here. -/
theorem explicit_four_ap_free_reciprocal_gt :
    (∀ a ∈ sixAFinset, 0 < a) ∧
      APFree 4 (sixAFinset : Set ℤ) ∧
      (∑ a ∈ sixAFinset, (1 : ℚ) / (a : ℚ)) > 111 / 25 := by
  exact ⟨sixAFinset_positive, sixAFinset_apFree,
    sixA_reciprocal_gt_unconditional⟩

#print axioms explicit_four_ap_free_reciprocal_gt

end Erdos3Candidate
