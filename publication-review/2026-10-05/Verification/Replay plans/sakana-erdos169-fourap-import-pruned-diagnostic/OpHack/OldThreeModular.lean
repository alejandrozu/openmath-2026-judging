import OpHack.BaseDigitAP

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos3Candidate

/-- Three canonical base-55 digits drawn from Walker's alphabet. -/
def oldThreeResidues (z : ℤ) : Prop :=
  z % 55 ∈ walkerDigits ∧ (z / 55) % 55 ∈ walkerDigits ∧
    (z / 3025) % 55 ∈ walkerDigits

/-- Digit descent modulo 55³. -/
theorem oldThree_modular_free : ModularAPFree 4 166375 oldThreeResidues := by
  intro a step hnonzero hAP
  by_cases h55 : (55 : ℤ) ∣ step
  · by_cases h3025 : (3025 : ℤ) ∣ step
    · have hfactor : step = 3025 * (step / 3025) := by
        rcases h3025 with ⟨q, hq⟩
        omega
      have hnot : ¬ (55 : ℤ) ∣ step / 3025 := by
        intro hq
        rcases hq with ⟨q, hq⟩
        apply hnonzero
        refine ⟨q, ?_⟩
        omega
      apply walkerDigits_modular_free (a / 3025) (step / 3025) hnot
      intro i
      have hi := (hAP i).2.2
      have hlin : a + (i : ℤ) * step = a + 3025 * ((i : ℤ) * (step / 3025)) := by
        conv_lhs => rw [hfactor]
        ring
      rw [hlin] at hi
      convert hi using 1 <;> omega
    · have hfactor : step = 55 * (step / 55) := by
        rcases h55 with ⟨q, hq⟩
        omega
      have hnot : ¬ (55 : ℤ) ∣ step / 55 := by
        intro hq
        rcases hq with ⟨q, hq⟩
        apply h3025
        refine ⟨q, ?_⟩
        omega
      apply walkerDigits_modular_free (a / 55) (step / 55) hnot
      intro i
      have hi := (hAP i).2.1
      have hlin : a + (i : ℤ) * step = a + 55 * ((i : ℤ) * (step / 55)) := by
        conv_lhs => rw [hfactor]
        ring
      rw [hlin] at hi
      convert hi using 1 <;> omega
  · apply walkerDigits_modular_free a step h55
    intro i
    have hi := (hAP i).1
    convert hi using 1 <;> omega

end Erdos3Candidate
