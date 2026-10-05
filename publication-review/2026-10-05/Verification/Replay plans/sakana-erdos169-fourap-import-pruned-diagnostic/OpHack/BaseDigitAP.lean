import OpHack.DigitDescent
import OpHack.ErdosSingletonFinite

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos3Candidate

/-- Walker's 21 digits, regarded as integers. -/
def walkerDigits : Set ℤ := {z | 0 ≤ z ∧ z.toNat ∈ ErdosSingletonIndependent.D}

theorem walkerDigits_bound : ∀ z ∈ walkerDigits, 0 ≤ z ∧ z < 55 := by
  intro z hz
  rcases hz with ⟨h0, hD⟩
  have hmax : z.toNat ≤ 47 := by
    simp [ErdosSingletonIndependent.D] at hD
    omega
  omega

theorem walkerDigits_modular_free : ModularAPFree 4 55 walkerDigits := by
  intro a step hn hAP
  have hstep : step % 55 ≠ 0 := by
    simpa only [Int.dvd_iff_emod_eq_zero] using hn
  let an : ℕ := (a % 55).toNat
  let dn : ℕ := (step % 55).toNat
  have ha : an < 55 := by dsimp [an]; omega
  have hd : 1 ≤ dn ∧ dn ≤ 54 := by dsimp [dn]; omega
  have h0 : a % 55 ∈ walkerDigits := by simpa using hAP (0 : Fin 4)
  have h1 : (a + step) % 55 ∈ walkerDigits := by simpa using hAP (1 : Fin 4)
  have h2 : (a + 2 * step) % 55 ∈ walkerDigits := by simpa using hAP (2 : Fin 4)
  have h3 : (a + 3 * step) % 55 ∈ walkerDigits := by simpa using hAP (3 : Fin 4)
  have heq1 : (an + dn) % 55 = ((a + step) % 55).toNat := by dsimp [an, dn]; omega
  have heq2 : (an + 2 * dn) % 55 = ((a + 2 * step) % 55).toNat := by dsimp [an, dn]; omega
  have heq3 : (an + 3 * dn) % 55 = ((a + 3 * step) % 55).toNat := by dsimp [an, dn]; omega
  have hmem : (an, dn) ∈ ErdosSingletonIndependent.badBasePairs := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · simp [ha]
      · simpa using hd
    · change an ∈ ErdosSingletonIndependent.D ∧
        (an + dn) % 55 ∈ ErdosSingletonIndependent.D ∧
        (an + 2 * dn) % 55 ∈ ErdosSingletonIndependent.D ∧
        (an + 3 * dn) % 55 ∈ ErdosSingletonIndependent.D
      dsimp [walkerDigits] at h0 h1 h2 h3
      rw [heq1, heq2, heq3]
      exact ⟨h0.2, h1.2, h2.2, h3.2⟩
  rw [ErdosSingletonIndependent.base_modular_four_free] at hmem
  simpa using hmem

/-- The base-55 digit sets are four-AP-free for every finite length. -/
theorem walkerDigitSet_apFree (n : ℕ) : APFree 4 (digitSet walkerDigits n) :=
  digitSet_apFree walkerDigits walkerDigits_bound walkerDigits_modular_free n

end Erdos3Candidate
