import OpHack.ResidueFibre

namespace Erdos3Candidate

/-- Integers with at most `n` base-55 digits from `D`, with leading zero allowed. -/
def digitSet (D : Set ℤ) : ℕ → Set ℤ
  | 0 => {0}
  | n + 1 => {z | ∃ d ∈ D, ∃ t ∈ digitSet D n, z = d + 55 * t}

/-- A modularly four-AP-free digit alphabet gives four-AP-free finite digit sets. -/
theorem digitSet_apFree (D : Set ℤ)
    (hBound : ∀ d ∈ D, 0 ≤ d ∧ d < 55)
    (hMod : ModularAPFree 4 55 D) (n : ℕ) :
    APFree 4 (digitSet D n) := by
  induction n with
  | zero =>
      intro a step hstep hAP
      have h0 := hAP (0 : Fin 4)
      have h1 := hAP (1 : Fin 4)
      change a + ((0 : Fin 4) : ℤ) * step ∈ ({0} : Set ℤ) at h0
      change a + ((1 : Fin 4) : ℤ) * step ∈ ({0} : Set ℤ) at h1
      simp at h0 h1
      omega
  | succ n ih =>
      intro a step hstep hAP
      have hSupport : ∀ i : Fin 4, (a + (i : ℤ) * step) % 55 ∈ D := by
        intro i
        obtain ⟨d, hd, t, ht, heq⟩ := hAP i
        have hbd := hBound d hd
        have hrem : (a + (i : ℤ) * step) % 55 = d := by
          rw [heq]
          omega
        rw [hrem]
        exact hd
      have hdiv : (55 : ℤ) ∣ step := by
        by_contra hn
        exact hMod a step hn hSupport
      obtain ⟨e, he⟩ := hdiv
      have he0 : e ≠ 0 := by
        intro hz
        apply hstep
        simp [he, hz]
      have hzero := hAP (0 : Fin 4)
      obtain ⟨d0, hd0, t0, ht0, ha⟩ := hzero
      have ha' : a = d0 + 55 * t0 := by simpa using ha
      have hTail : ∀ i : Fin 4, t0 + (i : ℤ) * e ∈ digitSet D n := by
        intro i
        obtain ⟨di, hdi, ti, hti, hi⟩ := hAP i
        have hEq : di + 55 * ti = d0 + 55 * (t0 + (i : ℤ) * e) := by
          calc
            di + 55 * ti = a + (i : ℤ) * step := hi.symm
            _ = d0 + 55 * (t0 + (i : ℤ) * e) := by rw [ha', he]; ring
        have hbd0 := hBound d0 hd0
        have hbdi := hBound di hdi
        have htiEq : ti = t0 + (i : ℤ) * e := by omega
        rw [← htiEq]
        exact hti
      exact ih t0 e he0 hTail

end Erdos3Candidate
