import OpHack.OldThreeModular
import OpHack.ErdosSixFinite

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos3Candidate

local notation "M" => (166375 : ℤ)

def sixResidueSupport (z : ℤ) : Prop :=
  oldThreeResidues z ∨ z.toNat ∈ ErdosSixIndependent.U

/-- The old 22-digit block together with six 21-digit fibres. -/
def sixE : Set ℤ :=
  digitSet walkerDigits 22 ∪
    {x | ∃ u : ℕ, u ∈ ErdosSixIndependent.U ∧
      ∃ t ∈ digitSet walkerDigits 21, x = (u : ℤ) + M * t}

/-- The positive version of the finite set used for the reciprocal sum. -/
def sixA : Set ℤ := {x | x - 1 ∈ sixE}

/-- The original block has a canonical three-digit residue and a 19-digit tail. -/
theorem old_block_decomp {x : ℤ} (hx : x ∈ digitSet walkerDigits 22) :
    ∃ s t : ℤ, 0 ≤ s ∧ s < M ∧ oldThreeResidues s ∧
      t ∈ digitSet walkerDigits 19 ∧ x = s + M * t := by
  change (∃ d0 ∈ walkerDigits, ∃ t0 ∈ digitSet walkerDigits 21,
    x = d0 + 55 * t0) at hx
  rcases hx with ⟨d0, hd0, t0, ht0, hx⟩
  change (∃ d1 ∈ walkerDigits, ∃ t1 ∈ digitSet walkerDigits 20,
    t0 = d1 + 55 * t1) at ht0
  rcases ht0 with ⟨d1, hd1, t1, ht1, ht0⟩
  change (∃ d2 ∈ walkerDigits, ∃ t2 ∈ digitSet walkerDigits 19,
    t1 = d2 + 55 * t2) at ht1
  rcases ht1 with ⟨d2, hd2, t2, ht2, ht1⟩
  refine ⟨d0 + 55 * d1 + 3025 * d2, t2, ?_, ?_, ?_, ht2, ?_⟩
  · have h0 := walkerDigits_bound d0 hd0
    have h1 := walkerDigits_bound d1 hd1
    have h2 := walkerDigits_bound d2 hd2
    omega
  · have h0 := walkerDigits_bound d0 hd0
    have h1 := walkerDigits_bound d1 hd1
    have h2 := walkerDigits_bound d2 hd2
    omega
  · have h0 := walkerDigits_bound d0 hd0
    have h1 := walkerDigits_bound d1 hd1
    have h2 := walkerDigits_bound d2 hd2
    dsimp [oldThreeResidues]
    constructor
    · convert hd0 using 1 <;> omega
    constructor
    · convert hd1 using 1 <;> omega
    · convert hd2 using 1 <;> omega
  · rw [hx, ht0, ht1]
    ring

private theorem new_not_old {u : ℕ} (hu : u ∈ ErdosSixIndependent.U) :
    ¬ oldThreeResidues (u : ℤ) := by
  simp only [ErdosSixIndependent.U, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with h | h | h | h | h | h
  all_goals subst u
  all_goals norm_num [oldThreeResidues, walkerDigits, ErdosSingletonIndependent.D]

private theorem six_support {x : ℤ} (hx : x ∈ sixE) :
    sixResidueSupport (x % M) := by
  rcases hx with hOld | hNew
  · obtain ⟨s, t, hs0, hsM, hsOld, ht, hEq⟩ := old_block_decomp hOld
    have hrem : x % M = s := by rw [hEq]; omega
    rw [hrem]
    exact Or.inl hsOld
  · obtain ⟨u, hu, t, ht, hEq⟩ := hNew
    have huM : u < 166375 := (ErdosSixIndependent.new_residue_data u hu).1
    have hrem : x % M = u := by rw [hEq]; omega
    rw [hrem]
    exact Or.inr (by simpa using hu)

/-- Conditional AP-freeness, requiring only the joint finite modular certificate. -/
theorem sixA_apFree (hS : ModularAPFree 4 M sixResidueSupport) : APFree 4 sixA := by
  intro a d hd hAP
  have hE : ∀ i : Fin 4, a - 1 + (i : ℤ) * d ∈ sixE := by
    intro i
    have hi := hAP i
    change a + (i : ℤ) * d - 1 ∈ sixE at hi
    convert hi using 1 <;> ring
  have hdiv : M ∣ d := by
    by_contra hn
    exact hS (a - 1) d hn (fun i => six_support (hE i))
  obtain ⟨e, he⟩ := hdiv
  have he0 : e ≠ 0 := by
    intro hz
    apply hd
    simp [he, hz]
  let r : ℤ := (a - 1) % M
  let t0 : ℤ := (a - 1) / M
  have hr0 : 0 ≤ r := by dsimp [r]; omega
  have hrM : r < M := by dsimp [r]; omega
  have ha : a - 1 = r + M * t0 := by dsimp [r, t0]; omega
  have hiEq (i : Fin 4) : a - 1 + (i : ℤ) * d = r + M * (t0 + (i : ℤ) * e) := by
    rw [ha, he]; ring
  have hiRem (i : Fin 4) : (a - 1 + (i : ℤ) * d) % M = r := by
    rw [hiEq]; omega
  rcases hE (0 : Fin 4) with hOld | hNew
  · obtain ⟨s, t, hs0, hsM, hsOld, ht, hEq⟩ := old_block_decomp hOld
    have hs : s = r := by
      have : (a - 1 + ((0 : Fin 4) : ℤ) * d) % M = s := by rw [hEq]; omega
      simpa [hiRem] using this.symm
    apply walkerDigitSet_apFree 19 t0 e he0
    intro i
    rcases hE i with hOldI | hNewI
    · obtain ⟨si, ti, hsi0, hsiM, hsiOld, hti, hEqI⟩ := old_block_decomp hOldI
      have hsi : si = r := by
        have : (a - 1 + (i : ℤ) * d) % M = si := by rw [hEqI]; omega
        rw [hiRem] at this
        exact this.symm
      have htiEq : ti = t0 + (i : ℤ) * e := by
        rw [hiEq, hsi] at hEqI
        omega
      rwa [← htiEq]
    · obtain ⟨u, hu, ti, hti, hEqI⟩ := hNewI
      have huM : u < 166375 := (ErdosSixIndependent.new_residue_data u hu).1
      have hur : (u : ℤ) = r := by
        have : (a - 1 + (i : ℤ) * d) % M = u := by rw [hEqI]; omega
        rw [hiRem] at this
        exact this.symm
      exact False.elim ((new_not_old hu) (hur ▸ hs ▸ hsOld))
  · obtain ⟨u, hu, t, ht, hEq⟩ := hNew
    have huM : u < 166375 := (ErdosSixIndependent.new_residue_data u hu).1
    have hur : (u : ℤ) = r := by
      have : (a - 1 + ((0 : Fin 4) : ℤ) * d) % M = u := by rw [hEq]; omega
      simpa [hiRem] using this.symm
    apply walkerDigitSet_apFree 21 t0 e he0
    intro i
    rcases hE i with hOldI | hNewI
    · obtain ⟨si, ti, hsi0, hsiM, hsiOld, hti, hEqI⟩ := old_block_decomp hOldI
      have hsi : si = r := by
        have : (a - 1 + (i : ℤ) * d) % M = si := by rw [hEqI]; omega
        rw [hiRem] at this
        exact this.symm
      exact False.elim ((new_not_old hu) (hur ▸ hsi ▸ hsiOld))
    · obtain ⟨ui, hui, ti, hti, hEqI⟩ := hNewI
      have huiM : ui < 166375 := (ErdosSixIndependent.new_residue_data ui hui).1
      have huir : (ui : ℤ) = r := by
        have : (a - 1 + (i : ℤ) * d) % M = ui := by rw [hEqI]; omega
        rw [hiRem] at this
        exact this.symm
      have htiEq : ti = t0 + (i : ℤ) * e := by
        rw [hiEq, huir] at hEqI
        omega
      rwa [← htiEq]

#print axioms sixA_apFree

end Erdos3Candidate
