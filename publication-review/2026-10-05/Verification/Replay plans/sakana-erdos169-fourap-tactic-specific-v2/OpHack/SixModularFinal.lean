import OpHack.SixModularAssembly

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Erdos3Candidate
open ErdosSixIndependent

private theorem canonical_modEq (x : ℤ) :
    x ≡ ((x % M).toNat : ℤ) [ZMOD M] := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg x (by decide))]
  exact (Int.mod_modEq x M).symm

private theorem canonical_add (x d : ℤ) (k : Fin 4) :
    ((x + (k : ℤ) * d) % M).toNat =
      (((x % M).toNat + k.val * (d % M).toNat) % M) := by
  have hcongr := (canonical_modEq x).add
    ((Int.ModEq.refl (k : ℤ)).mul (canonical_modEq d))
  have hcast : ((x % M).toNat : ℤ) + (k : ℤ) * ((d % M).toNat : ℤ) =
      (((x % M).toNat + k.val * (d % M).toNat : ℕ) : ℤ) := by
    norm_cast
  rw [hcongr.eq, hcast, ← Int.natCast_mod]
  rfl

private theorem canonical_minus (x d : ℤ) :
    ((x - d) % M).toNat =
      (((x % M).toNat + M - (d % M).toNat) % M) := by
  have hdBound : (d % M).toNat < M :=
    (Int.toNat_lt' (by decide)).mpr (Int.emod_lt_of_pos d (by decide))
  have hsub : (d % M).toNat ≤ (x % M).toNat + M :=
    (Nat.le_of_lt hdBound).trans (Nat.le_add_left M _)
  have hmod : (0 : ℤ) ≡ (M : ℤ) [ZMOD M] :=
    Int.modulus_modEq_zero.symm
  have hcongr : x - d ≡
      ((x % M).toNat : ℤ) + (M : ℤ) - ((d % M).toNat : ℤ) [ZMOD M] := by
    simpa only [add_zero] using
      ((canonical_modEq x).add hmod).sub (canonical_modEq d)
  have hcast : (((x % M).toNat + M - (d % M).toNat : ℕ) : ℤ) =
      ((x % M).toNat : ℤ) + (M : ℤ) - ((d % M).toNat : ℤ) := by
    rw [Int.natCast_sub hsub, Int.natCast_add]
  rw [hcongr.eq, ← hcast, ← Int.natCast_mod]
  rfl

private theorem no_two_new (a d : ℤ)
    (hnot : ¬ (166375 : ℤ) ∣ d)
    (hAP : ∀ k : Fin 4, sixResidues ((a + (k : ℤ) * d) % 166375))
    (i j : Fin 4) (hij : i < j)
    (hiU : ((a + (i : ℤ) * d) % 166375).toNat ∈ U)
    (hjU : ((a + (j : ℤ) * d) % 166375).toNat ∈ U) : False := by
  let u := ((a + (i : ℤ) * d) % 166375).toNat
  let v := ((a + (j : ℤ) * d) % 166375).toNat
  have hi : (a + (i : ℤ) * d) % M = u :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))).symm
  have hj : (a + (j : ℤ) * d) % M = v :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))).symm
  have huBound : u < M := (new_residue_data u hiU).1
  have hvBound : v < M := (new_residue_data v hjU).1
  have hne : u ≠ v := by
    intro heq
    have hp := pair_step a d u v i j huBound hvBound hij hi hj
    have hzero : pairDifference u v i.val j.val = 0 := by
      rw [← heq]
      simp [pairDifference]
    have hd0 : d % 166375 = 0 := by simpa [M, hzero] using hp
    exact hnot (Int.dvd_iff_emod_eq_zero.mpr hd0)
  have hall := pair_all_terms a d u v i j hiU hjU hne hij hi hj
  have hbad := two_new_exclusion u hiU v hjU hne i j hij
  apply hbad
  intro k
  have hk0 : 0 ≤ (a + (k : ℤ) * d) % 166375 :=
    Int.emod_nonneg _ (by decide)
  have hkAllowed : allowed (((a + (k : ℤ) * d) % 166375).toNat) :=
    (sixResidues_iff_allowed _ hk0).mp (hAP k)
  have hkTerm : ((a + (k : ℤ) * d) % 166375).toNat =
      pairTerm u v i.val j.val k.val := by
    simpa [M] using hall k
  rw [hkTerm] at hkAllowed
  exact hkAllowed
private theorem old_nat_of_int (x : ℤ)
    (h : oldThreeResidues (x % M)) : oldThree ((x % M).toNat) :=
  (oldThree_int_nat _ (Int.emod_nonneg _ (by decide))).mp h

private theorem no_endpoint_residue (x d : ℤ)
    (hu : (x % M).toNat ∈ U)
    (h1 : oldThreeResidues ((x + d) % M))
    (h2 : oldThreeResidues ((x + 2 * d) % M))
    (h3 : oldThreeResidues ((x + 3 * d) % M)) : False := by
  let u := (x % M).toNat
  let t := (d % M).toNat
  have ht : t < M :=
    (Int.toNat_lt' (by decide)).mpr (Int.emod_lt_of_pos d (by decide))
  have h1n := old_nat_of_int (x + d) h1
  have h2n := old_nat_of_int (x + 2 * d) h2
  have h3n := old_nat_of_int (x + 3 * d) h3
  have heq1 : ((x + d) % M).toNat = (u + t) % M := by
    simpa [u, t] using canonical_add x d (1 : Fin 4)
  have heq2 : ((x + 2 * d) % M).toNat = (u + 2 * t) % M := by
    simpa [u, t] using canonical_add x d (2 : Fin 4)
  have heq3 : ((x + 3 * d) % M).toNat = (u + 3 * t) % M := by
    simpa [u, t] using canonical_add x d (3 : Fin 4)
  rw [heq1] at h1n
  rw [heq2] at h2n
  rw [heq3] at h3n
  exact no_endpoint_new u t hu ht h1n h2n h3n

private theorem no_middle_residue (x d : ℤ)
    (hu : (x % M).toNat ∈ U)
    (h0 : oldThreeResidues ((x - d) % M))
    (h2 : oldThreeResidues ((x + d) % M))
    (h3 : oldThreeResidues ((x + 2 * d) % M)) : False := by
  let u := (x % M).toNat
  let t := (d % M).toNat
  have ht : t < M :=
    (Int.toNat_lt' (by decide)).mpr (Int.emod_lt_of_pos d (by decide))
  have h0n := old_nat_of_int (x - d) h0
  have h2n := old_nat_of_int (x + d) h2
  have h3n := old_nat_of_int (x + 2 * d) h3
  have heq0 : ((x - d) % M).toNat = (u + M - t) % M := by
    simpa [u, t] using canonical_minus x d
  have heq2 : ((x + d) % M).toNat = (u + t) % M := by
    simpa [u, t] using canonical_add x d (1 : Fin 4)
  have heq3 : ((x + 2 * d) % M).toNat = (u + 2 * t) % M := by
    simpa [u, t] using canonical_add x d (2 : Fin 4)
  rw [heq0] at h0n
  rw [heq2] at h2n
  rw [heq3] at h3n
  exact no_middle_new u t hu ht h0n h2n h3n
/-- The old three-digit alphabet together with the six audited new residues
    excludes every nonzero-step modular four-term progression. -/
theorem sixResidues_modular_free : ModularAPFree 4 166375 sixResidues := by
  intro a d hnot hAP
  let P (i : Fin 4) : Prop :=
    (((a + (i : ℤ) * d) % 166375).toNat ∈ U)
  have hOld (i : Fin 4) (hi : ¬ P i) :
      oldThreeResidues ((a + (i : ℤ) * d) % 166375) := by
    have h := hAP i
    change oldThreeResidues ((a + (i : ℤ) * d) % 166375) ∨ P i at h
    exact h.resolve_right hi
  by_cases htwo : ∃ i j : Fin 4, i < j ∧ P i ∧ P j
  · rcases htwo with ⟨i, j, hij, hi, hj⟩
    exact no_two_new a d hnot hAP i j hij hi hj
  by_cases hnone : ∀ i : Fin 4, ¬ P i
  · exact oldThree_modular_free a d hnot (fun i => hOld i (hnone i))
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, P i := by
    by_contra h
    apply hnone
    intro j hj
    exact h ⟨j, hj⟩
  have honly (j : Fin 4) (hji : j ≠ i) : ¬ P j := by
    intro hj
    rcases lt_or_gt_of_ne hji with hlt | hlt
    · exact htwo ⟨j, i, hlt, hj, hi⟩
    · exact htwo ⟨i, j, hlt, hi, hj⟩
  fin_cases i
  · have hu : (a % M).toNat ∈ U := by simpa [P] using hi
    have h1 : oldThreeResidues ((a + d) % M) := by
      simpa using hOld (1 : Fin 4) (honly (1 : Fin 4) (by decide))
    have h2 : oldThreeResidues ((a + 2 * d) % M) := by
      simpa using hOld (2 : Fin 4) (honly (2 : Fin 4) (by decide))
    have h3 : oldThreeResidues ((a + 3 * d) % M) := by
      simpa using hOld (3 : Fin 4) (honly (3 : Fin 4) (by decide))
    exact no_endpoint_residue a d hu h1 h2 h3
  · have hu : ((a + d) % M).toNat ∈ U := by simpa [P] using hi
    have h0 : oldThreeResidues (a % M) := by
      simpa using hOld (0 : Fin 4) (honly (0 : Fin 4) (by decide))
    have h2 : oldThreeResidues ((a + 2 * d) % M) := by
      simpa using hOld (2 : Fin 4) (honly (2 : Fin 4) (by decide))
    have h3 : oldThreeResidues ((a + 3 * d) % M) := by
      simpa using hOld (3 : Fin 4) (honly (3 : Fin 4) (by decide))
    apply no_middle_residue (a + d) d hu
    · simpa only [add_sub_cancel_right] using h0
    · simpa only [show (a + d) + d = a + 2 * d by ring] using h2
    · simpa only [show (a + d) + 2 * d = a + 3 * d by ring] using h3
  · have hu : ((a + 2 * d) % M).toNat ∈ U := by simpa [P] using hi
    have h0 : oldThreeResidues (a % M) := by
      simpa using hOld (0 : Fin 4) (honly (0 : Fin 4) (by decide))
    have h1 : oldThreeResidues ((a + d) % M) := by
      simpa using hOld (1 : Fin 4) (honly (1 : Fin 4) (by decide))
    have h3 : oldThreeResidues ((a + 3 * d) % M) := by
      simpa using hOld (3 : Fin 4) (honly (3 : Fin 4) (by decide))
    apply no_middle_residue (a + 2 * d) (-d) hu
    · simpa only [show (a + 2 * d) - (-d) = a + 3 * d by ring] using h3
    · simpa only [show (a + 2 * d) + (-d) = a + d by ring] using h1
    · simpa only [show (a + 2 * d) + 2 * (-d) = a by ring] using h0
  · have hu : ((a + 3 * d) % M).toNat ∈ U := by simpa [P] using hi
    have h0 : oldThreeResidues (a % M) := by
      simpa using hOld (0 : Fin 4) (honly (0 : Fin 4) (by decide))
    have h1 : oldThreeResidues ((a + d) % M) := by
      simpa using hOld (1 : Fin 4) (honly (1 : Fin 4) (by decide))
    have h2 : oldThreeResidues ((a + 2 * d) % M) := by
      simpa using hOld (2 : Fin 4) (honly (2 : Fin 4) (by decide))
    apply no_endpoint_residue (a + 3 * d) (-d) hu
    · simpa only [show (a + 3 * d) + (-d) = a + 2 * d by ring] using h2
    · simpa only [show (a + 3 * d) + 2 * (-d) = a + d by ring] using h1
    · simpa only [show (a + 3 * d) + 3 * (-d) = a by ring] using h0

#print axioms sixResidues_modular_free

end Erdos3Candidate
