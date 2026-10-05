import OpHack.OldThreeModular
import OpHack.ErdosSixFinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Erdos3Candidate
open ErdosSixIndependent

def sixResidues (z : ℤ) : Prop := oldThreeResidues z ∨ z.toNat ∈ U

private theorem gap_inv (i j : Fin 4) (hij : i < j) :
    (((j.val : ℤ) - i.val) * (inverseGap (j.val - i.val) : ℕ)) % M = 1 := by
  have hi := i.isLt
  have hj := j.isLt
  have hgap : j.val - i.val = 1 ∨ j.val - i.val = 2 ∨ j.val - i.val = 3 := by
    omega
  rcases hgap with hgap | hgap | hgap
  · have hgapZ : (j.val : ℤ) - i.val = 1 := by omega
    norm_num [hgap, hgapZ, inverseGap, M]
  · have hgapZ : (j.val : ℤ) - i.val = 2 := by omega
    norm_num [hgap, hgapZ, inverseGap, M]
  · have hgapZ : (j.val : ℤ) - i.val = 3 := by omega
    norm_num [hgap, hgapZ, inverseGap, M]

theorem oldThree_int_nat (z : ℤ) (hz : 0 ≤ z) :
    oldThreeResidues z ↔ oldThree z.toNat := by
  have h0 : (z % 55).toNat = z.toNat % 55 := by omega
  have h1 : ((z / 55) % 55).toNat = z.toNat / 55 % 55 := by omega
  have h2 : ((z / 3025) % 55).toNat = z.toNat / 3025 % 55 := by omega
  have hp0 : 0 ≤ z % 55 := by omega
  have hp1 : 0 ≤ (z / 55) % 55 := by omega
  have hp2 : 0 ≤ (z / 3025) % 55 := by omega
  have hD : ErdosSingletonIndependent.D = D := rfl
  simp [oldThreeResidues, oldThree, oldTwo, walkerDigits,
    h0, h1, h2, hp0, hp1, hp2, hD] <;> tauto

theorem sixResidues_iff_allowed (z : ℤ) (hz : 0 ≤ z) :
    sixResidues z ↔ allowed z.toNat := by
  simp [sixResidues, allowed, oldThree_int_nat z hz]

theorem pair_step (a d : ℤ) (u v : ℕ) (i j : Fin 4)
    (hu : u < M) (hv : v < M) (hij : i < j)
    (hi : (a + (i : ℤ) * d) % M = u)
    (hj : (a + (j : ℤ) * d) % M = v) :
    d % M = pairDifference u v i.val j.val := by
  let g : ℤ := (j.val : ℤ) - (i.val : ℤ)
  let q : ℤ := (inverseGap (j.val - i.val) : ℕ)
  have hi' : a + (i : ℤ) * d ≡ (u : ℤ) [ZMOD M] := by
    change (a + (i : ℤ) * d) % 166375 = (u : ℤ) % 166375
    have hu' : u < 166375 := hu
    have hiNum : (a + (i : ℤ) * d) % 166375 = (u : ℤ) := hi
    omega
  have hj' : a + (j : ℤ) * d ≡ (v : ℤ) [ZMOD M] := by
    change (a + (j : ℤ) * d) % 166375 = (v : ℤ) % 166375
    have hv' : v < 166375 := hv
    have hjNum : (a + (j : ℤ) * d) % 166375 = (v : ℤ) := hj
    omega
  have hgap : g * d ≡ (v : ℤ) - (u : ℤ) [ZMOD M] := by
    convert hj'.sub hi' using 1 <;> dsimp [g] <;> ring
  have hinv : g * q ≡ 1 [ZMOD M] := by
    exact gap_inv i j hij
  have h1 := hinv.mul (Int.ModEq.refl d)
  have h2 := hgap.mul (Int.ModEq.refl q)
  have hcongr : d ≡ ((v : ℤ) - (u : ℤ)) * q [ZMOD M] := by
    calc
      d ≡ (g * q) * d [ZMOD M] := by simpa using h1.symm
      _ ≡ ((v : ℤ) - (u : ℤ)) * q [ZMOD M] := by
        convert h2 using 1 <;> ring
  have hgapval : j.val - i.val = 1 ∨ j.val - i.val = 2 ∨ j.val - i.val = 3 := by
    have hiBound := i.isLt
    have hjBound := j.isLt
    omega
  rcases hgapval with hgapval | hgapval | hgapval
  · have hu' : u < 166375 := hu
    have hv' : v < 166375 := hv
    simp [pairDifference, hgapval, inverseGap, q, M, Int.ModEq] at hcongr ⊢
    omega
  · have hu' : u < 166375 := hu
    have hv' : v < 166375 := hv
    simp [pairDifference, hgapval, inverseGap, q, M, Int.ModEq] at hcongr ⊢
    omega
  · have hu' : u < 166375 := hu
    have hv' : v < 166375 := hv
    simp [pairDifference, hgapval, inverseGap, q, M, Int.ModEq] at hcongr ⊢
    omega

theorem pair_all_terms (a d : ℤ) (u v : ℕ) (i j : Fin 4)
    (hu : u ∈ U) (hv : v ∈ U) (hne : u ≠ v) (hij : i < j)
    (hi : (a + (i : ℤ) * d) % M = u)
    (hj : (a + (j : ℤ) * d) % M = v) :
    ∀ k : Fin 4,
      ((a + (k : ℤ) * d) % M).toNat =
        pairTerm u v i.val j.val k.val := by
  let p := pairDifference u v i.val j.val
  let s := pairStart u v i.val j.val
  have huBound : u < M := (new_residue_data u hu).1
  have hvBound : v < M := (new_residue_data v hv).1
  have hpBound : p < M := Nat.mod_lt _ (by decide)
  have hpStep : d % M = p := pair_step a d u v i j huBound hvBound hij hi hj
  have hpCon : d ≡ (p : ℤ) [ZMOD M] := by
    change d % 166375 = (p : ℤ) % 166375
    have hpBound' : p < 166375 := hpBound
    have hpStep' : d % 166375 = (p : ℤ) := hpStep
    omega
  have hpairI : (s + i.val * p) % M = u := by
    simpa [pairTerm, s, p] using (pair_data u hu v hv hne i j hij).2.1
  have hpairIZ : ((s : ℤ) + (i : ℤ) * (p : ℤ)) % M = u := by
    have hcast : ((s : ℤ) + (i : ℤ) * (p : ℤ)) =
        ((s + i.val * p : ℕ) : ℤ) := by norm_cast
    rw [hcast, ← Int.natCast_mod]
    exact_mod_cast hpairI
  have hAtI : a + (i : ℤ) * d ≡ (s : ℤ) + (i : ℤ) * (p : ℤ) [ZMOD M] := by
    change (a + (i : ℤ) * d) % 166375 =
      ((s : ℤ) + (i : ℤ) * (p : ℤ)) % 166375
    have hiNum : (a + (i : ℤ) * d) % 166375 = (u : ℤ) := hi
    have hpairINum : ((s : ℤ) + (i : ℤ) * (p : ℤ)) % 166375 = (u : ℤ) := hpairIZ
    omega
  have hiMul : (i : ℤ) * d ≡ (i : ℤ) * (p : ℤ) [ZMOD M] :=
    (Int.ModEq.refl (i : ℤ)).mul hpCon
  have hbase : a ≡ (s : ℤ) [ZMOD M] := by
    convert hAtI.sub hiMul using 1 <;> ring
  intro k
  have hkMul : (k : ℤ) * d ≡ (k : ℤ) * (p : ℤ) [ZMOD M] :=
    (Int.ModEq.refl (k : ℤ)).mul hpCon
  have hkCon : a + (k : ℤ) * d ≡ (s : ℤ) + (k : ℤ) * (p : ℤ) [ZMOD M] :=
    hbase.add hkMul
  have hcast : ((s : ℤ) + (k : ℤ) * (p : ℤ)) =
      ((s + k.val * p : ℕ) : ℤ) := by norm_cast
  have hkZ : (a + (k : ℤ) * d) % M =
      ((pairTerm u v i.val j.val k.val : ℕ) : ℤ) := by
    unfold Int.ModEq at hkCon
    rw [hkCon, hcast, ← Int.natCast_mod]
    rfl
  rw [hkZ]
  simp

private theorem oldTwo_mod_iff (x y : ℕ) (hxy : x % 3025 = y % 3025) :
    oldTwo x ↔ oldTwo y := by
  have h0 : x % 55 = y % 55 := by omega
  have h1 : x / 55 % 55 = y / 55 % 55 := by omega
  simp [oldTwo, h0, h1]

private theorem high_digit_mod (x : ℕ) :
    ((x % M) / 3025) % 55 = (x / 3025) % 55 := by
  dsimp [M]
  omega

theorem no_endpoint_new (u d : ℕ) (hu : u ∈ U) (hd : d < M)
    (h1 : oldThree ((u + d) % M))
    (h2 : oldThree ((u + 2 * d) % M))
    (h3 : oldThree ((u + 3 * d) % M)) : False := by
  simp only [M] at *
  have huBound : u < 166375 := (new_residue_data u hu).1
  have hunit1 : ((u + d) % M) % 55 =
      (u % 55 + d % 55) % 55 := by dsimp [M] at *; omega
  have hunit2 : ((u + 2 * d) % M) % 55 =
      (u % 55 + 2 * (d % 55)) % 55 := by dsimp [M] at *; omega
  have hunit3 : ((u + 3 * d) % M) % 55 =
      (u % 55 + 3 * (d % 55)) % 55 := by dsimp [M] at *; omega
  have hunit : d % 55 ∈ endpointCandidates (u % 55) := by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_range]
      omega
    · change (u % 55 + d % 55) % 55 ∈ D ∧
        (u % 55 + 2 * (d % 55)) % 55 ∈ D ∧
        (u % 55 + 3 * (d % 55)) % 55 ∈ D
      rw [← hunit1, ← hunit2, ← hunit3]
      exact ⟨h1.1.1, h2.1.1, h3.1.1⟩
  rcases new_residue_data u hu with ⟨_, _, hz, _, _⟩
  rcases hz with hz | hz
  · rw [hz, endpoint_7] at hunit
    simpa using hunit
  · rw [hz, endpoint_51] at hunit
    simpa using hunit

theorem no_middle_new (u d : ℕ) (hu : u ∈ U) (hd : d < M)
    (h0 : oldThree ((u + M - d) % M))
    (h2 : oldThree ((u + d) % M))
    (h3 : oldThree ((u + 2 * d) % M)) : False := by
  simp only [M] at *
  have huBound : u < 166375 := (new_residue_data u hu).1
  have hunit0 : ((u + M - d) % M) % 55 =
      (u % 55 + 55 - d % 55) % 55 := by dsimp [M] at *; omega
  have hunit2 : ((u + d) % M) % 55 =
      (u % 55 + d % 55) % 55 := by dsimp [M] at *; omega
  have hunit3 : ((u + 2 * d) % M) % 55 =
      (u % 55 + 2 * (d % 55)) % 55 := by dsimp [M] at *; omega
  have hunit : d % 55 ∈ unitsCandidates (u % 55) := by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_range.mpr (Nat.mod_lt _ (by decide))
    · simp only [decide_eq_true_eq]
      change (u % 55 + 55 - d % 55) % 55 ∈ D ∧
          (u % 55 + d % 55) % 55 ∈ D ∧
          (u % 55 + 2 * (d % 55)) % 55 ∈ D
      rw [← hunit0, ← hunit2, ← hunit3]
      exact ⟨h0.1.1, h2.1.1, h3.1.1⟩
  have hlow0 : ((u + M - d) % M) % 3025 =
      (u % 3025 + 3025 - d % 3025) % 3025 := by dsimp [M] at *; omega
  have hlow2 : ((u + d) % M) % 3025 = (u + d % 3025) % 3025 := by dsimp [M] at *; omega
  have hlow3 : ((u + 2 * d) % M) % 3025 =
      (u + 2 * (d % 3025)) % 3025 := by dsimp [M] at *; omega
  have hlow0old : oldTwo ((u % 3025 + 3025 - d % 3025) % 3025) :=
    (oldTwo_mod_iff _ _ (by simpa only [Nat.mod_mod] using hlow0)).mp h0.1
  have hlow2old : oldTwo ((u + d % 3025) % 3025) :=
    (oldTwo_mod_iff _ _ (by simpa only [Nat.mod_mod] using hlow2)).mp h2.1
  have hlow3old : oldTwo ((u + 2 * (d % 3025)) % 3025) :=
    (oldTwo_mod_iff _ _ (by simpa only [Nat.mod_mod] using hlow3)).mp h3.1
  have hunitX : d % 55 ∈ unitsCandidates ((u % 3025) % 55) := by
    have hx : (u % 3025) % 55 = u % 55 := by dsimp [M] at *; omega
    simpa [hx] using hunit
  have hlow : d % 3025 ∈ twoCandidates (u % 3025) := by
    dsimp [twoCandidates]
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_flatMap.mpr
      refine ⟨d % 55, hunitX, ?_⟩
      apply List.mem_map.mpr
      refine ⟨d / 55 % 55, List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
      omega
    · simp only [decide_eq_true_eq]
      change oldTwo ((u % 3025 + 3025 - d % 3025) % 3025) ∧
        oldTwo ((u % 3025 + d % 3025) % 3025) ∧
        oldTwo ((u % 3025 + 2 * (d % 3025)) % 3025)
      have hx2 : (u % 3025 + d % 3025) % 3025 =
          (u + d % 3025) % 3025 := by dsimp [M] at *; omega
      have hx3 : (u % 3025 + 2 * (d % 3025)) % 3025 =
          (u + 2 * (d % 3025)) % 3025 := by dsimp [M] at *; omega
      rw [hx2, hx3]
      exact ⟨hlow0old, hlow2old, hlow3old⟩
  rcases third_offsets u hu (d % 3025) hlow with
    ⟨hLowBound, hoff0, hoff2, hoff3⟩
  have hthird0 : ((u + M - d) % M) / 3025 % 55 =
      (u / 3025 + 55 - d / 3025) % 55 := by
    dsimp [M] at *
    have hdDecomp : d = 3025 * (d / 3025) + d % 3025 := by omega
    have ht : d / 3025 < 55 := by omega
    have hx : u + 166375 - d =
        (u - d % 3025) + 3025 * (55 - d / 3025) := by omega
    have hq : (u + 166375 - d) / 3025 =
        u / 3025 + 55 - d / 3025 := by
      rw [hx]
      omega
    rw [high_digit_mod, hq]
  have hthird2 : ((u + d) % M) / 3025 % 55 =
      (u / 3025 + 1 + d / 3025) % 55 := by dsimp [M] at *; omega
  have hthird3 : ((u + 2 * d) % M) / 3025 % 55 =
      (u / 3025 + 1 + 2 * (d / 3025)) % 55 := by dsimp [M] at *; omega
  have hthird : d / 3025 ∈ thirdCandidates (u / 3025) := by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_range]
      omega
    · change (u / 3025 + 55 - d / 3025) % 55 ∈ D ∧
        (u / 3025 + 1 + d / 3025) % 55 ∈ D ∧
        (u / 3025 + 1 + 2 * (d / 3025)) % 55 ∈ D
      rw [← hthird0, ← hthird2, ← hthird3]
      exact ⟨h0.2, h2.2, h3.2⟩
  rcases new_residue_data u hu with ⟨_, _, _, _, hz⟩
  rcases hz with hz | hz
  · rw [hz, third_8] at hthird
    simpa using hthird
  · rw [hz, third_39] at hthird
    simpa using hthird

end Erdos3Candidate
