import OpHack.DigitCounting
import OpHack.SixFloorBridge

/-! Exact finite-list to digit-Finset identifications. Large prefix sets are
    identified structurally; the tiny digit and residue checks use `decide`. -/
namespace Erdos3Candidate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both arithmetic certificate digit lists match the Finset alphabet. -/
theorem six_digits_finset :
    (SixHarmonicCertificate.digits.map Int.ofNat).toFinset = walkerFinset := by
  decide

theorem old_digits_finset :
    (HarmonicCertificate.digits.map Int.ofNat).toFinset = walkerFinset := by
  decide

/-- The six certificate residue values match the AP-free construction. -/
theorem six_extensions_finset :
    SixHarmonicCertificate.extensions.toFinset = ErdosSixIndependent.U := by
  decide

/-- The nonzero certificate digits match the finite leading alphabet. -/
theorem six_nonzero_digits_finset :
    ((SixHarmonicCertificate.digits.filter (fun d => d != 0)).map
      Int.ofNat).toFinset = walkerFinset.erase 0 := by
  decide

theorem old_nonzero_digits_finset :
    ((HarmonicCertificate.digits.filter (fun d => d != 0)).map
      Int.ofNat).toFinset = walkerFinset.erase 0 := by
  decide

private theorem nat_pair_finset (l m : List ℕ) :
    ((l.flatMap fun (a : ℕ) => m.map fun (b : ℕ) => 55 * a + b).map Int.ofNat).toFinset =
      ((l.map Int.ofNat).toFinset.product (m.map Int.ofNat).toFinset).image
        (fun p => 55 * p.1 + p.2) := by
  ext z
  simp only [Finset.product_eq_sprod, List.mem_toFinset, List.mem_map, List.mem_flatMap,
    Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨n, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨((a : ℤ), (b : ℤ)), ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, ?_⟩
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · rintro ⟨⟨a, b⟩, ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, hval⟩
    refine ⟨55 * u + v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      using hval

/-- The 441 certified old prefix values are exactly the two-digit set. -/
theorem old_prefixes_finset :
    (HarmonicCertificate.prefixes.map Int.ofNat).toFinset = digitFinset 2 := by
  rw [HarmonicCertificate.prefixes, nat_pair_finset, old_digits_finset]
  ext z
  rw [Finset.mem_image, mem_digitFinset_high 1, digitFinset_one]
  constructor
  · rintro ⟨⟨a, b⟩, hpair, hval⟩
    have ⟨ha, hb⟩ := Finset.mem_product.mp hpair
    refine ⟨b, hb, a, ha, ?_⟩
    simpa only [pow_one, add_comm] using hval.symm
  · rintro ⟨b, hb, a, ha, hval⟩
    refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
    simpa only [pow_one, add_comm] using hval.symm

/-- The 420 certified positive-leading prefixes are exactly the Finset layer. -/
theorem old_leading_prefix_finset :
    (HarmonicCertificate.leadingPrefix.map Int.ofNat).toFinset = leadingPrefix := by
  rw [HarmonicCertificate.leadingPrefix, nat_pair_finset,
    old_nonzero_digits_finset, old_digits_finset]
  rfl

#print axioms old_prefixes_finset
#print axioms old_leading_prefix_finset
#print axioms six_digits_finset
#print axioms six_extensions_finset

private theorem natList_sum_cast (l : List ℕ) (hl : l.Nodup) (f : ℤ → ℚ) :
    (∑ z ∈ (l.map Int.ofNat).toFinset, f z) =
      (l.map fun (n : ℕ) => f (n : ℤ)).sum := by
  rw [List.sum_toFinset _ (hl.map Int.ofNat_injective)]
  simp only [List.map_map, Function.comp_def, Int.ofNat_eq_natCast]

private theorem flat_natList_sum_cast (l m : List ℕ)
    (hl : l.Nodup) (hm : m.Nodup) (f : ℕ → ℤ → ℚ) :
    (l.flatMap fun (u : ℕ) => m.map fun (d : ℕ) => f u (d : ℤ)).sum =
      ∑ u ∈ l.toFinset, ∑ d ∈ (m.map Int.ofNat).toFinset, f u d := by
  have hinner (u : ℕ) :
      (m.map fun (d : ℕ) => f u (d : ℤ)).sum =
        ∑ d ∈ (m.map Int.ofNat).toFinset, f u d :=
    (natList_sum_cast m hm (f u)).symm
  calc
    (l.flatMap fun (u : ℕ) => m.map fun (d : ℕ) => f u (d : ℤ)).sum =
        (l.map fun (u : ℕ) => (m.map fun (d : ℕ) => f u (d : ℤ)).sum).sum := by
          simp only [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]
    _ = (l.map fun (u : ℕ) => ∑ d ∈ (m.map Int.ofNat).toFinset, f u d).sum := by
          congr 1
          exact List.map_congr_left (fun u hu => hinner u)
    _ = ∑ u ∈ l.toFinset, ∑ d ∈ (m.map Int.ofNat).toFinset, f u d := by
          rw [List.sum_toFinset _ hl]

/-- Exact old-prefix List sum is the reciprocal sum of the two-digit Finset. -/
theorem old_prefix_list_sum :
    (HarmonicCertificate.prefixes.map fun (p : ℕ) => (1 : ℚ) / ((p : ℚ) + 1)).sum =
      ∑ z ∈ digitFinset 2, (1 : ℚ) / ((z : ℚ) + 1) := by
  rw [← old_prefixes_finset]
  simpa only [Int.cast_natCast] using (natList_sum_cast HarmonicCertificate.prefixes
    old_prefixes_nodup (fun z => (1 : ℚ) / ((z : ℚ) + 1))).symm

/-- Exact old-leading-prefix List sum is the corresponding Finset sum. -/
theorem old_tail_list_sum :
    (HarmonicCertificate.leadingPrefix.map fun (p : ℕ) =>
      (1 : ℚ) / ((p : ℚ) + 454 / 1155)).sum =
      ∑ p ∈ leadingPrefix, (1 : ℚ) / ((p : ℚ) + 454 / 1155) := by
  rw [← old_leading_prefix_finset]
  simpa only [Int.cast_natCast] using (natList_sum_cast HarmonicCertificate.leadingPrefix
    old_leading_prefix_nodup
    (fun z => (1 : ℚ) / ((z : ℚ) + 454 / 1155))).symm

/-- Exact six-fibre first-digit List sum matches the product Finset. -/
theorem new_prefix_list_sum :
    (SixHarmonicCertificate.extensions.flatMap fun (u : ℕ) =>
      SixHarmonicCertificate.digits.map fun (d : ℕ) =>
        (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1)).sum =
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset,
          (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1) := by
  rw [← six_extensions_finset, ← six_digits_finset]
  simpa only [Int.cast_natCast] using
    flat_natList_sum_cast SixHarmonicCertificate.extensions SixHarmonicCertificate.digits
      six_extensions_nodup six_digits_nodup
      (fun (u : ℕ) (d : ℤ) => (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1))

/-- The common six-fibre tail List coefficient matches the product Finset. -/
theorem new_tail_list_sum :
    (SixHarmonicCertificate.extensions.flatMap fun (_u : ℕ) =>
      (SixHarmonicCertificate.digits.filter (fun d => d != 0)).map fun (d : ℕ) =>
        (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155))).sum =
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset.erase 0,
          (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155)) := by
  rw [← six_extensions_finset, ← six_nonzero_digits_finset]
  have hfiltered :
      (SixHarmonicCertificate.digits.filter (fun d => d != 0)).Nodup :=
    six_digits_nodup.filter _
  simpa only [Int.cast_natCast] using
    flat_natList_sum_cast SixHarmonicCertificate.extensions
      (SixHarmonicCertificate.digits.filter (fun d => d != 0))
      six_extensions_nodup hfiltered
      (fun (_u : ℕ) (d : ℤ) => (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155)))

#print axioms old_prefix_list_sum
#print axioms old_tail_list_sum
#print axioms new_prefix_list_sum
#print axioms new_tail_list_sum

end Erdos3Candidate
