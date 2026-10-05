import OpHack.DigitCounting
import OpHack.ReciprocalBlocks
import OpHack.SixTermwise

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

namespace Erdos3Candidate

-- The huge finite sets are accessed through their checked structural lemmas.
attribute [local irreducible] digitFinset

/-- The six additional fibres, before translating every element by one. -/
def sixNewFibreFinset : Finset ℤ :=
  (ErdosSixIndependent.U.product (digitFinset 21)).image
    (fun p => (p.1 : ℤ) + 166375 * p.2)

private theorem six_new_not_old {u : ℕ} (hu : u ∈ ErdosSixIndependent.U) :
    ¬ oldThreeResidues (u : ℤ) := by
  simp only [ErdosSixIndependent.U, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with h | h | h | h | h | h
  all_goals subst u
  all_goals norm_num [oldThreeResidues, walkerDigits, ErdosSingletonIndependent.D]

/-- Canonical residues prevent overlap between the old block and new fibres. -/
theorem six_old_new_disjoint :
    Disjoint (digitFinset 22) sixNewFibreFinset := by
  apply Finset.disjoint_left.mpr
  intro z hOld hNew
  obtain ⟨r, tOld, hr0, hrM, hrOld, htOld, hzOld⟩ :=
    old_block_decomp ((mem_digitFinset 22 z).mp hOld)
  obtain ⟨⟨u, tNew⟩, hpair, hzNew⟩ :=
    Finset.mem_image.mp hNew
  have ⟨hu, htNew⟩ := Finset.mem_product.mp hpair
  have huM : u < 166375 := by
    have h := (ErdosSixIndependent.new_residue_data u hu).1
    change u < 166375 at h
    exact h
  have hru : r = (u : ℤ) := by
    dsimp at hzNew
    omega
  exact (six_new_not_old hu) (hru ▸ hrOld)

/-- Distinct residues and unique quotient make the new-fibre parametrization injective. -/
theorem six_new_fibre_inj :
    Set.InjOn (fun p : ℕ × ℤ => (p.1 : ℤ) + 166375 * p.2)
      (ErdosSixIndependent.U.product (digitFinset 21)) := by
  rintro ⟨u, t⟩ hut ⟨v, s⟩ hvs heq
  have ⟨hu, _⟩ := Finset.mem_product.mp hut
  have ⟨hv, _⟩ := Finset.mem_product.mp hvs
  have huM : u < 166375 := by
    have h := (ErdosSixIndependent.new_residue_data u hu).1
    change u < 166375 at h
    exact h
  have hvM : v < 166375 := by
    have h := (ErdosSixIndependent.new_residue_data v hv).1
    change v < 166375 at h
    exact h
  dsimp at heq
  have huv : u = v := by omega
  subst v
  have hts : t = s := by omega
  exact Prod.ext rfl hts

/-- The reciprocal sum of the actual finite set has no duplicate old/new
    elements or duplicate new-fibre parametrizations. -/
theorem six_reciprocal_decomp :
    (∑ a ∈ sixAFinset, (1 : ℚ) / (a : ℚ)) =
      (∑ t ∈ digitFinset 22, (1 : ℚ) / ((t : ℚ) + 1)) +
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ t ∈ digitFinset 21,
          (1 : ℚ) / (166375 * (t : ℚ) + (u : ℚ) + 1) := by
  have hshift : Set.InjOn (fun x : ℤ => x + 1) sixEFinset := by
    intro x hx y hy hxy
    exact add_right_cancel hxy
  rw [sixAFinset, Finset.sum_image hshift]
  simp only [Int.cast_add, Int.cast_one]
  change (∑ e ∈ digitFinset 22 ∪ sixNewFibreFinset,
      (1 : ℚ) / ((e : ℚ) + 1)) = _
  rw [Finset.sum_union six_old_new_disjoint]
  congr 1
  unfold sixNewFibreFinset
  rw [Finset.sum_image six_new_fibre_inj, Finset.product_eq_sprod, Finset.sum_product]
  congr 1
  ext u
  congr 1
  ext t
  push_cast
  ring

#print axioms six_reciprocal_decomp

/-- Every element of the translated finite set is a positive integer. -/
theorem sixAFinset_positive : ∀ a ∈ sixAFinset, 0 < a := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  have he0 : 0 ≤ e := by
    change e ∈ digitFinset 22 ∪ sixNewFibreFinset at he
    rcases Finset.mem_union.mp he with hOld | hNew
    · exact (digitFinset_bound 22 e hOld).1
    · obtain ⟨⟨u, t⟩, hpair, rfl⟩ := Finset.mem_image.mp hNew
      have ht0 := (digitFinset_bound 21 t (Finset.mem_product.mp hpair).2).1
      have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
      dsimp
      omega
  omega

private theorem suffix_card_sum_nonneg (j : ℕ) :
    (digitFinset j).card = 21 ^ j ∧
    (∑ x ∈ digitFinset j, (x : ℚ)) =
      ((digitFinset j).card : ℚ) * (433 / 1134) * ((55 : ℚ)^j - 1) ∧
    (∀ x ∈ digitFinset j, 0 ≤ x) := by
  refine ⟨digitFinset_card j, ?_, ?_⟩
  · rw [digitFinset_card]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using digitFinset_sum j
  · intro x hx
    exact (digitFinset_bound j x hx).1

/-- One old prefix and a suffix of positive length. -/
theorem old_prefix_suffix_lower (p j : ℕ) (hj : 1 ≤ j) :
    ((21 / 55 : ℚ)^j) / ((p : ℚ) + 454 / 1155) ≤
      ∑ x ∈ digitFinset j,
        1 / ((p : ℚ) * (55 : ℚ)^j + x + 1) := by
  obtain ⟨hc, hs, hn⟩ := suffix_card_sum_nonneg j
  exact old_suffix_block_lower (digitFinset j) j p hj hc hs hn

/-- The uniform comparison applies to suffix layers of positive length. -/
theorem six_new_prefix_suffix_lower (u p j : ℕ)
    (hu : u ∈ ErdosSixIndependent.U) (hj : 1 ≤ j) :
    ((21 / 55 : ℚ)^j) /
      (166375 * ((p : ℚ) + 454 / 1155)) ≤
      ∑ x ∈ digitFinset j,
        1 / (166375 * ((p : ℚ) * (55 : ℚ)^j + x) + (u : ℚ) + 1) := by
  have hOld := old_prefix_suffix_lower p j hj
  have hscale :
      (1 / 166375 : ℚ) *
        (((21 / 55 : ℚ)^j) / ((p : ℚ) + 454 / 1155)) ≤
      (1 / 166375 : ℚ) *
        (∑ x ∈ digitFinset j,
          1 / ((p : ℚ) * (55 : ℚ)^j + x + 1)) :=
    mul_le_mul_of_nonneg_left hOld (by norm_num)
  have hpoint : ∀ x ∈ digitFinset j,
      (1 / 166375 : ℚ) /
          ((p : ℚ) * (55 : ℚ)^j + x + 1) ≤
        1 / (166375 * ((p : ℚ) * (55 : ℚ)^j + x) + (u : ℚ) + 1) := by
    intro x hx
    have hx0 : 0 ≤ x := (digitFinset_bound j x hx).1
    have ht0 : (0 : ℤ) ≤ (p : ℤ) * (55 : ℤ)^j + x := by positivity
    have hh := six_new_termwise_of_mem u hu
      ((p : ℤ) * (55 : ℤ)^j + x) ht0
    convert hh using 1 <;> push_cast <;> ring
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.mul_sum] at hscale
  calc
    ((21 / 55 : ℚ)^j) /
        (166375 * ((p : ℚ) + 454 / 1155)) =
        (1 / 166375 : ℚ) *
          (((21 / 55 : ℚ)^j) / ((p : ℚ) + 454 / 1155)) := by
          simp [div_eq_mul_inv, mul_inv_rev]
          ring
    _ ≤ ∑ x ∈ digitFinset j,
        (1 / 166375 : ℚ) /
          ((p : ℚ) * (55 : ℚ)^j + x + 1) := by
          convert hscale using 1
          congr 1
          ext x
          simp [div_eq_mul_inv]
    _ ≤ _ := hsum

private theorem old_prefix_suffix_lower_int (p : ℤ) (j : ℕ)
    (hp : 0 ≤ p) (hj : 1 ≤ j) :
    ((21 / 55 : ℚ)^j) / ((p : ℚ) + 454 / 1155) ≤
      ∑ x ∈ digitFinset j,
        1 / ((p : ℚ) * (55 : ℚ)^j + x + 1) := by
  have hpq : (p.toNat : ℚ) = (p : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hp
  simpa only [hpq] using old_prefix_suffix_lower p.toNat j hj

private theorem six_new_prefix_suffix_lower_int (u : ℕ) (p : ℤ) (j : ℕ)
    (hu : u ∈ ErdosSixIndependent.U) (hp : 0 ≤ p) (hj : 1 ≤ j) :
    ((21 / 55 : ℚ)^j) /
      (166375 * ((p : ℚ) + 454 / 1155)) ≤
      ∑ x ∈ digitFinset j,
        1 / (166375 * ((p : ℚ) * (55 : ℚ)^j + x) + (u : ℚ) + 1) := by
  have hpq : (p.toNat : ℚ) = (p : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hp
  simpa only [hpq] using six_new_prefix_suffix_lower u p.toNat j hu hj

/-- Every old layer has the certified common prefix coefficient. -/
theorem old_layer_reciprocal_lower (j : ℕ) (hj : 1 ≤ j) :
    (∑ p ∈ leadingPrefix, (1 : ℚ) / ((p : ℚ) + 454 / 1155)) *
      (21 / 55 : ℚ)^j ≤
      ∑ z ∈ twoDigitLayer j, (1 : ℚ) / ((z : ℚ) + 1) := by
  conv_rhs => rw [twoDigitLayer_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hp0 := (digitFinset_bound 2 p (leadingPrefix_mem_two hp)).1
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    div_eq_mul_inv, one_mul, mul_comm] using
      old_prefix_suffix_lower_int p j hp0 hj

/-- The six new layers share a tail coefficient, with no change to their base prefixes. -/
theorem six_new_layer_reciprocal_lower (j : ℕ) (hj : 1 ≤ j) :
    (∑ u ∈ ErdosSixIndependent.U,
      ∑ d ∈ walkerFinset.erase 0,
        (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155))) *
      (21 / 55 : ℚ)^j ≤
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ z ∈ leadingBlocks j,
          (1 : ℚ) / (166375 * (z : ℚ) + (u : ℚ) + 1) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u hu
  conv_rhs => rw [leadingBlocks_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  have hd0 := (walkerFinset_bound (Finset.mem_erase.mp hd).2).1
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    div_eq_mul_inv, one_mul, mul_comm, add_comm] using
      six_new_prefix_suffix_lower_int u d j hu hd0 hj

/-- The old 22-digit contribution, with its exact two-digit singleton prefix. -/
theorem old_reciprocal_weighted_lower :
    (∑ t ∈ digitFinset 2, (1 : ℚ) / ((t : ℚ) + 1)) +
      (∑ p ∈ leadingPrefix, (1 : ℚ) / ((p : ℚ) + 454 / 1155)) *
        (∑ i ∈ Finset.range 20, (21 / 55 : ℚ)^(i+1)) ≤
      ∑ t ∈ digitFinset 22, (1 : ℚ) / ((t : ℚ) + 1) := by
  conv_rhs =>
    rw [digitFinset_prefix_sum 20 (fun t => (1 : ℚ) / ((t : ℚ) + 1))]
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => old_layer_reciprocal_lower (i + 1) (by omega))

/-- Each new fibre retains its exact residue in the singleton prefix. -/
theorem six_new_reciprocal_weighted_lower :
    (∑ u ∈ ErdosSixIndependent.U,
      ∑ d ∈ walkerFinset,
        (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1)) +
      (∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset.erase 0,
          (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155))) *
        (∑ i ∈ Finset.range 20, (21 / 55 : ℚ)^(i+1)) ≤
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ t ∈ digitFinset 21,
          (1 : ℚ) / (166375 * (t : ℚ) + (u : ℚ) + 1) := by
  have hdecomp :
      (∑ u ∈ ErdosSixIndependent.U,
        ∑ t ∈ digitFinset 21,
          (1 : ℚ) / (166375 * (t : ℚ) + (u : ℚ) + 1)) =
      (∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset,
          (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1)) +
        ∑ i ∈ Finset.range 20,
          ∑ u ∈ ErdosSixIndependent.U,
            ∑ z ∈ leadingBlocks (i + 1),
              (1 : ℚ) / (166375 * (z : ℚ) + (u : ℚ) + 1) := by
    calc
      _ = ∑ u ∈ ErdosSixIndependent.U,
          ((∑ t ∈ digitFinset 1,
              (1 : ℚ) / (166375 * (t : ℚ) + (u : ℚ) + 1)) +
            ∑ i ∈ Finset.range 20,
              ∑ z ∈ leadingBlocks (i + 1),
                (1 : ℚ) / (166375 * (z : ℚ) + (u : ℚ) + 1)) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact digitFinset_leading_sum 20 _
      _ = _ := by
        rw [digitFinset_one, Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_comm
  conv_rhs => rw [hdecomp]
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ =>
    six_new_layer_reciprocal_lower (i + 1) (by omega))

/-- Exact old and new singleton sums, plus the shared positive-length tail weight. -/
theorem six_reciprocal_weighted_lower :
    ((∑ t ∈ digitFinset 2, (1 : ℚ) / ((t : ℚ) + 1)) +
      ∑ u ∈ ErdosSixIndependent.U,
        ∑ d ∈ walkerFinset,
          (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1)) +
      ((∑ p ∈ leadingPrefix, (1 : ℚ) / ((p : ℚ) + 454 / 1155)) +
        ∑ u ∈ ErdosSixIndependent.U,
          ∑ d ∈ walkerFinset.erase 0,
            (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155))) *
        (∑ i ∈ Finset.range 20, (21 / 55 : ℚ)^(i+1)) ≤
      ∑ a ∈ sixAFinset, (1 : ℚ) / (a : ℚ) := by
  conv_rhs => rw [six_reciprocal_decomp]
  calc
    _ = ((∑ t ∈ digitFinset 2, (1 : ℚ) / ((t : ℚ) + 1)) +
          (∑ p ∈ leadingPrefix, (1 : ℚ) / ((p : ℚ) + 454 / 1155)) *
            (∑ i ∈ Finset.range 20, (21 / 55 : ℚ)^(i+1))) +
        ((∑ u ∈ ErdosSixIndependent.U,
            ∑ d ∈ walkerFinset,
              (1 : ℚ) / (166375 * (d : ℚ) + (u : ℚ) + 1)) +
          (∑ u ∈ ErdosSixIndependent.U,
            ∑ d ∈ walkerFinset.erase 0,
              (1 : ℚ) / (166375 * ((d : ℚ) + 454 / 1155))) *
            (∑ i ∈ Finset.range 20, (21 / 55 : ℚ)^(i+1))) := by ring
    _ ≤ _ := add_le_add old_reciprocal_weighted_lower six_new_reciprocal_weighted_lower

#print axioms sixAFinset_positive
#print axioms six_reciprocal_weighted_lower

end Erdos3Candidate
