import Openmath.Proofs.ParabolaAlgebra104
import Openmath.Proofs.HaarWitness

/-!
# An explicit three-dimensional chart in the full parabola host

Colors 0, 1, t and 1+t are used, with t outside the prime field.
This file proves the chart is injective rather than postulating an affine
component or a cycle pair. Global Kempe component identification is separate.
-/

namespace RobertPublishable.TWO

open Erdos585 Erdos585.Parabola104

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {F : Type*} [Field F] [CharP F 3] [Algebra (ZMod 3) F]

abbrev Coord := HaarWitness.Coord 3

theorem prime_scalar_cases (s : ZMod 3) :
    algebraMap (ZMod 3) F s = 0 ∨ algebraMap (ZMod 3) F s = 1 ∨
      algebraMap (ZMod 3) F s = -1 := by
  have hs : s = 0 ∨ s = 1 ∨ s = -1 :=
    (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = -1) s
  rcases hs with rfl | rfl | rfl <;> simp

theorem prime_scalar_t_independent (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (a b : ZMod 3)
    (h : algebraMap (ZMod 3) F a + algebraMap (ZMod 3) F b * t = 0) :
    a = 0 ∧ b = 0 := by
  let i : ZMod 3 →+* F := algebraMap (ZMod 3) F
  change i a + i b * t = 0 at h
  by_cases hb : b = 0
  · refine ⟨i.injective ?_, hb⟩
    simpa [hb] using h
  · have hbF : i b ≠ 0 := fun he => hb (i.injective (by simpa using he))
    have he : i b * t = -i a := by linear_combination h
    have ht : t = i (-a / b) := by
      calc
        t = -i a / i b := (eq_div_iff hbF).mpr (by simpa [mul_comm] using he)
        _ = i (-a / b) := by simp
    rcases prime_scalar_cases (F := F) (-a / b) with h0 | h1 | hm
    · exact False.elim (ht0 (ht.trans h0))
    · exact False.elim (ht1 (ht.trans h1))
    · exact False.elim (htm (ht.trans hm))

def chart (t : F) : Coord →ₗ[ZMod 3] F × F where
  toFun x := x.1 • point 1 + x.2.1 • point t + x.2.2 • point (1 + t)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' r x := by
    simp [smul_add, smul_smul]

@[simp] theorem chart_A (t : F) : chart t (1, 0, 0) = point 1 := by
  simp [chart]

@[simp] theorem chart_B (t : F) : chart t (0, 1, 0) = point t := by
  simp [chart]

@[simp] theorem chart_C (t : F) : chart t (0, 0, 1) = point (1 + t) := by
  simp [chart]

theorem chart_kernel (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) (h : chart t x = 0) : x = 0 := by
  let i : ZMod 3 →+* F := algebraMap (ZMod 3) F
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change (x.1 • point 1 + x.2.1 • point t + x.2.2 • point (1 + t)).1 = 0 at hx
  change (x.1 • point 1 + x.2.1 • point t + x.2.2 • point (1 + t)).2 = 0 at hy
  simp only [point, Prod.fst_add, Prod.snd_add, Algebra.smul_def,
    Prod.algebraMap_apply, Prod.fst_mul, Prod.snd_mul, one_pow, mul_one] at hx hy
  have hfirst : i (x.1 + x.2.2) + i (x.2.1 + x.2.2) * t = 0 := by
    simp only [map_add]
    linear_combination hx
  obtain ⟨ha, hb⟩ := prime_scalar_t_independent t ht0 ht1 htm _ _ hfirst
  have haF := congrArg i ha
  have hbF := congrArg i hb
  simp only [map_add, map_zero] at haF hbF
  have hthree : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hcF : i x.2.2 * t = 0 := by
    linear_combination (i x.2.2 * t) * hthree - hy + haF + t ^ 2 * hbF
  have hc : x.2.2 = 0 :=
    i.injective (by simpa using (mul_eq_zero.mp hcF).resolve_right ht0)
  exact Prod.ext (by simpa [hc] using ha) (Prod.ext (by simpa [hc] using hb) hc)

theorem chart_injective (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    Function.Injective (chart t) := by
  intro x y h
  apply sub_eq_zero.mp
  apply chart_kernel t ht0 ht1 htm
  rw [map_sub, h, sub_self]

theorem exists_nonprime_parameter [Fintype F] [DecidableEq F]
    (hc : 3 < Fintype.card F) : ∃ t : F, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 := by
  have hcard : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa using lt_of_le_of_lt (Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)) hc
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨t, ?_, ?_, ?_⟩ <;> intro h <;> apply ht <;> simp [h]

#print axioms prime_scalar_cases
#print axioms prime_scalar_t_independent
#print axioms chart_kernel
#print axioms chart_injective
#print axioms exists_nonprime_parameter

end RobertPublishable.TWO
