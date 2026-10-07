import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The exact real parameters and floor of written Lemma F

These are scalar lemmas, not a substitute for the graph-factor theorem.
The graph theorem will derive η≥0 from its nonempty near-regular degree interval.
The upper degree parameter d is real; only the factor degree is rounded.
-/
namespace RobertPublishable.Factor

noncomputable def theta (η γ d : ℝ) : ℝ := (η + 2/d)/γ
noncomputable def roundedDegree (η γ d : ℝ) : ℕ := ⌊(1-η-theta η γ d)*d⌋₊

theorem scalar_bounds (η γ d : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hη0 : 0 ≤ η) (hη : η ≤ γ^2/8) (hd : 16/γ^2 ≤ d) :
    0 < d ∧ 0 < theta η γ d ∧ theta η γ d ≤ γ/4 ∧
    η + theta η γ d ≤ 3*γ/8 ∧
    (1-3*γ/8)*d-1 ≤ (roundedDegree η γ d : ℝ) ∧
    (roundedDegree η γ d : ℝ) ≤ (1-η-theta η γ d)*d ∧
    (roundedDegree η γ d : ℝ) ≤ d ∧
    γ*d-(d-(roundedDegree η γ d : ℝ)) ≥ (γ/2)*(roundedDegree η γ d : ℝ) := by
  have hsq : 0 < γ^2 := by positivity
  have hd0 : 0 < d := lt_of_lt_of_le (div_pos (by norm_num) hsq) hd
  have hdp : 16 ≤ d*γ^2 := (div_le_iff₀ hsq).mp hd
  have hinv : 2/d ≤ γ^2/8 := (div_le_iff₀ hd0).mpr (by nlinarith [hdp])
  have hθ0 : 0 < theta η γ d := by unfold theta; positivity
  have hθ : theta η γ d ≤ γ/4 := by
    apply (div_le_iff₀ hγ0).mpr
    nlinarith
  have hsum : η + theta η γ d ≤ 3*γ/8 := by nlinarith
  have hφ : 0 ≤ (1-η-theta η γ d)*d := by
    have hh : 0 ≤ 1-η-theta η γ d := by nlinarith
    exact mul_nonneg hh hd0.le
  have hkU : (roundedDegree η γ d : ℝ) ≤ (1-η-theta η γ d)*d := Nat.floor_le hφ
  have hkL' : (1-η-theta η γ d)*d < (roundedDegree η γ d : ℝ)+1 := Nat.lt_floor_add_one _
  have hprod : (1-3*γ/8)*d ≤ (1-η-theta η γ d)*d := by
    nlinarith [mul_nonneg (show 0 ≤ 3*γ/8-η-theta η γ d by linarith) hd0.le]
  have hkL : (1-3*γ/8)*d-1 ≤ (roundedDegree η γ d : ℝ) := by linarith
  have hkD : (roundedDegree η γ d : ℝ) ≤ d := by
    nlinarith [mul_nonneg (add_nonneg hη0 hθ0.le) hd0.le]
  have hgd : 8 ≤ γ*d := by
    nlinarith [mul_nonneg hd0.le (show 0 ≤ γ-γ^2 by nlinarith)]
  have hret : γ*d-(d-(roundedDegree η γ d : ℝ)) ≥ (γ/2)*(roundedDegree η γ d : ℝ) := by
    nlinarith [mul_nonneg hγ0.le (show 0 ≤ d-(roundedDegree η γ d : ℝ) by linarith)]
  exact ⟨hd0,hθ0,hθ,hsum,hkL,hkU,hkD,hret⟩

#print axioms scalar_bounds

set_option maxHeartbeats 0 in
/-- The actual degree-count and small-cut expansion inequalities rule out a
violating Gale cut. Graph incidence identities supply these inputs later. -/
theorem no_small_cut_violation (η γ d X Y a b c : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ γ^2/8) (hd : 16/γ^2 ≤ d)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hrow : (1-η)*d*X ≤ a+b) (hcol : a+c ≤ d*Y)
    (hexp : γ*d*(X+Y) ≤ b+c) :
    (roundedDegree η γ d : ℝ)*X ≤ (roundedDegree η γ d : ℝ)*Y+b := by
  obtain ⟨hd0,hθ0,hθ,hηθ,hkL,hkU,hkD,hret⟩ := scalar_bounds η γ d hγ0 hγ1 hη0 hη hd
  let K : ℝ := roundedDegree η γ d
  have hk0 : 0 ≤ K := by positivity
  by_contra hn
  have hviol : K*Y+b < K*X := lt_of_not_ge hn
  have hXY : Y < X := by
    by_contra hn'
    have hle : X ≤ Y := le_of_not_gt hn'
    have hm := mul_le_mul_of_nonneg_left hle hk0
    linarith
  have hkphi : (1-η-theta η γ d)*d < K+1 := Nat.lt_floor_add_one _
  have hgap : d-K ≤ (η+theta η γ d)*d+1 := by linarith
  have hmid : theta η γ d*d ≤ (1-η)*d-K := by linarith
  have hgapY := mul_le_mul_of_nonneg_right hgap hY
  have hmidX := mul_le_mul_of_nonneg_right hmid hX
  have hbudget : c < (η*d+1)*Y-theta η γ d*d*(X-Y) := by
    nlinarith [hrow,hcol,hviol,hgapY,hmidX]
  have hθid : theta η γ d*γ*d = η*d+2 := by
    unfold theta
    field_simp [ne_of_gt hγ0,ne_of_gt hd0]
  have hβ : η*d+1 ≤ theta η γ d*γ*d := by rw [hθid]; linarith
  have hβY := mul_le_mul_of_nonneg_right hβ hY
  have hdel : 0 < X-Y := by linarith
  have hcommon : theta η γ d*(d*(X-Y)) < theta η γ d*(γ*d*Y) := by
    nlinarith [hbudget,hβY,hc]
  have hdelta : d*(X-Y) < γ*d*Y := (mul_lt_mul_iff_right₀ hθ0).mp (by simpa [mul_comm] using hcommon)
  have hkdelta := mul_le_mul_of_nonneg_right hkD hdel.le
  have hbnd : b < γ*d*Y := by nlinarith [hviol,hkdelta,hdelta]
  have hpos : 0 < theta η γ d*d*(X-Y) := by positivity
  have hcnd : c < (η*d+1)*Y := by nlinarith [hbudget,hpos]
  have hsq : 0 < γ^2 := by positivity
  have hdp : 16 ≤ d*γ^2 := (div_le_iff₀ hsq).mp hd
  have hηd := mul_le_mul_of_nonneg_right hη hd0.le
  have hγsq : γ^2 ≤ γ := by nlinarith
  have hγd := mul_le_mul_of_nonneg_right hγsq hd0.le
  have hβcap : η*d+1 ≤ γ*d := by nlinarith [hηd,hdp,hγd]
  have hβcapY := mul_le_mul_of_nonneg_right hβcap hY
  have hstrict : 2*(γ*d)*Y < γ*d*(X+Y) := by
    nlinarith [mul_pos hγ0 hd0, mul_pos (mul_pos hγ0 hd0) hdel]
  nlinarith [hexp,hbnd,hcnd,hβcapY,hstrict]

#print axioms no_small_cut_violation
end RobertPublishable.Factor
