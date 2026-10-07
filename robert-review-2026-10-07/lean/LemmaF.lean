import NearRegularCriterion

/-! # The full written balanced bipartite factor lemma

The near-regular degree interval and actual small-cut expansion produce an
actual spanning factor. Neither the Gale criterion nor the factor nor retained
expansion is an input. P ⊕ Q is the original graph's balanced vertex partition.
The empty-host pathology is excluded by Nonempty P; eta nonnegativity is proved
from the literal degree interval, rather than added to the written hypotheses.
-/
open Finset SimpleGraph
open scoped Classical BigOperators
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]

set_option maxHeartbeats 0 in
/-- Lemma F, with the source's exact constants, floor, and half-vertex cut range. -/
theorem lemma_F (r : P → Q → Prop) [Nonempty P]
    (η γ d : ℝ) (hbalance : Fintype.card P = Fintype.card Q)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη : η ≤ γ^2/8) (hd : 16/γ^2 ≤ d)
    (hdeg : ∀ v, (1-η)*d ≤ ((bipGraph r).degree v : ℝ) ∧
      ((bipGraph r).degree v : ℝ) ≤ d)
    (hexp : ∀ Z : Finset (P ⊕ Q), Z.Nonempty → Z.card ≤ Fintype.card P →
      γ*d*(Z.card : ℝ) ≤ (cutCount (bipGraph r) Z : ℝ)) :
    ∃ F : SimpleGraph (P ⊕ Q), F ≤ bipGraph r ∧
      F.IsRegularOfDegree (roundedDegree η γ d) ∧
      (1-3*γ/8)*d-1 ≤ (roundedDegree η γ d : ℝ) ∧
      ∀ Z : Finset (P ⊕ Q), Z.card ≤ Fintype.card P →
        (γ/2)*(roundedDegree η γ d : ℝ)*(Z.card : ℝ) ≤ (cutCount F Z : ℝ) := by
  have hd0 : 0 < d := lt_of_lt_of_le (div_pos (by norm_num) (by positivity)) hd
  have hη0 : 0 ≤ η := by
    obtain ⟨p⟩ := ‹Nonempty P›
    have hh := (hdeg (Sum.inl p)).1.trans (hdeg (Sum.inl p)).2
    by_contra hn
    have hneg : 0 < -η := by linarith
    nlinarith [mul_pos hneg hd0]
  obtain ⟨_,_,_,_,hkL,_,_,hret⟩ := scalar_bounds η γ d hγ0 hγ1 hη0 hη hd
  obtain ⟨F,hFH,hreg⟩ := exists_spanning_regular_factor r (roundedDegree η γ d)
    hbalance (near_regular_cut_condition r η γ d hbalance hγ0 hγ1 hη hd hdeg hexp)
  refine ⟨F,hFH,hreg,hkL,?_⟩
  intro Z hZ
  by_cases hne : Z.Nonempty
  · have hloss : ∀ v, ((bipGraph r).degree v : ℝ) - (F.degree v : ℝ) ≤
        d-(roundedDegree η γ d : ℝ) := by
      intro v
      rw [hreg.degree_eq v]
      exact sub_le_sub_right (hdeg v).2 _
    have hcut := cutCount_real_le_of_degree_loss F (bipGraph r) hFH
      (d-(roundedDegree η γ d : ℝ)) hloss Z
    have he := hexp Z hne hZ
    have hm := mul_le_mul_of_nonneg_right hret (show 0 ≤ (Z.card : ℝ) by positivity)
    nlinarith
  · have hz : Z = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hz,cutCount]

#check @lemma_F
#print axioms lemma_F
end RobertPublishable.Factor
