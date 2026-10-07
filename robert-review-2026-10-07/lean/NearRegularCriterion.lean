import GraphCuts
import NearRegularScalars

/-! # Near regularity and literal edge expansion imply the full Gale criterion

The complementary-pair argument preserves unit edge capacities. In particular
the network cut criterion is proved here, never supplied as a main premise. -/
open Finset SimpleGraph
open scoped Classical BigOperators
namespace RobertPublishable.Factor
variable {P Q : Type*} [DecidableEq P] [DecidableEq Q] [Fintype P] [Fintype Q]

lemma row_degree_bounds (r : P → Q → Prop) (η d : ℝ)
    (hdeg : ∀ v, (1-η)*d ≤ ((bipGraph r).degree v : ℝ) ∧
      ((bipGraph r).degree v : ℝ) ≤ d) (X : Finset P) :
    (1-η)*d*(X.card : ℝ) ≤ (cellCount r X univ : ℝ) ∧
      (cellCount r X univ : ℝ) ≤ d*(X.card : ℝ) := by
  rw [row_sum,Nat.cast_sum]
  constructor
  · calc
      (1-η)*d*(X.card : ℝ) = ∑ p ∈ X, (1-η)*d := by simp [mul_comm]
      _ ≤ ∑ p ∈ X, ((univ.filter (r p)).card : ℝ) := by
        apply sum_le_sum
        intro p _
        simpa only [degree_left] using (hdeg (Sum.inl p)).1
  · calc
      (∑ p ∈ X, ((univ.filter (r p)).card : ℝ)) ≤ ∑ _p ∈ X, d := by
        apply sum_le_sum
        intro p _
        simpa only [degree_left] using (hdeg (Sum.inl p)).2
      _ = d*(X.card : ℝ) := by simp [mul_comm]

lemma column_degree_bounds (r : P → Q → Prop) (η d : ℝ)
    (hdeg : ∀ v, (1-η)*d ≤ ((bipGraph r).degree v : ℝ) ∧
      ((bipGraph r).degree v : ℝ) ≤ d) (Y : Finset Q) :
    (1-η)*d*(Y.card : ℝ) ≤ (cellCount r univ Y : ℝ) ∧
      (cellCount r univ Y : ℝ) ≤ d*(Y.card : ℝ) := by
  rw [column_sum,Nat.cast_sum]
  constructor
  · calc
      (1-η)*d*(Y.card : ℝ) = ∑ q ∈ Y, (1-η)*d := by simp [mul_comm]
      _ ≤ ∑ q ∈ Y, ((univ.filter (fun p => r p q)).card : ℝ) := by
        apply sum_le_sum
        intro q _
        simpa only [degree_right] using (hdeg (Sum.inr q)).1
  · calc
      (∑ q ∈ Y, ((univ.filter (fun p => r p q)).card : ℝ)) ≤ ∑ _q ∈ Y, d := by
        apply sum_le_sum
        intro q _
        simpa only [degree_right] using (hdeg (Sum.inr q)).2
      _ = d*(Y.card : ℝ) := by simp [mul_comm]

set_option maxHeartbeats 0 in
theorem near_regular_cut_condition (r : P → Q → Prop) [Nonempty P]
    (η γ d : ℝ) (hbalance : Fintype.card P = Fintype.card Q)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη : η ≤ γ^2/8) (hd : 16/γ^2 ≤ d)
    (hdeg : ∀ v, (1-η)*d ≤ ((bipGraph r).degree v : ℝ) ∧
      ((bipGraph r).degree v : ℝ) ≤ d)
    (hexp : ∀ Z : Finset (P ⊕ Q), Z.Nonempty → Z.card ≤ Fintype.card P →
      γ*d*(Z.card : ℝ) ≤ (cutCount (bipGraph r) Z : ℝ)) :
    CutCondition r (roundedDegree η γ d) := by
  have hd0 : 0 < d := lt_of_lt_of_le (div_pos (by norm_num) (by positivity)) hd
  have hη0 : 0 ≤ η := by
    obtain ⟨p⟩ := ‹Nonempty P›
    have hh := (hdeg (Sum.inl p)).1.trans (hdeg (Sum.inl p)).2
    by_contra hn
    have hneg : 0 < -η := by linarith
    have hpos := mul_pos hneg hd0
    nlinarith
  let K : ℝ := roundedDegree η γ d
  have hK : 0 ≤ K := by positivity
  have he : ∀ X : Finset P, ∀ Y : Finset Q,
      X.card + Y.card ≤ Fintype.card P →
      γ*d*((X.card : ℝ)+(Y.card : ℝ)) ≤
        (cellCount r X Yᶜ : ℝ)+(cellCount r Xᶜ Y : ℝ) := by
    intro X Y hcard
    by_cases h0 : X.card + Y.card = 0
    · have hx : X.card = 0 := by omega
      have hy : Y.card = 0 := by omega
      simp only [hx,hy,Nat.cast_zero,zero_add,mul_zero]
      positivity
    · have hne : (X.disjSum Y).Nonempty := card_pos.mp (by rw [card_disjSum]; omega)
      have hh := hexp (X.disjSum Y) hne (by simpa only [card_disjSum] using hcard)
      simpa only [card_disjSum,bipartite_cut_count,Nat.cast_add] using hh
  intro X Y
  have hb : 0 ≤ (cellCount r X Yᶜ : ℝ) := by positivity
  have hc : 0 ≤ (cellCount r Xᶜ Y : ℝ) := by positivity
  by_cases hsmall : X.card + Y.card ≤ Fintype.card P
  · have hrow := (row_degree_bounds r η d hdeg X).1
    have hcol := (column_degree_bounds r η d hdeg Y).2
    rw [row_split r X Y,Nat.cast_add] at hrow
    rw [column_split r X Y,Nat.cast_add] at hcol
    have hs := no_small_cut_violation η γ d X.card Y.card
      (cellCount r X Y) (cellCount r X Yᶜ) (cellCount r Xᶜ Y)
      hγ0 hγ1 hη0 hη hd (by positivity) (by positivity) hb hc hrow hcol (he X Y hsmall)
    rw [crossing_as_cell]
    exact_mod_cast hs
  · have hx : X.card + Xᶜ.card = Fintype.card P := card_add_card_compl X
    have hy : Y.card + Yᶜ.card = Fintype.card Q := card_add_card_compl Y
    have hcompsmall : Xᶜ.card + Yᶜ.card ≤ Fintype.card P := by omega
    have hrow := (column_degree_bounds r η d hdeg Yᶜ).1
    have hcol := (row_degree_bounds r η d hdeg Xᶜ).2
    rw [column_split r X Yᶜ,Nat.cast_add] at hrow
    rw [row_split r Xᶜ Y,Nat.cast_add] at hcol
    have hec := he Xᶜ Yᶜ hcompsmall
    simp only [compl_compl] at hec
    have hs := no_small_cut_violation η γ d Yᶜ.card Xᶜ.card
      (cellCount r Xᶜ Yᶜ) (cellCount r X Yᶜ) (cellCount r Xᶜ Y)
      hγ0 hγ1 hη0 hη hd (by positivity) (by positivity) hb hc
      (by linarith [hrow]) (by linarith [hcol]) (by linarith [hec])
    have hn : roundedDegree η γ d * Yᶜ.card ≤
        roundedDegree η γ d * Xᶜ.card + cellCount r X Yᶜ := by exact_mod_cast hs
    have hxm := congrArg (fun n : ℕ => roundedDegree η γ d * n) hx
    have hym := congrArg (fun n : ℕ => roundedDegree η γ d * n) hy
    simp only [Nat.mul_add] at hxm hym
    rw [hbalance] at hxm
    rw [crossing_as_cell]
    change roundedDegree η γ d * X.card ≤ roundedDegree η γ d * Y.card + cellCount r X Yᶜ
    nlinarith

#print axioms near_regular_cut_condition
end RobertPublishable.Factor
