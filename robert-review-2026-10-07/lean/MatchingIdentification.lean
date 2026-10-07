import GlobalSelectors

/-!
# The two actual global swaps implement the prime-three Haar matchings

The graph and coloring are the full original parabola host. Statements below
identify actual colored edges on the injective chart; no closed-move or
cycle-pair hypothesis is used. The cycle extraction is a separate composition.
-/

noncomputable section

namespace RobertPublishable.TWO

open SimpleGraph Erdos585 Erdos585.Parabola104

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [CharP F 3] [Algebra (ZMod 3) F]

theorem canonical_zero_edge (t : F) (x : Coord) :
    ((canonical (F := F)).labelGraph 0).Adj (vertex t (x, false)) (vertex t (x, true)) := by
  apply (canonical_label_cross 0 _ _).mpr
  simp [vertex]

theorem canonical_B_edge (t : F) (x : Coord) :
    ((canonical (F := F)).labelGraph t).Adj
      (vertex t (x, false)) (vertex t (x + (0, 1, 0), true)) := by
  apply (canonical_label_cross t _ _).mpr
  simp [vertex, map_add]

theorem canonical_A_edge (t : F) (x : Coord) :
    ((canonical (F := F)).labelGraph 1).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchA x, true)) := by
  apply (canonical_label_cross 1 _ _).mpr
  simp [vertex, chart_matchA]

theorem canonical_C_edge (t : F) (x : Coord) :
    ((canonical (F := F)).labelGraph (1 + t)).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchC x, true)) := by
  apply (canonical_label_cross (1 + t) _ _).mpr
  simp [vertex, chart_matchC]

private theorem matchZero_eq_add_B (x : Coord) (h : x.1 = x.2.2) :
    HaarWitness.matchZero x = x + (0, 1, 0) := by
  simp [HaarWitness.matchZero, HaarWitness.middleShift, h, Prod.add_def]

private theorem matchZero_eq_self (x : Coord) (h : x.1 ≠ x.2.2) :
    HaarWitness.matchZero x = x := by
  simp [HaarWitness.matchZero, HaarWitness.middleShift, h]

private theorem matchB_eq_self (x : Coord) (h : x.1 = x.2.2) :
    HaarWitness.matchB x = x := by
  ext <;> simp [HaarWitness.matchB, HaarWitness.middleShift, h]

private theorem matchB_eq_add_B (x : Coord) (h : x.1 ≠ x.2.2) :
    HaarWitness.matchB x = x + (0, 1, 0) := by
  simp [HaarWitness.matchB, HaarWitness.middleShift, h, Prod.add_def]

theorem round1_zero_edge (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    ((round1 t).labelGraph 0).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchZero x, true)) := by
  change ((KempeSwap104.swap canonical 0 t (firstComponents t)).labelGraph 0).Adj _ _
  by_cases hx : x.1 = x.2.2
  · have hu := (firstSelected_vertex t ht0 ht1 htm x false).mpr hx
    rw [KempeSwap104.swap_labelGraph_adj_selected canonical 0 t (firstComponents t) hu]
    simp only [Equiv.swap_apply_left]
    rw [matchZero_eq_add_B x hx]
    exact canonical_B_edge t x
  · have hu : ¬ KempeSwap104.Selected canonical 0 t (firstComponents t) (vertex t (x, false)) :=
      fun h => hx ((firstSelected_vertex t ht0 ht1 htm x false).mp h)
    rw [KempeSwap104.swap_labelGraph_adj_not_selected canonical 0 t (firstComponents t) hu]
    rw [matchZero_eq_self x hx]
    exact canonical_zero_edge t x

theorem round1_B_edge (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    ((round1 t).labelGraph t).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchB x, true)) := by
  change ((KempeSwap104.swap canonical 0 t (firstComponents t)).labelGraph t).Adj _ _
  by_cases hx : x.1 = x.2.2
  · have hu := (firstSelected_vertex t ht0 ht1 htm x false).mpr hx
    rw [KempeSwap104.swap_labelGraph_adj_selected canonical 0 t (firstComponents t) hu]
    simp only [Equiv.swap_apply_right]
    rw [matchB_eq_self x hx]
    exact canonical_zero_edge t x
  · have hu : ¬ KempeSwap104.Selected canonical 0 t (firstComponents t) (vertex t (x, false)) :=
      fun h => hx ((firstSelected_vertex t ht0 ht1 htm x false).mp h)
    rw [KempeSwap104.swap_labelGraph_adj_not_selected canonical 0 t (firstComponents t) hu]
    rw [matchB_eq_add_B x hx]
    exact canonical_B_edge t x

theorem round1_A_edge (t : F) (ht1 : t ≠ 1) (x : Coord) :
    ((round1 t).labelGraph 1).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchA x, true)) := by
  change ((KempeSwap104.swap canonical 0 t (firstComponents t)).labelGraph 1).Adj _ _
  rw [swap_labelGraph_of_other canonical 0 t 1 (firstComponents t) one_ne_zero ht1.symm]
  exact canonical_A_edge t x

theorem round1_C_edge (t : F) (htm : t ≠ -1) (x : Coord) :
    ((round1 t).labelGraph (1 + t)).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchC x, true)) := by
  have hc0 : 1 + t ≠ 0 := by intro h; apply htm; linear_combination h
  have hct : 1 + t ≠ t := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination h
  change ((KempeSwap104.swap canonical 0 t (firstComponents t)).labelGraph (1 + t)).Adj _ _
  rw [swap_labelGraph_of_other canonical 0 t (1 + t) (firstComponents t) hc0 hct]
  exact canonical_C_edge t x

theorem round2_AFinal_edge (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    ((round2 t).labelGraph 1).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchAFinal x, true)) := by
  change ((KempeSwap104.swap (round1 t) 1 (1 + t) (secondComponents t)).labelGraph 1).Adj _ _
  by_cases hx : ∃ u : ZMod 3, x = HaarWitness.mark u
  · obtain ⟨u, rfl⟩ := hx
    have hu := (secondSelected_left t ht0 ht1 htm (HaarWitness.mark u)).mpr ⟨u, rfl⟩
    rw [KempeSwap104.swap_labelGraph_adj_selected (round1 t) 1 (1 + t) (secondComponents t) hu]
    simp only [Equiv.swap_apply_left, HaarWitness.matchAFinal_mark]
    exact round1_C_edge t htm _
  · have hu : ¬ KempeSwap104.Selected (round1 t) 1 (1 + t) (secondComponents t) (vertex t (x, false)) :=
      fun h => hx ((secondSelected_left t ht0 ht1 htm x).mp h)
    rw [KempeSwap104.swap_labelGraph_adj_not_selected (round1 t) 1 (1 + t) (secondComponents t) hu]
    rw [HaarWitness.matchAFinal_fixed x (not_exists.mp hx)]
    exact round1_A_edge t ht1 x

theorem round2_CFinal_edge (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    ((round2 t).labelGraph (1 + t)).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchCFinal x, true)) := by
  change ((KempeSwap104.swap (round1 t) 1 (1 + t) (secondComponents t)).labelGraph (1 + t)).Adj _ _
  by_cases hx : ∃ u : ZMod 3, x = HaarWitness.mark u
  · obtain ⟨u, rfl⟩ := hx
    have hu := (secondSelected_left t ht0 ht1 htm (HaarWitness.mark u)).mpr ⟨u, rfl⟩
    rw [KempeSwap104.swap_labelGraph_adj_selected (round1 t) 1 (1 + t) (secondComponents t) hu]
    simp only [Equiv.swap_apply_right, HaarWitness.matchCFinal_mark]
    exact round1_A_edge t ht1 _
  · have hu : ¬ KempeSwap104.Selected (round1 t) 1 (1 + t) (secondComponents t) (vertex t (x, false)) :=
      fun h => hx ((secondSelected_left t ht0 ht1 htm x).mp h)
    rw [KempeSwap104.swap_labelGraph_adj_not_selected (round1 t) 1 (1 + t) (secondComponents t) hu]
    rw [HaarWitness.matchCFinal_fixed x (not_exists.mp hx)]
    exact round1_C_edge t htm x

theorem round2_zero_edge (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    ((round2 t).labelGraph 0).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchZero x, true)) := by
  have hc0 : 1 + t ≠ 0 := by intro h; apply htm; linear_combination h
  change ((KempeSwap104.swap (round1 t) 1 (1 + t) (secondComponents t)).labelGraph 0).Adj _ _
  rw [swap_labelGraph_of_other (round1 t) 1 (1 + t) 0 (secondComponents t) zero_ne_one hc0.symm]
  exact round1_zero_edge t ht0 ht1 htm x

theorem round2_B_edge (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    ((round2 t).labelGraph t).Adj
      (vertex t (x, false)) (vertex t (HaarWitness.matchB x, true)) := by
  have htc : t ≠ 1 + t := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination -h
  change ((KempeSwap104.swap (round1 t) 1 (1 + t) (secondComponents t)).labelGraph t).Adj _ _
  rw [swap_labelGraph_of_other (round1 t) 1 (1 + t) t (secondComponents t) ht1 htc]
  exact round1_B_edge t ht0 ht1 htm x

#print axioms round1_zero_edge
#print axioms round1_B_edge
#print axioms round2_AFinal_edge
#print axioms round2_CFinal_edge
#print axioms round2_zero_edge
#print axioms round2_B_edge

end RobertPublishable.TWO
