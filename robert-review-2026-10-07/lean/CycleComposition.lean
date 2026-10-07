import MatchingIdentification
import Openmath.Proofs.HaarCycle
import Openmath.Proofs.ParabolaBarrier104

/-!
# Actual exposed cycles after two global component-union rounds

The final state is `round2`, built from the original full parabola graph with
two genuine Kempe swaps. Existing prime-three Haar successor proofs supply
the cycles only after the matching identification has been proved.
-/

noncomputable section

namespace RobertPublishable.TWO

open SimpleGraph Erdos585 Erdos585.Parabola104

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [CharP F 3] [Algebra (ZMod 3) F]

theorem label_cross_iff_matching (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (φ : (fullGraph (F := F)).EdgeLabeling F) (hφ : KempeSwap104.FullColoring φ)
    (c : F) (f : Equiv.Perm Coord)
    (hedge : ∀ x, (φ.labelGraph c).Adj (vertex t (x, false)) (vertex t (f x, true)))
    (x y : Coord) :
    (φ.labelGraph c).Adj (vertex t (x, false)) (vertex t (y, true)) ↔ y = f x := by
  constructor
  · intro h
    obtain ⟨w, _, huniq⟩ := hφ (vertex t (x, false)) c
    have hv : vertex t (y, true) = vertex t (f x, true) :=
      (huniq _ h).trans (huniq _ (hedge x)).symm
    exact chart_injective t ht0 ht1 htm (congrArg Prod.fst hv)
  · rintro rfl
    exact hedge x

theorem label_same_impossible (t : F) (φ : (fullGraph (F := F)).EdgeLabeling F)
    (c : F) (x y : Coord) (b : Bool) :
    ¬ (φ.labelGraph c).Adj (vertex t (x, b)) (vertex t (y, b)) := by
  intro h
  exact Haar.graph_same _ _ _ b (φ.labelGraph_le h)

def redFactor (t : F) : SimpleGraph (Host (F := F)) :=
  KempeSwap104.twoFactor (round2 t) 1 0

def blueFactor (t : F) : SimpleGraph (Host (F := F)) :=
  KempeSwap104.twoFactor (round2 t) (1 + t) t

def localRed (t : F) : SimpleGraph (Coord × Bool) := (redFactor t).comap (vertex t)
def localBlue (t : F) : SimpleGraph (Coord × Bool) := (blueFactor t).comap (vertex t)

theorem red_cross (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x y : Coord) : (localRed t).Adj (x, false) (y, true) ↔
    y = HaarWitness.matchAFinal x ∨ y = HaarWitness.matchZero x := by
  simp only [localRed, redFactor, SimpleGraph.comap_adj, KempeSwap104.twoFactor_adj]
  rw [label_cross_iff_matching t ht0 ht1 htm (round2 t) (round2_full t)
    1 HaarWitness.matchAFinal (round2_AFinal_edge t ht0 ht1 htm),
    label_cross_iff_matching t ht0 ht1 htm (round2 t) (round2_full t)
      0 HaarWitness.matchZero (round2_zero_edge t ht0 ht1 htm)]

theorem blue_cross (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x y : Coord) : (localBlue t).Adj (x, false) (y, true) ↔
    y = HaarWitness.matchCFinal x ∨ y = HaarWitness.matchB x := by
  simp only [localBlue, blueFactor, SimpleGraph.comap_adj, KempeSwap104.twoFactor_adj]
  rw [label_cross_iff_matching t ht0 ht1 htm (round2 t) (round2_full t)
    (1 + t) HaarWitness.matchCFinal (round2_CFinal_edge t ht0 ht1 htm),
    label_cross_iff_matching t ht0 ht1 htm (round2 t) (round2_full t)
      t HaarWitness.matchB (round2_B_edge t ht0 ht1 htm)]

theorem localRed_same (t : F) (x y : Coord) (b : Bool) :
    ¬ (localRed t).Adj (x, b) (y, b) := by
  intro h
  rcases h with h | h
  · exact label_same_impossible t (round2 t) 1 x y b h
  · exact label_same_impossible t (round2 t) 0 x y b h

theorem localBlue_same (t : F) (x y : Coord) (b : Bool) :
    ¬ (localBlue t).Adj (x, b) (y, b) := by
  intro h
  rcases h with h | h
  · exact label_same_impossible t (round2 t) (1 + t) x y b h
  · exact label_same_impossible t (round2 t) t x y b h

theorem red_cycle_local (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    ∃ p : (localRed t).Walk (0, false) (0, false), p.IsCycle ∧ ∀ v, v ∈ p.support := by
  apply HaarCycle.cycle_of_two_matchings (localRed t) HaarWitness.matchAFinal HaarWitness.matchZero
    (red_cross t ht0 ht1 htm) (localRed_same t)
  · intro x
    exact (HaarWitness.middleShift_ne_matchAFinal _ x).symm
  · rw [← HaarWitness.redFinal_eq_successor]
    exact HaarWitness.redFinal_isCycleOn

theorem blue_cycle_local (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    ∃ p : (localBlue t).Walk (0, false) (0, false), p.IsCycle ∧ ∀ v, v ∈ p.support := by
  apply HaarCycle.cycle_of_two_matchings (localBlue t) HaarWitness.matchCFinal HaarWitness.matchB
    (blue_cross t ht0 ht1 htm) (localBlue_same t)
  · intro x
    exact (HaarWitness.middleShift_ne_matchCFinal _ x).symm
  · rw [← HaarWitness.blueFinal_eq_successor]
    exact HaarWitness.blueFinal_isCycleOn

theorem mapped_support_eq_image {H : SimpleGraph (Coord × Bool)}
    {K : SimpleGraph (Host (F := F))} (t : F) (f : H →g K)
    (hf : ∀ v, f v = vertex t v) {u : Coord × Bool} (p : H.Walk u u)
    (hall : ∀ v, v ∈ p.support) :
    (p.map f).support.toFinset = Finset.univ.image (vertex t) := by
  ext v
  simp only [Walk.support_map, List.mem_toFinset, List.mem_map,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, _, hw⟩
    exact ⟨w, (hf w).symm.trans hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, hall w, (hf w).trans hw⟩

theorem chart_support_card (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    (Finset.univ.image (vertex t)).card = 54 := by
  rw [Finset.card_image_of_injective _ (vertex_injective t ht0 ht1 htm), Finset.card_univ]
  norm_num [Coord, HaarWitness.Coord, ZMod.card]

theorem final_factors_disjoint (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    Disjoint (redFactor t).edgeSet (blueFactor t).edgeSet := by
  apply SimpleGraph.disjoint_edgeSet.mpr
  have hAC : (1 : F) ≠ 1 + t := by intro h; apply ht0; linear_combination -h
  have h0C : (0 : F) ≠ 1 + t := by intro h; apply htm; linear_combination -h
  unfold redFactor blueFactor KempeSwap104.twoFactor
  rw [disjoint_sup_left, disjoint_sup_right, disjoint_sup_right]
  exact ⟨⟨EdgeLabeling.pairwise_disjoint_labelGraph hAC,
      EdgeLabeling.pairwise_disjoint_labelGraph ht1.symm⟩,
    ⟨EdgeLabeling.pairwise_disjoint_labelGraph h0C,
      EdgeLabeling.pairwise_disjoint_labelGraph ht0.symm⟩⟩

/-- The cycles are in actual final two-color factors of the full host. They
share exactly the injective chart's54 vertices, not all vertices of the host. -/
theorem actual_two_round_exposed_cycles (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    ∃ (p : (redFactor t).Walk (vertex t (0, false)) (vertex t (0, false)))
      (q : (blueFactor t).Walk (vertex t (0, false)) (vertex t (0, false))),
      p.IsCycle ∧ q.IsCycle ∧
      p.support.toFinset = q.support.toFinset ∧
      Disjoint p.edges.toFinset q.edges.toFinset ∧ p.support.toFinset.card = 54 := by
  obtain ⟨p, hp, hps⟩ := red_cycle_local t ht0 ht1 htm
  obtain ⟨q, hq, hqs⟩ := blue_cycle_local t ht0 ht1 htm
  let rmap : localRed t →g redFactor t := Hom.comap (vertex t) (redFactor t)
  let bmap : localBlue t →g blueFactor t := Hom.comap (vertex t) (blueFactor t)
  have hrS := mapped_support_eq_image t rmap (fun _ => rfl) p hps
  have hbS := mapped_support_eq_image t bmap (fun _ => rfl) q hqs
  refine ⟨p.map rmap, q.map bmap, hp.map (vertex_injective t ht0 ht1 htm),
    hq.map (vertex_injective t ht0 ht1 htm), hrS.trans hbS.symm, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro e heR heB
    exact Set.disjoint_left.mp (final_factors_disjoint t ht0 ht1 htm)
      ((p.map rmap).edges_subset_edgeSet (List.mem_toFinset.mp heR))
      ((q.map bmap).edges_subset_edgeSet (List.mem_toFinset.mp heB))
  · exact (congrArg Finset.card hrS).trans (chart_support_card t ht0 ht1 htm)

/-- The old zero/one-round barrier and the new actual two-round witness have
the same full-host semantics. No assertion about individual-flip minimality. -/
theorem exactly_two_component_union_rounds (hc : 3 < Fintype.card F) :
    ParabolaBarrier104.OneRoundBarrier (F := F) ∧
    ∃ (t : F), t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 ∧
      ∃ (p : (redFactor t).Walk (vertex t (0, false)) (vertex t (0, false)))
        (q : (blueFactor t).Walk (vertex t (0, false)) (vertex t (0, false))),
        p.IsCycle ∧ q.IsCycle ∧ p.support.toFinset = q.support.toFinset ∧
        Disjoint p.edges.toFinset q.edges.toFinset ∧ p.support.toFinset.card = 54 := by
  obtain ⟨t, ht0, ht1, htm⟩ := exists_nonprime_parameter hc
  exact ⟨ParabolaBarrier104.one_round_barrier,
    t, ht0, ht1, htm, actual_two_round_exposed_cycles t ht0 ht1 htm⟩

theorem family_exactly_two_component_union_rounds (k : ℕ) (hk : 2 ≤ k) :
    ParabolaBarrier104.OneRoundBarrier (F := ParabolaBarrier104.FamilyField k) ∧
    ∃ (t : ParabolaBarrier104.FamilyField k), t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 ∧
      ∃ (p : (redFactor t).Walk (vertex t (0, false)) (vertex t (0, false)))
        (q : (blueFactor t).Walk (vertex t (0, false)) (vertex t (0, false))),
        p.IsCycle ∧ q.IsCycle ∧ p.support.toFinset = q.support.toFinset ∧
        Disjoint p.edges.toFinset q.edges.toFinset ∧ p.support.toFinset.card = 54 := by
  apply exactly_two_component_union_rounds
  rw [ParabolaBarrier104.field_card k hk]
  have hpow : (3 : ℕ) ^ 2 ≤ 3 ^ k := by gcongr <;> omega
  norm_num at hpow
  omega

#print axioms label_cross_iff_matching
#print axioms red_cross
#print axioms blue_cross
#print axioms red_cycle_local
#print axioms blue_cycle_local
#print axioms chart_support_card
#print axioms final_factors_disjoint
#print axioms actual_two_round_exposed_cycles
#print axioms exactly_two_component_union_rounds
#print axioms family_exactly_two_component_union_rounds
#check @actual_two_round_exposed_cycles
#check @family_exactly_two_component_union_rounds

end RobertPublishable.TWO
