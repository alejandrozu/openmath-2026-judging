import ComponentUnions
import PrimeChart
import Openmath.Proofs.ParabolaGraph104

/-!
# First global selector in the literal parabola host

The canonical host includes every field colour. Closure below is proved for
actual global edges of the selected two-colour factor, independently of all
unused colours. No inducedness or assumed legal-move interface is introduced.
-/

noncomputable section

namespace RobertPublishable.TWO

open SimpleGraph Erdos585 Erdos585.Parabola104

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [CharP F 3] [Algebra (ZMod 3) F]

abbrev Host := (F × F) × Bool

def vertex (t : F) (v : Coord × Bool) : Host (F := F) := (chart t v.1, v.2)

theorem vertex_injective (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    Function.Injective (vertex t) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  exact Prod.ext (chart_injective t ht0 ht1 htm (congrArg Prod.fst h))
    (congrArg (fun v : Host (F := F) => v.2) h)

def firstSet (t : F) : Set (Host (F := F)) :=
  {v | ∃ x : Coord, chart t x = v.1 ∧ x.1 = x.2.2}

theorem firstSet_edge_closed (t : F) :
    ∀ ⦃u v : Host (F := F)⦄, u ∈ firstSet t →
      (KempeSwap104.twoFactor (canonical (F := F)) 0 t).Adj u v → v ∈ firstSet t := by
  rintro ⟨X, b⟩ ⟨Y, c⟩ ⟨x, hx, heq⟩ h
  change chart t x = X at hx
  subst X
  cases b <;> cases c
  · rcases h with h | h
    · exact False.elim (canonical_label_same 0 (chart t x) Y false h)
    · exact False.elim (canonical_label_same t (chart t x) Y false h)
  · rcases h with h | h
    · have hy := (canonical_label_cross 0 (chart t x) Y).mp h
      simp only [point_zero] at hy
      exact ⟨x, (sub_eq_zero.mp hy).symm, heq⟩
    · have hy := (canonical_label_cross t (chart t x) Y).mp h
      refine ⟨x + (0, 1, 0), ?_, ?_⟩
      · rw [map_add, chart_B]
        calc
          chart t x + point t = chart t x + (Y - chart t x) := by rw [hy]
          _ = Y := by abel
      · simpa only [Prod.fst_add, Prod.snd_add, add_zero] using heq
  · rcases h with h | h
    · have hy := (canonical_label_cross 0 Y (chart t x)).mp h.symm
      simp only [point_zero] at hy
      exact ⟨x, sub_eq_zero.mp hy, heq⟩
    · have hy := (canonical_label_cross t Y (chart t x)).mp h.symm
      refine ⟨x - (0, 1, 0), ?_, ?_⟩
      · rw [map_sub, chart_B]
        calc
          chart t x - point t = chart t x - (chart t x - Y) := by rw [hy]
          _ = Y := by abel
      · simpa [Prod.sub_def] using heq
  · rcases h with h | h
    · exact False.elim (canonical_label_same 0 (chart t x) Y true h)
    · exact False.elim (canonical_label_same t (chart t x) Y true h)

def firstComponents (t : F) :
    Set (KempeSwap104.twoFactor (canonical (F := F)) 0 t).ConnectedComponent :=
  componentsInside _ (firstSet t)

theorem firstSelected_iff (t : F) (v : Host (F := F)) :
    KempeSwap104.Selected canonical 0 t (firstComponents t) v ↔ v ∈ firstSet t :=
  selected_iff_of_edge_closed canonical 0 t (firstSet t) (firstSet_edge_closed t) v

def round1 (t : F) : (fullGraph (F := F)).EdgeLabeling F :=
  KempeSwap104.swap canonical 0 t (firstComponents t)

theorem round1_full (t : F) : KempeSwap104.FullColoring (round1 t) :=
  KempeSwap104.swap_fullColoring canonical canonical_full 0 t (firstComponents t)

theorem chart_matchA (t : F) (x : Coord) :
    chart t (HaarWitness.matchA x) = chart t x + point 1 := by
  change chart t (x + (1, 0, 0)) = _
  rw [map_add, chart_A]

theorem chart_matchC (t : F) (x : Coord) :
    chart t (HaarWitness.matchC x) = chart t x + point (1 + t) := by
  change chart t (x + (0, 0, 1)) = _
  rw [map_add, chart_C]

private theorem markC_eq_markA_previous (u : ZMod 3) :
    HaarWitness.matchC (HaarWitness.mark u) =
      HaarWitness.matchA (HaarWitness.mark (u - 1)) := by
  ext <;> simp [HaarWitness.matchA, HaarWitness.matchC, HaarWitness.mark] <;> ring

private theorem markA_sub_C (u : ZMod 3) :
    HaarWitness.matchA (HaarWitness.mark u) - (0, 0, 1) =
      HaarWitness.mark (u + 1) := by
  ext <;> simp [HaarWitness.matchA, HaarWitness.mark, Prod.sub_def] <;> ring

def secondSet (t : F) : Set (Host (F := F)) :=
  {v | if v.2 then ∃ u : ZMod 3, chart t (HaarWitness.matchA (HaarWitness.mark u)) = v.1
       else ∃ u : ZMod 3, chart t (HaarWitness.mark u) = v.1}

theorem secondSet_canonical_edge_closed (t : F) :
    ∀ ⦃u v : Host (F := F)⦄, u ∈ secondSet t →
      (KempeSwap104.twoFactor (canonical (F := F)) 1 (1 + t)).Adj u v → v ∈ secondSet t := by
  rintro ⟨X, b⟩ ⟨Y, c⟩ hu h
  cases b <;> cases c
  · rcases h with h | h
    · exact False.elim (canonical_label_same 1 X Y false h)
    · exact False.elim (canonical_label_same (1 + t) X Y false h)
  · obtain ⟨u, hx⟩ := hu
    change chart t (HaarWitness.mark u) = X at hx
    subst X
    rcases h with h | h
    · have hy := (canonical_label_cross 1 (chart t (HaarWitness.mark u)) Y).mp h
      refine ⟨u, ?_⟩
      calc
        chart t (HaarWitness.matchA (HaarWitness.mark u)) =
            chart t (HaarWitness.mark u) + point 1 := chart_matchA t _
        _ = chart t (HaarWitness.mark u) + (Y - chart t (HaarWitness.mark u)) := by rw [hy]
        _ = Y := by abel
    · have hy := (canonical_label_cross (1 + t) (chart t (HaarWitness.mark u)) Y).mp h
      refine ⟨u - 1, ?_⟩
      calc
        chart t (HaarWitness.matchA (HaarWitness.mark (u - 1))) =
            chart t (HaarWitness.matchC (HaarWitness.mark u)) := by rw [markC_eq_markA_previous]
        _ = chart t (HaarWitness.mark u) + point (1 + t) := chart_matchC t _
        _ = chart t (HaarWitness.mark u) + (Y - chart t (HaarWitness.mark u)) := by rw [hy]
        _ = Y := by abel
  · obtain ⟨u, hx⟩ := hu
    change chart t (HaarWitness.matchA (HaarWitness.mark u)) = X at hx
    subst X
    rcases h with h | h
    · have hy := (canonical_label_cross 1 Y (chart t (HaarWitness.matchA (HaarWitness.mark u)))).mp h.symm
      refine ⟨u, ?_⟩
      calc
        chart t (HaarWitness.mark u) =
            chart t (HaarWitness.matchA (HaarWitness.mark u)) - point 1 := by rw [chart_matchA]; abel
        _ = chart t (HaarWitness.matchA (HaarWitness.mark u)) -
            (chart t (HaarWitness.matchA (HaarWitness.mark u)) - Y) := by rw [hy]
        _ = Y := by abel
    · have hy := (canonical_label_cross (1 + t) Y (chart t (HaarWitness.matchA (HaarWitness.mark u)))).mp h.symm
      refine ⟨u + 1, ?_⟩
      calc
        chart t (HaarWitness.mark (u + 1)) =
            chart t (HaarWitness.matchA (HaarWitness.mark u) - (0, 0, 1)) := by rw [markA_sub_C]
        _ = chart t (HaarWitness.matchA (HaarWitness.mark u)) - point (1 + t) := by rw [map_sub, chart_C]
        _ = chart t (HaarWitness.matchA (HaarWitness.mark u)) -
            (chart t (HaarWitness.matchA (HaarWitness.mark u)) - Y) := by rw [hy]
        _ = Y := by abel
  · rcases h with h | h
    · exact False.elim (canonical_label_same 1 X Y true h)
    · exact False.elim (canonical_label_same (1 + t) X Y true h)

theorem round1_AC_unchanged (t : F) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    KempeSwap104.twoFactor (round1 t) 1 (1 + t) = KempeSwap104.twoFactor canonical 1 (1 + t) := by
  have hc0 : 1 + t ≠ 0 := by intro h; apply htm; linear_combination h
  have hct : 1 + t ≠ t := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination h
  exact swap_twoFactor_of_other canonical 0 t 1 (1 + t) (firstComponents t)
    one_ne_zero ht1.symm hc0 hct

theorem secondSet_edge_closed (t : F) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    ∀ ⦃u v : Host (F := F)⦄, u ∈ secondSet t →
      (KempeSwap104.twoFactor (round1 t) 1 (1 + t)).Adj u v → v ∈ secondSet t := by
  intro u v hu h
  rw [round1_AC_unchanged t ht1 htm] at h
  exact secondSet_canonical_edge_closed t hu h

def secondComponents (t : F) :
    Set (KempeSwap104.twoFactor (round1 t) 1 (1 + t)).ConnectedComponent :=
  componentsInside _ (secondSet t)

theorem secondSelected_iff (t : F) (ht1 : t ≠ 1) (htm : t ≠ -1) (v : Host (F := F)) :
    KempeSwap104.Selected (round1 t) 1 (1 + t) (secondComponents t) v ↔ v ∈ secondSet t :=
  selected_iff_of_edge_closed (round1 t) 1 (1 + t) (secondSet t)
    (secondSet_edge_closed t ht1 htm) v

def round2 (t : F) : (fullGraph (F := F)).EdgeLabeling F :=
  KempeSwap104.swap (round1 t) 1 (1 + t) (secondComponents t)

theorem round2_full (t : F) : KempeSwap104.FullColoring (round2 t) :=
  KempeSwap104.swap_fullColoring (round1 t) (round1_full t) 1 (1 + t) (secondComponents t)

theorem firstSelected_vertex (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) (b : Bool) :
    KempeSwap104.Selected canonical 0 t (firstComponents t) (vertex t (x, b)) ↔ x.1 = x.2.2 := by
  rw [firstSelected_iff]
  change (∃ y : Coord, chart t y = chart t x ∧ y.1 = y.2.2) ↔ _
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy := chart_injective t ht0 ht1 htm hy
    subst y
    exact heq
  · intro h
    exact ⟨x, rfl, h⟩

theorem secondSelected_left (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    KempeSwap104.Selected (round1 t) 1 (1 + t) (secondComponents t) (vertex t (x, false))
      ↔ ∃ u : ZMod 3, x = HaarWitness.mark u := by
  rw [secondSelected_iff t ht1 htm]
  change (∃ u : ZMod 3, chart t (HaarWitness.mark u) = chart t x) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (chart_injective t ht0 ht1 htm hu).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

theorem secondSelected_right (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (x : Coord) :
    KempeSwap104.Selected (round1 t) 1 (1 + t) (secondComponents t) (vertex t (x, true))
      ↔ ∃ u : ZMod 3, x = HaarWitness.matchA (HaarWitness.mark u) := by
  rw [secondSelected_iff t ht1 htm]
  change (∃ u : ZMod 3, chart t (HaarWitness.matchA (HaarWitness.mark u)) = chart t x) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (chart_injective t ht0 ht1 htm hu).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

#print axioms vertex_injective
#print axioms firstSet_edge_closed
#print axioms firstSelected_iff
#print axioms round1_full
#print axioms secondSet_canonical_edge_closed
#print axioms round1_AC_unchanged
#print axioms secondSet_edge_closed
#print axioms secondSelected_iff
#print axioms round2_full
#print axioms firstSelected_vertex
#print axioms secondSelected_left
#print axioms secondSelected_right

end RobertPublishable.TWO
