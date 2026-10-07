import Openmath.Proofs.KempeSwap104

/-!
# Actual component-union selectors for the two-round construction

These are graph-semantic interfaces, using the original `KempeSwap104.swap`.
For the final parabola result, closure of the two concrete selected sets must
still be proved; it is not supplied by an assertion about a small subgraph.
-/

namespace RobertPublishable.TWO

open SimpleGraph Erdos585

variable {V C : Type*} {G : SimpleGraph V}

def componentsInside (H : SimpleGraph V) (U : Set V) : Set H.ConnectedComponent :=
  {D | D.supp ⊆ U}

theorem mem_of_reachable_of_edge_closed (H : SimpleGraph V) (U : Set V)
    (hclosed : ∀ ⦃u v⦄, u ∈ U → H.Adj u v → v ∈ U)
    {u v : V} (hu : u ∈ U) (hr : H.Reachable u v) : v ∈ U := by
  rw [reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact hu
  | @tail y z _ hyz ih => exact hclosed ih hyz

/-- A closed set is selected by a set of complete, global components. -/
theorem selected_iff_of_edge_closed (φ : G.EdgeLabeling C) (a b : C) (U : Set V)
    (hclosed : ∀ ⦃u v⦄, u ∈ U → (KempeSwap104.twoFactor φ a b).Adj u v → v ∈ U)
    (v : V) :
    KempeSwap104.Selected φ a b (componentsInside (KempeSwap104.twoFactor φ a b) U) v
      ↔ v ∈ U := by
  change ((KempeSwap104.twoFactor φ a b).connectedComponentMk v).supp ⊆ U ↔ v ∈ U
  constructor
  · intro h
    exact h (ConnectedComponent.connectedComponentMk_mem (v := v))
  · intro hv w hw
    have hr : (KempeSwap104.twoFactor φ a b).Reachable v w :=
      ((KempeSwap104.twoFactor φ a b).connectedComponentMk v).reachable_of_mem_supp
        (ConnectedComponent.connectedComponentMk_mem (v := v)) hw
    exact mem_of_reachable_of_edge_closed _ U hclosed hv hr

/-- Neither global component choice nor extra colours affect an untouched label. -/
theorem swap_labelGraph_of_other [DecidableEq C] (φ : G.EdgeLabeling C)
    (a b c : C) (J : Set (KempeSwap104.twoFactor φ a b).ConnectedComponent)
    (hca : c ≠ a) (hcb : c ≠ b) :
    (KempeSwap104.swap φ a b J).labelGraph c = φ.labelGraph c := by
  classical
  ext u v
  by_cases hu : KempeSwap104.Selected φ a b J u
  · rw [KempeSwap104.swap_labelGraph_adj_selected φ a b J hu]
    rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
  · exact KempeSwap104.swap_labelGraph_adj_not_selected φ a b J hu v c

theorem swap_twoFactor_of_other [DecidableEq C] (φ : G.EdgeLabeling C)
    (a b c d : C) (J : Set (KempeSwap104.twoFactor φ a b).ConnectedComponent)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    KempeSwap104.twoFactor (KempeSwap104.swap φ a b J) c d =
      KempeSwap104.twoFactor φ c d := by
  rw [KempeSwap104.twoFactor, KempeSwap104.twoFactor,
    swap_labelGraph_of_other φ a b c J hca hcb,
    swap_labelGraph_of_other φ a b d J hda hdb]

theorem two_actual_swaps_full [DecidableEq C] (φ : G.EdgeLabeling C)
    (hφ : KempeSwap104.FullColoring φ) (a b c d : C)
    (J₁ : Set (KempeSwap104.twoFactor φ a b).ConnectedComponent)
    (J₂ : Set (KempeSwap104.twoFactor (KempeSwap104.swap φ a b J₁) c d).ConnectedComponent) :
    KempeSwap104.FullColoring (KempeSwap104.swap (KempeSwap104.swap φ a b J₁) c d J₂) :=
  KempeSwap104.swap_fullColoring _
    (KempeSwap104.swap_fullColoring φ hφ a b J₁) c d J₂

#print axioms mem_of_reachable_of_edge_closed
#print axioms selected_iff_of_edge_closed
#print axioms swap_labelGraph_of_other
#print axioms swap_twoFactor_of_other
#print axioms two_actual_swaps_full

end RobertPublishable.TWO
