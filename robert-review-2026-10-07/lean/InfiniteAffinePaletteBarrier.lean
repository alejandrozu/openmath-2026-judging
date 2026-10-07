/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
-/
import AffinePaletteBarrier
import HaarInfinite

/-! # Sidon-palette recolouring without a finite ambient-module assumption

Finite cycle supports and a finite palette suffice. The cycle partner is
transferred into the induced colour component by proving every one of its
actual edges belongs there; no transfer premise or pair exclusion is assumed.
-/
noncomputable section
namespace OpenMathReview.InfiniteAffinePaletteBarrier
open SimpleGraph Finset Erdos585 KempeSwap104
open OpenMathReview.AffinePaletteBarrier
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [DecidableEq V]

theorem no_partner_in_component (S T : Finset V) (hcap : TripleClosed S)
    (hTS : T ⊆ S) (hne : T.Nonempty) (hc : T.card ≤ 3)
    {u : V × Bool} (p : (Haar.graph T).Walk u u) (hp : p.IsCycle) :
    ¬ ∃ (w : V × Bool) (q : (Haar.graph S).Walk w w), q.IsCycle ∧
      (p.mapLe (Haar.graph_mono hTS)).support.toFinset = q.support.toFinset ∧
      Disjoint (p.mapLe (Haar.graph_mono hTS)).edges.toFinset q.edges.toFinset := by
  rintro ⟨w,q,hq,hS,hE⟩
  have hqs : ∀ x ∈ q.support, x ∈ p.support := by
    intro x hx
    rw [← List.mem_toFinset, ← hS, Walk.support_mapLe_eq_support, List.mem_toFinset] at hx
    exact hx
  have hedges : ∀ e ∈ q.edges, e ∈ (Haar.graph T).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with | _ x y => ?_
    have hx : x ∈ p.support := hqs x (q.fst_mem_support_of_mem_edges he)
    have hy : y ∈ p.support := hqs y (q.snd_mem_support_of_mem_edges he)
    have hr : (Haar.graph T).Reachable x y :=
      (show (Haar.graph T).Reachable u x from ⟨p.takeUntil x hx⟩).symm.trans
        (show (Haar.graph T).Reachable u y from ⟨p.takeUntil y hy⟩)
    exact (Haar.graph T).mem_edgeSet.mpr
      (component_induced S T hcap hTS hne hc hr (q.adj_of_mem_edges he))
  let qT := q.transfer (Haar.graph T) hedges
  have hqT : qT.IsCycle := hq.transfer hedges
  have hsT : p.support.toFinset = qT.support.toFinset := by
    simpa only [qT,Walk.support_transfer,Walk.support_mapLe_eq_support] using hS
  have heT : Disjoint p.edges.toFinset qT.edges.toFinset := by
    simpa only [qT,Walk.edges_transfer,Walk.edges_mapLe_eq_edges] using hE
  have hpair : HasPairF (Haar.graph T) := ⟨u,w,p,qT,hp,hqT,hsT,heT⟩
  have hfour := OpenMathReview.HaarInfinite.four_le_card_of_pair T
    ((hasPairF_iff _).mp hpair)
  omega

/-- Every finite Sidon palette gives the actual one-round obstruction, even in
an infinite characteristic-three module; this asserts no infinite Hamilton cycle. -/
theorem sidon_exposed_cycle_no_partner (S : Finset V) (hs : Sidon S)
    (a b : Color S) (J : Set (twoFactor (canonical S) a b).ConnectedComponent)
    (i j : Color S) {u : V × Bool}
    (p : (twoFactor (swap (canonical S) a b J) i j).Walk u u) (hp : p.IsCycle) :
    ¬ ∃ (w : V × Bool) (q : (Haar.graph S).Walk w w), q.IsCycle ∧
      (p.mapLe (twoFactor_le (swap (canonical S) a b J) i j)).support.toFinset =
        q.support.toFinset ∧
      Disjoint (p.mapLe (twoFactor_le (swap (canonical S) a b J) i j)).edges.toFinset
        q.edges.toFinset := by
  obtain ⟨T,hT,hcard,hfactor⟩ := swap_factor_palette (canonical S) a b J i j
  rw [canonical_colorSubgraph] at hfactor
  have hne : (palette S T).Nonempty := by
    obtain ⟨c,hc⟩ := hT
    exact ⟨c.val,mem_image.mpr ⟨c,hc,rfl⟩⟩
  have hc : (palette S T).card ≤ 3 := by rwa [palette_card]
  have hh := no_partner_in_component S (palette S T) (tripleClosed_of_sidon S hs)
    (palette_subset S T) hne hc (p.mapLe hfactor) (hp.mapLe hfactor)
  simpa only [Walk.support_mapLe_eq_support,Walk.edges_mapLe_eq_edges] using hh

#print axioms no_partner_in_component
#print axioms sidon_exposed_cycle_no_partner
#check @sidon_exposed_cycle_no_partner
end OpenMathReview.InfiniteAffinePaletteBarrier
