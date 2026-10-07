import MultigraphCut
import Mathlib.Tactic.FinCases

/-! # The four-vertex skeleton K in PROOF-R1

There are three individually labelled edges 03 and three 12, then single 02
and 13. The proof excludes every connected two-regular pair, not only Hamilton
cycles; the two parallel-edge cycles are also covered.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

def skeletonK : LooplessMultigraph (Fin 4) (Fin 8) where
  ends e := if e.val < 3 then s(0,3) else if e.val < 6 then s(1,2)
    else if e.val = 6 then s(0,2) else s(1,3)
  loopless := by decide

def kColor (u : Fin 4) : Bool := decide (u = 0 ∨ u = 3)
def kCut : Finset (Fin 8) := {6,7}
def kBundle (c : Bool) : Finset (Fin 8) := if c then {0,1,2} else {3,4,5}

lemma k_cut_contains (e : Fin 8) : Crosses kColor true (skeletonK.ends e) → e ∈ kCut := by
  fin_cases e <;> simp [skeletonK,kColor,kCut]

lemma k_bundle_of_constant (c : Bool) (e : Fin 8)
    (h : ∀ u ∈ skeletonK.ends e, kColor u = c) : e ∈ kBundle c := by
  have hc : ∀ c e, (∀ u ∈ skeletonK.ends e, kColor u = c) → e ∈ kBundle c := by decide
  exact hc c e h

lemma k_incident_of_bundle (c : Bool) (u : Fin 4) (e : Fin 8)
    (hu : kColor u = c) (he : e ∈ kBundle c) : u ∈ skeletonK.ends e := by
  have hc : ∀ c u e, kColor u = c → e ∈ kBundle c → u ∈ skeletonK.ends e := by decide
  exact hc c u e hu he

lemma k_bundle_card (c : Bool) : (kBundle c).card = 3 := by cases c <;> decide

theorem skeletonK_pairfree : ¬ skeletonK.HasPair := by
  classical
  rintro ⟨S,F,H,hF,hH,hdis⟩
  obtain ⟨u,hu⟩ := hF.nonempty
  have hconst : ∀ v ∈ S, kColor v = kColor u := by
    intro v hv
    exact (skeletonK.pair_constant_of_small_cut S F H hF hH hdis kColor kCut
      k_cut_contains (by decide) hu hv).symm
  have hsubF : F ⊆ kBundle (kColor u) := by
    intro e he
    apply k_bundle_of_constant
    intro v hv
    exact hconst v (LooplessMultigraph.IsCycleOn.mem_support_of_incident skeletonK hF he hv)
  have hsubH : H ⊆ kBundle (kColor u) := by
    intro e he
    apply k_bundle_of_constant
    intro v hv
    exact hconst v (LooplessMultigraph.IsCycleOn.mem_support_of_incident skeletonK hH he hv)
  have hcardF : F.card = 2 := by
    have hd := hF.degree_eq u
    have hf : F.filter (fun e => u ∈ skeletonK.ends e) = F := by
      apply filter_eq_self.mpr
      intro e he
      exact k_incident_of_bundle _ u e rfl (hsubF he)
    simpa [LooplessMultigraph.degree, hu, hf] using hd
  have hcardH : H.card = 2 := by
    have hd := hH.degree_eq u
    have hf : H.filter (fun e => u ∈ skeletonK.ends e) = H := by
      apply filter_eq_self.mpr
      intro e he
      exact k_incident_of_bundle _ u e rfl (hsubH he)
    simpa [LooplessMultigraph.degree, hu, hf] using hd
  have hn := card_le_card (union_subset hsubF hsubH)
  rw [card_union_of_disjoint hdis, hcardF, hcardH, k_bundle_card] at hn
  omega

#print axioms skeletonK_pairfree
end RobertPublishable.SUB
