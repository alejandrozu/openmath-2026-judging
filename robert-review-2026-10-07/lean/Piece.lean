import MultigraphCut
import Mathlib.Tactic.FinCases

/-! # The pair-free four-cycle piece of L6b

The edge multiplicities are 3,3,3,1 around a,b,c,d. Every genuinely connected
two-regular subgraph with all four vertices needs the single da edge. Smaller
common supports cannot carry four edge-disjoint incidences at each vertex.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

def piece : LooplessMultigraph (Fin 4) (Fin 10) where
  ends e := if e.val < 3 then s(0,1) else if e.val < 6 then s(1,2)
    else if e.val < 9 then s(2,3) else s(3,0)
  loopless := by decide

def ab : Finset (Fin 10) := {0,1,2}
def bc : Finset (Fin 10) := {3,4,5}
def cd : Finset (Fin 10) := {6,7,8}
def closing : Finset (Fin 10) := {9}
def halfColor (u : Fin 4) : Bool := decide (u = 0 ∨ u = 1)
def starAt (u : Fin 4) : Finset (Fin 10) := univ.filter (fun e => u ∈ piece.ends e)

lemma star0 : starAt 0 = ab ∪ closing := by decide
lemma star1 : starAt 1 = ab ∪ bc := by decide
lemma star3 : starAt 3 = cd ∪ closing := by decide
lemma star0_card : (starAt 0).card = 4 := by decide
lemma star3_card : (starAt 3).card = 4 := by decide

lemma degree_as_star (F : Finset (Fin 10)) (u : Fin 4) :
    piece.degree F u = (F ∩ starAt u).card := by
  change (F.filter (fun e => u ∈ piece.ends e)).card = _
  congr 1
  ext e
  simp [LooplessMultigraph.degree, starAt]

lemma inter_union_count (F A B : Finset (Fin 10)) (hd : Disjoint A B) :
    (F ∩ (A ∪ B)).card = (F ∩ A).card + (F ∩ B).card := by
  rw [inter_union_distrib_left,
    card_union_of_disjoint (hd.mono inter_subset_right inter_subset_right)]

lemma degree0 (F : Finset (Fin 10)) :
    piece.degree F 0 = (F ∩ ab).card + (if (9:Fin 10) ∈ F then 1 else 0) := by
  rw [degree_as_star, star0, inter_union_count F ab closing (by decide)]
  by_cases h : (9:Fin 10) ∈ F <;> simp [closing,h]

lemma degree1 (F : Finset (Fin 10)) :
    piece.degree F 1 = (F ∩ ab).card + (F ∩ bc).card := by
  rw [degree_as_star, star1, inter_union_count F ab bc (by decide)]

lemma boundary_half (F : Finset (Fin 10)) :
    (piece.boundary F halfColor).card = (F ∩ bc).card +
      (if (9:Fin 10) ∈ F then 1 else 0) := by
  have hb : ∀ e, Crosses halfColor true (piece.ends e) ↔ e ∈ bc ∪ closing := by
    intro e
    fin_cases e <;> simp [piece, halfColor, bc, closing]
  have hf : piece.boundary F halfColor = F ∩ (bc ∪ closing) := by
    ext e
    simp [LooplessMultigraph.boundary,hb]
  rw [hf, inter_union_count F bc closing (by decide)]
  by_cases h : (9:Fin 10) ∈ F <;> simp [closing,h]

lemma force_star (S : Finset (Fin 4)) (F H : Finset (Fin 10))
    (hF : piece.IsCycleOn S F) (hH : piece.IsCycleOn S H) (hd : Disjoint F H)
    (u : Fin 4) (hu : u ∈ S) (hs : (starAt u).card = 4) : starAt u ⊆ F ∪ H := by
  classical
  have hdf : (F ∩ starAt u).card = 2 := by
    rw [← degree_as_star, hF.degree_eq]
    simp [hu]
  have hdh : (H ∩ starAt u).card = 2 := by
    rw [← degree_as_star, hH.degree_eq]
    simp [hu]
  have hdis : Disjoint (F ∩ starAt u) (H ∩ starAt u) :=
    hd.mono inter_subset_left inter_subset_left
  have hc : ((F ∩ starAt u) ∪ (H ∩ starAt u)).card = 4 := by
    rw [card_union_of_disjoint hdis,hdf,hdh]
  have he : (F ∩ starAt u) ∪ (H ∩ starAt u) = starAt u :=
    eq_of_subset_of_card_le (union_subset inter_subset_right inter_subset_right)
      (by rw [hc,hs])
  intro e he'
  have hx := he.symm ▸ he'
  rcases mem_union.mp hx with hx | hx
  · exact mem_union.mpr (Or.inl (mem_inter.mp hx).1)
  · exact mem_union.mpr (Or.inr (mem_inter.mp hx).1)

lemma needs_closing (S : Finset (Fin 4)) (F : Finset (Fin 10))
    (h : piece.IsCycleOn S F) (h0 : (0:Fin 4) ∈ S) (h1 : (1:Fin 4) ∈ S)
    (h2 : (2:Fin 4) ∈ S) : (9:Fin 10) ∈ F := by
  by_contra hn
  have hd0 := h.degree_eq 0
  have hd1 := h.degree_eq 1
  rw [degree0] at hd0
  rw [degree1] at hd1
  simp only [h0,h1,if_true,hn,if_false,add_zero] at hd0 hd1
  have hb := piece.two_le_boundary_of_distinct_colors S F h halfColor h0 h2 (by decide)
  rw [boundary_half] at hb
  simp only [hn,if_false,add_zero] at hb
  omega

theorem piece_pairfree : ¬ piece.HasPair := by
  classical
  rintro ⟨S,F,H,hF,hH,hd⟩
  have hmem (e : Fin 10) (he : e ∈ F ∪ H) (u : Fin 4) (hu : u ∈ piece.ends e) : u ∈ S := by
    rcases mem_union.mp he with he | he
    · exact LooplessMultigraph.IsCycleOn.mem_support_of_incident piece hF he hu
    · exact LooplessMultigraph.IsCycleOn.mem_support_of_incident piece hH he hu
  have h0 : (0:Fin 4) ∈ S := by
    by_contra hn0
    have hn3 : (3:Fin 4) ∉ S := by
      intro h3
      have hs := force_star S F H hF hH hd 3 h3 star3_card
      exact hn0 (hmem 9 (hs (by decide)) 0 (by decide))
    have hsub (J : Finset (Fin 10)) (hJ : piece.IsCycleOn S J) : J ⊆ bc := by
      intro e he
      have hx : ∀ u ∈ piece.ends e, u ≠ (0:Fin 4) ∧ u ≠ (3:Fin 4) := by
        intro u hu
        have huS := LooplessMultigraph.IsCycleOn.mem_support_of_incident piece hJ he hu
        exact ⟨fun h => hn0 (h ▸ huS), fun h => hn3 (h ▸ huS)⟩
      have hc : ∀ e, (∀ u ∈ piece.ends e, u ≠ (0:Fin 4) ∧ u ≠ (3:Fin 4)) → e ∈ bc := by decide
      exact hc e hx
    obtain ⟨u,hu⟩ := hF.nonempty
    have huc : u = (1:Fin 4) ∨ u = (2:Fin 4) := by
      have hu0 : u ≠ (0:Fin 4) := fun h => hn0 (h ▸ hu)
      have hu3 : u ≠ (3:Fin 4) := fun h => hn3 (h ▸ hu)
      have hx : ∀ u : Fin 4, u ≠ 0 → u ≠ 3 → u = 1 ∨ u = 2 := by decide
      exact hx u hu0 hu3
    have hinc : ∀ e ∈ bc, u ∈ piece.ends e := by
      rcases huc with rfl | rfl <;> decide
    have hcard (J : Finset (Fin 10)) (hJ : piece.IsCycleOn S J) : J.card = 2 := by
      have hf : J.filter (fun e => u ∈ piece.ends e) = J :=
        filter_eq_self.mpr (fun e he => hinc e (hsub J hJ he))
      have hx := hJ.degree_eq u
      simpa [LooplessMultigraph.degree,hf,hu] using hx
    have hh := card_le_card (union_subset (hsub F hF) (hsub H hH))
    rw [card_union_of_disjoint hd,hcard F hF,hcard H hH] at hh
    have hbc : bc.card = 3 := by decide
    omega
  have hs0 := force_star S F H hF hH hd 0 h0 star0_card
  have h1 : (1:Fin 4) ∈ S := hmem 0 (hs0 (by decide)) 1 (by decide)
  have h3 : (3:Fin 4) ∈ S := hmem 9 (hs0 (by decide)) 3 (by decide)
  have hs3 := force_star S F H hF hH hd 3 h3 star3_card
  have h2 : (2:Fin 4) ∈ S := hmem 6 (hs3 (by decide)) 2 (by decide)
  exact disjoint_left.mp hd (needs_closing S F hF h0 h1 h2)
    (needs_closing S H hH h0 h1 h2)

#print axioms piece_pairfree
end RobertPublishable.SUB
