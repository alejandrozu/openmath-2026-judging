import Projection
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Small cuts for labelled loopless multigraph cycles

This supplements the exact connected two-regular cycle convention with a finite
handshake proof. It is used for the explicit six-regular skeleton of B6.
-/
open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB
namespace LooplessMultigraph
variable {U E : Type*} [DecidableEq U] [DecidableEq E] [Fintype U]
  (L : LooplessMultigraph U E)

lemma IsCycleOn.mem_support_of_incident {S : Finset U} {F : Finset E}
    (h : L.IsCycleOn S F) {e : E} (he : e ∈ F) {u : U} (hu : u ∈ L.ends e) : u ∈ S := by
  by_contra hn
  have hd := h.degree_eq u
  have hpos : 0 < L.degree F u :=
    Finset.card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hu⟩⟩
  simp [hn] at hd
  omega

lemma degree_weight_sum (F : Finset E) (w : U → ℤ) :
    ∑ u, (L.degree F u : ℤ) * w u =
      ∑ e ∈ F, Erdos585.BipartiteBalance.edgeWeight w (L.ends e) := by
  classical
  have hlocal (u : U) : (L.degree F u : ℤ) * w u =
      ∑ e ∈ F, if u ∈ L.ends e then w u else 0 := by
    simp [degree, ← Finset.sum_filter]
  simp_rw [hlocal]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e he
  have hne := L.loopless e
  generalize hz : L.ends e = z at *
  induction z using Sym2.inductionOn with | _ a b => ?_
  have hab : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hne
  simp only [Sym2.mem_iff, Erdos585.BipartiteBalance.edgeWeight_mk]
  have hdis : Disjoint ({a} : Finset U) {b} := by simp [hab]
  have hf : univ.filter (fun u => u = a ∨ u = b) = {a,b} := by ext; simp
  rw [← Finset.sum_filter, hf]
  simp [hab]

noncomputable def boundary (F : Finset E) (color : U → Bool) : Finset E :=
  F.filter (fun e => Crosses color true (L.ends e))

noncomputable def inner (F : Finset E) (color : U → Bool) : Finset E :=
  F.filter (fun e => ∀ u ∈ L.ends e, color u = true)

lemma edge_indicator (color : U → Bool) (z : Sym2 U) :
    Erdos585.BipartiteBalance.edgeWeight (fun u => if color u then (1:ℤ) else 0) z =
      (if Crosses color true z then 1 else 0) +
      2 * (if (∀ u ∈ z, color u = true) then 1 else 0) := by
  induction z using Sym2.inductionOn with | _ a b => ?_
  simp only [Erdos585.BipartiteBalance.edgeWeight_mk, crosses_mk]
  have hforall : (∀ u ∈ s(a,b), color u = true) ↔ color a = true ∧ color b = true := by
    constructor
    · intro h; exact ⟨h a (by simp), h b (by simp)⟩
    · rintro ⟨ha,hb⟩ u hu
      simp only [Sym2.mem_iff] at hu
      rcases hu with rfl | rfl <;> assumption
  simp only [hforall]
  cases ha : color a <;> cases hb : color b <;> simp

lemma cycle_boundary_even (S : Finset U) (F : Finset E) (h : L.IsCycleOn S F)
    (color : U → Bool) : Even (L.boundary F color).card := by
  classical
  have hd := L.degree_weight_sum F (fun u => if color u then (1:ℤ) else 0)
  have hleft : ∑ u, (L.degree F u : ℤ) * (if color u then 1 else 0) =
      2 * ((S.filter fun u => color u = true).card : ℤ) := by
    simp_rw [h.degree_eq]
    simp [Finset.sum_ite, Finset.sum_filter, Finset.sum_const, mul_comm]
  have hright : ∑ e ∈ F, Erdos585.BipartiteBalance.edgeWeight
      (fun u => if color u then (1:ℤ) else 0) (L.ends e) =
      (L.boundary F color).card + 2 * ((L.inner F color).card : ℤ) := by
    simp_rw [edge_indicator]
    rw [sum_add_distrib, ← mul_sum]
    simp [boundary, inner, Finset.sum_ite]
  rw [hleft, hright] at hd
  apply even_iff_two_dvd.mpr
  exact (Int.natCast_dvd_natCast.mp (by omega : (2:ℤ) ∣ ((L.boundary F color).card : ℤ)))

lemma exists_boundary_of_distinct_colors (S : Finset U) (F : Finset E)
    (h : L.IsCycleOn S F) (color : U → Bool)
    {u v : U} (hu : u ∈ S) (hv : v ∈ S) (hc : color u ≠ color v) :
    (L.boundary F color).Nonempty := by
  classical
  obtain ⟨p⟩ := h.connected u hu v hv
  let cut : Finset (Sym2 U) := (L.boundary F color).image L.ends
  have hcut : ∀ a b, (L.supportGraph F).Adj a b → color a ≠ color b → s(a,b) ∈ cut := by
    intro a b hab hcol
    have he : s(a,b) ∈ F.image L.ends := hab.1
    obtain ⟨e, heF, he⟩ := mem_image.mp he
    apply mem_image.mpr
    refine ⟨e, mem_filter.mpr ⟨heF, ?_⟩, he⟩
    rw [he, crosses_mk]
    cases ha : color a <;> cases hb : color b <;> simp_all
  obtain ⟨z, hz, hzc⟩ := Erdos585.exists_cut_edge_of_walk color cut hcut p hc
  obtain ⟨e, he, hez⟩ := mem_image.mp hzc
  exact ⟨e, he⟩

lemma two_le_boundary_of_distinct_colors (S : Finset U) (F : Finset E)
    (h : L.IsCycleOn S F) (color : U → Bool)
    {u v : U} (hu : u ∈ S) (hv : v ∈ S) (hc : color u ≠ color v) :
    2 ≤ (L.boundary F color).card := by
  have hn := (L.exists_boundary_of_distinct_colors S F h color hu hv hc).card_pos
  have he := L.cycle_boundary_even S F h color
  obtain ⟨n, hn'⟩ := he
  omega

/-- A pair cannot cross a cut containing at most three labelled edges. -/
theorem pair_constant_of_small_cut_on (S : Finset U) (F H : Finset E)
    (hF : L.IsCycleOn S F) (hH : L.IsCycleOn S H) (hd : Disjoint F H)
    (color : U → Bool) (cut : Finset E)
    (hcut : ∀ e ∈ F ∪ H, Crosses color true (L.ends e) → e ∈ cut)
    (hsize : cut.card ≤ 3) {u v : U} (hu : u ∈ S) (hv : v ∈ S) :
    color u = color v := by
  classical
  by_contra hne
  have hnF := L.two_le_boundary_of_distinct_colors S F hF color hu hv hne
  have hnH := L.two_le_boundary_of_distinct_colors S H hH color hu hv hne
  have hsub : L.boundary F color ∪ L.boundary H color ⊆ cut := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hcut e (mem_union.mpr (Or.inl (mem_filter.mp he).1)) (mem_filter.mp he).2
    · exact hcut e (mem_union.mpr (Or.inr (mem_filter.mp he).1)) (mem_filter.mp he).2
  have hdis : Disjoint (L.boundary F color) (L.boundary H color) :=
    hd.mono (filter_subset _ _) (filter_subset _ _)
  have hn := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hn
  omega

theorem pair_constant_of_small_cut (S : Finset U) (F H : Finset E)
    (hF : L.IsCycleOn S F) (hH : L.IsCycleOn S H) (hd : Disjoint F H)
    (color : U → Bool) (cut : Finset E)
    (hcut : ∀ e, Crosses color true (L.ends e) → e ∈ cut)
    (hsize : cut.card ≤ 3) {u v : U} (hu : u ∈ S) (hv : v ∈ S) :
    color u = color v :=
  L.pair_constant_of_small_cut_on S F H hF hH hd color cut
    (fun e _ hc => hcut e hc) hsize hu hv

end LooplessMultigraph
end RobertPublishable.SUB
