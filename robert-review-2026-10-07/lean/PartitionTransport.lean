import LemmaF

/-! # Same-vertex transport from a balanced bipartition

The shore labelling is only a graph isomorphism, not a factor or a cut
criterion. The resulting spanning factor lives on the given vertex type V.
-/
open Finset SimpleGraph
open scoped Classical BigOperators
namespace RobertPublishable.Factor

theorem cutCount_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (S : Finset V) :
    cutCount H (S.map f.toEquiv.toEmbedding) = cutCount G S := by
  have hv : ∀ v, (((S.map f.toEquiv.toEmbedding)ᶜ).filter (H.Adj (f v))).card =
      (Sᶜ.filter (G.Adj v)).card := by
    intro v
    have he : ((S.map f.toEquiv.toEmbedding)ᶜ).filter (H.Adj (f v)) =
        (Sᶜ.filter (G.Adj v)).map f.toEquiv.toEmbedding := by
      ext w
      obtain ⟨u,rfl⟩ := f.surjective w
      constructor
      · intro hh
        obtain ⟨hs,ha⟩ := mem_filter.mp hh
        apply mem_map.mpr
        refine ⟨u,mem_filter.mpr ⟨?_,f.map_adj_iff.mp ha⟩,rfl⟩
        apply mem_compl.mpr
        intro hu
        exact (mem_compl.mp hs) (mem_map.mpr ⟨u,hu,rfl⟩)
      · intro hh
        obtain ⟨z,hz,hzu⟩ := mem_map.mp hh
        have hzu' : z = u := f.injective hzu
        subst z
        obtain ⟨hs,ha⟩ := mem_filter.mp hz
        apply mem_filter.mpr
        refine ⟨mem_compl.mpr ?_,f.map_adj_iff.mpr ha⟩
        intro hu
        obtain ⟨z,hz,hzu⟩ := mem_map.mp hu
        have hzu' : z = u := f.injective hzu
        subst z
        exact (mem_compl.mp hs) hz
    rw [he,card_map]
  unfold cutCount
  rw [sum_map]
  exact sum_congr rfl (fun v _ => hv v)

variable {P Q V : Type*} [DecidableEq P] [DecidableEq Q] [DecidableEq V]
  [Fintype P] [Fintype Q] [Fintype V]

set_option maxHeartbeats 0 in
/-- The full factor conclusion on an arbitrary labelled host with an explicit
balanced bipartition. Cut sizes are expressed as 2|Z|≤|V|. -/
theorem lemma_F_of_balanced_partition (r : P → Q → Prop) [Nonempty P]
    (H : SimpleGraph V) (e : (P ⊕ Q) ≃ V)
    (hpart : ∀ a b, H.Adj (e a) (e b) ↔ (bipGraph r).Adj a b)
    (η γ d : ℝ) (hbalance : Fintype.card P = Fintype.card Q)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη : η ≤ γ^2/8) (hd : 16/γ^2 ≤ d)
    (hdeg : ∀ v, (1-η)*d ≤ (H.degree v : ℝ) ∧ (H.degree v : ℝ) ≤ d)
    (hexp : ∀ Z : Finset V, Z.Nonempty → 2*Z.card ≤ Fintype.card V →
      γ*d*(Z.card : ℝ) ≤ (cutCount H Z : ℝ)) :
    ∃ F : SimpleGraph V, F ≤ H ∧ F.IsRegularOfDegree (roundedDegree η γ d) ∧
      (1-3*γ/8)*d-1 ≤ (roundedDegree η γ d : ℝ) ∧
      ∀ Z : Finset V, 2*Z.card ≤ Fintype.card V →
        (γ/2)*(roundedDegree η γ d : ℝ)*(Z.card : ℝ) ≤ (cutCount F Z : ℝ) := by
  let f : bipGraph r ≃g H := { toEquiv := e, map_rel_iff' := fun {a b} => hpart a b }
  have hcard : Fintype.card V = 2*Fintype.card P := by
    have hh := Fintype.card_congr e
    rw [Fintype.card_sum,hbalance] at hh
    omega
  have hdeg' : ∀ v, (1-η)*d ≤ ((bipGraph r).degree v : ℝ) ∧
      ((bipGraph r).degree v : ℝ) ≤ d := by
    intro v
    rw [← f.degree_eq v]
    exact hdeg (f v)
  have hexp' : ∀ Z : Finset (P ⊕ Q), Z.Nonempty → Z.card ≤ Fintype.card P →
      γ*d*(Z.card : ℝ) ≤ (cutCount (bipGraph r) Z : ℝ) := by
    intro Z hne hZ
    have hh := hexp (Z.map e.toEmbedding) hne.map (by rw [card_map,hcard]; omega)
    have hcut : cutCount H (Z.map e.toEmbedding) = cutCount (bipGraph r) Z := by
      simpa only [f] using cutCount_iso f Z
    rw [card_map,hcut] at hh
    exact hh
  obtain ⟨F,hFH,hreg,hk,he⟩ := lemma_F r η γ d hbalance hγ0 hγ1 hη hd hdeg' hexp'
  let fF : F.comap e.symm ≃g F := { toEquiv := e.symm, map_rel_iff' := Iff.rfl }
  refine ⟨F.comap e.symm,?_,?_,hk,?_⟩
  · intro a b hab
    have hh := (hpart (e.symm a) (e.symm b)).mpr (hFH hab)
    simpa only [e.apply_symm_apply] using hh
  · intro v
    have hh : F.degree (e.symm v) = (F.comap e.symm).degree v := fF.degree_eq v
    exact hh.symm.trans (hreg.degree_eq (e.symm v))
  · intro Z hZ
    have hc : (Z.map e.symm.toEmbedding).card ≤ Fintype.card P := by
      rw [card_map]
      rw [hcard] at hZ
      omega
    have hh := he (Z.map e.symm.toEmbedding) hc
    have hcut : cutCount F (Z.map e.symm.toEmbedding) = cutCount (F.comap e.symm) Z := by
      exact cutCount_iso fF Z
    rw [card_map,hcut] at hh
    exact hh

#print axioms cutCount_iso
#check @lemma_F_of_balanced_partition
#print axioms lemma_F_of_balanced_partition
end RobertPublishable.Factor
