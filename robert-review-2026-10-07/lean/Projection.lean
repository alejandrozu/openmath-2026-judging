/- Additive formal proof of the link-edge projection in Robert Huynh's R1.
The multigraph cycle convention is exactly: a nonempty connected 2-regular
finite edge-subgraph. Parallel edges are individually labelled, so a cycle on
two vertices is allowed. No pair-free conclusion is an input to the projection.
-/
import Passage
import Mathlib.Data.Finset.Preimage
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

variable {V U E : Type*} [DecidableEq V] [DecidableEq U] [DecidableEq E]

/-- Loopless multigraph; different edge labels may have the same unordered ends. -/
structure LooplessMultigraph (U E : Type*) where
  ends : E → Sym2 U
  loopless : ∀ e, ¬ (ends e).IsDiag

namespace LooplessMultigraph

noncomputable def degree (L : LooplessMultigraph U E) (F : Finset E) (u : U) : ℕ := by
  classical
  exact (F.filter fun e => u ∈ L.ends e).card

def supportGraph (L : LooplessMultigraph U E) (F : Finset E) : SimpleGraph U :=
  fromEdgeSet (↑(F.image L.ends) : Set (Sym2 U))

/-- This is the connected 2-regular multigraph definition used in PROOF-R1.md.
The support and edge set are finite even when the ambient multigraph is infinite. -/
structure IsCycleOn (L : LooplessMultigraph U E) (S : Finset U) (F : Finset E) : Prop where
  nonempty : S.Nonempty
  degree_eq : ∀ u, L.degree F u = if u ∈ S then 2 else 0
  connected : ∀ u ∈ S, ∀ v ∈ S, (L.supportGraph F).Reachable u v

def HasPair (L : LooplessMultigraph U E) : Prop :=
  ∃ S F₁ F₂, L.IsCycleOn S F₁ ∧ L.IsCycleOn S F₂ ∧ Disjoint F₁ F₂

end LooplessMultigraph

/-- Faithful correspondence between individually labelled skeleton edges and all
inter-copy edges of the simple substitution. Injectivity excludes duplicate links. -/
structure LinkProjection (G : SimpleGraph V) (L : LooplessMultigraph U E) (copy : V → U) where
  link : E → Sym2 V
  injective : Function.Injective link
  link_edge : ∀ e, link e ∈ G.edgeSet
  ends_eq : ∀ e, L.ends e = Sym2.map copy (link e)
  complete : ∀ z ∈ G.edgeSet, ¬ (Sym2.map copy z).IsDiag → ∃ e, link e = z

lemma crosses_iff_mem_mapped (copy : V → U) (u : U) (z : Sym2 V)
    (hne : ¬ (Sym2.map copy z).IsDiag) :
    Crosses copy u z ↔ u ∈ Sym2.map copy z := by
  induction z using Sym2.inductionOn with | _ a b => ?_
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hne
  simp only [crosses_mk, Sym2.map_mk, Sym2.mem_iff]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl ha.symm
    · exact Or.inr hb.symm
  · rintro (ha | hb)
    · exact Or.inl ⟨ha.symm, fun hb => hne (ha.symm.trans hb.symm)⟩
    · exact Or.inr ⟨fun ha => hne (ha.trans hb), hb.symm⟩

lemma nonDiag_of_crosses (copy : V → U) (u : U) (z : Sym2 V)
    (h : Crosses copy u z) : ¬ (Sym2.map copy z).IsDiag := by
  induction z using Sym2.inductionOn with | _ a b => ?_
  simp only [crosses_mk, Sym2.map_mk, Sym2.mk_isDiag_iff] at *
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact fun hab => hb (hab.symm.trans ha)
  · exact fun hab => ha (hab.trans hb)

namespace LinkProjection

variable {G : SimpleGraph V} {L : LooplessMultigraph U E} {copy : V → U}
  (P : LinkProjection G L copy)

noncomputable def projectedEdges {a b : V} (p : G.Walk a b) : Finset E :=
  p.edges.toFinset.preimage P.link P.injective.injOn

@[simp] lemma mem_projectedEdges {a b : V} (p : G.Walk a b) (e : E) :
    e ∈ P.projectedEdges p ↔ P.link e ∈ p.edges := by
  simp [projectedEdges]

lemma incident_iff_crosses (u : U) (e : E) :
    u ∈ L.ends e ↔ Crosses copy u (P.link e) := by
  rw [P.ends_eq]
  exact (crosses_iff_mem_mapped copy u (P.link e)
    (by rw [← P.ends_eq]; exact L.loopless e)).symm

lemma incidence_image_eq_boundary {a b : V} (p : G.Walk a b) (u : U) :
    ((P.projectedEdges p).filter (fun e => u ∈ L.ends e)).image P.link =
      p.edges.toFinset.filter (Crosses copy u) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨e, he, rfl⟩ := mem_image.mp hz
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr ((P.mem_projectedEdges p e).mp
      (mem_filter.mp he).1), (P.incident_iff_crosses u e).mp (mem_filter.mp he).2⟩
  · intro hz
    have hzp := (mem_filter.mp hz).1
    have hzc := (mem_filter.mp hz).2
    obtain ⟨e, he⟩ := P.complete z
      (p.edges_subset_edgeSet (List.mem_toFinset.mp hzp))
      (nonDiag_of_crosses copy u z hzc)
    refine mem_image.mpr ⟨e, mem_filter.mpr ⟨?_, ?_⟩, he⟩
    · rw [P.mem_projectedEdges, he]
      exact List.mem_toFinset.mp hzp
    · rw [P.incident_iff_crosses, he]
      exact hzc

lemma projected_degree_eq_boundary {a b : V} (p : G.Walk a b) (u : U) :
    L.degree (P.projectedEdges p) u =
      (p.edges.toFinset.filter (Crosses copy u)).card := by
  classical
  rw [LooplessMultigraph.degree, ← P.incidence_image_eq_boundary]
  exact (card_image_of_injective _ P.injective).symm

lemma projected_disjoint {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (hd : Disjoint p.edges.toFinset q.edges.toFinset) :
    Disjoint (P.projectedEdges p) (P.projectedEdges q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp hd
    (List.mem_toFinset.mpr ((P.mem_projectedEdges p e).mp he))
    (List.mem_toFinset.mpr ((P.mem_projectedEdges q e).mp hf))

lemma quotient_reachable_of_walk {a b : V} (p : G.Walk a b) (F : Finset E)
    (hF : ∀ e ∈ p.edges, ∀ f, P.link f = e → f ∈ F) :
    (L.supportGraph F).Reachable (copy a) (copy b) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have htail : ∀ e ∈ p.edges, ∀ f, P.link f = e → f ∈ F := by
      intro e he f hf
      exact hF e (by simp [he]) f hf
    have hr := ih htail
    by_cases hcopy : copy a = copy b
    · simpa [hcopy] using hr
    · obtain ⟨e, he⟩ := P.complete s(a,b) (G.mem_edgeSet.mpr hab)
        (by simp [Sym2.map_mk, Sym2.mk_isDiag_iff, hcopy])
      have heF : e ∈ F := hF s(a,b) (by simp) e he
      have hadj : (L.supportGraph F).Adj (copy a) (copy b) := by
        change s(copy a, copy b) ∈ (↑(F.image L.ends) : Set (Sym2 U)) ∧ copy a ≠ copy b
        refine ⟨?_, hcopy⟩
        exact mem_image.mpr ⟨e, heF, by rw [P.ends_eq, he]; rfl⟩
      exact hadj.reachable.trans hr

lemma projected_support_connected {a : V} (p : G.Walk a a)
    (u : U) (hu : u ∈ p.support.toFinset.image copy)
    (v : U) (hv : v ∈ p.support.toFinset.image copy) :
    (L.supportGraph (P.projectedEdges p)).Reachable u v := by
  classical
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
  have hx' : x ∈ p.support := List.mem_toFinset.mp hx
  have hy' : y ∈ p.support := List.mem_toFinset.mp hy
  have rx := P.quotient_reachable_of_walk (p.takeUntil x hx') (P.projectedEdges p) ?_
  · have ry := P.quotient_reachable_of_walk (p.takeUntil y hy') (P.projectedEdges p) ?_
    · exact rx.symm.trans ry
    · intro e he f hf
      apply (P.mem_projectedEdges p f).mpr
      rw [hf]
      exact p.edges_takeUntil_subset_edges hy' he
  · intro e he f hf
    apply (P.mem_projectedEdges p f).mpr
    rw [hf]
    exact p.edges_takeUntil_subset_edges hx' he

lemma boundary_empty_outside_support {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (u : U) (hu : u ∉ p.support.toFinset.image copy) :
    p.edges.toFinset.filter (Crosses copy u) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨x, hxe, hxu⟩ := (mem_filter.mp he).2.1
  have hx : x ∈ p.support := (p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mpr
    ⟨e, List.mem_toFinset.mp (mem_filter.mp he).1, hxe⟩
  exact hu (mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, hxu⟩)

theorem projected_cycle {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hpass : ∀ u ∈ p.support.toFinset.image copy,
      (p.edges.toFinset.filter (Crosses copy u)).card = 2) :
    L.IsCycleOn (p.support.toFinset.image copy) (P.projectedEdges p) := by
  classical
  refine ⟨?_, ?_, P.projected_support_connected p⟩
  · exact ⟨copy a, mem_image.mpr ⟨a, List.mem_toFinset.mpr p.start_mem_support, rfl⟩⟩
  · intro u
    rw [P.projected_degree_eq_boundary]
    by_cases hu : u ∈ p.support.toFinset.image copy
    · simp [hu, hpass u hu]
    · simp [hu, boundary_empty_outside_support p hp u hu]

end LinkProjection
end RobertPublishable.SUB
