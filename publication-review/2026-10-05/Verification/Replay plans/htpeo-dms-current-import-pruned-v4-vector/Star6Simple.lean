/-
  Star6Simple.lean — the corollaries of Star6Corollaries.lean for Mathlib's `SimpleGraph`
  (Lean 4.33.1 + Mathlib v4.33.1).  Statements fixed by the lead; proofs to be filled in.
-/
import Star6Corollaries
set_option backward.isDefEq.respectTransparency false

namespace Star6
open RH2Fid

section simple
variable {V : Type} [Fintype V] [DecidableEq V]

/-- the incidence map of a simple graph: the edges are the elements of `G.edgeSet` -/
def edgeEn (G : SimpleGraph V) : G.edgeSet → Sym2 V := fun e => e.1

/-- `c` is a star edge colouring of the simple graph `G`: adjacent edges get different colours and no path or
    cycle with four edges is bicoloured (`RH2Fid.StarP` for the incidence map of `G`) -/
def IsStarEdgeColouring (G : SimpleGraph V) {K : Type} (c : G.edgeSet → K) : Prop := StarP (edgeEn G) c

/-- no edge of `G` is a bridge -/
def Bridgeless (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem edgeEn_loopless : LooplessP (edgeEn G) := by
  intro e
  exact G.not_isDiag_of_mem_edgeSet e.2

private theorem edgeEn_deg (v : V) : RH2Fid.deg (edgeEn G) v = G.degree v := by
  classical
  let f : {e : G.edgeSet // v ∈ e.1} ≃ G.incidenceSet v :=
    { toFun := fun e => ⟨e.1.1, ⟨e.1.2, e.2⟩⟩
      invFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := by intro e; cases e with | mk e h => cases e; rfl
      right_inv := by intro e; cases e with | mk e h => rfl }
  calc
    RH2Fid.deg (edgeEn G) v = Fintype.card {e : G.edgeSet // v ∈ e.1} := by
      rw [RH2Fid.deg, ← Fintype.card_subtype]
      rfl
    _ = Fintype.card (G.incidenceSet v) := Fintype.card_congr f
    _ = G.degree v := G.card_incidenceSet_eq_degree v

private theorem edgeEn_cubic (hreg : G.IsRegularOfDegree 3) : CubicP (edgeEn G) := by
  intro v
  rw [edgeEn_deg]
  exact hreg.degree_eq v

private theorem edgeEn_maxDeg3 (hdeg : ∀ v, G.degree v ≤ 3) : MaxDeg3 (edgeEn G) := by
  intro v
  rw [edgeEn_deg]
  exact hdeg v

private theorem edgeEn_conn_of_reachable {H : SimpleGraph V} (F : G.edgeSet → Prop)
    (hstep : ∀ a b, H.Adj a b → Step (edgeEn G) F a b)
    {u v : V} (h : H.Reachable u v) : Conn (edgeEn G) F u v := by
  apply (H.reachable_iff_reflTransGen u v).1 at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (hstep _ _ hbc)

private theorem edgeEn_connected (hconn : G.Connected) : ConnectedP (edgeEn G) := by
  intro u v
  apply edgeEn_conn_of_reachable G (fun _ => True) (u := u) (v := v)
  · intro a b hab
    exact ⟨⟨s(a, b), G.mem_edgeSet.mpr hab⟩, trivial, rfl⟩
  · exact hconn.preconnected u v

private theorem edgeEn_bridgeless (hbr : Bridgeless G) : BridgelessP (edgeEn G) := by
  intro e
  obtain ⟨u, v, huv⟩ := RH2Fid.sym2_rep e.1
  intro hbridge
  have hnotconn := (RH2Fid.bridge_iff (edgeEn G) e huv).1 hbridge
  apply hnotconn
  have hreach : (G.deleteEdges {s(u, v)}).Reachable u v := by
    by_contra h
    apply hbr e.1 e.2
    rw [huv]
    exact (G.isBridge_iff).2 h
  apply edgeEn_conn_of_reachable G (fun f => f ≠ e) (u := u) (v := v)
    (H := G.deleteEdges {s(u, v)})
  · intro a b hab
    have hab' := (SimpleGraph.deleteEdges_adj).1 hab
    refine ⟨⟨s(a, b), G.mem_edgeSet.mpr hab'.1⟩, ?_, rfl⟩
    intro heq
    have he : s(a, b) = s(u, v) := by
      calc
        s(a, b) = e.1 := congrArg Subtype.val heq
        _ = s(u, v) := huv
    exact hab'.2 (by simpa [he])
  · exact hreach

private def pmSubgraph (N : G.edgeSet → Prop) : G.Subgraph where
  verts := Set.univ
  Adj a b := ∃ e : G.edgeSet, N e ∧ e.1 = s(a, b)
  adj_sub := by
    intro a b h
    obtain ⟨e, _, he⟩ := h
    exact G.mem_edgeSet.mp (he ▸ e.2)
  edge_vert := by intro a b _; exact Set.mem_univ a
  symm.symm := by
    intro a b h
    obtain ⟨e, hN, he⟩ := h
    exact ⟨e, hN, he.trans Sym2.eq_swap⟩

private theorem pmSubgraph_edge_iff (N : G.edgeSet → Prop) (e : G.edgeSet) :
    e.1 ∈ (pmSubgraph G N).edgeSet ↔ N e := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.ind with
  | h a b =>
    change (∃ f : G.edgeSet, N f ∧ f.1 = s(a, b)) ↔ N ⟨s(a, b), hz⟩
    constructor
    · rintro ⟨f, hf, hval⟩
      have : f = ⟨s(a, b), hz⟩ := Subtype.ext hval
      simpa [this] using hf
    · intro h
      exact ⟨⟨s(a, b), hz⟩, h, rfl⟩

private theorem pmSubgraph_isPerfectMatching (N : G.edgeSet → Prop)
    (hpm : IsPM (edgeEn G) N) : (pmSubgraph G N).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨e, he, hv⟩ := hpm.2 v
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
  refine ⟨w, ⟨e, he, hw⟩, ?_⟩
  intro w' hw'
  obtain ⟨f, hf, hfvw⟩ := hw'
  by_cases hef : e = f
  · have hsym : s(v, w) = s(v, w') := by
      calc
        s(v, w) = e.1 := hw.symm
        _ = f.1 := congrArg Subtype.val hef
        _ = s(v, w') := hfvw
    exact Sym2.congr_right.mp hsym.symm
  · have hvf : v ∈ f.1 := by rw [hfvw]; exact Sym2.mem_mk_left v w'
    exact False.elim ((hpm.1 e f he hf hef v hv) hvf)

/-- **Schönberger's theorem** (1934) for Mathlib simple graphs: in a connected bridgeless 3-regular graph every
    edge lies in a perfect matching, and every edge is avoided by a perfect matching. -/
theorem simple_schoenberger (hconn : G.Connected) (hreg : G.IsRegularOfDegree 3) (hbr : Bridgeless G)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet) ∧
    (∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∉ M.edgeSet) := by
  letI : Fintype G.edgeSet := inferInstance
  obtain ⟨⟨N₁, hN₁, he₁⟩, ⟨N₂, hN₂, he₂⟩⟩ :=
    plain_schoenberger V G.edgeSet (edgeEn G) (edgeEn_loopless G)
      (edgeEn_connected G hconn) (edgeEn_bridgeless G hbr) (edgeEn_cubic G hreg) ⟨e, he⟩
  constructor
  · exact ⟨pmSubgraph G N₁, pmSubgraph_isPerfectMatching G N₁ hN₁,
      (pmSubgraph_edge_iff G N₁ ⟨e, he⟩).2 he₁⟩
  · exact ⟨pmSubgraph G N₂, pmSubgraph_isPerfectMatching G N₂ hN₂,
      fun h => he₂ ((pmSubgraph_edge_iff G N₂ ⟨e, he⟩).1 h)⟩

/-- **Petersen's theorem** (1891), connected case: a connected bridgeless 3-regular graph has a perfect matching. -/
theorem simple_petersen_connected (hconn : G.Connected) (hreg : G.IsRegularOfDegree 3) (hbr : Bridgeless G) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  let v : V := Classical.choice hconn.nonempty
  have hv : 0 < G.degree v := by rw [hreg.degree_eq]; decide
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).1 hv
  obtain ⟨M, hM, _⟩ := (simple_schoenberger G hconn hreg hbr (G.mem_edgeSet.mpr hw)).1
  exact ⟨M, hM⟩

/-- **Small-order theorem, simple graphs**: every bridgeless 3-regular simple graph on at most 14 vertices has a star
    edge colouring with 6 colours. -/
theorem simple_star6_cubic_bridgeless_le14 (hreg : G.IsRegularOfDegree 3) (hbr : Bridgeless G)
    (hn : Fintype.card V ≤ 14) : ∃ c : G.edgeSet → Fin 6, IsStarEdgeColouring G c := by
  letI : Fintype G.edgeSet := inferInstance
  exact (star6P_iff (edgeEn G)).1
    (plain_star6_cubic_bridgeless_le14 V G.edgeSet (edgeEn G) (edgeEn_loopless G)
      (edgeEn_bridgeless G hbr) (edgeEn_cubic G hreg) hn)

/-- **Small-order theorem, simple graphs**: every simple graph of maximum degree at most 3 on at most 7 vertices has
    a star edge colouring with 6 colours. -/
theorem simple_star6_subcubic_le7 (hdeg : ∀ v, G.degree v ≤ 3) (hn : Fintype.card V ≤ 7) :
    ∃ c : G.edgeSet → Fin 6, IsStarEdgeColouring G c := by
  letI : Fintype G.edgeSet := inferInstance
  exact (star6P_iff (edgeEn G)).1
    (plain_star6_subcubic_le7 V G.edgeSet (edgeEn G) (edgeEn_loopless G)
      (edgeEn_maxDeg3 G hdeg) hn)

end simple

end Star6

#print axioms Star6.simple_schoenberger
#print axioms Star6.simple_petersen_connected
#print axioms Star6.simple_star6_cubic_bridgeless_le14
#print axioms Star6.simple_star6_subcubic_le7
