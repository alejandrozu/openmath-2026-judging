/-
Copyright (c) 2025 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import IndependentTransversals.MainDefs
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Independent Transversals - Basic Lemmas

This file contains lemmas and auxiliary definitions building on the core definitions
in `MainDefs.lean`.

## Main Results

* Partition API: `pairwiseDisjoint`, `sUnion_eq`, `nonempty_of_mem`
* `blockOf` - The unique block containing a vertex
* `ncard_ge_of_thick` - For a t-thick partition with n blocks, |V| ≥ n * t
* Neighborhood bounds: `ncard_neighborSet_le_maxDegree`, etc.
* `agreeOnBlock` / `agreeOnBlocks` - Agreement of ITs on blocks
* `oplus` - Replacing a vertex in an IT
* IT helper lemmas: `unique_vertex`, `card_eq`, `inter_block_singleton`
-/

open scoped Set

namespace IndependentTransversals

variable {V : Type*} [DecidableEq V]

namespace PartitionedGraph

variable (G : PartitionedGraph V)

/-! ### Partition API -/

/-- Blocks are pairwise disjoint. -/
lemma pairwiseDisjoint : G.blocks.PairwiseDisjoint id :=
  G.isPartition.pairwiseDisjoint

/-- Blocks cover the whole vertex set. -/
lemma sUnion_eq : ⋃₀ G.blocks = Set.univ :=
  G.isPartition.sUnion_eq_univ

/-- Blocks are nonempty. -/
lemma nonempty_of_mem {U : Set V} (hU : U ∈ G.blocks) : U.Nonempty :=
  Setoid.nonempty_of_mem_partition G.isPartition hU

/-- For a t-thick partition with n blocks, |V| ≥ n * t.

Proof: V = ⋃₀ blocks (partition property), and for pairwise disjoint finite sets,
|⋃₀ S| = Σ_{s ∈ S} |s|. Each |s| ≥ t by thickness, so Σ |s| ≥ |S| * t.

This lemma is technical and requires converting between Set.ncard and Finset.card
via Set.ncard_eq_toFinset_card' and using Finset.card_biUnion for disjoint unions. -/
lemma ncard_ge_of_thick [Finite V] (t : ℕ) (h_thick : G.isThick t) :
    G.blocks.ncard * t ≤ (Set.univ : Set V).ncard := by
  rw [← G.sUnion_eq]
  have h_disj := G.pairwiseDisjoint
  have h_blocks_fin : G.blocks.Finite := Set.toFinite G.blocks
  -- Convert sUnion to biUnion: ⋃₀ blocks = ⋃ B ∈ blocks, B
  rw [Set.sUnion_eq_biUnion]
  -- Each block is finite since V is finite
  have h_each_fin : ∀ B ∈ G.blocks, B.Finite := fun B _ => Set.toFinite B
  -- PairwiseDisjoint for the identity function
  have h_disj' : G.blocks.PairwiseDisjoint fun B => B := h_disj
  -- Use equality for pairwise disjoint: |⋃ B ∈ blocks, B| = Σᶠ_{B ∈ blocks} |B|
  rw [Set.Finite.ncard_biUnion h_blocks_fin h_each_fin h_disj']
  -- Now need: |blocks| * t ≤ Σᶠ_{B ∈ blocks} |B|
  -- Use finsum_mem_eq_finite_toFinset_sum to convert finsum to Finset.sum
  rw [finsum_mem_eq_finite_toFinset_sum _ h_blocks_fin]
  rw [Set.ncard_eq_toFinset_card G.blocks h_blocks_fin]
  -- Now: h_blocks_fin.toFinset.card * t ≤ Σ_{B ∈ h_blocks_fin.toFinset} |B|
  -- Use Finset.card_nsmul_le_sum: |s| • n ≤ Σ f when n ≤ f for all elements
  -- For ℕ, smul is multiplication: a • b = a * b
  -- Goal: blocks.ncard * t ≤ sum
  -- After rw [mul_comm]: t * blocks.ncard ≤ sum
  -- Finset.card_nsmul_le_sum gives: s.card • t ≤ s.sum f (i.e., s.card * t)
  -- So we need: s.card * t ≤ sum, which matches after noting * = •
  rw [← smul_eq_mul]
  apply Finset.card_nsmul_le_sum
  intro B hB
  have hB_blocks : B ∈ G.blocks := h_blocks_fin.mem_toFinset.mp hB
  exact h_thick B hB_blocks

variable [Fintype V]

/-- Convenience alias: the maximum degree Δ of the graph.
    This is `SimpleGraph.maxDegree G.graph`. -/
noncomputable def maxDegree [DecidableRel G.graph.Adj] : ℕ :=
  G.graph.maxDegree

section NeighborhoodBounds
/-! ### Neighborhood Bounds -/

variable [DecidableRel G.graph.Adj]

/-- The ncard of a neighborSet equals the degree. -/
lemma ncard_neighborSet_eq_degree (v : V) :
    (G.graph.neighborSet v).ncard = G.graph.degree v := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact SimpleGraph.card_neighborSet_eq_degree G.graph v

/-- The ncard of a neighborSet is at most maxDegree. -/
lemma ncard_neighborSet_le_maxDegree (v : V) :
    (G.graph.neighborSet v).ncard ≤ G.maxDegree := by
  rw [G.ncard_neighborSet_eq_degree]
  exact SimpleGraph.degree_le_maxDegree G.graph v

/-- Any intersection of a neighborSet with another set has ncard at most maxDegree. -/
lemma ncard_inter_neighborSet_le_maxDegree (v : V) (X : Set V) :
    (G.graph.neighborSet v ∩ X).ncard ≤ G.maxDegree := by
  calc (G.graph.neighborSet v ∩ X).ncard
    ≤ (G.graph.neighborSet v).ncard := Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    _ ≤ G.maxDegree := G.ncard_neighborSet_le_maxDegree v

/-- The union of neighborhoods intersected with X has size at most Δ * |S|. -/
lemma ncard_biUnion_neighborSet_inter_le {S X : Set V} (hS : S.Finite) :
    (⋃ v ∈ S, G.graph.neighborSet v ∩ X).ncard ≤ G.maxDegree * S.ncard := by
  classical
  calc (⋃ v ∈ S, G.graph.neighborSet v ∩ X).ncard
    ≤ ∑ᶠ v ∈ S, (G.graph.neighborSet v ∩ X).ncard := Set.Finite.ncard_biUnion_le hS _
    _ ≤ ∑ᶠ v ∈ S, G.maxDegree := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS]
        apply Finset.sum_le_sum
        intro v hv
        simp only [Set.Finite.mem_toFinset] at hv
        exact G.ncard_inter_neighborSet_le_maxDegree v X
    _ = G.maxDegree * S.ncard := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const,
            smul_eq_mul, mul_comm, Set.ncard_eq_toFinset_card S hS]

end NeighborhoodBounds

/-! ### Additional Block Operations -/

/-- The blocks that intersect a given vertex set X. Paper notation: U_X -/
def blocksIntersecting (X : Set V) : Set (Set V) :=
  {U ∈ G.blocks | (U ∩ X).Nonempty}

/-- The closure of a set X is the union of all blocks that intersect X.
    Paper notation: cl(X) = V_{U_X} -/
def closure (X : Set V) : Set V :=
  G.blockUnion (G.blocksIntersecting X)

/-- X restricted to the blocks in R. Paper notation: X_R = X ∩ V_R -/
def restrictToBlocks (X : Set V) (R : Set (Set V)) : Set V :=
  X ∩ G.blockUnion R

/-! ### Block Membership -/

omit [Fintype V] in
/-- Every vertex is in exactly one block (from partition property). -/
lemma exists_unique_block_mem (v : V) : ∃! U, U ∈ G.blocks ∧ v ∈ U :=
  G.isPartition.2 v

omit [Fintype V] in
/-- Every vertex is in some block. -/
lemma exists_block_mem (v : V) : ∃ U ∈ G.blocks, v ∈ U := by
  obtain ⟨U, ⟨hU, hv⟩, _⟩ := G.exists_unique_block_mem v
  exact ⟨U, hU, hv⟩

omit [Fintype V] in
/-- The unique block containing a vertex v (exists by partition property). -/
noncomputable def blockOf (v : V) : Set V :=
  Classical.choose (G.exists_block_mem v)

omit [Fintype V] in
lemma blockOf_mem (v : V) : G.blockOf v ∈ G.blocks :=
  (Classical.choose_spec (G.exists_block_mem v)).1

omit [Fintype V] in
lemma mem_blockOf (v : V) : v ∈ G.blockOf v :=
  (Classical.choose_spec (G.exists_block_mem v)).2

omit [Fintype V] in
/-- The block containing a vertex is unique (from partition uniqueness). -/
lemma blockOf_unique (v : V) (U : Set V) (hU : U ∈ G.blocks) (hv : v ∈ U) :
    U = G.blockOf v := by
  have huniq := G.exists_unique_block_mem v
  have hU_witness : U ∈ G.blocks ∧ v ∈ U := ⟨hU, hv⟩
  have hB_witness : G.blockOf v ∈ G.blocks ∧ v ∈ G.blockOf v := ⟨G.blockOf_mem v, G.mem_blockOf v⟩
  exact huniq.unique hU_witness hB_witness

end PartitionedGraph

/-! ### Agreement and Reconfiguration Operations -/

/-- Two independent transversals agree on a block if they contain the same vertex from it. -/
def agreeOnBlock (S T : Set V) (U : Set V) : Prop :=
  S ∩ U = T ∩ U

/-- Two independent transversals agree on a set of blocks if they agree on each block. -/
def agreeOnBlocks (S T : Set V) (R : Set (Set V)) : Prop :=
  ∀ U ∈ R, agreeOnBlock S T U

/-! ### Helper Lemmas -/

omit [DecidableEq V] in
/-- agreeOnBlock is symmetric. -/
lemma agreeOnBlock_symm {S T U : Set V} (h : agreeOnBlock S T U) : agreeOnBlock T S U :=
  h.symm

omit [DecidableEq V] in
/-- agreeOnBlock is transitive. -/
lemma agreeOnBlock_trans {S T W U : Set V} (h1 : agreeOnBlock S T U) (h2 : agreeOnBlock T W U) :
    agreeOnBlock S W U :=
  h1.trans h2

omit [DecidableEq V] in
/-- agreeOnBlock is reflexive. -/
lemma agreeOnBlock_refl (S U : Set V) : agreeOnBlock S S U := rfl

omit [DecidableEq V] in
/-- agreeOnBlocks is symmetric. -/
lemma agreeOnBlocks_symm {S T : Set V} {R : Set (Set V)} (h : agreeOnBlocks S T R) :
    agreeOnBlocks T S R :=
  fun U hU => agreeOnBlock_symm (h U hU)

omit [DecidableEq V] in
/-- agreeOnBlocks is transitive. -/
lemma agreeOnBlocks_trans {S T W : Set V} {R : Set (Set V)}
    (h1 : agreeOnBlocks S T R) (h2 : agreeOnBlocks T W R) : agreeOnBlocks S W R :=
  fun U hU => agreeOnBlock_trans (h1 U hU) (h2 U hU)

omit [DecidableEq V] in
/-- agreeOnBlocks is reflexive. -/
lemma agreeOnBlocks_refl (S : Set V) (R : Set (Set V)) : agreeOnBlocks S S R :=
  fun U _ => agreeOnBlock_refl S U

variable [Fintype V] (G : PartitionedGraph V)

/-- Given an IT S and a vertex v independent of S, S ⊕ v is the IT obtained by
    replacing S's vertex in v's block with v. -/
def PartitionedGraph.oplus (S : Set V) (v : V) : Set V :=
  (S \ G.blockOf v) ∪ {v}

omit [Fintype V] in
/-- An IT has exactly one vertex in each block. -/
lemma PartitionedGraph.IsIndependentTransversal.unique_vertex {S : Set V}
    (hS : G.IsIndependentTransversal S) (U : Set V) (hU : U ∈ G.blocks) :
    ∃! v, v ∈ S ∧ v ∈ U := by
  obtain ⟨v, hv, huniq⟩ := hS.2 U hU
  refine ⟨v, ⟨hv.1, hv.2⟩, ?_⟩
  intro w ⟨hwS, hwU⟩
  exact huniq w ⟨hwS, hwU⟩

omit [Fintype V] in
/-- An IT S has cardinality equal to the number of blocks. -/
lemma PartitionedGraph.IsIndependentTransversal.card_eq {S : Set V}
    (hS : G.IsIndependentTransversal S) (_hfin : G.blocks.Finite) :
    S.ncard = G.blocks.ncard := by
  -- The map v ↦ blockOf v gives a bijection from S to blocks
  -- First show the image equals blocks
  have h_image : G.blockOf '' S = G.blocks := by
    ext U
    constructor
    · -- If U = blockOf v for some v ∈ S, then U ∈ blocks
      intro ⟨v, hv, hvU⟩
      rw [← hvU]
      exact G.blockOf_mem v
    · -- If U ∈ blocks, find v ∈ S ∩ U and show U = blockOf v
      intro hU
      obtain ⟨v, hv, _⟩ := hS.2 U hU
      use v, hv.1
      exact (G.blockOf_unique v U hU hv.2).symm
  -- Now show blockOf is injective on S
  have h_inj : Set.InjOn G.blockOf S := by
    intro v hv w hw hvw
    -- v and w are in the same block (blockOf v = blockOf w)
    -- Since S meets each block exactly once, v = w
    have hv_in : v ∈ S ∩ G.blockOf v := ⟨hv, G.mem_blockOf v⟩
    have hw_mem : w ∈ G.blockOf v := by rw [hvw]; exact G.mem_blockOf w
    have hw_in : w ∈ S ∩ G.blockOf v := ⟨hw, hw_mem⟩
    obtain ⟨u, _, huniq⟩ := hS.2 (G.blockOf v) (G.blockOf_mem v)
    have hvu : v = u := huniq v hv_in
    have hwu : w = u := huniq w hw_in
    rw [hvu, hwu]
  -- Combine: |S| = |blockOf '' S| = |blocks|
  rw [← h_image]
  exact (Set.ncard_image_of_injOn h_inj).symm

omit [Fintype V] in
/-- If S is an IT and v ∈ S, then v's block intersects S at exactly {v}. -/
lemma PartitionedGraph.IsIndependentTransversal.inter_block_singleton
    {S : Set V} (hS : G.IsIndependentTransversal S) {v : V} (hv : v ∈ S) :
    S ∩ G.blockOf v = {v} := by
  ext w
  constructor
  · intro ⟨hwS, hwB⟩
    obtain ⟨u, hu, huniq⟩ := hS.2 (G.blockOf v) (G.blockOf_mem v)
    have hv' : v ∈ S ∩ G.blockOf v := ⟨hv, G.mem_blockOf v⟩
    have hw' : w ∈ S ∩ G.blockOf v := ⟨hwS, hwB⟩
    have : v = u := huniq v hv'
    have : w = u := huniq w hw'
    simp_all
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact ⟨hv, G.mem_blockOf v⟩

/-! ### Notation reminder

For symmetric difference, use Mathlib's `symmDiff`:
* `symmDiff S T = (S \ T) ∪ (T \ S)`
* Paper notation: S △ T
-/

end IndependentTransversals
