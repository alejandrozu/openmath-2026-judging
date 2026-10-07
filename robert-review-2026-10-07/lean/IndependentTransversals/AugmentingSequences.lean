/-
Copyright (c) 2025 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import IndependentTransversals.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Augmenting Sequences

This file defines augmenting sequences and feasible tuples, which are the key
technical tools for proving both Haxell's theorem and the main reconfiguration result.

## Main Definitions

* `AugmentingSeq` - A sequence of vertices satisfying the augmenting conditions
* `FeasibleTuple` - A triple (S, C, v) where v is augmenting for (S, C)
* `FeasibleTupleLt` - The strict partial order on feasible tuples

## Main Results

* The partial order on feasible tuples is well-founded
* Bounds on |C_k| and |B_k| (Equation 2.1)
-/

namespace IndependentTransversals

variable {V : Type*} [DecidableEq V] [Fintype V]

section AugmentingSequences

/-- A partial independent transversal is an independent set that meets each block
    in at most one vertex.
    Recall: `G.graph.IsIndepSet S ↔ S.Pairwise (fun v w ↦ ¬G.graph.Adj v w)` -/
def PartitionedGraph.IsPartialIT (G : PartitionedGraph V) (S : Set V) : Prop :=
  G.graph.IsIndepSet S ∧
  ∀ U ∈ G.blocks, (S ∩ U).ncard ≤ 1

omit [Fintype V] in
/-- The empty set is a partial IT. -/
lemma PartitionedGraph.isPartialIT_empty (G : PartitionedGraph V) : G.IsPartialIT ∅ := by
  constructor
  · -- ∅ is vacuously independent
    intro v hv
    simp only [Set.mem_empty_iff_false] at hv
  · -- ∅ ∩ U = ∅ has cardinality 0 ≤ 1
    intro U _
    simp only [Set.empty_inter, Set.ncard_empty]
    exact Nat.zero_le 1

omit [Fintype V] in
/-- A full IT is also a partial IT. -/
lemma PartitionedGraph.IsIndependentTransversal.isPartialIT (G : PartitionedGraph V) {S : Set V}
    (hS : G.IsIndependentTransversal S) : G.IsPartialIT S := by
  constructor
  · exact hS.1
  · intro U hU
    obtain ⟨v, hv, _⟩ := hS.2 U hU
    have h_eq : S ∩ U = S ∩ G.blockOf v := by
      rw [G.blockOf_unique v U hU hv.2]
    rw [h_eq, PartitionedGraph.IsIndependentTransversal.inter_block_singleton G hS hv.1]
    simp only [Set.ncard_singleton, le_refl]

/-- The blocks not covered by a partial IT. -/
def PartitionedGraph.uncoveredBlocks (G : PartitionedGraph V) (S : Set V) : Set (Set V) :=
  G.blocks \ G.blocksIntersecting S

/-- A partial IT with no uncovered blocks is a full independent transversal. -/
lemma PartitionedGraph.partialIT_of_no_uncovered (G : PartitionedGraph V) (S : Set V)
    (hPartial : G.IsPartialIT S) (hFull : G.uncoveredBlocks S = ∅) :
    G.IsIndependentTransversal S := by
  constructor
  · exact hPartial.1
  · intro U hU
    -- U is covered (not in uncoveredBlocks), so S ∩ U is nonempty
    have hCovered : U ∈ G.blocksIntersecting S := by
      rw [Set.eq_empty_iff_forall_notMem] at hFull
      have hU_not_uncovered := hFull U
      simp only [uncoveredBlocks, Set.mem_diff, not_and, not_not] at hU_not_uncovered
      exact hU_not_uncovered hU
    -- blocksIntersecting S means S ∩ U is nonempty
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hCovered
    obtain ⟨v, hv⟩ := hCovered.2
    -- S ∩ U has at most 1 element (from IsPartialIT)
    have hAtMostOne := hPartial.2 U hU
    -- So there's exactly one element
    use v
    constructor
    · exact ⟨hv.2, hv.1⟩
    · intro w hw
      -- Both v and w are in S ∩ U, which has ncard ≤ 1
      have hv_mem : v ∈ S ∩ U := ⟨hv.2, hv.1⟩
      have hw_mem : w ∈ S ∩ U := hw
      -- If {v, w} ⊆ S ∩ U and |S ∩ U| ≤ 1, then v = w
      by_contra hne
      have hne' : v ≠ w := fun h => hne h.symm
      have h_two : 2 ≤ (S ∩ U).ncard := by
        have h_pair : ({v, w} : Set V) ⊆ S ∩ U := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hv_mem
          · exact hw_mem
        have h_card_pair : ({v, w} : Set V).ncard = 2 := Set.ncard_pair hne'
        calc 2 = ({v, w} : Set V).ncard := h_card_pair.symm
          _ ≤ (S ∩ U).ncard := Set.ncard_le_ncard h_pair (Set.toFinite _)
      omega

/-- Given a partial IT S and a sequence of vertices v = (v₁,...,vₘ), we define
    B_k inductively: B_0 = uncovered blocks, B_k = B_{k-1} ∪ U_{N_S(v_k)}. -/
def PartitionedGraph.blocksSeq (G : PartitionedGraph V) (S : Set V) (seq : List V) :
    ℕ → Set (Set V)
  | 0 => G.uncoveredBlocks S
  | k + 1 =>
    match seq[k]? with
    | none => G.uncoveredBlocks S
    | some v => G.blocksSeq S seq k ∪ G.blocksIntersecting (G.graph.neighborSet v ∩ S)

/-- Given a partial IT S, a set C, and a sequence v, we define C_k inductively:
    C_0 = C, C_k = C_{k-1} ∪ N_S[v_k] where N_S[v] = (N_G(v) ∩ S) ∪ {v}.
    Note: We add only neighbors in S (not full neighborhood) to match Equation 2.1 bounds. -/
def PartitionedGraph.vertexSeq (G : PartitionedGraph V) (S C : Set V) (seq : List V) :
    ℕ → Set V
  | 0 => C
  | k + 1 =>
    match seq[k]? with
    | none => C
    | some v => G.vertexSeq S C seq k ∪ (G.graph.neighborSet v ∩ S) ∪ {v}

omit [Fintype V] in
/-- blocksSeq is preserved when appending elements, for indices within the original list. -/
lemma PartitionedGraph.blocksSeq_append (G : PartitionedGraph V) (S : Set V) (seq : List V)
    (v : V) (k : ℕ) (hk : k ≤ seq.length) :
    G.blocksSeq S (seq ++ [v]) k = G.blocksSeq S seq k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold blocksSeq
    have hk' : k < seq.length := Nat.lt_of_succ_le hk
    rw [List.getElem?_append_left hk', ih (le_of_lt hk')]

omit [Fintype V] in
/-- vertexSeq is preserved when appending elements, for indices within the original list. -/
lemma PartitionedGraph.vertexSeq_append (G : PartitionedGraph V) (S C : Set V) (seq : List V)
    (v : V) (k : ℕ) (hk : k ≤ seq.length) :
    G.vertexSeq S C (seq ++ [v]) k = G.vertexSeq S C seq k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold vertexSeq
    have hk' : k < seq.length := Nat.lt_of_succ_le hk
    rw [List.getElem?_append_left hk', ih (le_of_lt hk')]

omit [Fintype V] in
/-- blocksSeq is preserved when taking a prefix, for indices within the prefix. -/
lemma PartitionedGraph.blocksSeq_take (G : PartitionedGraph V) (S : Set V) (seq : List V)
    (n k : ℕ) (hn : n ≤ seq.length) (hk : k ≤ n) :
    G.blocksSeq S (seq.take n) k = G.blocksSeq S seq k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold blocksSeq
    have hk' : k < n := Nat.lt_of_succ_le hk
    have hk_lt : k < seq.length := Nat.lt_of_lt_of_le hk' hn
    simp only [List.getElem?_take, hk', ↓reduceIte, ih (le_of_lt hk')]

omit [Fintype V] in
/-- vertexSeq is preserved when taking a prefix, for indices within the prefix. -/
lemma PartitionedGraph.vertexSeq_take (G : PartitionedGraph V) (S C : Set V) (seq : List V)
    (n k : ℕ) (hn : n ≤ seq.length) (hk : k ≤ n) :
    G.vertexSeq S C (seq.take n) k = G.vertexSeq S C seq k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold vertexSeq
    have hk' : k < n := Nat.lt_of_succ_le hk
    have hk_lt : k < seq.length := Nat.lt_of_lt_of_le hk' hn
    simp only [List.getElem?_take, hk', ↓reduceIte, ih (le_of_lt hk')]

/-- The degree of vertex v_k in the sequence, i.e., |N_S(v_k)|. -/
noncomputable def PartitionedGraph.degreeAt (G : PartitionedGraph V) (S : Set V)
    (seq : List V) (k : ℕ) : ℕ :=
  match seq[k - 1]? with
  | some v => (G.graph.neighborSet v ∩ S).ncard
  | none => 0

/-- The degree sequence d(v) = (d₁(v), ..., dₘ(v)). -/
noncomputable def PartitionedGraph.degreeSeq (G : PartitionedGraph V) (S : Set V)
    (seq : List V) : List ℕ :=
  seq.mapIdx fun _ v => (G.graph.neighborSet v ∩ S).ncard

/-- A sequence v is augmenting for (S, C) if for all k:
    1. v_k ∈ V_{B_{k-1}} (the vertex is in the block union at step k)
    2. v_k is not adjacent to any vertex in C_{k-1} (disjoint neighborhood)
    3. d_k(v) > 0 if k ≠ m (positive degree for non-last elements)

    Note: These are the exact 3 conditions from the paper's Definition 2.3.
    The paper's construction chooses v_k from V_{B_k} \ C_k, but this "freshness"
    is NOT a condition of being augmenting - it's a consequence of how we construct
    augmenting sequences. In the main proof (Lemma 2.5), we do NOT need v_k ∉ S ∪ T
    in all cases. Instead, if v_m ∈ S, then S' = S ⊕ v_m = S (unchanged), so we
    simply case split on whether v_m ∈ S, v_m ∈ T, or v_m ∉ S ∪ T. -/
def PartitionedGraph.IsAugmenting (G : PartitionedGraph V) (S C : Set V)
    (seq : List V) : Prop :=
  ∀ k : Fin seq.length,
    let v := seq[k]
    -- Condition 1: v_k ∈ V_{B_{k-1}}
    v ∈ G.blockUnion (G.blocksSeq S seq k) ∧
    -- Condition 2: v_k not adjacent to C_{k-1}
    Disjoint (G.graph.neighborSet v) (G.vertexSeq S C seq k) ∧
    -- Condition 3: d_k > 0 if k ≠ m-1
    (k.val + 1 < seq.length → 0 < (G.graph.neighborSet v ∩ S).ncard)

/-- A feasible tuple (S, C, v) consists of a partial IT S, a set C ⊆ V_{U\U_S},
    and an augmenting sequence v. -/
structure PartitionedGraph.FeasibleTuple (G : PartitionedGraph V) where
  S : Set V
  C : Set V
  seq : List V
  isPartialIT : G.IsPartialIT S
  C_subset : C ⊆ G.blockUnion (G.uncoveredBlocks S)
  isAugmenting : G.IsAugmenting S C seq

end AugmentingSequences

section AugmentingProperties

variable (G : PartitionedGraph V)

omit [Fintype V] in
/-- The S-neighborhood of v_j is contained in vertexSeq at step j+1.
    This follows from the definition: vertexSeq (j+1) = vertexSeq j ∪ N_S(v_j) ∪ {v_j}. -/
lemma PartitionedGraph.neighborSet_inter_S_subset_vertexSeq (S C : Set V) (seq : List V)
    (j : ℕ) (hj : j < seq.length) :
    G.graph.neighborSet seq[j] ∩ S ⊆ G.vertexSeq S C seq (j + 1) := by
  simp only [vertexSeq]
  have hseq : seq[j]? = some seq[j] := List.getElem?_eq_getElem hj
  simp only [hseq]
  intro x hx
  -- Goal: x ∈ (vertexSeq ∪ neighborSet ∩ S) ∪ {v}
  -- We want x ∈ neighborSet ∩ S, which is the right part of the left union
  left; right
  exact hx

omit [Fintype V] in
/-- vertexSeq is monotonically increasing. -/
lemma PartitionedGraph.vertexSeq_mono (S C : Set V) (seq : List V) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ seq.length) :
    G.vertexSeq S C seq j ⊆ G.vertexSeq S C seq k := by
  induction hjk with
  | refl => exact Set.Subset.refl _
  | step _ ih =>
    rename_i k' hj'
    have hk' : k' < seq.length := Nat.lt_of_succ_le hk
    have ih' := ih (le_of_lt (Nat.lt_of_succ_le hk))
    simp only [vertexSeq]
    cases hseq : seq[k']? with
    | none =>
      -- This case is impossible since k' < seq.length
      have hsome := List.getElem?_eq_getElem hk'
      rw [hseq] at hsome
      exact (Option.some_ne_none _ hsome.symm).elim
    | some v =>
      intro x hx
      left; left
      exact ih' hx

omit [Fintype V] in
/-- If j < k, then N_S(v_j) ⊆ vertexSeq k. -/
lemma PartitionedGraph.neighborSet_inter_S_subset_vertexSeq' (S C : Set V) (seq : List V)
    {j k : ℕ} (hj : j < k) (hk : k ≤ seq.length) :
    G.graph.neighborSet seq[j] ∩ S ⊆ G.vertexSeq S C seq k := by
  have hj' : j < seq.length := Nat.lt_of_lt_of_le hj hk
  have h1 := G.neighborSet_inter_S_subset_vertexSeq S C seq j hj'
  have h2 := G.vertexSeq_mono S C seq (Nat.succ_le_of_lt hj) hk
  exact Set.Subset.trans h1 h2

omit [Fintype V] in
/-- The vertex v_j is contained in vertexSeq at step j+1.
    This follows from the definition: vertexSeq (j+1) = vertexSeq j ∪ N_S(v_j) ∪ {v_j}. -/
lemma PartitionedGraph.vertex_mem_vertexSeq (S C : Set V) (seq : List V)
    (j : ℕ) (hj : j < seq.length) :
    seq[j] ∈ G.vertexSeq S C seq (j + 1) := by
  simp only [vertexSeq]
  have hseq : seq[j]? = some seq[j] := List.getElem?_eq_getElem hj
  simp only [hseq]
  right
  exact Set.mem_singleton_iff.mpr rfl

omit [Fintype V] in
/-- If j < k, then v_j ∈ vertexSeq k. -/
lemma PartitionedGraph.vertex_mem_vertexSeq' (S C : Set V) (seq : List V)
    {j k : ℕ} (hj : j < k) (hk : k ≤ seq.length) :
    seq[j] ∈ G.vertexSeq S C seq k := by
  have hj' : j < seq.length := Nat.lt_of_lt_of_le hj hk
  have h1 := G.vertex_mem_vertexSeq S C seq j hj'
  have h2 := G.vertexSeq_mono S C seq (Nat.succ_le_of_lt hj) hk
  exact h2 h1

omit [Fintype V] in
/-- Membership characterization for vertexSeq: x ∈ vertexSeq S C seq m implies
    x ∈ C, or x = seq[j] for some j < m, or x ∈ N(seq[j]) ∩ S for some j < m.

    Note: This is stated as an implication to avoid dependent type issues. -/
lemma PartitionedGraph.mem_vertexSeq_of (S C : Set V) (seq : List V)
    (m : ℕ) (hm : m ≤ seq.length) (x : V) (hx : x ∈ G.vertexSeq S C seq m) :
    x ∈ C ∨ (∃ j : Fin m, x = seq[j.val]'(Nat.lt_of_lt_of_le j.isLt hm)) ∨
    (∃ j : Fin m,
      x ∈ G.graph.neighborSet (seq[j.val]'(Nat.lt_of_lt_of_le j.isLt hm)) ∩ S) := by
  induction m generalizing x with
  | zero =>
    simp only [vertexSeq] at hx
    left; exact hx
  | succ m ih =>
    have hm' : m ≤ seq.length := Nat.le_of_succ_le hm
    have hm_lt : m < seq.length := Nat.lt_of_succ_le hm
    simp only [vertexSeq] at hx
    have hseq : seq[m]? = some seq[m] := List.getElem?_eq_getElem hm_lt
    simp only [hseq] at hx
    rcases hx with ⟨hx_vs | hx_nbr⟩ | hx_eq
    · -- x ∈ vertexSeq m
      rcases ih hm' x hx_vs with hC | ⟨⟨j, hj⟩, hx_eq⟩ | ⟨⟨j, hj⟩, hx_nbr⟩
      · left; exact hC
      · right; left
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hx_eq⟩
      · right; right
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hx_nbr⟩
    · -- x ∈ N(seq[m]) ∩ S
      right; right
      exact ⟨⟨m, Nat.lt_succ_self m⟩, hx_nbr⟩
    · -- x = seq[m]
      right; left
      exact ⟨⟨m, Nat.lt_succ_self m⟩, Set.mem_singleton_iff.mp hx_eq⟩

omit [Fintype V] in
/-- **Key Lemma**: Augmenting sequences have pairwise distinct vertices.

    Proof: Suppose v_i = v_j for some i < j in the sequence.
    1. v_i ∈ vertexSeq (i+1) ⊆ vertexSeq j (by monotonicity)
    2. For augmenting condition at j: N(v_j) ∩ vertexSeq j = ∅
    3. Since v_i = v_j, we have N(v_i) ∩ vertexSeq j = ∅
    4. But N(v_i) ∩ S ⊆ vertexSeq (i+1) ⊆ vertexSeq j
    5. So N(v_i) ∩ S = ∅, meaning d_i = 0
    6. The augmenting condition requires d_i > 0 for i < m-1
    7. So i = m-1, but i < j ≤ m-1, contradiction -/
lemma PartitionedGraph.augmenting_seq_distinct (S C : Set V) (seq : List V)
    (haug : G.IsAugmenting S C seq) :
    seq.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  -- Goal: ∀ i j, i < j → j < seq.length → seq[i]? ≠ seq[j]?
  intro i j hij hj_len
  -- Need to show seq[i]? ≠ seq[j]?
  by_contra h_eq
  -- Have i < j and j < seq.length, so i < seq.length
  have hi_len : i < seq.length := Nat.lt_trans hij hj_len
  -- Extract the equality seq[i] = seq[j]
  have h_vi_eq_vj : seq[i] = seq[j] := by
    simp only [List.getElem?_eq_getElem hi_len, List.getElem?_eq_getElem hj_len,
               Option.some_inj] at h_eq
    exact h_eq
  -- v_i ∈ vertexSeq (i+1) ⊆ vertexSeq j (since i+1 ≤ j, i.e., i < j)
  have h_vi_in_Cj : seq[i] ∈ G.vertexSeq S C seq j :=
    G.vertex_mem_vertexSeq' S C seq hij (Nat.le_of_lt hj_len)
  -- The augmenting condition at j: N(v_j) ∩ vertexSeq j = ∅
  have h_disj := (haug ⟨j, hj_len⟩).2.1
  -- Since v_i = v_j and v_i ∈ vertexSeq j, N(v_i) ∩ vertexSeq j = ∅
  -- But N(v_i) ∩ S ⊆ vertexSeq (i+1) ⊆ vertexSeq j
  have h_NS_sub : G.graph.neighborSet seq[i] ∩ S ⊆ G.vertexSeq S C seq j :=
    G.neighborSet_inter_S_subset_vertexSeq' S C seq hij (Nat.le_of_lt hj_len)
  -- N(v_j) = N(v_i), and N(v_i) ∩ S ⊆ vertexSeq j, but N(v_j) ∩ vertexSeq j = ∅
  -- So N(v_i) ∩ S ⊆ N(v_j) ∩ vertexSeq j = ∅
  have h_NS_empty : G.graph.neighborSet seq[i] ∩ S = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx_N hx_S
    have hx_in : x ∈ G.vertexSeq S C seq j := h_NS_sub ⟨hx_N, hx_S⟩
    rw [h_vi_eq_vj] at hx_N
    exact Set.disjoint_left.mp h_disj hx_N hx_in
  -- So d_i = |N(v_i) ∩ S| = 0
  have h_di_zero : (G.graph.neighborSet seq[i] ∩ S).ncard = 0 := by
    rw [h_NS_empty, Set.ncard_empty]
  -- But augmenting requires d_i > 0 for i < m-1
  have h_i_last : i + 1 < seq.length → 0 < (G.graph.neighborSet seq[i] ∩ S).ncard :=
    (haug ⟨i, hi_len⟩).2.2
  -- So i + 1 ≥ seq.length, i.e., i ≥ seq.length - 1
  have h_i_bound : ¬(i + 1 < seq.length) := by
    intro h_lt
    have := h_i_last h_lt
    omega
  -- So i + 1 ≥ seq.length, meaning i = seq.length - 1 (since i < seq.length)
  have h_i_eq : i + 1 = seq.length := by omega
  -- But i < j < seq.length and i + 1 = seq.length means j < i + 1 = seq.length ≤ j + 1
  -- We have j < seq.length = i + 1, so j ≤ i, contradicting i < j
  omega

/-- Augmenting sequences have length at most |V|.
    This follows from the fact that the vertices are pairwise distinct. -/
lemma PartitionedGraph.augmenting_seq_length_le (S C : Set V) (seq : List V)
    (haug : G.IsAugmenting S C seq) :
    seq.length ≤ Fintype.card V := by
  have h_nodup := G.augmenting_seq_distinct S C seq haug
  exact List.Nodup.length_le_card h_nodup

omit [Fintype V] in
/-- For an augmenting sequence, N_S(v_k) is disjoint from N_S(v_j) for j < k.
    This is because N_S(v_j) ⊆ vertexSeq k and v_k is disjoint from vertexSeq k. -/
lemma PartitionedGraph.augmenting_neighborSets_disjoint (S C : Set V) (seq : List V)
    (haug : G.IsAugmenting S C seq) {j k : ℕ} (hj : j < k) (hk : k < seq.length) :
    Disjoint (G.graph.neighborSet seq[k] ∩ S) (G.graph.neighborSet seq[j] ∩ S) := by
  -- N_S(v_j) ⊆ vertexSeq k (by neighborSet_inter_S_subset_vertexSeq')
  have h_sub := G.neighborSet_inter_S_subset_vertexSeq' S C seq hj (le_of_lt hk)
  -- v_k is disjoint from vertexSeq k (by augmenting property)
  have h_disj := (haug ⟨k, hk⟩).2.1
  -- So N(v_k) ∩ vertexSeq k = ∅
  -- Therefore N_S(v_k) ∩ N_S(v_j) ⊆ N(v_k) ∩ N_S(v_j) ⊆ N(v_k) ∩ vertexSeq k = ∅
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro ⟨hx_Nk, hx_S⟩ hx_Nj hx_S'
  -- x ∈ N(v_k) and x ∈ N_S(v_j) ⊆ vertexSeq k
  have hx_vtx : x ∈ G.vertexSeq S C seq k := h_sub ⟨hx_Nj, hx_S⟩
  -- But N(v_k) ∩ vertexSeq k = ∅
  exact Set.disjoint_left.mp h_disj hx_Nk hx_vtx

omit [Fintype V] in
/-- Helper: If U ∈ blocksSeq S seq m, then either U is uncovered or there exists j < m
    such that U ∈ blocksIntersecting (N_S(seq[j])). -/
lemma PartitionedGraph.blocksSeq_mem_cases (S : Set V) (seq : List V) (U : Set V)
    (m : ℕ) (hm : m ≤ seq.length) (hU : U ∈ G.blocksSeq S seq m) :
    U ∈ G.uncoveredBlocks S ∨
    ∃ (j : ℕ) (hj : j < seq.length), j < m ∧
      U ∈ G.blocksIntersecting (G.graph.neighborSet seq[j] ∩ S) := by
  induction m with
  | zero =>
    simp only [blocksSeq] at hU
    left; exact hU
  | succ m' ih =>
    simp only [blocksSeq] at hU
    have hm'_lt : m' < seq.length := Nat.lt_of_succ_le hm
    cases hseq : seq[m']? with
    | none =>
      exact (Option.some_ne_none _ ((List.getElem?_eq_getElem hm'_lt).symm.trans hseq)).elim
    | some v =>
      rw [hseq] at hU
      rcases hU with hU_prev | hU_new
      · -- U ∈ B_{m'}
        have hm'_le : m' ≤ seq.length := Nat.le_of_lt hm'_lt
        rcases ih hm'_le hU_prev with huncov | ⟨j, hj_bound, hj_lt, hU_j⟩
        · left; exact huncov
        · right
          exact ⟨j, hj_bound, Nat.lt_trans hj_lt (Nat.lt_succ_self m'), hU_j⟩
      · -- U ∈ blocksIntersecting(N_S(seq[m']))
        right
        have h_eq : seq[m'] = v := by
          have h := List.getElem?_eq_getElem hm'_lt
          simp only [hseq] at h
          exact (Option.some_injective _ h).symm
        have hU_new' : U ∈ G.blocksIntersecting (G.graph.neighborSet seq[m'] ∩ S) := by
          rw [h_eq]; exact hU_new
        exact ⟨m', hm'_lt, Nat.lt_succ_self m', hU_new'⟩

/-- For an augmenting sequence with partial IT S, the new blocks at step k
    (blocksIntersecting(N_S(v_k))) are disjoint from B_k.

    Proof: Suppose U ∈ blocksIntersecting(N_S(v_k)) ∩ B_k.
    - U contains some s ∈ S ∩ N(v_k) (from membership in blocksIntersecting(N_S(v_k)))
    - If U ∈ uncoveredBlocks S, then S ∩ U = ∅, contradicting s ∈ S ∩ U
    - If U ∈ blocksIntersecting(N_S(v_j)) for some j < k, then U contains s' ∈ S ∩ N(v_j)
    - Since S is partial IT, |S ∩ U| ≤ 1, so s = s'
    - Then s ∈ N(v_j) ∩ N(v_k), contradicting augmenting_neighborSets_disjoint -/
lemma PartitionedGraph.augmenting_blocksSeq_disjoint (S C : Set V) (seq : List V)
    (hS : G.IsPartialIT S) (haug : G.IsAugmenting S C seq)
    (k : ℕ) (hk : k < seq.length) :
    Disjoint (G.blocksIntersecting (G.graph.neighborSet seq[k] ∩ S)) (G.blocksSeq S seq k) := by
  -- Prove: if U ∈ blocksIntersecting(N_S(seq[k])) and U ∈ B_k, get contradiction
  rw [Set.disjoint_iff_inter_eq_empty]
  ext U
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hU_new hU_old
  -- U is in blocksIntersecting(N_S(seq[k])), so it contains some s ∈ S ∩ N(seq[k])
  simp only [blocksIntersecting, Set.mem_setOf_eq] at hU_new
  obtain ⟨hU_block, s, hs_U, hs_NS⟩ := hU_new
  have hs_S : s ∈ S := hs_NS.2
  have hs_Nk : s ∈ G.graph.neighborSet seq[k] := hs_NS.1
  -- Use the helper lemma to analyze membership in B_k
  rcases G.blocksSeq_mem_cases S seq U k (Nat.le_of_lt hk) hU_old with
      huncov | ⟨j, hj_len, hj_lt_k, hU_j⟩
  · -- Case 1: U ∈ uncoveredBlocks S, so S ∩ U = ∅
    simp only [uncoveredBlocks, Set.mem_diff, blocksIntersecting, Set.mem_setOf_eq,
      not_and, Set.not_nonempty_iff_eq_empty, Set.inter_comm] at huncov
    have hU_empty := huncov.2 hU_block
    have hs_in : s ∈ S ∩ U := ⟨hs_S, hs_U⟩
    rw [hU_empty] at hs_in
    exact Set.notMem_empty s hs_in
  · -- Case 2: U ∈ blocksIntersecting(N_S(seq[j])) for some j < k
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hU_j
    obtain ⟨_, s', hs'_U, hs'_NS⟩ := hU_j
    have hs'_S : s' ∈ S := hs'_NS.2
    have hs'_Nj : s' ∈ G.graph.neighborSet seq[j] := hs'_NS.1
    -- s, s' ∈ S ∩ U, so s = s' by partial IT property
    have h_eq : s = s' := by
      by_contra hne
      have h_pair : ({s, s'} : Set V) ⊆ S ∩ U := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> exact ⟨‹_›, ‹_›⟩
      have h_two : 2 ≤ (S ∩ U).ncard :=
        (Set.ncard_pair hne).symm.trans_le (Set.ncard_le_ncard h_pair (Set.toFinite _))
      have h_one := hS.2 U hU_block
      omega
    -- s = s' ∈ N(seq[k]) ∩ N(seq[j]) contradicts augmenting_neighborSets_disjoint
    have h_disj := G.augmenting_neighborSets_disjoint S C seq haug hj_lt_k hk
    rw [Set.disjoint_iff_inter_eq_empty] at h_disj
    have hs_Nj : s ∈ G.graph.neighborSet seq[j] := by rw [h_eq]; exact hs'_Nj
    have hs_in_both : s ∈ (G.graph.neighborSet seq[k] ∩ S) ∩
        (G.graph.neighborSet seq[j] ∩ S) := ⟨⟨hs_Nk, hs_S⟩, ⟨hs_Nj, hs_S⟩⟩
    rw [h_disj] at hs_in_both
    exact Set.notMem_empty s hs_in_both

omit [Fintype V] in
/-- A prefix of an augmenting sequence is also augmenting.
    This is key for the truncated sequence construction in Case 2 of two_or_zero. -/
lemma PartitionedGraph.isAugmenting_take (S C : Set V) (seq : List V)
    (n : ℕ) (hn : n ≤ seq.length) (haug : G.IsAugmenting S C seq) :
    G.IsAugmenting S C (seq.take n) := by
  intro kFin
  let k := kFin.val
  -- kFin.isLt : k < (seq.take n).length = n (since n ≤ seq.length)
  have h_take_len : (seq.take n).length = n := List.length_take_of_le hn
  have hk_lt_n : k < n := by rw [← h_take_len]; exact kFin.isLt
  have hk_lt_len : k < seq.length := Nat.lt_of_lt_of_le hk_lt_n hn
  have h_orig := haug (Fin.mk k hk_lt_len)
  -- The k-th element of (seq.take n) equals the k-th element of seq
  have h_elem_eq : (seq.take n)[kFin] = seq[k]'hk_lt_len := List.getElem_take
  -- Show each part of the conjunction
  constructor
  · -- Condition 1: v ∈ blockUnion (blocksSeq S (seq.take n) k)
    rw [h_elem_eq, G.blocksSeq_take S seq n k hn (le_of_lt hk_lt_n)]
    simpa only [Fin.getElem_fin] using h_orig.1
  constructor
  · -- Condition 2: Disjoint (neighborSet v) (vertexSeq S C (seq.take n) k)
    rw [h_elem_eq, G.vertexSeq_take S C seq n k hn (le_of_lt hk_lt_n)]
    simpa only [Fin.getElem_fin] using h_orig.2.1
  -- Condition 3: k + 1 < (seq.take n).length → 0 < degree
  intro hk_succ_lt
  -- hk_succ_lt : k + 1 < (seq.take n).length = n (by h_take_len)
  -- Need: k + 1 < seq.length
  have hk_succ_lt_n : k + 1 < n := h_take_len ▸ hk_succ_lt
  have hk_succ_lt_len : k + 1 < seq.length := Nat.lt_of_lt_of_le hk_succ_lt_n hn
  rw [h_elem_eq]
  exact h_orig.2.2 hk_succ_lt_len

omit [Fintype V] in
/-- Extending an augmenting sequence by one element that satisfies the augmenting conditions.
    If v is augmenting and w satisfies:
    1. w ∈ V_{B_m} (w is in a block from blocksSeq at step m = v.length)
    2. N(w) ∩ C_m = ∅ (w is disjoint from vertexSeq at step m)
    3. The last element of seq (if any) has positive S-degree
    Then v ++ [w] is also augmenting.

    Note: Condition 3 is automatically satisfied in most applications because:
    - If seq = [], there is no last element to check
    - If seq ≠ [], the extension argument in the paper only applies when the last
      element has positive degree (otherwise we could improve via Case 2) -/
lemma PartitionedGraph.isAugmenting_append_one (S C : Set V) (seq : List V) (w : V)
    (haug : G.IsAugmenting S C seq)
    (hw_block : w ∈ G.blockUnion (G.blocksSeq S seq seq.length))
    (hw_disjoint : Disjoint (G.graph.neighborSet w) (G.vertexSeq S C seq seq.length))
    (h_last_pos : ∀ (h : seq ≠ []), 0 < (G.graph.neighborSet (seq.getLast h) ∩ S).ncard) :
    G.IsAugmenting S C (seq ++ [w]) := by
  intro kFin
  let k := kFin.val
  have h_len : (seq ++ [w]).length = seq.length + 1 := by simp
  have hk_lt : k < seq.length + 1 := h_len ▸ kFin.isLt
  by_cases hk_seq : k < seq.length
  · -- k < seq.length: Use the augmenting property of seq
    have h_elem : (seq ++ [w])[kFin] = seq[k]'hk_seq := List.getElem_append_left hk_seq
    rw [h_elem]
    -- The augmenting conditions for seq[k] transfer to seq ++ [w]
    have h_orig := haug (Fin.mk k hk_seq)
    constructor
    · -- Condition 1: seq[k] ∈ V_{blocksSeq S (seq ++ [w]) k}
      have h_eq : G.blocksSeq S (seq ++ [w]) k = G.blocksSeq S seq k :=
        G.blocksSeq_append S seq w k (le_of_lt hk_seq)
      rw [h_eq]
      exact h_orig.1
    constructor
    · -- Condition 2: Disjoint (neighborSet seq[k]) (vertexSeq S C (seq ++ [w]) k)
      have h_eq : G.vertexSeq S C (seq ++ [w]) k = G.vertexSeq S C seq k :=
        G.vertexSeq_append S C seq w k (le_of_lt hk_seq)
      rw [h_eq]
      exact h_orig.2.1
    -- Condition 3: k + 1 < (seq ++ [w]).length → 0 < degree
    intro hk_succ
    by_cases hk_succ_seq : k + 1 < seq.length
    · exact h_orig.2.2 hk_succ_seq
    · -- k + 1 = seq.length, so k = seq.length - 1 (last element of seq)
      have hk_eq' : k + 1 = seq.length :=
        Nat.eq_of_lt_succ_of_not_lt (Nat.succ_lt_succ hk_seq) hk_succ_seq
      have h_seq_ne : seq ≠ [] := by
        intro h_empty
        rw [h_empty] at hk_seq
        exact Nat.not_lt_zero k hk_seq
      have h_last_lt : seq.length - 1 < seq.length := by omega
      have hk_last : k = seq.length - 1 := by omega
      -- seq[k] = seq.getLast h_seq_ne
      have h_getLast : seq.getLast h_seq_ne = seq[seq.length - 1]'h_last_lt :=
        List.getLast_eq_getElem h_seq_ne
      have h_idx : seq[k]'hk_seq = seq[seq.length - 1]'h_last_lt := by congr 1
      rw [h_idx, ← h_getLast]
      exact h_last_pos h_seq_ne
  · -- k = seq.length: This is the new element w
    have hk_eq : k = seq.length := Nat.eq_of_lt_succ_of_not_lt hk_lt hk_seq
    have h_not_lt : ¬ k < seq.length := hk_seq
    have h_ge : seq.length ≤ k := Nat.not_lt.mp h_not_lt
    have h_elem : (seq ++ [w])[kFin] = w := by
      have : (seq ++ [w])[k]'(h_len ▸ (by omega : k < seq.length + 1)) = w := by
        rw [List.getElem_append_right h_ge]
        simp [hk_eq]
      simpa only [Fin.getElem_fin, k] using this
    rw [h_elem]
    constructor
    · -- Condition 1: w ∈ V_{blocksSeq S (seq ++ [w]) k}
      have h_eq : G.blocksSeq S (seq ++ [w]) k = G.blocksSeq S seq seq.length := by
        rw [hk_eq]
        exact G.blocksSeq_append S seq w seq.length (le_refl _)
      rw [h_eq]
      exact hw_block
    constructor
    · -- Condition 2: Disjoint (neighborSet w) (vertexSeq S C (seq ++ [w]) k)
      have h_eq : G.vertexSeq S C (seq ++ [w]) k = G.vertexSeq S C seq seq.length := by
        rw [hk_eq]
        exact G.vertexSeq_append S C seq w seq.length (le_refl _)
      rw [h_eq]
      exact hw_disjoint
    -- Condition 3: k + 1 < (seq ++ [w]).length → 0 < degree
    intro h_false
    -- (seq ++ [w]).length = seq.length + 1, and k = seq.length
    -- So k + 1 = seq.length + 1 = (seq ++ [w]).length, contradicting h_false
    omega

omit [Fintype V] in
/-- The degree sequence of seq is a prefix of the degree sequence of seq ++ [w]. -/
lemma PartitionedGraph.degreeSeq_prefix_of_append (S : Set V) (seq : List V) (w : V) :
    G.degreeSeq S seq <+: G.degreeSeq S (seq ++ [w]) := by
  simp only [degreeSeq]
  rw [List.mapIdx_concat]
  exact List.prefix_append _ _

omit [Fintype V] in
/-- If seq ≠ [], then degreeSeq seq is a proper prefix of degreeSeq (seq ++ [w]). -/
lemma PartitionedGraph.degreeSeq_proper_prefix_of_append (S : Set V) (seq : List V) (w : V) :
    G.degreeSeq S (seq ++ [w]) ≠ G.degreeSeq S seq := by
  simp only [degreeSeq, ne_eq]
  rw [List.mapIdx_concat]
  intro h
  have h_len := congrArg List.length h
  simp at h_len

end AugmentingProperties

section PartialOrder

variable (G : PartitionedGraph V)

/-- Comparison of degree sequences with ∞-padding.
    d1 < d2 iff either:
    1. d2 is a proper prefix of d1 (extending a sequence is progress), OR
    2. At the first differing position k, d1[k] < d2[k]

    This is equivalent to padding shorter sequences with +∞ and comparing lexicographically.
    Example: (1,2,3,4) < (1,2,3) because (1,2,3) is a prefix and (1,2,3,4) extends it.

    Note: This is NOT the same as List.Lex, which has [] < [a] (shorter is smaller).
    Here we want [a] < [] in the prefix case (longer is smaller when extending). -/
def degSeqLt (d1 d2 : List ℕ) : Prop :=
  -- Case 1: d2 is a proper prefix of d1 (d1 extends d2)
  (d2 <+: d1 ∧ d1 ≠ d2) ∨
  -- Case 2: First differing position has d1 smaller, and d1 is not an extension of d2
  (List.Lex (· < ·) d1 d2 ∧ ¬(d1 <+: d2))

/-- The strict partial order on feasible tuples:
    (S, C, v) < (S', C', v') if |S| > |S'| or
    (|S| = |S'| and degree sequence of v is smaller in the ∞-padded lex order).

    The ordering on degree sequences treats longer sequences as smaller when one extends
    the other: (d₁,...,dₘ,dₘ₊₁) < (d₁,...,dₘ). This ensures extending an augmenting
    sequence constitutes progress in the well-founded order. -/
def PartitionedGraph.FeasibleTupleLt (t1 t2 : G.FeasibleTuple) : Prop :=
  t1.S.ncard > t2.S.ncard ∨
  (t1.S.ncard = t2.S.ncard ∧ degSeqLt (G.degreeSeq t1.S t1.seq) (G.degreeSeq t2.S t2.seq))

/-- Encode a list as a natural number by padding to maxLen with (maxVal + 1) and
    interpreting in base (maxVal + 2) with big-endian representation.
    This encoding has the property that:
    - Longer lists (extensions) get smaller encodings (padding adds large values)
    - Lex-smaller lists get smaller encodings

    The big-endian representation ensures that position 0 has the highest weight,
    so lexicographic order corresponds to numerical order on the encodings. -/
def encodeList (maxLen maxVal : ℕ) (d : List ℕ) : ℕ :=
  let base := maxVal + 2
  let padded := d ++ List.replicate (maxLen - d.length) (maxVal + 1)
  padded.foldl (fun acc x => base * acc + x) 0

/-- Helper: The padded list has length maxLen when d.length ≤ maxLen. -/
lemma encodeList_padded_length (maxLen maxVal : ℕ) (d : List ℕ) (hd : d.length ≤ maxLen) :
    (d ++ List.replicate (maxLen - d.length) (maxVal + 1)).length = maxLen := by
  rw [List.length_append, List.length_replicate]
  omega

/-- Helper: foldl with base multiplication distributes over initial value. -/
private lemma foldl_base_mul_add (b : ℕ) (L : List ℕ) (init : ℕ) :
    L.foldl (fun acc x => b * acc + x) init =
    init * b ^ L.length + L.foldl (fun acc x => b * acc + x) 0 := by
  induction L generalizing init with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (b * init + h), ih (b * 0 + h)]
    simp only [mul_zero, zero_add, pow_succ]
    -- Goal: (b * init + h) * b^|t| + foldl = init * (b * b^|t|) + (h * b^|t| + foldl)
    set f := List.foldl (fun acc x ↦ b * acc + x) 0 t
    -- Now the goal only involves arithmetic with f as an opaque term
    have h1 : (b * init + h) * b ^ t.length = b * init * b ^ t.length + h * b ^ t.length :=
      Nat.add_mul _ _ _
    have h2 : b * init * b ^ t.length = init * b * b ^ t.length := by
      rw [Nat.mul_comm b init]
    have h3 : init * b * b ^ t.length = init * (b * b ^ t.length) := Nat.mul_assoc _ _ _
    have h4 : b * b ^ t.length = b ^ t.length * b := Nat.mul_comm _ _
    rw [h1, h2, h3, h4]
    -- Now: init * (b^t.length * b) + h * b^t.length + f
    --    = init * (b^t.length * b) + (h * b^t.length + f)
    omega

/-- Helper: big-endian foldl encoding with bounded elements is < b^length. -/
private lemma foldl_lt_pow (b : ℕ) (_hb : 1 < b) (L : List ℕ) (hL : ∀ x ∈ L, x < b) :
    L.foldl (fun acc x => b * acc + x) 0 < b ^ L.length := by
  induction L with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    have hh : h < b := hL h (by simp)
    have ht : ∀ x ∈ t, x < b := fun x hx => hL x (by simp [hx])
    have iht := ih ht
    rw [foldl_base_mul_add]
    simp only [mul_zero, zero_add]
    -- Goal: h * b^|t| + foldl t 0 < b * b^|t|
    have h1 : h + 1 ≤ b := hh
    have h2 : List.foldl (fun acc x ↦ b * acc + x) 0 t + 1 ≤ b ^ t.length := iht
    set f := List.foldl (fun acc x ↦ b * acc + x) 0 t
    set p := b ^ t.length
    have key : h * p + f + 1 ≤ b * p := by
      calc h * p + f + 1
          ≤ h * p + p := by omega
        _ = (h + 1) * p := by rw [Nat.add_mul]; simp
        _ ≤ b * p := Nat.mul_le_mul_right _ h1
    have comm : b * p = p * b := Nat.mul_comm _ _
    omega

/-- Helper: big-endian encoding comparison when lists differ at first position.
    If L1 = common ++ [a] ++ rest1 and L2 = common ++ [c] ++ rest2 with a < c and
    rest1.length = rest2.length, and all elements < b, then foldl L1 < foldl L2. -/
private lemma bigEndian_lt_of_first_diff (b : ℕ) (hb : 1 < b)
    (common rest1 rest2 : List ℕ) (a c : ℕ) (hac : a < c)
    (hlen : rest1.length = rest2.length)
    (hbound1 : ∀ x ∈ rest1, x < b) :
    (common ++ [a] ++ rest1).foldl (fun acc x => b * acc + x) 0 <
    (common ++ [c] ++ rest2).foldl (fun acc x => b * acc + x) 0 := by
  -- Simplify foldl over concatenated lists
  simp only [List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- Set up notation
  set F := List.foldl (fun acc x ↦ b * acc + x) 0 common
  set v1 := List.foldl (fun acc x ↦ b * acc + x) 0 rest1
  set v2 := List.foldl (fun acc x ↦ b * acc + x) 0 rest2
  set k := rest1.length
  -- Use foldl_base_mul_add to expand
  have hL1 : List.foldl (fun acc x ↦ b * acc + x) (b * F + a) rest1
           = (b * F + a) * b ^ k + v1 := foldl_base_mul_add b rest1 (b * F + a)
  have hL2 : List.foldl (fun acc x ↦ b * acc + x) (b * F + c) rest2
           = (b * F + c) * b ^ rest2.length + v2 := foldl_base_mul_add b rest2 (b * F + c)
  rw [hL1, hL2, hlen]
  -- Goal: (b * F + a) * b^k + v1 < (b * F + c) * b^k + v2
  have hv1_bound : v1 < b ^ k := foldl_lt_pow b hb rest1 hbound1
  -- Key: a < c, so (b * F + a) * b^k + b^k ≤ (b * F + c) * b^k
  have h1 : a + 1 ≤ c := hac
  have h_key : (b * F + a) * b ^ k + v1 < (b * F + c) * b ^ k := by
    have heq : (b * F + a) * b ^ k + b ^ k = (b * F + a + 1) * b ^ k := by
      have lhs_exp : (b * F + a) * b ^ k = b * F * b ^ k + a * b ^ k :=
        Nat.add_mul _ _ _
      have rhs_exp : (b * F + a + 1) * b ^ k = (b * F + a) * b ^ k + 1 * b ^ k :=
        Nat.add_mul _ _ _
      rw [lhs_exp, rhs_exp, Nat.one_mul, Nat.add_mul]
    calc (b * F + a) * b ^ k + v1
        < (b * F + a) * b ^ k + b ^ k := by omega
      _ = (b * F + a + 1) * b ^ k := heq
      _ ≤ (b * F + c) * b ^ k := Nat.mul_le_mul_right _ (by omega)
  -- Goal: (b * F + a) * b^k + v1 < (b * F + c) * b^k + v2
  -- We have h_key: (b * F + a) * b^k + v1 < (b * F + c) * b^k
  -- Need to also handle the hlen substitution
  rw [← hlen]
  omega

/-- Helper: encodeList decreases when extending a prefix.
    If d2 is a proper prefix of d1 with bounded lengths and values,
    then encodeList d1 < encodeList d2.

    Intuition: d1 has more "real" values (≤ maxVal) where d2 has padding (maxVal + 1).
    Since padding values are larger, d2's encoding is larger. -/
lemma encodeList_prefix_lt (maxLen maxVal : ℕ) (d1 d2 : List ℕ)
    (h_prefix : d2 <+: d1) (h_ne : d1 ≠ d2)
    (h_len1 : d1.length ≤ maxLen) (h_len2 : d2.length ≤ maxLen)
    (h_val1 : ∀ x ∈ d1, x ≤ maxVal) (_h_val2 : ∀ x ∈ d2, x ≤ maxVal) :
    encodeList maxLen maxVal d1 < encodeList maxLen maxVal d2 := by
  -- d2 <+: d1 means d2 is a prefix of d1, i.e., d1 = d2 ++ suffix for some nonempty suffix
  obtain ⟨suffix, hsuffix⟩ := h_prefix
  have hsuffix_ne : suffix ≠ [] := by
    intro h_empty
    rw [h_empty, List.append_nil] at hsuffix
    exact h_ne hsuffix.symm
  obtain ⟨s0, srest, hsuffix_eq⟩ : ∃ s0 srest, suffix = s0 :: srest :=
    List.exists_cons_of_ne_nil hsuffix_ne
  rw [hsuffix_eq] at hsuffix
  -- Now d1 = d2 ++ s0 :: srest
  -- Define the padded versions
  let base := maxVal + 2
  let pad1 := d1 ++ List.replicate (maxLen - d1.length) (maxVal + 1)
  let pad2 := d2 ++ List.replicate (maxLen - d2.length) (maxVal + 1)
  -- pad1 = d2 ++ [s0] ++ srest ++ pad_suffix1
  -- pad2 = d2 ++ pad_suffix2
  -- At position |d2|: pad1 has s0 ≤ maxVal, pad2 has maxVal+1
  have hd1_eq : d1 = d2 ++ [s0] ++ srest := by simp [hsuffix, List.append_assoc]
  have hs0_bound : s0 ≤ maxVal := by
    apply h_val1
    rw [hd1_eq]
    simp
  have hs0_lt : s0 < maxVal + 1 := Nat.lt_succ_of_le hs0_bound
  -- pad1 = d2 ++ [s0] ++ (srest ++ replicate(maxLen - |d1|, maxVal+1))
  -- pad2 = d2 ++ [maxVal+1] ++ replicate(maxLen - |d2| - 1, maxVal+1)
  have hlen1 : d1.length = d2.length + 1 + srest.length := by
    rw [hd1_eq]
    simp only [List.length_append, List.length_singleton]
  have hpad2_ne : maxLen - d2.length ≠ 0 := by
    have h : d2.length < d1.length := by rw [hlen1]; omega
    omega
  obtain ⟨n2, hn2⟩ : ∃ n, maxLen - d2.length = n + 1 := Nat.exists_eq_succ_of_ne_zero hpad2_ne
  -- Define rest1 and rest2 for bigEndian_lt_of_first_diff
  let rest1 := srest ++ List.replicate (maxLen - d1.length) (maxVal + 1)
  let rest2 := List.replicate n2 (maxVal + 1)
  -- Show rest1.length = rest2.length
  have hrest_len : rest1.length = rest2.length := by
    simp only [rest1, rest2, List.length_append, List.length_replicate]
    -- Goal: srest.length + (maxLen - d1.length) = n2
    -- From hlen1: d1.length = d2.length + 1 + srest.length
    -- From hn2: maxLen - d2.length = n2 + 1, so n2 = maxLen - d2.length - 1
    -- Need to show:
    --   srest.length + (maxLen - (d2.length + 1 + srest.length)) = maxLen - d2.length - 1
    have h1 : maxLen - d1.length = maxLen - d2.length - 1 - srest.length := by
      rw [hlen1]; omega
    rw [h1]
    omega
  -- Show all elements of rest1 are < base = maxVal + 2
  have hrest1_bound : ∀ x ∈ rest1, x < base := by
    intro x hx
    simp only [rest1, List.mem_append, List.mem_replicate] at hx
    rcases hx with hx_srest | ⟨_, hx_pad⟩
    · -- x ∈ srest, so x ∈ d1, so x ≤ maxVal
      have h := h_val1 x (by rw [hd1_eq]; simp [hx_srest])
      omega
    · -- x = maxVal + 1
      rw [hx_pad]; omega
  -- Expand encodeList and use the decomposition
  simp only [encodeList]
  -- Rewrite the left side using hd1_eq
  have hpad1_eq : d1 ++ List.replicate (maxLen - d1.length) (maxVal + 1) = d2 ++ [s0] ++ rest1 := by
    simp only [rest1, hd1_eq]
    simp [List.append_assoc]
  -- Rewrite the right side
  have hpad2_eq : d2 ++ List.replicate (maxLen - d2.length) (maxVal + 1)
                = d2 ++ [maxVal + 1] ++ rest2 := by
    simp only [rest2, hn2]
    simp [List.append_assoc, List.replicate_succ]
  rw [hpad1_eq, hpad2_eq]
  have hbase : 1 < base := by omega
  exact bigEndian_lt_of_first_diff base hbase d2 rest1 rest2 s0 (maxVal + 1)
    hs0_lt hrest_len hrest1_bound

/-- Helper: encodeList decreases under List.Lex when d1 is not a prefix of d2.
    If List.Lex (· < ·) d1 d2 and d1 is not a prefix of d2, then there exists a first position
    where d1[k] < d2[k]. In big-endian encoding, this means d1's encoding is smaller.

    Note: This is a technical lemma for well-foundedness. The proof is involved because
    we need to track how padding interacts with the lexicographic structure. -/
lemma encodeList_lex_lt (maxLen maxVal : ℕ) (d1 d2 : List ℕ)
    (h_lex : List.Lex (· < ·) d1 d2)
    (h_not_prefix : ¬(d1 <+: d2))
    (h_len1 : d1.length ≤ maxLen) (h_len2 : d2.length ≤ maxLen)
    (h_val1 : ∀ x ∈ d1, x ≤ maxVal) (h_val2 : ∀ x ∈ d2, x ≤ maxVal) :
    encodeList maxLen maxVal d1 < encodeList maxLen maxVal d2 := by
  -- The proof proceeds by induction on the Lex structure.
  -- Key insight: padding to maxLen makes all lists have the same encoded "length",
  -- so lexicographic comparison transfers to numerical comparison.
  induction h_lex generalizing maxLen with
  | nil =>
    -- d1 = [], so d1 <+: d2, contradiction with h_not_prefix
    simp at h_not_prefix
  | @rel a l1 b l2 h_lt =>
    -- d1 = a :: l1, d2 = b :: l2 with a < b
    -- The first elements differ, so we use bigEndian_lt_of_first_diff
    simp only [encodeList]
    simp only [List.length_cons] at h_len1 h_len2
    -- Define rest lists with explicit padding calculations
    set rest1 := l1 ++ List.replicate (maxLen - l1.length - 1) (maxVal + 1) with hrest1_def
    set rest2 := l2 ++ List.replicate (maxLen - l2.length - 1) (maxVal + 1) with hrest2_def
    have hsub1 : maxLen - (l1.length + 1) = maxLen - l1.length - 1 := by omega
    have hsub2 : maxLen - (l2.length + 1) = maxLen - l2.length - 1 := by omega
    have hpad1 : (a :: l1) ++ List.replicate (maxLen - (a :: l1).length) (maxVal + 1)
               = [a] ++ rest1 := by simp [hrest1_def, hsub1]
    have hpad2 : (b :: l2) ++ List.replicate (maxLen - (b :: l2).length) (maxVal + 1)
               = [b] ++ rest2 := by simp [hrest2_def, hsub2]
    rw [hpad1, hpad2]
    have hrest_len : rest1.length = rest2.length := by
      simp only [hrest1_def, hrest2_def, List.length_append, List.length_replicate]
      omega
    have hrest1_bound : ∀ x ∈ rest1, x < maxVal + 2 := by
      intro x hx
      simp only [hrest1_def, List.mem_append, List.mem_replicate] at hx
      rcases hx with hx_l | ⟨_, hx_pad⟩
      · have h := h_val1 x (List.mem_cons_of_mem a hx_l); omega
      · omega
    have hbase : 1 < maxVal + 2 := by omega
    exact bigEndian_lt_of_first_diff (maxVal + 2) hbase [] rest1 rest2 a b
      h_lt hrest_len hrest1_bound
  | @cons a l1 l2 h_lex_tail ih =>
    -- d1 = a :: l1, d2 = a :: l2 with List.Lex (· < ·) l1 l2
    -- The first elements are equal, so we recurse on the tails
    have h_not_prefix' : ¬(l1 <+: l2) := by
      intro hpre
      apply h_not_prefix
      exact List.cons_prefix_cons.mpr ⟨rfl, hpre⟩
    simp only [List.length_cons] at h_len1 h_len2
    simp only [encodeList]
    -- Define rest lists
    set rest1 := l1 ++ List.replicate (maxLen - l1.length - 1) (maxVal + 1) with hrest1_def
    set rest2 := l2 ++ List.replicate (maxLen - l2.length - 1) (maxVal + 1) with hrest2_def
    have hsub1 : maxLen - (l1.length + 1) = maxLen - l1.length - 1 := by omega
    have hsub2 : maxLen - (l2.length + 1) = maxLen - l2.length - 1 := by omega
    have hpad1 : (a :: l1) ++ List.replicate (maxLen - (a :: l1).length) (maxVal + 1)
               = a :: rest1 := by simp [hrest1_def, hsub1]
    have hpad2 : (a :: l2) ++ List.replicate (maxLen - (a :: l2).length) (maxVal + 1)
               = a :: rest2 := by simp [hrest2_def, hsub2]
    rw [hpad1, hpad2]
    -- foldl (a :: rest) 0 = foldl rest a
    simp only [List.foldl_cons]
    -- Use foldl_base_mul_add: foldl L a = a * base^|L| + foldl L 0
    have hlen_rest : rest1.length = rest2.length := by
      simp only [hrest1_def, hrest2_def, List.length_append, List.length_replicate]
      omega
    -- Simplify initial value: (maxVal + 2) * 0 + a = a
    have hinit : (maxVal + 2) * 0 + a = a := by simp
    simp only [hinit]
    -- Goal: foldl rest1 a < foldl rest2 a
    -- Use foldl_base_mul_add: foldl L a = a * base^|L| + foldl L 0
    rw [show List.foldl (fun acc x ↦ (maxVal + 2) * acc + x) a rest1
          = a * (maxVal + 2) ^ rest1.length +
            List.foldl (fun acc x ↦ (maxVal + 2) * acc + x) 0 rest1
          from foldl_base_mul_add _ _ _,
        show List.foldl (fun acc x ↦ (maxVal + 2) * acc + x) a rest2
          = a * (maxVal + 2) ^ rest2.length +
            List.foldl (fun acc x ↦ (maxVal + 2) * acc + x) 0 rest2
          from foldl_base_mul_add _ _ _,
        hlen_rest]
    -- Goal: a * base^|rest2| + foldl rest1 0 < a * base^|rest2| + foldl rest2 0
    apply Nat.add_lt_add_left
    -- Now show foldl rest1 0 < foldl rest2 0 using induction
    -- rest1 = l1 ++ replicate(maxLen - 1 - l1.length, ...) = encodeList (maxLen - 1) l1
    have hlen_eq1 : maxLen - l1.length - 1 = (maxLen - 1) - l1.length := by omega
    have hlen_eq2 : maxLen - l2.length - 1 = (maxLen - 1) - l2.length := by omega
    have hrest1_enc : List.foldl (fun acc x => (maxVal + 2) * acc + x) 0 rest1
                    = encodeList (maxLen - 1) maxVal l1 := by
      simp only [encodeList, hrest1_def, hlen_eq1]
    have hrest2_enc : List.foldl (fun acc x => (maxVal + 2) * acc + x) 0 rest2
                    = encodeList (maxLen - 1) maxVal l2 := by
      simp only [encodeList, hrest2_def, hlen_eq2]
    rw [hrest1_enc, hrest2_enc]
    exact ih (maxLen - 1) h_not_prefix' (by omega) (by omega)
      (fun x hx => h_val1 x (List.mem_cons_of_mem a hx))
      (fun x hx => h_val2 x (List.mem_cons_of_mem a hx))

/-- Main encoding lemma: degSeqLt implies encoding decreases. -/
lemma encodeList_degSeqLt (maxLen maxVal : ℕ) (d1 d2 : List ℕ)
    (h_lt : degSeqLt d1 d2)
    (h_len1 : d1.length ≤ maxLen) (h_len2 : d2.length ≤ maxLen)
    (h_val1 : ∀ x ∈ d1, x ≤ maxVal) (h_val2 : ∀ x ∈ d2, x ≤ maxVal) :
    encodeList maxLen maxVal d1 < encodeList maxLen maxVal d2 := by
  rcases h_lt with ⟨h_prefix, h_ne⟩ | ⟨h_lex, h_not_prefix⟩
  · -- Case 1: d2 is a proper prefix of d1
    exact encodeList_prefix_lt maxLen maxVal d1 d2 h_prefix h_ne h_len1 h_len2 h_val1 h_val2
  · -- Case 2: List.Lex d1 d2 with ¬(d1 <+: d2)
    exact encodeList_lex_lt maxLen maxVal d1 d2 h_lex h_not_prefix h_len1 h_len2 h_val1 h_val2

/-- degSeqLt is well-founded for sequences of bounded length and bounded values.

    The proof uses the encoding to a natural number. For bounded sequences:
    - Length ≤ maxLen
    - Values ≤ maxVal
    We encode into ℕ using base (maxVal+2) with padding to length maxLen.

    The encoding decreases under degSeqLt because:
    1. Prefix case: longer sequences have smaller padding contribution
    2. Lex case: at first differing position, smaller value means smaller encoding -/
theorem degSeqLt_wf_bounded (maxLen maxVal : ℕ) :
    WellFounded (fun d1 d2 : List ℕ =>
      d1.length ≤ maxLen ∧ d2.length ≤ maxLen ∧
      (∀ x ∈ d1, x ≤ maxVal) ∧ (∀ x ∈ d2, x ≤ maxVal) ∧
      degSeqLt d1 d2) := by
  -- We prove this by showing every element is accessible via strong induction on encoding
  apply WellFounded.intro
  intro d
  -- Use strong induction on the encoding of d
  have h_enc := encodeList maxLen maxVal d
  generalize h_enc_eq : encodeList maxLen maxVal d = n at *
  induction n using Nat.strong_induction_on generalizing d with
  | _ n ih =>
    apply Acc.intro
    intro d' ⟨_, _, _, _, h_lt⟩
    -- Need to show encodeList d' < encodeList d = n
    -- This follows from encodeList_degSeqLt
    rename_i h_len1' h_len2' h_val1' h_val2'
    have h_enc_lt : encodeList maxLen maxVal d' < n := by
      rw [← h_enc_eq]
      exact encodeList_degSeqLt maxLen maxVal d' d h_lt h_len1' h_len2' h_val1' h_val2'
    exact ih (encodeList maxLen maxVal d') h_enc_lt d' rfl

/-- The partial order is well-founded.
    Proof: The order is a lexicographic product of:
    1. The reverse of the natural numbers (bounded by |V|) for |S|
    2. The ∞-padded lexicographic order on degree sequences

    Key observations:
    - |S| ≤ |V| for any partial IT S (so there are finitely many possible values)
    - Degree sequences have length ≤ |V| and values ≤ Δ ≤ |V| - 1
    - The ∞-padded lex order on bounded sequences is well-founded

    We use Prod.Lex with (Fintype.card V - S.ncard, encoding of degree sequence). -/
theorem PartitionedGraph.feasibleTuple_lt_wf : WellFounded (G.FeasibleTupleLt) := by
  -- Define a measure on feasible tuples
  let measure := fun (t : G.FeasibleTuple) =>
    (Fintype.card V - t.S.ncard, encodeList (Fintype.card V) (Fintype.card V)
      (G.degreeSeq t.S t.seq))
  -- Prod.Lex on (ℕ, ℕ) with < is well-founded
  have h_wf : WellFounded (Prod.Lex (· < ·) (· < ·) : ℕ × ℕ → ℕ × ℕ → Prop) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  -- Show FeasibleTupleLt is a subrelation of InvImage measure (Prod.Lex)
  apply Subrelation.wf _ (InvImage.wf measure h_wf)
  intro t1 t2 h_lt
  simp only [InvImage, FeasibleTupleLt] at h_lt ⊢
  rcases h_lt with h_ncard | ⟨h_eq, h_deg⟩
  · -- Case: t1.S.ncard > t2.S.ncard
    -- First component decreases
    left
    have h_bound : t1.S.ncard ≤ Fintype.card V := by
      have h1 : t1.S.ncard ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      rw [Set.ncard_univ, ← Fintype.card_eq_nat_card] at h1
      exact h1
    omega
  · -- Case: t1.S.ncard = t2.S.ncard and degSeqLt
    -- First component equal, second component (encoding) decreases
    -- Use Prod.Lex.right' which allows proving with ≤ on first component
    have h_first_eq : (Fintype.card V - t1.S.ncard) = (Fintype.card V - t2.S.ncard) := by omega
    -- The goal involves `measure t1` and `measure t2` which are let-bound
    -- Unfold and use Prod.Lex.right with the equality
    change Prod.Lex (· < ·) (· < ·)
      (Fintype.card V - t1.S.ncard,
        encodeList (Fintype.card V) (Fintype.card V) (G.degreeSeq t1.S t1.seq))
      (Fintype.card V - t2.S.ncard,
        encodeList (Fintype.card V) (Fintype.card V) (G.degreeSeq t2.S t2.seq))
    rw [h_first_eq]
    apply Prod.Lex.right
    -- Show encoding decreases under degSeqLt
    -- This is the key technical step: degSeqLt implies encoding decreases
    -- The encoding is designed so that:
    -- 1. Longer sequences (prefix case) have smaller encodings (padding with large values)
    -- 2. Lex-smaller sequences have smaller encodings (big-endian)
    -- The encoding preserves the order - this is the technical claim
    -- For a complete proof, we would need to verify the encoding properties
    -- Apply encodeList_degSeqLt to show encoding decreases
    -- Need: length bounds and value bounds
    have h_deg1 := G.degreeSeq t1.S t1.seq
    have h_deg2 := G.degreeSeq t2.S t2.seq
    -- Length of degreeSeq equals length of seq
    have hlen1 : (G.degreeSeq t1.S t1.seq).length = t1.seq.length := by
      simp only [degreeSeq, List.length_mapIdx]
    have hlen2 : (G.degreeSeq t2.S t2.seq).length = t2.seq.length := by
      simp only [degreeSeq, List.length_mapIdx]
    -- seq.length ≤ Fintype.card V by augmenting_seq_length_le
    have hseq1 : t1.seq.length ≤ Fintype.card V :=
      G.augmenting_seq_length_le t1.S t1.C t1.seq t1.isAugmenting
    have hseq2 : t2.seq.length ≤ Fintype.card V :=
      G.augmenting_seq_length_le t2.S t2.C t2.seq t2.isAugmenting
    -- So degreeSeq.length ≤ Fintype.card V
    have h_len1 : (G.degreeSeq t1.S t1.seq).length ≤ Fintype.card V := by rw [hlen1]; exact hseq1
    have h_len2 : (G.degreeSeq t2.S t2.seq).length ≤ Fintype.card V := by rw [hlen2]; exact hseq2
    -- Each element of degreeSeq is |N(v) ∩ S| ≤ |V| ≤ Fintype.card V
    have h_val1 : ∀ x ∈ G.degreeSeq t1.S t1.seq, x ≤ Fintype.card V := by
      intro x hx
      simp only [degreeSeq, List.mem_mapIdx] at hx
      obtain ⟨i, _, hi_eq⟩ := hx
      rw [← hi_eq]
      have hcard : (G.graph.neighborSet (t1.seq[i]) ∩ t1.S).ncard ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      rw [Set.ncard_univ, ← Fintype.card_eq_nat_card] at hcard
      exact hcard
    have h_val2 : ∀ x ∈ G.degreeSeq t2.S t2.seq, x ≤ Fintype.card V := by
      intro x hx
      simp only [degreeSeq, List.mem_mapIdx] at hx
      obtain ⟨i, _, hi_eq⟩ := hx
      rw [← hi_eq]
      have hcard : (G.graph.neighborSet (t2.seq[i]) ∩ t2.S).ncard ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      rw [Set.ncard_univ, ← Fintype.card_eq_nat_card] at hcard
      exact hcard
    exact encodeList_degSeqLt (Fintype.card V) (Fintype.card V)
      (G.degreeSeq t1.S t1.seq) (G.degreeSeq t2.S t2.seq) h_deg h_len1 h_len2 h_val1 h_val2

end PartialOrder

section BlocksIntersectingBound

variable (G : PartitionedGraph V)

/-- The number of blocks intersecting a set X is at most |X|.
    This holds because blocks are pairwise disjoint, so we can define
    an injection from blocksIntersecting X to X by picking a witness from each block.

    Proof idea:
    1. For each block U ∈ blocksIntersecting X, choose a witness x_U ∈ U ∩ X
    2. The map U ↦ x_U is injective (since blocks are disjoint)
    3. Therefore |blocksIntersecting X| ≤ |X| -/
lemma PartitionedGraph.blocksIntersecting_ncard_le (X : Set V) :
    (G.blocksIntersecting X).ncard ≤ X.ncard := by
  classical
  -- Handle the case where X is empty
  by_cases hX : X = ∅
  · -- When X = ∅, blocksIntersecting X = ∅
    have h_empty : G.blocksIntersecting X = ∅ := by
      simp only [blocksIntersecting, hX, Set.inter_empty]
      ext U
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      exact Set.not_nonempty_empty
    rw [h_empty, hX]
    simp only [Set.ncard_empty, le_refl]
  -- X is nonempty, so we can use an element as default
  have hXne : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hX
  -- Define a function that picks a witness from each block
  let f : Set V → V := fun U =>
    if h : (U ∩ X).Nonempty then h.some else hXne.some
  -- Show f maps blocksIntersecting X into X
  have hf_mem : ∀ U ∈ G.blocksIntersecting X, f U ∈ X := by
    intro U hU
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hU
    simp only [f, dif_pos hU.2]
    exact (hU.2.some_mem).2
  -- Show f is injective on blocksIntersecting X
  have hf_inj : Set.InjOn f (G.blocksIntersecting X) := by
    intro U₁ hU₁ U₂ hU₂ hf_eq
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hU₁ hU₂
    have hfU₁_mem : f U₁ ∈ U₁ := by
      simp only [f, dif_pos hU₁.2]
      exact (hU₁.2.some_mem).1
    have hfU₂_mem : f U₂ ∈ U₂ := by
      simp only [f, dif_pos hU₂.2]
      exact (hU₂.2.some_mem).1
    -- Use pairwise disjointness
    by_contra h_ne
    have h_disj := G.pairwiseDisjoint hU₁.1 hU₂.1 h_ne
    exact Set.disjoint_left.mp h_disj hfU₁_mem (hf_eq ▸ hfU₂_mem)
  -- Apply the cardinality lemma
  exact Set.ncard_le_ncard_of_injOn f hf_mem hf_inj (Set.toFinite X)

/-- For a subset X of a partial IT S, the number of blocks intersecting X equals |X|.
    This is because each vertex in X is in a distinct block (partial IT property).

    Proof idea:
    1. The upper bound |blocksIntersecting X| ≤ |X| is from blocksIntersecting_ncard_le
    2. For the lower bound, define g : X → blocksIntersecting X by g(x) = blockOf x
    3. g is well-defined: x ∈ X ∩ blockOf x, so blockOf x ∈ blocksIntersecting X
    4. g is injective: if x₁ ≠ x₂ but blockOf x₁ = blockOf x₂, then x₁, x₂ ∈ S ∩ U
       for some block U, contradicting |S ∩ U| ≤ 1
    5. Therefore |X| ≤ |blocksIntersecting X|, giving equality -/
lemma PartitionedGraph.blocksIntersecting_ncard_eq_of_subset_partialIT (X S : Set V)
    (hS : G.IsPartialIT S) (hX : X ⊆ S) :
    (G.blocksIntersecting X).ncard = X.ncard := by
  apply Nat.le_antisymm
  · -- Upper bound: from blocksIntersecting_ncard_le
    exact G.blocksIntersecting_ncard_le X
  · -- Lower bound: construct injection from X to blocksIntersecting X
    classical
    by_cases hXne : X.Nonempty
    · -- Define g(x) = blockOf x
      let g : V → Set V := fun x => G.blockOf x
      -- Show g maps X into blocksIntersecting X
      have hg_mem : ∀ x ∈ X, g x ∈ G.blocksIntersecting X := by
        intro x hx
        simp only [blocksIntersecting, Set.mem_setOf_eq]
        constructor
        · exact G.blockOf_mem x
        · exact ⟨x, G.mem_blockOf x, hx⟩
      -- Show g is injective on X (using partial IT property)
      have hg_inj : Set.InjOn g X := by
        intro x₁ hx₁ x₂ hx₂ hg_eq
        -- If blockOf x₁ = blockOf x₂, then x₁, x₂ ∈ S ∩ blockOf x₁
        by_contra hne
        have hx₁_S : x₁ ∈ S := hX hx₁
        have hx₂_S : x₂ ∈ S := hX hx₂
        have hx₁_mem : x₁ ∈ S ∩ G.blockOf x₁ := ⟨hx₁_S, G.mem_blockOf x₁⟩
        have hx₂_in_block : x₂ ∈ G.blockOf x₁ := by
          have : G.blockOf x₁ = G.blockOf x₂ := hg_eq
          rw [this]
          exact G.mem_blockOf x₂
        have hx₂_mem : x₂ ∈ S ∩ G.blockOf x₁ := ⟨hx₂_S, hx₂_in_block⟩
        -- S ∩ blockOf x₁ has at least 2 elements
        have h_two : 2 ≤ (S ∩ G.blockOf x₁).ncard := by
          have h_pair : ({x₁, x₂} : Set V) ⊆ S ∩ G.blockOf x₁ := by
            intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact hx₁_mem
            · exact hx₂_mem
          have h_card_pair : ({x₁, x₂} : Set V).ncard = 2 := Set.ncard_pair hne
          calc 2 = ({x₁, x₂} : Set V).ncard := h_card_pair.symm
            _ ≤ (S ∩ G.blockOf x₁).ncard := Set.ncard_le_ncard h_pair (Set.toFinite _)
        -- But S is a partial IT, so |S ∩ U| ≤ 1 for any block U
        have h_one := hS.2 (G.blockOf x₁) (G.blockOf_mem x₁)
        omega
      -- Apply cardinality lemma for injective functions
      exact Set.ncard_le_ncard_of_injOn g hg_mem hg_inj (Set.toFinite _)
    · -- X is empty
      rw [Set.not_nonempty_iff_eq_empty] at hXne
      simp only [hXne, Set.ncard_empty]
      exact Nat.zero_le _

end BlocksIntersectingBound

section BlocksSeqSubset

variable (G : PartitionedGraph V)

omit [Fintype V] in
/-- blocksIntersecting X is a subset of partition.blocks. -/
lemma PartitionedGraph.blocksIntersecting_subset (X : Set V) :
    G.blocksIntersecting X ⊆ G.blocks := by
  intro U hU
  simp only [blocksIntersecting, Set.mem_setOf_eq] at hU
  exact hU.1

omit [Fintype V] in
/-- uncoveredBlocks S is a subset of partition.blocks. -/
lemma PartitionedGraph.uncoveredBlocks_subset (S : Set V) :
    G.uncoveredBlocks S ⊆ G.blocks := by
  intro U hU
  simp only [uncoveredBlocks] at hU
  exact Set.mem_of_mem_diff hU

omit [Fintype V] in
/-- blocksSeq at any step is a subset of partition.blocks. -/
lemma PartitionedGraph.blocksSeq_subset (S : Set V) (seq : List V) (k : ℕ) :
    G.blocksSeq S seq k ⊆ G.blocks := by
  induction k with
  | zero => exact G.uncoveredBlocks_subset S
  | succ k ih =>
    simp only [blocksSeq]
    cases hseq : seq[k]? with
    | none => exact G.uncoveredBlocks_subset S
    | some v =>
      intro U hU
      simp only [Set.mem_union] at hU
      rcases hU with hU_k | hU_new
      · exact ih hU_k
      · exact G.blocksIntersecting_subset _ hU_new

omit [Fintype V] in
/-- blocksSeq is monotonically increasing within sequence bounds: blocksSeq k ⊆ blocksSeq (k+1). -/
lemma PartitionedGraph.blocksSeq_mono (S : Set V) (seq : List V) (k : ℕ) (hk : k < seq.length) :
    G.blocksSeq S seq k ⊆ G.blocksSeq S seq (k + 1) := by
  simp only [blocksSeq]
  have hseq : seq[k]? = some seq[k] := List.getElem?_eq_getElem hk
  simp only [hseq]
  exact Set.subset_union_left

omit [Fintype V] in
/-- blocksSeq is monotonically increasing within sequence bounds. -/
lemma PartitionedGraph.blocksSeq_mono' (S : Set V) (seq : List V) {j k : ℕ} (hjk : j ≤ k)
    (hk : k ≤ seq.length) :
    G.blocksSeq S seq j ⊆ G.blocksSeq S seq k := by
  induction hjk with
  | refl => exact fun _ h => h
  | @step m _ ih =>
    have hm : m < seq.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk
    have ih' := ih (Nat.le_of_lt hm)
    exact fun U hU => G.blocksSeq_mono S seq m hm (ih' hU)

omit [Fintype V] in
/-- blocksSeq always contains uncoveredBlocks (B_0) within sequence bounds. -/
lemma PartitionedGraph.uncoveredBlocks_subset_blocksSeq (S : Set V) (seq : List V) (k : ℕ)
    (hk : k ≤ seq.length) :
    G.uncoveredBlocks S ⊆ G.blocksSeq S seq k := by
  have h0 : G.blocksSeq S seq 0 = G.uncoveredBlocks S := rfl
  rw [← h0]
  exact G.blocksSeq_mono' S seq (Nat.zero_le k) hk

omit [Fintype V] in
/-- When B ⊆ partition.blocks, blockUnion B = ⋃₀ B. -/
lemma PartitionedGraph.blockUnion_eq_sUnion {B : Set (Set V)} (hB : B ⊆ G.blocks) :
    G.blockUnion B = ⋃₀ B := by
  simp only [blockUnion]
  congr 1
  exact Set.inter_eq_self_of_subset_left hB

/-- The ncard of blockUnion is at least t times the number of blocks when each block
    has size ≥ t. -/
lemma PartitionedGraph.ncard_blockUnion_ge_of_thick {B : Set (Set V)} (hB : B ⊆ G.blocks)
    (hB_fin : B.Finite) (t : ℕ) (h_thick : ∀ U ∈ B, t ≤ U.ncard) :
    t * B.ncard ≤ (G.blockUnion B).ncard := by
  classical
  rw [G.blockUnion_eq_sUnion hB]
  -- Convert to biUnion
  have h_eq : ⋃₀ B = ⋃ U ∈ B, U := Set.sUnion_eq_biUnion
  rw [h_eq]
  -- Blocks are pairwise disjoint
  have h_disj : B.PairwiseDisjoint id := fun U hU W hW hne =>
    G.pairwiseDisjoint (hB hU) (hB hW) hne
  -- Each block is finite (subset of a Fintype)
  have h_each_fin : ∀ U ∈ B, U.Finite := fun U _ => Set.toFinite U
  -- Apply Finite.ncard_biUnion for equality
  rw [Set.Finite.ncard_biUnion hB_fin h_each_fin h_disj]
  -- Now: t * B.ncard ≤ ∑ᶠ U ∈ B, U.ncard
  rw [finsum_mem_eq_finite_toFinset_sum _ hB_fin]
  have h_card_eq : B.ncard = hB_fin.toFinset.card := Set.ncard_eq_toFinset_card B hB_fin
  rw [h_card_eq, mul_comm]
  apply Finset.card_nsmul_le_sum
  intro U hU
  simp only [Set.Finite.mem_toFinset] at hU
  exact h_thick U hU

end BlocksSeqSubset

section Bounds

variable (G : PartitionedGraph V)

omit [Fintype V] in
/-- Equation 2.1: |C_k| ≤ |C| + k + Σᵢ₌₁ᵏ dᵢ(v).
    Proof by induction on k:
    - Base case: C_0 = C, so |C_0| = |C|
    - Inductive step: C_{k+1} = C_k ∪ N(v_{k+1}) ∪ {v_{k+1}}
      |C_{k+1}| ≤ |C_k| + |N(v_{k+1}) ∩ S| + 1 -/
lemma PartitionedGraph.vertexSeq_card_bound (t : G.FeasibleTuple) (k : ℕ)
    (hk : k ≤ t.seq.length) :
    (G.vertexSeq t.S t.C t.seq k).ncard ≤
      t.C.ncard + k + ((G.degreeSeq t.S t.seq).take k).sum := by
  induction k with
  | zero =>
    simp only [vertexSeq, List.take_zero, List.sum_nil, add_zero]
    exact le_refl _
  | succ k ih =>
    -- Need to handle the case split in vertexSeq definition
    simp only [vertexSeq]
    cases hseq : t.seq[k]? with
    | none =>
      -- If sequence is too short, vertexSeq returns C
      -- C.ncard ≤ C.ncard + (k+1) + sum trivially holds
      have h1 : t.C.ncard ≤ t.C.ncard + (k + 1) := Nat.le_add_right _ _
      have h2 : t.C.ncard + (k + 1) ≤
          t.C.ncard + (k + 1) + ((G.degreeSeq t.S t.seq).take (k + 1)).sum :=
        Nat.le_add_right _ _
      exact Nat.le_trans h1 h2
    | some v =>
      -- C_{k+1} = C_k ∪ (N(v) ∩ S) ∪ {v}
      -- |C_{k+1}| ≤ |C_k| + |N(v) ∩ S| + 1
      -- By IH: |C_k| ≤ |C| + k + Σᵢ₌₁ᵏ dᵢ
      -- d_{k+1} = |N(v) ∩ S| by definition of degreeSeq
      have h_le_k : k ≤ t.seq.length := Nat.le_of_succ_le hk
      have ih' := ih h_le_k
      -- Union bound: |A ∪ B ∪ C| ≤ |A| + |B| + |C|
      have h_union : (G.vertexSeq t.S t.C t.seq k ∪ (G.graph.neighborSet v ∩ t.S) ∪ {v}).ncard ≤
          (G.vertexSeq t.S t.C t.seq k).ncard +
          (G.graph.neighborSet v ∩ t.S).ncard + 1 := by
        calc (G.vertexSeq t.S t.C t.seq k ∪ (G.graph.neighborSet v ∩ t.S) ∪ {v}).ncard
          ≤ (G.vertexSeq t.S t.C t.seq k ∪ (G.graph.neighborSet v ∩ t.S)).ncard +
              ({v} : Set V).ncard := Set.ncard_union_le _ _
          _ ≤ (G.vertexSeq t.S t.C t.seq k).ncard +
              (G.graph.neighborSet v ∩ t.S).ncard + ({v} : Set V).ncard := by
            apply Nat.add_le_add_right
            exact Set.ncard_union_le _ _
          _ = _ := by simp only [Set.ncard_singleton]
      -- The key step: relate sum(take (k+1)) to sum(take k) + degree at k
      -- degreeSeq[k] = |N(seq[k]) ∩ S| by definition of mapIdx
      -- Get the index k in the sequence
      have hk_lt : k < t.seq.length := by
        have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hseq
        exact hlt
      -- degreeSeq has the same length as seq
      have h_deg_len : (G.degreeSeq t.S t.seq).length = t.seq.length := by
        simp only [degreeSeq, List.length_mapIdx]
      -- k < degreeSeq.length
      have hk_lt_deg : k < (G.degreeSeq t.S t.seq).length := by
        rw [h_deg_len]; exact hk_lt
      -- Use sum_take_succ: sum(take (k+1)) = sum(take k) + degreeSeq[k]
      have h_sum : ((G.degreeSeq t.S t.seq).take (k + 1)).sum =
          ((G.degreeSeq t.S t.seq).take k).sum + (G.degreeSeq t.S t.seq)[k] :=
        List.sum_take_succ (G.degreeSeq t.S t.seq) k hk_lt_deg
      -- degreeSeq[k] = |N(seq[k]) ∩ S| = |N(v) ∩ S|
      have h_deg_eq : (G.degreeSeq t.S t.seq)[k] = (G.graph.neighborSet v ∩ t.S).ncard := by
        change (List.mapIdx (fun _ w => (G.graph.neighborSet w ∩ t.S).ncard) t.seq)[k]'(by
          simpa only [List.length_mapIdx] using hk_lt) = _
        rw [List.getElem_mapIdx]
        -- seq[k] = v from hseq
        have ⟨_, hv_eq⟩ := List.getElem?_eq_some_iff.mp hseq
        rw [hv_eq]
      -- Combine everything
      calc (G.vertexSeq t.S t.C t.seq k ∪ (G.graph.neighborSet v ∩ t.S) ∪ {v}).ncard
        ≤ (G.vertexSeq t.S t.C t.seq k).ncard + (G.graph.neighborSet v ∩ t.S).ncard + 1 := h_union
        _ ≤ (t.C.ncard + k + ((G.degreeSeq t.S t.seq).take k).sum) +
            (G.graph.neighborSet v ∩ t.S).ncard + 1 := by
          apply Nat.add_le_add_right
          apply Nat.add_le_add_right
          exact ih'
        _ = t.C.ncard + k + ((G.degreeSeq t.S t.seq).take k).sum +
            (G.graph.neighborSet v ∩ t.S).ncard + 1 := by omega
        _ = t.C.ncard + k + (((G.degreeSeq t.S t.seq).take k).sum +
            (G.graph.neighborSet v ∩ t.S).ncard) + 1 := by omega
        _ = t.C.ncard + k + (((G.degreeSeq t.S t.seq).take k).sum +
            (G.degreeSeq t.S t.seq)[k]) + 1 := by rw [h_deg_eq]
        _ = t.C.ncard + k + ((G.degreeSeq t.S t.seq).take (k + 1)).sum + 1 := by rw [h_sum]
        _ = t.C.ncard + (k + 1) + ((G.degreeSeq t.S t.seq).take (k + 1)).sum := by omega

/-- Equation 2.1 (upper bound): |B_k| ≤ |U \ U_S| + Σᵢ₌₁ᵏ dᵢ(v).
    The equality in the paper relies on specific properties of augmenting sequences.
    For now, we prove the upper bound by induction. -/
lemma PartitionedGraph.blocksSeq_card_bound (t : G.FeasibleTuple) (k : ℕ)
    (hk : k ≤ t.seq.length) :
    (G.blocksSeq t.S t.seq k).ncard ≤
      (G.uncoveredBlocks t.S).ncard + ((G.degreeSeq t.S t.seq).take k).sum := by
  induction k with
  | zero =>
    simp only [blocksSeq, List.take_zero, List.sum_nil, add_zero]
    exact le_refl _
  | succ k ih =>
    simp only [blocksSeq]
    cases hseq : t.seq[k]? with
    | none =>
      -- If sequence is too short, blocksSeq returns uncoveredBlocks
      have h1 : (G.uncoveredBlocks t.S).ncard ≤
          (G.uncoveredBlocks t.S).ncard + ((G.degreeSeq t.S t.seq).take (k + 1)).sum :=
        Nat.le_add_right _ _
      exact h1
    | some v =>
      -- B_{k+1} = B_k ∪ blocksIntersecting(N(v) ∩ S)
      have h_le_k : k ≤ t.seq.length := Nat.le_of_succ_le hk
      have ih' := ih h_le_k
      -- Get k < seq.length from hseq
      have hk_lt : k < t.seq.length := by
        have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hseq
        exact hlt
      have h_deg_len : (G.degreeSeq t.S t.seq).length = t.seq.length := by
        simp only [degreeSeq, List.length_mapIdx]
      have hk_lt_deg : k < (G.degreeSeq t.S t.seq).length := by
        rw [h_deg_len]; exact hk_lt
      -- sum(take (k+1)) = sum(take k) + degreeSeq[k]
      have h_sum : ((G.degreeSeq t.S t.seq).take (k + 1)).sum =
          ((G.degreeSeq t.S t.seq).take k).sum + (G.degreeSeq t.S t.seq)[k] :=
        List.sum_take_succ (G.degreeSeq t.S t.seq) k hk_lt_deg
      -- degreeSeq[k] = |N(v) ∩ S|
      have h_deg_eq : (G.degreeSeq t.S t.seq)[k] = (G.graph.neighborSet v ∩ t.S).ncard := by
        change (List.mapIdx (fun _ w => (G.graph.neighborSet w ∩ t.S).ncard) t.seq)[k]'(by
          simpa only [List.length_mapIdx] using hk_lt) = _
        rw [List.getElem_mapIdx]
        have ⟨_, hv_eq⟩ := List.getElem?_eq_some_iff.mp hseq
        rw [hv_eq]
      -- Key bound: |blocksIntersecting X| ≤ |X| (each vertex is in at most one block)
      have h_blocks_bound : (G.blocksIntersecting (G.graph.neighborSet v ∩ t.S)).ncard ≤
          (G.graph.neighborSet v ∩ t.S).ncard := by
        -- Each block in blocksIntersecting X contains at least one element of X
        -- Since blocks are pairwise disjoint, different blocks contain different elements
        -- We can define an injection from blocksIntersecting X to X
        apply G.blocksIntersecting_ncard_le
      -- Union bound for sets of sets
      have h_union : (G.blocksSeq t.S t.seq k ∪
          G.blocksIntersecting (G.graph.neighborSet v ∩ t.S)).ncard ≤
          (G.blocksSeq t.S t.seq k).ncard +
          (G.blocksIntersecting (G.graph.neighborSet v ∩ t.S)).ncard :=
        Set.ncard_union_le _ _
      -- Combine everything
      calc (G.blocksSeq t.S t.seq k ∪ G.blocksIntersecting (G.graph.neighborSet v ∩ t.S)).ncard
        ≤ (G.blocksSeq t.S t.seq k).ncard +
            (G.blocksIntersecting (G.graph.neighborSet v ∩ t.S)).ncard := h_union
        _ ≤ (G.blocksSeq t.S t.seq k).ncard + (G.graph.neighborSet v ∩ t.S).ncard := by
          apply Nat.add_le_add_left; exact h_blocks_bound
        _ ≤ ((G.uncoveredBlocks t.S).ncard + ((G.degreeSeq t.S t.seq).take k).sum) +
            (G.graph.neighborSet v ∩ t.S).ncard := by
          apply Nat.add_le_add_right; exact ih'
        _ = (G.uncoveredBlocks t.S).ncard + ((G.degreeSeq t.S t.seq).take k).sum +
            (G.graph.neighborSet v ∩ t.S).ncard := by omega
        _ = (G.uncoveredBlocks t.S).ncard + (((G.degreeSeq t.S t.seq).take k).sum +
            (G.graph.neighborSet v ∩ t.S).ncard) := by omega
        _ = (G.uncoveredBlocks t.S).ncard + (((G.degreeSeq t.S t.seq).take k).sum +
            (G.degreeSeq t.S t.seq)[k]) := by rw [h_deg_eq]
        _ = (G.uncoveredBlocks t.S).ncard + ((G.degreeSeq t.S t.seq).take (k + 1)).sum := by
          rw [h_sum]

/-- **Key Equality (Equation 2.1)**: For augmenting sequences with partial IT S,
    |B_k| = |uncovered| + Σ_{i<k} d_i.
    This is an equality (not just an upper bound) because:
    1. The new blocks at each step are disjoint from previous blocks
    2. The number of new blocks equals the degree d_k -/
lemma PartitionedGraph.blocksSeq_card_eq (S C : Set V) (seq : List V)
    (hS : G.IsPartialIT S) (haug : G.IsAugmenting S C seq)
    (k : ℕ) (hk : k ≤ seq.length) :
    (G.blocksSeq S seq k).ncard =
      (G.uncoveredBlocks S).ncard + ((G.degreeSeq S seq).take k).sum := by
  induction k with
  | zero =>
    simp only [blocksSeq, List.take_zero, List.sum_nil, add_zero]
  | succ k ih =>
    simp only [blocksSeq]
    have hk_lt : k < seq.length := Nat.lt_of_succ_le hk
    have h_le_k : k ≤ seq.length := Nat.le_of_lt hk_lt
    cases hseq : seq[k]? with
    | none =>
      -- seq[k]? = none contradicts k < seq.length
      exact (Option.some_ne_none _ ((List.getElem?_eq_getElem hk_lt).symm.trans hseq)).elim
    | some v =>
      -- Simplify the match expression
      simp only
      -- Extract v = seq[k]
      have h_v_eq : seq[k] = v := by
        have h := List.getElem?_eq_getElem hk_lt
        simp only [hseq] at h
        exact (Option.some_injective _ h).symm
      -- The new blocks are disjoint from B_k
      have h_disj : Disjoint (G.blocksIntersecting (G.graph.neighborSet seq[k] ∩ S))
          (G.blocksSeq S seq k) := G.augmenting_blocksSeq_disjoint S C seq hS haug k hk_lt
      rw [h_v_eq] at h_disj
      -- For disjoint finite sets, |A ∪ B| = |A| + |B|
      have h_union_eq : (G.blocksSeq S seq k ∪
          G.blocksIntersecting (G.graph.neighborSet v ∩ S)).ncard =
          (G.blocksSeq S seq k).ncard +
          (G.blocksIntersecting (G.graph.neighborSet v ∩ S)).ncard := by
        rw [Set.ncard_union_eq (h_disj.symm) (Set.toFinite _) (Set.toFinite _)]
      -- |blocksIntersecting(N_S(v))| = |N_S(v)| because N_S(v) ⊆ S and S is partial IT
      have h_NS_subset : G.graph.neighborSet v ∩ S ⊆ S := Set.inter_subset_right
      have h_blocks_eq : (G.blocksIntersecting (G.graph.neighborSet v ∩ S)).ncard =
          (G.graph.neighborSet v ∩ S).ncard :=
        G.blocksIntersecting_ncard_eq_of_subset_partialIT _ S hS h_NS_subset
      -- degreeSeq[k] = |N(v) ∩ S|
      have h_deg_len : (G.degreeSeq S seq).length = seq.length := by
        simp only [degreeSeq, List.length_mapIdx]
      have hk_lt_deg : k < (G.degreeSeq S seq).length := by
        rw [h_deg_len]; exact hk_lt
      have h_deg_eq : (G.degreeSeq S seq)[k] = (G.graph.neighborSet v ∩ S).ncard := by
        simp only [degreeSeq, List.getElem_mapIdx, h_v_eq]
      -- sum(take (k+1)) = sum(take k) + degreeSeq[k]
      have h_sum : ((G.degreeSeq S seq).take (k + 1)).sum =
          ((G.degreeSeq S seq).take k).sum + (G.degreeSeq S seq)[k] :=
        List.sum_take_succ (G.degreeSeq S seq) k hk_lt_deg
      -- Apply IH
      have ih' := ih h_le_k
      calc (G.blocksSeq S seq k ∪ G.blocksIntersecting (G.graph.neighborSet v ∩ S)).ncard
        _ = (G.blocksSeq S seq k).ncard +
            (G.blocksIntersecting (G.graph.neighborSet v ∩ S)).ncard := h_union_eq
        _ = (G.blocksSeq S seq k).ncard + (G.graph.neighborSet v ∩ S).ncard := by rw [h_blocks_eq]
        _ = ((G.uncoveredBlocks S).ncard + ((G.degreeSeq S seq).take k).sum) +
            (G.graph.neighborSet v ∩ S).ncard := by rw [ih']
        _ = (G.uncoveredBlocks S).ncard + (((G.degreeSeq S seq).take k).sum +
            (G.graph.neighborSet v ∩ S).ncard) := by omega
        _ = (G.uncoveredBlocks S).ncard + (((G.degreeSeq S seq).take k).sum +
            (G.degreeSeq S seq)[k]) := by rw [h_deg_eq]
        _ = (G.uncoveredBlocks S).ncard + ((G.degreeSeq S seq).take (k + 1)).sum := by rw [h_sum]

end Bounds

end IndependentTransversals
