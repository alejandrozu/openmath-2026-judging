/-
Copyright (c) 2025 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import IndependentTransversals.AugmentingSequences

/-! Attributed additive adaptation of the pure augmenting-sequence proof.
The thickness-based extension step is replaced by the explicit sufficient
no-small-total-domination condition; the IT conclusion is proved by the
same well-founded argument. No independent transversal is assumed. -/
namespace IndependentTransversals
variable {V : Type*} [DecidableEq V] [Fintype V]
section Haxell
variable (G : PartitionedGraph V) [DecidableRel G.graph.Adj]
/-- A sufficient non-domination condition, independent of a degree bound.
It is a known Haxell-type criterion, not a new Robert Huynh result. -/
def PartitionedGraph.NoSmallTotalDomination : Prop :=
  ∀ B : Set (Set V), B ⊆ G.blocks → B.Nonempty →
    ∀ D : Set V, D.ncard ≤ 2 * (B.ncard - 1) →
      ∃ v ∈ G.blockUnion B, Disjoint (G.graph.neighborSet v) D

lemma PartitionedGraph.can_extend_without_domination (t : G.FeasibleTuple)
    (h_nodom : G.NoSmallTotalDomination)
    (h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1))
    (h_not_full : (G.uncoveredBlocks t.S).Nonempty)
    (h_C_empty : t.C = ∅) :
    ∃ v ∈ G.blockUnion (G.blocksSeq t.S t.seq t.seq.length),
      Disjoint (G.graph.neighborSet v) (G.vertexSeq t.S t.C t.seq t.seq.length) := by
  let m := t.seq.length
  let B_m := G.blocksSeq t.S t.seq m
  let C_m := G.vertexSeq t.S t.C t.seq m
  let deg_sum := ((G.degreeSeq t.S t.seq).take m).sum
  have h_Bm_nonempty : B_m.Nonempty :=
    Set.Nonempty.mono (G.uncoveredBlocks_subset_blocksSeq t.S t.seq m (le_refl m)) h_not_full
  have h_Bm_eq : B_m.ncard = (G.uncoveredBlocks t.S).ncard + deg_sum :=
    G.blocksSeq_card_eq t.S t.C t.seq t.isPartialIT t.isAugmenting m (le_refl m)
  have h_sum_ge_m : m ≤ deg_sum := by
    -- Each degree d_i > 0 for i < m
    -- degreeSeq has length = seq.length = m
    have h_deg_len : (G.degreeSeq t.S t.seq).length = m := by
      simp only [degreeSeq, List.length_mapIdx, m]
    have h_take_all : (G.degreeSeq t.S t.seq).take m = G.degreeSeq t.S t.seq := by
      exact List.take_of_length_le (le_of_eq h_deg_len)
    simp only [deg_sum, h_take_all]
    -- Now show: m ≤ (degreeSeq t.S t.seq).sum
    -- Each element of degreeSeq is > 0, so sum ≥ length = m
    have h_all_pos' : ∀ i (hi : i < (G.degreeSeq t.S t.seq).length),
        0 < (G.degreeSeq t.S t.seq)[i] := by
      intro i hi
      rw [h_deg_len] at hi
      simp only [degreeSeq, List.getElem_mapIdx]
      -- degreeAt t.S t.seq (i + 1) = N(seq[i]) ∩ S).ncard
      simp only [degreeAt] at h_all_pos
      have h_seq_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
        simp only [Nat.add_sub_cancel]
        exact List.getElem?_eq_getElem hi
      specialize h_all_pos i hi
      simp only [h_seq_idx] at h_all_pos
      exact h_all_pos
    -- Sum of positive naturals is at least the count
    have h_sum_ge : (G.degreeSeq t.S t.seq).length ≤ (G.degreeSeq t.S t.seq).sum := by
      have : ∀ l : List ℕ, (∀ i (hi : i < l.length), 0 < l[i]) → l.length ≤ l.sum := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons x xs ih =>
          intro h_pos
          simp only [List.length_cons, List.sum_cons]
          have h_x_pos : 0 < x :=
            h_pos 0 (by simp only [List.length_cons]; omega)
          have h_ih : xs.length ≤ xs.sum :=
            ih (fun i hi =>
              h_pos (i + 1) (by simp only [List.length_cons]; omega))
          omega
      exact this _ h_all_pos'
    rw [h_deg_len] at h_sum_ge
    exact h_sum_ge
  have h_Cm_bound := G.vertexSeq_card_bound t m (le_refl m)
  have h_C_zero : t.C.ncard = 0 := by simp [h_C_empty]
  have h_Cm_bound' : C_m.ncard ≤ m + deg_sum := by
    simpa only [h_C_zero, zero_add] using h_Cm_bound
  have h_uncovered_pos : 0 < (G.uncoveredBlocks t.S).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 h_not_full
  have h_small : C_m.ncard ≤ 2 * (B_m.ncard - 1) := by omega
  exact h_nodom B_m (G.blocksSeq_subset t.S t.seq m) h_Bm_nonempty C_m h_small

lemma list_lex_of_prefix_and_lt {l1 l2 : List ℕ} {k : ℕ}
    (hk_lt_l1 : k < l1.length) (hk_lt_l2 : k < l2.length)
    (h_eq : ∀ i (hi : i < k), l1[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_l1)) =
                              l2[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_l2)))
    (h_lt : l1[k] < l2[k]) :
    List.Lex (· < ·) l1 l2 := by
  -- Prove by strong induction on k
  induction k generalizing l1 l2 with
  | zero =>
    -- k = 0: l1[0] < l2[0], use List.Lex.rel
    match l1, l2 with
    | a :: l1', b :: l2' =>
      simp only [List.getElem_cons_zero] at *
      exact List.Lex.rel h_lt
    | [], _ => simp at hk_lt_l1
    | _, [] => simp at hk_lt_l2
  | succ k' ih =>
    -- k = k' + 1: first elements equal, recurse on tails
    match l1, l2 with
    | a :: l1', b :: l2' =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk_lt_l1 hk_lt_l2
      -- a = b (from h_eq at i = 0)
      have hab : a = b := by
        have h0 := h_eq 0 (Nat.zero_lt_succ k')
        simp only [List.getElem_cons_zero] at h0
        exact h0
      rw [hab]
      apply List.Lex.cons
      -- Apply induction on tails
      apply ih hk_lt_l1 hk_lt_l2
      · intro i hi
        have h_succ := h_eq (i + 1) (Nat.add_lt_add_right hi 1)
        simp only [List.getElem_cons_succ] at h_succ
        convert h_succ using 2
      · simp only [List.getElem_cons_succ] at h_lt ⊢
        convert h_lt using 2
    | [], _ => simp at hk_lt_l1
    | _, [] => simp at hk_lt_l2

/-- Helper lemma: l1 is not a prefix of l2 if they differ at position k. -/
lemma not_prefix_of_ne_at {l1 l2 : List ℕ} {k : ℕ}
    (hk_lt_l1 : k < l1.length)
    (hk_lt_l2 : k < l2.length)
    (h_ne : l1[k] ≠ l2[k]) :
    ¬(l1 <+: l2) := by
  intro h_prefix
  have h_eq := List.IsPrefix.getElem h_prefix hk_lt_l1
  exact h_ne h_eq

omit [DecidableRel G.graph.Adj] in
/-- If d_m = 0, we can improve the partial IT or reduce the sequence.

    Proof outline (from the paper):
    Since d_m = 0, the last vertex v_m has no neighbors in S (N_S(v_m) = ∅).
    This means v_m is independent from S.

    Let k be the smallest index for which v_m ∈ V_{B_k}.

    Case 1 (k = 0): v_m is in an uncovered block.
      Then S' = S ∪ {v_m} is a strictly larger partial IT.
      The tuple (S', ∅, []) has |S'| > |S|.

    Case 2 (k ≥ 1): v_m is in a block U that was added at step k.
      This means U ∈ blocksIntersecting(N_S(v_k)), so there exists s ∈ S ∩ U ∩ N(v_k).
      Since d_m = 0, we have v_m ≁ s (v_m has no S-neighbors).
      Let S' = S ⊕ v_m = (S \ U) ∪ {v_m} (replace s with v_m).
      Let seq' = (v_1, ..., v_k) (truncate the sequence).
      Then |S'| = |S| and d_i(seq') = d_i(seq) for i < k, but d_k(seq') = d_k(seq) - 1
      because s was the unique S-neighbor of v_k in U. -/
lemma PartitionedGraph.improve_from_zero_degree (t : G.FeasibleTuple)
    (h_nonempty : t.seq ≠ [])
    (h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0) :
    ∃ t' : G.FeasibleTuple, t'.C = ∅ ∧
        (∀ x ∈ t'.S, x ∈ t.S ∨ ∃ i, ∃ _ : i < t.seq.length, x = t.seq[i]) ∧
        (∀ x ∈ t'.seq, x ∈ t.seq) ∧
        G.FeasibleTupleLt t' t := by
  have h_len_pos : 0 < t.seq.length := List.length_pos_of_ne_nil h_nonempty
  let m := t.seq.length - 1
  have hm : m < t.seq.length := Nat.sub_one_lt_of_lt h_len_pos
  have hm_eq : m + 1 = t.seq.length := Nat.sub_add_cancel h_len_pos
  let v_m := t.seq[m]
  -- d_m = 0 means v_m has no neighbors in S
  have h_no_neighbors : G.graph.neighborSet v_m ∩ t.S = ∅ := by
    rw [← Set.ncard_eq_zero]
    simp only [degreeAt] at h_last_zero
    have hseq : t.seq.length - 1 < t.seq.length := by omega
    simp only [List.getElem?_eq_getElem hseq] at h_last_zero
    exact h_last_zero
  -- v_m is independent from all vertices in S
  have h_indep : ∀ s ∈ t.S, ¬G.graph.Adj v_m s := by
    intro s hs hadj
    have : s ∈ G.graph.neighborSet v_m ∩ t.S := ⟨hadj, hs⟩
    rw [h_no_neighbors] at this
    exact this
  -- From augmenting property: v_m ∈ V_{B_m}
  have h_aug := t.isAugmenting ⟨m, hm⟩
  have h_vm_in_Bm : v_m ∈ G.blockUnion (G.blocksSeq t.S t.seq m) := h_aug.1
  -- v_m is in some block U ∈ B_m
  have ⟨U, hU_in_Bm, hv_in_U⟩ : ∃ U ∈ G.blocksSeq t.S t.seq m, v_m ∈ U := by
    have hBm_sub : G.blocksSeq t.S t.seq m ⊆ G.blocks := G.blocksSeq_subset t.S t.seq m
    rw [G.blockUnion_eq_sUnion hBm_sub] at h_vm_in_Bm
    exact Set.mem_sUnion.mp h_vm_in_Bm
  have hU_blocks : U ∈ G.blocks := G.blocksSeq_subset t.S t.seq m hU_in_Bm
  -- Use the blocksSeq_mem_cases lemma to analyze U's membership
  rcases G.blocksSeq_mem_cases t.S t.seq U m (le_of_lt hm) hU_in_Bm with
    hU_uncov | ⟨k, hk_len, hk_lt_m, hU_from_k⟩
  · -- Case 1: U ∈ uncoveredBlocks S (k = 0 case)
    -- S ∩ U = ∅ (U is uncovered)
    have hS_disjoint_U : Disjoint t.S U := by
      simp only [uncoveredBlocks, blocksIntersecting] at hU_uncov
      simp only [Set.mem_diff, Set.mem_setOf_eq, not_and] at hU_uncov
      have := hU_uncov.2 hU_blocks
      rw [Set.not_nonempty_iff_eq_empty, Set.inter_comm] at this
      exact Set.disjoint_iff_inter_eq_empty.mpr this
    -- S' = S ∪ {v_m} is independent (v_m has no S-neighbors)
    let S' := t.S ∪ {v_m}
    have hS'_indep : G.graph.IsIndepSet S' := by
      intro x hx y hy hne
      simp only [S', Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx, hy with ⟨hxS | hx_eq, hyS | hy_eq⟩
      · exact t.isPartialIT.1 hxS hyS hne
      · subst hy_eq; exact fun hadj => h_indep x hxS (G.graph.adj_symm hadj)
      · subst hx_eq; exact h_indep y hyS
      · subst hx_eq hy_eq; exact (hne rfl).elim
    -- S' is a partial IT
    have hS'_partial : G.IsPartialIT S' := by
      constructor
      · exact hS'_indep
      · intro U' hU'
        by_cases hU'_eq : U' = U
        · -- U' is the (now covered) block containing v_m
          rw [hU'_eq]
          have h_inter : S' ∩ U = {v_m} := by
            ext x
            simp only [S', Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U⟩
              rcases hx_S' with hxS | hx_eq
              · exact (Set.disjoint_left.mp hS_disjoint_U hxS hx_U).elim
              · exact hx_eq
            · intro hx_eq; subst hx_eq; exact ⟨Or.inr rfl, hv_in_U⟩
          rw [h_inter, Set.ncard_singleton]
        · -- U' ≠ U: v_m ∉ U' since blocks are disjoint
          have hv_not_in_U' : v_m ∉ U' := by
            intro hv_U'
            have hdisj := G.pairwiseDisjoint hU_blocks hU' (Ne.symm hU'_eq)
            exact Set.disjoint_left.mp hdisj hv_in_U hv_U'
          have h_inter : S' ∩ U' = t.S ∩ U' := by
            ext x
            simp only [S', Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U'⟩
              rcases hx_S' with hxS | hx_eq
              · exact ⟨hxS, hx_U'⟩
              · subst hx_eq; exact (hv_not_in_U' hx_U').elim
            · intro ⟨hxS, hx_U'⟩; exact ⟨Or.inl hxS, hx_U'⟩
          rw [h_inter]
          exact t.isPartialIT.2 U' hU'
    -- Construct the new feasible tuple with larger S
    let t' : G.FeasibleTuple := ⟨S', ∅, [], hS'_partial, Set.empty_subset _, fun k => Fin.elim0 k⟩
    use t'
    refine ⟨rfl, ?_, ?_, ?_⟩
    · -- t'.S ⊆ t.S ∪ {v_m}: every element is in t.S or is a seq element
      intro x hx
      have hx : x ∈ S' := hx
      simp only [S', Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with hxS | hx_eq
      · left; exact hxS
      · right; exact ⟨m, hm, hx_eq⟩
    · -- t'.seq = []: vacuously true
      intro x hx; exact (List.not_mem_nil hx).elim
    · left  -- |S'| > |S|
      have hv_not_in_S : v_m ∉ t.S := Set.disjoint_left.mp hS_disjoint_U.symm hv_in_U
      calc S'.ncard = (t.S ∪ {v_m}).ncard := rfl
        _ = t.S.ncard + ({v_m} : Set V).ncard :=
            Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hv_not_in_S)
        _ = t.S.ncard + 1 := by simp only [Set.ncard_singleton]
        _ > t.S.ncard := by omega
  · -- Case 2: U ∈ blocksIntersecting(N_S(seq[k])) for some k < m
    -- This means U contains some s ∈ S ∩ N(seq[k])
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hU_from_k
    obtain ⟨_, s, hs_U, hs_NS⟩ := hU_from_k
    have hs_S : s ∈ t.S := hs_NS.2
    have hs_Nk : G.graph.Adj t.seq[k] s := hs_NS.1
    -- Key: v_m and s are in the same block U, but v_m ≁ s (since d_m = 0)
    have _h_vm_not_adj_s : ¬G.graph.Adj v_m s := h_indep s hs_S
    -- S' = S ⊕ v_m = (S \ U) ∪ {v_m}
    -- Note: We use blockOf v_m = U (since v_m ∈ U and blocks are unique)
    have hU_eq_blockOf : U = G.blockOf v_m := G.blockOf_unique v_m U hU_blocks hv_in_U
    let S' := G.oplus t.S v_m
    -- S' is independent: v_m is not adjacent to any vertex in S
    have hS'_indep : G.graph.IsIndepSet S' := by
      intro x hx y hy hne
      simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx hy
      rcases hx, hy with ⟨⟨hxS, hxU⟩ | hx_eq, ⟨hyS, hyU⟩ | hy_eq⟩
      · exact t.isPartialIT.1 hxS hyS hne
      · subst hy_eq
        intro hadj
        exact h_indep x hxS (G.graph.adj_symm hadj)
      · subst hx_eq
        exact h_indep y hyS
      · subst hx_eq hy_eq; exact (hne rfl).elim
    -- S' is a partial IT
    have hS'_partial : G.IsPartialIT S' := by
      constructor
      · exact hS'_indep
      · intro U' hU'
        by_cases hU'_eq : U' = G.blockOf v_m
        · -- U' is v_m's block: S' ∩ U' = {v_m}
          rw [hU'_eq]
          have h_inter : S' ∩ G.blockOf v_m = {v_m} := by
            ext x
            simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
              Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U⟩
              rcases hx_S' with ⟨hxS, hxU⟩ | hx_eq
              · exact (hxU hx_U).elim
              · exact hx_eq
            · intro hx_eq; subst hx_eq; exact ⟨Or.inr rfl, G.mem_blockOf v_m⟩
          rw [h_inter, Set.ncard_singleton]
        · -- U' ≠ blockOf v_m: S' ∩ U' = S ∩ U' (removing s doesn't affect other blocks)
          have h_inter : S' ∩ U' = t.S ∩ U' := by
            ext x
            simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
              Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U'⟩
              rcases hx_S' with ⟨hxS, _⟩ | hx_eq
              · exact ⟨hxS, hx_U'⟩
              · -- x = v_m ∈ U', but v_m ∈ blockOf v_m ≠ U', contradiction
                subst hx_eq
                have hdisj := G.pairwiseDisjoint (G.blockOf_mem v_m) hU' (fun h => hU'_eq h.symm)
                exact (Set.disjoint_left.mp hdisj (G.mem_blockOf v_m) hx_U').elim
            · intro ⟨hxS, hx_U'⟩
              -- x ∈ S and x ∈ U' ≠ blockOf v_m, so x ∉ blockOf v_m
              have hx_not_in_block : x ∉ G.blockOf v_m := by
                intro hx_block
                have hdisj := G.pairwiseDisjoint (G.blockOf_mem v_m) hU' (fun h => hU'_eq h.symm)
                exact Set.disjoint_left.mp hdisj hx_block hx_U'
              exact ⟨Or.inl ⟨hxS, hx_not_in_block⟩, hx_U'⟩
          rw [h_inter]
          exact t.isPartialIT.2 U' hU'
    -- The truncated sequence seq' = t.seq.take (k + 1)
    let seq' := t.seq.take (k + 1)
    have h_seq'_len : seq'.length = k + 1 := by
      simp only [seq', List.length_take]
      -- k < m and m < seq.length, so k + 1 ≤ m + 1 ≤ seq.length
      have h_k1_le : k + 1 ≤ t.seq.length := by
        have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
        omega
      exact Nat.min_eq_left h_k1_le
    -- Helper 1: uncoveredBlocks S' = uncoveredBlocks t.S
    -- Both S and S' cover the same blocks: U was covered by S (s ∈ S ∩ U) and
    -- is covered by S' (v_m ∈ S' ∩ U). Other blocks are unchanged.
    have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
    -- The intersection t.S ∩ G.blockOf v_m = {s} (used in multiple places)
    have h_S_inter_block : t.S ∩ G.blockOf v_m = {s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hz_S, hz_block⟩
        by_contra hne
        have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard := by
          have h_pair : ({z, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
            intro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl
            · exact ⟨hz_S, hz_block⟩
            · exact ⟨hs_S, hs_in_block⟩
          exact (Set.ncard_pair hne).symm.trans_le
            (Set.ncard_le_ncard h_pair (Set.toFinite _))
        have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
        omega
      · intro hz_eq; subst hz_eq; exact ⟨hs_S, hs_in_block⟩
    have h_uncov_eq : G.uncoveredBlocks S' = G.uncoveredBlocks t.S := by
      ext W
      simp only [uncoveredBlocks, blocksIntersecting, Set.mem_diff, Set.mem_setOf_eq]
      constructor
      · intro ⟨hW_block, hW_not_int⟩
        refine ⟨hW_block, ?_⟩
        intro hW_hyp
        -- hW_hyp : W ∈ G.blocks ∧ (W ∩ t.S).Nonempty
        obtain ⟨_, hW_int⟩ := hW_hyp
        obtain ⟨y, hy_W, hy_S⟩ := hW_int
        -- W ∩ S.Nonempty implies W ∩ S'.Nonempty
        apply hW_not_int
        refine ⟨hW_block, ?_⟩
        -- Either y ∈ S' directly, or y = s (unique element in blockOf v_m ∩ S) and we use v_m
        by_cases hy_in_block : y ∈ G.blockOf v_m
        · -- y ∈ S ∩ blockOf v_m, so y = s (unique). W contains s, so W = blockOf v_m.
          have hy_eq_s : y = s := by
            have hy_in_inter : y ∈ t.S ∩ G.blockOf v_m := ⟨hy_S, hy_in_block⟩
            rw [h_S_inter_block] at hy_in_inter
            exact Set.mem_singleton_iff.mp hy_in_inter
          -- y = s, so W contains s. Since s ∈ blockOf v_m and blocks are disjoint, W = blockOf v_m.
          have hW_eq_block : W = G.blockOf v_m := by
            have h := G.blockOf_unique s W hW_block (hy_eq_s ▸ hy_W)
            have h' := G.blockOf_unique s (G.blockOf v_m) (G.blockOf_mem v_m) hs_in_block
            rw [h, h']
          -- v_m ∈ W ∩ S'
          refine ⟨v_m, ?_, ?_⟩
          · rw [hW_eq_block]; exact G.mem_blockOf v_m
          · simp only [S', oplus, Set.mem_union, Set.mem_singleton_iff]; right; trivial
        · -- y ∉ blockOf v_m, so y ∈ S \ blockOf v_m ⊆ S'
          refine ⟨y, hy_W, ?_⟩
          simp only [S', oplus, Set.mem_union, Set.mem_diff]
          left; exact ⟨hy_S, hy_in_block⟩
      · intro ⟨hW_block, hW_not_int⟩
        refine ⟨hW_block, ?_⟩
        intro hW_hyp
        -- hW_hyp : W ∈ G.blocks ∧ (W ∩ S').Nonempty
        obtain ⟨_, hW_int⟩ := hW_hyp
        obtain ⟨y, hy_W, hy_S'⟩ := hW_int
        -- W ∩ S'.Nonempty implies W ∩ S.Nonempty
        apply hW_not_int
        refine ⟨hW_block, ?_⟩
        simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hy_S'
        rcases hy_S' with ⟨hy_S, _⟩ | hy_eq
        · exact ⟨y, hy_W, hy_S⟩
        · -- y = v_m ∈ W. Since v_m ∈ blockOf v_m and blocks are disjoint, W = blockOf v_m.
          subst hy_eq
          have hW_eq_block : W = G.blockOf v_m :=
            G.blockOf_unique v_m W hW_block hy_W
          refine ⟨s, ?_, hs_S⟩
          rw [hW_eq_block]; exact hs_in_block
    -- Helper 2: For j < m, seq[j] ≁ v_m (from augmenting disjointness: v_m ⊥ C_m)
    have h_vm_not_adj : ∀ j (hj : j < m), ¬G.graph.Adj t.seq[j] v_m := by
      intro j hj hadj
      -- seq[j] ∈ vertexSeq (j+1) ⊆ vertexSeq m
      have hj_lt_len : j < t.seq.length := Nat.lt_of_lt_of_le hj (Nat.le_of_lt hm)
      have h_seq_j_in_vtx : t.seq[j] ∈ G.vertexSeq t.S t.C t.seq (j + 1) := by
        simp only [vertexSeq]
        have hseq_j : t.seq[j]? = some t.seq[j] := List.getElem?_eq_getElem hj_lt_len
        simp only [hseq_j]
        right; rfl
      have h_mono := G.vertexSeq_mono t.S t.C t.seq (Nat.succ_le_of_lt hj) (Nat.le_of_lt hm)
      have h_seq_j_in_Cm : t.seq[j] ∈ G.vertexSeq t.S t.C t.seq m := h_mono h_seq_j_in_vtx
      -- v_m is disjoint from C_m (from augmenting property)
      have h_vm_disj := h_aug.2.1
      -- hadj : G.graph.Adj t.seq[j] v_m, need to show contradiction
      -- neighborSet v_m = {w | Adj v_m w}, so Adj t.seq[j] v_m means t.seq[j] ∈ neighborSet v_m
      have h_seq_j_in_N : t.seq[j] ∈ G.graph.neighborSet v_m := G.graph.adj_symm hadj
      exact Set.disjoint_left.mp h_vm_disj h_seq_j_in_N h_seq_j_in_Cm
    -- Helper 3: For j < k, s ∉ neighborSet seq[j] (from augmenting_neighborSets_disjoint)
    have h_s_not_in_Nj : ∀ j (hj : j < k), s ∉ G.graph.neighborSet t.seq[j] := by
      intro j hj hs_Nj
      -- s ∈ N(seq[k]) ∩ S and s ∈ N(seq[j]) ∩ S for j < k
      -- This contradicts augmenting_neighborSets_disjoint
      have h_disj := G.augmenting_neighborSets_disjoint t.S t.C t.seq t.isAugmenting hj hk_len
      have hs_in_Nk : s ∈ G.graph.neighborSet t.seq[k] ∩ t.S := ⟨hs_Nk, hs_S⟩
      have hs_in_Nj : s ∈ G.graph.neighborSet t.seq[j] ∩ t.S := ⟨hs_Nj, hs_S⟩
      have hs_in_both : s ∈ (G.graph.neighborSet t.seq[k] ∩ t.S) ∩
          (G.graph.neighborSet t.seq[j] ∩ t.S) := ⟨hs_in_Nk, hs_in_Nj⟩
      rw [Set.disjoint_iff_inter_eq_empty] at h_disj
      rw [h_disj] at hs_in_both
      exact Set.notMem_empty s hs_in_both
    -- Helper 4: For j < k, N_{S'}(seq[j]) = N_S(seq[j])
    have h_NS_eq : ∀ j (hj : j < k), G.graph.neighborSet t.seq[j] ∩ S' =
        G.graph.neighborSet t.seq[j] ∩ t.S := by
      intro j hj
      ext x
      simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hx_Nj, hx_S'⟩
        rcases hx_S' with ⟨hx_S, _⟩ | hx_eq
        · exact ⟨hx_Nj, hx_S⟩
        · -- x = v_m ∈ neighborSet seq[j], so seq[j] ~ v_m
          subst hx_eq
          exfalso
          have hj_lt_m : j < m := Nat.lt_trans hj hk_lt_m
          -- hx_Nj : v_m ∈ G.graph.neighborSet t.seq[j], i.e., Adj t.seq[j] v_m
          exact h_vm_not_adj j hj_lt_m hx_Nj
      · intro ⟨hx_Nj, hx_S⟩
        constructor
        · exact hx_Nj
        · -- Need x ∈ S' = (S \ U) ∪ {v_m}
          by_cases hx_vm : x = v_m
          · right; exact hx_vm
          · left
            constructor
            · exact hx_S
            · -- x ∈ S, need x ∉ U = blockOf v_m
              -- If x ∈ U, then x ∈ S ∩ U = {s}, so x = s
              -- But s ∉ neighborSet seq[j] for j < k
              intro hx_U
              have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
              have hx_eq_s : x = s := by
                have h_inter : t.S ∩ G.blockOf v_m = {s} := by
                  ext y
                  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
                  constructor
                  · intro ⟨hy_S, hy_U⟩
                    by_contra hne
                    have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard := by
                      have h_pair : ({y, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
                        intro z hz
                        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
                        rcases hz with rfl | rfl
                        · exact ⟨hy_S, hy_U⟩
                        · exact ⟨hs_S, hs_in_block⟩
                      exact (Set.ncard_pair hne).symm.trans_le
                        (Set.ncard_le_ncard h_pair (Set.toFinite _))
                    have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
                    omega
                  · intro hy_eq; subst hy_eq; exact ⟨hs_S, hs_in_block⟩
                have hx_in_inter : x ∈ t.S ∩ G.blockOf v_m := ⟨hx_S, hx_U⟩
                rw [h_inter] at hx_in_inter
                exact Set.mem_singleton_iff.mp hx_in_inter
              subst hx_eq_s
              exact h_s_not_in_Nj j hj hx_Nj
    -- Helper 5: blocksSeq S' seq' i = blocksSeq t.S t.seq i for i ≤ k
    have h_blocksSeq_eq : ∀ i (hi : i ≤ k), G.blocksSeq S' seq' i = G.blocksSeq t.S t.seq i := by
      intro i hi
      induction i with
      | zero => simp only [blocksSeq]; exact h_uncov_eq
      | succ i' ih =>
        have hi' : i' ≤ k := Nat.le_of_succ_le hi
        have hi'_lt_k : i' < k := Nat.lt_of_succ_le hi
        have hi'_lt_k1 : i' < k + 1 := Nat.lt_succ_of_lt hi'_lt_k
        have hi'_lt_len : i' < t.seq.length := Nat.lt_trans hi'_lt_k hk_len
        have hi'_lt_seq'_len : i' < seq'.length := by rw [h_seq'_len]; exact hi'_lt_k1
        simp only [blocksSeq]
        -- seq'[i']? = some seq'[i'] = some t.seq[i']
        have h_seq'_i' : seq'[i']? = some t.seq[i'] := by
          have h1 : seq'[i']? = some seq'[i'] := List.getElem?_eq_getElem hi'_lt_seq'_len
          have h2 : seq'[i'] = t.seq[i'] := by
            simp only [seq']
            rw [List.getElem_take]
          rw [h1, h2]
        have h_seq_i' : t.seq[i']? = some t.seq[i'] := List.getElem?_eq_getElem hi'_lt_len
        simp only [h_seq'_i', h_seq_i']
        rw [ih hi']
        -- Need: blocksIntersecting (N_{S'}(seq[i'])) = blocksIntersecting (N_S(seq[i']))
        congr 1
        exact congr_arg G.blocksIntersecting (h_NS_eq i' hi'_lt_k)
    -- Show seq' is augmenting for (S', ∅)
    have h_aug' : G.IsAugmenting S' ∅ seq' := by
      intro ⟨i, hi⟩
      have hi_lt_k1 : i < k + 1 := by rw [← h_seq'_len]; exact hi
      have hi_lt_len : i < t.seq.length := by
        have h_k1_le : k + 1 ≤ t.seq.length := by
          have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
          omega
        omega
      -- seq'[i] = t.seq[i] for i < k + 1
      have h_seq'_i : seq'[i]'hi = t.seq[i]'hi_lt_len := by
        simp only [seq']
        rw [List.getElem_take]
      -- Get the augmenting property from the original tuple
      have h_aug_i := t.isAugmenting ⟨i, hi_lt_len⟩
      have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp hi_lt_k1
      -- The goal involves seq'[⟨i, hi⟩]. We need to convert to t.seq[i] using h_seq'_i.
      constructor
      · -- Condition 1: seq'[i] ∈ V_{blocksSeq S' seq' i}
        change seq'.get ⟨i, hi⟩ ∈ G.blockUnion (G.blocksSeq S' seq' i)
        simp only [List.get_eq_getElem]
        rw [h_seq'_i, h_blocksSeq_eq i hi_le_k]
        exact h_aug_i.1
      constructor
      · -- Condition 2: Disjoint (neighborSet seq'[i]) (vertexSeq S' ∅ seq' i)
        change Disjoint (G.graph.neighborSet (seq'.get ⟨i, hi⟩)) (G.vertexSeq S' ∅ seq' i)
        simp only [List.get_eq_getElem]
        rw [h_seq'_i]
        -- Show vertexSeq S' ∅ seq' i ⊆ vertexSeq t.S t.C t.seq i
        have h_vtx_sub : G.vertexSeq S' ∅ seq' i ⊆ G.vertexSeq t.S t.C t.seq i := by
          induction i with
          | zero =>
            simp only [vertexSeq]
            exact Set.empty_subset _
          | succ i' ih_vtx =>
            have hi'_le_k : i' ≤ k := Nat.le_of_succ_le hi_le_k
            have hi'_lt_k : i' < k := Nat.lt_of_succ_le hi_le_k
            have hi'_lt_k1 : i' < k + 1 := Nat.lt_succ_of_lt hi'_lt_k
            have hi'_lt_seq'_len : i' < seq'.length := by rw [h_seq'_len]; exact hi'_lt_k1
            have hi'_lt_len' : i' < t.seq.length := Nat.lt_trans hi'_lt_k hk_len
            simp only [vertexSeq]
            have h_seq'_i'_some : seq'[i']? = some seq'[i'] :=
              List.getElem?_eq_getElem hi'_lt_seq'_len
            have h_seq_i'_some : t.seq[i']? = some t.seq[i'] :=
              List.getElem?_eq_getElem hi'_lt_len'
            simp only [h_seq'_i'_some, h_seq_i'_some]
            have h_seq'_i'_eq : seq'[i'] = t.seq[i'] := by
              simp only [seq']; rw [List.getElem_take]
            rw [h_seq'_i'_eq]
            intro x hx
            simp only [Set.mem_union, Set.mem_singleton_iff] at hx ⊢
            rcases hx with ((hx_vtx | hx_NS) | hx_eq)
            · left; left
              -- Need to provide all generalized arguments to ih_vtx
              have h_seq'_i' : seq'[i'] = t.seq[i'] := by simp only [seq']; rw [List.getElem_take]
              have h_aug_i' := t.isAugmenting ⟨i', hi'_lt_len'⟩
              exact ih_vtx hi'_lt_seq'_len hi'_lt_k1 hi'_lt_len' h_seq'_i' h_aug_i' hi'_le_k hx_vtx
            · left; right
              rw [h_NS_eq i' hi'_lt_k] at hx_NS
              exact hx_NS
            · right; exact hx_eq
        exact Set.disjoint_of_subset_right h_vtx_sub h_aug_i.2.1
      -- Condition 3: positive degree for non-last position
      intro h_not_last
      change 0 < (G.graph.neighborSet (seq'.get ⟨i, hi⟩) ∩ S').ncard
      simp only [List.get_eq_getElem]
      rw [h_seq'_i]
      have hi_lt_k : i < k := by
        simp only [] at h_not_last
        omega
      have h_deg_eq : (G.graph.neighborSet t.seq[i] ∩ S').ncard =
          (G.graph.neighborSet t.seq[i] ∩ t.S).ncard := by
        congr 1; exact h_NS_eq i hi_lt_k
      rw [h_deg_eq]
      have hi_not_last_orig : i + 1 < t.seq.length := by
        have : i + 1 ≤ k := hi_lt_k
        have : k < m := hk_lt_m
        have : m < t.seq.length := hm
        omega
      exact h_aug_i.2.2 hi_not_last_orig
    -- Construct the new feasible tuple
    let t' : G.FeasibleTuple := ⟨S', ∅, seq', hS'_partial, Set.empty_subset _, h_aug'⟩
    use t'
    refine ⟨rfl, ?_, ?_, ?_⟩
    · -- t'.S ⊆ t.S ∪ {v_m}: every element is in t.S or is a seq element
      intro x hx
      have hx : x ∈ S' := hx
      simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx
      rcases hx with ⟨hxS, _⟩ | hx_eq
      · left; exact hxS
      · right; exact ⟨m, hm, hx_eq⟩
    · -- t'.seq elements come from t.seq (t'.seq is a prefix of t.seq)
      intro x hx
      exact List.mem_of_mem_take hx
    · -- Show FeasibleTupleLt t' t
      -- |S'| = |S| (we swapped one vertex for another)
      -- The degree sequence is smaller: d_i(seq') = d_i(seq) for i < k,
      -- and d_k(seq') = d_k(seq) - 1 (s was removed from N_S(v_k))
      right
      constructor
      · -- |S'| = |S|
        -- oplus replaces one vertex with another in the same block
        -- S' = (S \ blockOf v_m) ∪ {v_m}
        -- Since s ∈ S ∩ U and U = blockOf v_m, we have s ∈ S ∩ blockOf v_m
        -- The partial IT property ensures |S ∩ U| ≤ 1, so S ∩ U = {s}
        -- Therefore S' = (S \ {s}) ∪ {v_m} has the same cardinality
        have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
        have h_S_inter_block : t.S ∩ G.blockOf v_m = {s} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
          constructor
          · intro ⟨hxS, hxU⟩
            -- x, s ∈ S ∩ blockOf v_m, and |S ∩ blockOf v_m| ≤ 1
            by_contra hne
            have h_pair : ({x, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl
              · exact ⟨hxS, hxU⟩
              · exact ⟨hs_S, hs_in_block⟩
            have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard :=
              (Set.ncard_pair hne).symm.trans_le (Set.ncard_le_ncard h_pair (Set.toFinite _))
            have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
            omega
          · intro hx_eq
            subst hx_eq
            exact ⟨hs_S, hs_in_block⟩
        -- S' = (S \ blockOf v_m) ∪ {v_m}, where S ∩ blockOf v_m = {s}
        -- So |S'| = |S \ blockOf v_m| + 1 = |S| - |S ∩ blockOf v_m| + 1 = |S| - 1 + 1 = |S|
        have h_diff_card : (t.S \ G.blockOf v_m).ncard = t.S.ncard - 1 := by
          -- Use: (s ∩ t).ncard + (s \ t).ncard = s.ncard
          have h_add := Set.ncard_inter_add_ncard_diff_eq_ncard t.S (G.blockOf v_m) (Set.toFinite _)
          rw [h_S_inter_block, Set.ncard_singleton] at h_add
          omega
        have h_disj : Disjoint (t.S \ G.blockOf v_m) {v_m} := by
          rw [Set.disjoint_singleton_right]
          intro hv_in
          exact hv_in.2 (G.mem_blockOf v_m)
        calc S'.ncard = (G.oplus t.S v_m).ncard := rfl
          _ = ((t.S \ G.blockOf v_m) ∪ {v_m}).ncard := rfl
          _ = (t.S \ G.blockOf v_m).ncard + ({v_m} : Set V).ncard := by
              exact Set.ncard_union_eq h_disj (Set.toFinite _) (Set.toFinite _)
          _ = (t.S \ G.blockOf v_m).ncard + 1 := by simp only [Set.ncard_singleton]
          _ = (t.S.ncard - 1) + 1 := by rw [h_diff_card]
          _ = t.S.ncard := by
              have h_S_nonempty : t.S.Nonempty := ⟨s, hs_S⟩
              have h_ncard_pos : 0 < t.S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr h_S_nonempty
              omega
      · -- degSeqLt (degreeSeq S' seq') (degreeSeq S seq)
        -- This requires showing that d_k(seq') = d_k(seq) - 1
        -- The key insight: N_{S'}(t.seq[k]) = N_S(t.seq[k]) \ {s}
        -- because s was the unique S-neighbor of t.seq[k] in block U,
        -- and S' = S \ U ∪ {v_m} with v_m ≁ t.seq[k] (from augmenting disjointness)
        simp only [degSeqLt]
        -- Use Case 2: List.Lex (· < ·) d1 d2 ∧ ¬(d1 <+: d2)
        right
        -- First establish key facts about the degree sequences
        let d1 := G.degreeSeq S' seq'
        let d2 := G.degreeSeq t.S t.seq
        have h_d1_len : d1.length = k + 1 := by
          simp only [d1, degreeSeq, List.length_mapIdx, h_seq'_len]
        have h_d2_len : d2.length = t.seq.length := by
          simp only [d2, degreeSeq, List.length_mapIdx]
        -- Key fact: N_{S'}(seq[k]) = N_S(seq[k]) \ {s}
        have h_NS_k : G.graph.neighborSet t.seq[k] ∩ S' =
            (G.graph.neighborSet t.seq[k] ∩ t.S) \ {s} := by
          ext x
          simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
            Set.mem_singleton_iff]
          constructor
          · intro ⟨hx_Nk, hx_S'⟩
            rcases hx_S' with ⟨hx_S, hx_not_block⟩ | hx_vm
            · refine ⟨⟨hx_Nk, hx_S⟩, ?_⟩
              intro hx_eq
              subst hx_eq
              exact hx_not_block hs_in_block
            · -- x = v_m, but v_m ∉ N(seq[k]) by augmenting disjointness
              subst hx_vm
              exfalso
              exact h_vm_not_adj k hk_lt_m hx_Nk
          · intro ⟨⟨hx_Nk, hx_S⟩, hx_ne_s⟩
            refine ⟨hx_Nk, ?_⟩
            left
            constructor
            · exact hx_S
            · intro hx_block
              have hx_in_inter : x ∈ t.S ∩ G.blockOf v_m := ⟨hx_S, hx_block⟩
              rw [h_S_inter_block] at hx_in_inter
              exact hx_ne_s (Set.mem_singleton_iff.mp hx_in_inter)
        -- Therefore d1[k] < d2[k]
        have hs_in_NS_k : s ∈ G.graph.neighborSet t.seq[k] ∩ t.S := ⟨hs_Nk, hs_S⟩
        have h_finite_k : (G.graph.neighborSet t.seq[k] ∩ t.S).Finite := Set.toFinite _
        have h_dk_lt : (G.graph.neighborSet t.seq[k] ∩ S').ncard <
            (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
          rw [h_NS_k]
          calc ((G.graph.neighborSet t.seq[k] ∩ t.S) \ {s}).ncard
            = (G.graph.neighborSet t.seq[k] ∩ t.S).ncard - 1 := by
                exact Set.ncard_diff_singleton_of_mem hs_in_NS_k
            _ < (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
                have h_pos : 0 < (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
                  rw [Set.ncard_pos h_finite_k]
                  exact ⟨s, hs_in_NS_k⟩
                omega
        -- For i < k: d1[i] = d2[i] (degrees agree)
        have h_deg_eq : ∀ i (hi : i < k), (G.graph.neighborSet t.seq[i] ∩ S').ncard =
            (G.graph.neighborSet t.seq[i] ∩ t.S).ncard := by
          intro i hi
          congr 1
          exact h_NS_eq i hi
        -- seq'[i] = seq[i] for i < k + 1
        have h_seq'_eq : ∀ i (hi : i < k + 1), seq'[i]'(by rw [h_seq'_len]; exact hi) =
            t.seq[i]'(Nat.lt_of_lt_of_le hi (by omega : k + 1 ≤ t.seq.length)) := by
          intro i hi
          simp only [seq', List.getElem_take]
        -- Need to show: List.Lex (·<·) d1 d2 ∧ ¬(d1 <+: d2)
        -- Length facts
        have hk_lt_d1 : k < d1.length := by simp only [h_d1_len]; exact Nat.lt_succ_self k
        have hk_lt_d2 : k < d2.length := by simp only [h_d2_len]; exact hk_len
        -- d1[i] = d2[i] for i < k
        have h_d_eq : ∀ i (hi : i < k),
            d1[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_d1)) =
            d2[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_d2)) := by
          intro i hi
          simp only [d1, d2, degreeSeq, List.getElem_mapIdx]
          have hi_lt_k1 : i < k + 1 := Nat.lt_of_lt_of_le hi (Nat.le_of_lt (Nat.lt_succ_self k))
          have h_seq'_i := h_seq'_eq i hi_lt_k1
          conv_lhs => rw [h_seq'_i]
          exact h_deg_eq i hi
        -- d1[k] < d2[k]
        have h_d_k_lt : d1[k]'hk_lt_d1 < d2[k]'hk_lt_d2 := by
          simp only [d1, d2, degreeSeq, List.getElem_mapIdx]
          have h_seq'_k := h_seq'_eq k (Nat.lt_succ_self k)
          conv_lhs => rw [h_seq'_k]
          exact h_dk_lt
        constructor
        · -- List.Lex (·<·) d1 d2
          exact list_lex_of_prefix_and_lt hk_lt_d1 hk_lt_d2 h_d_eq h_d_k_lt
        · -- ¬(d1 <+: d2)
          exact not_prefix_of_ne_at hk_lt_d1 hk_lt_d2 (Nat.ne_of_lt h_d_k_lt)

theorem PartitionedGraph.haxell_no_small_total_domination
    (h_nodom : G.NoSmallTotalDomination) : ∃ S, G.IsIndependentTransversal S := by
  -- The proof uses well-founded induction on feasible tuples
  -- Key insight: for any feasible tuple t that's not a full IT, we can find a strictly smaller one
  -- By well-foundedness, any minimal tuple must have S being a full IT
  suffices h : ∀ t : G.FeasibleTuple, t.C = ∅ → (G.uncoveredBlocks t.S).Nonempty →
      ∃ t' : G.FeasibleTuple, t'.C = ∅ ∧ G.FeasibleTupleLt t' t by
    -- Use well-founded recursion to find a tuple where uncoveredBlocks is empty
    have hwf := G.feasibleTuple_lt_wf
    -- Start with the empty tuple
    let t₀ : G.FeasibleTuple := ⟨∅, ∅, [], G.isPartialIT_empty, Set.empty_subset _,
      fun k => Fin.elim0 k⟩
    have h_t0_C_empty : t₀.C = ∅ := rfl
    -- Use WellFounded.min to find a minimal feasible tuple in the subset with C = ∅
    -- Define the set of feasible tuples with C = ∅ (nonempty since it contains t₀)
    let tuples : Set G.FeasibleTuple := {t | t.C = ∅}
    have h_nonempty : tuples.Nonempty := ⟨t₀, h_t0_C_empty⟩
    -- Get a minimal element using well-foundedness
    let t_min := hwf.min tuples h_nonempty
    have h_t_min_C_empty : t_min.C = ∅ := hwf.min_mem tuples h_nonempty
    -- The minimal tuple has empty uncoveredBlocks (otherwise h would give a smaller one)
    have h_uncovered_empty : G.uncoveredBlocks t_min.S = ∅ := by
      by_contra h_ne
      have h_ne' : (G.uncoveredBlocks t_min.S).Nonempty := Set.nonempty_iff_ne_empty.mpr h_ne
      obtain ⟨t', h_t'_C, ht'⟩ := h t_min h_t_min_C_empty h_ne'
      have h_t'_mem : t' ∈ tuples := h_t'_C
      exact hwf.not_lt_min tuples h_t'_mem ht'
    -- A partial IT with no uncovered blocks is a full IT
    use t_min.S
    exact PartitionedGraph.partialIT_of_no_uncovered G t_min.S t_min.isPartialIT h_uncovered_empty
  -- Prove the key lemma: if uncoveredBlocks is nonempty and C = ∅,
  -- we can find a smaller tuple with C = ∅
  intro t h_C_empty h_not_full
  -- Case analysis on the sequence
  by_cases h_seq_empty : t.seq = []
  · -- Empty sequence: use can_extend_sequence to extend it
    have h_can_extend := G.can_extend_without_domination t h_nodom
      (fun i hi => by simp [h_seq_empty] at hi) h_not_full h_C_empty
    -- h_can_extend gives a vertex v that can extend the sequence
    obtain ⟨v, hv_mem, hv_disj⟩ := h_can_extend
    -- Construct new tuple with sequence [v]
    let new_seq : List V := [v]
    -- Show the extended sequence gives a valid FeasibleTuple
    have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
      intro ⟨k, hk⟩
      simp only [new_seq, List.length_singleton] at hk
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst hk0
      simp only [new_seq]
      refine ⟨?_, ?_, ?_⟩
      · -- v ∈ V_{B_0}
        -- blocksSeq t.S [v] 0 = uncoveredBlocks t.S
        simp only [blocksSeq]
        simp only [h_seq_empty] at hv_mem
        exact hv_mem
      · -- Disjoint (neighborSet v) (vertexSeq t.S t.C [v] 0)
        -- vertexSeq t.S t.C [v] 0 = t.C
        simp only [vertexSeq]
        simp only [h_seq_empty] at hv_disj
        exact hv_disj
      · -- Condition 3: k + 1 < length → positive degree
        -- k = 0 and length = 1, so k + 1 = 1 = length, condition is vacuous
        intro h_lt
        simp only [List.length_singleton] at h_lt
        omega
    let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
    use t'
    constructor
    · -- t'.C = t.C = ∅
      exact h_C_empty
    · -- Show t' < t: same |S|, but new_seq = [v] extends [] = t.seq
      right
      constructor
      · rfl  -- same S, same ncard
      · -- degSeqLt (degreeSeq S [v]) (degreeSeq S [])
        -- [] is a prefix of [v], so [v] < [] in our ordering
        simp only [degSeqLt, h_seq_empty, degreeSeq, List.mapIdx_nil]
        left
        constructor
        · exact List.nil_prefix
        · exact List.cons_ne_nil _ _
  · -- Non-empty sequence: check if last degree is zero
    by_cases h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0
    · -- Last degree is zero: use improve_from_zero_degree
      obtain ⟨t', hC, _, _, hlt⟩ := G.improve_from_zero_degree t h_seq_empty h_last_zero
      exact ⟨t', hC, hlt⟩
    · -- All degrees are positive
      have h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1) := by
        intro i hi
        by_cases h_last : i + 1 = t.seq.length
        · simp only [h_last] at h_last_zero ⊢
          omega
        · -- For earlier indices, augmenting condition gives positive degree
          have h_aug := t.isAugmenting ⟨i, hi⟩
          have h_lt_len : i + 1 < t.seq.length := by omega
          -- h_aug.2.2 gives: (G.graph.neighborSet t.seq[i] ∩ t.S).ncard > 0
          -- Need to show this equals degreeAt t.S t.seq (i + 1)
          simp only [degreeAt]
          have h_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
            simp only [Nat.add_sub_cancel]
            exact List.getElem?_eq_getElem hi
          simp only [h_idx]
          exact h_aug.2.2 h_lt_len
      have h_can_extend := G.can_extend_without_domination t h_nodom h_all_pos h_not_full h_C_empty
      -- h_can_extend gives a vertex v that can extend the sequence
      -- Construct new tuple with extended sequence t.seq ++ [v]
      obtain ⟨v, hv_mem, hv_disj⟩ := h_can_extend
      let new_seq : List V := t.seq ++ [v]
      -- Show the extended sequence gives a valid FeasibleTuple
      have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
        -- The extended sequence satisfies augmenting:
        -- Key: blocksSeq and vertexSeq use List.take, so they agree on prefixes
        intro ⟨k, hk⟩
        simp only [new_seq, List.length_append, List.length_singleton] at hk
        by_cases h_last : k = t.seq.length
        · -- k is the new last index (for vertex v)
          subst h_last
          constructor
          · -- v ∈ V_{B_{t.seq.length}}
            -- new_seq[t.seq.length] = v and blocksSeq agrees with t.seq
            change (t.seq ++ [v])[t.seq.length] ∈
                G.blockUnion (G.blocksSeq t.S (t.seq ++ [v]) t.seq.length)
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            rw [PartitionedGraph.blocksSeq_append G t.S t.seq v t.seq.length (le_refl _)]
            exact hv_mem
          constructor
          · -- Condition 2: Disjoint (neighborSet v) (vertexSeq ... t.seq.length)
            change Disjoint (G.graph.neighborSet (t.seq ++ [v])[t.seq.length])
                (G.vertexSeq t.S t.C (t.seq ++ [v]) t.seq.length)
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v t.seq.length (le_refl _)]
            exact hv_disj
          · -- Condition 3: k+1 < new_seq.length → positive degree
            -- But k = t.seq.length and new_seq.length = t.seq.length + 1, so k+1 = new_seq.length
            intro h_lt
            -- h_lt says t.seq.length + 1 < (t.seq ++ [v]).length = t.seq.length + 1
            exfalso
            simp only [new_seq, List.length_append, List.length_singleton] at h_lt
            omega
        · -- k < t.seq.length: inherited from t.isAugmenting
          have hk_lt : k < t.seq.length := by omega
          have h_aug_k := t.isAugmenting ⟨k, hk_lt⟩
          constructor
          · -- Condition 1: v_k ∈ V_{B_k}
            change (t.seq ++ [v])[k] ∈ G.blockUnion (G.blocksSeq t.S (t.seq ++ [v]) k)
            rw [List.getElem_append_left hk_lt]
            rw [PartitionedGraph.blocksSeq_append G t.S t.seq v k (le_of_lt hk_lt)]
            exact h_aug_k.1
          constructor
          · -- Condition 2: v_k not adjacent to C_k
            change Disjoint (G.graph.neighborSet (t.seq ++ [v])[k])
                (G.vertexSeq t.S t.C (t.seq ++ [v]) k)
            rw [List.getElem_append_left hk_lt]
            rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v k (le_of_lt hk_lt)]
            exact h_aug_k.2.1
          -- Condition 3: positive degree if k+1 < new_seq.length
          intro hk_lt_new
          change 0 < (G.graph.neighborSet (t.seq ++ [v])[k] ∩ t.S).ncard
          rw [List.getElem_append_left hk_lt]
          -- Either k + 1 < t.seq.length (use h_aug_k.2.2) or k + 1 = t.seq.length (use h_all_pos)
          by_cases h_case : k + 1 < t.seq.length
          · exact h_aug_k.2.2 h_case
          · -- k + 1 = t.seq.length, so k = t.seq.length - 1
            have h_eq : k + 1 = t.seq.length := by
              simp only [new_seq, List.length_append, List.length_singleton] at hk_lt_new
              omega
            -- Use h_all_pos: for k < t.seq.length, 0 < degreeAt t.S t.seq (k + 1)
            have h_pos := h_all_pos k hk_lt
            simp only [degreeAt, Nat.add_sub_cancel] at h_pos
            rw [List.getElem?_eq_getElem hk_lt] at h_pos
            exact h_pos
      let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
      use t'
      constructor
      · -- t'.C = t.C = ∅
        exact h_C_empty
      · -- Show t' < t: same |S|, but new_seq extends t.seq
        right
        constructor
        · rfl  -- same S, same ncard
        · -- degSeqLt (degreeSeq S new_seq) (degreeSeq S t.seq)
          -- t.seq is a proper prefix of new_seq, so new_seq < t.seq in our ordering
          simp only [degSeqLt]
          left
          constructor
          · -- degreeSeq t.S t.seq is a prefix of degreeSeq t.S new_seq
            simp only [degreeSeq]
            rw [List.mapIdx_append]
            exact List.prefix_append _ _
          · -- degreeSeq t.S new_seq ≠ degreeSeq t.S t.seq
            -- The append of a non-empty list is not equal to the original (lengths differ)
            simp only [degreeSeq, ne_eq]
            rw [List.mapIdx_append]
            intro h_eq
            have h_len_eq : (List.mapIdx (fun i v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq ++
                List.mapIdx (fun i v => (G.graph.neighborSet v ∩ t.S).ncard) [v]).length =
                (List.mapIdx (fun i v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq).length := by
              congr 1
            simp only [List.length_append, List.mapIdx_cons, List.length_singleton,
              List.mapIdx_nil] at h_len_eq
            omega


#print axioms PartitionedGraph.haxell_no_small_total_domination
#check @PartitionedGraph.haxell_no_small_total_domination
end Haxell
end IndependentTransversals
