import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The deterministic edge-loss step in balanced vertex deletion

`edgesTo G S T` counts actual adjacent pairs from `S` to `T`. For disjoint
sets this counts each crossing undirected edge once. The results below prove
the factor `t * |S|` loss when at most `t` vertices are deleted in each shore;
they do not assume or prove the missing factor or Hamiltonicity theorem.
-/

namespace RobertPublishable.BM

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgesTo (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℕ :=
  ∑ v ∈ S, (T.filter (G.Adj v)).card

theorem edgesTo_union {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T D : Finset V) (hd : Disjoint T D) :
    edgesTo G S (T ∪ D) = edgesTo G S T + edgesTo G S D := by
  unfold edgesTo
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  rw [filter_union, card_union_of_disjoint]
  exact hd.mono (filter_subset _ _) (filter_subset _ _)

theorem edgesTo_le_card_mul {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Finset V) : edgesTo G S T ≤ S.card * T.card := by
  unfold edgesTo
  calc
    (∑ v ∈ S, (T.filter (G.Adj v)).card) ≤ ∑ _v ∈ S, T.card :=
      sum_le_sum fun v _ => card_filter_le _ _
    _ = S.card * T.card := by simp

theorem deleted_neighbors_le_shore_budget {G : SimpleGraph V} [DecidableRel G.Adj]
    (P Q D : Finset V) (t : ℕ)
    (hb : G.IsBipartiteWith (P : Set V) (Q : Set V))
    (cover : ∀ v, v ∈ P ∨ v ∈ Q)
    (hP : (D ∩ P).card ≤ t) (hQ : (D ∩ Q).card ≤ t) (v : V) :
    (D.filter (G.Adj v)).card ≤ t := by
  rcases cover v with hv | hv
  · apply (card_le_card (show D.filter (G.Adj v) ⊆ D ∩ Q from ?_)).trans hQ
    intro w hw
    obtain ⟨hD, hadj⟩ := mem_filter.mp hw
    exact mem_inter.mpr ⟨hD, hb.mem_of_mem_adj hv hadj⟩
  · apply (card_le_card (show D.filter (G.Adj v) ⊆ D ∩ P from ?_)).trans hP
    intro w hw
    obtain ⟨hD, hadj⟩ := mem_filter.mp hw
    exact mem_inter.mpr ⟨hD, hb.symm.mem_of_mem_adj hv hadj⟩

/-- The lost cut edges have only one endpoint in the test set, so the budget is
`t * |S|`, rather than the twice-as-large total number of deleted vertices. -/
theorem balanced_deleted_edges_le {G : SimpleGraph V} [DecidableRel G.Adj]
    (P Q D S : Finset V) (t : ℕ)
    (hb : G.IsBipartiteWith (P : Set V) (Q : Set V))
    (cover : ∀ v, v ∈ P ∨ v ∈ Q)
    (hP : (D ∩ P).card ≤ t) (hQ : (D ∩ Q).card ≤ t) :
    edgesTo G S D ≤ t * S.card := by
  unfold edgesTo
  calc
    (∑ v ∈ S, (D.filter (G.Adj v)).card) ≤ ∑ _v ∈ S, t :=
      sum_le_sum fun v _ => deleted_neighbors_le_shore_budget P Q D t hb cover hP hQ v
    _ = t * S.card := by simp [Nat.mul_comm]

/-- A cut on surviving vertices splits exactly into its retained cut and the
edges to deleted vertices. This is an actual adjacency-count identity. -/
theorem cut_deletion_identity {G : SimpleGraph V} [DecidableRel G.Adj]
    (S D : Finset V) (hSD : Disjoint S D) :
    edgesTo G S Sᶜ = edgesTo G S (Sᶜ \ D) + edgesTo G S D := by
  have hD : D ⊆ Sᶜ := by
    intro v hv
    exact mem_compl.mpr (fun hs => disjoint_left.mp hSD hs hv)
  have hU : (Sᶜ \ D) ∪ D = Sᶜ := by
    ext v
    simp only [mem_union, mem_sdiff, mem_compl]
    constructor
    · rintro (⟨hs, _⟩ | hd)
      · exact hs
      · exact mem_compl.mp (hD hd)
    · intro hs
      by_cases hd : v ∈ D
      · exact Or.inr hd
      · exact Or.inl ⟨hs, hd⟩
  calc
    edgesTo G S Sᶜ = edgesTo G S ((Sᶜ \ D) ∪ D) := congrArg (edgesTo G S) hU.symm
    _ = edgesTo G S (Sᶜ \ D) + edgesTo G S D :=
      edgesTo_union S (Sᶜ \ D) D sdiff_disjoint

theorem balanced_cut_loss_le {G : SimpleGraph V} [DecidableRel G.Adj]
    (P Q D S : Finset V) (t : ℕ)
    (hb : G.IsBipartiteWith (P : Set V) (Q : Set V))
    (cover : ∀ v, v ∈ P ∨ v ∈ Q)
    (hP : (D ∩ P).card ≤ t) (hQ : (D ∩ Q).card ≤ t)
    (hSD : Disjoint S D) :
    edgesTo G S Sᶜ ≤ edgesTo G S (Sᶜ \ D) + t * S.card := by
  rw [cut_deletion_identity S D hSD]
  exact Nat.add_le_add_left (balanced_deleted_edges_le P Q D S t hb cover hP hQ) _

#print axioms edgesTo_union
#print axioms edgesTo_le_card_mul
#print axioms deleted_neighbors_le_shore_budget
#print axioms balanced_deleted_edges_le
#print axioms cut_deletion_identity
#print axioms balanced_cut_loss_le

end RobertPublishable.BM
