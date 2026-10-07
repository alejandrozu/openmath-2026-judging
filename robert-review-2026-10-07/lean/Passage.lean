/-
Additive formalization of Robert Huynh's PROOF-R1.md, public commit
1efc324e155ef0b6a7081c5f695c6c825e7debef. Original source and prior audit unchanged.
New proof development for the coauthored publication, 7 October 2026.
-/
import Openmath.Proofs.BipartiteBalance
import Openmath.Proofs.CutGluing

open SimpleGraph Finset
open scoped Classical
namespace RobertPublishable.SUB

variable {V U : Type*} [DecidableEq V] [DecidableEq U]
    {G : SimpleGraph V}

/-- An edge has exactly one end in a prescribed copy. -/
def Crosses (copy : V → U) (u : U) (e : Sym2 V) : Prop :=
  (∃ x ∈ e, copy x = u) ∧ (∃ y ∈ e, copy y ≠ u)

@[simp] lemma crosses_mk (copy : V → U) (u : U) (a b : V) :
    Crosses copy u s(a,b) ↔
      (copy a = u ∧ copy b ≠ u) ∨ (copy a ≠ u ∧ copy b = u) := by
  constructor
  · rintro ⟨⟨x, hx, hxu⟩, ⟨y, hy, hyu⟩⟩
    simp only [Sym2.mem_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> aesop
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact ⟨⟨a, by simp, ha⟩, ⟨b, by simp, hb⟩⟩
    · exact ⟨⟨b, by simp, hb⟩, ⟨a, by simp, ha⟩⟩

/-- Local shore imbalance: I has weight -1, O has weight +1, other copies zero. -/
def localWeight (copy : V → U) (outer : V → Bool) (u : U) (v : V) : ℤ :=
  if copy v = u then if outer v then 1 else -1 else 0

lemma edge_weight_is_boundary (copy : V → U) (outer : V → Bool) (u : U)
    (hinternal : ∀ a b, G.Adj a b → copy a = copy b → outer a ≠ outer b)
    (hexternal : ∀ a b, G.Adj a b → copy a ≠ copy b → outer a = true ∧ outer b = true)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    Erdos585.BipartiteBalance.edgeWeight (localWeight copy outer u) e =
      if Crosses copy u e then 1 else 0 := by
  induction e using Sym2.inductionOn with | _ a b => ?_
  have hab : G.Adj a b := G.mem_edgeSet.mp he
  by_cases hcopy : copy a = copy b
  · have houter := hinternal a b hab hcopy
    by_cases hu : copy b = u <;> cases ha : outer a <;> cases hb : outer b <;>
      simp_all [localWeight, Erdos585.BipartiteBalance.edgeWeight_mk]
  · have houter := hexternal a b hab hcopy
    by_cases ha : copy a = u <;> by_cases hb : copy b = u <;>
      simp_all [localWeight, Erdos585.BipartiteBalance.edgeWeight_mk]

lemma cycle_boundary_count (copy : V → U) (outer : V → Bool) (u : U)
    (hinternal : ∀ a b, G.Adj a b → copy a = copy b → outer a ≠ outer b)
    (hexternal : ∀ a b, G.Adj a b → copy a ≠ copy b → outer a = true ∧ outer b = true)
    {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    ((p.edges.toFinset.filter (Crosses copy u)).card : ℤ) =
      2 * ∑ v ∈ p.support.toFinset, localWeight copy outer u v := by
  classical
  have hw := Erdos585.BipartiteBalance.cycle_weight_sum (localWeight copy outer u) hp
  calc
    _ = ∑ e ∈ p.edges.toFinset, Erdos585.BipartiteBalance.edgeWeight
          (localWeight copy outer u) e := by
      symm
      calc
        _ = ∑ e ∈ p.edges.toFinset, (if Crosses copy u e then (1 : ℤ) else 0) := by
          apply sum_congr rfl
          intro e he
          exact edge_weight_is_boundary copy outer u hinternal hexternal
            (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
        _ = _ := by simp
    _ = _ := hw

lemma equal_boundary_counts (copy : V → U) (outer : V → Bool) (u : U)
    (hinternal : ∀ a b, G.Adj a b → copy a = copy b → outer a ≠ outer b)
    (hexternal : ∀ a b, G.Adj a b → copy a ≠ copy b → outer a = true ∧ outer b = true)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset) :
    (p.edges.toFinset.filter (Crosses copy u)).card =
      (q.edges.toFinset.filter (Crosses copy u)).card := by
  have h1 := cycle_boundary_count copy outer u hinternal hexternal hp
  have h2 := cycle_boundary_count copy outer u hinternal hexternal hq
  rw [hS] at h1
  omega

lemma pair_boundary_at_most_three (copy : V → U) (outer : V → Bool) (u : U)
    (hinternal : ∀ a b, G.Adj a b → copy a = copy b → outer a ≠ outer b)
    (hexternal : ∀ a b, G.Adj a b → copy a ≠ copy b → outer a = true ∧ outer b = true)
    (cut : Finset (Sym2 V))
    (hcut : ∀ e ∈ G.edgeSet, Crosses copy u e → e ∈ cut)
    (hsize : cut.card ≤ 7)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) :
    (p.edges.toFinset.filter (Crosses copy u)).card ≤ 3 := by
  classical
  have heq := equal_boundary_counts copy outer u hinternal hexternal hp hq hS
  have hsub : p.edges.toFinset.filter (Crosses copy u) ∪
      q.edges.toFinset.filter (Crosses copy u) ⊆ cut := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hcut e (p.edges_subset_edgeSet (List.mem_toFinset.mp (mem_filter.mp he).1))
        (mem_filter.mp he).2
    · exact hcut e (q.edges_subset_edgeSet (List.mem_toFinset.mp (mem_filter.mp he).1))
        (mem_filter.mp he).2
  have hd : Disjoint (p.edges.toFinset.filter (Crosses copy u))
      (q.edges.toFinset.filter (Crosses copy u)) := hE.mono (filter_subset _ _) (filter_subset _ _)
  have hn := card_le_card hsub
  rw [card_union_of_disjoint hd, heq] at hn
  omega

lemma at_least_two_boundary (copy : V → U) (u : U) (cut : Finset (Sym2 V))
    (hcut : ∀ e ∈ G.edgeSet, e ∈ cut ↔ Crosses copy u e)
    {a : V} {p : G.Walk a a} (hp : p.IsCycle)
    (hin : ∃ x ∈ p.support, copy x = u)
    (hout : ∃ x ∈ p.support, copy x ≠ u) :
    2 ≤ (p.edges.toFinset.filter (Crosses copy u)).card := by
  classical
  let color : V → Bool := fun x => decide (copy x = u)
  have hcolor : ∀ a b, G.Adj a b → color a ≠ color b → s(a,b) ∈ cut := by
    intro x y hxy hne
    apply (hcut _ (G.mem_edgeSet.mpr hxy)).2
    by_cases hx : copy x = u <;> by_cases hy : copy y = u <;>
      simp_all [color]
  have hset : cut ∩ p.edges.toFinset = p.edges.toFinset.filter (Crosses copy u) := by
    ext e
    by_cases he : e ∈ p.edges.toFinset
    · have h := hcut e (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
      simp [he, h]
    · simp [he]
  rw [← hset]
  by_cases ha : copy a = u
  · obtain ⟨x, hx, hxc⟩ := hout
    apply Erdos585.two_le_card_cut_edges color cut hcolor p hp.isTrail hx
    simp [color, ha, hxc]
  · obtain ⟨x, hx, hxc⟩ := hin
    apply Erdos585.two_le_card_cut_edges color cut hcolor p hp.isTrail hx
    simp [color, ha, hxc]

/-- The genuine single-passage statement: two incident links per cycle, for every
copy met by the common support unless the pair is entirely within that copy. -/
theorem single_passage (copy : V → U) (outer : V → Bool) (u : U)
    (hinternal : ∀ a b, G.Adj a b → copy a = copy b → outer a ≠ outer b)
    (hexternal : ∀ a b, G.Adj a b → copy a ≠ copy b → outer a = true ∧ outer b = true)
    (cut : Finset (Sym2 V))
    (hcut : ∀ e ∈ G.edgeSet, e ∈ cut ↔ Crosses copy u e)
    (hsize : cut.card ≤ 7)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (hin : ∃ x ∈ p.support, copy x = u) :
    (∀ x ∈ p.support, copy x = u) ∨
      ((p.edges.toFinset.filter (Crosses copy u)).card = 2 ∧
       (q.edges.toFinset.filter (Crosses copy u)).card = 2) := by
  classical
  by_cases hall : ∀ x ∈ p.support, copy x = u
  · exact Or.inl hall
  right
  have hout : ∃ x ∈ p.support, copy x ≠ u := by simpa using hall
  have hlo := at_least_two_boundary copy u cut hcut hp hin hout
  have hhi := pair_boundary_at_most_three copy outer u hinternal hexternal cut
    (fun e he h => (hcut e he).2 h) hsize hp hq hS hE
  have hw := cycle_boundary_count copy outer u hinternal hexternal hp
  have heq := equal_boundary_counts copy outer u hinternal hexternal hp hq hS
  constructor
  · omega
  · omega

#print axioms single_passage

end RobertPublishable.SUB
