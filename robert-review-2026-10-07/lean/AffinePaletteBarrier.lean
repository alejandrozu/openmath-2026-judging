/-
Copyright 2026 Robert Huynh and Alejandro Zarzuelo Urdiales.
Licensed under the Apache License, Version 2.0.
The graph and move proof generalizes Robert Huynh's characteristic-three
parabola argument to every palette with the stated affine geometry.
-/
import Openmath.Proofs.ParabolaGraph104
import Openmath.Proofs.InducedComponentBarrier104

/-! # A one-round obstruction from affine palette geometry

The premise is an explicit condition on palette points and linear spans,
not an assumed recolouring failure, cycle exclusion or graph degree bound.
The conclusion concerns actual component-union swaps and actual IsCycle walks.
-/
noncomputable section
namespace OpenMathReview.AffinePaletteBarrier
open SimpleGraph Finset Erdos585 KempeSwap104
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [DecidableEq V]

/-- Affine spans of at most three palette points contain no extra palette point. -/
def TripleClosed (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ z ∈ S,
    z - a ∈ Submodule.span (ZMod 3) ({b - a, c - a} : Set V) →
      z = a ∨ z = b ∨ z = c

/-- Unordered pair sums determine their two summands, allowing repetition. -/
def Sidon (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

private theorem triple_self (x : V) : x+x+x=0 := by
  calc
    x+x+x = (1+1+1 : ZMod 3) • x := by simp only [add_smul,one_smul]
    _ = 0 := by rw [show (1+1+1 : ZMod 3)=0 by decide, zero_smul]

private theorem scalar_three_cases (u : ZMod 3) : u=0 ∨ u=1 ∨ u= -1 := by
  fin_cases u
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Known Sidon-to-2-cap implication, stated as the precise span interface needed here. -/
theorem tripleClosed_of_sidon (S : Finset V) (hs : Sidon S) : TripleClosed S := by
  intro a ha b hb c hc z hz hspan
  obtain ⟨u,v,huv⟩ := Submodule.mem_span_pair.mp hspan
  rcases scalar_three_cases u with rfl | rfl | rfl <;>
    rcases scalar_three_cases v with rfl | rfl | rfl <;>
    simp only [zero_smul,one_smul,neg_one_smul,zero_add,add_zero] at huv
  · left
    exact sub_eq_zero.mp huv.symm
  · right; right
    exact sub_left_injective huv.symm
  · have hp : z+c=a+a := by
      have he := congrArg (fun w : V => w+a+c) huv
      convert he.symm using 1 <;> abel
    rcases hs z hz c hc a ha a ha hp with ⟨hza,_⟩ | ⟨hza,_⟩ <;> exact Or.inl hza
  · right; left
    exact sub_left_injective huv.symm
  · have hp : z+a=b+c := by
      have he := congrArg (fun w : V => w+a+a) huv
      convert he.symm using 1 <;> abel
    rcases hs z hz a ha b hb c hc hp with ⟨hzb,_⟩ | ⟨hzc,_⟩
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inr hzc)
  · have hp : z+c=a+b := by
      have he := congrArg (fun w : V => w+a+c) huv
      convert he.symm using 1 <;> abel
    rcases hs z hz c hc a ha b hb hp with ⟨hza,_⟩ | ⟨hzb,_⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzb)
  · have hp : z+b=a+a := by
      have he := congrArg (fun w : V => w+a+b) huv
      convert he.symm using 1 <;> abel
    rcases hs z hz b hb a ha a ha hp with ⟨hza,_⟩ | ⟨hza,_⟩ <;> exact Or.inl hza
  · have hp : z+b=a+c := by
      have he := congrArg (fun w : V => w+a+b) huv
      convert he.symm using 1 <;> abel
    rcases hs z hz b hb a ha c hc hp with ⟨hza,_⟩ | ⟨hzc,_⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inr hzc)
  · have hsum : z+b+c=a+a+a := by
      have he := congrArg (fun w : V => w+a+b+c) huv
      convert he.symm using 1 <;> abel
    rw [triple_self] at hsum
    have hzz : z+z= -z := eq_neg_of_add_eq_zero_left (triple_self z)
    have hbc : b+c= -z := eq_neg_of_add_eq_zero_right (by simpa only [add_assoc] using hsum)
    have hp : z+z=b+c := hzz.trans hbc.symm
    rcases hs z hz z hz b hb c hc hp with ⟨hzb,_⟩ | ⟨_,hzb⟩
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inl hzb)

private theorem exists_eq_triple (T : Finset V) (hne : T.Nonempty) (hc : T.card ≤ 3) :
    ∃ a b c : V, T = {a, b, c} := by
  have hp := hne.card_pos
  have h : T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases h with h | h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, b, by simp⟩
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h
    exact ⟨a, b, c, rfl⟩

private theorem differenceSpan_triple (a b c : V) :
    HaarComponents104.differenceSpan {a, b, c} a =
      Submodule.span (ZMod 3) ({b - a, c - a} : Set V) := by
  unfold HaarComponents104.differenceSpan
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨s, hs, rfl⟩
    simp only [Finset.mem_coe, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · simp
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span ⟨b, by simp, rfl⟩
    · exact Submodule.subset_span ⟨c, by simp, rfl⟩

/-- The finite palette geometry implies inducedness of every small-colour component. -/
theorem component_induced (S T : Finset V) (hcap : TripleClosed S)
    (hTS : T ⊆ S) (hne : T.Nonempty) (hc : T.card ≤ 3)
    {u v : V × Bool} (hr : (Haar.graph T).Reachable u v)
    (he : (Haar.graph S).Adj u v) : (Haar.graph T).Adj u v := by
  obtain ⟨a, b, c, rfl⟩ := exists_eq_triple T hne hc
  have ha : a ∈ S := hTS (by simp)
  have hb : b ∈ S := hTS (by simp)
  have hcc : c ∈ S := hTS (by simp)
  have aux (X Y : V)
      (hR : (Haar.graph {a, b, c}).Reachable (X, false) (Y, true))
      (hE : (Haar.graph S).Adj (X, false) (Y, true)) :
      (Haar.graph {a, b, c}).Adj (X, false) (Y, true) := by
    have hm := (HaarComponents104.reachable_iff_mem_differenceSpan
      {a, b, c} (by simp : a ∈ ({a,b,c} : Finset V)) X Y true).mp hR
    simp only [ite_true] at hm
    rw [differenceSpan_triple] at hm
    have hz := (Haar.graph_cross S X Y).mp hE
    have heq : (Y - X) - a = Y - X - a := rfl
    have hmem := hcap a ha b hb c hcc (Y-X) hz hm
    exact (Haar.graph_cross _ _ _).mpr (by simpa using hmem)
  obtain ⟨X, d⟩ := u
  obtain ⟨Y, e⟩ := v
  cases d <;> cases e
  · exact (Haar.graph_same _ _ _ false he).elim
  · exact aux X Y hr he
  · exact (aux Y X hr.symm he.symm).symm
  · exact (Haar.graph_same _ _ _ true he).elim

abbrev Color (S : Finset V) := {s : V // s ∈ S}

def palette (S : Finset V) (T : Finset (Color S)) : Finset V := T.image Subtype.val

theorem palette_subset (S : Finset V) (T : Finset (Color S)) : palette S T ⊆ S := by
  rintro x hx
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
  exact c.property

theorem palette_card (S : Finset V) (T : Finset (Color S)) : (palette S T).card = T.card :=
  Finset.card_image_of_injective T Subtype.val_injective

private theorem shift_mem (S : Finset V) {x y : V × Bool} (h : (Haar.graph S).Adj x y) :
    (if x.2 then x.1-y.1 else y.1-x.1) ∈ S := by
  rcases h with h | h <;> simp [h.1, h.2.1, h.2.2]

def canonical (S : Finset V) : (Haar.graph S).EdgeLabeling (Color S) :=
  EdgeLabeling.mk
    (fun x y h => ⟨if x.2 then x.1-y.1 else y.1-x.1, shift_mem S h⟩)
    (by
      intro x y h
      apply Subtype.ext
      rcases h with h | h <;> simp [h.1, h.2.1])

theorem canonical_label_cross (S : Finset V) (c : Color S) (X Y : V) :
    ((canonical S).labelGraph c).Adj (X, false) (Y, true) ↔ Y-X=c.val := by
  rw [EdgeLabeling.labelGraph_adj]
  constructor
  · rintro ⟨h, hc⟩
    exact congrArg Subtype.val hc
  · intro he
    refine ⟨(Haar.graph_cross S X Y).mpr (he ▸ c.property), ?_⟩
    exact Subtype.ext he

theorem canonical_labelGraph (S : Finset V) (c : Color S) :
    (canonical S).labelGraph c = Haar.graph {c.val} := by
  ext ⟨X,b⟩ ⟨Y,d⟩
  cases b <;> cases d
  · constructor
    · intro h
      exact (Haar.graph_same S X Y false ((canonical S).labelGraph_le h)).elim
    · intro h
      exact (Haar.graph_same {c.val} X Y false h).elim
  · simp [canonical_label_cross, Haar.graph_cross]
  · rw [SimpleGraph.adj_comm, canonical_label_cross, SimpleGraph.adj_comm]
    simp [Haar.graph_cross]
  · constructor
    · intro h
      exact (Haar.graph_same S X Y true ((canonical S).labelGraph_le h)).elim
    · intro h
      exact (Haar.graph_same {c.val} X Y true h).elim

theorem canonical_full (S : Finset V) : FullColoring (canonical S) := by
  intro v c
  rw [canonical_labelGraph]
  obtain ⟨X,b⟩ := v
  cases b
  · refine ⟨(X+c.val,true), ?_, ?_⟩
    · simp [Haar.graph_cross]
    · rintro ⟨Y,d⟩ h
      cases d
      · exact (Haar.graph_same _ _ _ false h).elim
      · have he : Y-X=c.val := by simpa [Haar.graph_cross] using h
        have hy : Y=X+c.val := by rw [← he]; abel
        exact congrArg (fun y : V => (y,true)) hy
  · refine ⟨(X-c.val,false), ?_, ?_⟩
    · apply SimpleGraph.Adj.symm
      simp [Haar.graph_cross]
    · rintro ⟨Y,d⟩ h
      cases d
      · have he : X-Y=c.val := by simpa [Haar.graph_cross] using h.symm
        have hy : Y=X-c.val := by rw [← he]; abel
        exact congrArg (fun y : V => (y,false)) hy
      · exact (Haar.graph_same _ _ _ true h).elim

theorem canonical_colorSubgraph (S : Finset V) (T : Finset (Color S)) :
    colorSubgraph (canonical S) T = Haar.graph (palette S T) := by
  ext x y
  rw [colorSubgraph_adj]
  simp only [canonical_labelGraph]
  obtain ⟨X,b⟩ := x
  obtain ⟨Y,d⟩ := y
  cases b <;> cases d <;> simp [Haar.graph, palette]

variable [Fintype V]

/-- The general palette theorem has genuine moves and cycle-partner exclusion. -/
theorem exposed_cycle_no_partner (S : Finset V) (hcap : TripleClosed S)
    (a b : Color S) (J : Set (twoFactor (canonical S) a b).ConnectedComponent)
    (i j : Color S) {u : V × Bool}
    (p : (twoFactor (swap (canonical S) a b J) i j).Walk u u) (hp : p.IsCycle) :
    ¬ ∃ (w : V × Bool) (q : (Haar.graph S).Walk w w), q.IsCycle ∧
      (p.mapLe (twoFactor_le (swap (canonical S) a b J) i j)).support.toFinset =
        q.support.toFinset ∧
      Disjoint (p.mapLe (twoFactor_le (swap (canonical S) a b J) i j)).edges.toFinset
        q.edges.toFinset := by
  obtain ⟨T, hT, hc, hfactor⟩ := swap_factor_palette (canonical S) a b J i j
  rw [canonical_colorSubgraph] at hfactor
  have hpne : (palette S T).Nonempty := by
    obtain ⟨c,hc⟩ := hT
    exact ⟨c.val, mem_image.mpr ⟨c,hc,rfl⟩⟩
  have hcard : (palette S T).card ≤ 3 := by rwa [palette_card]
  have hh := InducedComponentBarrier104.no_partner
    (Haar.graph_mono (palette_subset S T))
    (fun x y hr he => component_induced S (palette S T) hcap (palette_subset S T) hpne hcard hr he)
    (fun x => by rw [HaarDegree.degree_eq_card]; exact hcard)
    (p.mapLe hfactor) (hp.mapLe hfactor)
  simpa only [Walk.support_mapLe_eq_support, Walk.edges_mapLe_eq_edges] using hh

/-- The actual one-round detector obstruction for every finite Sidon palette. -/
theorem sidon_exposed_cycle_no_partner (S : Finset V) (hs : Sidon S)
    (a b : Color S) (J : Set (twoFactor (canonical S) a b).ConnectedComponent)
    (i j : Color S) {u : V × Bool}
    (p : (twoFactor (swap (canonical S) a b J) i j).Walk u u) (hp : p.IsCycle) :
    ¬ ∃ (w : V × Bool) (q : (Haar.graph S).Walk w w), q.IsCycle ∧
      (p.mapLe (twoFactor_le (swap (canonical S) a b J) i j)).support.toFinset =
        q.support.toFinset ∧
      Disjoint (p.mapLe (twoFactor_le (swap (canonical S) a b J) i j)).edges.toFinset
        q.edges.toFinset :=
  exposed_cycle_no_partner S (tripleClosed_of_sidon S hs) a b J i j p hp

#print axioms component_induced
#print axioms tripleClosed_of_sidon
#print axioms canonical_full
#print axioms exposed_cycle_no_partner
#print axioms sidon_exposed_cycle_no_partner
#check @exposed_cycle_no_partner
#check @sidon_exposed_cycle_no_partner
end OpenMathReview.AffinePaletteBarrier
