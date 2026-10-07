/-
Copyright (c) 2025 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Partition

/-!
# Main Definitions

Definitions used in the statements of the two main theorems:

* **Haxell's theorem** (`PartitionedGraph.haxell_theorem` in `Haxell.lean`):
  Every (2Δ)-thick partitioned graph has an independent transversal.

* **Theorem 1.2** (`PartitionedGraph.main_theorem` in `MainProof.lean`):
  For irreducible (2Δ)-thick partitioned graphs not isomorphic to disjoint K_{Δ,Δ},
  the reconfigurability graph of independent transversals is connected.

A reader can find both theorem statements in `Main.lean` and click through
to this file for every definition they use.

## Definitions

* `PartitionedGraph` - A simple graph G on V together with a partition U of V into blocks
* `PartitionedGraph.isThick t` - Every block of U has at least t vertices
* `PartitionedGraph.IsIndependentTransversal` - S is an independent set of G meeting each
  block of U exactly once
* `PartitionedGraph.ReconfigAdj` - Adjacency in the reconfigurability graph of (G, U)
* `PartitionedGraph.Reconfigurable` - Path-connectedness in the reconfigurability graph
  of (G, U)
* `PartitionedGraph.irreducible` - Every proper nonempty subset of blocks of U has an edge
  of G to its complement
* `PartitionedGraph.isExceptional` - (G, U) is exceptional: G is isomorphic to a disjoint
  union of |U| copies of K_{Δ,Δ}, where Δ is the maximum degree of G

-/

open scoped Set

namespace IndependentTransversals

variable {V : Type*} [DecidableEq V]

/-- A partitioned graph (often written as the pair (G, U) in the paper) is a simple
    graph G together with a partition U of its vertex set.

    We use `Setoid.IsPartition` from Mathlib which says:
    * `∅ ∉ blocks` (no empty blocks)
    * `∀ a, ∃! b ∈ blocks, a ∈ b` (each vertex is in exactly one block) -/
structure PartitionedGraph (V : Type*) [DecidableEq V] where
  /-- The underlying graph G -/
  graph : SimpleGraph V
  /-- The collection of blocks U -/
  blocks : Set (Set V)
  /-- The blocks form a partition of V -/
  isPartition : Setoid.IsPartition blocks

namespace PartitionedGraph

variable (G : PartitionedGraph V)

/-- A partition is t-thick if every block has at least t vertices. -/
def isThick (t : ℕ) : Prop :=
  ∀ U ∈ G.blocks, t ≤ U.ncard

variable [Fintype V]

/-- A set S is an independent transversal of a partitioned graph if it is an independent set
    of G that meets each block of U in exactly one vertex. -/
def IsIndependentTransversal (S : Set V) : Prop :=
  G.graph.IsIndepSet S ∧
  ∀ U ∈ G.blocks, ∃! v, v ∈ S ∩ U

/-- Given a set of blocks R ⊆ U, the union of all blocks in R. Paper notation: V_R -/
def blockUnion (R : Set (Set V)) : Set V :=
  ⋃₀ (R ∩ G.blocks)

end PartitionedGraph

/-! ### Reconfigurability Graph -/

section ReconfigGraph

variable [Fintype V] (G : PartitionedGraph V)

/-- Two independent transversals S and T are adjacent in the reconfigurability graph
    if S ∪ T is independent and has size |U| + 1 (i.e., they differ on exactly one block
    and the two vertices in that block are non-adjacent). -/
def PartitionedGraph.ReconfigAdj (S T : Set V) : Prop :=
  G.IsIndependentTransversal S ∧
  G.IsIndependentTransversal T ∧
  G.graph.IsIndepSet (S ∪ T) ∧
  (S ∪ T).ncard = G.blocks.ncard + 1

/-- Two independent transversals are reconfigurable if there is a path between them
    in the reconfigurability graph. -/
def PartitionedGraph.Reconfigurable (S T : Set V) : Prop :=
  Relation.ReflTransGen G.ReconfigAdj S T

end ReconfigGraph

/-! ### Irreducibility -/

section Irreducibility

variable [Fintype V] (G : PartitionedGraph V)

/-- A partitioned graph is irreducible if it cannot be written as a disjoint union of two
    nontrivial partitioned graphs. Equivalently, the graph restricted to any proper nonempty
    subset of blocks has edges connecting it to the complement. -/
def PartitionedGraph.irreducible : Prop :=
  ∀ R, R ⊂ G.blocks → R.Nonempty →
    ∃ v ∈ G.blockUnion R, ∃ w ∈ G.blockUnion (G.blocks \ R), G.graph.Adj v w

end Irreducibility

/-! ### Exceptional Structure -/

section CompleteBipartite

variable [Fintype V] (G : PartitionedGraph V) [DecidableRel G.graph.Adj]

/-- Auxiliary definition: G is a disjoint union of |U| copies of K_{Δ,Δ} for a given Δ.
    The induction proof needs Δ as a free parameter (it is fixed at the top level while
    subgraphs may have smaller max degree). See `isExceptional` for the top-level version. -/
def PartitionedGraph.isDisjointKDD (Δ : ℕ) : Prop :=
  -- Number of components equals number of blocks
  (Nat.card G.graph.ConnectedComponent = G.blocks.ncard) ∧
  -- Each component is isomorphic to K_{Δ,Δ}
  (∀ C : G.graph.ConnectedComponent,
    Nonempty (G.graph.induce C.supp ≃g
      completeBipartiteGraph (Fin Δ) (Fin Δ)))

/-- A partitioned graph (G, U) is *exceptional* if G is isomorphic to a disjoint union
    of |U| copies of the complete bipartite graph K_{Δ,Δ}, where Δ is the maximum degree
    of G. Formally:
    1. The number of connected components of G equals |U|
    2. Each connected component is isomorphic to K_{Δ,Δ}

    When (G, U) has this structure, reconfiguration between independent transversals
    may not be possible; this is the sole obstruction in Theorem 1.2. -/
def PartitionedGraph.isExceptional : Prop :=
  G.isDisjointKDD G.graph.maxDegree

end CompleteBipartite

end IndependentTransversals
