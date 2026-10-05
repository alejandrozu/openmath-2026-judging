/-
  StarCert.lean — an explicit (decidable) form of the star condition and a machine-checked certificate:
  K₄ with one subdivided edge has a star 6-edge-colouring.
-/
import StarCore

namespace MGraph
variable {G : MGraph}

/-- the walk condition written out over the vertex and edge tuples (no structure quantification) -/
def NoBicolExplicit (k : Nat) (c : Fin G.m → Fin k) : Prop :=
  ∀ v0 v1 v2 v3 v4 : Fin G.n, ∀ e1 e2 e3 e4 : Fin G.m,
    G.Joins e1 v0 v1 → G.Joins e2 v1 v2 → G.Joins e3 v2 v3 → G.Joins e4 v3 v4 →
    v0 ≠ v1 → v0 ≠ v2 → v0 ≠ v3 → v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v2 ≠ v3 → v2 ≠ v4 → v3 ≠ v4 →
    ¬ (c e1 = c e3 ∧ c e2 = c e4)

theorem star_iff_explicit (k : Nat) (c : Fin G.m → Fin k) :
    Star k c ↔ (∀ a b, G.Adj a b → c a ≠ c b) ∧ NoBicolExplicit k c := by
  rw [star_iff]
  constructor
  · rintro ⟨hp, hw⟩
    refine ⟨hp, ?_⟩
    intro v0 v1 v2 v3 v4 e1 e2 e3 e4 h1 h2 h3 h4 d01 d02 d03 d12 d13 d14 d23 d24 d34 hb
    exact hw ⟨v0, v1, v2, v3, v4, e1, e2, e3, e4, h1, h2, h3, h4, d01, d02, d03, d12, d13, d14, d23, d24, d34⟩ hb
  · rintro ⟨hp, hw⟩
    refine ⟨hp, ?_⟩
    intro w hb
    exact hw w.v0 w.v1 w.v2 w.v3 w.v4 w.e1 w.e2 w.e3 w.e4 w.h1 w.h2 w.h3 w.h4
      w.d01 w.d02 w.d03 w.d12 w.d13 w.d14 w.d23 w.d24 w.d34 hb

/-- existential quantification over `Fin n` is decidable (via `Nat.decidableExistsLT'`) -/
instance decExistsFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ x : Fin n, p x) :=
  decidable_of_iff (∃ m, ∃ h : m < n, p ⟨m, h⟩)
    ⟨fun ⟨m, h, hp⟩ => ⟨⟨m, h⟩, hp⟩, fun ⟨⟨m, h⟩, hp⟩ => ⟨m, h, hp⟩⟩

instance decJoins (f : Fin G.m) (x y : Fin G.n) : Decidable (G.Joins f x y) := by
  unfold Joins; infer_instance

instance decInc (f : Fin G.m) (x : Fin G.n) : Decidable (G.Inc f x) := by
  unfold Inc; infer_instance

instance decAdj (a b : Fin G.m) : Decidable (G.Adj a b) := by
  unfold Adj; infer_instance

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
instance decNoBicolExplicit (k : Nat) (c : Fin G.m → Fin k) : Decidable (NoBicolExplicit k c) := by
  unfold NoBicolExplicit; infer_instance

instance decStar (k : Nat) (c : Fin G.m → Fin k) : Decidable (Star k c) :=
  decidable_of_iff _ (star_iff_explicit k c).symm

/-! ### certificate: K₄ with one subdivided edge (5 vertices, 7 edges) is star 6-edge-colourable -/

def k4subdivEdges : List (Fin 5 × Fin 5) := [(0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4), (2, 4)]

def k4subdiv : MGraph where
  n := 5
  m := 7
  ends := fun i => k4subdivEdges.getD i.val (0, 0)

def k4subdivCol : Fin 7 → Fin 6 := fun i => ([0, 1, 1, 4, 2, 5, 3] : List (Fin 6)).getD i.val 0

instance decK4s : Decidable (@Star k4subdiv 6 k4subdivCol) := decStar (G := k4subdiv) 6 k4subdivCol

theorem k4subdiv_star6 : @Star k4subdiv 6 k4subdivCol := by native_decide

end MGraph
