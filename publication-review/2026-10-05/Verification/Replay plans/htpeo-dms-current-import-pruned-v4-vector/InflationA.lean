import InflationDefs
import Mathlib.Data.Fin.VecNotation

namespace Inflation

def kappa (s : Fin 12) : Fin 5 := ![0, 1, 2, 2, 3, 4, 0, 2, 3, 4, 0, 1] s
def pi (i : Fin 3) : Fin 5 := ![4, 3, 1] i
def seen (a : Fin 9) : Finset (Fin 5) :=
  ![{0, 2, 4}, {0, 1, 3}, {1, 2, 4}, {0, 2, 3}, {0, 1, 2},
    {1, 2, 3}, {2, 3, 4}, {0, 3, 4}, {0, 1, 4}] a

theorem table_piece_mem : ∀ s : Fin 12,
    kappa s ∈ seen (pe1 s.val) ∧ kappa s ∈ seen (pe2 s.val) := by decide

theorem table_piece_rich : ∀ s : Fin 12, ∀ z : Fin 5,
    z ∈ seen (pe1 s.val) → z ∈ seen (pe2 s.val) → z = kappa s := by decide

theorem table_piece_proper : ∀ s t : Fin 12, ∀ a : Fin 9,
    s ≠ t → (pe1 s.val = a ∨ pe2 s.val = a) →
    (pe1 t.val = a ∨ pe2 t.val = a) → kappa s ≠ kappa t := by decide

theorem table_port_mem : ∀ i : Fin 3, pi i ∈ seen (portv i) := by decide

theorem table_port_proper : ∀ i : Fin 3, ∀ s : Fin 12,
    (pe1 s.val = portv i ∨ pe2 s.val = portv i) → kappa s ≠ pi i := by decide

theorem table_port_inj : Function.Injective portv := by decide
theorem table_pi_inj : Function.Injective pi := by decide

end Inflation

namespace MGraph

/-- An incident-colour set at each vertex gives the star property when each edge
except for one possible exceptional edge per vertex has a unique shared colour. -/
theorem star_of_seen (G : MGraph) (c : Fin G.m → Fin 5)
    (S : Fin G.n → Finset (Fin 5)) (P : Fin G.m → Prop)
    (hmem : ∀ e x, G.Inc e x → c e ∈ S x)
    (hproper : ∀ a b, G.Adj a b → c a ≠ c b)
    (hrich : ∀ e x y, P e → G.Joins e x y →
      ∀ z, z ∈ S x → z ∈ S y → z = c e)
    (hunique : ∀ a b x, ¬ P a → ¬ P b → G.Inc a x → G.Inc b x → a = b) :
    G.Star 5 c := by
  apply (star_iff 5 c).2
  refine ⟨hproper, ?_⟩
  intro w hb
  have adj23 : G.Adj w.e2 w.e3 :=
    ⟨w.e2_ne_e3, w.v2, w.inc_e2_v2, w.inc_e3_v2⟩
  have neq23 := hproper w.e2 w.e3 adj23
  by_cases hp2 : P w.e2
  · have hc1 : c w.e3 ∈ S w.v1 := hb.1 ▸ hmem w.e1 w.v1 w.inc_e1_v1
    have hc3 : c w.e3 ∈ S w.v2 := hmem w.e3 w.v2 w.inc_e3_v2
    have heq := hrich w.e2 w.v1 w.v2 hp2 w.h2 (c w.e3) hc1 hc3
    exact neq23 heq.symm
  by_cases hp3 : P w.e3
  · have hc4 : c w.e2 ∈ S w.v3 := hb.2 ▸ hmem w.e4 w.v3 w.inc_e4_v3
    have hc2 : c w.e2 ∈ S w.v2 := hmem w.e2 w.v2 w.inc_e2_v2
    have heq := hrich w.e3 w.v2 w.v3 hp3 w.h3 (c w.e2) hc2 hc4
    exact neq23 heq
  exact w.e2_ne_e3 (hunique w.e2 w.e3 w.v2 hp2 hp3 w.inc_e2_v2 w.inc_e3_v2)

end MGraph
