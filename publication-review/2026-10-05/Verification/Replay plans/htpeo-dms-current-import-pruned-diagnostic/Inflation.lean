import InflationDefs
import InflationE

namespace Inflation

theorem inflate_star5 (H : MGraph) (hl : H.Loopless) (slot : Fin H.m → Bool → Fin 3)
    (hinj : PortsInj H slot) :
    ∃ c : Fin (inflate H slot).m → Fin 5, (inflate H slot).Star 5 c := by
  obtain ⟨φ, hφ⟩ := base_coloring_exists H slot hinj
  have hex : ∀ X : Fin H.n, ∃ ρ : Fin 5 → Fin 5,
      Function.Injective ρ ∧
      ∀ e b, endOf H e b = X → ρ (pi (slot e b)) = φ e :=
    local_permutation H slot hl hinj φ hφ
  choose ρ hρ hmatch using hex
  refine ⟨inflCol H slot φ ρ, ?_⟩
  apply inflate_star5_of_matching H slot φ ρ hinj hρ
  intro e b
  exact hmatch (endOf H e b) e b rfl

end Inflation

#print axioms Inflation.inflate_star5
