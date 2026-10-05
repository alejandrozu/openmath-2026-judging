import OpHack.SixFibreAP
import OpHack.SixModularFinal

namespace Erdos3Candidate

/-- The explicit positive finite six-fibre set has no nonconstant four-term
    arithmetic progression. The joint modular certificate discharges the
    only hypothesis of the canonical-fibre lifting theorem. -/
theorem sixA_apFree_unconditional : APFree 4 sixA := by
  exact sixA_apFree sixResidues_modular_free

#print axioms sixA_apFree_unconditional

end Erdos3Candidate
