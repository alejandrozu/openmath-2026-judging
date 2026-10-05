/-
  star6: statement check and axiom report for the main theorems (Lean 4.33.1 + Mathlib v4.33.1).
  Built by run433.sh (lean Main.lean with LEAN_PATH) or by lake build; see README.md.
-/
import MhFact_ba4d9c5abd0afd83
import MhFact_6c78409a046a3fe7

open RH2F in
example :
    BASE12 ∧ SIMPLE14 ∧ B14D ∧ FEEXIST16 ∧ (IID16 → IID) ∧ (FEEXISTD18 → FEEXISTD10) ∧
    (FEEXTTNE16 → FEEXIST0NE16 → IID16) ∧
    (FEEXTD10 → FEEXISTD18 → POLE → TDTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD18 → WEXT → TDLTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD18 → POLE → TDTRI → FEEXTTNE16 → FEEXIST0NE16 → DMS) := layer37

/-- the conditional main theorem, route A (hypotheses are named open statements, not axioms) -/
theorem star6_dms_conditional_A :
    RH2F.FEEXTD10 → RH2F.FEEXISTD18 → RH2F.POLE → RH2F.TDTRI → RH2F.FEEXTTNE16 → RH2F.FEEXIST0NE16 → RH2F.DMS :=
  RH2F.layer37.2.2.2.2.2.2.2.2.2

/-- the conditional main theorem, route B -/
theorem star6_dms_conditional_B :
    RH2F.FEEXTD10 → RH2F.FEEXISTD18 → RH2F.WEXT → RH2F.TDLTRI → RH2F.IID16 → RH2F.DMS :=
  RH2F.layer37.2.2.2.2.2.2.2.2.1

/-- the unconditional finite theorems -/
theorem star6_finite : RH2F.BASE12 ∧ RH2F.SIMPLE14 ∧ RH2F.B14D ∧ RH2F.FEEXIST16 :=
  ⟨RH2F.layer37.1, RH2F.layer37.2.1, RH2F.layer37.2.2.1, RH2F.layer37.2.2.2.1⟩

#print RH2F.DMS
#check @RH2Fid.fidelity_bundle
#print axioms RH2F.layer37
#print axioms star6_dms_conditional_A
#print axioms star6_dms_conditional_B
#print axioms star6_finite
#print axioms RH2F.layer37a
#print axioms RH2F.layer35
#print axioms RH2F.layer32d
#print axioms RH2F.layer28
#print axioms RH2F.base12
#print axioms RH2F.simple14
#print axioms RH2F.b14d
#print axioms RH2F.feexist16
#print axioms RH2F.feexistD10_of_18
#print axioms RH2F.iid16_of_ne
#print axioms RH2F.cls16c
#print axioms RH2F.rh2_final
#print axioms RH2P.layerP
#print axioms RH2Fid.fidelity_bundle
