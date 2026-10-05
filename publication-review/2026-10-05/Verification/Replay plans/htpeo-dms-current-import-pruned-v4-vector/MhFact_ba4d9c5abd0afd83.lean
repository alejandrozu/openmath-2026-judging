-- Lean proof of fact ba4d9c5abd0afd83 (RH2F.layer37); added by fact_submit, do not edit
import MhFact_1b2e17f98116d9aa
import MhFact_6b1f8729194e23a3
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000

/-
  Layer 37 — ROOT-CS4 in Lean with all finite parts discharged: BASE12, SIMPLE14, B14D and the leaf case (II_D) on at
  most 14 vertices (layer 37a) and (FE-EXIST-D) on 16 vertices (layer 36); and (II_D) on at least 16 vertices from the
  leaf engine statements (FE-EXT-T-NE)₁₆ and (FE-EXIST-0-NE)₁₆ (contracts P31, P30).
-/

namespace RH2F
open MGraph

/-- (II_D) on at least 16 vertices from the leaf engine statements -/
theorem iid16_of_ne (hextT : FEEXTTNE16) (hex0 : FEEXIST0NE16) : IID16 := by
  intro X P hG h16 h2 g hg hpar hcut
  have hel : Eligible P g := ⟨hg, hpar, hcut⟩
  obtain ⟨M, hM, hMg, C, hC, hCg, hne⟩ := hex0 X P hG h2 h16 g hel
  obtain ⟨c, hc, _⟩ := hextT X P hG h2 h16 g hel M C hM hMg hC hCg hne
  exact ⟨c, hc⟩

/-- **layer 37** -/
theorem layer37 :
    BASE12 ∧ SIMPLE14 ∧ B14D ∧ FEEXIST16 ∧ (IID16 → IID) ∧ (FEEXISTD18 → FEEXISTD10) ∧
    (FEEXTTNE16 → FEEXIST0NE16 → IID16) ∧
    (FEEXTD10 → FEEXISTD18 → POLE → TDTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD18 → WEXT → TDLTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD18 → POLE → TDTRI → FEEXTTNE16 → FEEXIST0NE16 → DMS) :=
  ⟨layer37a.1, layer37a.2.1, layer37a.2.2.1, feexist16, layer37a.2.2.2.1, feexistD10_of_18, iid16_of_ne,
   fun hext hex hpole htd hD => layer37a.2.2.2.2.1 hext (feexistD10_of_18 hex) hpole htd hD,
   fun hext hex hW htdl hD => layer37a.2.2.2.2.2 hext (feexistD10_of_18 hex) hW htdl hD,
   fun hext hex hpole htd hT h0 => layer37a.2.2.2.2.1 hext (feexistD10_of_18 hex) hpole htd (iid16_of_ne hT h0)⟩

end RH2F
