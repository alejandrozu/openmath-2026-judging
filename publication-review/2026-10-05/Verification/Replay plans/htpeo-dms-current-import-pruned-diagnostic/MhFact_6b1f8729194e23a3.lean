-- Lean proof of fact 6b1f8729194e23a3 (RH2F.layer36); added by fact_submit, do not edit
import MhFact_c03bb6e1daa663e4
import MhFact_78d98836f6372f68
import MhFact_4e63409f7b05a806
import MhFact_4b7436a78212f56a
import MhFact_916ccd41e9db4312
import MhFact_78a34517ee1a6fff
import MhFact_0e0e37a38e3c97d5
import MhFact_f645e06d2ce727a3
import MhFact_c35583f86422a75a
import MhFact_51ff9480dc00823f
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000

-- ===== from FE6.lean =====
/-
  FE6 — the classification of the c4c members of 𝒮 with 16 vertices, far-exchange existence (FE-EXIST-D) on all
  digon insertions with exactly 16 vertices, and the reduction of (FE-EXIST-D)₁₀ to hosts with at least 18
  vertices.
-/

namespace RH2F
open MGraph

/-- the insertion tables of all hosts of 𝒮_14 -/
theorem htab14W : ∀ k, k < sRep14.length → HostTabW 14 sRep14 c16 (by decide) (by decide) k := by
  intro k hk
  have hl : sRep14.length = 341 := sRep14_len
  by_cases h0 : k < 45
  · exact wTab14R_0_45 k (by omega) h0 hk
  by_cases h1 : k < 90
  · exact wTab14R_45_90 k (by omega) h1 hk
  by_cases h2 : k < 135
  · exact wTab14R_90_135 k (by omega) h2 hk
  by_cases h3 : k < 180
  · exact wTab14R_135_180 k (by omega) h3 hk
  by_cases h4 : k < 225
  · exact wTab14R_180_225 k (by omega) h4 hk
  by_cases h5 : k < 270
  · exact wTab14R_225_270 k (by omega) h5 hk
  by_cases h6 : k < 315
  · exact wTab14R_270_315 k (by omega) h6 hk
  exact wTab14R_315_341 k (by omega) (by omega) hk

/-- **classification of the cyclically 4-edge-connected simple members of 𝒢 with 16 vertices**: each is
    isomorphic to one of the 607 listed graphs `c16` -/
theorem cls16c : ∀ (X : MGraph) (P : Fin X.m → Prop), C4C X P → SimpleP P → vcount P = 16 →
    ∃ k, k < c16.length ∧ IsoFrom P (ofList 16 (c16.getD k []) (by decide)) :=
  cls_stepC (n := 14) (by decide) (by decide) (by decide) (repsOK_of_repsB sRep14_B) scl14 htab14W

/-- far-exchange existence at every edge and status, on the digon insertions of hosts of (FE-EXIST-D)₁₀ with
    exactly 16 vertices -/
def FEEXIST16 : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Host10 Y Q D → vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) = 16 →
    ∀ g, digSet Q D g → ∀ t : Bool, ∃ M, PMOn (digSet Q D) M ∧ (M g ↔ t = true) ∧ ∃ C, FarEx (digSet Q D) M C

/-- (FE-EXIST-D)₁₀ restricted to digon insertions with at least 18 vertices -/
def FEEXISTD18 : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), Host10 Y Q D → 18 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) →
    ∀ g, digSet Q D g → ∀ t : Bool, ∃ M, PMOn (digSet Q D) M ∧ (M g ↔ t = true) ∧ ∃ C, FarEx (digSet Q D) M C

/-- **(FE-EXIST-D) at 16 vertices** -/
theorem feexist16 : FEEXIST16 := by
  intro Y Q D hH htot
  obtain ⟨hC, hS, h10, _⟩ := hH
  have hev := vcount_even' hC.1
  have hv : vcount Q = 10 ∨ vcount Q = 12 ∨ vcount Q = 14 ∨ vcount Q = 16 := by omega
  rcases hv with hv | hv | hv | hv
  · exact fe_of_hosts scl10 (fun k hk => hfe10R_0_14 k (Nat.zero_le _) (by rw [sRep10_len] at hk; exact hk))
      Y Q D hC hS hv (by omega) (by omega)
  · exact fe_of_hosts scl12 (fun k hk => hfe12R_0_57 k (Nat.zero_le _) (by rw [sRep12_len] at hk; exact hk))
      Y Q D hC hS hv (by omega) (by omega)
  · exact fe_of_hosts scl14 (fun k hk => hfe14R_0_341 k (Nat.zero_le _) (by rw [sRep14_len] at hk; exact hk))
      Y Q D hC hS hv (by omega) (by omega)
  · obtain ⟨k, hk, hI⟩ := cls16c Y Q hC hS hv
    exact hfe16R_0_607 k (Nat.zero_le _) (by rw [c16_len] at hk; exact hk) Y Q D hC.1.1 hI (by omega)

/-- **(FE-EXIST-D)₁₀ from its part on at least 18 vertices** -/
theorem feexistD10_of_18 (h18 : FEEXISTD18) : FEEXISTD10 := by
  intro Y Q D hH g hg t
  have hev := vcount_even' hH.1.1
  have h16 := hH.2.2.2
  by_cases h : vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) = 16
  · exact feexist16 Y Q D hH h g hg t
  · exact h18 Y Q D hH (by omega) g hg t

/-- **layer 36** -/
theorem layer36 : FEEXIST16 ∧ (FEEXISTD18 → FEEXISTD10) := ⟨feexist16, feexistD10_of_18⟩

end RH2F
