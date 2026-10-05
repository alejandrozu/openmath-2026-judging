-- Lean proof of fact 38b6f78a47fdf12e (RH2F.layer32d); added by fact_submit, do not edit
import MhFact_f4c06558ba3030b8
import MhFact_def3ba43f6eccb6d
import MhFact_256b4143cc30000f
import MhFact_a8bfe25dadf921db
set_option backward.isDefEq.respectTransparency false

-- ===== from L32d.lean =====
namespace RH2F
open MGraph

/-- all hosts of 𝒮_4 -/
theorem gA4 : ∀ k, k < sRep4.length → ∀ rc ∈ dRCa4.getD k [], GoodH (digGrC 4 (by decide) (sRep4.getD k []) rc) := by
  intro k hk
  have hK : sRep4.length = 1 := sRep4_len
  rcases (by omega : k = 0) with rfl
  · exact gA4_0

/-- all hosts of 𝒮_6 -/
theorem gA6 : ∀ k, k < sRep6.length → ∀ rc ∈ dRCa6.getD k [], GoodH (digGrC 6 (by decide) (sRep6.getD k []) rc) := by
  intro k hk
  have hK : sRep6.length = 2 := sRep6_len
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact gA6_0
  · exact gA6_1

/-- all hosts of 𝒮_8 -/
theorem gA8 : ∀ k, k < sRep8.length → ∀ rc ∈ dRCa8.getD k [], GoodH (digGrC 8 (by decide) (sRep8.getD k []) rc) := by
  intro k hk
  have hK : sRep8.length = 4 := sRep8_len
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact gA8_0
  · exact gA8_1
  · exact gA8_2
  · exact gA8_3

/-- all hosts of 𝒮_10 -/
theorem gA10 : ∀ k, k < sRep10.length → ∀ rc ∈ dRCa10.getD k [], GoodH (digGrC 10 (by decide) (sRep10.getD k []) rc) := by
  intro k hk
  have hK : sRep10.length = 14 := sRep10_len
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gA10_0
  · exact gA10_1
  · exact gA10_2
  · exact gA10_3
  · exact gA10_4
  · exact gA10_5
  · exact gA10_6
  · exact gA10_7
  · exact gA10_8
  · exact gA10_9
  · exact gA10_10
  · exact gA10_11
  · exact gA10_12
  · exact gA10_13

/-- the hosts of 𝒮_12 at the code 0 -/
theorem gA12z : ∀ k, k < sRep12.length → GoodH (digGrC 12 (by decide) (sRep12.getD k []) 0) := by
  intro k hk
  have hmem : ∀ k, k < 57 → (0 : Nat) ∈ dRCa12.getD k [] := by decide
  have hk' : k < 57 := by rw [sRep12_len] at hk; exact hk
  exact layer32c k (Nat.zero_le _) hk' 0 (hmem k hk')

/-- **the members of 𝒟 with 10 or 12 vertices** -/
theorem d1012 : ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 10 ≤ vcount P → vcount P ≤ 12 →
    EX1On P ∧ ∀ g, Eligible P g → Colourable (leafSet P g) 6 :=
  d1012_of gA4 gA6 gA8 gA10 gA12z

/-- **BASE12** (the Lean definition of fact 30194dab4e05fdcf) -/
theorem base12 : BASE12 := fun X P hG h2 hv => (d1012 X P hG h2 (by omega) (by omega)).1

/-- **(II_D) on at most 12 vertices** -/
theorem iid12 : ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 6 ≤ vcount P → vcount P ≤ 12 → TwoCutReducedOn P →
    ∀ g, P g → (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) → (∀ S, TwoCut P S → ¬ Crosses P S g) →
    Colourable (leafSet P g) 6 := by
  intro X P hG h6 h12 h2 g hg hpar hcut
  by_cases h8 : vcount P ≤ 8
  · exact small_leaf hG h8 hg
  · have hev := vcount_even' hG
    exact (d1012 X P hG h2 (by omega) h12).2 g ⟨hg, hpar, hcut⟩

/-- **layer32d**: BASE12 and (II_D) on at most 12 vertices -/
theorem layer32d : BASE12 ∧ (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 6 ≤ vcount P → vcount P ≤ 12 → TwoCutReducedOn P →
    ∀ g, P g → (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) → (∀ S, TwoCut P S → ¬ Crosses P S g) →
    Colourable (leafSet P g) 6) :=
  ⟨base12, iid12⟩

end RH2F
