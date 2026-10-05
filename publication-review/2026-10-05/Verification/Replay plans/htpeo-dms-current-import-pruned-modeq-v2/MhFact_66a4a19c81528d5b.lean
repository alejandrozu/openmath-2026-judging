-- Lean proof of fact 66a4a19c81528d5b (RH2F.layer35); added by fact_submit, do not edit
import MhFact_38b6f78a47fdf12e
import MhFact_024845889158353d
import MhFact_4e4dfbfc10836500
import MhFact_7b9500b9ad8bca15
import MhFact_5343a2db598602a9
import MhFact_06139ad5904fa064
import MhFact_96b352680829f174
import MhFact_c1bad3abf5f2e5e8
import MhFact_144fd607d85ac5da
import MhFact_e68d717a207ff44f
import MhFact_b536c7d8a4f139e4
import MhFact_7217c8f0517c24a9
import MhFact_79ac08d5cf0788b9
import MhFact_55368cd7a0c74072
import MhFact_6882aa6fa76ff8ed
import MhFact_77a5aa23394eb0f0
import MhFact_6460e64b00785972
import MhFact_e63e13afc71071cb
import MhFact_b71709db7a82637a
import MhFact_5e8f7a0c3cb04161
import MhFact_1f8ebb817a59b41d
import MhFact_7c9b506b16bbaf73
set_option backward.isDefEq.respectTransparency false

-- ===== from L35.lean =====
namespace RH2F
open MGraph

/-- all hosts of 𝒮_4 -/
theorem gB4 : ∀ k, k < sRep4.length → ∀ rc ∈ dRCb4.getD k [], GoodH (digGrC 4 (by decide) (sRep4.getD k []) rc) := by
  intro k hk
  have hK : sRep4.length = 1 := sRep4_len
  rcases (by omega : k = 0) with rfl
  · exact gB4_0

/-- all hosts of 𝒮_6 -/
theorem gB6 : ∀ k, k < sRep6.length → ∀ rc ∈ dRCb6.getD k [], GoodH (digGrC 6 (by decide) (sRep6.getD k []) rc) := by
  intro k hk
  have hK : sRep6.length = 2 := sRep6_len
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact gB6_0
  · exact gB6_1

/-- all hosts of 𝒮_8 -/
theorem gB8 : ∀ k, k < sRep8.length → ∀ rc ∈ dRCb8.getD k [], GoodH (digGrC 8 (by decide) (sRep8.getD k []) rc) := by
  intro k hk
  have hK : sRep8.length = 4 := sRep8_len
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact gB8_0
  · exact gB8_1
  · exact gB8_2
  · exact gB8_3

/-- all hosts of 𝒮_10 -/
theorem gB10 : ∀ k, k < sRep10.length → ∀ rc ∈ dRCb10.getD k [], GoodH (digGrC 10 (by decide) (sRep10.getD k []) rc) := by
  intro k hk
  have hK : sRep10.length = 14 := sRep10_len
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gB10_0
  · exact gB10_1
  · exact gB10_2
  · exact gB10_3
  · exact gB10_4
  · exact gB10_5
  · exact gB10_6
  · exact gB10_7
  · exact gB10_8
  · exact gB10_9
  · exact gB10_10
  · exact gB10_11
  · exact gB10_12
  · exact gB10_13

/-- all hosts of 𝒮_12 -/
theorem gB12 : ∀ k, k < sRep12.length → ∀ rc ∈ dRCb12.getD k [], GoodH (digGrC 12 (by decide) (sRep12.getD k []) rc) := by
  intro k hk
  have hK : sRep12.length = 57 := sRep12_len
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gB12_0
  · exact gB12_1
  · exact gB12_2
  · exact gB12_3
  · exact gB12_4
  · exact gB12_5
  · exact gB12_6
  · exact gB12_7
  · exact gB12_8
  · exact gB12_9
  · exact gB12_10
  · exact gB12_11
  · exact gB12_12
  · exact gB12_13
  · exact gB12_14
  · exact gB12_15
  · exact gB12_16
  · exact gB12_17
  · exact gB12_18
  · exact gB12_19
  · exact gB12_20
  · exact gB12_21
  · exact gB12_22
  · exact gB12_23
  · exact gB12_24
  · exact gB12_25
  · exact gB12_26
  · exact gB12_27
  · exact gB12_28
  · exact gB12_29
  · exact gB12_30
  · exact gB12_31
  · exact gB12_32
  · exact gB12_33
  · exact gB12_34
  · exact gB12_35
  · exact gB12_36
  · exact gB12_37
  · exact gB12_38
  · exact gB12_39
  · exact gB12_40
  · exact gB12_41
  · exact gB12_42
  · exact gB12_43
  · exact gB12_44
  · exact gB12_45
  · exact gB12_46
  · exact gB12_47
  · exact gB12_48
  · exact gB12_49
  · exact gB12_50
  · exact gB12_51
  · exact gB12_52
  · exact gB12_53
  · exact gB12_54
  · exact gB12_55
  · exact gB12_56

/-- all hosts of 𝒮_14 at the code 0 -/
theorem gB14 : ∀ k, k < sRep14.length → GoodH (digGrC 14 (by decide) (sRep14.getD k []) 0) := by
  intro k hk
  have hK : sRep14.length = 341 := sRep14_len
  have hmem : (0 : Nat) ∈ (List.replicate 341 [0]).getD k [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (show k < 341 by omega)]
    simp
  by_cases h0 : k < 60
  · exact layer34_0 k (by omega) (by omega) 0 hmem
  by_cases h1 : k < 120
  · exact layer34_1 k (by omega) (by omega) 0 hmem
  by_cases h2 : k < 180
  · exact layer34_2 k (by omega) (by omega) 0 hmem
  by_cases h3 : k < 240
  · exact layer34_3 k (by omega) (by omega) 0 hmem
  by_cases h4 : k < 300
  · exact layer34_4 k (by omega) (by omega) 0 hmem
  exact layer34_5 k (by omega) (by omega) 0 hmem

/-- **the members of 𝒟 with 14 vertices** -/
theorem d14 : ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → vcount P = 14 →
    EX1On P ∧ ∀ g, Eligible P g → Colourable (leafSet P g) 6 :=
  d14_of gB4 gB6 gB8 gB10 gB12 gB14

/-- **SIMPLE14** (the Lean definition of fact 30194dab4e05fdcf) -/
theorem simple14 : SIMPLE14 := fun X P hS hv =>
  (d14 X P hS.1 (fun S hS2 => absurd hS2 (hS.2.2 S)) hv).1

/-- **B14D** (the Lean definition of fact 30194dab4e05fdcf) -/
theorem b14d : B14D := fun X P hG h2 hv _ => (d14 X P hG h2 hv).1

/-- **(II_D) on at most 14 vertices** -/
theorem iid14 : ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 6 ≤ vcount P → vcount P ≤ 14 → TwoCutReducedOn P →
    ∀ g, P g → (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) → (∀ S, TwoCut P S → ¬ Crosses P S g) →
    Colourable (leafSet P g) 6 := by
  intro X P hG h6 h14 h2 g hg hpar hcut
  by_cases h12 : vcount P ≤ 12
  · exact iid12 X P hG h6 h12 h2 g hg hpar hcut
  · have hev := vcount_even' hG
    exact (d14 X P hG h2 (by omega)).2 g ⟨hg, hpar, hcut⟩

/-- **layer35**: SIMPLE14, B14D and (II_D) on at most 14 vertices -/
theorem layer35 : SIMPLE14 ∧ B14D ∧ (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 6 ≤ vcount P → vcount P ≤ 14 → TwoCutReducedOn P →
    ∀ g, P g → (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) → (∀ S, TwoCut P S → ¬ Crosses P S g) →
    Colourable (leafSet P g) 6) :=
  ⟨simple14, b14d, iid14⟩

end RH2F
