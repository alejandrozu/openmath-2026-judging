/-
  Families.lean — the infinite-family theorems in the vocabulary of the DMS chain.

  For each family: the graph is subcubic and loopless (so it is in the scope of `RH2F.DMS`), and every edge set
  `P` is star `k`-colourable (`MGraph.Colourable P k`) with k = 5 (and hence k = 6: the conclusion of `RH2F.DMS`
  for this graph).  `BlockStar.dms_iff : RH2F.DMS ↔ ∀ G, DMSfor G`.
-/
import BlockProps
import FlowerSnark
import GoldbergSnark
import GPetersen2
import GPFive

open BlockStar SeamSeq

/-- the statement proved for each graph `G` of a family: `G` is a subcubic loopless multigraph and every edge
    set of `G` has a star edge colouring with `k` colours and with 6 colours -/
def StarFamily (G : MGraph) (k : Nat) : Prop :=
  G.Subcubic ∧ G.Loopless ∧ (∀ P : Fin G.m → Prop, MGraph.Colourable P k) ∧
    (∀ P : Fin G.m → Prop, MGraph.Colourable P 6)

theorem starFamily_dms {G : MGraph} {k : Nat} (h : StarFamily G k) : DMSfor G := fun _ _ => h.2.2.2

namespace FlowerSnark

theorem tw_cases {n j : Nat} (hn : 2 ≤ n) (hj : j < n) :
    (tw n ((j + 0) % n) = 1 ∧ tw n ((j + 1) % n) = 0) ∨ (tw n ((j + 0) % n) = 0 ∧ tw n ((j + 1) % n) = 1) ∨
      (tw n ((j + 0) % n) = 0 ∧ tw n ((j + 1) % n) = 0) := by
  rw [modc hj (by omega), modc hj (by omega)]
  unfold tw
  split_ifs <;> omega

theorem flower_loopless (n : Nat) (hn : 2 ≤ n) : (flowerSnark n).Loopless := by
  apply BG_loopless
  · show 1 < n
    omega
  · intro w s hs hz
    have hz' : fjmp s = 0 := hz
    show fsrc s ≠ fdst w s
    have hs' : s < 6 := hs
    interval_cases s <;> first | exact absurd hz' (by decide) | simp [fsrc, fdst]

theorem flower_subcubic (n : Nat) (hn : 2 ≤ n) : (flowerSnark n).Subcubic := by
  apply BG_subcubic
  intro j hj
  have two : ∀ p, p ≤ flowerWir.D → p = 0 ∨ p = 1 := by
    intro p hp
    have hp' : p ≤ 1 := hp
    omega
  rcases tw_cases hn hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨fun p => [1, 0].getD p 0, ?_, by decide +kernel⟩
    intro p hp
    rcases two p hp with rfl | rfl
    · exact h0.symm
    · exact h1.symm
  · refine ⟨fun p => [0, 1].getD p 0, ?_, by decide +kernel⟩
    intro p hp
    rcases two p hp with rfl | rfl
    · exact h0.symm
    · exact h1.symm
  · refine ⟨fun p => [0, 0].getD p 0, ?_, by decide +kernel⟩
    intro p hp
    rcases two p hp with rfl | rfl
    · exact h0.symm
    · exact h1.symm

/-- **Flower snarks J_n, n odd, n ≥ 5** -/
theorem flower_family (n : Nat) (hodd : n % 2 = 1) (hn : 5 ≤ n) : StarFamily (flowerSnark n) 5 :=
  ⟨flower_subcubic n (by omega), flower_loopless n (by omega),
    colourable_of_star (flower_star n hodd hn) (Nat.le_refl 5),
    colourable_of_star (flower_star n hodd hn) (by decide)⟩

end FlowerSnark

namespace GoldbergSnark

theorem goldberg_loopless (k : Nat) (hk : 2 ≤ k) : (goldbergSnark k).Loopless := by
  apply BG_loopless
  · show 1 < k
    omega
  · intro w s hs hz
    have hz' : gjmp s = 0 := hz
    show gsrc s ≠ gdst s
    have hs' : s < 12 := hs
    interval_cases s <;> first | exact absurd hz' (by decide) | decide

theorem goldberg_subcubic (k : Nat) : (goldbergSnark k).Subcubic :=
  BG_subcubic _ _ _ (fun _ _ => ⟨fun _ => (), fun _ _ => rfl, by decide +kernel⟩)

/-- **Goldberg snarks G_k, k odd, k ≥ 5** -/
theorem goldberg_family (k : Nat) (hodd : k % 2 = 1) (hk : 5 ≤ k) : StarFamily (goldbergSnark k) 5 :=
  ⟨goldberg_subcubic k, goldberg_loopless k (by omega),
    colourable_of_star (goldberg_star k hodd hk) (Nat.le_refl 5),
    colourable_of_star (goldberg_star k hodd hk) (by decide)⟩

end GoldbergSnark

namespace GPetersen2

theorem gp2_loopless (k : Nat) (hk : 3 ≤ k) : (gp2 k).Loopless := by
  apply BG_loopless
  · show 2 < k
    omega
  · intro w s hs hz
    have hz' : pjmp s = 0 := hz
    show psrc s ≠ pdst s
    have hs' : s < 3 := hs
    interval_cases s <;> first | exact absurd hz' (by decide) | decide

theorem gp2_subcubic (k : Nat) : (gp2 k).Subcubic :=
  BG_subcubic _ _ _ (fun _ _ => ⟨fun _ => (), fun _ _ => rfl, by decide +kernel⟩)

/-- **GP(k,2), k ≥ 5**: star 6-edge-colouring whose colour class 5 (the sixth colour) is the set of spokes -/
theorem gp2_spoke_family (k : Nat) (hk : 5 ≤ k) :
    (gp2 k).Subcubic ∧ (gp2 k).Loopless ∧ (gp2 k).Star 6 (gpCol k) ∧
      (∀ e : Fin (gp2 k).m, (gpCol k e).val = 5 ↔ e.val % 3 = 1) :=
  ⟨gp2_subcubic k, gp2_loopless k (by omega), gp2_star k hk, gp2_spokes k⟩

end GPetersen2

namespace GP2Five
open GPetersen2

/-- **GP(n,2), n ≥ 5** -/
theorem gp2_family (n : Nat) (hn : 5 ≤ n) : StarFamily (gp2 n) 5 :=
  ⟨gp2_subcubic n, gp2_loopless n (by omega),
    colourable_of_star (star5 n hn) (Nat.le_refl 5), colourable_of_star (star5 n hn) (by decide)⟩

end GP2Five

namespace GP3Five
open GPetersen2

theorem gp3_loopless (n : Nat) (hn : 4 ≤ n) : (gp3 n).Loopless := by
  apply BG_loopless
  · show 3 < n
    omega
  · intro w s hs hz
    have hz' : qjmp s = 0 := hz
    show psrc s ≠ pdst s
    have hs' : s < 3 := hs
    interval_cases s <;> first | exact absurd hz' (by decide) | decide

theorem gp3_subcubic (n : Nat) : (gp3 n).Subcubic :=
  BG_subcubic _ _ _ (fun _ _ => ⟨fun _ => (), fun _ _ => rfl, by decide +kernel⟩)

/-- **GP(n,3), n ≥ 7** -/
theorem gp3_family (n : Nat) (hn : 7 ≤ n) : StarFamily (gp3 n) 5 :=
  ⟨gp3_subcubic n, gp3_loopless n (by omega),
    colourable_of_star (star5 n hn) (Nat.le_refl 5), colourable_of_star (star5 n hn) (by decide)⟩

end GP3Five

#check @FlowerSnark.flower_star
#check @GoldbergSnark.goldberg_star
#check @GPetersen2.gp2_star
#check @GPetersen2.gp2_spokes
#check @GP2Five.star5
#check @GP3Five.star5
#check @FlowerSnark.flower_family
#check @GoldbergSnark.goldberg_family
#check @GPetersen2.gp2_spoke_family
#check @GP2Five.gp2_family
#check @GP3Five.gp3_family
#print StarFamily
#print BlockStar.DMSfor
#check @BlockStar.dms_iff
#check @starFamily_dms
#print axioms FlowerSnark.flower_star
#print axioms GoldbergSnark.goldberg_star
#print axioms GPetersen2.gp2_star
#print axioms GPetersen2.gp2_spokes
#print axioms GP2Five.star5
#print axioms GP3Five.star5
#print axioms FlowerSnark.flower_family
#print axioms GoldbergSnark.goldberg_family
#print axioms GPetersen2.gp2_spoke_family
#print axioms GP2Five.gp2_family
#print axioms GP3Five.gp3_family
#check @BlockStar.star_of_windows
#check @BlockStar.BG_ends
#print axioms BlockStar.star_of_windows
#print axioms BlockStar.BG_ends
#print axioms BlockStar.dms_iff
