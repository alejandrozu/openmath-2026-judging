/-
  GPetersen2.lean — GP(k,2), k ≥ 5: the star 6-edge-colouring with the spokes as sixth colour class
  (definitions in GPetersen2Defs.lean, window checks for k < 45 in GPetersen2W1..3.lean).
-/
import GPetersen2W1
import GPetersen2W2
import GPetersen2W3

namespace GPetersen2
open BlockStar

theorem Wsmall : ∀ k, k < 45 → 5 ≤ k → winsAll k := by
  intro k h1 h2
  rcases (show k < 27 ∨ (27 ≤ k ∧ k < 37) ∨ 37 ≤ k by omega) with c | c | c
  · exact Wpart1 k c h2
  · exact Wpart2 k c.2 c.1
  · exact Wpart3 k h1 c

theorem rep {k : Nat} (hk : 45 ≤ k) {j : Nat} (hj : j < k) :
    ∃ j', j' < 20 + 6 * (k % 5) ∧ ∀ p, p ≤ 6 →
      gidx (20 + 6 * (k % 5)) ((j' + p) % (20 + 6 * (k % 5))) = gidx k ((j + p) % k) := by
  have hm : (20 + 6 * (k % 5)) % 5 = k % 5 := by omega
  rcases (show j < 5 ∨ (5 ≤ j ∧ j + 10 + 6 * (k % 5) < k) ∨ k ≤ j + 10 + 6 * (k % 5) by omega) with c | c | c
  · refine ⟨j, by omega, ?_⟩
    intro p hp
    rw [SeamSeq.modc hj (by omega), SeamSeq.modc (by omega) (by omega)]
    simp only [gidx, hm]
    split_ifs <;> omega
  · refine ⟨5 + j % 5, by omega, ?_⟩
    intro p hp
    rw [SeamSeq.modc hj (by omega), SeamSeq.modc (by omega) (by omega)]
    simp only [gidx, hm]
    split_ifs <;> omega
  · refine ⟨j + (20 + 6 * (k % 5)) - k, by omega, ?_⟩
    intro p hp
    rw [SeamSeq.modc hj (by omega), SeamSeq.modc (by omega) (by omega)]
    simp only [gidx, hm]
    split_ifs <;> omega

/-- **GP(k,2).** For every `k ≥ 5`, `gpCol k` is a star edge colouring of GP(k,2) with 6 colours. -/
theorem gp2_star (k : Nat) (hk : 5 ≤ k) : (gp2 k).Star 6 (gpCol k) := by
  apply star_of_windows
  intro j hj
  by_cases c : k < 45
  · exact ⟨_, _, fun p _ => ⟨rfl, rfl⟩, Wsmall k c hk j hj⟩
  · obtain ⟨j', hj', hrep⟩ := rep (by omega) hj
    have hk' : 20 + 6 * (k % 5) < 45 := by omega
    refine ⟨fun _ => (), fun p => pchi (20 + 6 * (k % 5)) ((j' + p) % (20 + 6 * (k % 5))), ?_,
      Wsmall _ hk' (by omega) j' hj'⟩
    intro p hp
    have hp' : p ≤ 6 := hp
    refine ⟨rfl, ?_⟩
    have e := hrep p hp'
    have h1 : ¬ (k < 20 ∧ k < 6 * (k % 5)) := by omega
    have h2 : ¬ (20 + 6 * (k % 5) < 20 ∧ 20 + 6 * (k % 5) < 6 * ((20 + 6 * (k % 5)) % 5)) := by omega
    show pchi (20 + 6 * (k % 5)) ((j' + p) % (20 + 6 * (k % 5))) = pchi k ((j + p) % k)
    unfold pchi
    rw [if_neg h1, if_neg h2, e]

/-- the sixth colour class (colour 5) is exactly the set of spokes (edge type 1, i.e. edge numbers 3i+1) -/
theorem gp2_spokes (k : Nat) (e : Fin (gp2 k).m) : (gpCol k e).val = 5 ↔ e.val % 3 = 1 := by
  show pct (pchi k (e.val / 3)) (e.val % 3) = 5 ↔ e.val % 3 = 1
  unfold pct
  split_ifs <;> omega

end GPetersen2

#print axioms GPetersen2.gp2_star
#print axioms GPetersen2.gp2_spokes
