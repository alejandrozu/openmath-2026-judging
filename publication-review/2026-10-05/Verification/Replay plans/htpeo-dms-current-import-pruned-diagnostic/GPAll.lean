/-
  GPAll.lean — generalized Petersen graphs GP(n,k) for all 1 ≤ k ≤ 15 and all n ≥ 2k+1, except GP(3,1) (the prism,
  whose star chromatic index is 6): star edge colourings with 5 colours.  (Zhu–Shao conjecture: every GP(n,k)
  except GP(3,1) has star chromatic index at most 5; this is the case k ≤ 15.)
-/
import GPn1
import GPn2
import GPn3
import GPn4
import GPn5
import GPn6
import GPn7
import GPn8
import GPn9
import GPn10
import GPn11
import GPn12
import GPn13
import GPn14
import GPn15

open GPk

/-- **GP(n,k), 1 ≤ k ≤ 15, n ≥ 2k+1, (n,k) ≠ (3,1)**: a star edge colouring with 5 colours exists -/
theorem gp_star5 (k n : Nat) (hk : 1 ≤ k) (hK : k ≤ 15) (hn : 2 * k + 1 ≤ n) (hex : ¬ (n = 3 ∧ k = 1)) :
    ∃ c : Fin (gp n k).m → Fin 5, (gp n k).Star 5 c := by
  interval_cases k
  · exact ⟨_, GPn1.star5 n (by omega)⟩
  · exact ⟨_, GPn2.star5 n (by omega)⟩
  · exact ⟨_, GPn3.star5 n (by omega)⟩
  · exact ⟨_, GPn4.star5 n (by omega)⟩
  · exact ⟨_, GPn5.star5 n (by omega)⟩
  · exact ⟨_, GPn6.star5 n (by omega)⟩
  · exact ⟨_, GPn7.star5 n (by omega)⟩
  · exact ⟨_, GPn8.star5 n (by omega)⟩
  · exact ⟨_, GPn9.star5 n (by omega)⟩
  · exact ⟨_, GPn10.star5 n (by omega)⟩
  · exact ⟨_, GPn11.star5 n (by omega)⟩
  · exact ⟨_, GPn12.star5 n (by omega)⟩
  · exact ⟨_, GPn13.star5 n (by omega)⟩
  · exact ⟨_, GPn14.star5 n (by omega)⟩
  · exact ⟨_, GPn15.star5 n (by omega)⟩

/-- the same in the vocabulary of the DMS chain: subcubic, loopless, every edge set star 5- and 6-colourable -/
theorem gp_family (k n : Nat) (hk : 1 ≤ k) (hK : k ≤ 15) (hn : 2 * k + 1 ≤ n) (hex : ¬ (n = 3 ∧ k = 1)) :
    StarFam (gp n k) 5 := by
  interval_cases k
  · exact GPn1.family n (by omega)
  · exact GPn2.family n (by omega)
  · exact GPn3.family n (by omega)
  · exact GPn4.family n (by omega)
  · exact GPn5.family n (by omega)
  · exact GPn6.family n (by omega)
  · exact GPn7.family n (by omega)
  · exact GPn8.family n (by omega)
  · exact GPn9.family n (by omega)
  · exact GPn10.family n (by omega)
  · exact GPn11.family n (by omega)
  · exact GPn12.family n (by omega)
  · exact GPn13.family n (by omega)
  · exact GPn14.family n (by omega)
  · exact GPn15.family n (by omega)
