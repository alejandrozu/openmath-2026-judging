/-
  SeamStar.lean — window criterion for the block sequences of `SeamSeq`: if the six cyclic sequences of
  lengths 5, 9, 13 (seam Q) and 7, 11, 15 (seam T0 T1 T2) pass the window check, then for every odd n ≥ 5 the
  block-wise colouring of the cyclic block graph with n blocks is a star edge colouring.
-/
import BlockStar
import SeamSeq

namespace SeamStar
open BlockStar SeamSeq

variable {W : Type} {r q : Nat}

/-- all `n` cyclic windows of the sequence of length `n` pass the window check -/
abbrev winsAll (Wr : Wir W r q) (f : Nat → W) (ct : Nat → Nat → Nat) (χ : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∀ j, j < n → winOK Wr ct (fun p => f (tw n ((j + p) % n))) (fun p => χ n ((j + p) % n)) = true

theorem seam_star (Wr : Wir W r q) (hD : Wr.D = 1) (f : Nat → W) (ct : Nat → Nat → Nat) {k : Nat}
    (hct : ∀ c s, ct c s < k)
    (h5 : winsAll Wr f ct chi1 5) (h9 : winsAll Wr f ct chi1 9) (h13 : winsAll Wr f ct chi1 13)
    (h7 : winsAll Wr f ct chi3 7) (h11 : winsAll Wr f ct chi3 11) (h15 : winsAll Wr f ct chi3 15)
    (n : Nat) (hodd : n % 2 = 1) (hn : 5 ≤ n) :
    (BG Wr n (fun J => f (tw n J))).Star k (bcol q ct hct (chi n)) := by
  rcases (show n % 4 = 1 ∨ n % 4 = 3 by omega) with h4 | h4
  · have hχ : chi n = chi1 n := by funext J; simp [chi, h4]
    rw [hχ]
    apply star_of_windows
    intro j hj
    by_cases c13 : 13 ≤ n
    · obtain ⟨j', hj', hrep⟩ := rep1 h4 c13 hj
      refine ⟨fun p => f (tw 13 ((j' + p) % 13)), fun p => chi1 13 ((j' + p) % 13), ?_, h13 j' hj'⟩
      intro p hp
      rw [hD] at hp
      obtain ⟨e1, e2⟩ := hrep p (by omega)
      exact ⟨by show f (tw 13 ((j' + p) % 13)) = f (tw n ((j + p) % n)); rw [e1], e2⟩
    · rcases (show n = 5 ∨ n = 9 by omega) with rfl | rfl
      · exact ⟨_, _, fun p _ => ⟨rfl, rfl⟩, h5 j hj⟩
      · exact ⟨_, _, fun p _ => ⟨rfl, rfl⟩, h9 j hj⟩
  · have hχ : chi n = chi3 n := by funext J; simp [chi, h4]
    rw [hχ]
    apply star_of_windows
    intro j hj
    by_cases c15 : 15 ≤ n
    · obtain ⟨j', hj', hrep⟩ := rep3 h4 c15 hj
      refine ⟨fun p => f (tw 15 ((j' + p) % 15)), fun p => chi3 15 ((j' + p) % 15), ?_, h15 j' hj'⟩
      intro p hp
      rw [hD] at hp
      obtain ⟨e1, e2⟩ := hrep p (by omega)
      exact ⟨by show f (tw 15 ((j' + p) % 15)) = f (tw n ((j + p) % n)); rw [e1], e2⟩
    · rcases (show n = 7 ∨ n = 11 by omega) with rfl | rfl
      · exact ⟨_, _, fun p _ => ⟨rfl, rfl⟩, h7 j hj⟩
      · exact ⟨_, _, fun p _ => ⟨rfl, rfl⟩, h11 j hj⟩

end SeamStar
