/-
  Check.lean — the main statements once more with the graph argument written explicitly
  (`MGraph.Star` takes the graph as an implicit argument, which `#check` does not print).
-/
import Families

#check @MGraph.Star

example (n : Nat) (hodd : n % 2 = 1) (hn : 5 ≤ n) :
    @MGraph.Star (FlowerSnark.flowerSnark n) 5 (FlowerSnark.flowerCol n) := FlowerSnark.flower_star n hodd hn

example (k : Nat) (hodd : k % 2 = 1) (hk : 5 ≤ k) :
    @MGraph.Star (GoldbergSnark.goldbergSnark k) 5 (GoldbergSnark.goldbergCol k) :=
  GoldbergSnark.goldberg_star k hodd hk

example (k : Nat) (hk : 5 ≤ k) : @MGraph.Star (GPetersen2.gp2 k) 6 (GPetersen2.gpCol k) := GPetersen2.gp2_star k hk

example (n : Nat) (hn : 5 ≤ n) : @MGraph.Star (GPetersen2.gp2 n) 5 (GP2Five.col n) := GP2Five.star5 n hn

example (n : Nat) (hn : 7 ≤ n) : @MGraph.Star (GP3Five.gp3 n) 5 (GP3Five.col n) := GP3Five.star5 n hn

/-- unconditionally, for the flower snarks: the conclusion of `RH2F.DMS` -/
example (n : Nat) (hodd : n % 2 = 1) (hn : 5 ≤ n) :
    ∀ P : Fin (FlowerSnark.flowerSnark n).m → Prop, MGraph.Colourable P 6 :=
  (FlowerSnark.flower_family n hodd hn).2.2.2

set_option pp.explicit true in
#check @FlowerSnark.flower_star
