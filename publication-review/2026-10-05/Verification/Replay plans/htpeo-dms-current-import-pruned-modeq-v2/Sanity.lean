/-
  Sanity.lean — prints the edge lists of J_5, J_7, G_5, GP(5,2), M_5 and of the inflation of the theta graph as defined here (pairs of vertex numbers, in the
  order of the edge numbers), for the independent comparison in sanity_check.py (not part of any proof).
-/
import FlowerSnark
import GoldbergSnark
import GPPeriodic
import Mobius
import InflationDefs

def edgeList (G : MGraph) : List (Nat × Nat) :=
  (List.finRange G.m).map fun e => ((G.ends e).1.val, (G.ends e).2.val)

#eval IO.println (toString (edgeList (FlowerSnark.flowerSnark 5)))
#eval IO.println (toString (edgeList (FlowerSnark.flowerSnark 7)))
#eval IO.println (toString (edgeList (GoldbergSnark.goldbergSnark 5)))
#eval IO.println (toString (edgeList (GPk.gp 5 2)))
#eval IO.println (toString ((List.finRange (FlowerSnark.flowerSnark 5).m).map fun e => (FlowerSnark.flowerCol 5 e).val))
#eval IO.println (toString ((List.finRange (GoldbergSnark.goldbergSnark 5).m).map fun e => (GoldbergSnark.goldbergCol 5 e).val))
#eval IO.println (toString (edgeList (Mobius.mobius 5)))

/-- the theta graph: two vertices joined by three parallel edges; edge `e` uses port `e` at both ends -/
def thetaH : MGraph := ⟨2, 3, fun _ => (⟨0, by decide⟩, ⟨1, by decide⟩)⟩

#eval IO.println (toString (edgeList (Inflation.inflate thetaH (fun e _ => e))))
