/-
  All.lean — every main statement of pack4 (`#check`) with its axioms (`#print axioms`).
  The output of this file is build/All.out (copied to axioms.log).
-/
import Families
import Check
import GPPeriodic
import GPAll
import Mobius
import Inflation

#print MGraph
#print MGraph.Star
#print MGraph.StarOn
#print MGraph.Bicol
#print MGraph.Walk4
#print MGraph.Subcubic
#print MGraph.Loopless
#print MGraph.Colourable
#print RH2F.DMS
#print BlockStar.DMSfor
#print StarFamily
#print GPk.StarFam
#print BlockStar.Wir
#print BlockStar.BG
#print BlockStar.bcol
#print FlowerSnark.flowerSnark
#print GoldbergSnark.goldbergSnark
#print GPetersen2.gp2
#print GP3Five.gp3
#print GPk.gp
#print Mobius.mobius
#print Inflation.inflate
#print Inflation.PortsInj
#check @FlowerSnark.flower_star
#check @FlowerSnark.flower_family
#check @GoldbergSnark.goldberg_star
#check @GoldbergSnark.goldberg_family
#check @GPetersen2.gp2_star
#check @GPetersen2.gp2_spokes
#check @GPetersen2.gp2_spoke_family
#check @GP2Five.star5
#check @GP2Five.gp2_family
#check @GP3Five.star5
#check @GP3Five.gp3_family
#check @GPk.star4
#check @GPk.family4
#check @GPk.star6
#check @GPk.family6
#check @GPk.star8
#check @GPk.family8
#check @GPk.star10
#check @GPk.family10
#check @GPk.star12
#check @GPk.family12
#check @GPk.star14
#check @GPk.family14
#check @gp_star5
#check @gp_family
#check @Mobius.star5
#check @Mobius.mobius_family
#check @Inflation.inflate_star5
#check @BlockStar.star_of_windows
#check @BlockStar.BG_ends
#check @BlockStar.BG_loopless
#check @BlockStar.BG_subcubic
#check @BlockStar.colourable_of_star
#check @BlockStar.dms_iff
#check @starFamily_dms
#check @GPk.periodic_star
#print axioms FlowerSnark.flower_star
#print axioms FlowerSnark.flower_family
#print axioms GoldbergSnark.goldberg_star
#print axioms GoldbergSnark.goldberg_family
#print axioms GPetersen2.gp2_star
#print axioms GPetersen2.gp2_spokes
#print axioms GPetersen2.gp2_spoke_family
#print axioms GP2Five.star5
#print axioms GP2Five.gp2_family
#print axioms GP3Five.star5
#print axioms GP3Five.gp3_family
#print axioms GPk.star4
#print axioms GPk.family4
#print axioms GPk.star6
#print axioms GPk.family6
#print axioms GPk.star8
#print axioms GPk.family8
#print axioms GPk.star10
#print axioms GPk.family10
#print axioms GPk.star12
#print axioms GPk.family12
#print axioms GPk.star14
#print axioms GPk.family14
#print axioms gp_star5
#print axioms gp_family
#print axioms Mobius.star5
#print axioms Mobius.mobius_family
#print axioms Inflation.inflate_star5
#print axioms BlockStar.star_of_windows
#print axioms BlockStar.BG_ends
#print axioms BlockStar.BG_loopless
#print axioms BlockStar.BG_subcubic
#print axioms BlockStar.colourable_of_star
#print axioms BlockStar.dms_iff
#print axioms starFamily_dms
#print axioms GPk.periodic_star
