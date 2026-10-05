/-
  Star6Corollaries.lean — unconditional corollaries of the star6 chain, stated in the vocabulary of the
  statement `RH2F.DMS` (Lean 4.33.1 + Mathlib v4.33.1; imports the pack3 library, which is not modified).

  Vocabulary (all from the library):
    `MGraph`            finite multigraph: `n` vertices `Fin n`, `m` edges `Fin m`, `ends : Fin m → Fin n × Fin n`
    `Loopless G`        no edge has equal ends
    `Subcubic G`        no vertex has 4 distinct incident edges
    `P : Fin G.m → Prop` an edge set (sub-multigraph); `fun _ => True` is the whole multigraph
    `ConnectedOn P`, `BridgelessOn P`, `CubicOn P`   the sub-multigraph `P` is connected / has no bridge / is 3-regular
    `InG X P`           := `Loopless X ∧ ConnectedOn P ∧ BridgelessOn P ∧ CubicOn P`
    `vcount P`          number of vertices met by `P`
    `StarOn P k c`      `c` is a star edge colouring of `P` with colours `Fin k` (proper, no bicoloured 4-edge path or 4-cycle)
    `Colourable P k`    := `∃ c, StarOn P k c`
    `PMOn P N`          `N` is a perfect matching of `P`;  `ClassOn P N c`: `N` is a colour class of `c`
    `leafSet P g`       the leaf graph T(P, g): delete the edge `g = st`, add a vertex `x` joined to `s` and `t`
                        and a pendant edge `xℓ`
    `TwoCutReducedOn P` every 2-edge-cut of `P` has a side with exactly two vertices
    `RH2F.DMS`          := `∀ G, Subcubic G → Loopless G → ∀ P : Fin G.m → Prop, Colourable P 6`
                        (the Dvořák–Mohar–Šámal conjecture for loopless multigraphs; NOT proved)

  Sections:  A. small-order theorems (new);  B. structure of a counterexample (new);
             C. reductions that are already in the library (re-exported);  D. known theorems (re-exported).
-/
import Star6Bounded
import MhFact_ba4d9c5abd0afd83
import MhFact_6c78409a046a3fe7
set_option backward.isDefEq.respectTransparency false

namespace Star6
open MGraph RH2F

/-! ## A. Small-order theorems -/

/-- (H) for at most 14 vertices (from the finite theorems `d1012`, `d14` behind BASE12, SIMPLE14, B14D) -/
theorem hypLE14 : HypLE 14 := by
  intro X P hG h10 h14 h2
  by_cases h12 : vcount P ≤ 12
  · exact (d1012 X P hG h2 h10 h12).1
  · have hev := vcount_even' hG
    exact (d14 X P hG h2 (by omega)).1

/-- (II_D) for at most 14 vertices (`iid14`) -/
theorem iidLE14 : IIDLE 14 := fun X P hG h6 h14 h2 g hg hpar hcut => iid14 X P hG h6 h14 h2 g hg hpar hcut

/-- **Theorem A1.** Every bridgeless cubic sub-multigraph `P` (connected or not) of a loopless multigraph with at
    most 14 vertices has a star edge colouring with 6 colours. -/
theorem star6_cubic_bridgeless_le14 (X : MGraph) (P : Fin X.m → Prop) (hL : Loopless X) (hB : BridgelessOn P)
    (hK : CubicOn P) (h14 : vcount P ≤ 14) : Colourable P 6 :=
  dmsI_all_le 14 hypLE14 X P hL hB hK h14

/-- **Theorem A1, whole-graph form.** Every bridgeless cubic loopless multigraph on at most 14 vertices is star
    6-edge-colourable. -/
theorem star6_cubic_bridgeless_graph_le14 (G : MGraph) (hL : Loopless G)
    (hB : BridgelessOn (fun _ : Fin G.m => True)) (hK : CubicOn (fun _ : Fin G.m => True)) (h14 : G.n ≤ 14) :
    Colourable (fun _ : Fin G.m => True) 6 :=
  star6_cubic_bridgeless_le14 G _ hL hB hK (Nat.le_trans (vcount_le_n _) h14)

/-- **Theorem A2 (perfect matchings as colour classes).** In a connected bridgeless cubic loopless multigraph with
    between 10 and 14 vertices, every edge `g` lies in a perfect matching that is a colour class of some star
    6-edge-colouring, and `g` is avoided by a perfect matching that is a colour class of some star 6-edge-colouring.
    (This is the property "EX1-good" of the chain with Schönberger's theorem inserted; it fails for some graphs on
    at most 8 vertices.) -/
theorem matching_colour_class_10_14 (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) (h10 : 10 ≤ vcount P)
    (h14 : vcount P ≤ 14) (g : Fin X.m) (hg : P g) :
    (∃ N c, PMOn P N ∧ N g ∧ StarOn P 6 c ∧ ClassOn P N c) ∧
    (∃ N c, PMOn P N ∧ ¬ N g ∧ StarOn P 6 c ∧ ClassOn P N c) := by
  have hex := ex1red_le 14 RH2P.pstat smallFacts hypLE14 X P hG h10 h14
  constructor
  · obtain ⟨N, hN, hNg, c, hc, hcl⟩ := hex g hg true (RH2P.pstat X P hG g hg true)
    exact ⟨N, c, hN, hNg.2 rfl, hc, hcl⟩
  · obtain ⟨N, hN, hNg, c, hc, hcl⟩ := hex g hg false (RH2P.pstat X P hG g hg false)
    exact ⟨N, c, hN, fun h => absurd (hNg.1 h) (by decide), hc, hcl⟩

/-- the leaf case for hosts with at most 14 vertices -/
theorem iicLE14 : IIcLE 14 := iic_le 14 hypLE14 iidLE14

/-- **Theorem A3 (leaf graphs).** For every connected bridgeless cubic loopless multigraph `P` with at most 14
    vertices and every edge `g` of `P`, the leaf graph T(P, g) (a subcubic graph on at most 16 vertices whose only
    vertex of degree less than 3 is the leaf `ℓ`; it contains `P` with `g` subdivided) has a star edge colouring with
    6 colours. -/
theorem star6_leaf_le14 (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) (h14 : vcount P ≤ 14) (g : Fin X.m)
    (hg : P g) : Colourable (leafSet P g) 6 :=
  iicLE14 X P hG h14 g hg

/-- connected bridgeless cubic on at most 14 vertices -/
theorem cubicLE14 : CubicLE 14 := fun X P hG h14 => star6_cubic_bridgeless_le14 X P hG.1 hG.2.2.1 hG.2.2.2 h14

/-- **Theorem A4 (all subcubic multigraphs of small order).** Every loopless multigraph of maximum degree at most 3
    on at most 7 vertices, and every sub-multigraph of it, has a star edge colouring with 6 colours.
    (7 = 14 / 2: the library's reduction of a graph with two vertices of degree < 3 doubles the graph.) -/
theorem star6_subcubic_le7 (G : MGraph) (hsub : Subcubic G) (hloop : Loopless G) (h7 : G.n ≤ 7)
    (P : Fin G.m → Prop) : Colourable P 6 :=
  dms_le 14 cubicLE14 iicLE14 G hsub hloop (by omega) P

/-- **Theorem A5 (the bounded reduction, for every `N`).** If (H) and (II_D) hold for graphs with at most `N`
    vertices, then (1) every bridgeless cubic loopless multigraph with at most `N` vertices is star
    6-edge-colourable, (2) every connected one with between 10 and `N` vertices is EX1-good, (3) all leaf graphs of
    connected ones with at most `N` vertices are star 6-edge-colourable, and (4) every subcubic loopless multigraph
    with at most `N / 2` vertices is star 6-edge-colourable.  No hypothesis about larger graphs is used. -/
theorem bounded_reduction (N : Nat) (hH : HypLE N) (hD : IIDLE N) :
    (∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → BridgelessOn P → CubicOn P → vcount P ≤ N → Colourable P 6) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → vcount P ≤ N → EX1On P) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P ≤ N → ∀ g, P g → Colourable (leafSet P g) 6) ∧
    (∀ (G : MGraph), Subcubic G → Loopless G → 2 * G.n ≤ N → ∀ P : Fin G.m → Prop, Colourable P 6) :=
  ⟨dmsI_all_le N hH, ex1red_le N RH2P.pstat smallFacts hH, iic_le N hH hD,
   dms_le N (fun X P hG h => dmsI_all_le N hH X P hG.1 hG.2.2.1 hG.2.2.2 h) (iic_le N hH hD)⟩

/-! ## B. Structure of a counterexample -/

/-- (H) restricted to at least 16 vertices -/
def Hyp16 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 16 ≤ vcount P → TwoCutReducedOn P → EX1On P

/-- (H) from its part on at least 16 vertices -/
theorem hyp_of_hyp16 (h : Hyp16) : Hyp := by
  intro X P hG h10 h2
  by_cases h14 : vcount P ≤ 14
  · exact hypLE14 X P hG h10 h14 h2
  · have hev := vcount_even' hG
    exact h X P hG (by omega) h2

/-- **Theorem B1 (reduction of DMS to 2-cut-reduced cubic graphs on at least 16 vertices).** DMS holds if
    (a) every 2-cut-reduced connected bridgeless cubic loopless multigraph on at least 16 vertices is EX1-good, and
    (b) for every such multigraph `P` and every edge `g` of `P` that lies in no digon and in no 2-edge-cut, the leaf
        graph T(P, g) is star 6-edge-colourable (`IID16`). -/
theorem dms_of_hyp16_iid16 (hH : Hyp16) (hD : IID16) : DMS :=
  dms_of_H_IID (hyp_of_hyp16 hH) (iid_of_iid16 hD)

/-- **Theorem B2 (shape of a counterexample to DMS, strong form).** If DMS fails, then there is a 2-cut-reduced
    connected bridgeless cubic loopless multigraph `P` on at least 16 vertices such that either `P` is not EX1-good,
    or some leaf graph T(P, g), `g` an edge in no digon and in no 2-edge-cut, is not star 6-edge-colourable. -/
theorem counterexample_reduced16 (h : ¬ DMS) :
    (∃ (X : MGraph) (P : Fin X.m → Prop), InG X P ∧ 16 ≤ vcount P ∧ TwoCutReducedOn P ∧ ¬ EX1On P) ∨
    (∃ (X : MGraph) (P : Fin X.m → Prop) (g : Fin X.m), InG X P ∧ 16 ≤ vcount P ∧ TwoCutReducedOn P ∧
      Eligible P g ∧ ¬ Colourable (leafSet P g) 6) := by
  apply Classical.byContradiction
  intro hno
  apply h
  apply dms_of_hyp16_iid16
  · intro X P hG h16 h2
    apply Classical.byContradiction
    intro hE
    exact hno (Or.inl ⟨X, P, hG, h16, h2, hE⟩)
  · intro X P hG h16 h2 g hg hpar hcut
    apply Classical.byContradiction
    intro hc
    exact hno (Or.inr ⟨X, P, g, hG, h16, h2, ⟨hg, hpar, hcut⟩, hc⟩)

/-- **Theorem B3 (shape of a counterexample to DMS, colouring form).** If DMS fails, then there is a connected
    bridgeless cubic loopless multigraph `P` on at least 16 vertices such that either `P` itself or one of its leaf
    graphs T(P, g) is not star 6-edge-colourable. -/
theorem counterexample_cubic16 (h : ¬ DMS) :
    (∃ (X : MGraph) (P : Fin X.m → Prop), InG X P ∧ 16 ≤ vcount P ∧ ¬ Colourable P 6) ∨
    (∃ (X : MGraph) (P : Fin X.m → Prop) (g : Fin X.m), InG X P ∧ 16 ≤ vcount P ∧ P g ∧
      ¬ Colourable (leafSet P g) 6) := by
  apply Classical.byContradiction
  intro hno
  apply h
  refine DmsIILean.dms_of_I_II ?_ (iiToDMSII_c ?_)
  · intro X P hL hC hB hK _
    have hG : InG X P := ⟨hL, hC, hB, hK⟩
    by_cases h14 : vcount P ≤ 14
    · exact cubicLE14 X P hG h14
    · have hev := vcount_even' hG
      apply Classical.byContradiction
      intro hc
      exact hno (Or.inl ⟨X, P, hG, by omega, hc⟩)
  · intro X P hG g hg
    by_cases h14 : vcount P ≤ 14
    · exact iicLE14 X P hG h14 g hg
    · have hev := vcount_even' hG
      apply Classical.byContradiction
      intro hc
      exact hno (Or.inr ⟨X, P, g, hG, by omega, hg, hc⟩)

/-- **Theorem B4 (a smallest graph that is not EX1-good).** Let `P` be a connected bridgeless cubic loopless
    multigraph on at least 10 vertices that is not EX1-good, such that all such multigraphs with fewer vertices (and
    at least 10) are EX1-good.  Then `P` is 2-cut-reduced (every 2-edge-cut cuts off a digon) and has at least 16
    vertices. -/
theorem smallest_not_ex1 (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) (h10 : 10 ≤ vcount P)
    (hbad : ¬ EX1On P)
    (hmin : ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InG Y Q → 10 ≤ vcount Q → vcount Q < vcount P → EX1On Q) :
    TwoCutReducedOn P ∧ 16 ≤ vcount P := by
  constructor
  · apply Classical.byContradiction
    intro hred
    exact hbad (ex1red_step RH2P.pstat smallFacts hG _ rfl h10 hmin hred)
  · apply Classical.byContradiction
    intro h16
    have hev := vcount_even' hG
    exact hbad (ex1red_le 14 RH2P.pstat smallFacts hypLE14 X P hG h10 (by omega))

/-- **Theorem B5 (an edge-minimal counterexample).** Let `Q` be an edge-minimal non-star-6-colourable edge set of a
    subcubic loopless multigraph `G` (`Q` is not colourable, every proper subset is).  Then `Q` is connected, `G` has
    at least 8 vertices, and if `Q` is cubic, then `Q` is bridgeless and has at least 16 vertices. -/
theorem minimal_counterexample (G : MGraph) (hsub : Subcubic G) (hloop : Loopless G) (Q : Fin G.m → Prop)
    (hmin : MinimalCounterexample Q 6) :
    ConnectedOn Q ∧ 8 ≤ G.n ∧ (CubicOn Q → BridgelessOn Q ∧ 16 ≤ vcount Q) := by
  refine ⟨minimal_connected hmin, ?_, ?_⟩
  · apply Classical.byContradiction
    intro h8
    exact minimal_impossible_le 14 cubicLE14 iicLE14 hsub hloop (by omega) hmin
  · intro hK
    have hB : BridgelessOn Q := by
      intro f hf B
      by_cases hfc : Core Q f
      · exact core_no_cut hsub Q hmin hfc B
      · obtain ⟨x, hfx, hx1⟩ := deg1_of_pendant (Classical.byContradiction fun hp => hfc ⟨hf, hp⟩)
        exact qdeg1_not3 hx1 (hK x ⟨f, hf, hfx⟩)
    have hG : InG G Q := ⟨hloop, minimal_connected hmin, hB, hK⟩
    have hev := vcount_even' hG
    refine ⟨hB, ?_⟩
    apply Classical.byContradiction
    intro h16
    exact hmin.1 (cubicLE14 G Q hG (by omega))

/-! ## C. Reductions already in the library (re-exported under readable names; no new proof) -/

/-- **(H) ∧ (II) ⇒ DMS** (Theorem RH2, all auxiliary hypotheses discharged): if every 2-cut-reduced connected
    bridgeless cubic loopless multigraph on at least 10 vertices is EX1-good and every leaf graph of a bridgeless
    cubic loopless multigraph is star 6-edge-colourable, then DMS holds. -/
theorem dms_of_H_II : Hyp → II → DMS := rh2_final

/-- **(H) ∧ (II_D) ⇒ DMS** (II-RED2): the leaf hypothesis is only needed for 2-cut-reduced hosts on at least 6
    vertices and edges in no digon and no 2-edge-cut. -/
theorem dms_of_H_IID' : Hyp → IID → DMS := dms_of_H_IID

/-- **(I) ∧ (II) ⇒ DMS** (minimal-counterexample reduction): DMS follows from star 6-colourability of the connected
    bridgeless cubic loopless multigraphs other than K₃,₃ and of the suppression configurations. -/
theorem dms_of_I_II' : DmsIILean.DMS_I → DmsIILean.DMS_II → DMS := DmsIILean.dms_of_I_II

/-- **EX1-RED**: under (H), every connected bridgeless cubic loopless multigraph on at least 10 vertices is
    EX1-good (reduction along 2-edge-cuts). -/
theorem ex1_of_H : Hyp → ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 10 ≤ vcount P → EX1On P :=
  ex1red RH2P.pstat smallFacts

/-- **HOLE ⇒ DMS** (the first reduction of the project) -/
theorem dms_of_HOLE : HOLE → DMS := dms_of_hole

/-- **statement fidelity**: the `MGraph` statement `DMS` is equivalent to the statement `DMSP` written with
    `Fintype` vertex and edge types and `Sym2`-valued incidence (`∀ V E en, LooplessP en → MaxDeg3 en → Star6P en`) -/
theorem dms_iff_plain : DMS ↔ RH2Fid.DMSP := RH2Fid.fidelity_bundle.1.2.2

/-- the top theorem of the chain, re-exported -/
theorem chain_top :
    BASE12 ∧ SIMPLE14 ∧ B14D ∧ FEEXIST16 ∧ (IID16 → IID) ∧ (FEEXISTD18 → FEEXISTD10) ∧
    (FEEXTTNE16 → FEEXIST0NE16 → IID16) ∧
    (FEEXTD10 → FEEXISTD18 → POLE → TDTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD18 → WEXT → TDLTRI → IID16 → DMS) ∧
    (FEEXTD10 → FEEXISTD18 → POLE → TDTRI → FEEXTTNE16 → FEEXIST0NE16 → DMS) := layer37

/-! ## D. Known theorems formalised in the library (re-exported) -/

/-- **Schönberger's theorem (1934)** for multigraphs: in a connected bridgeless cubic loopless multigraph every edge
    lies in a perfect matching.  (Library: `RH2P.schoenberger`, proved from Mathlib's Tutte theorem.) -/
theorem schoenberger_in (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) (g : Fin X.m) (hg : P g) :
    ∃ N, PMOn P N ∧ N g := RH2P.schoenberger hG hg

/-- every edge of a connected bridgeless cubic loopless multigraph is avoided by some perfect matching
    (Plesník-type statement for one edge; library: `RH2P.pstat`) -/
theorem schoenberger_out (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) (g : Fin X.m) (hg : P g) :
    ∃ N, PMOn P N ∧ ¬ N g := by
  obtain ⟨N, hN, hNg⟩ := RH2P.pstat X P hG g hg false
  exact ⟨N, hN, fun h => absurd (hNg.1 h) (by decide)⟩

/-- **Petersen's theorem (1891)** for multigraphs: every connected bridgeless cubic loopless multigraph has a perfect
    matching. -/
theorem petersen (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) : ∃ N, PMOn P N := by
  by_cases hne : ∃ g, P g
  · obtain ⟨g, hg⟩ := hne
    obtain ⟨N, hN, _⟩ := RH2P.schoenberger hG hg
    exact ⟨N, hN⟩
  · exact ⟨fun _ => False, fun _ hf => hf.elim, fun x ⟨f, hf, _⟩ => absurd ⟨f, hf⟩ hne⟩

/-- a connected bridgeless cubic loopless multigraph has an even number of vertices -/
theorem cubic_even (X : MGraph) (P : Fin X.m → Prop) (hG : InG X P) : vcount P % 2 = 0 := vcount_even' hG

/-! ## E. The small-order theorems for multigraphs given by `Fintype` vertex and edge types and a `Sym2`-valued
  incidence map `en : E → Sym2 V` (the "plain" vocabulary of the fidelity module `RH2Fid`):
  `LooplessP en`, `MaxDeg3 en`, `CubicP en` (degree = number of incident edges), `ConnectedP en`,
  `BridgelessP en` (deleting an edge does not increase the number of components), `IsPM en N`,
  `StarP en c` (proper, no bicoloured path or cycle with 4 edges), `Star6P en` (a star colouring with colours 1..6),
  `EX1GoodP en`, `enT en g s t` (the leaf graph). -/

section plain
open RH2Fid

/-- **Theorem E1 (= A1, plain form).** Every bridgeless cubic loopless multigraph on at most 14 vertices is star
    6-edge-colourable. -/
theorem plain_star6_cubic_bridgeless_le14 (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V)
    (hl : LooplessP en) (hb : BridgelessP en) (hc : CubicP en) (hn : Fintype.card V ≤ 14) : Star6P en := by
  let R := encRep en (ori en) (ori_spec en)
  have hV := cubic_hV en hc
  have hcol := star6_cubic_bridgeless_le14 (encG (ori en)) (fun _ => True)
    (enc_loopless en (ori en) (ori_spec en) hl) (R.bridgeless_iff.2 hb) (R.cubicOn_of hc)
    (by rw [R.vcount_eq hV]; exact hn)
  exact (star6P_iff en).2 ((R.colourable_iff (by decide)).1 hcol)

/-- **Theorem E2 (= A4, plain form).** Every loopless multigraph of maximum degree at most 3 on at most 7 vertices is
    star 6-edge-colourable. -/
theorem plain_star6_subcubic_le7 (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V)
    (hl : LooplessP en) (hdeg : MaxDeg3 en) (hn : Fintype.card V ≤ 7) : Star6P en := by
  let R := encRep en (ori en) (ori_spec en)
  have hc := star6_subcubic_le7 (encG (ori en)) (R.subcubic_of (fun _ => trivial) hdeg)
    (enc_loopless en (ori en) (ori_spec en) hl) (by show Fintype.card V ≤ 7; exact hn) (fun _ => True)
  exact (star6P_iff en).2 ((R.colourable_iff (by decide)).1 hc)

/-- **Theorem E3 (= A2, plain form).** Every connected bridgeless cubic loopless multigraph with between 10 and 14
    vertices is EX1-good: for every edge `g` and `t ∈ {0, 1}`, some perfect matching `N` with `[g ∈ N] = t` is a
    colour class of a star 6-edge-colouring. -/
theorem plain_ex1_10_14 (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V)
    (hl : LooplessP en) (hconn : ConnectedP en) (hb : BridgelessP en) (hc : CubicP en)
    (h10 : 10 ≤ Fintype.card V) (h14 : Fintype.card V ≤ 14) : EX1GoodP en := by
  let R := encRep en (ori en) (ori_spec en)
  have hV := cubic_hV en hc
  have hin : RH2F.InG (encG (ori en)) (fun _ => True) :=
    ⟨enc_loopless en _ (ori_spec en) hl, R.connectedOn_of hconn, R.bridgeless_iff.2 hb, R.cubicOn_of hc⟩
  have hex := ex1red_le 14 RH2P.pstat smallFacts hypLE14 (encG (ori en)) (fun _ => True) hin
    (by rw [R.vcount_eq hV]; exact h10) (by rw [R.vcount_eq hV]; exact h14)
  -- from here: the proof of `RH2Fid.hyp_iff` (direction →), verbatim
  intro g t ht ⟨N', hpm', hind'⟩
  have hN : ∀ f, R.liftN N' f → True := fun _ _ => trivial
  have hfun : (fun e => R.liftN N' (R.ψ e)) = N' := funext fun e => propext (R.liftN_ψ N' e)
  have hpm : RH2F.PMOn (fun _ => True) (R.liftN N') := by
    rw [R.pmOn_iff hV _ hN, hfun]; exact hpm'
  have hst : R.liftN N' (R.ψ g) ↔ decide (t = 1) = true := by
    rw [R.liftN_ψ]; exact (ind_iff N' g t ht).1 hind'
  obtain ⟨N2, hpm2, hst2, c, hc2, hcl⟩ := hex (R.ψ g) trivial (decide (t = 1)) ⟨_, hpm, hst⟩
  refine ⟨fun e => N2 (R.ψ e), (R.pmOn_iff hV N2 (fun _ _ => trivial)).1 hpm2,
    (ind_iff _ g t ht).2 hst2, toN (fun e => c (R.ψ e)), toN_range _, ?_, (R.classOn_iff N2 c).1 hcl⟩
  exact (starP_congr en _ _ (fun e f => by simp only [toN, Fin.ext_iff]; omega)).1
    ((R.starOn_iff c).1 hc2)

/-- **Theorem E4 (= A3, plain form).** For every connected bridgeless cubic loopless multigraph on at most 14
    vertices and every edge `g = st`, the leaf graph T(G, g) is star 6-edge-colourable. -/
theorem plain_star6_leaf_le14 (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V)
    (hl : LooplessP en) (hconn : ConnectedP en) (hb : BridgelessP en) (hc : CubicP en)
    (hn : Fintype.card V ≤ 14) (g : E) (s t : V) (hst : en g = s(s, t)) : Star6P (enT en g s t) := by
  let o := oriG en g s t
  have ho := oriG_spec en g s t hst
  let R := encRep en o ho
  have hV := cubic_hV en hc
  have hg : (encG o).ends (R.ψ g) = (R.φ s, R.φ t) := by
    show (encG o).ends (Fintype.equivFin E g) = _
    rw [encG_ends]
    simp only [o, oriG, if_pos rfl]
    rfl
  have hin : RH2F.InG (encG o) (fun _ => True) :=
    ⟨enc_loopless en o ho hl, R.connectedOn_of hconn, R.bridgeless_iff.2 hb, R.cubicOn_of hc⟩
  have hcol := star6_leaf_le14 (encG o) (fun _ => True) hin (by rw [R.vcount_eq hV]; exact hn) (R.ψ g) trivial
  exact (star6P_iff _).2 (((leafRep R g s t hg).colourable_iff (by decide)).1 hcol)

/-- **Theorem E5 (Schönberger's theorem, plain form).** In a connected bridgeless cubic loopless multigraph every
    edge lies in some perfect matching and is avoided by some perfect matching. -/
theorem plain_schoenberger (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V)
    (hl : LooplessP en) (hconn : ConnectedP en) (hb : BridgelessP en) (hc : CubicP en) (g : E) :
    (∃ N, IsPM en N ∧ N g) ∧ (∃ N, IsPM en N ∧ ¬ N g) := by
  let R := encRep en (ori en) (ori_spec en)
  have hV := cubic_hV en hc
  have hin : RH2F.InG (encG (ori en)) (fun _ => True) :=
    ⟨enc_loopless en _ (ori_spec en) hl, R.connectedOn_of hconn, R.bridgeless_iff.2 hb, R.cubicOn_of hc⟩
  constructor
  · obtain ⟨N, hN, hNg⟩ := schoenberger_in _ _ hin (R.ψ g) trivial
    exact ⟨fun e => N (R.ψ e), (R.pmOn_iff hV N (fun _ _ => trivial)).1 hN, hNg⟩
  · obtain ⟨N, hN, hNg⟩ := schoenberger_out _ _ hin (R.ψ g) trivial
    exact ⟨fun e => N (R.ψ e), (R.pmOn_iff hV N (fun _ _ => trivial)).1 hN, hNg⟩

end plain

end Star6

#print axioms Star6.plain_star6_cubic_bridgeless_le14
#print axioms Star6.plain_star6_subcubic_le7
#print axioms Star6.plain_ex1_10_14
#print axioms Star6.plain_star6_leaf_le14
#print axioms Star6.plain_schoenberger
#print axioms Star6.star6_cubic_bridgeless_le14
#print axioms Star6.star6_cubic_bridgeless_graph_le14
#print axioms Star6.matching_colour_class_10_14
#print axioms Star6.star6_leaf_le14
#print axioms Star6.star6_subcubic_le7
#print axioms Star6.bounded_reduction
#print axioms Star6.dms_of_hyp16_iid16
#print axioms Star6.counterexample_reduced16
#print axioms Star6.counterexample_cubic16
#print axioms Star6.smallest_not_ex1
#print axioms Star6.minimal_counterexample
#print axioms Star6.dms_of_H_II
#print axioms Star6.dms_of_H_IID'
#print axioms Star6.dms_of_I_II'
#print axioms Star6.ex1_of_H
#print axioms Star6.dms_of_HOLE
#print axioms Star6.dms_iff_plain
#print axioms Star6.chain_top
#print axioms Star6.schoenberger_in
#print axioms Star6.schoenberger_out
#print axioms Star6.petersen
#print axioms Star6.cubic_even
#print axioms RH2F.ex1red_step
#print axioms RH2F.ex1red_le
#print axioms RH2F.iic_le
#print axioms RH2F.dmsI_all_le
#print axioms RH2F.dms_le
