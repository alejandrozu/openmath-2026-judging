-- Lean proof of fact f7fb58786d241d68 (RH2F.layer19); added by fact_submit, do not edit
import MhFact_345a55d7429fd4b1
set_option backward.isDefEq.respectTransparency false

/-
  NE1.lean — the no-enclosed-exchange (NE) closing set of the root in Lean: Theorem H-ENG-NE (fact b771fa70cbc11e0b)
  and Theorem ROOT-CS3 (fact 2d98b2523e97e6a0). Condition (d) (no enclosed exchange), the four far-exchange engine
  statements on all members of 𝒟 with at least 16 vertices, and the finite facts BASE12 (a20d73d94641ebb9), SIMPLE14
  (8f3cb2fcdd7e4727), B14-D (aa531b4ce552c207), LMC8 (9e8d394528f010f9) and LMC14 (18134123ad3fcd9c) as named
  hypotheses (their proofs rest on exhaustive enumerations up to isomorphism, done outside Lean).
-/

namespace RH2F
open MGraph
open Classical

section ne
variable {X : MGraph}

/-! ### simple members of 𝒟 have no 2-edge-cut -/

/-- a 2-edge-cut side with exactly two vertices `a1`, `a2` carries two parallel edges `a1 a2` -/
theorem Cut2.side_two_par {P : Fin X.m → Prop} (hG : InG X P) (C : Cut2 P) (h2 : scount P C.S true = 2) :
    ∃ f f', f ≠ f' ∧ P f ∧ P f' ∧ X.Joins f C.a1 C.a2 ∧ X.Joins f' C.a1 C.a2 := by
  -- the side consists of `a1` and `a2`
  have only : ∀ w, meets P w → C.S w = true → w = C.a1 ∨ w = C.a2 := by
    intro w hw hSw
    refine Classical.byContradiction fun hne => ?_
    push_neg at hne
    have h3 := cntF_triple X.n C.ha (Ne.symm hne.1) (Ne.symm hne.2)
    have hle : cntF X.n (fun k => k = C.a1 ∨ k = C.a2 ∨ k = w) ≤ scount P C.S true := by
      apply cntF_mono
      rintro k (rfl | rfl | rfl)
      · exact ⟨⟨C.e1, C.P1, joins_inc_left C.j1⟩, C.sa1⟩
      · exact ⟨⟨C.e2, C.P2, joins_inc_left C.j2⟩, C.sa2⟩
      · exact ⟨hw, hSw⟩
    omega
  -- every edge at `a1` other than `e1` joins `a1` and `a2`
  have other : ∀ d, P d → X.Inc d C.a1 → d ≠ C.e1 → X.Joins d C.a1 C.a2 := by
    intro d hd hda hne
    have hnc : C.S (X.ends d).1 = C.S (X.ends d).2 := by
      refine Classical.byContradiction fun hc => ?_
      rcases C.cut d hd hc with rfl | rfl
      · exact hne rfl
      · rcases inc_of_joins C.j2 hda with e | e
        · exact C.ha e
        · have := C.sb2; rw [← e, C.sa1] at this; exact absurd this (by decide)
    have hl := hG.1 d
    rcases hda with e | e
    · have hz : (X.ends d).2 = C.a1 ∨ (X.ends d).2 = C.a2 :=
        only _ ⟨d, hd, Or.inr rfl⟩ (by rw [← hnc, e, C.sa1])
      rcases hz with hz | hz
      · exact absurd (e.trans hz.symm) hl
      · left; rw [← e, ← hz]
    · have hz : (X.ends d).1 = C.a1 ∨ (X.ends d).1 = C.a2 :=
        only _ ⟨d, hd, Or.inl rfl⟩ (by rw [hnc, e, C.sa1])
      rcases hz with hz | hz
      · exact absurd (hz.trans e.symm) hl
      · right; rw [← e, ← hz]
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ :=
    hG.2.2.2 C.a1 ⟨C.e1, C.P1, joins_inc_left C.j1⟩
  rcases hall C.e1 C.P1 (joins_inc_left C.j1) with h | h | h
  · exact ⟨q, r, dqr, hq, hr, other q hq iq (by rw [h]; exact Ne.symm dpq),
      other r hr ir (by rw [h]; exact Ne.symm dpr)⟩
  · exact ⟨p, r, dpr, hp, hr, other p hp ip (by rw [h]; exact dpq),
      other r hr ir (by rw [h]; exact Ne.symm dqr)⟩
  · exact ⟨p, q, dpq, hp, hq, other p hp ip (by rw [h]; exact dpr),
      other q hq iq (by rw [h]; exact dqr)⟩

/-- **a simple 2-cut-reduced member of 𝒢 has no 2-edge-cut**, hence lies in 𝒮 -/
theorem no2cut_of_simple {P : Fin X.m → Prop} (hG : InG X P) (h2 : TwoCutReducedOn P) (hS : SimpleP P) :
    ∀ S, ¬ TwoCut P S := by
  intro S hS'
  obtain ⟨C, rfl⟩ := cut2_of_twoCut hG hS'
  have key : ∀ C' : Cut2 P, scount P C'.S true = 2 → False := by
    intro C' h
    obtain ⟨f, f', hne, hf, hf', jf, jf'⟩ := C'.side_two_par hG h
    exact hne (hS f f' _ _ hf hf' jf jf')
  rcases h2 _ hS' with h | h
  · exact key C h
  · exact key C.flip (by rw [scount_flip]; exact h)

theorem inS_of_simple {P : Fin X.m → Prop} (hG : InG X P) (h2 : TwoCutReducedOn P) (hS : SimpleP P) : InS X P :=
  ⟨hG, hS, no2cut_of_simple hG h2 hS⟩

/-! ### condition (d) and the engine statements -/

/-- an exchange of `(M, C)`: an edge of `M` that meets no edge of `C` -/
def Exch (M C : Fin X.m → Prop) (p : Fin X.m) : Prop := M p ∧ ∀ c, C c → ¬ Meet p c

/-- both ends of the edge `f` lie in the side `S` (the vertices with `S`-value `true`) -/
def Inside (S : Fin X.n → Bool) (f : Fin X.m) : Prop := S (X.ends f).1 = true ∧ S (X.ends f).2 = true

/-- condition (d), **no enclosed exchange**: every cyclic 3-edge-cut side `S` of `P` with at least 5 vertices that
    contains both ends of an exchange of `(M, C)` contains both ends of an edge of `C` -/
def NoEnc (P M C : Fin X.m → Prop) : Prop :=
  ∀ S, CycSide P S → 5 ≤ scount P S true → (∃ p, Exch M C p ∧ Inside S p) → ∃ c, C c ∧ Inside S c

/-- an eligible edge `g` of `P`: no other edge of `P` joins its ends, and `g` lies in no 2-edge-cut of `P` (its ends
    are distinct since the ambient is loopless) -/
def Eligible (P : Fin X.m → Prop) (g : Fin X.m) : Prop :=
  P g ∧ (∀ h, P h → h ≠ g → ¬ X.Joins h (X.ends g).1 (X.ends g).2) ∧ (∀ S, TwoCut P S → ¬ Crosses P S g)

end ne

/-- (FE-EXT-NE)₁₆: for every member `P` of 𝒟 with at least 16 vertices, every perfect matching `M` and every
    far-exchange set `C` for `M` with no enclosed exchange, `P` has a star 6-colouring `c` with `c⁻¹(6) = M` and
    `c⁻¹(5) = C` (colours `5` and `4` of `Fin 6`) -/
def FEEXTNE16 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 16 ≤ vcount P →
    ∀ M C, PMOn P M → FarEx P M C → NoEnc P M C →
      ∃ c, StarOn P 6 c ∧ ∀ f, P f → ((M f ↔ c f = 5) ∧ (C f ↔ c f = 4))

/-- (FE-EXIST-NE)₁₆: for every member `P` of 𝒟 with at least 16 vertices, every edge `g` and every status `t`
    realised by some perfect matching, there are a perfect matching `M` with `[g ∈ M] = t` and a far-exchange set for
    `M` with no enclosed exchange -/
def FEEXISTNE16 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 16 ≤ vcount P →
    ∀ g, P g → ∀ t : Bool, (∃ N, PMOn P N ∧ (N g ↔ t = true)) →
      ∃ M, PMOn P M ∧ (M g ↔ t = true) ∧ ∃ C, FarEx P M C ∧ NoEnc P M C

/-- (FE-EXT-T-NE)₁₆: for every member `P` of 𝒟 with at least 16 vertices, every eligible edge `g`, every perfect
    matching `M` with `g ∉ M` and every far-exchange set `C` for `M` with `g ∉ C` and no enclosed exchange, the leaf
    graph T(P, g) has a star 6-colouring whose colour class `6` (`5` here) is `M ∪ {xℓ}` and whose colour class `5`
    (`4` here) is `C`; `xℓ` is the new edge `newE g 2` -/
def FEEXTTNE16 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 16 ≤ vcount P →
    ∀ g, Eligible P g → ∀ M C, PMOn P M → ¬ M g → FarEx P M C → ¬ C g → NoEnc P M C →
      ∃ c, StarOn (leafSet P g) 6 c ∧ ∀ e, leafSet P g e →
        ((c e = 5 ↔ (∃ f, M f ∧ e = oldE g f) ∨ e = newE g 2 (by decide)) ∧ (c e = 4 ↔ ∃ f, C f ∧ e = oldE g f))

/-- (FE-EXIST-0-NE)₁₆: for every member `P` of 𝒟 with at least 16 vertices and every eligible edge `g` there are a
    perfect matching `M` with `g ∉ M` and a far-exchange set `C` for `M` with `g ∉ C` and no enclosed exchange -/
def FEEXIST0NE16 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 16 ≤ vcount P →
    ∀ g, Eligible P g → ∃ M, PMOn P M ∧ ¬ M g ∧ ∃ C, FarEx P M C ∧ ¬ C g ∧ NoEnc P M C

/-! ### the finite facts (named hypotheses) -/

/-- Lemma BASE12 (fact a20d73d94641ebb9): every member of 𝒟 with 10 or 12 vertices is EX1-good -/
def BASE12 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → (vcount P = 10 ∨ vcount P = 12) → EX1On P

/-- Lemma SIMPLE14 (fact 8f3cb2fcdd7e4727): every simple 3-edge-connected cubic graph on 14 vertices (member of 𝒮)
    is EX1-good -/
def SIMPLE14 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InS X P → vcount P = 14 → EX1On P

/-- Lemma B14-D (fact aa531b4ce552c207): every member of 𝒟 with exactly 14 vertices that is not simple is
    EX1-good -/
def B14D : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → vcount P = 14 → ¬ SimpleP P → EX1On P

/-- Lemma LMC8 (fact 9e8d394528f010f9): every member of 𝒢 with at most 8 vertices is MC-leaf-good at every edge:
    T(P, g) has a star 6-colouring in which every vertex meets exactly one edge of colour `6` (`5` here) -/
def LMC8 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → vcount P ≤ 8 → ∀ g, P g → ∃ c, MCol (leafSet P g) c

/-- Lemma LMC14 (fact 18134123ad3fcd9c): every member of 𝒟 with 10 to 14 vertices is MC-leaf-good at every
    eligible edge -/
def LMC14 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 10 ≤ vcount P → vcount P ≤ 14 →
    ∀ g, Eligible P g → ∃ c, MCol (leafSet P g) c

/-! ### Theorem H-ENG-NE and Theorem ROOT-CS3 -/

/-- **Theorem H-ENG-NE** (fact b771fa70cbc11e0b), with its finite facts BASE12, SIMPLE14 and B14-D as hypotheses:
    (FE-EXT-NE)₁₆ ∧ (FE-EXIST-NE)₁₆ implies (H) -/
theorem hengne (hB12 : BASE12) (hS14 : SIMPLE14) (hB14 : B14D) (hext : FEEXTNE16) (hex : FEEXISTNE16) : Hyp := by
  intro X P hG h10 h2
  have hev := vcount_even RH2P.pstat hG
  by_cases h12 : vcount P ≤ 12
  · exact hB12 X P hG h2 (by omega)
  by_cases h14 : vcount P = 14
  · by_cases hs : SimpleP P
    · exact hS14 X P (inS_of_simple hG h2 hs) h14
    · exact hB14 X P hG h2 h14 hs
  have h16 : 16 ≤ vcount P := by omega
  intro g hg t ht
  obtain ⟨M, hM, hst, C, hC, hne⟩ := hex X P hG h2 h16 g hg t ht
  obtain ⟨c, hc, hcl⟩ := hext X P hG h2 h16 M C hM hC hne
  exact ⟨M, hM, hst, c, hc, 5, fun f hf => (hcl f hf).1⟩

/-- (II_D) from the leaf engine statements and the finite facts LMC8, LMC14 (part (2) of ROOT-CS3) -/
theorem iid_of_ne (hL8 : LMC8) (hL14 : LMC14) (hextT : FEEXTTNE16) (hex0 : FEEXIST0NE16) : IID := by
  intro X P hG h6 h2 g hg hpar hcut
  have hev := vcount_even RH2P.pstat hG
  have hel : Eligible P g := ⟨hg, hpar, hcut⟩
  by_cases h8 : vcount P ≤ 8
  · obtain ⟨c, hc⟩ := hL8 X P hG h8 g hg
    exact ⟨c, hc.1⟩
  by_cases h14 : vcount P ≤ 14
  · obtain ⟨c, hc⟩ := hL14 X P hG h2 (by omega) h14 g hel
    exact ⟨c, hc.1⟩
  have h16 : 16 ≤ vcount P := by omega
  obtain ⟨M, hM, hMg, C, hC, hCg, hne⟩ := hex0 X P hG h2 h16 g hel
  obtain ⟨c, hc, _⟩ := hextT X P hG h2 h16 g hel M C hM hMg hC hCg hne
  exact ⟨c, hc⟩

/-- **Theorem ROOT-CS3** (fact 2d98b2523e97e6a0), with the finite facts BASE12, SIMPLE14, B14-D, LMC8 and LMC14 as
    hypotheses: the four NE engine statements imply (1) (H), (2) (II_D), (3) (II) and (4) DMS -/
theorem rootcs3 (hB12 : BASE12) (hS14 : SIMPLE14) (hB14 : B14D) (hL8 : LMC8) (hL14 : LMC14)
    (hext : FEEXTNE16) (hex : FEEXISTNE16) (hextT : FEEXTTNE16) (hex0 : FEEXIST0NE16) :
    Hyp ∧ IID ∧ II ∧ DMS := by
  have hH := hengne hB12 hS14 hB14 hext hex
  have hD := iid_of_ne hL8 hL14 hextT hex0
  exact ⟨hH, hD, ii_of hH hD, rh2_final hH (ii_of hH hD)⟩

/-- **layer 19**: simple members of 𝒟 are in 𝒮; H-ENG-NE; (II_D) from the leaf engine statements; ROOT-CS3 -/
theorem layer19 :
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → SimpleP P → InS X P) ∧
    (BASE12 → SIMPLE14 → B14D → FEEXTNE16 → FEEXISTNE16 → Hyp) ∧
    (LMC8 → LMC14 → FEEXTTNE16 → FEEXIST0NE16 → IID) ∧
    (BASE12 → SIMPLE14 → B14D → LMC8 → LMC14 → FEEXTNE16 → FEEXISTNE16 → FEEXTTNE16 → FEEXIST0NE16 →
      Hyp ∧ IID ∧ II ∧ DMS) :=
  ⟨fun _ _ hG h2 hS => inS_of_simple hG h2 hS, hengne, iid_of_ne, rootcs3⟩

end RH2F
