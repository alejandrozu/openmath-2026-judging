-- Lean proof of fact 3e79907cfcc0085b (RH2F.layer9); added by fact_submit, do not edit
import MhFact_066dc781a8de9c11

-- ===== from GL.lean =====

namespace RH2F
open MGraph
open Classical

/-- the glued edge list: `A`-list with entry `jA` replaced by the cut edge `x u`, then the `B`-list shifted by `nA` with
    entry `jB` replaced by the cut edge `y v`; `(x, y)` and `(u, v)` are the ends of `jA`, `jB` oriented by `oA`, `oB` -/
def glueEl (elA : List (Nat × Nat)) (nA jA : Nat) (oA : Bool) (elB : List (Nat × Nat)) (jB : Nat) (oB : Bool) :
    List (Nat × Nat) :=
  elA.set jA (if oA then (gE elA jA).2 else (gE elA jA).1, (if oB then (gE elB jB).2 else (gE elB jB).1) + nA) ++
  (elB.map (fun e => (e.1 + nA, e.2 + nA))).set jB
    (if oA then (gE elA jA).1 else (gE elA jA).2, (if oB then (gE elB jB).1 else (gE elB jB).2) + nA)

section glueEl
variable {elA elB : List (Nat × Nat)} {nA jA jB : Nat} {oA oB : Bool}

theorem glueEl_length : (glueEl elA nA jA oA elB jB oB).length = elA.length + elB.length := by simp [glueEl]

theorem glue_A {i : Nat} (hi : i < elA.length) (hij : i ≠ jA) : gE (glueEl elA nA jA oA elB jB oB) i = gE elA i := by
  unfold gE glueEl
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi),
    List.getElem?_set_ne (Ne.symm hij)]

theorem glue_jA (hj : jA < elA.length) : gE (glueEl elA nA jA oA elB jB oB) jA =
    (if oA then (gE elA jA).2 else (gE elA jA).1, (if oB then (gE elB jB).2 else (gE elB jB).1) + nA) := by
  rw [show gE (glueEl elA nA jA oA elB jB oB) jA = (glueEl elA nA jA oA elB jB oB).getD jA (0, 0) from rfl]
  unfold glueEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj), List.getElem?_set_self hj]
  rfl

theorem glue_B {i : Nat} (hi : i < elB.length) (hij : i ≠ jB) :
    gE (glueEl elA nA jA oA elB jB oB) (elA.length + i) = ((gE elB i).1 + nA, (gE elB i).2 + nA) := by
  rw [show gE (glueEl elA nA jA oA elB jB oB) (elA.length + i) =
    (glueEl elA nA jA oA elB jB oB).getD (elA.length + i) (0, 0) from rfl]
  unfold glueEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getElem?_set_ne (Ne.symm (by simpa using hij))]
  simp [gE, List.getD_eq_getElem?_getD, hi]

theorem glue_jB (hj : jB < elB.length) : gE (glueEl elA nA jA oA elB jB oB) (elA.length + jB) =
    (if oA then (gE elA jA).1 else (gE elA jA).2, (if oB then (gE elB jB).1 else (gE elB jB).2) + nA) := by
  rw [show gE (glueEl elA nA jA oA elB jB oB) (elA.length + jB) =
    (glueEl elA nA jA oA elB jB oB).getD (elA.length + jB) (0, 0) from rfl]
  unfold glueEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [List.getElem?_set_self, hj]

end glueEl


theorem elOK_glue {nA nB : Nat} {elA elB : List (Nat × Nat)} {jA jB : Nat} {oA oB : Bool}
    (hA : elOK nA elA = true) (hB : elOK nB elB = true) (hjA : jA < elA.length) (hjB : jB < elB.length) :
    elOK (nA + nB) (glueEl elA nA jA oA elB jB oB) = true := by
  unfold elOK at hA hB ⊢
  rw [List.all_eq_true] at hA hB ⊢
  have mA : gE elA jA ∈ elA := by
    unfold gE; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjA]; exact List.getElem_mem hjA
  have mB : gE elB jB ∈ elB := by
    unfold gE; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjB]; exact List.getElem_mem hjB
  have bA := hA _ mA
  have bB := hB _ mB
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at bA bB
  intro e he
  unfold glueEl at he
  rw [List.mem_append] at he
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  rcases he with he | he
  · rcases List.mem_or_eq_of_mem_set he with he | rfl
    · have := hA e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
      exact ⟨⟨by omega, by omega⟩, this.2⟩
    · cases oA <;> cases oB <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
        exact ⟨⟨by omega, by omega⟩, by omega⟩
  · rcases List.mem_or_eq_of_mem_set he with he | rfl
    · rw [List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      have := hB e' he'
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · cases oA <;> cases oB <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
        exact ⟨⟨by omega, by omega⟩, by omega⟩


section glueiso
variable {X : MGraph} {P : Fin X.m → Prop}

/-- **the gluing isomorphism**: isomorphisms of both edge closures of a 2-edge-cut onto `ofList nA elA` and
    `ofList nB elB` give an isomorphism of `P` onto the glued multigraph `ofList (nA + nB) (glueEl …)` -/
theorem Cut2.glue_iso (C : Cut2 P) {nA nB : Nat} {elA elB : List (Nat × Nat)} {hnA : 0 < nA} {hnB : 0 < nB}
    (helA : elOK nA elA = true) (helB : elOK nB elB = true)
    {αA : Fin X.n → Fin (ofList nA elA hnA).n} {βA : Fin (addEdge X C.a1 C.a2).m → Fin (ofList nA elA hnA).m}
    (hA : IsoMap C.clo (ofList nA elA hnA) αA βA) (oA : Bool)
    (hoA1 : (if oA then (gE elA (βA (Fin.last X.m)).val).2 else (gE elA (βA (Fin.last X.m)).val).1) = (αA C.a1).val)
    (hoA2 : (if oA then (gE elA (βA (Fin.last X.m)).val).1 else (gE elA (βA (Fin.last X.m)).val).2) = (αA C.a2).val)
    {αB : Fin X.n → Fin (ofList nB elB hnB).n} {βB : Fin (addEdge X C.b1 C.b2).m → Fin (ofList nB elB hnB).m}
    (hB : IsoMap C.flip.clo (ofList nB elB hnB) αB βB) (oB : Bool)
    (hoB1 : (if oB then (gE elB (βB (Fin.last X.m)).val).2 else (gE elB (βB (Fin.last X.m)).val).1) = (αB C.b1).val)
    (hoB2 : (if oB then (gE elB (βB (Fin.last X.m)).val).1 else (gE elB (βB (Fin.last X.m)).val).2) = (αB C.b2).val) :
    ∃ a b, IsoMap P (ofList (nA + nB) (glueEl elA nA (βA (Fin.last X.m)).val oA elB (βB (Fin.last X.m)).val oB)
      (Nat.lt_of_lt_of_le hnA (Nat.le_add_right nA nB))) a b := by
  obtain ⟨hαA, hβA, hsA, hjA⟩ := hA
  obtain ⟨hαB, hβB, hsB, hjB⟩ := hB
  let jA := (βA (Fin.last X.m)).val
  let jB := (βB (Fin.last X.m)).val
  have hjAl : jA < elA.length := (βA (Fin.last X.m)).isLt
  have hjBl : jB < elB.length := (βB (Fin.last X.m)).isLt
  have hlen := glueEl_length (elA := elA) (nA := nA) (jA := jA) (oA := oA) (elB := elB) (jB := jB) (oB := oB)
  let α : Fin X.n → Fin (nA + nB) := fun v =>
    if C.S v = true then ⟨(αA v).val, by have : (αA v).val < nA := (αA v).isLt; omega⟩
    else ⟨(αB v).val + nA, by have : (αB v).val < nB := (αB v).isLt; omega⟩
  let β : Fin X.m → Fin (glueEl elA nA jA oA elB jB oB).length := fun f =>
    if C.inA f then ⟨(βA (Fin.castSucc f)).val, by have : (βA (Fin.castSucc f)).val < elA.length := (βA _).isLt; omega⟩
    else if C.flip.inA f then ⟨elA.length + (βB (Fin.castSucc f)).val,
      by have : (βB (Fin.castSucc f)).val < elB.length := (βB _).isLt; omega⟩
    else if f = C.e1 then ⟨jA, by omega⟩ else ⟨elA.length + jB, by omega⟩
  have αA_ : ∀ v, C.S v = true → (α v).val = (αA v).val := fun v hv => by simp [α, hv]
  have αB_ : ∀ v, C.S v = false → (α v).val = (αB v).val + nA := fun v hv => by simp [α, hv]
  have βA_ : ∀ f, C.inA f → (β f).val = (βA (Fin.castSucc f)).val := fun f hf => by simp [β, hf]
  have βB_ : ∀ f, C.flip.inA f → (β f).val = elA.length + (βB (Fin.castSucc f)).val := fun f hf => by
    have : ¬ C.inA f := fun h => C.not_flip_of_inA h hf
    simp [β, this, hf]
  have βe1 : (β C.e1).val = jA := by
    have h1 : ¬ C.inA C.e1 := C.not_inA_of_cut (Or.inl rfl)
    have h2 : ¬ C.flip.inA C.e1 := C.flip.not_inA_of_cut (Or.inl rfl)
    simp [β, h1, h2]
  have βe2 : (β C.e2).val = elA.length + jB := by
    have h1 : ¬ C.inA C.e2 := C.not_inA_of_cut (Or.inr rfl)
    have h2 : ¬ C.flip.inA C.e2 := C.flip.not_inA_of_cut (Or.inr rfl)
    simp [β, h1, h2, Ne.symm C.ne12]
  have neA : ∀ f, C.inA f → (βA (Fin.castSucc f)).val ≠ jA := fun f hf h =>
    castSucc_ne_last f (hβA _ _ (C.clo_old hf) C.clo_last (Fin.ext h))
  have neB : ∀ f, C.flip.inA f → (βB (Fin.castSucc f)).val ≠ jB := fun f hf h =>
    castSucc_ne_last f (hβB _ _ (C.flip.clo_old hf) C.flip.clo_last (Fin.ext h))
  have ltA : ∀ f, (βA f).val < elA.length := fun f => (βA f).isLt
  have ltB : ∀ f, (βB f).val < elB.length := fun f => (βB f).isLt
  have ltαA : ∀ v, (αA v).val < nA := fun v => (αA v).isLt
  have hel' := elOK_glue (oA := oA) (oB := oB) helA helB hjAl hjBl
  have endsG := fun (e : Fin (ofList (nA + nB) (glueEl elA nA jA oA elB jB oB) (by omega)).m) =>
    ofList_ends (hn := by omega) hel' e
  have endsA := fun (e : Fin (ofList nA elA hnA).m) => ofList_ends (hn := hnA) helA e
  have endsB := fun (e : Fin (ofList nB elB hnB).m) => ofList_ends (hn := hnB) helB e
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · -- vertices
    intro x y hx hy hxy
    have hxy' := congrArg Fin.val hxy
    cases sx : C.S x <;> cases sy : C.S y
    · rw [αB_ x sx, αB_ y sy] at hxy'
      exact hαB x y ((C.flip.meets_clo x).2 ⟨hx, by simp [Cut2.flip_S, sx]⟩)
        ((C.flip.meets_clo y).2 ⟨hy, by simp [Cut2.flip_S, sy]⟩) (Fin.ext (by omega))
    · rw [αB_ x sx, αA_ y sy] at hxy'; have := ltαA y; omega
    · rw [αA_ x sx, αB_ y sy] at hxy'; have := ltαA x; omega
    · rw [αA_ x sx, αA_ y sy] at hxy'
      exact hαA x y ((C.meets_clo x).2 ⟨hx, sx⟩) ((C.meets_clo y).2 ⟨hy, sy⟩) (Fin.ext hxy')
  · -- edges
    intro f g hf hg hfg
    have hfg' := congrArg Fin.val hfg
    rcases C.cases_P hf with fA | fB | fc <;> rcases C.cases_P hg with gA | gB | gc
    · rw [βA_ f fA, βA_ g gA] at hfg'
      exact castSucc_inj' (hβA _ _ (C.clo_old fA) (C.clo_old gA) (Fin.ext hfg'))
    · rw [βA_ f fA, βB_ g gB] at hfg'; have := ltA (Fin.castSucc f); omega
    · rcases gc with rfl | rfl
      · rw [βA_ f fA, βe1] at hfg'; exact absurd hfg' (neA f fA)
      · rw [βA_ f fA, βe2] at hfg'; have := ltA (Fin.castSucc f); omega
    · rw [βB_ f fB, βA_ g gA] at hfg'; have := ltA (Fin.castSucc g); omega
    · rw [βB_ f fB, βB_ g gB] at hfg'
      exact castSucc_inj' (hβB _ _ (C.flip.clo_old fB) (C.flip.clo_old gB) (Fin.ext (by omega)))
    · rcases gc with rfl | rfl
      · rw [βB_ f fB, βe1] at hfg'; omega
      · rw [βB_ f fB, βe2] at hfg'; exact absurd (by omega) (neB f fB)
    · rcases fc with rfl | rfl
      · rw [βe1, βA_ g gA] at hfg'; exact absurd hfg'.symm (neA g gA)
      · rw [βe2, βA_ g gA] at hfg'; have := ltA (Fin.castSucc g); omega
    · rcases fc with rfl | rfl
      · rw [βe1, βB_ g gB] at hfg'; omega
      · rw [βe2, βB_ g gB] at hfg'; exact absurd (by omega) (neB g gB)
    · rcases fc with rfl | rfl <;> rcases gc with rfl | rfl
      · rfl
      · rw [βe1, βe2] at hfg'; omega
      · rw [βe2, βe1] at hfg'; omega
      · rfl
  · -- surjective
    intro i
    have hi : i.val < elA.length + elB.length := by
      have : i.val < (glueEl elA nA jA oA elB jB oB).length := i.isLt
      omega
    by_cases hiA : i.val < elA.length
    · obtain ⟨g, hg, hgi⟩ := hsA ⟨i.val, hiA⟩
      rcases hg with rfl | ⟨d, rfl, hd⟩
      · exact ⟨C.e1, C.P1, Fin.ext (by rw [βe1]; exact congrArg Fin.val hgi)⟩
      · exact ⟨d, hd.1, Fin.ext (by rw [βA_ d hd]; exact congrArg Fin.val hgi)⟩
    · obtain ⟨g, hg, hgi⟩ := hsB ⟨i.val - elA.length, by show i.val - elA.length < elB.length; omega⟩
      have hgi' := congrArg Fin.val hgi
      simp only at hgi'
      rcases hg with rfl | ⟨d, rfl, hd⟩
      · exact ⟨C.e2, C.P2, Fin.ext (by rw [βe2]; show elA.length + jB = i.val; omega)⟩
      · exact ⟨d, hd.1, Fin.ext (by rw [βB_ d hd]; omega)⟩
  · -- incidence
    intro f hf
    have hG' := endsG (β f)
    rcases C.cases_P hf with fA | fB | fc
    · have hj := hjA _ (C.clo_old fA)
      rw [addEdge_ends_old] at hj
      have s1 := C.side_of_inA fA (Or.inl rfl)
      have s2 := C.side_of_inA fA (Or.inr rfl)
      have hQ := endsA (βA (Fin.castSucc f))
      rw [βA_ f fA, glue_A (ltA _) (neA f fA)] at hG'
      rcases hj with h | h <;> rw [h] at hQ <;> simp only at hQ
      · exact Or.inl (Prod.ext (Fin.ext (by rw [hG'.1, αA_ _ s1]; exact hQ.1.symm))
          (Fin.ext (by rw [hG'.2, αA_ _ s2]; exact hQ.2.symm)))
      · exact Or.inr (Prod.ext (Fin.ext (by rw [hG'.1, αA_ _ s2]; exact hQ.1.symm))
          (Fin.ext (by rw [hG'.2, αA_ _ s1]; exact hQ.2.symm)))
    · have hj := hjB _ (C.flip.clo_old fB)
      rw [addEdge_ends_old] at hj
      have s1 : C.S (X.ends f).1 = false := by
        have := C.flip.side_of_inA fB (Or.inl rfl); simpa [Cut2.flip_S] using this
      have s2 : C.S (X.ends f).2 = false := by
        have := C.flip.side_of_inA fB (Or.inr rfl); simpa [Cut2.flip_S] using this
      have hQ := endsB (βB (Fin.castSucc f))
      rw [βB_ f fB, glue_B (ltB _) (neB f fB)] at hG'
      rcases hj with h | h <;> rw [h] at hQ <;> simp only at hQ
      · exact Or.inl (Prod.ext (Fin.ext (by rw [hG'.1, αB_ _ s1, ← hQ.1]))
          (Fin.ext (by rw [hG'.2, αB_ _ s2, ← hQ.2])))
      · exact Or.inr (Prod.ext (Fin.ext (by rw [hG'.1, αB_ _ s2, ← hQ.1]))
          (Fin.ext (by rw [hG'.2, αB_ _ s1, ← hQ.2])))
    · rcases fc with rfl | rfl
      · rw [βe1, glue_jA hjAl] at hG'
        have ha : (α C.a1).val = (if oA then (gE elA jA).2 else (gE elA jA).1) := by rw [αA_ _ C.sa1]; exact hoA1.symm
        have hb : (α C.b1).val = (if oB then (gE elB jB).2 else (gE elB jB).1) + nA := by
          rw [αB_ _ C.sb1, ← hoB1]
        rcases C.j1 with h | h <;> rw [h]
        · exact Or.inl (Prod.ext (Fin.ext (by rw [hG'.1, ha])) (Fin.ext (by rw [hG'.2, hb])))
        · exact Or.inr (Prod.ext (Fin.ext (by rw [hG'.1, ha])) (Fin.ext (by rw [hG'.2, hb])))
      · rw [βe2, glue_jB hjBl] at hG'
        have ha : (α C.a2).val = (if oA then (gE elA jA).1 else (gE elA jA).2) := by rw [αA_ _ C.sa2]; exact hoA2.symm
        have hb : (α C.b2).val = (if oB then (gE elB jB).1 else (gE elB jB).2) + nA := by
          rw [αB_ _ C.sb2, ← hoB2]
        rcases C.j2 with h | h <;> rw [h]
        · exact Or.inl (Prod.ext (Fin.ext (by rw [hG'.1, ha])) (Fin.ext (by rw [hG'.2, hb])))
        · exact Or.inr (Prod.ext (Fin.ext (by rw [hG'.1, ha])) (Fin.ext (by rw [hG'.2, hb])))

end glueiso

end RH2F


-- ===== from TC.lean =====

/-! The gluings of table T6 (TAB-C, fact 1cbbdf1f13cbe1b5) re-indexed as `glueEl`, their EX1 certificates,
    the end-swapping automorphisms of Rep02 at entry 2 and Rep03 at entry 0, and the edge swaps between the two
    equal-orientation gluings. -/

namespace RH2F
open MGraph

theorem t6_3_0_4_0 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 4) 0 false) [([[(0, 4, 1), (3, 2, 5), (5, 3, 3)], [(1, 2, 4), (2, 3, 5), (6, 5, 0)], [(1, 1, 4), (3, 0, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 0, 3)], [(0, 0, 1), (7, 5, 5), (11, 8, 2)], [(6, 1, 0), (7, 4, 5), (10, 7, 3)], [(8, 7, 5), (9, 7, 1), (14, 9, 0)], [(8, 6, 5), (9, 6, 1), (10, 5, 3)], [(11, 4, 2), (12, 9, 5), (13, 9, 1)], [(12, 8, 5), (13, 8, 1), (14, 6, 0)]], [1, 4, 5, 5, 2, 3, 0, 5, 5, 1, 3, 2, 5, 1, 0]), ([[(0, 4, 3), (3, 2, 1), (5, 3, 5)], [(1, 2, 5), (2, 3, 2), (6, 5, 0)], [(1, 1, 5), (3, 0, 1), (4, 3, 4)], [(2, 1, 2), (4, 2, 4), (5, 0, 5)], [(0, 0, 3), (7, 5, 1), (11, 8, 5)], [(6, 1, 0), (7, 4, 1), (10, 7, 5)], [(8, 7, 4), (9, 7, 3), (14, 9, 5)], [(8, 6, 4), (9, 6, 3), (10, 5, 5)], [(11, 4, 5), (12, 9, 2), (13, 9, 0)], [(12, 8, 2), (13, 8, 0), (14, 6, 5)]], [3, 5, 2, 1, 4, 5, 0, 1, 4, 3, 5, 5, 2, 0, 5]), ([[(0, 4, 5), (3, 2, 3), (5, 3, 1)], [(1, 2, 4), (2, 3, 2), (6, 5, 5)], [(1, 1, 4), (3, 0, 3), (4, 3, 5)], [(2, 1, 2), (4, 2, 5), (5, 0, 1)], [(0, 0, 5), (7, 5, 0), (11, 8, 2)], [(6, 1, 5), (7, 4, 0), (10, 7, 1)], [(8, 7, 2), (9, 7, 5), (14, 9, 0)], [(8, 6, 2), (9, 6, 5), (10, 5, 1)], [(11, 4, 2), (12, 9, 1), (13, 9, 5)], [(12, 8, 1), (13, 8, 5), (14, 6, 0)]], [5, 4, 2, 3, 5, 1, 5, 0, 2, 5, 1, 2, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_3_0_4_0 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 4) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 4) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [6, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_4_4 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 4) 4 false) [([[(0, 7, 0), (3, 2, 5), (5, 3, 1)], [(1, 2, 3), (2, 3, 5), (10, 5, 0)], [(1, 1, 3), (3, 0, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 0, 1)], [(6, 5, 5), (7, 5, 1), (11, 8, 2)], [(6, 4, 5), (7, 4, 1), (10, 1, 0)], [(8, 7, 5), (9, 7, 2), (14, 9, 1)], [(0, 0, 0), (8, 6, 5), (9, 6, 2)], [(11, 4, 2), (12, 9, 5), (13, 9, 0)], [(12, 8, 5), (13, 8, 0), (14, 6, 1)]], [0, 3, 5, 5, 2, 1, 5, 1, 5, 2, 0, 2, 5, 0, 1]), ([[(0, 7, 0), (3, 2, 2), (5, 3, 5)], [(1, 2, 5), (2, 3, 3), (10, 5, 0)], [(1, 1, 5), (3, 0, 2), (4, 3, 1)], [(2, 1, 3), (4, 2, 1), (5, 0, 5)], [(6, 5, 1), (7, 5, 5), (11, 8, 2)], [(6, 4, 1), (7, 4, 5), (10, 1, 0)], [(8, 7, 2), (9, 7, 5), (14, 9, 1)], [(0, 0, 0), (8, 6, 2), (9, 6, 5)], [(11, 4, 2), (12, 9, 0), (13, 9, 5)], [(12, 8, 0), (13, 8, 5), (14, 6, 1)]], [0, 5, 3, 2, 1, 5, 1, 5, 2, 5, 0, 2, 0, 5, 1]), ([[(0, 7, 5), (3, 2, 0), (5, 3, 4)], [(1, 2, 1), (2, 3, 3), (10, 5, 5)], [(1, 1, 1), (3, 0, 0), (4, 3, 5)], [(2, 1, 3), (4, 2, 5), (5, 0, 4)], [(6, 5, 4), (7, 5, 2), (11, 8, 5)], [(6, 4, 4), (7, 4, 2), (10, 1, 5)], [(8, 7, 3), (9, 7, 2), (14, 9, 5)], [(0, 0, 5), (8, 6, 3), (9, 6, 2)], [(11, 4, 5), (12, 9, 1), (13, 9, 0)], [(12, 8, 1), (13, 8, 0), (14, 6, 5)]], [5, 1, 3, 0, 5, 4, 4, 2, 3, 2, 5, 5, 1, 0, 5])] = true := by
  decide +kernel
theorem sw6_3_0_4_4 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 4) 4 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 4) 4 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_6_0 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 0 false) [([[(0, 6, 0), (3, 2, 5), (5, 3, 1)], [(1, 2, 3), (2, 3, 5), (6, 5, 0)], [(1, 1, 3), (3, 0, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 0, 1)], [(8, 6, 5), (10, 7, 3), (11, 8, 2)], [(6, 1, 0), (7, 7, 5), (14, 9, 1)], [(0, 0, 0), (8, 4, 5), (9, 7, 4)], [(7, 5, 5), (9, 6, 4), (10, 4, 3)], [(11, 4, 2), (12, 9, 5), (13, 9, 0)], [(12, 8, 5), (13, 8, 0), (14, 5, 1)]], [0, 3, 5, 5, 2, 1, 0, 5, 5, 4, 3, 2, 5, 0, 1]), ([[(0, 6, 4), (3, 2, 3), (5, 3, 5)], [(1, 2, 5), (2, 3, 1), (6, 5, 0)], [(1, 1, 5), (3, 0, 3), (4, 3, 2)], [(2, 1, 1), (4, 2, 2), (5, 0, 5)], [(8, 6, 1), (10, 7, 0), (11, 8, 5)], [(6, 1, 0), (7, 7, 3), (14, 9, 5)], [(0, 0, 4), (8, 4, 1), (9, 7, 5)], [(7, 5, 3), (9, 6, 5), (10, 4, 0)], [(11, 4, 5), (12, 9, 2), (13, 9, 4)], [(12, 8, 2), (13, 8, 4), (14, 5, 5)]], [4, 5, 1, 3, 2, 5, 0, 3, 1, 5, 0, 5, 2, 4, 5]), ([[(0, 6, 5), (3, 2, 3), (5, 3, 2)], [(1, 2, 4), (2, 3, 1), (6, 5, 5)], [(1, 1, 4), (3, 0, 3), (4, 3, 5)], [(2, 1, 1), (4, 2, 5), (5, 0, 2)], [(8, 6, 1), (10, 7, 5), (11, 8, 2)], [(6, 1, 5), (7, 7, 3), (14, 9, 0)], [(0, 0, 5), (8, 4, 1), (9, 7, 0)], [(7, 5, 3), (9, 6, 0), (10, 4, 5)], [(11, 4, 2), (12, 9, 1), (13, 9, 5)], [(12, 8, 1), (13, 8, 5), (14, 5, 0)]], [5, 4, 1, 3, 5, 2, 5, 3, 1, 0, 5, 2, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_3_0_6_0 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 6) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [6, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_6_3 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 3 false) [([[(0, 6, 0), (3, 2, 5), (5, 3, 1)], [(1, 2, 3), (2, 3, 5), (9, 7, 0)], [(1, 1, 3), (3, 0, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 0, 1)], [(8, 6, 5), (10, 7, 3), (11, 8, 2)], [(6, 6, 4), (7, 7, 5), (14, 9, 1)], [(0, 0, 0), (6, 5, 4), (8, 4, 5)], [(7, 5, 5), (9, 1, 0), (10, 4, 3)], [(11, 4, 2), (12, 9, 5), (13, 9, 0)], [(12, 8, 5), (13, 8, 0), (14, 5, 1)]], [0, 3, 5, 5, 2, 1, 4, 5, 5, 0, 3, 2, 5, 0, 1]), ([[(0, 6, 0), (3, 2, 2), (5, 3, 5)], [(1, 2, 5), (2, 3, 3), (9, 7, 0)], [(1, 1, 5), (3, 0, 2), (4, 3, 1)], [(2, 1, 3), (4, 2, 1), (5, 0, 5)], [(8, 6, 3), (10, 7, 5), (11, 8, 2)], [(6, 6, 5), (7, 7, 4), (14, 9, 1)], [(0, 0, 0), (6, 5, 5), (8, 4, 3)], [(7, 5, 4), (9, 1, 0), (10, 4, 5)], [(11, 4, 2), (12, 9, 0), (13, 9, 5)], [(12, 8, 0), (13, 8, 5), (14, 5, 1)]], [0, 5, 3, 2, 1, 5, 5, 4, 3, 0, 5, 2, 0, 5, 1]), ([[(0, 6, 5), (3, 2, 2), (5, 3, 0)], [(1, 2, 1), (2, 3, 4), (9, 7, 5)], [(1, 1, 1), (3, 0, 2), (4, 3, 5)], [(2, 1, 4), (4, 2, 5), (5, 0, 0)], [(8, 6, 3), (10, 7, 2), (11, 8, 5)], [(6, 6, 4), (7, 7, 3), (14, 9, 5)], [(0, 0, 5), (6, 5, 4), (8, 4, 3)], [(7, 5, 3), (9, 1, 5), (10, 4, 2)], [(11, 4, 5), (12, 9, 1), (13, 9, 0)], [(12, 8, 1), (13, 8, 0), (14, 5, 5)]], [5, 1, 4, 2, 5, 0, 4, 3, 3, 5, 2, 5, 1, 0, 5])] = true := by
  decide +kernel
theorem sw6_3_0_6_3 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 6) 3 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 3 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_6_5 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 5 false) [([[(0, 4, 0), (3, 2, 5), (5, 3, 1)], [(1, 2, 3), (2, 3, 5), (11, 8, 0)], [(1, 1, 3), (3, 0, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 0, 1)], [(0, 0, 0), (8, 6, 5), (10, 7, 2)], [(6, 6, 4), (7, 7, 5), (14, 9, 1)], [(6, 5, 4), (8, 4, 5), (9, 7, 3)], [(7, 5, 5), (9, 6, 3), (10, 4, 2)], [(11, 1, 0), (12, 9, 5), (13, 9, 2)], [(12, 8, 5), (13, 8, 2), (14, 5, 1)]], [0, 3, 5, 5, 2, 1, 4, 5, 5, 3, 2, 0, 5, 2, 1]), ([[(0, 4, 0), (3, 2, 2), (5, 3, 5)], [(1, 2, 5), (2, 3, 3), (11, 8, 0)], [(1, 1, 5), (3, 0, 2), (4, 3, 1)], [(2, 1, 3), (4, 2, 1), (5, 0, 5)], [(0, 0, 0), (8, 6, 3), (10, 7, 5)], [(6, 6, 5), (7, 7, 4), (14, 9, 1)], [(6, 5, 5), (8, 4, 3), (9, 7, 2)], [(7, 5, 4), (9, 6, 2), (10, 4, 5)], [(11, 1, 0), (12, 9, 2), (13, 9, 5)], [(12, 8, 2), (13, 8, 5), (14, 5, 1)]], [0, 5, 3, 2, 1, 5, 5, 4, 3, 2, 5, 0, 2, 5, 1]), ([[(0, 4, 5), (3, 2, 2), (5, 3, 1)], [(1, 2, 3), (2, 3, 4), (11, 8, 5)], [(1, 1, 3), (3, 0, 2), (4, 3, 5)], [(2, 1, 4), (4, 2, 5), (5, 0, 1)], [(0, 0, 5), (8, 6, 4), (10, 7, 0)], [(6, 6, 3), (7, 7, 2), (14, 9, 5)], [(6, 5, 3), (8, 4, 4), (9, 7, 5)], [(7, 5, 2), (9, 6, 5), (10, 4, 0)], [(11, 1, 5), (12, 9, 1), (13, 9, 0)], [(12, 8, 1), (13, 8, 0), (14, 5, 5)]], [5, 3, 4, 2, 5, 1, 3, 2, 4, 5, 0, 5, 1, 0, 5])] = true := by
  decide +kernel
theorem sw6_3_0_6_5 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 6) 5 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 5 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_6_6 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 6 false) [([[(0, 8, 1), (3, 2, 5), (5, 3, 2)], [(1, 2, 4), (2, 3, 5), (12, 9, 0)], [(1, 1, 4), (3, 0, 5), (4, 3, 3)], [(2, 1, 5), (4, 2, 3), (5, 0, 2)], [(8, 6, 5), (10, 7, 0), (11, 8, 3)], [(6, 6, 4), (7, 7, 5), (14, 9, 2)], [(6, 5, 4), (8, 4, 5), (9, 7, 1)], [(7, 5, 5), (9, 6, 1), (10, 4, 0)], [(0, 0, 1), (11, 4, 3), (13, 9, 5)], [(12, 1, 0), (13, 8, 5), (14, 5, 2)]], [1, 4, 5, 5, 3, 2, 4, 5, 5, 1, 0, 3, 0, 5, 2]), ([[(0, 8, 1), (3, 2, 3), (5, 3, 5)], [(1, 2, 5), (2, 3, 4), (12, 9, 0)], [(1, 1, 5), (3, 0, 3), (4, 3, 2)], [(2, 1, 4), (4, 2, 2), (5, 0, 5)], [(8, 6, 0), (10, 7, 4), (11, 8, 5)], [(6, 6, 3), (7, 7, 1), (14, 9, 5)], [(6, 5, 3), (8, 4, 0), (9, 7, 5)], [(7, 5, 1), (9, 6, 5), (10, 4, 4)], [(0, 0, 1), (11, 4, 5), (13, 9, 2)], [(12, 1, 0), (13, 8, 2), (14, 5, 5)]], [1, 5, 4, 3, 2, 5, 3, 1, 0, 5, 4, 5, 0, 2, 5]), ([[(0, 8, 5), (3, 2, 2), (5, 3, 0)], [(1, 2, 3), (2, 3, 4), (12, 9, 5)], [(1, 1, 3), (3, 0, 2), (4, 3, 5)], [(2, 1, 4), (4, 2, 5), (5, 0, 0)], [(8, 6, 4), (10, 7, 5), (11, 8, 3)], [(6, 6, 5), (7, 7, 2), (14, 9, 0)], [(6, 5, 5), (8, 4, 4), (9, 7, 1)], [(7, 5, 2), (9, 6, 1), (10, 4, 5)], [(0, 0, 5), (11, 4, 3), (13, 9, 1)], [(12, 1, 5), (13, 8, 1), (14, 5, 0)]], [5, 3, 4, 2, 5, 0, 5, 2, 4, 1, 5, 3, 5, 1, 0])] = true := by
  decide +kernel
theorem sw6_3_0_6_6 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 6) 6 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 6) 6 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [12, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 13, 14] = true := by decide +kernel
theorem t6_3_0_7_0 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 7) 0 false) [([[(0, 4, 3), (3, 2, 5), (5, 3, 2)], [(1, 2, 4), (2, 3, 5), (6, 5, 0)], [(1, 1, 4), (3, 0, 5), (4, 3, 1)], [(2, 1, 5), (4, 2, 1), (5, 0, 2)], [(0, 0, 3), (12, 8, 5), (14, 9, 0)], [(6, 1, 0), (7, 6, 5), (8, 7, 4)], [(7, 5, 5), (9, 8, 1), (10, 7, 3)], [(8, 5, 4), (10, 6, 3), (11, 9, 5)], [(9, 6, 1), (12, 4, 5), (13, 9, 2)], [(11, 7, 5), (13, 8, 2), (14, 4, 0)]], [3, 4, 5, 5, 1, 2, 0, 5, 4, 1, 3, 5, 5, 2, 0]), ([[(0, 4, 1), (3, 2, 3), (5, 3, 5)], [(1, 2, 5), (2, 3, 2), (6, 5, 0)], [(1, 1, 5), (3, 0, 3), (4, 3, 4)], [(2, 1, 2), (4, 2, 4), (5, 0, 5)], [(0, 0, 1), (12, 8, 2), (14, 9, 5)], [(6, 1, 0), (7, 6, 1), (8, 7, 5)], [(7, 5, 1), (9, 8, 5), (10, 7, 4)], [(8, 5, 5), (10, 6, 4), (11, 9, 3)], [(9, 6, 5), (12, 4, 2), (13, 9, 0)], [(11, 7, 3), (13, 8, 0), (14, 4, 5)]], [1, 5, 2, 3, 4, 5, 0, 1, 5, 5, 4, 3, 2, 0, 5]), ([[(0, 4, 5), (3, 2, 2), (5, 3, 4)], [(1, 2, 3), (2, 3, 1), (6, 5, 5)], [(1, 1, 3), (3, 0, 2), (4, 3, 5)], [(2, 1, 1), (4, 2, 5), (5, 0, 4)], [(0, 0, 5), (12, 8, 1), (14, 9, 0)], [(6, 1, 5), (7, 6, 4), (8, 7, 0)], [(7, 5, 4), (9, 8, 3), (10, 7, 5)], [(8, 5, 0), (10, 6, 5), (11, 9, 2)], [(9, 6, 3), (12, 4, 1), (13, 9, 5)], [(11, 7, 2), (13, 8, 5), (14, 4, 0)]], [5, 3, 1, 2, 5, 4, 5, 4, 0, 3, 5, 2, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_3_0_7_0 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 7) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 7) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [6, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_7_1 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 7) 1 false) [([[(0, 6, 4), (3, 2, 5), (5, 3, 3)], [(1, 2, 2), (2, 3, 5), (7, 5, 0)], [(1, 1, 2), (3, 0, 5), (4, 3, 1)], [(2, 1, 5), (4, 2, 1), (5, 0, 3)], [(6, 5, 5), (12, 8, 3), (14, 9, 4)], [(6, 4, 5), (7, 1, 0), (8, 7, 1)], [(0, 0, 4), (9, 8, 5), (10, 7, 0)], [(8, 5, 1), (10, 6, 0), (11, 9, 5)], [(9, 6, 5), (12, 4, 3), (13, 9, 2)], [(11, 7, 5), (13, 8, 2), (14, 4, 4)]], [4, 2, 5, 5, 1, 3, 5, 0, 1, 5, 0, 5, 3, 2, 4]), ([[(0, 6, 4), (3, 2, 3), (5, 3, 5)], [(1, 2, 5), (2, 3, 2), (7, 5, 0)], [(1, 1, 5), (3, 0, 3), (4, 3, 1)], [(2, 1, 2), (4, 2, 1), (5, 0, 5)], [(6, 5, 5), (12, 8, 4), (14, 9, 2)], [(6, 4, 5), (7, 1, 0), (8, 7, 3)], [(0, 0, 4), (9, 8, 1), (10, 7, 5)], [(8, 5, 3), (10, 6, 5), (11, 9, 0)], [(9, 6, 1), (12, 4, 4), (13, 9, 5)], [(11, 7, 0), (13, 8, 5), (14, 4, 2)]], [4, 5, 2, 3, 1, 5, 5, 0, 3, 1, 5, 0, 4, 5, 2]), ([[(0, 6, 5), (3, 2, 4), (5, 3, 0)], [(1, 2, 1), (2, 3, 2), (7, 5, 5)], [(1, 1, 1), (3, 0, 4), (4, 3, 5)], [(2, 1, 2), (4, 2, 5), (5, 0, 0)], [(6, 5, 4), (12, 8, 5), (14, 9, 0)], [(6, 4, 4), (7, 1, 5), (8, 7, 3)], [(0, 0, 5), (9, 8, 3), (10, 7, 2)], [(8, 5, 3), (10, 6, 2), (11, 9, 5)], [(9, 6, 3), (12, 4, 5), (13, 9, 1)], [(11, 7, 5), (13, 8, 1), (14, 4, 0)]], [5, 1, 2, 4, 5, 0, 4, 5, 3, 3, 2, 5, 5, 1, 0]), ([[(0, 6, 3), (3, 2, 5), (5, 3, 2)], [(1, 2, 1), (2, 3, 5), (7, 5, 0)], [(1, 1, 1), (3, 0, 5), (4, 3, 4)], [(2, 1, 5), (4, 2, 4), (5, 0, 2)], [(6, 5, 1), (12, 8, 2), (14, 9, 5)], [(6, 4, 1), (7, 1, 0), (8, 7, 5)], [(0, 0, 3), (9, 8, 5), (10, 7, 4)], [(8, 5, 5), (10, 6, 4), (11, 9, 3)], [(9, 6, 5), (12, 4, 2), (13, 9, 0)], [(11, 7, 3), (13, 8, 0), (14, 4, 5)]], [3, 1, 5, 5, 4, 2, 1, 0, 5, 5, 4, 3, 2, 0, 5])] = true := by
  decide +kernel
theorem sw6_3_0_7_1 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 7) 1 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 7) 1 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [7, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_3_0_8_0 : exCert (4 + 6) (glueEl (repL 3) 4 0 false (repL 8) 0 false) [([[(0, 4, 3), (3, 2, 5), (5, 3, 2)], [(1, 2, 4), (2, 3, 5), (6, 7, 0)], [(1, 1, 4), (3, 0, 5), (4, 3, 1)], [(2, 1, 5), (4, 2, 1), (5, 0, 2)], [(0, 0, 3), (7, 8, 5), (8, 9, 0)], [(9, 7, 5), (10, 8, 1), (11, 9, 3)], [(12, 7, 2), (13, 8, 4), (14, 9, 5)], [(6, 1, 0), (9, 5, 5), (12, 6, 2)], [(7, 4, 5), (10, 5, 1), (13, 6, 4)], [(8, 4, 0), (11, 5, 3), (14, 6, 5)]], [3, 4, 5, 5, 1, 2, 0, 5, 0, 5, 1, 3, 2, 4, 5]), ([[(0, 4, 3), (3, 2, 4), (5, 3, 5)], [(1, 2, 5), (2, 3, 2), (6, 7, 0)], [(1, 1, 5), (3, 0, 4), (4, 3, 1)], [(2, 1, 2), (4, 2, 1), (5, 0, 5)], [(0, 0, 3), (7, 8, 1), (8, 9, 5)], [(9, 7, 3), (10, 8, 5), (11, 9, 0)], [(12, 7, 5), (13, 8, 2), (14, 9, 4)], [(6, 1, 0), (9, 5, 3), (12, 6, 5)], [(7, 4, 1), (10, 5, 5), (13, 6, 2)], [(8, 4, 5), (11, 5, 0), (14, 6, 4)]], [3, 5, 2, 4, 1, 5, 0, 1, 5, 3, 5, 0, 5, 2, 4]), ([[(0, 4, 5), (3, 2, 0), (5, 3, 3)], [(1, 2, 2), (2, 3, 4), (6, 7, 5)], [(1, 1, 2), (3, 0, 0), (4, 3, 5)], [(2, 1, 4), (4, 2, 5), (5, 0, 3)], [(0, 0, 5), (7, 8, 4), (8, 9, 1)], [(9, 7, 3), (10, 8, 2), (11, 9, 5)], [(12, 7, 1), (13, 8, 5), (14, 9, 0)], [(6, 1, 5), (9, 5, 3), (12, 6, 1)], [(7, 4, 4), (10, 5, 2), (13, 6, 5)], [(8, 4, 1), (11, 5, 5), (14, 6, 0)]], [5, 2, 4, 0, 5, 3, 5, 4, 1, 3, 2, 5, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_3_0_8_0 : isoChk (ofList (4 + 6) (glueEl (repL 3) 4 0 true (repL 8) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 3) 4 0 false (repL 8) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [6, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_4_0 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 4) 0 false) [([[(0, 1, 5), (1, 1, 0), (2, 4, 1)], [(0, 0, 5), (1, 0, 0), (5, 3, 2)], [(3, 3, 5), (4, 3, 1), (6, 5, 0)], [(3, 2, 5), (4, 2, 1), (5, 1, 2)], [(2, 0, 1), (7, 5, 5), (11, 8, 2)], [(6, 2, 0), (7, 4, 5), (10, 7, 3)], [(8, 7, 5), (9, 7, 1), (14, 9, 0)], [(8, 6, 5), (9, 6, 1), (10, 5, 3)], [(11, 4, 2), (12, 9, 5), (13, 9, 1)], [(12, 8, 5), (13, 8, 1), (14, 6, 0)]], [5, 0, 1, 5, 1, 2, 0, 5, 5, 1, 3, 2, 5, 1, 0]), ([[(0, 1, 1), (1, 1, 5), (2, 4, 3)], [(0, 0, 1), (1, 0, 5), (5, 3, 4)], [(3, 3, 3), (4, 3, 5), (6, 5, 0)], [(3, 2, 3), (4, 2, 5), (5, 1, 4)], [(2, 0, 3), (7, 5, 1), (11, 8, 5)], [(6, 2, 0), (7, 4, 1), (10, 7, 5)], [(8, 7, 4), (9, 7, 3), (14, 9, 5)], [(8, 6, 4), (9, 6, 3), (10, 5, 5)], [(11, 4, 5), (12, 9, 2), (13, 9, 0)], [(12, 8, 2), (13, 8, 0), (14, 6, 5)]], [1, 5, 3, 3, 5, 4, 0, 1, 4, 3, 5, 5, 2, 0, 5]), ([[(0, 1, 4), (1, 1, 1), (2, 4, 5)], [(0, 0, 4), (1, 0, 1), (5, 3, 5)], [(3, 3, 3), (4, 3, 2), (6, 5, 5)], [(3, 2, 3), (4, 2, 2), (5, 1, 5)], [(2, 0, 5), (7, 5, 0), (11, 8, 2)], [(6, 2, 5), (7, 4, 0), (10, 7, 1)], [(8, 7, 2), (9, 7, 5), (14, 9, 0)], [(8, 6, 2), (9, 6, 5), (10, 5, 1)], [(11, 4, 2), (12, 9, 1), (13, 9, 5)], [(12, 8, 1), (13, 8, 5), (14, 6, 0)]], [4, 1, 5, 3, 2, 5, 5, 0, 2, 5, 1, 2, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_2_2_4_0 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 4) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 4) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 6, 3, 4, 5, 2, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_4_4 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 4) 4 false) [([[(0, 1, 5), (1, 1, 2), (2, 7, 0)], [(0, 0, 5), (1, 0, 2), (5, 3, 1)], [(3, 3, 5), (4, 3, 2), (10, 5, 0)], [(3, 2, 5), (4, 2, 2), (5, 1, 1)], [(6, 5, 5), (7, 5, 1), (11, 8, 2)], [(6, 4, 5), (7, 4, 1), (10, 2, 0)], [(8, 7, 5), (9, 7, 2), (14, 9, 1)], [(2, 0, 0), (8, 6, 5), (9, 6, 2)], [(11, 4, 2), (12, 9, 5), (13, 9, 0)], [(12, 8, 5), (13, 8, 0), (14, 6, 1)]], [5, 2, 0, 5, 2, 1, 5, 1, 5, 2, 0, 2, 5, 0, 1]), ([[(0, 1, 2), (1, 1, 5), (2, 7, 0)], [(0, 0, 2), (1, 0, 5), (5, 3, 1)], [(3, 3, 2), (4, 3, 5), (10, 5, 0)], [(3, 2, 2), (4, 2, 5), (5, 1, 1)], [(6, 5, 1), (7, 5, 5), (11, 8, 2)], [(6, 4, 1), (7, 4, 5), (10, 2, 0)], [(8, 7, 2), (9, 7, 5), (14, 9, 1)], [(2, 0, 0), (8, 6, 2), (9, 6, 5)], [(11, 4, 2), (12, 9, 0), (13, 9, 5)], [(12, 8, 0), (13, 8, 5), (14, 6, 1)]], [2, 5, 0, 2, 5, 1, 1, 5, 2, 5, 0, 2, 0, 5, 1]), ([[(0, 1, 1), (1, 1, 4), (2, 7, 5)], [(0, 0, 1), (1, 0, 4), (5, 3, 5)], [(3, 3, 0), (4, 3, 3), (10, 5, 5)], [(3, 2, 0), (4, 2, 3), (5, 1, 5)], [(6, 5, 4), (7, 5, 2), (11, 8, 5)], [(6, 4, 4), (7, 4, 2), (10, 2, 5)], [(8, 7, 3), (9, 7, 2), (14, 9, 5)], [(2, 0, 5), (8, 6, 3), (9, 6, 2)], [(11, 4, 5), (12, 9, 1), (13, 9, 0)], [(12, 8, 1), (13, 8, 0), (14, 6, 5)]], [1, 4, 5, 0, 3, 5, 4, 2, 3, 2, 5, 5, 1, 0, 5])] = true := by
  decide +kernel
theorem sw6_2_2_4_4 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 4) 4 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 4) 4 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 10, 3, 4, 5, 6, 7, 8, 9, 2, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_6_0 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 0 false) [([[(0, 1, 5), (1, 1, 2), (2, 6, 0)], [(0, 0, 5), (1, 0, 2), (5, 3, 1)], [(3, 3, 5), (4, 3, 2), (6, 5, 0)], [(3, 2, 5), (4, 2, 2), (5, 1, 1)], [(8, 6, 5), (10, 7, 3), (11, 8, 2)], [(6, 2, 0), (7, 7, 5), (14, 9, 1)], [(2, 0, 0), (8, 4, 5), (9, 7, 4)], [(7, 5, 5), (9, 6, 4), (10, 4, 3)], [(11, 4, 2), (12, 9, 5), (13, 9, 0)], [(12, 8, 5), (13, 8, 0), (14, 5, 1)]], [5, 2, 0, 5, 2, 1, 0, 5, 5, 4, 3, 2, 5, 0, 1]), ([[(0, 1, 0), (1, 1, 5), (2, 6, 4)], [(0, 0, 0), (1, 0, 5), (5, 3, 2)], [(3, 3, 1), (4, 3, 5), (6, 5, 0)], [(3, 2, 1), (4, 2, 5), (5, 1, 2)], [(8, 6, 1), (10, 7, 0), (11, 8, 5)], [(6, 2, 0), (7, 7, 3), (14, 9, 5)], [(2, 0, 4), (8, 4, 1), (9, 7, 5)], [(7, 5, 3), (9, 6, 5), (10, 4, 0)], [(11, 4, 5), (12, 9, 2), (13, 9, 4)], [(12, 8, 2), (13, 8, 4), (14, 5, 5)]], [0, 5, 4, 1, 5, 2, 0, 3, 1, 5, 0, 5, 2, 4, 5]), ([[(0, 1, 4), (1, 1, 3), (2, 6, 5)], [(0, 0, 4), (1, 0, 3), (5, 3, 5)], [(3, 3, 2), (4, 3, 1), (6, 5, 5)], [(3, 2, 2), (4, 2, 1), (5, 1, 5)], [(8, 6, 1), (10, 7, 5), (11, 8, 2)], [(6, 2, 5), (7, 7, 3), (14, 9, 0)], [(2, 0, 5), (8, 4, 1), (9, 7, 0)], [(7, 5, 3), (9, 6, 0), (10, 4, 5)], [(11, 4, 2), (12, 9, 1), (13, 9, 5)], [(12, 8, 1), (13, 8, 5), (14, 5, 0)]], [4, 3, 5, 2, 1, 5, 5, 3, 1, 0, 5, 2, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_2_2_6_0 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 6) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 6, 3, 4, 5, 2, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_6_3 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 3 false) [([[(0, 1, 5), (1, 1, 2), (2, 6, 0)], [(0, 0, 5), (1, 0, 2), (5, 3, 1)], [(3, 3, 5), (4, 3, 2), (9, 7, 0)], [(3, 2, 5), (4, 2, 2), (5, 1, 1)], [(8, 6, 5), (10, 7, 3), (11, 8, 2)], [(6, 6, 4), (7, 7, 5), (14, 9, 1)], [(2, 0, 0), (6, 5, 4), (8, 4, 5)], [(7, 5, 5), (9, 2, 0), (10, 4, 3)], [(11, 4, 2), (12, 9, 5), (13, 9, 0)], [(12, 8, 5), (13, 8, 0), (14, 5, 1)]], [5, 2, 0, 5, 2, 1, 4, 5, 5, 0, 3, 2, 5, 0, 1]), ([[(0, 1, 2), (1, 1, 5), (2, 6, 0)], [(0, 0, 2), (1, 0, 5), (5, 3, 1)], [(3, 3, 2), (4, 3, 5), (9, 7, 0)], [(3, 2, 2), (4, 2, 5), (5, 1, 1)], [(8, 6, 3), (10, 7, 5), (11, 8, 2)], [(6, 6, 5), (7, 7, 4), (14, 9, 1)], [(2, 0, 0), (6, 5, 5), (8, 4, 3)], [(7, 5, 4), (9, 2, 0), (10, 4, 5)], [(11, 4, 2), (12, 9, 0), (13, 9, 5)], [(12, 8, 0), (13, 8, 5), (14, 5, 1)]], [2, 5, 0, 2, 5, 1, 5, 4, 3, 0, 5, 2, 0, 5, 1]), ([[(0, 1, 1), (1, 1, 2), (2, 6, 5)], [(0, 0, 1), (1, 0, 2), (5, 3, 5)], [(3, 3, 4), (4, 3, 0), (9, 7, 5)], [(3, 2, 4), (4, 2, 0), (5, 1, 5)], [(8, 6, 3), (10, 7, 2), (11, 8, 5)], [(6, 6, 4), (7, 7, 3), (14, 9, 5)], [(2, 0, 5), (6, 5, 4), (8, 4, 3)], [(7, 5, 3), (9, 2, 5), (10, 4, 2)], [(11, 4, 5), (12, 9, 1), (13, 9, 0)], [(12, 8, 1), (13, 8, 0), (14, 5, 5)]], [1, 2, 5, 4, 0, 5, 4, 3, 3, 5, 2, 5, 1, 0, 5])] = true := by
  decide +kernel
theorem sw6_2_2_6_3 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 6) 3 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 3 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 9, 3, 4, 5, 6, 7, 8, 2, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_6_5 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 5 false) [([[(0, 1, 5), (1, 1, 2), (2, 4, 0)], [(0, 0, 5), (1, 0, 2), (5, 3, 1)], [(3, 3, 5), (4, 3, 2), (11, 8, 0)], [(3, 2, 5), (4, 2, 2), (5, 1, 1)], [(2, 0, 0), (8, 6, 5), (10, 7, 2)], [(6, 6, 4), (7, 7, 5), (14, 9, 1)], [(6, 5, 4), (8, 4, 5), (9, 7, 3)], [(7, 5, 5), (9, 6, 3), (10, 4, 2)], [(11, 2, 0), (12, 9, 5), (13, 9, 2)], [(12, 8, 5), (13, 8, 2), (14, 5, 1)]], [5, 2, 0, 5, 2, 1, 4, 5, 5, 3, 2, 0, 5, 2, 1]), ([[(0, 1, 2), (1, 1, 5), (2, 4, 0)], [(0, 0, 2), (1, 0, 5), (5, 3, 1)], [(3, 3, 2), (4, 3, 5), (11, 8, 0)], [(3, 2, 2), (4, 2, 5), (5, 1, 1)], [(2, 0, 0), (8, 6, 3), (10, 7, 5)], [(6, 6, 5), (7, 7, 4), (14, 9, 1)], [(6, 5, 5), (8, 4, 3), (9, 7, 2)], [(7, 5, 4), (9, 6, 2), (10, 4, 5)], [(11, 2, 0), (12, 9, 2), (13, 9, 5)], [(12, 8, 2), (13, 8, 5), (14, 5, 1)]], [2, 5, 0, 2, 5, 1, 5, 4, 3, 2, 5, 0, 2, 5, 1]), ([[(0, 1, 1), (1, 1, 4), (2, 4, 5)], [(0, 0, 1), (1, 0, 4), (5, 3, 5)], [(3, 3, 2), (4, 3, 3), (11, 8, 5)], [(3, 2, 2), (4, 2, 3), (5, 1, 5)], [(2, 0, 5), (8, 6, 3), (10, 7, 0)], [(6, 6, 2), (7, 7, 4), (14, 9, 5)], [(6, 5, 2), (8, 4, 3), (9, 7, 5)], [(7, 5, 4), (9, 6, 5), (10, 4, 0)], [(11, 2, 5), (12, 9, 1), (13, 9, 0)], [(12, 8, 1), (13, 8, 0), (14, 5, 5)]], [1, 4, 5, 2, 3, 5, 2, 4, 3, 5, 0, 5, 1, 0, 5])] = true := by
  decide +kernel
theorem sw6_2_2_6_5 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 6) 5 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 5 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 11, 3, 4, 5, 6, 7, 8, 9, 10, 2, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_6_6 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 6 false) [([[(0, 1, 5), (1, 1, 0), (2, 8, 1)], [(0, 0, 5), (1, 0, 0), (5, 3, 2)], [(3, 3, 5), (4, 3, 1), (12, 9, 0)], [(3, 2, 5), (4, 2, 1), (5, 1, 2)], [(8, 6, 5), (10, 7, 0), (11, 8, 3)], [(6, 6, 4), (7, 7, 5), (14, 9, 2)], [(6, 5, 4), (8, 4, 5), (9, 7, 1)], [(7, 5, 5), (9, 6, 1), (10, 4, 0)], [(2, 0, 1), (11, 4, 3), (13, 9, 5)], [(12, 2, 0), (13, 8, 5), (14, 5, 2)]], [5, 0, 1, 5, 1, 2, 4, 5, 5, 1, 0, 3, 0, 5, 2]), ([[(0, 1, 4), (1, 1, 5), (2, 8, 1)], [(0, 0, 4), (1, 0, 5), (5, 3, 2)], [(3, 3, 3), (4, 3, 5), (12, 9, 0)], [(3, 2, 3), (4, 2, 5), (5, 1, 2)], [(8, 6, 0), (10, 7, 4), (11, 8, 5)], [(6, 6, 3), (7, 7, 1), (14, 9, 5)], [(6, 5, 3), (8, 4, 0), (9, 7, 5)], [(7, 5, 1), (9, 6, 5), (10, 4, 4)], [(2, 0, 1), (11, 4, 5), (13, 9, 2)], [(12, 2, 0), (13, 8, 2), (14, 5, 5)]], [4, 5, 1, 3, 5, 2, 3, 1, 0, 5, 4, 5, 0, 2, 5]), ([[(0, 1, 3), (1, 1, 0), (2, 8, 5)], [(0, 0, 3), (1, 0, 0), (5, 3, 5)], [(3, 3, 2), (4, 3, 4), (12, 9, 5)], [(3, 2, 2), (4, 2, 4), (5, 1, 5)], [(8, 6, 2), (10, 7, 5), (11, 8, 4)], [(6, 6, 5), (7, 7, 3), (14, 9, 0)], [(6, 5, 5), (8, 4, 2), (9, 7, 1)], [(7, 5, 3), (9, 6, 1), (10, 4, 5)], [(2, 0, 5), (11, 4, 4), (13, 9, 1)], [(12, 2, 5), (13, 8, 1), (14, 5, 0)]], [3, 0, 5, 2, 4, 5, 5, 3, 2, 1, 5, 4, 5, 1, 0])] = true := by
  decide +kernel
theorem sw6_2_2_6_6 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 6) 6 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 6) 6 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 12, 3, 4, 5, 6, 7, 8, 9, 10, 11, 2, 13, 14] = true := by decide +kernel
theorem t6_2_2_7_0 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 7) 0 false) [([[(0, 1, 5), (1, 1, 0), (2, 4, 3)], [(0, 0, 5), (1, 0, 0), (5, 3, 2)], [(3, 3, 5), (4, 3, 3), (6, 5, 0)], [(3, 2, 5), (4, 2, 3), (5, 1, 2)], [(2, 0, 3), (12, 8, 5), (14, 9, 0)], [(6, 2, 0), (7, 6, 5), (8, 7, 4)], [(7, 5, 5), (9, 8, 1), (10, 7, 3)], [(8, 5, 4), (10, 6, 3), (11, 9, 5)], [(9, 6, 1), (12, 4, 5), (13, 9, 2)], [(11, 7, 5), (13, 8, 2), (14, 4, 0)]], [5, 0, 3, 5, 3, 2, 0, 5, 4, 1, 3, 5, 5, 2, 0]), ([[(0, 1, 0), (1, 1, 5), (2, 4, 1)], [(0, 0, 0), (1, 0, 5), (5, 3, 4)], [(3, 3, 3), (4, 3, 5), (6, 5, 0)], [(3, 2, 3), (4, 2, 5), (5, 1, 4)], [(2, 0, 1), (12, 8, 2), (14, 9, 5)], [(6, 2, 0), (7, 6, 1), (8, 7, 5)], [(7, 5, 1), (9, 8, 5), (10, 7, 4)], [(8, 5, 5), (10, 6, 4), (11, 9, 3)], [(9, 6, 5), (12, 4, 2), (13, 9, 0)], [(11, 7, 3), (13, 8, 0), (14, 4, 5)]], [0, 5, 1, 3, 5, 4, 0, 1, 5, 5, 4, 3, 2, 0, 5]), ([[(0, 1, 3), (1, 1, 4), (2, 4, 5)], [(0, 0, 3), (1, 0, 4), (5, 3, 5)], [(3, 3, 2), (4, 3, 1), (6, 5, 5)], [(3, 2, 2), (4, 2, 1), (5, 1, 5)], [(2, 0, 5), (12, 8, 1), (14, 9, 0)], [(6, 2, 5), (7, 6, 4), (8, 7, 0)], [(7, 5, 4), (9, 8, 3), (10, 7, 5)], [(8, 5, 0), (10, 6, 5), (11, 9, 2)], [(9, 6, 3), (12, 4, 1), (13, 9, 5)], [(11, 7, 2), (13, 8, 5), (14, 4, 0)]], [3, 4, 5, 2, 1, 5, 5, 4, 0, 3, 5, 2, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_2_2_7_0 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 7) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 7) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 6, 3, 4, 5, 2, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_7_1 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 7) 1 false) [([[(0, 1, 5), (1, 1, 1), (2, 6, 4)], [(0, 0, 5), (1, 0, 1), (5, 3, 3)], [(3, 3, 5), (4, 3, 4), (7, 5, 0)], [(3, 2, 5), (4, 2, 4), (5, 1, 3)], [(6, 5, 5), (12, 8, 3), (14, 9, 4)], [(6, 4, 5), (7, 2, 0), (8, 7, 1)], [(2, 0, 4), (9, 8, 5), (10, 7, 0)], [(8, 5, 1), (10, 6, 0), (11, 9, 5)], [(9, 6, 5), (12, 4, 3), (13, 9, 2)], [(11, 7, 5), (13, 8, 2), (14, 4, 4)]], [5, 1, 4, 5, 4, 3, 5, 0, 1, 5, 0, 5, 3, 2, 4]), ([[(0, 1, 0), (1, 1, 5), (2, 6, 4)], [(0, 0, 0), (1, 0, 5), (5, 3, 1)], [(3, 3, 4), (4, 3, 5), (7, 5, 0)], [(3, 2, 4), (4, 2, 5), (5, 1, 1)], [(6, 5, 5), (12, 8, 4), (14, 9, 2)], [(6, 4, 5), (7, 2, 0), (8, 7, 3)], [(2, 0, 4), (9, 8, 1), (10, 7, 5)], [(8, 5, 3), (10, 6, 5), (11, 9, 0)], [(9, 6, 1), (12, 4, 4), (13, 9, 5)], [(11, 7, 0), (13, 8, 5), (14, 4, 2)]], [0, 5, 4, 4, 5, 1, 5, 0, 3, 1, 5, 0, 4, 5, 2]), ([[(0, 1, 1), (1, 1, 4), (2, 6, 5)], [(0, 0, 1), (1, 0, 4), (5, 3, 5)], [(3, 3, 2), (4, 3, 0), (7, 5, 5)], [(3, 2, 2), (4, 2, 0), (5, 1, 5)], [(6, 5, 4), (12, 8, 5), (14, 9, 0)], [(6, 4, 4), (7, 2, 5), (8, 7, 3)], [(2, 0, 5), (9, 8, 3), (10, 7, 2)], [(8, 5, 3), (10, 6, 2), (11, 9, 5)], [(9, 6, 3), (12, 4, 5), (13, 9, 1)], [(11, 7, 5), (13, 8, 1), (14, 4, 0)]], [1, 4, 5, 2, 0, 5, 4, 5, 3, 3, 2, 5, 5, 1, 0]), ([[(0, 1, 5), (1, 1, 1), (2, 6, 3)], [(0, 0, 5), (1, 0, 1), (5, 3, 4)], [(3, 3, 5), (4, 3, 3), (7, 5, 0)], [(3, 2, 5), (4, 2, 3), (5, 1, 4)], [(6, 5, 1), (12, 8, 2), (14, 9, 5)], [(6, 4, 1), (7, 2, 0), (8, 7, 5)], [(2, 0, 3), (9, 8, 5), (10, 7, 4)], [(8, 5, 5), (10, 6, 4), (11, 9, 3)], [(9, 6, 5), (12, 4, 2), (13, 9, 0)], [(11, 7, 3), (13, 8, 0), (14, 4, 5)]], [5, 1, 3, 5, 3, 4, 1, 0, 5, 5, 4, 3, 2, 0, 5])] = true := by
  decide +kernel
theorem sw6_2_2_7_1 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 7) 1 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 7) 1 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 7, 3, 4, 5, 6, 2, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem t6_2_2_8_0 : exCert (4 + 6) (glueEl (repL 2) 4 2 false (repL 8) 0 false) [([[(0, 1, 5), (1, 1, 4), (2, 4, 3)], [(0, 0, 5), (1, 0, 4), (5, 3, 2)], [(3, 3, 5), (4, 3, 3), (6, 7, 0)], [(3, 2, 5), (4, 2, 3), (5, 1, 2)], [(2, 0, 3), (7, 8, 5), (8, 9, 0)], [(9, 7, 5), (10, 8, 1), (11, 9, 3)], [(12, 7, 2), (13, 8, 4), (14, 9, 5)], [(6, 2, 0), (9, 5, 5), (12, 6, 2)], [(7, 4, 5), (10, 5, 1), (13, 6, 4)], [(8, 4, 0), (11, 5, 3), (14, 6, 5)]], [5, 4, 3, 5, 3, 2, 0, 5, 0, 5, 1, 3, 2, 4, 5]), ([[(0, 1, 2), (1, 1, 5), (2, 4, 3)], [(0, 0, 2), (1, 0, 5), (5, 3, 1)], [(3, 3, 4), (4, 3, 5), (6, 7, 0)], [(3, 2, 4), (4, 2, 5), (5, 1, 1)], [(2, 0, 3), (7, 8, 1), (8, 9, 5)], [(9, 7, 3), (10, 8, 5), (11, 9, 0)], [(12, 7, 5), (13, 8, 2), (14, 9, 4)], [(6, 2, 0), (9, 5, 3), (12, 6, 5)], [(7, 4, 1), (10, 5, 5), (13, 6, 2)], [(8, 4, 5), (11, 5, 0), (14, 6, 4)]], [2, 5, 3, 4, 5, 1, 0, 1, 5, 3, 5, 0, 5, 2, 4]), ([[(0, 1, 2), (1, 1, 3), (2, 4, 5)], [(0, 0, 2), (1, 0, 3), (5, 3, 5)], [(3, 3, 0), (4, 3, 4), (6, 7, 5)], [(3, 2, 0), (4, 2, 4), (5, 1, 5)], [(2, 0, 5), (7, 8, 4), (8, 9, 1)], [(9, 7, 3), (10, 8, 2), (11, 9, 5)], [(12, 7, 1), (13, 8, 5), (14, 9, 0)], [(6, 2, 5), (9, 5, 3), (12, 6, 1)], [(7, 4, 4), (10, 5, 2), (13, 6, 5)], [(8, 4, 1), (11, 5, 5), (14, 6, 0)]], [2, 3, 5, 0, 4, 5, 5, 4, 1, 3, 2, 5, 1, 5, 0])] = true := by
  decide +kernel
theorem sw6_2_2_8_0 : isoChk (ofList (4 + 6) (glueEl (repL 2) 4 2 true (repL 8) 0 true) (by decide))
    (ofList (4 + 6) (glueEl (repL 2) 4 2 false (repL 8) 0 false) (by decide)) (by decide) (by decide)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 6, 3, 4, 5, 2, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
def flipV_2 : List Nat := [2, 3, 0, 1]
def flipE_2 : List Nat := [3, 4, 2, 0, 1, 5]
theorem flip_2 : isoChk (repG 2) (repG 2) (repN_pos 2) (repM_pos 2) flipV_2 flipE_2 = true := by decide +kernel
def flipV_3 : List Nat := [1, 0, 2, 3]
def flipE_3 : List Nat := [0, 3, 5, 1, 4, 2]
theorem flip_3 : isoChk (repG 3) (repG 3) (repN_pos 3) (repM_pos 3) flipV_3 flipE_3 = true := by decide +kernel

end RH2F


-- ===== from TA.lean =====

namespace RH2F
open MGraph

section tabc
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the gluing step of (tabc) for given closure isomorphisms onto concrete multigraphs -/
theorem Cut2.tabc_gen (C : Cut2 P) {nA nB : Nat} {elA elB : List (Nat × Nat)} {hnA : 0 < nA} {hnB : 0 < nB}
    (hmA : 0 < elA.length) (helA : elOK nA elA = true) (helB : elOK nB elB = true)
    {αA : Fin X.n → Fin (ofList nA elA hnA).n} {βA : Fin (addEdge X C.a1 C.a2).m → Fin (ofList nA elA hnA).m}
    (hA : IsoMap C.clo (ofList nA elA hnA) αA βA) {ja : Nat} (hja : (βA (Fin.last X.m)).val = ja)
    {αB : Fin X.n → Fin (ofList nB elB hnB).n} {βB : Fin (addEdge X C.b1 C.b2).m → Fin (ofList nB elB hnB).m}
    (hB : IsoMap C.flip.clo (ofList nB elB hnB) αB βB) {jb : Nat} (hjb : (βB (Fin.last X.m)).val = jb)
    {σl τl : List Nat} (hflip : isoChk (ofList nA elA hnA) (ofList nA elA hnA) hnA hmA σl τl = true)
    (hτ : (lget τl elA.length hmA ja).val = ja)
    (hσ1 : (lget σl nA hnA (gE elA ja).1).val = (gE elA ja).2)
    (hσ2 : (lget σl nA hnA (gE elA ja).2).val = (gE elA ja).1)
    {cs : List (List (List (Nat × Nat × Nat)) × List Nat)}
    (hff : exCert (nA + nB) (glueEl elA nA ja false elB jb false) cs = true)
    {st tt : List Nat} {h1 : 0 < nA + nB} {h2 : 0 < (glueEl elA nA ja false elB jb false).length}
    (htt : isoChk (ofList (nA + nB) (glueEl elA nA ja true elB jb true) h1)
      (ofList (nA + nB) (glueEl elA nA ja false elB jb false) h1) h1 h2 st tt = true) :
    EX1On P := by
  have hFF : EX1FullH (ofList (nA + nB) (glueEl elA nA ja false elB jb false) h1) := ex1Full_of_cert hff
  have hTT := concMap_of_chk htt
  -- the glued isomorphism for equal orientations
  have main : ∀ {αA' : Fin X.n → Fin (ofList nA elA hnA).n} {βA' : Fin (addEdge X C.a1 C.a2).m → Fin (ofList nA elA hnA).m},
      IsoMap C.clo (ofList nA elA hnA) αA' βA' → (βA' (Fin.last X.m)).val = ja → ∀ o : Bool,
      (if o then (gE elA ja).2 else (gE elA ja).1) = (αA' C.a1).val →
      (if o then (gE elA ja).1 else (gE elA ja).2) = (αA' C.a2).val →
      (if o then (gE elB jb).2 else (gE elB jb).1) = (αB C.b1).val →
      (if o then (gE elB jb).1 else (gE elB jb).2) = (αB C.b2).val → EX1On P := by
    intro αA' βA' hA' hja' o ho1 ho2 ho3 ho4
    rw [← hja'] at ho1 ho2
    rw [← hjb] at ho3 ho4
    have hg0 := C.glue_iso (hnA := hnA) (hnB := hnB) helA helB hA' o ho1 ho2 hB o ho3 ho4
    rw [hja', hjb] at hg0
    obtain ⟨a, b, hg⟩ := hg0
    cases o
    · exact ex1On_of_iso ⟨a, b, hg⟩ hFF
    · exact ex1On_of_iso ⟨_, _, isoMap_comp hg hTT⟩ hFF
  obtain ⟨oA, hoA1, hoA2⟩ := C.orient helA hA
  obtain ⟨oB, hoB1, hoB2⟩ := C.flip.orient helB hB
  rw [hja] at hoA1 hoA2
  rw [hjb] at hoB1 hoB2
  by_cases hoo : oA = oB
  · subst hoo
    exact main hA hja oA hoA1 hoA2 hoB1 hoB2
  · -- flip side `A`
    have hF := concMap_of_chk hflip
    have hA' := isoMap_comp hA hF
    have hja' : (lget τl elA.length hmA (βA (Fin.last X.m)).val).val = ja := by rw [hja]; exact hτ
    have hoB : oB = !oA := by cases oA <;> cases oB <;> simp_all
    subst hoB
    refine main hA' hja' (!oA) ?_ ?_ hoB1 hoB2
    · cases oA <;> simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at hoA1 ⊢
      · show (gE elA ja).2 = (lget σl nA hnA (αA C.a1).val).val
        rw [← hoA1, hσ1]
      · show (gE elA ja).1 = (lget σl nA hnA (αA C.a1).val).val
        rw [← hoA1, hσ2]
    · cases oA <;> simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at hoA2 ⊢
      · show (gE elA ja).1 = (lget σl nA hnA (αA C.a2).val).val
        rw [← hoA2, hσ2]
      · show (gE elA ja).2 = (lget σl nA hnA (αA C.a2).val).val
        rw [← hoA2, hσ1]

/-- **(tabc)**: the 10-vertex gluings of table T6, without the hypothesis `¬ EX1On C.cloD` (it is not used). -/
theorem sfTabc0 : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 4 →
    scount P C.S false = 6 → ¬ EX1On C.flip.clo → ¬ C.RecipeD → EX1On P := by
  intro X P C hG h4 h6 hnB hnD
  obtain ⟨ka, hka1, hka25, hkan, hisoA⟩ := cls 4 _ _ (C.clo_inG hG) (by rw [C.vcount_clo, h4]) (by decide) (by decide)
  have hvB : vcount C.flip.clo = 6 := by rw [C.flip.vcount_clo, scount_flip]; exact h6
  obtain ⟨kb, hkb1, hkb25, hkbn, hisoB⟩ := cls 6 _ _ (C.flip.clo_inG hG) hvB (by decide) (by decide)
  have hTB : ¬ T5 kb := fun hT => hnB (ex1On_of_iso hisoB (ex1Full_rep kb hT))
  obtain ⟨hkb, _⟩ := bad_of kb hkb25 hkb1 hTB
  have kb_cases : kb = 4 ∨ kb = 6 ∨ kb = 7 ∨ kb = 8 := by
    rcases hkb with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · subst h; exact absurd hkbn (by decide)
  obtain ⟨αA, βA, hmA⟩ := hisoA
  obtain ⟨αB, βB, hmB⟩ := hisoB
  rcases k_of_4 ka hka25 hka1 hkan with rfl | rfl
  · obtain ⟨αA', βA', hmA', hjA⟩ := C.aut_iso 2 autChk_2 hmA
    rcases autR_2 (βA (Fin.last X.m)) with h | h <;> rw [h] at hjA
    · exact absurd (C.recipeD_of_iso (repL_ok 2 (by decide)) hmA' hjA recD_2_0_0 recD_2_0_1) hnD
    rcases kb_cases with rfl | rfl | rfl | rfl
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 4 autChk_4 hmB
      rcases autR_4 (βB (Fin.last X.m)) with h | h <;> rw [h] at hjB
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 4 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_4_0 sw6_2_2_4_0
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 4 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_4_4 sw6_2_2_4_4
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 6 autChk_6 hmB
      rcases autR_6 (βB (Fin.last X.m)) with h | h | h | h <;> rw [h] at hjB
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_6_0 sw6_2_2_6_0
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_6_3 sw6_2_2_6_3
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_6_5 sw6_2_2_6_5
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_6_6 sw6_2_2_6_6
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 7 autChk_7 hmB
      rcases autR_7 (βB (Fin.last X.m)) with h | h <;> rw [h] at hjB
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 7 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_7_0 sw6_2_2_7_0
      · exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 7 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_7_1 sw6_2_2_7_1
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 8 autChk_8 hmB
      rw [autR_8 (βB (Fin.last X.m))] at hjB
      exact C.tabc_gen (hmA := repM_pos 2) (repL_ok 2 (by decide)) (repL_ok 8 (by decide)) hmA' hjA hmB' hjB flip_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_2_2_8_0 sw6_2_2_8_0
  · obtain ⟨αA', βA', hmA', hjA⟩ := C.aut_iso 3 autChk_3 hmA
    rw [autR_3 (βA (Fin.last X.m))] at hjA
    rcases kb_cases with rfl | rfl | rfl | rfl
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 4 autChk_4 hmB
      rcases autR_4 (βB (Fin.last X.m)) with h | h <;> rw [h] at hjB
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 4 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_4_0 sw6_3_0_4_0
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 4 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_4_4 sw6_3_0_4_4
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 6 autChk_6 hmB
      rcases autR_6 (βB (Fin.last X.m)) with h | h | h | h <;> rw [h] at hjB
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_6_0 sw6_3_0_6_0
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_6_3 sw6_3_0_6_3
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_6_5 sw6_3_0_6_5
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 6 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_6_6 sw6_3_0_6_6
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 7 autChk_7 hmB
      rcases autR_7 (βB (Fin.last X.m)) with h | h <;> rw [h] at hjB
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 7 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_7_0 sw6_3_0_7_0
      · exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 7 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_7_1 sw6_3_0_7_1
    · obtain ⟨αB', βB', hmB', hjB⟩ := C.flip.aut_iso 8 autChk_8 hmB
      rw [autR_8 (βB (Fin.last X.m))] at hjB
      exact C.tabc_gen (hmA := repM_pos 3) (repL_ok 3 (by decide)) (repL_ok 8 (by decide)) hmA' hjA hmB' hjB flip_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) t6_3_0_8_0 sw6_3_0_8_0

/-- (tabc) of SmallFacts (fact 341b6e5e1be16205), from `sfTabc0`. -/
theorem sfTabc : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 4 →
    scount P C.S false = 6 → ¬ EX1On C.flip.clo → ¬ EX1On C.cloD → ¬ C.RecipeD → EX1On P :=
  fun X P C hG h4 h6 hnB _ hnD => sfTabc0 X P C hG h4 h6 hnB hnD

/-- A 4-vertex side against a 6-vertex side whose closure is not EX1-good: the whole graph is EX1-good.
    With recipe D on side A this is Lemma SR (a) (fact 657e581f1145250f) with (s2) on side B; otherwise `sfTabc0`. -/
theorem tabc46 : ∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 4 →
    scount P C.S false = 6 → ¬ EX1On C.flip.clo → EX1On P := by
  intro X P C hG h4 h6 hnB
  by_cases hD : C.RecipeD
  · exact C.sr_a RH2P.pstat hG hD (sfS2 X P C.flip hG (by rw [scount_flip]; exact h6))
  · exact sfTabc0 X P C hG h4 h6 hnB hD

/-- **the small-side facts of EX1-RED** -/
theorem smallFacts : SmallFacts := ⟨sfS2, sfS3, sfS4, sfS5, sfTabc⟩

/-- **Theorem RH2** (fact 6bfcd4d52c94468a) in Lean: (H) and (II) imply DMS -/
theorem rh2_final : Hyp → II → DMS := fun hH hII => RH2P.rh2_P smallFacts b8s hH hII

end tabc

end RH2F

namespace RH2F
open MGraph

/-- **Layer 9 of the Lean formalization of RH2**: the gluings (tabc) of table T6 (TAB-C) (in a strengthened form:
    a 4-vertex side against a 6-vertex side with non-EX1-good closure), hence all small-side facts of EX1-RED, and **Theorem RH2** (fact 6bfcd4d52c94468a): (H) and (II) imply DMS. -/
theorem layer9 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → scount P C.S true = 4 →
      scount P C.S false = 6 → ¬ EX1On C.flip.clo → EX1On P) ∧
    SmallFacts ∧ (Hyp → II → DMS) :=
  ⟨tabc46, smallFacts, rh2_final⟩

end RH2F
