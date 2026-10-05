-- Lean proof of fact a030b9ec722eb795 (RH2F.layer11); added by fact_submit, do not edit
import MhFact_75fc19c47ee38b89
set_option backward.isDefEq.respectTransparency false

-- ===== from II3.lean =====
/-
  II3.lean — Lemma SMALL-2SIDED (fact 5c988cebcde7d49b) and the small leaf graphs of Theorem II-RED2 (fact
  52408ddd08d61ae6, Step 2): transport of certificates from the representatives Rep_k (fact be9b0c62ac86fc55) along
  the isomorphisms of the classification (fact 6e44d3c2232b5736), and sound Bool checkers for the certificates.
-/

namespace RH2F
open MGraph
open Classical

section ii3
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the colours of the edges other than `j` at `x` -/
def Zc {H : MGraph} (cr : Fin H.m → Fin 6) (j : Fin H.m) (x : Fin H.n) (κ : Fin 6) : Prop :=
  ∃ h, h ≠ j ∧ H.Inc h x ∧ cr h = κ

/-- `H` has a star 6-colouring whose colour sets at the two ends of `j` (without `j`) share exactly one colour
    (`s(j) = 1`): they meet and are different -/
def Good1 (H : MGraph) (j : Fin H.m) : Prop :=
  ∃ cr : Fin H.m → Fin 6, StarOn (fun _ => True) 6 cr ∧
    (∃ κ, Zc cr j (H.ends j).1 κ ∧ Zc cr j (H.ends j).2 κ) ∧
    ¬ ∀ κ, (Zc cr j (H.ends j).1 κ ↔ Zc cr j (H.ends j).2 κ)

/-- **SMALL-2SIDED, transport**: if the closure `G_A` is isomorphic to `H` and every edge of `H` is good, then
    `G_A` is 2-sided at `g_A` -/
theorem Cut2.twoSided_of_good (C : Cut2 P) {H : MGraph} (hiso : IsoFrom C.clo H) (hg : ∀ j, Good1 H j) :
    C.TwoSided := by
  obtain ⟨α, β, hα, hβ, hsurj, hj⟩ := hiso
  have hlast : C.clo (Fin.last X.m) := Or.inl rfl
  obtain ⟨cr, hcr, hmeet, hsmall⟩ := hg (β (Fin.last X.m))
  let c : Fin (addEdge X C.a1 C.a2).m → Fin 6 := fun i => cr (β i)
  have hc : StarOn C.clo 6 c := starOn_of_iso hα hβ hj hcr
  let φ : Fin X.m → Fin 6 := fun f => c (C.toClo f)
  have mv : ∀ v, (v = C.a1 ∨ v = C.a2) → meets C.clo v := by
    rintro v (rfl | rfl)
    · exact ⟨Fin.last X.m, hlast, (C.inc_new_iff).2 (Or.inl rfl)⟩
    · exact ⟨Fin.last X.m, hlast, (C.inc_new_iff).2 (Or.inr rfl)⟩
  have key : ∀ v, (v = C.a1 ∨ v = C.a2) → ∀ κ, C.Pset φ v κ ↔ Zc cr (β (Fin.last X.m)) (α v) κ := by
    intro v hv κ
    constructor
    · rintro ⟨f, hf, hfv, hκ⟩
      have hfc : C.clo (Fin.castSucc f) := Or.inr ⟨f, rfl, hf⟩
      refine ⟨β (Fin.castSucc f), fun h => Fin.castSucc_ne_last f (hβ _ _ hfc hlast h), ?_, ?_⟩
      · have hjf := hj _ hfc
        rw [addEdge_ends_old] at hjf
        exact inc_map hjf hfv
      · have : C.toClo f = Fin.castSucc f := C.toClo_old (fun h => C.not_inA_of_cut h hf)
        show c (Fin.castSucc f) = κ
        rw [← this]; exact hκ
    · rintro ⟨h, hne, hinc, hκ⟩
      obtain ⟨i, hi, rfl⟩ := hsurj h
      rcases hi with rfl | ⟨d, rfl, hd⟩
      · exact absurd rfl hne
      · refine ⟨d, hd, ?_, ?_⟩
        · have hjd := hj _ (Or.inr ⟨d, rfl, hd⟩)
          rw [addEdge_ends_old] at hjd
          have hm : ∀ w, X.Inc d w → meets C.clo w := fun w hw =>
            ⟨Fin.castSucc d, Or.inr ⟨d, rfl, hd⟩, addEdge_inc_old.2 hw⟩
          rcases inc_of_joins hjd hinc with h' | h'
          · rw [hα _ _ (mv v hv) (hm _ (Or.inl rfl)) h']; exact Or.inl rfl
          · rw [hα _ _ (mv v hv) (hm _ (Or.inr rfl)) h']; exact Or.inr rfl
        · have : C.toClo d = Fin.castSucc d := C.toClo_old (fun h => C.not_inA_of_cut h hd)
          show c (C.toClo d) = κ
          rw [this]; exact hκ
  -- the ends of `β g_A` are `α a1`, `α a2`
  have hjl := hj _ hlast
  rw [addEdge_ends_new] at hjl
  have sym : ∀ (A B : Fin 6 → Prop), (A = Zc cr (β (Fin.last X.m)) (α C.a1) ∧ B = Zc cr (β (Fin.last X.m)) (α C.a2)) →
      ((∃ κ, A κ ∧ B κ) ∧ ¬ ∀ κ, (A κ ↔ B κ)) := by
    rintro A B ⟨rfl, rfl⟩
    rcases hjl with h | h <;> rw [h] at hmeet hsmall
    · exact ⟨hmeet, hsmall⟩
    · obtain ⟨κ, h1, h2⟩ := hmeet
      exact ⟨⟨κ, h2, h1⟩, fun h' => hsmall fun κ => (h' κ).symm⟩
  obtain ⟨hM, hS⟩ := sym _ _ ⟨rfl, rfl⟩
  have hφ : StarOn C.pole 6 φ := C.pole_of_clo c hc
  have hφe : φ C.e1 = φ C.e2 := C.pole_eq_of_clo c
  refine ⟨⟨φ, hφ, hφe, fun h => hS fun κ => ?_⟩, ⟨φ, hφ, hφe, ?_⟩⟩
  · rw [← key C.a1 (Or.inl rfl), ← key C.a2 (Or.inr rfl)]; exact h κ
  · obtain ⟨κ, h1, h2⟩ := hM
    exact ⟨κ, (key C.a1 (Or.inl rfl) κ).2 h1, (key C.a2 (Or.inr rfl) κ).2 h2⟩


/-! ### the Bool checker for `Good1` on explicit multigraphs -/

/-- the colours of the edges other than `j` at `x`, from an edge list -/
def zlist (el : List (Nat × Nat)) (cl : List Nat) (j x : Nat) : List Nat :=
  ((List.range el.length).filter
    (fun e => !Nat.beq e j && (Nat.beq (gE el e).1 x || Nat.beq (gE el e).2 x))).map (colN cl)

/-- `s(j) = 1`: the two colour lists meet and are different as sets -/
def s1Chk (el : List (Nat × Nat)) (cl : List Nat) (j : Nat) : Bool :=
  (zlist el cl j (gE el j).1).any (fun κ => (zlist el cl j (gE el j).2).contains κ) &&
  ((zlist el cl j (gE el j).1).any (fun κ => !(zlist el cl j (gE el j).2).contains κ) ||
   (zlist el cl j (gE el j).2).any (fun κ => !(zlist el cl j (gE el j).1).contains κ))

/-- every certificate colouring is star, and every edge has a certificate with `s = 1` -/
def s1Cert (n : Nat) (el : List (Nat × Nat)) (cs : List (List (List (Nat × Nat × Nat)) × List Nat)) : Bool :=
  cs.all (fun p => fastStar2 n el p.1 p.2) && (List.range el.length).all (fun j => cs.any (fun p => s1Chk el p.2 j))

section chk
variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

theorem mem_zlist (hel : elOK n el = true) (cl : List Nat) (j : Fin (ofList n el hn).m) (x : Fin n) (k : Nat) :
    k ∈ zlist el cl j.val x.val ↔
      ∃ h : Fin (ofList n el hn).m, h ≠ j ∧ (ofList n el hn).Inc h x ∧ colN cl h.val = k := by
  unfold zlist
  simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true]
  constructor
  · rintro ⟨e, ⟨he, hne, hinc⟩, rfl⟩
    have hends := ofList_ends (hn := hn) hel ⟨e, he⟩
    refine ⟨⟨e, he⟩, fun h => ?_, ?_, rfl⟩
    · have hv : e = j.val := congrArg Fin.val h
      rw [hv, nbeq_true rfl] at hne; exact absurd hne (by decide)
    · rcases hinc with h | h
      · left; apply Fin.ext; rw [hends.1]; exact Nat.eq_of_beq_eq_true h
      · right; apply Fin.ext; rw [hends.2]; exact Nat.eq_of_beq_eq_true h
  · rintro ⟨h, hne, hinc, rfl⟩
    have hends := ofList_ends (hn := hn) hel h
    refine ⟨h.val, ⟨h.isLt, nbeq_false (fun e => hne (Fin.ext e)), ?_⟩, rfl⟩
    rcases hinc with hh | hh
    · left; rw [← hends.1, hh]; exact nbeq_true rfl
    · right; rw [← hends.2, hh]; exact nbeq_true rfl

theorem zlist_lt {cl : List Nat} {j x k : Nat} (h : k ∈ zlist el cl j x) : k < 6 := by
  unfold zlist at h
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 h
  exact Nat.mod_lt _ (by decide)

theorem zc_iff (hel : elOK n el = true) (cl : List Nat) (j : Fin (ofList n el hn).m) (x : Fin n) (κ : Fin 6) :
    Zc (colF (ofList n el hn).m cl) j x κ ↔ κ.val ∈ zlist el cl j.val x.val := by
  rw [mem_zlist hel]
  constructor
  · rintro ⟨h, hne, hinc, hκ⟩; exact ⟨h, hne, hinc, by rw [← hκ]; rfl⟩
  · rintro ⟨h, hne, hinc, hk⟩; exact ⟨h, hne, hinc, Fin.ext hk⟩

theorem good1_of_chk (hel : elOK n el = true) {cl : List Nat}
    (hst : StarOn (fun _ => True) 6 (colF (ofList n el hn).m cl)) (j : Fin (ofList n el hn).m)
    (hchk : s1Chk el cl j.val = true) : Good1 (ofList n el hn) j := by
  have hends := ofList_ends (hn := hn) hel j
  have z1 : ∀ κ : Fin 6, Zc (colF (ofList n el hn).m cl) j ((ofList n el hn).ends j).1 κ ↔
      κ.val ∈ zlist el cl j.val (gE el j.val).1 := fun κ => by rw [zc_iff hel, hends.1]
  have z2 : ∀ κ : Fin 6, Zc (colF (ofList n el hn).m cl) j ((ofList n el hn).ends j).2 κ ↔
      κ.val ∈ zlist el cl j.val (gE el j.val).2 := fun κ => by rw [zc_iff hel, hends.2]
  unfold s1Chk at hchk
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem, Bool.not_eq_true',
    ] at hchk
  obtain ⟨⟨k, hk1, hk2⟩, hsm⟩ := hchk
  refine ⟨colF _ cl, hst, ⟨⟨k, zlist_lt hk1⟩, (z1 _).2 hk1, (z2 _).2 hk2⟩, fun h => ?_⟩
  rcases hsm with ⟨k', hk1', hk2'⟩ | ⟨k', hk2', hk1'⟩
  · have := (z2 ⟨k', zlist_lt hk1'⟩).1 ((h _).1 ((z1 _).2 hk1'))
    exact absurd this (by simpa using hk2')
  · have := (z1 ⟨k', zlist_lt hk2'⟩).1 ((h _).2 ((z2 _).2 hk2'))
    exact absurd this (by simpa using hk1')

theorem good_of_cert {cs : List (List (List (Nat × Nat × Nat)) × List Nat)} (h : s1Cert n el cs = true) :
    ∀ j : Fin (ofList n el hn).m, Good1 (ofList n el hn) j := by
  intro j
  unfold s1Cert at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨p, hp, hc⟩ := h.2 j.val j.isLt
  have hfs := h.1 p hp
  have hel : elOK n el = true := by
    unfold fastStar2 at hfs; simp only [Bool.and_eq_true] at hfs; exact hfs.1.1.1
  exact good1_of_chk hel (star_of_fast2 hfs) j hc

end chk


/-! ### leaf graphs of explicit multigraphs -/

/-- the edge list of T(ofList n el, j): entry `j` becomes `s x`, then `x t` and `x ℓ` (with `x = n`, `ℓ = n + 1`) -/
def leafEl (n : Nat) (el : List (Nat × Nat)) (j : Nat) : List (Nat × Nat) :=
  el.set j ((gE el j).1, n) ++ [(n, (gE el j).2), (n, n + 1)]

theorem leafEl_length (n : Nat) (el : List (Nat × Nat)) (j : Nat) : (leafEl n el j).length = el.length + 2 := by
  simp [leafEl]

theorem gE_set_app_ne {el : List (Nat × Nat)} {j i : Nat} {v : Nat × Nat} {l : List (Nat × Nat)}
    (hi : i < el.length) (hij : i ≠ j) : gE (el.set j v ++ l) i = gE el i := by
  have h1 : i < (el.set j v).length := by simpa using hi
  simp only [gE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h1, List.getElem?_set_ne (Ne.symm hij)]

theorem gE_set_app_eq {el : List (Nat × Nat)} {j : Nat} {v : Nat × Nat} {l : List (Nat × Nat)}
    (hj : j < el.length) : gE (el.set j v ++ l) j = v := by
  have h1 : j < (el.set j v).length := by simpa using hj
  simp only [gE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h1, List.getElem?_set_self hj]; rfl

theorem gE_leafEl_old {n : Nat} {el : List (Nat × Nat)} {j i : Nat} (hi : i < el.length) (hij : i ≠ j) :
    gE (leafEl n el j) i = gE el i := gE_set_app_ne hi hij

theorem gE_leafEl_j {n : Nat} {el : List (Nat × Nat)} {j : Nat} (hj : j < el.length) :
    gE (leafEl n el j) j = ((gE el j).1, n) := gE_set_app_eq hj

theorem gE_leafEl_m {n : Nat} {el : List (Nat × Nat)} {j : Nat} :
    gE (leafEl n el j) el.length = (n, (gE el j).2) := by
  simp [leafEl, gE, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem gE_leafEl_m1 {n : Nat} {el : List (Nat × Nat)} {j : Nat} :
    gE (leafEl n el j) (el.length + 1) = (n, n + 1) := by
  simp [leafEl, gE, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem joins_vals {H : MGraph} {e : Fin H.m} {p q : Fin H.n} (h1 : (H.ends e).1.val = p.val)
    (h2 : (H.ends e).2.val = q.val) : H.Joins e p q := Or.inl (Prod.ext (Fin.ext h1) (Fin.ext h2))

theorem lv_val {Y : MGraph} (v : Fin Y.n) : (lv v : Fin (Y.n + 2)).val = v.val := by simp [lv]
theorem vx_val (Y : MGraph) : (vx Y).val = Y.n := by simp [vx]
theorem vl_val (Y : MGraph) : (vl Y).val = Y.n + 1 := by simp [vl]

/-- a checked star colouring of `leafEl` gives a star colouring of the leaf graph T(ofList n el, j) -/
theorem leaf_ofList {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    (j : Fin (ofList n el hn).m) {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hfs : fastStar2 (n + 2) (leafEl n el j.val) nb cl = true) :
    Colourable (leafSet (fun _ : Fin (ofList n el hn).m => True) j) 6 := by
  have hn2 : 0 < n + 2 := by omega
  have hel2 : elOK (n + 2) (leafEl n el j.val) = true := by
    unfold fastStar2 at hfs; simp only [Bool.and_eq_true] at hfs; exact hfs.1.1.1
  have hst := star_of_fast2 (hn := hn2) hfs
  have hjm : j.val < el.length := j.isLt
  have hm : (ofList (n + 2) (leafEl n el j.val) hn2).m = el.length + 2 := leafEl_length _ _ _
  let μ : Fin (leafG (ofList n el hn) j).m → Fin (ofList (n + 2) (leafEl n el j.val) hn2).m := fun i =>
    ⟨if i.val < el.length then i.val else if i.val = el.length then j.val else i.val - 1, by
      have hi : i.val < el.length + 3 := i.isLt
      rw [hm]; split_ifs <;> omega⟩
  have hold : ∀ a : Fin (leafG (ofList n el hn) j).m, leafSet (fun _ => True) j a → a.val < el.length →
      a.val ≠ j.val := by
    intro a ha hlt he
    have : leafSet (fun _ : Fin (ofList n el hn).m => True) j (oldE j ⟨a.val, hlt⟩) := by
      have : a = oldE j ⟨a.val, hlt⟩ := Fin.ext rfl
      rw [← this]; exact ha
    exact ((set_old _ j _).1 this).2 (Fin.ext he)
  refine colourable_emb (X := ofList (n + 2) (leafEl n el j.val) hn2) (P := fun _ => True)
    (Y := leafG (ofList n el hn) j) (fun v => v) μ (fun x y _ _ h => h) ?_ (fun _ _ => trivial) ?_ ⟨_, hst⟩
  · intro a b ha hb h
    have hv := congrArg Fin.val h
    simp only [μ] at hv
    have ha3 : a.val < el.length + 3 := a.isLt
    have hb3 : b.val < el.length + 3 := b.isLt
    have oa := hold a ha
    have ob := hold b hb
    apply Fin.ext
    split_ifs at hv <;> omega
  · intro a ha
    have e2 := ofList_ends (hn := hn2) hel2
    rcases leaf_cases j a with ⟨d, rfl⟩ | rfl | rfl | rfl
    · have hdj : d ≠ j := ((set_old _ j d).1 ha).2
      have hdv : d.val ≠ j.val := fun h => hdj (Fin.ext h)
      have hd' : d.val < el.length := d.isLt
      have hd : (μ (oldE j d)).val = d.val := by
        show (if d.val < el.length then d.val else _) = d.val
        rw [if_pos hd']
      have e1 := ofList_ends (hn := hn) hel d
      have hee := e2 (μ (oldE j d))
      rw [hd, gE_leafEl_old hd' hdv] at hee
      rw [ends_old]
      exact joins_vals (by rw [hee.1, lv_val, e1.1]) (by rw [hee.2, lv_val, e1.2])
    · have hd : (μ (newE j 0 (by decide))).val = j.val := by
        show (if el.length + 0 < el.length then _ else if el.length + 0 = el.length then j.val else _) = j.val
        rw [if_neg (by omega), if_pos (by omega)]
      have e1 := ofList_ends (hn := hn) hel j
      have hee := e2 (μ (newE j 0 (by decide)))
      rw [hd, gE_leafEl_j hjm] at hee
      rw [ends_new0]
      exact joins_vals (by rw [hee.1, lv_val, e1.1]) (by rw [hee.2, vx_val]; rfl)
    · have hd : (μ (newE j 1 (by decide))).val = el.length := by
        show (if el.length + 1 < el.length then _ else if el.length + 1 = el.length then j.val
          else el.length + 1 - 1) = el.length
        rw [if_neg (by omega), if_neg (by omega)]; omega
      have e1 := ofList_ends (hn := hn) hel j
      have hee := e2 (μ (newE j 1 (by decide)))
      rw [hd, gE_leafEl_m] at hee
      rw [ends_new1]
      exact joins_vals (by rw [hee.1, vx_val]; rfl) (by rw [hee.2, lv_val, e1.2])
    · have hd : (μ (newE j 2 (by decide))).val = el.length + 1 := by
        show (if el.length + 2 < el.length then _ else if el.length + 2 = el.length then j.val
          else el.length + 2 - 1) = el.length + 1
        rw [if_neg (by omega), if_neg (by omega)]; omega
      have hee := e2 (μ (newE j 2 (by decide)))
      rw [hd, gE_leafEl_m1] at hee
      rw [ends_new2]
      exact joins_vals (by rw [hee.1, vx_val]; rfl) (by rw [hee.2, vl_val]; rfl)


/-- vertices of a leaf graph -/
theorem leaf_vtx {g : Fin X.m} (hg : P g) {x : Fin (leafG X g).n} (hx : meets (leafSet P g) x) :
    (∃ v, x = lv v ∧ meets P v) ∨ x = vx X ∨ x = vl X := by
  obtain ⟨a, ha, hax⟩ := hx
  rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
  · obtain ⟨w, rfl, hw⟩ := inc_old_lv hax
    exact Or.inl ⟨w, rfl, d, ((set_old P g d).1 ha).1, hw⟩
  · unfold Inc at hax; rw [ends_new0] at hax
    rcases hax with h | h
    · exact Or.inl ⟨_, h.symm, g, hg, Or.inl rfl⟩
    · exact Or.inr (Or.inl h.symm)
  · unfold Inc at hax; rw [ends_new1] at hax
    rcases hax with h | h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inl ⟨_, h.symm, g, hg, Or.inr rfl⟩
  · unfold Inc at hax; rw [ends_new2] at hax
    rcases hax with h | h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)

/-- **leaf graphs along an isomorphism**: T(P, g) embeds into T(H, β g) -/
theorem leaf_of_iso (hloop : Loopless X) {H : MGraph} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m}
    (hα : ∀ x y, meets P x → meets P y → α x = α y → x = y) (hβ : ∀ f g, P f → P g → β f = β g → f = g)
    (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {g : Fin X.m} (hg : P g)
    (hc : Colourable (leafSet (fun _ : Fin H.m => True) (β g)) 6) : Colourable (leafSet P g) 6 := by
  have ms : meets P (X.ends g).1 := ⟨g, hg, Or.inl rfl⟩
  have mt : meets P (X.ends g).2 := ⟨g, hg, Or.inr rfl⟩
  have hst_ne : α (X.ends g).1 ≠ α (X.ends g).2 := fun h => hloop g (hα _ _ ms mt h)
  -- orientation of `β g`
  by_cases st : (H.ends (β g)).1 = α (X.ends g).1
  all_goals
    have hje := hj g hg
    let ρ : Fin (leafG X g).n → Fin (leafG H (β g)).n := fun v =>
      if h : v.val < X.n then lv (α ⟨v.val, h⟩) else if v.val = X.n then vx H else vl H
    have ρlv : ∀ v, ρ (lv v) = lv (α v) := fun v => by
      simp only [ρ, lv_val, v.isLt, dif_pos]; try rfl
    have ρvx : ρ (vx X) = vx H := by simp only [ρ, vx_val]; simp
    have ρvl : ρ (vl X) = vl H := by simp only [ρ, vl_val]; simp
  · -- straight orientation: `sx ↦ sx`, `xt ↦ xt`
    have hends : H.ends (β g) = (α (X.ends g).1, α (X.ends g).2) := by
      rcases hje with h | h
      · exact h
      · rw [h] at st; exact absurd st.symm hst_ne
    let μ : Fin (leafG X g).m → Fin (leafG H (β g)).m := fun i =>
      if h : i.val < X.m then oldE (β g) (β ⟨i.val, h⟩) else
      if i.val = X.m then newE (β g) 0 (by decide) else
      if i.val = X.m + 1 then newE (β g) 1 (by decide) else newE (β g) 2 (by decide)
    have μo : ∀ d, μ (oldE g d) = oldE (β g) (β d) := fun d => by
      simp only [μ, oldE, d.isLt, dif_pos]
    have μ0 : μ (newE g 0 (by decide)) = newE (β g) 0 (by decide) := by simp [μ, newE]
    have μ1 : μ (newE g 1 (by decide)) = newE (β g) 1 (by decide) := by simp [μ, newE]
    have μ2 : μ (newE g 2 (by decide)) = newE (β g) 2 (by decide) := by simp [μ, newE]
    refine colourable_emb (X := leafG H (β g)) (P := leafSet (fun _ : Fin H.m => True) (β g))
      (Y := leafG X g) ρ μ ?_ ?_ ?_ ?_ hc
    · intro x y hx hy h
      rcases leaf_vtx hg hx with ⟨v, rfl, hv⟩ | rfl | rfl <;>
        rcases leaf_vtx hg hy with ⟨w, rfl, hw⟩ | rfl | rfl <;>
        simp only [ρlv, ρvx, ρvl] at h
      · rw [hα _ _ hv hw (lv_inj h)]
      · exact absurd h (lv_ne_vx _)
      · exact absurd h (lv_ne_vl _)
      · exact absurd h.symm (lv_ne_vx _)
      · rfl
      · exact absurd h (vx_ne_vl H)
      · exact absurd h.symm (lv_ne_vl _)
      · exact absurd h.symm (vx_ne_vl H)
      · rfl
    · intro a b ha hb h
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl <;>
        rcases leaf_cases g b with ⟨d', rfl⟩ | rfl | rfl | rfl <;>
        simp only [μo, μ0, μ1, μ2] at h <;>
        first
        | rfl
        | exact absurd h (oldE_ne_new _ _)
        | exact absurd h.symm (oldE_ne_new _ _)
        | exact absurd h (new_ne _ _ (by decide))
        | (rw [hβ d d' ((set_old P g d).1 ha).1 ((set_old P g d').1 hb).1 (oldE_inj h)])
    · intro a ha
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
      · rw [μo, set_old]
        obtain ⟨hd, hne⟩ := (set_old P g d).1 ha
        exact ⟨trivial, fun h => hne (hβ d g hd hg h)⟩
      · rw [μ0]; exact set_new _ _ _ _
      · rw [μ1]; exact set_new _ _ _ _
      · rw [μ2]; exact set_new _ _ _ _
    · intro a ha
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
      · rw [μo, ends_old, ρlv, ρlv]; exact leaf_joins_of (hj d ((set_old P g d).1 ha).1)
      · rw [μ0, ends_new0]; simp only [ρlv, ρvx]; left; rw [ends_new0, hends]
      · rw [μ1, ends_new1]; simp only [ρlv, ρvx]; left; rw [ends_new1, hends]
      · rw [μ2, ends_new2]; simp only [ρvx, ρvl]; left; rw [ends_new2]
  · -- reversed orientation: `sx ↦ xt`, `xt ↦ sx`
    have hends : H.ends (β g) = (α (X.ends g).2, α (X.ends g).1) := by
      rcases hje with h | h
      · rw [h] at st; exact absurd rfl st
      · exact h
    let μ : Fin (leafG X g).m → Fin (leafG H (β g)).m := fun i =>
      if h : i.val < X.m then oldE (β g) (β ⟨i.val, h⟩) else
      if i.val = X.m then newE (β g) 1 (by decide) else
      if i.val = X.m + 1 then newE (β g) 0 (by decide) else newE (β g) 2 (by decide)
    have μo : ∀ d, μ (oldE g d) = oldE (β g) (β d) := fun d => by
      simp only [μ, oldE, d.isLt, dif_pos]
    have μ0 : μ (newE g 0 (by decide)) = newE (β g) 1 (by decide) := by simp [μ, newE]
    have μ1 : μ (newE g 1 (by decide)) = newE (β g) 0 (by decide) := by simp [μ, newE]
    have μ2 : μ (newE g 2 (by decide)) = newE (β g) 2 (by decide) := by simp [μ, newE]
    refine colourable_emb (X := leafG H (β g)) (P := leafSet (fun _ : Fin H.m => True) (β g))
      (Y := leafG X g) ρ μ ?_ ?_ ?_ ?_ hc
    · intro x y hx hy h
      rcases leaf_vtx hg hx with ⟨v, rfl, hv⟩ | rfl | rfl <;>
        rcases leaf_vtx hg hy with ⟨w, rfl, hw⟩ | rfl | rfl <;>
        simp only [ρlv, ρvx, ρvl] at h
      · rw [hα _ _ hv hw (lv_inj h)]
      · exact absurd h (lv_ne_vx _)
      · exact absurd h (lv_ne_vl _)
      · exact absurd h.symm (lv_ne_vx _)
      · rfl
      · exact absurd h (vx_ne_vl H)
      · exact absurd h.symm (lv_ne_vl _)
      · exact absurd h.symm (vx_ne_vl H)
      · rfl
    · intro a b ha hb h
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl <;>
        rcases leaf_cases g b with ⟨d', rfl⟩ | rfl | rfl | rfl <;>
        simp only [μo, μ0, μ1, μ2] at h <;>
        first
        | rfl
        | exact absurd h (oldE_ne_new _ _)
        | exact absurd h.symm (oldE_ne_new _ _)
        | exact absurd h (new_ne _ _ (by decide))
        | (rw [hβ d d' ((set_old P g d).1 ha).1 ((set_old P g d').1 hb).1 (oldE_inj h)])
    · intro a ha
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
      · rw [μo, set_old]
        obtain ⟨hd, hne⟩ := (set_old P g d).1 ha
        exact ⟨trivial, fun h => hne (hβ d g hd hg h)⟩
      · rw [μ0]; exact set_new _ _ _ _
      · rw [μ1]; exact set_new _ _ _ _
      · rw [μ2]; exact set_new _ _ _ _
    · intro a ha
      rcases leaf_cases g a with ⟨d, rfl⟩ | rfl | rfl | rfl
      · rw [μo, ends_old, ρlv, ρlv]; exact leaf_joins_of (hj d ((set_old P g d).1 ha).1)
      · rw [μ0, ends_new0]; simp only [ρlv, ρvx]; right; rw [ends_new1, hends]
      · rw [μ1, ends_new1]; simp only [ρlv, ρvx]; right; rw [ends_new0, hends]
      · rw [μ2, ends_new2]; simp only [ρvx, ρvl]; left; rw [ends_new2]


/-- the edge list is loopless, and for every edge `j` some certificate is a checked star colouring of `leafEl` -/
def leafCert (n : Nat) (el : List (Nat × Nat)) (cs : List (List (List (Nat × Nat × Nat)) × List Nat)) : Bool :=
  elOK n el && (List.range el.length).all (fun j => cs.any (fun p => fastStar2 (n + 2) (leafEl n el j) p.1 p.2))

theorem leaf_of_cert {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}
    {cs : List (List (List (Nat × Nat × Nat)) × List Nat)} (h : leafCert n el cs = true) :
    ∀ j : Fin (ofList n el hn).m, Colourable (leafSet (fun _ : Fin (ofList n el hn).m => True) j) 6 := by
  intro j
  unfold leafCert at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨p, _, hp⟩ := h.2 j.val j.isLt
  exact leaf_ofList h.1 j hp

end ii3

end RH2F

-- ===== from II3a.lean =====
namespace RH2F

/-! Rep02–Rep13: `s(j) = 1` certificates (SMALL-2SIDED) -/

def s1cs2 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 5), (1, 1, 1), (2, 2, 0)], [(0, 0, 5), (1, 0, 1), (5, 3, 2)], [(2, 0, 0), (3, 3, 3), (4, 3, 5)], [(3, 2, 3), (4, 2, 5), (5, 1, 2)]], [5, 1, 0, 3, 5, 2])]
theorem s1c2 : s1Cert (repN 2) (repL 2) s1cs2 = true := by decide +kernel

def s1cs3 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 5), (3, 2, 3), (5, 3, 4)], [(0, 0, 5), (1, 2, 4), (2, 3, 2)], [(1, 1, 4), (3, 0, 3), (4, 3, 0)], [(2, 1, 2), (4, 2, 0), (5, 0, 4)]], [5, 4, 2, 3, 0, 4]),
  ([[(0, 1, 1), (3, 2, 5), (5, 3, 0)], [(0, 0, 1), (1, 2, 4), (2, 3, 3)], [(1, 1, 4), (3, 0, 5), (4, 3, 1)], [(2, 1, 3), (4, 2, 1), (5, 0, 0)]], [1, 4, 3, 5, 1, 0])]
theorem s1c3 : s1Cert (repN 3) (repL 3) s1cs3 = true := by decide +kernel

def s1cs4 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 3), (1, 1, 1), (5, 4, 5)], [(0, 0, 3), (1, 0, 1), (4, 3, 0)], [(2, 3, 4), (3, 3, 3), (8, 5, 1)], [(2, 2, 4), (3, 2, 3), (4, 1, 0)], [(5, 0, 5), (6, 5, 4), (7, 5, 0)], [(6, 4, 4), (7, 4, 0), (8, 2, 1)]], [3, 1, 4, 3, 0, 5, 4, 0, 1]),
  ([[(0, 1, 4), (1, 1, 3), (5, 4, 5)], [(0, 0, 4), (1, 0, 3), (4, 3, 1)], [(2, 3, 4), (3, 3, 0), (8, 5, 2)], [(2, 2, 4), (3, 2, 0), (4, 1, 1)], [(5, 0, 5), (6, 5, 1), (7, 5, 3)], [(6, 4, 1), (7, 4, 3), (8, 2, 2)]], [4, 3, 4, 0, 1, 5, 1, 3, 2])]
theorem s1c4 : s1Cert (repN 4) (repL 4) s1cs4 = true := by decide +kernel

def s1cs5 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 2), (1, 2, 3), (5, 4, 4)], [(0, 0, 2), (4, 3, 4), (8, 5, 3)], [(1, 0, 3), (2, 3, 5), (3, 3, 1)], [(2, 2, 5), (3, 2, 1), (4, 1, 4)], [(5, 0, 4), (6, 5, 5), (7, 5, 1)], [(6, 4, 5), (7, 4, 1), (8, 1, 3)]], [2, 3, 5, 1, 4, 4, 5, 1, 3]),
  ([[(0, 1, 1), (1, 2, 5), (5, 4, 2)], [(0, 0, 1), (4, 3, 4), (8, 5, 3)], [(1, 0, 5), (2, 3, 0), (3, 3, 3)], [(2, 2, 0), (3, 2, 3), (4, 1, 4)], [(5, 0, 2), (6, 5, 5), (7, 5, 1)], [(6, 4, 5), (7, 4, 1), (8, 1, 3)]], [1, 5, 0, 3, 4, 2, 5, 1, 3]),
  ([[(0, 1, 1), (1, 2, 3), (5, 4, 0)], [(0, 0, 1), (4, 3, 5), (8, 5, 2)], [(1, 0, 3), (2, 3, 1), (3, 3, 4)], [(2, 2, 1), (3, 2, 4), (4, 1, 5)], [(5, 0, 0), (6, 5, 3), (7, 5, 4)], [(6, 4, 3), (7, 4, 4), (8, 1, 2)]], [1, 3, 1, 4, 5, 0, 3, 4, 2]),
  ([[(0, 1, 1), (1, 2, 3), (5, 4, 0)], [(0, 0, 1), (4, 3, 3), (8, 5, 4)], [(1, 0, 3), (2, 3, 2), (3, 3, 5)], [(2, 2, 2), (3, 2, 5), (4, 1, 3)], [(5, 0, 0), (6, 5, 2), (7, 5, 3)], [(6, 4, 2), (7, 4, 3), (8, 1, 4)]], [1, 3, 2, 5, 3, 0, 2, 3, 4])]
theorem s1c5 : s1Cert (repN 5) (repL 5) s1cs5 = true := by decide +kernel

def s1cs6 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(2, 2, 2), (4, 3, 5), (5, 4, 1)], [(0, 2, 5), (1, 3, 0), (8, 5, 3)], [(0, 1, 5), (2, 0, 2), (3, 3, 4)], [(1, 1, 0), (3, 2, 4), (4, 0, 5)], [(5, 0, 1), (6, 5, 2), (7, 5, 5)], [(6, 4, 2), (7, 4, 5), (8, 1, 3)]], [5, 0, 2, 4, 5, 1, 2, 5, 3]),
  ([[(2, 2, 0), (4, 3, 5), (5, 4, 3)], [(0, 2, 3), (1, 3, 2), (8, 5, 1)], [(0, 1, 3), (2, 0, 0), (3, 3, 4)], [(1, 1, 2), (3, 2, 4), (4, 0, 5)], [(5, 0, 3), (6, 5, 5), (7, 5, 4)], [(6, 4, 5), (7, 4, 4), (8, 1, 1)]], [3, 2, 0, 4, 5, 3, 5, 4, 1]),
  ([[(2, 2, 4), (4, 3, 3), (5, 4, 5)], [(0, 2, 0), (1, 3, 4), (8, 5, 2)], [(0, 1, 0), (2, 0, 4), (3, 3, 1)], [(1, 1, 4), (3, 2, 1), (4, 0, 3)], [(5, 0, 5), (6, 5, 4), (7, 5, 3)], [(6, 4, 4), (7, 4, 3), (8, 1, 2)]], [0, 4, 4, 1, 3, 5, 4, 3, 2])]
theorem s1c6 : s1Cert (repN 6) (repL 6) s1cs6 = true := by decide +kernel

def s1cs7 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 1), (6, 4, 0), (8, 5, 3)], [(0, 0, 1), (1, 2, 2), (2, 3, 4)], [(1, 1, 2), (3, 4, 3), (4, 3, 1)], [(2, 1, 4), (4, 2, 1), (5, 5, 5)], [(3, 2, 3), (6, 0, 0), (7, 5, 4)], [(5, 3, 5), (7, 4, 4), (8, 0, 3)]], [1, 2, 4, 3, 1, 5, 0, 4, 3]),
  ([[(0, 1, 0), (6, 4, 2), (8, 5, 3)], [(0, 0, 0), (1, 2, 1), (2, 3, 3)], [(1, 1, 1), (3, 4, 5), (4, 3, 2)], [(2, 1, 3), (4, 2, 2), (5, 5, 4)], [(3, 2, 5), (6, 0, 2), (7, 5, 1)], [(5, 3, 4), (7, 4, 1), (8, 0, 3)]], [0, 1, 3, 5, 2, 4, 2, 1, 3]),
  ([[(0, 1, 3), (6, 4, 2), (8, 5, 5)], [(0, 0, 3), (1, 2, 2), (2, 3, 5)], [(1, 1, 2), (3, 4, 4), (4, 3, 0)], [(2, 1, 5), (4, 2, 0), (5, 5, 4)], [(3, 2, 4), (6, 0, 2), (7, 5, 1)], [(5, 3, 4), (7, 4, 1), (8, 0, 5)]], [3, 2, 5, 4, 0, 4, 2, 1, 5]),
  ([[(0, 1, 5), (6, 4, 2), (8, 5, 4)], [(0, 0, 5), (1, 2, 1), (2, 3, 0)], [(1, 1, 1), (3, 4, 3), (4, 3, 2)], [(2, 1, 0), (4, 2, 2), (5, 5, 5)], [(3, 2, 3), (6, 0, 2), (7, 5, 1)], [(5, 3, 5), (7, 4, 1), (8, 0, 4)]], [5, 1, 0, 3, 2, 5, 2, 1, 4])]
theorem s1c7 : s1Cert (repN 7) (repL 7) s1cs7 = true := by decide +kernel

def s1cs8 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 3, 5), (1, 4, 0), (2, 5, 4)], [(3, 3, 0), (4, 4, 1), (5, 5, 3)], [(6, 3, 2), (7, 4, 3), (8, 5, 5)], [(0, 0, 5), (3, 1, 0), (6, 2, 2)], [(1, 0, 0), (4, 1, 1), (7, 2, 3)], [(2, 0, 4), (5, 1, 3), (8, 2, 5)]], [5, 0, 4, 0, 1, 3, 2, 3, 5]),
  ([[(0, 3, 3), (1, 4, 5), (2, 5, 1)], [(3, 3, 4), (4, 4, 3), (5, 5, 2)], [(6, 3, 2), (7, 4, 0), (8, 5, 5)], [(0, 0, 3), (3, 1, 4), (6, 2, 2)], [(1, 0, 5), (4, 1, 3), (7, 2, 0)], [(2, 0, 1), (5, 1, 2), (8, 2, 5)]], [3, 5, 1, 4, 3, 2, 2, 0, 5]),
  ([[(0, 3, 5), (1, 4, 2), (2, 5, 4)], [(3, 3, 1), (4, 4, 5), (5, 5, 3)], [(6, 3, 0), (7, 4, 4), (8, 5, 1)], [(0, 0, 5), (3, 1, 1), (6, 2, 0)], [(1, 0, 2), (4, 1, 5), (7, 2, 4)], [(2, 0, 4), (5, 1, 3), (8, 2, 1)]], [5, 2, 4, 1, 5, 3, 0, 4, 1]),
  ([[(0, 3, 5), (1, 4, 3), (2, 5, 4)], [(3, 3, 1), (4, 4, 4), (5, 5, 0)], [(6, 3, 2), (7, 4, 1), (8, 5, 5)], [(0, 0, 5), (3, 1, 1), (6, 2, 2)], [(1, 0, 3), (4, 1, 4), (7, 2, 1)], [(2, 0, 4), (5, 1, 0), (8, 2, 5)]], [5, 3, 4, 1, 4, 0, 2, 1, 5])]
theorem s1c8 : s1Cert (repN 8) (repL 8) s1cs8 = true := by decide +kernel

def s1cs9 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 3), (4, 4, 5), (8, 6, 2)], [(0, 0, 3), (3, 3, 4), (11, 7, 1)], [(1, 3, 0), (2, 3, 2), (7, 5, 3)], [(1, 2, 0), (2, 2, 2), (3, 1, 4)], [(4, 0, 5), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 2, 3)], [(8, 0, 2), (9, 7, 5), (10, 7, 4)], [(9, 6, 5), (10, 6, 4), (11, 1, 1)]], [3, 0, 2, 4, 5, 1, 0, 3, 2, 5, 4, 1]),
  ([[(0, 1, 4), (4, 4, 2), (8, 6, 0)], [(0, 0, 4), (3, 3, 0), (11, 7, 3)], [(1, 3, 5), (2, 3, 2), (7, 5, 0)], [(1, 2, 5), (2, 2, 2), (3, 1, 0)], [(4, 0, 2), (5, 5, 3), (6, 5, 4)], [(5, 4, 3), (6, 4, 4), (7, 2, 0)], [(8, 0, 0), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 3)]], [4, 5, 2, 0, 2, 3, 4, 0, 0, 5, 1, 3]),
  ([[(0, 1, 3), (4, 4, 0), (8, 6, 5)], [(0, 0, 3), (3, 3, 2), (11, 7, 1)], [(1, 3, 5), (2, 3, 1), (7, 5, 3)], [(1, 2, 5), (2, 2, 1), (3, 1, 2)], [(4, 0, 0), (5, 5, 5), (6, 5, 4)], [(5, 4, 5), (6, 4, 4), (7, 2, 3)], [(8, 0, 5), (9, 7, 3), (10, 7, 4)], [(9, 6, 3), (10, 6, 4), (11, 1, 1)]], [3, 5, 1, 2, 0, 5, 4, 3, 5, 3, 4, 1])]
theorem s1c9 : s1Cert (repN 9) (repL 9) s1cs9 = true := by decide +kernel

def s1cs10 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 5), (1, 1, 0), (4, 4, 1)], [(0, 0, 5), (1, 0, 0), (11, 7, 2)], [(2, 3, 3), (3, 3, 2), (7, 5, 0)], [(2, 2, 3), (3, 2, 2), (8, 6, 1)], [(4, 0, 1), (5, 5, 4), (6, 5, 2)], [(5, 4, 4), (6, 4, 2), (7, 2, 0)], [(8, 3, 1), (9, 7, 5), (10, 7, 4)], [(9, 6, 5), (10, 6, 4), (11, 1, 2)]], [5, 0, 3, 2, 1, 4, 2, 0, 1, 5, 4, 2]),
  ([[(0, 1, 3), (1, 1, 1), (4, 4, 0)], [(0, 0, 3), (1, 0, 1), (11, 7, 2)], [(2, 3, 3), (3, 3, 4), (7, 5, 5)], [(2, 2, 3), (3, 2, 4), (8, 6, 0)], [(4, 0, 0), (5, 5, 4), (6, 5, 2)], [(5, 4, 4), (6, 4, 2), (7, 2, 5)], [(8, 3, 0), (9, 7, 3), (10, 7, 5)], [(9, 6, 3), (10, 6, 5), (11, 1, 2)]], [3, 1, 3, 4, 0, 4, 2, 5, 0, 3, 5, 2]),
  ([[(0, 1, 3), (1, 1, 2), (4, 4, 4)], [(0, 0, 3), (1, 0, 2), (11, 7, 5)], [(2, 3, 4), (3, 3, 0), (7, 5, 5)], [(2, 2, 4), (3, 2, 0), (8, 6, 3)], [(4, 0, 4), (5, 5, 3), (6, 5, 1)], [(5, 4, 3), (6, 4, 1), (7, 2, 5)], [(8, 3, 3), (9, 7, 0), (10, 7, 1)], [(9, 6, 0), (10, 6, 1), (11, 1, 5)]], [3, 2, 4, 0, 4, 3, 1, 5, 3, 0, 1, 5])]
theorem s1c10 : s1Cert (repN 10) (repL 10) s1cs10 = true := by decide +kernel

def s1cs11 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 2, 5), (4, 4, 2), (8, 6, 3)], [(3, 3, 1), (7, 5, 4), (11, 7, 2)], [(0, 0, 5), (1, 3, 4), (2, 3, 2)], [(1, 2, 4), (2, 2, 2), (3, 1, 1)], [(4, 0, 2), (5, 5, 0), (6, 5, 3)], [(5, 4, 0), (6, 4, 3), (7, 1, 4)], [(8, 0, 3), (9, 7, 4), (10, 7, 5)], [(9, 6, 4), (10, 6, 5), (11, 1, 2)]], [5, 4, 2, 1, 2, 0, 3, 4, 3, 4, 5, 2]),
  ([[(0, 2, 1), (4, 4, 4), (8, 6, 0)], [(3, 3, 4), (7, 5, 1), (11, 7, 2)], [(0, 0, 1), (1, 3, 2), (2, 3, 3)], [(1, 2, 2), (2, 2, 3), (3, 1, 4)], [(4, 0, 4), (5, 5, 3), (6, 5, 5)], [(5, 4, 3), (6, 4, 5), (7, 1, 1)], [(8, 0, 0), (9, 7, 3), (10, 7, 5)], [(9, 6, 3), (10, 6, 5), (11, 1, 2)]], [1, 2, 3, 4, 4, 3, 5, 1, 0, 3, 5, 2]),
  ([[(0, 2, 2), (4, 4, 5), (8, 6, 3)], [(3, 3, 4), (7, 5, 2), (11, 7, 0)], [(0, 0, 2), (1, 3, 5), (2, 3, 1)], [(1, 2, 5), (2, 2, 1), (3, 1, 4)], [(4, 0, 5), (5, 5, 4), (6, 5, 1)], [(5, 4, 4), (6, 4, 1), (7, 1, 2)], [(8, 0, 3), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 0)]], [2, 5, 1, 4, 5, 4, 1, 2, 3, 5, 1, 0])]
theorem s1c11 : s1Cert (repN 11) (repL 11) s1cs11 = true := by decide +kernel

def s1cs12 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 0), (4, 4, 1), (8, 6, 5)], [(0, 0, 0), (3, 3, 3), (7, 5, 5)], [(1, 3, 2), (2, 3, 4), (11, 7, 0)], [(1, 2, 2), (2, 2, 4), (3, 1, 3)], [(4, 0, 1), (5, 5, 4), (6, 5, 2)], [(5, 4, 4), (6, 4, 2), (7, 1, 5)], [(8, 0, 5), (9, 7, 3), (10, 7, 1)], [(9, 6, 3), (10, 6, 1), (11, 2, 0)]], [0, 2, 4, 3, 1, 4, 2, 5, 5, 3, 1, 0]),
  ([[(0, 1, 5), (4, 4, 0), (8, 6, 1)], [(0, 0, 5), (3, 3, 2), (7, 5, 4)], [(1, 3, 3), (2, 3, 5), (11, 7, 0)], [(1, 2, 3), (2, 2, 5), (3, 1, 2)], [(4, 0, 0), (5, 5, 3), (6, 5, 5)], [(5, 4, 3), (6, 4, 5), (7, 1, 4)], [(8, 0, 1), (9, 7, 3), (10, 7, 2)], [(9, 6, 3), (10, 6, 2), (11, 2, 0)]], [5, 3, 5, 2, 0, 3, 5, 4, 1, 3, 2, 0])]
theorem s1c12 : s1Cert (repN 12) (repL 12) s1cs12 = true := by decide +kernel

def s1cs13 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 5), (1, 2, 1), (4, 4, 4)], [(0, 0, 5), (3, 3, 3), (7, 5, 0)], [(1, 0, 1), (2, 3, 5), (8, 6, 0)], [(2, 2, 5), (3, 1, 3), (11, 7, 4)], [(4, 0, 4), (5, 5, 5), (6, 5, 3)], [(5, 4, 5), (6, 4, 3), (7, 1, 0)], [(8, 2, 0), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 3, 4)]], [5, 1, 5, 3, 4, 5, 3, 0, 0, 5, 1, 4]),
  ([[(0, 1, 0), (1, 2, 5), (4, 4, 1)], [(0, 0, 0), (3, 3, 4), (7, 5, 1)], [(1, 0, 5), (2, 3, 1), (8, 6, 2)], [(2, 2, 1), (3, 1, 4), (11, 7, 0)], [(4, 0, 1), (5, 5, 3), (6, 5, 2)], [(5, 4, 3), (6, 4, 2), (7, 1, 1)], [(8, 2, 2), (9, 7, 5), (10, 7, 3)], [(9, 6, 5), (10, 6, 3), (11, 3, 0)]], [0, 5, 1, 4, 1, 3, 2, 1, 2, 5, 3, 0]),
  ([[(0, 1, 0), (1, 2, 2), (4, 4, 5)], [(0, 0, 0), (3, 3, 2), (7, 5, 4)], [(1, 0, 2), (2, 3, 1), (8, 6, 3)], [(2, 2, 1), (3, 1, 2), (11, 7, 5)], [(4, 0, 5), (5, 5, 3), (6, 5, 1)], [(5, 4, 3), (6, 4, 1), (7, 1, 4)], [(8, 2, 3), (9, 7, 4), (10, 7, 0)], [(9, 6, 4), (10, 6, 0), (11, 3, 5)]], [0, 2, 1, 2, 5, 3, 1, 4, 3, 4, 0, 5]),
  ([[(0, 1, 4), (1, 2, 2), (4, 4, 1)], [(0, 0, 4), (3, 3, 0), (7, 5, 5)], [(1, 0, 2), (2, 3, 3), (8, 6, 5)], [(2, 2, 3), (3, 1, 0), (11, 7, 1)], [(4, 0, 1), (5, 5, 0), (6, 5, 2)], [(5, 4, 0), (6, 4, 2), (7, 1, 5)], [(8, 2, 5), (9, 7, 2), (10, 7, 4)], [(9, 6, 2), (10, 6, 4), (11, 3, 1)]], [4, 2, 3, 0, 1, 0, 2, 5, 5, 2, 4, 1])]
theorem s1c13 : s1Cert (repN 13) (repL 13) s1cs13 = true := by decide +kernel

end RH2F

-- ===== from II3b.lean =====
namespace RH2F

/-! Rep14–Rep25: `s(j) = 1` certificates (SMALL-2SIDED) -/

def s1cs14 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(2, 2, 1), (4, 3, 5), (8, 6, 4)], [(0, 2, 4), (1, 3, 3), (7, 5, 2)], [(0, 1, 4), (2, 0, 1), (3, 3, 0)], [(1, 1, 3), (3, 2, 0), (4, 0, 5)], [(5, 5, 3), (6, 5, 4), (11, 7, 1)], [(5, 4, 3), (6, 4, 4), (7, 1, 2)], [(8, 0, 4), (9, 7, 0), (10, 7, 3)], [(9, 6, 0), (10, 6, 3), (11, 4, 1)]], [4, 3, 1, 0, 5, 3, 4, 2, 4, 0, 3, 1]),
  ([[(2, 2, 0), (4, 3, 5), (8, 6, 1)], [(0, 2, 1), (1, 3, 2), (7, 5, 4)], [(0, 1, 1), (2, 0, 0), (3, 3, 3)], [(1, 1, 2), (3, 2, 3), (4, 0, 5)], [(5, 5, 5), (6, 5, 0), (11, 7, 3)], [(5, 4, 5), (6, 4, 0), (7, 1, 4)], [(8, 0, 1), (9, 7, 5), (10, 7, 4)], [(9, 6, 5), (10, 6, 4), (11, 4, 3)]], [1, 2, 0, 3, 5, 5, 0, 4, 1, 5, 4, 3]),
  ([[(2, 2, 2), (4, 3, 1), (8, 6, 0)], [(0, 2, 0), (1, 3, 4), (7, 5, 5)], [(0, 1, 0), (2, 0, 2), (3, 3, 5)], [(1, 1, 4), (3, 2, 5), (4, 0, 1)], [(5, 5, 1), (6, 5, 3), (11, 7, 2)], [(5, 4, 1), (6, 4, 3), (7, 1, 5)], [(8, 0, 0), (9, 7, 4), (10, 7, 5)], [(9, 6, 4), (10, 6, 5), (11, 4, 2)]], [0, 4, 2, 5, 1, 1, 3, 5, 0, 4, 5, 2]),
  ([[(2, 2, 0), (4, 3, 3), (8, 6, 1)], [(0, 2, 5), (1, 3, 1), (7, 5, 2)], [(0, 1, 5), (2, 0, 0), (3, 3, 4)], [(1, 1, 1), (3, 2, 4), (4, 0, 3)], [(5, 5, 1), (6, 5, 4), (11, 7, 3)], [(5, 4, 1), (6, 4, 4), (7, 1, 2)], [(8, 0, 1), (9, 7, 0), (10, 7, 5)], [(9, 6, 0), (10, 6, 5), (11, 4, 3)]], [5, 1, 0, 4, 3, 1, 4, 2, 1, 0, 5, 3]),
  ([[(2, 2, 2), (4, 3, 3), (8, 6, 0)], [(0, 2, 3), (1, 3, 5), (7, 5, 4)], [(0, 1, 3), (2, 0, 2), (3, 3, 1)], [(1, 1, 5), (3, 2, 1), (4, 0, 3)], [(5, 5, 1), (6, 5, 0), (11, 7, 4)], [(5, 4, 1), (6, 4, 0), (7, 1, 4)], [(8, 0, 0), (9, 7, 2), (10, 7, 5)], [(9, 6, 2), (10, 6, 5), (11, 4, 4)]], [3, 5, 2, 1, 3, 1, 0, 4, 0, 2, 5, 4])]
theorem s1c14 : s1Cert (repN 14) (repL 14) s1cs14 = true := by decide +kernel

def s1cs15 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(2, 2, 0), (4, 3, 4), (5, 4, 5)], [(0, 2, 4), (1, 3, 1), (7, 5, 2)], [(0, 1, 4), (2, 0, 0), (3, 3, 3)], [(1, 1, 1), (3, 2, 3), (4, 0, 4)], [(5, 0, 5), (6, 5, 0), (8, 6, 3)], [(6, 4, 0), (7, 1, 2), (11, 7, 4)], [(8, 4, 3), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 5, 4)]], [4, 1, 0, 3, 4, 5, 0, 2, 3, 5, 1, 4]),
  ([[(2, 2, 2), (4, 3, 0), (5, 4, 3)], [(0, 2, 3), (1, 3, 1), (7, 5, 5)], [(0, 1, 3), (2, 0, 2), (3, 3, 4)], [(1, 1, 1), (3, 2, 4), (4, 0, 0)], [(5, 0, 3), (6, 5, 1), (8, 6, 4)], [(6, 4, 1), (7, 1, 5), (11, 7, 4)], [(8, 4, 4), (9, 7, 2), (10, 7, 0)], [(9, 6, 2), (10, 6, 0), (11, 5, 4)]], [3, 1, 2, 4, 0, 3, 1, 5, 4, 2, 0, 4]),
  ([[(2, 2, 5), (4, 3, 1), (5, 4, 2)], [(0, 2, 3), (1, 3, 0), (7, 5, 5)], [(0, 1, 3), (2, 0, 5), (3, 3, 4)], [(1, 1, 0), (3, 2, 4), (4, 0, 1)], [(5, 0, 2), (6, 5, 4), (8, 6, 3)], [(6, 4, 4), (7, 1, 5), (11, 7, 1)], [(8, 4, 3), (9, 7, 5), (10, 7, 0)], [(9, 6, 5), (10, 6, 0), (11, 5, 1)]], [3, 0, 5, 4, 1, 2, 4, 5, 3, 5, 0, 1]),
  ([[(2, 2, 4), (4, 3, 1), (5, 4, 0)], [(0, 2, 3), (1, 3, 5), (7, 5, 1)], [(0, 1, 3), (2, 0, 4), (3, 3, 0)], [(1, 1, 5), (3, 2, 0), (4, 0, 1)], [(5, 0, 0), (6, 5, 2), (8, 6, 5)], [(6, 4, 2), (7, 1, 1), (11, 7, 0)], [(8, 4, 5), (9, 7, 4), (10, 7, 1)], [(9, 6, 4), (10, 6, 1), (11, 5, 0)]], [3, 5, 4, 0, 1, 0, 2, 1, 5, 4, 1, 0])]
theorem s1c15 : s1Cert (repN 15) (repL 15) s1cs15 = true := by decide +kernel

def s1cs16 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(2, 2, 5), (3, 3, 3), (4, 4, 0)], [(0, 2, 0), (1, 3, 2), (7, 5, 3)], [(0, 1, 0), (2, 0, 5), (8, 6, 4)], [(1, 1, 2), (3, 0, 3), (11, 7, 5)], [(4, 0, 0), (5, 5, 1), (6, 5, 4)], [(5, 4, 1), (6, 4, 4), (7, 1, 3)], [(8, 2, 4), (9, 7, 2), (10, 7, 1)], [(9, 6, 2), (10, 6, 1), (11, 3, 5)]], [0, 2, 5, 3, 0, 1, 4, 3, 4, 2, 1, 5]),
  ([[(2, 2, 1), (3, 3, 2), (4, 4, 4)], [(0, 2, 3), (1, 3, 5), (7, 5, 2)], [(0, 1, 3), (2, 0, 1), (8, 6, 2)], [(1, 1, 5), (3, 0, 2), (11, 7, 0)], [(4, 0, 4), (5, 5, 1), (6, 5, 0)], [(5, 4, 1), (6, 4, 0), (7, 1, 2)], [(8, 2, 2), (9, 7, 4), (10, 7, 5)], [(9, 6, 4), (10, 6, 5), (11, 3, 0)]], [3, 5, 1, 2, 4, 1, 0, 2, 2, 4, 5, 0]),
  ([[(2, 2, 2), (3, 3, 1), (4, 4, 3)], [(0, 2, 5), (1, 3, 4), (7, 5, 1)], [(0, 1, 5), (2, 0, 2), (8, 6, 0)], [(1, 1, 4), (3, 0, 1), (11, 7, 5)], [(4, 0, 3), (5, 5, 0), (6, 5, 2)], [(5, 4, 0), (6, 4, 2), (7, 1, 1)], [(8, 2, 0), (9, 7, 2), (10, 7, 1)], [(9, 6, 2), (10, 6, 1), (11, 3, 5)]], [5, 4, 2, 1, 3, 0, 2, 1, 0, 2, 1, 5]),
  ([[(2, 2, 1), (3, 3, 5), (4, 4, 2)], [(0, 2, 4), (1, 3, 2), (7, 5, 3)], [(0, 1, 4), (2, 0, 1), (8, 6, 2)], [(1, 1, 2), (3, 0, 5), (11, 7, 1)], [(4, 0, 2), (5, 5, 4), (6, 5, 0)], [(5, 4, 4), (6, 4, 0), (7, 1, 3)], [(8, 2, 2), (9, 7, 3), (10, 7, 0)], [(9, 6, 3), (10, 6, 0), (11, 3, 1)]], [4, 2, 1, 5, 2, 4, 0, 3, 2, 3, 0, 1])]
theorem s1c16 : s1Cert (repN 16) (repL 16) s1cs16 = true := by decide +kernel

def s1cs17 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(3, 3, 1), (4, 4, 5), (8, 6, 4)], [(0, 2, 5), (1, 3, 4), (7, 5, 3)], [(0, 1, 5), (2, 3, 2), (11, 7, 3)], [(1, 1, 4), (2, 2, 2), (3, 0, 1)], [(4, 0, 5), (5, 5, 2), (6, 5, 1)], [(5, 4, 2), (6, 4, 1), (7, 1, 3)], [(8, 0, 4), (9, 7, 2), (10, 7, 0)], [(9, 6, 2), (10, 6, 0), (11, 2, 3)]], [5, 4, 2, 1, 5, 2, 1, 3, 4, 2, 0, 3]),
  ([[(3, 3, 4), (4, 4, 0), (8, 6, 2)], [(0, 2, 1), (1, 3, 5), (7, 5, 4)], [(0, 1, 1), (2, 3, 0), (11, 7, 3)], [(1, 1, 5), (2, 2, 0), (3, 0, 4)], [(4, 0, 0), (5, 5, 3), (6, 5, 1)], [(5, 4, 3), (6, 4, 1), (7, 1, 4)], [(8, 0, 2), (9, 7, 5), (10, 7, 0)], [(9, 6, 5), (10, 6, 0), (11, 2, 3)]], [1, 5, 0, 4, 0, 3, 1, 4, 2, 5, 0, 3]),
  ([[(3, 3, 1), (4, 4, 0), (8, 6, 2)], [(0, 2, 0), (1, 3, 2), (7, 5, 5)], [(0, 1, 0), (2, 3, 3), (11, 7, 1)], [(1, 1, 2), (2, 2, 3), (3, 0, 1)], [(4, 0, 0), (5, 5, 4), (6, 5, 1)], [(5, 4, 4), (6, 4, 1), (7, 1, 5)], [(8, 0, 2), (9, 7, 0), (10, 7, 4)], [(9, 6, 0), (10, 6, 4), (11, 2, 1)]], [0, 2, 3, 1, 0, 4, 1, 5, 2, 0, 4, 1])]
theorem s1c17 : s1Cert (repN 17) (repL 17) s1cs17 = true := by decide +kernel

def s1cs18 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(2, 2, 4), (4, 3, 2), (5, 4, 0)], [(0, 2, 3), (1, 3, 5), (8, 5, 4)], [(0, 1, 3), (2, 0, 4), (3, 3, 0)], [(1, 1, 5), (3, 2, 0), (4, 0, 2)], [(5, 0, 0), (9, 6, 3), (11, 7, 1)], [(6, 6, 5), (7, 7, 0), (8, 1, 4)], [(6, 5, 5), (9, 4, 3), (10, 7, 2)], [(7, 5, 0), (10, 6, 2), (11, 4, 1)]], [3, 5, 4, 0, 2, 0, 5, 0, 4, 3, 2, 1]),
  ([[(2, 2, 3), (4, 3, 1), (5, 4, 4)], [(0, 2, 2), (1, 3, 4), (8, 5, 5)], [(0, 1, 2), (2, 0, 3), (3, 3, 5)], [(1, 1, 4), (3, 2, 5), (4, 0, 1)], [(5, 0, 4), (9, 6, 2), (11, 7, 3)], [(6, 6, 1), (7, 7, 0), (8, 1, 5)], [(6, 5, 1), (9, 4, 2), (10, 7, 5)], [(7, 5, 0), (10, 6, 5), (11, 4, 3)]], [2, 4, 3, 5, 1, 4, 1, 0, 5, 2, 5, 3]),
  ([[(2, 2, 3), (4, 3, 2), (5, 4, 5)], [(0, 2, 5), (1, 3, 1), (8, 5, 2)], [(0, 1, 5), (2, 0, 3), (3, 3, 0)], [(1, 1, 1), (3, 2, 0), (4, 0, 2)], [(5, 0, 5), (9, 6, 4), (11, 7, 1)], [(6, 6, 0), (7, 7, 3), (8, 1, 2)], [(6, 5, 0), (9, 4, 4), (10, 7, 5)], [(7, 5, 3), (10, 6, 5), (11, 4, 1)]], [5, 1, 3, 0, 2, 5, 0, 3, 2, 4, 5, 1]),
  ([[(2, 2, 4), (4, 3, 5), (5, 4, 3)], [(0, 2, 5), (1, 3, 2), (8, 5, 1)], [(0, 1, 5), (2, 0, 4), (3, 3, 0)], [(1, 1, 2), (3, 2, 0), (4, 0, 5)], [(5, 0, 3), (9, 6, 1), (11, 7, 0)], [(6, 6, 4), (7, 7, 3), (8, 1, 1)], [(6, 5, 4), (9, 4, 1), (10, 7, 5)], [(7, 5, 3), (10, 6, 5), (11, 4, 0)]], [5, 2, 4, 0, 5, 3, 4, 3, 1, 1, 5, 0]),
  ([[(2, 2, 5), (4, 3, 2), (5, 4, 0)], [(0, 2, 4), (1, 3, 3), (8, 5, 1)], [(0, 1, 4), (2, 0, 5), (3, 3, 1)], [(1, 1, 3), (3, 2, 1), (4, 0, 2)], [(5, 0, 0), (9, 6, 3), (11, 7, 5)], [(6, 6, 5), (7, 7, 2), (8, 1, 1)], [(6, 5, 5), (9, 4, 3), (10, 7, 4)], [(7, 5, 2), (10, 6, 4), (11, 4, 5)]], [4, 3, 5, 1, 2, 0, 5, 2, 1, 3, 4, 5])]
theorem s1c18 : s1Cert (repN 18) (repL 18) s1cs18 = true := by decide +kernel

def s1cs19 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 1), (5, 4, 0), (7, 5, 5)], [(0, 0, 1), (1, 3, 4), (11, 7, 2)], [(2, 4, 3), (3, 3, 0), (8, 6, 5)], [(1, 1, 4), (3, 2, 0), (4, 5, 1)], [(2, 2, 3), (5, 0, 0), (6, 5, 2)], [(4, 3, 1), (6, 4, 2), (7, 0, 5)], [(8, 2, 5), (9, 7, 3), (10, 7, 0)], [(9, 6, 3), (10, 6, 0), (11, 1, 2)]], [1, 4, 3, 0, 1, 0, 2, 5, 5, 3, 0, 2]),
  ([[(0, 1, 5), (5, 4, 3), (7, 5, 0)], [(0, 0, 5), (1, 3, 3), (11, 7, 4)], [(2, 4, 2), (3, 3, 0), (8, 6, 3)], [(1, 1, 3), (3, 2, 0), (4, 5, 4)], [(2, 2, 2), (5, 0, 3), (6, 5, 1)], [(4, 3, 4), (6, 4, 1), (7, 0, 0)], [(8, 2, 3), (9, 7, 5), (10, 7, 1)], [(9, 6, 5), (10, 6, 1), (11, 1, 4)]], [5, 3, 2, 0, 4, 3, 1, 0, 3, 5, 1, 4]),
  ([[(0, 1, 1), (5, 4, 3), (7, 5, 4)], [(0, 0, 1), (1, 3, 3), (11, 7, 5)], [(2, 4, 5), (3, 3, 2), (8, 6, 4)], [(1, 1, 3), (3, 2, 2), (4, 5, 0)], [(2, 2, 5), (5, 0, 3), (6, 5, 2)], [(4, 3, 0), (6, 4, 2), (7, 0, 4)], [(8, 2, 4), (9, 7, 2), (10, 7, 1)], [(9, 6, 2), (10, 6, 1), (11, 1, 5)]], [1, 3, 5, 2, 0, 3, 2, 4, 4, 2, 1, 5]),
  ([[(0, 1, 1), (5, 4, 0), (7, 5, 5)], [(0, 0, 1), (1, 3, 3), (11, 7, 5)], [(2, 4, 5), (3, 3, 2), (8, 6, 1)], [(1, 1, 3), (3, 2, 2), (4, 5, 4)], [(2, 2, 5), (5, 0, 0), (6, 5, 3)], [(4, 3, 4), (6, 4, 3), (7, 0, 5)], [(8, 2, 1), (9, 7, 4), (10, 7, 2)], [(9, 6, 4), (10, 6, 2), (11, 1, 5)]], [1, 3, 5, 2, 4, 0, 3, 5, 1, 4, 2, 5])]
theorem s1c19 : s1Cert (repN 19) (repL 19) s1cs19 = true := by decide +kernel

def s1cs20 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(5, 4, 1), (7, 5, 4), (8, 6, 0)], [(0, 2, 4), (1, 3, 0), (11, 7, 1)], [(0, 1, 4), (2, 4, 0), (3, 3, 5)], [(1, 1, 0), (3, 2, 5), (4, 5, 3)], [(2, 2, 0), (5, 0, 1), (6, 5, 2)], [(4, 3, 3), (6, 4, 2), (7, 0, 4)], [(8, 0, 0), (9, 7, 3), (10, 7, 2)], [(9, 6, 3), (10, 6, 2), (11, 1, 1)]], [4, 0, 0, 5, 3, 1, 2, 4, 0, 3, 2, 1]),
  ([[(5, 4, 2), (7, 5, 5), (8, 6, 3)], [(0, 2, 3), (1, 3, 2), (11, 7, 1)], [(0, 1, 3), (2, 4, 4), (3, 3, 0)], [(1, 1, 2), (3, 2, 0), (4, 5, 3)], [(2, 2, 4), (5, 0, 2), (6, 5, 1)], [(4, 3, 3), (6, 4, 1), (7, 0, 5)], [(8, 0, 3), (9, 7, 4), (10, 7, 2)], [(9, 6, 4), (10, 6, 2), (11, 1, 1)]], [3, 2, 4, 0, 3, 2, 1, 5, 3, 4, 2, 1]),
  ([[(5, 4, 4), (7, 5, 1), (8, 6, 3)], [(0, 2, 5), (1, 3, 3), (11, 7, 0)], [(0, 1, 5), (2, 4, 3), (3, 3, 1)], [(1, 1, 3), (3, 2, 1), (4, 5, 0)], [(2, 2, 3), (5, 0, 4), (6, 5, 2)], [(4, 3, 0), (6, 4, 2), (7, 0, 1)], [(8, 0, 3), (9, 7, 2), (10, 7, 5)], [(9, 6, 2), (10, 6, 5), (11, 1, 0)]], [5, 3, 3, 1, 0, 4, 2, 1, 3, 2, 5, 0]),
  ([[(5, 4, 4), (7, 5, 3), (8, 6, 1)], [(0, 2, 3), (1, 3, 4), (11, 7, 1)], [(0, 1, 3), (2, 4, 1), (3, 3, 5)], [(1, 1, 4), (3, 2, 5), (4, 5, 2)], [(2, 2, 1), (5, 0, 4), (6, 5, 5)], [(4, 3, 2), (6, 4, 5), (7, 0, 3)], [(8, 0, 1), (9, 7, 5), (10, 7, 0)], [(9, 6, 5), (10, 6, 0), (11, 1, 1)]], [3, 4, 1, 5, 2, 4, 5, 3, 1, 5, 0, 1]),
  ([[(5, 4, 5), (7, 5, 1), (8, 6, 0)], [(0, 2, 5), (1, 3, 4), (11, 7, 2)], [(0, 1, 5), (2, 4, 3), (3, 3, 0)], [(1, 1, 4), (3, 2, 0), (4, 5, 3)], [(2, 2, 3), (5, 0, 5), (6, 5, 2)], [(4, 3, 3), (6, 4, 2), (7, 0, 1)], [(8, 0, 0), (9, 7, 3), (10, 7, 5)], [(9, 6, 3), (10, 6, 5), (11, 1, 2)]], [5, 4, 3, 0, 3, 5, 2, 1, 0, 3, 5, 2])]
theorem s1c20 : s1Cert (repN 20) (repL 20) s1cs20 = true := by decide +kernel

def s1cs21 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 0), (9, 6, 2), (11, 7, 1)], [(0, 0, 0), (1, 2, 4), (2, 3, 3)], [(1, 1, 4), (3, 4, 1), (4, 3, 2)], [(2, 1, 3), (4, 2, 2), (5, 5, 5)], [(3, 2, 1), (6, 6, 3), (7, 5, 0)], [(5, 3, 5), (7, 4, 0), (8, 7, 4)], [(6, 4, 3), (9, 0, 2), (10, 7, 5)], [(8, 5, 4), (10, 6, 5), (11, 0, 1)]], [0, 4, 3, 1, 2, 5, 3, 0, 4, 2, 5, 1]),
  ([[(0, 1, 5), (9, 6, 4), (11, 7, 1)], [(0, 0, 5), (1, 2, 2), (2, 3, 3)], [(1, 1, 2), (3, 4, 1), (4, 3, 0)], [(2, 1, 3), (4, 2, 0), (5, 5, 4)], [(3, 2, 1), (6, 6, 0), (7, 5, 3)], [(5, 3, 4), (7, 4, 3), (8, 7, 2)], [(6, 4, 0), (9, 0, 4), (10, 7, 5)], [(8, 5, 2), (10, 6, 5), (11, 0, 1)]], [5, 2, 3, 1, 0, 4, 0, 3, 2, 4, 5, 1]),
  ([[(0, 1, 2), (9, 6, 5), (11, 7, 1)], [(0, 0, 2), (1, 2, 5), (2, 3, 3)], [(1, 1, 5), (3, 4, 0), (4, 3, 1)], [(2, 1, 3), (4, 2, 1), (5, 5, 5)], [(3, 2, 0), (6, 6, 3), (7, 5, 4)], [(5, 3, 5), (7, 4, 4), (8, 7, 2)], [(6, 4, 3), (9, 0, 5), (10, 7, 0)], [(8, 5, 2), (10, 6, 0), (11, 0, 1)]], [2, 5, 3, 0, 1, 5, 3, 4, 2, 5, 0, 1]),
  ([[(0, 1, 0), (9, 6, 2), (11, 7, 5)], [(0, 0, 0), (1, 2, 4), (2, 3, 3)], [(1, 1, 4), (3, 4, 5), (4, 3, 0)], [(2, 1, 3), (4, 2, 0), (5, 5, 1)], [(3, 2, 5), (6, 6, 3), (7, 5, 2)], [(5, 3, 1), (7, 4, 2), (8, 7, 0)], [(6, 4, 3), (9, 0, 2), (10, 7, 4)], [(8, 5, 0), (10, 6, 4), (11, 0, 5)]], [0, 4, 3, 5, 0, 1, 3, 2, 0, 2, 4, 5]),
  ([[(0, 1, 2), (9, 6, 1), (11, 7, 3)], [(0, 0, 2), (1, 2, 4), (2, 3, 0)], [(1, 1, 4), (3, 4, 2), (4, 3, 3)], [(2, 1, 0), (4, 2, 3), (5, 5, 1)], [(3, 2, 2), (6, 6, 3), (7, 5, 5)], [(5, 3, 1), (7, 4, 5), (8, 7, 2)], [(6, 4, 3), (9, 0, 1), (10, 7, 4)], [(8, 5, 2), (10, 6, 4), (11, 0, 3)]], [2, 4, 0, 2, 3, 1, 3, 5, 2, 1, 4, 3])]
theorem s1c21 : s1Cert (repN 21) (repL 21) s1cs21 = true := by decide +kernel

def s1cs22 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 4, 3), (1, 5, 4), (8, 6, 0)], [(2, 3, 5), (3, 4, 0), (4, 5, 2)], [(5, 3, 0), (6, 4, 1), (7, 5, 3)], [(2, 1, 5), (5, 2, 0), (11, 7, 3)], [(0, 0, 3), (3, 1, 0), (6, 2, 1)], [(1, 0, 4), (4, 1, 2), (7, 2, 3)], [(8, 0, 0), (9, 7, 5), (10, 7, 4)], [(9, 6, 5), (10, 6, 4), (11, 3, 3)]], [3, 4, 5, 0, 2, 0, 1, 3, 0, 5, 4, 3]),
  ([[(0, 4, 3), (1, 5, 5), (8, 6, 4)], [(2, 3, 3), (3, 4, 1), (4, 5, 4)], [(5, 3, 4), (6, 4, 0), (7, 5, 2)], [(2, 1, 3), (5, 2, 4), (11, 7, 5)], [(0, 0, 3), (3, 1, 1), (6, 2, 0)], [(1, 0, 5), (4, 1, 4), (7, 2, 2)], [(8, 0, 4), (9, 7, 2), (10, 7, 1)], [(9, 6, 2), (10, 6, 1), (11, 3, 5)]], [3, 5, 3, 1, 4, 4, 0, 2, 4, 2, 1, 5]),
  ([[(0, 4, 2), (1, 5, 1), (8, 6, 5)], [(2, 3, 3), (3, 4, 5), (4, 5, 4)], [(5, 3, 4), (6, 4, 0), (7, 5, 2)], [(2, 1, 3), (5, 2, 4), (11, 7, 1)], [(0, 0, 2), (3, 1, 5), (6, 2, 0)], [(1, 0, 1), (4, 1, 4), (7, 2, 2)], [(8, 0, 5), (9, 7, 3), (10, 7, 4)], [(9, 6, 3), (10, 6, 4), (11, 3, 1)]], [2, 1, 3, 5, 4, 4, 0, 2, 5, 3, 4, 1]),
  ([[(0, 4, 3), (1, 5, 1), (8, 6, 4)], [(2, 3, 5), (3, 4, 2), (4, 5, 3)], [(5, 3, 4), (6, 4, 0), (7, 5, 5)], [(2, 1, 5), (5, 2, 4), (11, 7, 2)], [(0, 0, 3), (3, 1, 2), (6, 2, 0)], [(1, 0, 1), (4, 1, 3), (7, 2, 5)], [(8, 0, 4), (9, 7, 3), (10, 7, 0)], [(9, 6, 3), (10, 6, 0), (11, 3, 2)]], [3, 1, 5, 2, 3, 4, 0, 5, 4, 3, 0, 2])]
theorem s1c22 : s1Cert (repN 22) (repL 22) s1cs22 = true := by decide +kernel

def s1cs23 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 3, 0), (9, 6, 4), (11, 7, 5)], [(3, 3, 3), (4, 4, 5), (5, 5, 4)], [(6, 3, 2), (7, 4, 1), (8, 5, 3)], [(0, 0, 0), (3, 1, 3), (6, 2, 2)], [(1, 6, 0), (4, 1, 5), (7, 2, 1)], [(2, 7, 0), (5, 1, 4), (8, 2, 3)], [(1, 4, 0), (9, 0, 4), (10, 7, 2)], [(2, 5, 0), (10, 6, 2), (11, 0, 5)]], [0, 0, 0, 3, 5, 4, 2, 1, 3, 4, 2, 5]),
  ([[(0, 3, 2), (9, 6, 1), (11, 7, 4)], [(3, 3, 5), (4, 4, 2), (5, 5, 4)], [(6, 3, 1), (7, 4, 0), (8, 5, 5)], [(0, 0, 2), (3, 1, 5), (6, 2, 1)], [(1, 6, 4), (4, 1, 2), (7, 2, 0)], [(2, 7, 3), (5, 1, 4), (8, 2, 5)], [(1, 4, 4), (9, 0, 1), (10, 7, 5)], [(2, 5, 3), (10, 6, 5), (11, 0, 4)]], [2, 4, 3, 5, 2, 4, 1, 0, 5, 1, 5, 4]),
  ([[(0, 3, 2), (9, 6, 4), (11, 7, 0)], [(3, 3, 3), (4, 4, 1), (5, 5, 2)], [(6, 3, 4), (7, 4, 5), (8, 5, 0)], [(0, 0, 2), (3, 1, 3), (6, 2, 4)], [(1, 6, 0), (4, 1, 1), (7, 2, 5)], [(2, 7, 1), (5, 1, 2), (8, 2, 0)], [(1, 4, 0), (9, 0, 4), (10, 7, 3)], [(2, 5, 1), (10, 6, 3), (11, 0, 0)]], [2, 0, 1, 3, 1, 2, 4, 5, 0, 4, 3, 0]),
  ([[(0, 3, 2), (9, 6, 0), (11, 7, 4)], [(3, 3, 5), (4, 4, 2), (5, 5, 3)], [(6, 3, 4), (7, 4, 0), (8, 5, 5)], [(0, 0, 2), (3, 1, 5), (6, 2, 4)], [(1, 6, 3), (4, 1, 2), (7, 2, 0)], [(2, 7, 1), (5, 1, 3), (8, 2, 5)], [(1, 4, 3), (9, 0, 0), (10, 7, 5)], [(2, 5, 1), (10, 6, 5), (11, 0, 4)]], [2, 3, 1, 5, 2, 3, 4, 0, 5, 0, 5, 4]),
  ([[(0, 3, 3), (9, 6, 1), (11, 7, 0)], [(3, 3, 4), (4, 4, 0), (5, 5, 3)], [(6, 3, 5), (7, 4, 3), (8, 5, 2)], [(0, 0, 3), (3, 1, 4), (6, 2, 5)], [(1, 6, 4), (4, 1, 0), (7, 2, 3)], [(2, 7, 1), (5, 1, 3), (8, 2, 2)], [(1, 4, 4), (9, 0, 1), (10, 7, 5)], [(2, 5, 1), (10, 6, 5), (11, 0, 0)]], [3, 4, 1, 4, 0, 3, 5, 3, 2, 1, 5, 0])]
theorem s1c23 : s1Cert (repN 23) (repL 23) s1cs23 = true := by decide +kernel

def s1cs24 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 1), (1, 2, 2), (2, 3, 0)], [(0, 0, 1), (6, 6, 0), (7, 7, 5)], [(1, 0, 2), (8, 5, 5), (9, 7, 3)], [(2, 0, 0), (10, 5, 4), (11, 6, 3)], [(3, 5, 2), (4, 6, 4), (5, 7, 0)], [(3, 4, 2), (8, 2, 5), (10, 3, 4)], [(4, 4, 4), (6, 1, 0), (11, 3, 3)], [(5, 4, 0), (7, 1, 5), (9, 2, 3)]], [1, 2, 0, 2, 4, 0, 0, 5, 5, 3, 4, 3]),
  ([[(0, 1, 2), (1, 2, 3), (2, 3, 4)], [(0, 0, 2), (6, 6, 0), (7, 7, 4)], [(1, 0, 3), (8, 5, 5), (9, 7, 1)], [(2, 0, 4), (10, 5, 3), (11, 6, 1)], [(3, 5, 2), (4, 6, 5), (5, 7, 0)], [(3, 4, 2), (8, 2, 5), (10, 3, 3)], [(4, 4, 5), (6, 1, 0), (11, 3, 1)], [(5, 4, 0), (7, 1, 4), (9, 2, 1)]], [2, 3, 4, 2, 5, 0, 0, 4, 5, 1, 3, 1]),
  ([[(0, 1, 1), (1, 2, 5), (2, 3, 0)], [(0, 0, 1), (6, 6, 3), (7, 7, 0)], [(1, 0, 5), (8, 5, 2), (9, 7, 3)], [(2, 0, 0), (10, 5, 3), (11, 6, 4)], [(3, 5, 1), (4, 6, 5), (5, 7, 4)], [(3, 4, 1), (8, 2, 2), (10, 3, 3)], [(4, 4, 5), (6, 1, 3), (11, 3, 4)], [(5, 4, 4), (7, 1, 0), (9, 2, 3)]], [1, 5, 0, 1, 5, 4, 3, 0, 2, 3, 3, 4]),
  ([[(0, 1, 0), (1, 2, 1), (2, 3, 4)], [(0, 0, 0), (6, 6, 1), (7, 7, 5)], [(1, 0, 1), (8, 5, 5), (9, 7, 3)], [(2, 0, 4), (10, 5, 0), (11, 6, 3)], [(3, 5, 2), (4, 6, 5), (5, 7, 4)], [(3, 4, 2), (8, 2, 5), (10, 3, 0)], [(4, 4, 5), (6, 1, 1), (11, 3, 3)], [(5, 4, 4), (7, 1, 5), (9, 2, 3)]], [0, 1, 4, 2, 5, 4, 1, 5, 5, 3, 0, 3]),
  ([[(0, 1, 5), (1, 2, 1), (2, 3, 3)], [(0, 0, 5), (6, 6, 0), (7, 7, 4)], [(1, 0, 1), (8, 5, 4), (9, 7, 3)], [(2, 0, 3), (10, 5, 2), (11, 6, 5)], [(3, 5, 5), (4, 6, 1), (5, 7, 0)], [(3, 4, 5), (8, 2, 4), (10, 3, 2)], [(4, 4, 1), (6, 1, 0), (11, 3, 5)], [(5, 4, 0), (7, 1, 4), (9, 2, 3)]], [5, 1, 3, 5, 1, 0, 0, 4, 4, 3, 2, 5])]
theorem s1c24 : s1Cert (repN 24) (repL 24) s1cs24 = true := by decide +kernel

def s1cs25 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 1, 0), (1, 2, 3), (2, 3, 5)], [(0, 0, 0), (6, 5, 2), (10, 7, 1)], [(1, 0, 3), (7, 6, 2), (8, 4, 4)], [(2, 0, 5), (9, 4, 3), (11, 7, 0)], [(3, 5, 1), (8, 2, 4), (9, 3, 3)], [(3, 4, 1), (4, 6, 5), (6, 1, 2)], [(4, 5, 5), (5, 7, 4), (7, 2, 2)], [(5, 6, 4), (10, 1, 1), (11, 3, 0)]], [0, 3, 5, 1, 5, 4, 2, 2, 4, 3, 1, 0]),
  ([[(0, 1, 5), (1, 2, 0), (2, 3, 3)], [(0, 0, 5), (6, 5, 3), (10, 7, 2)], [(1, 0, 0), (7, 6, 2), (8, 4, 5)], [(2, 0, 3), (9, 4, 2), (11, 7, 4)], [(3, 5, 1), (8, 2, 5), (9, 3, 2)], [(3, 4, 1), (4, 6, 0), (6, 1, 3)], [(4, 5, 0), (5, 7, 1), (7, 2, 2)], [(5, 6, 1), (10, 1, 2), (11, 3, 4)]], [5, 0, 3, 1, 0, 1, 3, 2, 5, 2, 2, 4]),
  ([[(0, 1, 3), (1, 2, 5), (2, 3, 0)], [(0, 0, 3), (6, 5, 1), (10, 7, 2)], [(1, 0, 5), (7, 6, 1), (8, 4, 2)], [(2, 0, 0), (9, 4, 1), (11, 7, 5)], [(3, 5, 4), (8, 2, 2), (9, 3, 1)], [(3, 4, 4), (4, 6, 0), (6, 1, 1)], [(4, 5, 0), (5, 7, 3), (7, 2, 1)], [(5, 6, 3), (10, 1, 2), (11, 3, 5)]], [3, 5, 0, 4, 0, 3, 1, 1, 2, 1, 2, 5]),
  ([[(0, 1, 0), (1, 2, 3), (2, 3, 2)], [(0, 0, 0), (6, 5, 5), (10, 7, 4)], [(1, 0, 3), (7, 6, 1), (8, 4, 5)], [(2, 0, 2), (9, 4, 1), (11, 7, 0)], [(3, 5, 2), (8, 2, 5), (9, 3, 1)], [(3, 4, 2), (4, 6, 4), (6, 1, 5)], [(4, 5, 4), (5, 7, 3), (7, 2, 1)], [(5, 6, 3), (10, 1, 4), (11, 3, 0)]], [0, 3, 2, 2, 4, 3, 5, 1, 5, 1, 4, 0])]
theorem s1c25 : s1Cert (repN 25) (repL 25) s1cs25 = true := by decide +kernel

end RH2F

-- ===== from II3l.lean =====
namespace RH2F

/-! leaf graphs T(Rep_k, j), k = 1, 2, 3 (II-RED2 Step 2) -/

def lfcs1 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 2, 0), (1, 1, 1), (2, 1, 2)], [(1, 0, 1), (2, 0, 2), (3, 2, 3)], [(0, 0, 0), (3, 1, 3), (4, 3, 1)], [(4, 2, 1)]], [0, 1, 2, 3, 1]),
  ([[(0, 1, 0), (1, 2, 1), (2, 1, 2)], [(0, 0, 0), (2, 0, 2), (3, 2, 3)], [(1, 0, 1), (3, 1, 3), (4, 3, 0)], [(4, 2, 0)]], [0, 1, 2, 3, 0]),
  ([[(0, 1, 0), (1, 1, 1), (2, 2, 2)], [(0, 0, 0), (1, 0, 1), (3, 2, 3)], [(2, 0, 2), (3, 1, 3), (4, 3, 0)], [(4, 2, 0)]], [0, 1, 2, 3, 0])]
theorem lfc1 : leafCert (repN 1) (repL 1) lfcs1 = true := by decide +kernel

def lfcs2 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 4, 0), (1, 1, 1), (2, 2, 2)], [(1, 0, 1), (5, 3, 3), (6, 4, 4)], [(2, 0, 2), (3, 3, 0), (4, 3, 1)], [(3, 2, 0), (4, 2, 1), (5, 1, 3)], [(0, 0, 0), (6, 1, 4), (7, 5, 1)], [(7, 4, 1)]], [0, 1, 2, 0, 1, 3, 4, 1]),
  ([[(0, 1, 0), (1, 4, 1), (2, 2, 2)], [(0, 0, 0), (5, 3, 3), (6, 4, 4)], [(2, 0, 2), (3, 3, 0), (4, 3, 1)], [(3, 2, 0), (4, 2, 1), (5, 1, 3)], [(1, 0, 1), (6, 1, 4), (7, 5, 0)], [(7, 4, 0)]], [0, 1, 2, 0, 1, 3, 4, 0]),
  ([[(0, 1, 0), (1, 1, 1), (2, 4, 2)], [(0, 0, 0), (1, 0, 1), (5, 3, 3)], [(3, 3, 0), (4, 3, 1), (6, 4, 4)], [(3, 2, 0), (4, 2, 1), (5, 1, 3)], [(2, 0, 2), (6, 2, 4), (7, 5, 0)], [(7, 4, 0)]], [0, 1, 2, 0, 1, 3, 4, 0]),
  ([[(0, 1, 0), (1, 1, 1), (2, 2, 2)], [(0, 0, 0), (1, 0, 1), (5, 3, 3)], [(2, 0, 2), (3, 4, 0), (4, 3, 1)], [(4, 2, 1), (5, 1, 3), (6, 4, 4)], [(3, 2, 0), (6, 3, 4), (7, 5, 1)], [(7, 4, 1)]], [0, 1, 2, 0, 1, 3, 4, 1]),
  ([[(0, 1, 0), (1, 1, 1), (2, 2, 2)], [(0, 0, 0), (1, 0, 1), (5, 3, 3)], [(2, 0, 2), (3, 3, 0), (4, 4, 1)], [(3, 2, 0), (5, 1, 3), (6, 4, 4)], [(4, 2, 1), (6, 3, 4), (7, 5, 0)], [(7, 4, 0)]], [0, 1, 2, 0, 1, 3, 4, 0]),
  ([[(0, 1, 0), (1, 1, 1), (2, 2, 2)], [(0, 0, 0), (1, 0, 1), (6, 4, 4)], [(2, 0, 2), (3, 3, 0), (4, 3, 1)], [(3, 2, 0), (4, 2, 1), (5, 4, 3)], [(5, 3, 3), (6, 1, 4), (7, 5, 0)], [(7, 4, 0)]], [0, 1, 2, 0, 1, 3, 4, 0])]
theorem lfc2 : leafCert (repN 2) (repL 2) lfcs2 = true := by decide +kernel

def lfcs3 : List (List (List (Nat × Nat × Nat)) × List Nat) := [
  ([[(0, 4, 0), (3, 2, 2), (5, 3, 4)], [(1, 2, 0), (2, 3, 1), (6, 4, 5)], [(1, 1, 0), (3, 0, 2), (4, 3, 3)], [(2, 1, 1), (4, 2, 3), (5, 0, 4)], [(0, 0, 0), (6, 1, 5), (7, 5, 1)], [(7, 4, 1)]], [0, 0, 1, 2, 3, 4, 5, 1]),
  ([[(0, 1, 0), (3, 2, 2), (5, 3, 4)], [(0, 0, 0), (2, 3, 1), (6, 4, 5)], [(1, 4, 0), (3, 0, 2), (4, 3, 3)], [(2, 1, 1), (4, 2, 3), (5, 0, 4)], [(1, 2, 0), (6, 1, 5), (7, 5, 1)], [(7, 4, 1)]], [0, 0, 1, 2, 3, 4, 5, 1]),
  ([[(0, 1, 0), (3, 2, 2), (5, 3, 4)], [(0, 0, 0), (1, 2, 1), (6, 4, 5)], [(1, 1, 1), (3, 0, 2), (4, 3, 3)], [(2, 4, 0), (4, 2, 3), (5, 0, 4)], [(2, 3, 0), (6, 1, 5), (7, 5, 1)], [(7, 4, 1)]], [0, 1, 0, 2, 3, 4, 5, 1]),
  ([[(0, 1, 0), (3, 4, 1), (5, 3, 4)], [(0, 0, 0), (1, 2, 1), (2, 3, 2)], [(1, 1, 1), (4, 3, 3), (6, 4, 5)], [(2, 1, 2), (4, 2, 3), (5, 0, 4)], [(3, 0, 1), (6, 2, 5), (7, 5, 2)], [(7, 4, 2)]], [0, 1, 2, 1, 3, 4, 5, 2]),
  ([[(0, 1, 0), (3, 2, 2), (5, 3, 4)], [(0, 0, 0), (1, 2, 1), (2, 3, 2)], [(1, 1, 1), (3, 0, 2), (4, 4, 3)], [(2, 1, 2), (5, 0, 4), (6, 4, 5)], [(4, 2, 3), (6, 3, 5), (7, 5, 0)], [(7, 4, 0)]], [0, 1, 2, 2, 3, 4, 5, 0]),
  ([[(0, 1, 0), (3, 2, 2), (5, 4, 4)], [(0, 0, 0), (1, 2, 1), (2, 3, 2)], [(1, 1, 1), (3, 0, 2), (4, 3, 3)], [(2, 1, 2), (4, 2, 3), (6, 4, 5)], [(5, 0, 4), (6, 3, 5), (7, 5, 0)], [(7, 4, 0)]], [0, 1, 2, 2, 3, 4, 5, 0])]
theorem lfc3 : leafCert (repN 3) (repL 3) lfcs3 = true := by decide +kernel

end RH2F

-- ===== from II4.lean (part 1) =====
namespace RH2F
open MGraph
open Classical

section ii4
variable {X : MGraph} {P : Fin X.m → Prop}

/-- every edge of a representative with at least 4 vertices is good (SMALL-2SIDED certificates) -/
theorem good_rep (k : Nat) (hk2 : 2 ≤ k) (hk : k ≤ 25) : ∀ j, Good1 (repG k) j := by
  rcases (by omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
    k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
    k = 24 ∨ k = 25) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [good_of_cert s1c2, good_of_cert s1c3, good_of_cert s1c4, good_of_cert s1c5, good_of_cert s1c6,
    good_of_cert s1c7, good_of_cert s1c8, good_of_cert s1c9, good_of_cert s1c10, good_of_cert s1c11,
    good_of_cert s1c12, good_of_cert s1c13, good_of_cert s1c14, good_of_cert s1c15, good_of_cert s1c16,
    good_of_cert s1c17, good_of_cert s1c18, good_of_cert s1c19, good_of_cert s1c20, good_of_cert s1c21,
    good_of_cert s1c22, good_of_cert s1c23, good_of_cert s1c24, good_of_cert s1c25]

/-- the leaf graphs of the representatives with at most 4 vertices are star 6-colourable -/
theorem leaf_rep (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 3) :
    ∀ j : Fin (repG k).m, Colourable (leafSet (fun _ : Fin (repG k).m => True) j) 6 := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  exacts [leaf_of_cert lfc1, leaf_of_cert lfc2, leaf_of_cert lfc3]

theorem repN_le4 : ∀ k < 26, 1 ≤ k → repN k ≤ 4 → k ≤ 3 := by decide
theorem repN_one : repN 1 = 2 := rfl

/-- **Step 2 of II-RED2**: the leaf graphs of members of 𝒢 with at most 4 vertices -/
theorem step2 (hG : InG X P) (hpos : 0 < vcount P) (h4 : vcount P ≤ 4) {g : Fin X.m} (hg : P g) :
    Colourable (leafSet P g) 6 := by
  obtain ⟨k, hk1, hk25, hkn, α, β, hα, hβ, _, hj⟩ := cls _ X P hG rfl hpos (by omega)
  have hk3 : k ≤ 3 := repN_le4 k (by omega) hk1 (by omega)
  exact leaf_of_iso hG.1 hα hβ hj hg (leaf_rep k hk1 hk3 (β g))

/-- **SMALL-2SIDED** (fact 5c988cebcde7d49b) in pole form: a side with 4 to 8 vertices is 2-sided -/
theorem Cut2.small2sided (C : Cut2 P) (hG : InG X P) (h4 : 4 ≤ scount P C.S true)
    (h8 : scount P C.S true ≤ 8) : C.TwoSided := by
  obtain ⟨k, hk1, hk25, hkn, hiso⟩ := cls _ _ C.clo (C.clo_inG hG) C.vcount_clo (by omega) h8
  have hk2 : 2 ≤ k := by
    apply Classical.byContradiction
    intro h
    have : k = 1 := by omega
    subst this
    rw [repN_one] at hkn; omega
  exact C.twoSided_of_good hiso (good_rep k hk2 hk25)

end ii4

end RH2F

namespace RH2F
open MGraph

/-- **Layer 11 of the Lean formalization** (II-RED2 route): Lemma SMALL-2SIDED (fact 5c988cebcde7d49b) in pole
    form, and Step 2 of Theorem II-RED2 (fact 52408ddd08d61ae6): the leaf graphs of hosts with at most 4 vertices. -/
theorem layer11 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (C : Cut2 P), InG X P → 4 ≤ scount P C.S true →
      scount P C.S true ≤ 8 → C.TwoSided) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 0 < vcount P → vcount P ≤ 4 → ∀ g, P g →
      Colourable (leafSet P g) 6) :=
  ⟨fun _ _ C hG h4 h8 => C.small2sided hG h4 h8, fun _ _ hG hp h4 _ hg => step2 hG hp h4 hg⟩

end RH2F
