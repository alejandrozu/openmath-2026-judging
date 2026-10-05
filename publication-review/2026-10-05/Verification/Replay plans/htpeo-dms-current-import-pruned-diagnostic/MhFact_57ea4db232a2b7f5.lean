-- Lean proof of fact 57ea4db232a2b7f5 (RH2F.layer26); added by fact_submit, do not edit
import MhFact_85780d9a54267261
set_option backward.isDefEq.respectTransparency false

/-
  Layer 26 of the Lean formalization (RH2F): SMALL-PD (A) (fact 86f2b7c4166011f6) — the poles of the prism, K₃,₃
  and V₈ at every vertex and of K₄ with a digon on the edge 0 1 at its ends 0, 1 are dominant for every labelling of
  their ports — proved by a verified Bool checker (W-colourings, fact 1a864fdc0e0af441) evaluated by the kernel;
  hence ROOT-CS4 (fact 6010cb59aaf31d7a) without the finite hypothesis SMALLPD.
-/
-- ===== from PD1.lean =====

/-
  PD1.lean — generic tools for explicit small multigraphs given by edge lists:
  * `star_of_fast2R`: the table star checker `fastStar2` is sound for every multigraph whose ends are mapped onto the
    checked edge list by an injective renaming `ψ` of the vertices (used for the ambient `splitV D` of a pole, whose
    new vertices are numbered by the labelling `D`);
  * membership in 𝒢 of `ofList n el` from Bool certificates: loopless (`elOK`), cubic (`cubN`), connected and
    bridgeless (spanning orders `treeOK` of the multigraph and of the multigraph minus each edge).
-/

namespace RH2F
open MGraph

section pd1

/-! ### the table star checker under a renaming of the vertices -/

theorem mem_nbR {G : MGraph} {el : List (Nat × Nat)} (ψ : Fin G.n → Nat)
    (hm : ∀ e : Fin G.m, e.val < el.length)
    (hends : ∀ e : Fin G.m, ψ (G.ends e).1 = (gE el e.val).1 ∧ ψ (G.ends e).2 = (gE el e.val).2)
    {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hnb : nbOK el nb cl = true) {e : Fin G.m} {x y : Fin G.n} (h : G.Joins e x y) :
    (e.val, ψ y, colN cl e.val) ∈ nb.getD (ψ x) [] := by
  have h1 := List.all_eq_true.1 hnb e.val (List.mem_range.2 (hm e))
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h1
  have he := hends e
  rcases h with h | h <;> rw [h] at he <;> simp only at he <;> obtain ⟨e1, e2⟩ := he
  · rw [e1, e2]; exact h1.1
  · rw [e1, e2]; exact h1.2

/-- **soundness of the table checker under a renaming**: if an injective map `ψ` of the vertices of `G` into
    `[0, n)` carries the ends of every edge `e` of `G` to the `e`-th entry of `el`, a passed `fastStar2 n el nb cl`
    makes `cl` a star 6-colouring of `G` -/
theorem star_of_fast2R {G : MGraph} {n : Nat} {el : List (Nat × Nat)} (ψ : Fin G.n → Nat)
    (hψ : ∀ x y, ψ x = ψ y → x = y) (hψn : ∀ x, ψ x < n)
    (hm : ∀ e : Fin G.m, e.val < el.length)
    (hends : ∀ e : Fin G.m, ψ (G.ends e).1 = (gE el e.val).1 ∧ ψ (G.ends e).2 = (gE el e.val).2)
    {nb : List (List (Nat × Nat × Nat))} {cl : List Nat} (h : fastStar2 n el nb cl = true) :
    StarOn (G := G) (fun _ => True) 6 (colF G.m cl) := by
  unfold fastStar2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hnb⟩, hprop⟩, hwalk⟩ := h
  constructor
  · intro a b ⟨hab, x, hax, hbx⟩ _ _ heq
    obtain ⟨ya, hja⟩ := joins_of_inc hax
    obtain ⟨yb, hjb⟩ := joins_of_inc hbx
    have ha := mem_nbR ψ hm hends hnb hja
    have hb := mem_nbR ψ hm hends hnb hjb
    have h1 := List.all_eq_true.1 hprop (ψ x) (List.mem_range.2 (hψn x))
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 _ ha) _ hb
    have hc : colN cl a.val = colN cl b.val := congrArg Fin.val heq
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    simp only at h2
    rw [nbeq_false hne, nbeq_true hc] at h2
    exact absurd h2 (by decide)
  · intro w _ _ _ _ hbc
    have m1 := mem_nbR ψ hm hends hnb w.h1
    have m2 := mem_nbR ψ hm hends hnb w.h2
    have m3 := mem_nbR ψ hm hends hnb w.h3
    have m4 := mem_nbR ψ hm hends hnb w.h4
    have d01 : ψ w.v0 ≠ ψ w.v1 := fun h => w.d01 (hψ _ _ h)
    have d02 : ψ w.v0 ≠ ψ w.v2 := fun h => w.d02 (hψ _ _ h)
    have d03 : ψ w.v0 ≠ ψ w.v3 := fun h => w.d03 (hψ _ _ h)
    have d12 : ψ w.v1 ≠ ψ w.v2 := fun h => w.d12 (hψ _ _ h)
    have d13 : ψ w.v1 ≠ ψ w.v3 := fun h => w.d13 (hψ _ _ h)
    have d14 : ψ w.v1 ≠ ψ w.v4 := fun h => w.d14 (hψ _ _ h)
    have d23 : ψ w.v2 ≠ ψ w.v3 := fun h => w.d23 (hψ _ _ h)
    have d24 : ψ w.v2 ≠ ψ w.v4 := fun h => w.d24 (hψ _ _ h)
    have d34 : ψ w.v3 ≠ ψ w.v4 := fun h => w.d34 (hψ _ _ h)
    have c13 : colN cl w.e1.val = colN cl w.e3.val := congrArg Fin.val hbc.1
    have c24 : colN cl w.e2.val = colN cl w.e4.val := congrArg Fin.val hbc.2
    have k0 := List.all_eq_true.1 hwalk (ψ w.v0) (List.mem_range.2 (hψn _))
    have k1 := List.all_eq_true.1 k0 _ m1
    have k2 := List.all_eq_true.1 k1 _ m2
    simp only at k2
    rw [nbeq_false (Ne.symm d02)] at k2
    simp only [Bool.false_or] at k2
    have k3 := List.all_eq_true.1 k2 _ m3
    simp only at k3
    rw [nbeq_true c13, nbeq_false (Ne.symm d13)] at k3
    simp only [Bool.not_true, Bool.false_or] at k3
    have k4 := List.all_eq_true.1 k3 _ m4
    simp only at k4
    rw [nbeq_false d01, nbeq_false d03, nbeq_false d12, nbeq_false d14,
      nbeq_false d23, nbeq_false d24, nbeq_false d34, nbeq_true c24] at k4
    exact absurd k4 (by decide)

/-! ### incidence of `ofList` multigraphs in terms of the edge list -/

/-- edge `f` of the list `el` meets vertex `x` -/
def incN (el : List (Nat × Nat)) (f x : Nat) : Bool := (gE el f).1 == x || (gE el f).2 == x

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

theorem ofList_inc (hel : elOK n el = true) {f : Fin (ofList n el hn).m} {x : Fin (ofList n el hn).n} :
    (ofList n el hn).Inc f x ↔ incN el f.val x.val = true := by
  have he := ofList_ends (hn := hn) hel f
  unfold MGraph.Inc incN
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (h | h)
    · left; rw [← he.1, h]
    · right; rw [← he.2, h]
  · rintro (h | h)
    · left; exact Fin.ext (he.1.trans h)
    · right; exact Fin.ext (he.2.trans h)

theorem ofList_loopless (hel : elOK n el = true) : Loopless (ofList n el hn) := by
  intro f h
  have he := ofList_ends (hn := hn) hel f
  exact ofList_loop (hn := hn) hel f (he.1.symm.trans ((congrArg Fin.val h).trans he.2))

/-- in a loopless edge list, an edge joining `x` and `y` has `y` as its end other than `x` -/
theorem ofList_joins_oth (hel : elOK n el = true) {f : Fin (ofList n el hn).m} {x y : Fin (ofList n el hn).n}
    (h : (ofList n el hn).Joins f x y) : y.val = oth el f.val x.val := by
  have he := ofList_ends (hn := hn) hel f
  have hl := ofList_loop (hn := hn) hel f
  unfold oth
  rcases h with h | h <;> rw [h] at he <;> simp only at he <;> obtain ⟨e1, e2⟩ := he
  · rw [← e1, beq_self_eq_true, if_pos rfl]; exact e2
  · have hne : (gE el f.val).1 ≠ x.val := by rw [e2]; exact hl
    rw [if_neg (by simpa using hne)]; exact e1

/-- the ends of a listed edge are vertices -/
theorem gE_lt (hel : elOK n el = true) {f : Nat} (hf : f < el.length) : (gE el f).1 < n ∧ (gE el f).2 < n := by
  have hb := List.all_eq_true.1 hel _ (List.getElem_mem hf)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  have hg : gE el f = el[f] := by simp [gE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf]
  rw [hg]; exact hb.1

theorem oth_lt (hel : elOK n el = true) {f x : Nat} (hf : f < el.length) : oth el f x < n := by
  have h := gE_lt hel hf
  unfold oth; split
  · exact h.2
  · exact h.1

/-- an edge meeting `x` joins `x` to its other end -/
theorem ofList_joins_of_inc (hel : elOK n el = true) {f : Fin (ofList n el hn).m} {x : Fin (ofList n el hn).n}
    (h : incN el f.val x.val = true) :
    (ofList n el hn).Joins f x ⟨oth el f.val x.val, oth_lt hel f.isLt⟩ := by
  have he := ofList_ends (hn := hn) hel f
  unfold incN at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  unfold MGraph.Joins oth
  by_cases h1 : (gE el f.val).1 = x.val
  · left
    have : ((gE el f.val).1 == x.val) = true := by simpa using h1
    simp only [this, if_true]
    exact Prod.ext (Fin.ext (he.1.trans h1)) (Fin.ext he.2)
  · right
    have h2 : (gE el f.val).2 = x.val := h.resolve_left h1
    have : ((gE el f.val).1 == x.val) = false := by simpa using h1
    simp only [this]
    exact Prod.ext (Fin.ext he.1) (Fin.ext (he.2.trans h2))

/-! ### cubic -/

/-- every vertex meets exactly three edges of the list -/
def cubN (n : Nat) (el : List (Nat × Nat)) : Bool :=
  (List.range n).all (fun x => ((List.range el.length).filter (fun f => incN el f x)).length == 3)

theorem list_three {L : List Nat} (h : L.length = 3) : ∃ a b c, L = [a, b, c] := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, rfl⟩

theorem ofList_cubic (hel : elOK n el = true) (hc : cubN n el = true) :
    CubicOn (G := ofList n el hn) (fun _ => True) := by
  intro x _
  have h1 := List.all_eq_true.1 hc x.val (List.mem_range.2 x.isLt)
  simp only [beq_iff_eq] at h1
  obtain ⟨a, b, c, hL⟩ := list_three h1
  have hnd : ((List.range el.length).filter (fun f => incN el f x.val)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hmem : ∀ f, f ∈ (List.range el.length).filter (fun f => incN el f x.val) ↔
      f < el.length ∧ incN el f x.val = true := by
    intro f; simp [List.mem_filter, List.mem_range]
  rw [hL] at hnd hmem
  have ha := (hmem a).1 (by simp)
  have hb := (hmem b).1 (by simp)
  have hc' := (hmem c).1 (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hab, hac⟩, hbc⟩ := hnd
  refine ⟨⟨a, ha.1⟩, ⟨b, hb.1⟩, ⟨c, hc'.1⟩, trivial, trivial, trivial, (ofList_inc hel).2 ha.2,
    (ofList_inc hel).2 hb.2, (ofList_inc hel).2 hc'.2, fun h => hab (congrArg Fin.val h),
    fun h => hac (congrArg Fin.val h), fun h => hbc (congrArg Fin.val h), fun d _ hd => ?_⟩
  have := (hmem d.val).2 ⟨d.isLt, (ofList_inc hel).1 hd⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at this
  rcases this with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-! ### connected and bridgeless: spanning orders -/

/-- every vertex of `ord` is joined by an `F`-edge of the list to a vertex listed in `seen` or earlier in `ord` -/
def treeAux (el : List (Nat × Nat)) (F : Nat → Bool) : List Nat → List Nat → Bool
  | _, [] => true
  | seen, y :: rest => (List.range el.length).any (fun e => F e &&
      (((gE el e).1 == y && seen.contains (gE el e).2) || ((gE el e).2 == y && seen.contains (gE el e).1))) &&
      treeAux el F (y :: seen) rest

/-- `ord` lists, after the root `r`, every other vertex `< n`, each joined by an `F`-edge to an earlier one -/
def treeOK (n : Nat) (el : List (Nat × Nat)) (F : Nat → Bool) (r : Nat) (ord : List Nat) : Bool :=
  treeAux el F [r] ord && (List.range n).all (fun y => y == r || ord.contains y)

theorem treeAux_sound (F : Nat → Bool) (V : Nat → Bool) (r : Nat)
    (hV : ∀ e, e < el.length → F e = true → V (gE el e).1 = V (gE el e).2) :
    ∀ ord seen, (∀ s ∈ seen, V s = V r) → treeAux el F seen ord = true → ∀ y ∈ ord, V y = V r := by
  intro ord
  induction ord with
  | nil => intro _ _ _ y hy; cases hy
  | cons y rest ih =>
    intro seen hs h z hz
    unfold treeAux at h
    simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      List.contains_iff_mem] at h
    obtain ⟨⟨e, he, hF, hj⟩, hrest⟩ := h
    have hy : V y = V r := by
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, hV e he hF]; exact hs _ h2
      · rw [← h1, ← hV e he hF]; exact hs _ h2
    have hs' : ∀ s ∈ y :: seen, V s = V r := by
      intro s hs2
      rcases List.mem_cons.1 hs2 with rfl | h
      · exact hy
      · exact hs s h
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hy
    · exact ih _ hs' hrest z hz

/-- all vertices get the same value under a map constant along the `F`-edges -/
theorem treeOK_const (hel : elOK n el = true) {F : Nat → Bool} {r : Nat} {ord : List Nat}
    (ht : treeOK n el F r ord = true) (U : Fin (ofList n el hn).n → Bool)
    (hU : ∀ f : Fin (ofList n el hn).m, F f.val = true →
      U ((ofList n el hn).ends f).1 = U ((ofList n el hn).ends f).2) :
    ∀ x y : Fin (ofList n el hn).n, U x = U y := by
  unfold treeOK at ht
  simp only [Bool.and_eq_true] at ht
  obtain ⟨ht1, ht2⟩ := ht
  let V : Nat → Bool := fun y => if h : y < n then U ⟨y, h⟩ else false
  have hVU : ∀ x : Fin (ofList n el hn).n, V x.val = U x := fun x => dif_pos x.isLt
  have hV : ∀ e, e < el.length → F e = true → V (gE el e).1 = V (gE el e).2 := by
    intro e he hF
    have hends := ofList_ends (hn := hn) hel ⟨e, he⟩
    rw [← hends.1, ← hends.2, hVU, hVU]
    exact hU ⟨e, he⟩ hF
  have hall := treeAux_sound F V r hV ord [r] (by intro s hs; rw [List.mem_singleton.1 hs]) ht1
  have key : ∀ x : Fin (ofList n el hn).n, U x = V r := by
    intro x
    rw [← hVU]
    have h := List.all_eq_true.1 ht2 x.val (List.mem_range.2 x.isLt)
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    rcases h with h | h
    · rw [h]
    · exact hall _ h
  intro x y; rw [key x, key y]

theorem ofList_connected (hel : elOK n el = true) {r : Nat} {ord : List Nat}
    (ht : treeOK n el (fun _ => true) r ord = true) : ConnectedOn (G := ofList n el hn) (fun _ => True) := by
  intro U hU f g _ _
  exact treeOK_const hel ht U (fun f _ => hU f trivial) _ _

/-- spanning orders of the multigraph minus each edge -/
def bridgeN (n : Nat) (el : List (Nat × Nat)) (r : Nat) (ords : List (List Nat)) : Bool :=
  (List.range el.length).all (fun e => treeOK n el (fun f => f != e) r (ords.getD e []))

theorem ofList_bridgeless (hel : elOK n el = true) {r : Nat} {ords : List (List Nat)}
    (hb : bridgeN n el r ords = true) : BridgelessOn (G := ofList n el hn) (fun _ => True) := by
  intro e _ B
  have ht := List.all_eq_true.1 hb e.val (List.mem_range.2 e.isLt)
  have hc := treeOK_const hel ht B.U (fun f hf => B.sep f trivial (fun h => by
    subst h; simp at hf)) ((ofList n el hn).ends e).1 ((ofList n el hn).ends e).2
  rw [B.hu, B.hv] at hc
  exact Bool.noConfusion hc

/-- **membership in 𝒢 of an explicit edge list** from the Bool certificates -/
theorem ofList_inG (hel : elOK n el = true) (hc : cubN n el = true) {r : Nat} {ord : List Nat}
    (ht : treeOK n el (fun _ => true) r ord = true) {ords : List (List Nat)} (hb : bridgeN n el r ords = true) :
    InG (ofList n el hn) (fun _ => True) :=
  ⟨ofList_loopless hel, ofList_connected hel ht, ofList_bridgeless hel hb, ofList_cubic hel hc⟩

end pd1

end RH2F

-- ===== from PD2.lean =====

/-
  PD2.lean — a verified Bool checker for the dominance of a pole `Q(Y, v)` of an explicit multigraph
  `Y = ofList n el` (all edges, `Q = ⊤`) under **every** labelling of its ports:
  * incidences of the ambient `splitV D` at old vertices are those of `Y`, so `Col_t`, `Blk_t` and the colour-`6`
    perfect-matching condition are computed on the edge list and do not depend on the labelling (`vCol_iff_B`,
    `vBlk_iff_B`, `pm_of_pmN`);
  * the star property is checked once, on the ambient of the base labelling `a, b, c`, and transported to the ambient
    of every labelling by a renaming of the three new vertices (`star_split`);
  * `wN` is the W-colouring condition of fact 1a864fdc0e0af441 on the edge list (`wcol_of_wN`);
  * `poleN` checks that every listed colouring is an MC pole colouring, that every ordered triple of the ports has a
    W-colouring, and that every edge `g` of `Y − v` and status `s` has a W-colouring with `[d(g) = 6] = s`; by
    W-RED (b) this gives (D1) and (D2) for every labelling (`dominant_of_poleN`).
-/

namespace RH2F
open MGraph

section pd2

/-! ### poles of a vertex when all edges belong to the multigraph -/

theorem castAdd_inj3 {N : Nat} {a b : Fin N} (h : (Fin.castAdd 3 a : Fin (N + 3)) = Fin.castAdd 3 b) : a = b :=
  Fin.ext (by have := congrArg Fin.val h; exact this)

section gen
variable {Y : MGraph} {v : Fin Y.n}

theorem vPole_all (D : Ports (fun _ : Fin Y.m => True) v) (f : Fin Y.m) : vPole D f := by
  by_cases h : Y.Inc f v
  · exact Or.inr (D.all f trivial h)
  · exact Or.inl ⟨trivial, h⟩

/-- incidences of the ambient of a pole at an old vertex other than `v` are those of `Y` -/
theorem split_inc_old {Q : Fin Y.m → Prop} (D : Ports Q v) {f : Fin Y.m} {x : Fin Y.n} (hx : x ≠ v) :
    (splitV D).Inc f (Fin.castAdd 3 x) ↔ Y.Inc f x := by
  by_cases hp : ∃ t, f = D.p t
  · obtain ⟨t, rfl⟩ := hp
    unfold MGraph.Inc
    rw [splitV_ends_port]
    have hj := D.hj t
    constructor
    · rintro (h | h)
      · have hxt : D.x t = x := castAdd_inj3 h
        rcases hj with hj | hj <;> rw [hj]
        · exact Or.inr hxt
        · exact Or.inl hxt
      · exact absurd h.symm (castAdd_ne_natAdd' x t)
    · intro h
      left
      rcases hj with hj | hj <;> rw [hj] at h
      · rcases h with h | h
        · exact absurd h.symm hx
        · exact congrArg (Fin.castAdd 3) h
      · rcases h with h | h
        · exact congrArg (Fin.castAdd 3) h
        · exact absurd h.symm hx
  · unfold MGraph.Inc
    rw [nonport_ends D hp]
    constructor
    · rintro (h | h)
      · exact Or.inl (castAdd_inj3 h)
      · exact Or.inr (castAdd_inj3 h)
    · rintro (h | h)
      · exact Or.inl (congrArg (Fin.castAdd 3) h)
      · exact Or.inr (congrArg (Fin.castAdd 3) h)

/-- an edge other than `p t` at the port vertex `x t` is not a port edge -/
theorem not_port_of_inc (hloop : Loopless Y) {Q : Fin Y.m → Prop} (D : Ports Q v) {t : Fin 3} {f : Fin Y.m}
    (hf : f ≠ D.p t) (hinc : Y.Inc f (D.x t)) : ¬ ∃ s, f = D.p s := by
  rintro ⟨s, rfl⟩
  have hxv := x_ne_v hloop D t
  have hxs : D.x t = D.x s := by
    unfold MGraph.Inc at hinc
    rcases D.hj s with hj | hj <;> rw [hj] at hinc
    · rcases hinc with h | h
      · exact absurd h.symm hxv
      · exact h.symm
    · rcases hinc with h | h
      · exact h.symm
      · exact absurd h.symm hxv
  exact hf (congrArg D.p (D.xinj _ _ hxs).symm)

end gen

/-! ### the colour sets on the edge list -/

/-- the colours at `x` of the listed edges other than `pe` (`Col`) -/
def colB (el : List (Nat × Nat)) (cl : List Nat) (pe x κ : Nat) : Bool :=
  (List.range el.length).any (fun f => f != pe && incN el f x && colN cl f == κ)

/-- the colours `κ` of listed edges `f ≠ pe` at `x` whose other end meets another edge of the colour of `pe`
    (`Blk`) -/
def blkB (el : List (Nat × Nat)) (cl : List Nat) (pe x κ : Nat) : Bool :=
  (List.range el.length).any (fun f => f != pe && incN el f x && colN cl f == κ &&
    (List.range el.length).any (fun f' => f' != f && incN el f' (oth el f x) && colN cl f' == colN cl pe))

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

theorem vCol_iff_B (hel : elOK n el = true) {v : Fin (ofList n el hn).n}
    (D : Ports (fun _ : Fin (ofList n el hn).m => True) v) (cl : List Nat) (t : Fin 3) (κ : Fin 6) :
    vCol D (colF (ofList n el hn).m cl) t κ ↔ colB el cl (D.p t).val (D.x t).val κ.val = true := by
  have hloop := ofList_loopless (hn := hn) hel
  have hxv := x_ne_v hloop D t
  unfold vCol colB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, _, hne, hinc, hc⟩
    refine ⟨f.val, List.mem_range.2 f.isLt, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨⟨fun h => hne (Fin.ext h), (ofList_inc hel).1 ((split_inc_old D hxv).1 hinc)⟩, congrArg Fin.val hc⟩
  · rintro ⟨f, hf, h⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    obtain ⟨⟨hne, hinc⟩, hc⟩ := h
    have hf' := List.mem_range.1 hf
    exact ⟨⟨f, hf'⟩, vPole_all D _, fun h => hne (congrArg Fin.val h),
      (split_inc_old D hxv).2 ((ofList_inc (f := ⟨f, hf'⟩) hel).2 hinc), Fin.ext hc⟩

theorem vBlk_iff_B (hel : elOK n el = true) {v : Fin (ofList n el hn).n}
    (D : Ports (fun _ : Fin (ofList n el hn).m => True) v) (cl : List Nat) (t : Fin 3) (κ : Fin 6) :
    vBlk D (colF (ofList n el hn).m cl) t κ ↔ blkB el cl (D.p t).val (D.x t).val κ.val = true := by
  have hloop := ofList_loopless (hn := hn) hel
  have hxv := x_ne_v hloop D t
  -- the other end of a non-port edge at `x t` is not `v`
  have hrv : ∀ f : Fin (ofList n el hn).m, f ≠ D.p t → (ofList n el hn).Inc f (D.x t) →
      ∀ r, (ofList n el hn).Joins f (D.x t) r → r ≠ v := by
    intro f hne hinc r hj hr
    subst hr
    exact not_port_of_inc hloop D hne hinc (D.all f trivial (joins_inc_right hj))
  unfold vBlk blkB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, r, _, hne, hj, hc, f', _, hne', hinc', hc'⟩
    have hinc : (ofList n el hn).Inc f (D.x t) := (split_inc_old D hxv).1 (joins_inc_left hj)
    have hnp := not_port_of_inc hloop D hne hinc
    unfold MGraph.Joins at hj
    rw [nonport_ends D hnp] at hj
    obtain ⟨r', rfl, hj'⟩ : ∃ r' : Fin (ofList n el hn).n, r = Fin.castAdd 3 r' ∧
        (ofList n el hn).Joins f (D.x t) r' := by
      rcases hj with hj | hj
      · refine ⟨((ofList n el hn).ends f).2, (congrArg Prod.snd hj).symm, Or.inl ?_⟩
        have h1 := congrArg Prod.fst hj
        exact Prod.ext (castAdd_inj3 h1) rfl
      · refine ⟨((ofList n el hn).ends f).1, (congrArg Prod.fst hj).symm, Or.inr ?_⟩
        have h2 := congrArg Prod.snd hj
        exact Prod.ext rfl (castAdd_inj3 h2)
    have hr'v := hrv f hne hinc r' hj'
    have hoth := ofList_joins_oth hel hj'
    refine ⟨f.val, List.mem_range.2 f.isLt, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true, List.mem_range]
    refine ⟨⟨⟨fun h => hne (Fin.ext h), (ofList_inc hel).1 hinc⟩, congrArg Fin.val hc⟩,
      f'.val, f'.isLt, ⟨fun h => hne' (Fin.ext h), ?_⟩, congrArg Fin.val hc'⟩
    rw [← hoth]; exact (ofList_inc hel).1 ((split_inc_old D hr'v).1 hinc')
  · rintro ⟨f, hf, h⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨hne, hinc⟩, hc⟩, f', hf', ⟨hne', hinc'⟩, hc'⟩ := h
    have hf2 := List.mem_range.1 hf
    let F : Fin (ofList n el hn).m := ⟨f, hf2⟩
    have hincF : (ofList n el hn).Inc F (D.x t) := (ofList_inc hel).2 hinc
    have hneF : F ≠ D.p t := fun h => hne (congrArg Fin.val h)
    have hnp := not_port_of_inc hloop D hneF hincF
    have hjY := ofList_joins_of_inc (hn := hn) hel (f := F) hinc
    have hr'v := hrv F hneF hincF _ hjY
    refine ⟨F, Fin.castAdd 3 ⟨oth el f (D.x t).val, oth_lt hel hf2⟩, vPole_all D _, hneF, ?_, Fin.ext hc,
      ⟨f', hf'⟩, vPole_all D _, fun h => hne' (congrArg Fin.val h),
      (split_inc_old D hr'v).2 ((ofList_inc (f := ⟨f', hf'⟩) hel).2 hinc'), Fin.ext hc'⟩
    unfold MGraph.Joins
    rw [nonport_ends D hnp]
    rcases hjY with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ### the colour-`6` perfect matching condition -/

/-- every vertex other than `h0` meets exactly one listed edge of colour `5` -/
def pmN (n : Nat) (el : List (Nat × Nat)) (h0 : Nat) (cl : List Nat) : Bool :=
  (List.range n).all (fun x => x == h0 ||
    ((List.range el.length).filter (fun f => incN el f x && colN cl f == 5)).length == 1)

theorem list_one {L : List Nat} (h : L.length = 1) : ∃ a, L = [a] := by
  rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩ <;> simp at h
  exact ⟨a, rfl⟩

theorem pm_of_pmN (hel : elOK n el = true) {v : Fin (ofList n el hn).n}
    (D : Ports (fun _ : Fin (ofList n el hn).m => True) v) {cl : List Nat} (h : pmN n el v.val cl = true) :
    ∀ x, x ≠ v → meets (fun _ : Fin (ofList n el hn).m => True) x →
      ∃ a, vPole D a ∧ (splitV D).Inc a (Fin.castAdd 3 x) ∧ colF (ofList n el hn).m cl a = 5 ∧
        ∀ b, vPole D b → (splitV D).Inc b (Fin.castAdd 3 x) → colF (ofList n el hn).m cl b = 5 → b = a := by
  intro x hx _
  have h1 := List.all_eq_true.1 h x.val (List.mem_range.2 x.isLt)
  have hxv : (x.val == v.val) = false := by simpa using fun h' => hx (Fin.ext h')
  rw [hxv, Bool.false_or, beq_iff_eq] at h1
  obtain ⟨a, hL⟩ := list_one h1
  have hmem : ∀ f, f ∈ (List.range el.length).filter (fun f => incN el f x.val && colN cl f == 5) ↔
      f < el.length ∧ incN el f x.val = true ∧ colN cl f = 5 := by
    intro f; simp [List.mem_filter, List.mem_range]
  rw [hL] at hmem
  have ha := (hmem a).1 (List.mem_singleton_self a)
  refine ⟨⟨a, ha.1⟩, vPole_all D _, (split_inc_old D hx).2 ((ofList_inc (f := ⟨a, ha.1⟩) hel).2 ha.2.1),
    Fin.ext ha.2.2, ?_⟩
  intro b _ hb hb5
  have := (hmem b.val).2 ⟨b.isLt, (ofList_inc hel).1 ((split_inc_old D hx).1 hb), congrArg Fin.val hb5⟩
  exact Fin.ext (List.mem_singleton.1 this)

/-! ### the star property, checked on the base ambient -/

theorem starOn_top {G : MGraph} {P : Fin G.m → Prop} {k : Nat} {c : Fin G.m → Fin k}
    (h : StarOn (G := G) (fun _ => True) k c) : StarOn (G := G) P k c :=
  ⟨fun a b hab _ _ => h.1 a b hab trivial trivial, fun w _ _ _ _ => h.2 w trivial trivial trivial trivial⟩

/-- the index `0, 1, 2` of a base port edge -/
def posN (a b f : Nat) : Nat := if f == a then 0 else if f == b then 1 else 2

/-- the edges of the base ambient: a port edge `f ∈ {a, b, c}` joins its other end to the new vertex
    `n + posN a b f`; every other edge keeps its ends -/
def sE (n : Nat) (el : List (Nat × Nat)) (h0 a b c f : Nat) : Nat × Nat :=
  if (f == a || f == b || f == c) then (oth el f h0, n + posN a b f) else gE el f

/-- the edge list of the base ambient -/
def splitL (n : Nat) (el : List (Nat × Nat)) (h0 a b c : Nat) : List (Nat × Nat) :=
  (List.range el.length).map (sE n el h0 a b c)

theorem gE_splitL {h0 a b c f : Nat} (hf : f < el.length) :
    gE (splitL n el h0 a b c) f = sE n el h0 a b c f := by
  simp [gE, splitL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hf]

theorem posN_lt (a b f : Nat) : posN a b f < 3 := by
  unfold posN; split
  · omega
  · split <;> omega

theorem posN_inj {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {f f' : Nat}
    (hf : f = a ∨ f = b ∨ f = c) (hf' : f' = a ∨ f' = b ∨ f' = c) (h : posN a b f = posN a b f') : f = f' := by
  have pa : posN a b a = 0 := by simp [posN]
  have pb : posN a b b = 1 := by simp [posN, Ne.symm hab]
  have pc : posN a b c = 2 := by simp [posN, Ne.symm hac, Ne.symm hbc]
  rcases hf with h1 | h1 | h1 <;> rcases hf' with h2 | h2 | h2 <;> rw [h1, h2] at h ⊢ <;>
    first | rfl | (rw [pa, pb] at h; omega) | (rw [pa, pc] at h; omega) | (rw [pb, pc] at h; omega)

/-- **the star property for every labelling** from the star check of the base ambient -/
theorem star_split (hel : elOK n el = true) {v : Fin (ofList n el hn).n}
    (D : Ports (fun _ : Fin (ofList n el hn).m => True) v) {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hat : ∀ f, f < el.length → (incN el f v.val = true ↔ (f = a ∨ f = b ∨ f = c)))
    {nb : List (List (Nat × Nat × Nat))} {cl : List Nat}
    (hs : fastStar2 (n + 3) (splitL n el v.val a b c) nb cl = true) :
    StarOn (G := splitV D) (@vPole (ofList n el hn) (fun _ => True) v D) 6 (colF (ofList n el hn).m cl) := by
  have hpv : ∀ t, (D.p t).val = a ∨ (D.p t).val = b ∨ (D.p t).val = c := fun t =>
    (hat _ (D.p t).isLt).1 ((ofList_inc hel).1 (joins_inc_left (D.hj t)))
  have hx : ∀ t, (D.x t).val = oth el (D.p t).val v.val := fun t => ofList_joins_oth hel (D.hj t)
  let ψ : Fin (splitV D).n → Nat := fun u =>
    if u.val < n then u.val else n + posN a b (D.p ⟨(u.val - n) % 3, Nat.mod_lt _ (by decide)⟩).val
  refine starOn_top (star_of_fast2R (n := n + 3) (el := splitL n el v.val a b c) ψ ?_ ?_ ?_ ?_ hs)
  · intro x y h
    have hx3 : x.val < n + 3 := x.isLt
    have hy3 : y.val < n + 3 := y.isLt
    by_cases hxn : x.val < n <;> by_cases hyn : y.val < n <;> simp only [ψ, hxn, hyn, if_true, if_false] at h
    · exact Fin.ext h
    · have := posN_lt a b (D.p ⟨(y.val - n) % 3, Nat.mod_lt _ (by decide)⟩).val; omega
    · have := posN_lt a b (D.p ⟨(x.val - n) % 3, Nat.mod_lt _ (by decide)⟩).val; omega
    · have h' := posN_inj hab hac hbc (hpv _) (hpv _) (Nat.add_left_cancel h)
      have hst := D.pinj _ _ (Fin.ext h')
      have hv := congrArg Fin.val hst
      simp only at hv
      apply Fin.ext
      omega
  · intro x
    have hx3 : x.val < n + 3 := x.isLt
    by_cases hxn : x.val < n <;> simp only [ψ, hxn, if_true, if_false]
    · omega
    · have := posN_lt a b (D.p ⟨(x.val - n) % 3, Nat.mod_lt _ (by decide)⟩).val; omega
  · intro e
    simp only [splitL, List.length_map, List.length_range]
    exact e.isLt
  · intro e
    rw [gE_splitL e.isLt]
    by_cases hp : ∃ t, e = D.p t
    · obtain ⟨t, rfl⟩ := hp
      rw [splitV_ends_port]
      have hin : ((D.p t).val == a || (D.p t).val == b || (D.p t).val == c) = true := by
        rcases hpv t with h | h | h <;> simp [h]
      simp only [sE, hin, if_true]
      have h1 : (Fin.castAdd 3 (D.x t)).val < n := (D.x t).isLt
      have h2 : ¬ (Fin.natAdd (ofList n el hn).n t).val < n := by
        show ¬ (n + t.val < n); omega
      have h3 : ((Fin.natAdd (ofList n el hn).n t).val - n) % 3 = t.val := by
        show (n + t.val - n) % 3 = t.val; have := t.isLt; omega
      simp only [ψ, h1, h2, if_true, if_false]
      have h4 : (⟨((Fin.natAdd (ofList n el hn).n t).val - n) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = t :=
        Fin.ext h3
      rw [h4]
      exact ⟨hx t, rfl⟩
    · rw [nonport_ends D hp]
      have hnin : (e.val == a || e.val == b || e.val == c) = false := by
        cases hq : (e.val == a || e.val == b || e.val == c)
        · rfl
        · exfalso
          have : e.val = a ∨ e.val = b ∨ e.val = c := by
            simp only [Bool.or_eq_true, beq_iff_eq] at hq
            rcases hq with (h | h) | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          exact hp (D.all e trivial ((ofList_inc hel).2 ((hat _ e.isLt).2 this)))
      simp only [sE, hnin]
      have he := ofList_ends (hn := hn) hel e
      have h1 : (Fin.castAdd 3 ((ofList n el hn).ends e).1).val < n := ((ofList n el hn).ends e).1.isLt
      have h2 : (Fin.castAdd 3 ((ofList n el hn).ends e).2).val < n := ((ofList n el hn).ends e).2.isLt
      simp only [ψ, h1, h2, if_true]
      exact he

/-! ### the W-colouring condition on the edge list -/

/-- the W-colouring conditions at M-port `pi` (other ports `pj`, `pk`) for the colour list `cl`, apart from the MC
    pole property: colour `5` on `pi`, (W0), and shape (SU) or (S1) -/
def wN (el : List (Nat × Nat)) (cl : List Nat) (h0 pi pj pk : Nat) : Bool :=
  colN cl pi == 5 && colN cl pj != 5 && colN cl pk != 5 && colN cl pj != colN cl pk &&
  !blkB el cl pj (oth el pj h0) (colN cl pk) && !blkB el cl pk (oth el pk h0) (colN cl pj) &&
  ((List.range 6).all (fun κ => colB el cl pi (oth el pi h0) κ == (κ == colN cl pj || κ == colN cl pk)) ||
   (List.range 6).any (fun c => c != 5 && c != colN cl pj && c != colN cl pk &&
     ((List.range 6).all (fun κ => colB el cl pi (oth el pi h0) κ == (κ == colN cl pj || κ == c)) ||
      (List.range 6).all (fun κ => colB el cl pi (oth el pi h0) κ == (κ == colN cl pk || κ == c))) &&
     !colB el cl pj (oth el pj h0) c && !colB el cl pk (oth el pk h0) c &&
     !((List.range 6).any (fun κ => κ != 5 && κ != colN cl pj && κ != colN cl pk && colB el cl pj (oth el pj h0) κ) &&
       (List.range 6).any (fun κ => κ != 5 && κ != colN cl pj && κ != colN cl pk && colB el cl pk (oth el pk h0) κ))))

/-- a Bool-checked equation of truth values over all colours gives an equivalence -/
theorem shape_of_all {P : Fin 6 → Prop} {p : Nat → Bool} (hP : ∀ κ : Fin 6, P κ ↔ p κ.val = true)
    {A B : Fin 6} (h : (List.range 6).all (fun κ => p κ == (κ == A.val || κ == B.val)) = true) :
    ∀ κ, P κ ↔ κ = A ∨ κ = B := by
  intro κ
  have h1 := List.all_eq_true.1 h κ.val (List.mem_range.2 κ.isLt)
  rw [beq_iff_eq] at h1
  rw [hP, h1, Fin.ext_iff, Fin.ext_iff]
  simp

theorem wcol_of_wN (hel : elOK n el = true) {v : Fin (ofList n el hn).n}
    (D : Ports (fun _ : Fin (ofList n el hn).m => True) v) {cl : List Nat} {i j k : Fin 3}
    (hmc : MCPole D (colF (ofList n el hn).m cl))
    (h : wN el cl v.val (D.p i).val (D.p j).val (D.p k).val = true) :
    WCol D i j k (colF (ofList n el hn).m cl) := by
  have hx : ∀ t, (D.x t).val = oth el (D.p t).val v.val := fun t => ofList_joins_oth hel (D.hj t)
  have hC : ∀ t (κ : Fin 6), vCol D (colF (ofList n el hn).m cl) t κ ↔
      colB el cl (D.p t).val (oth el (D.p t).val v.val) κ.val = true := fun t κ => by
    rw [← hx]; exact vCol_iff_B hel D cl t κ
  have hB : ∀ t (κ : Fin 6), vBlk D (colF (ofList n el hn).m cl) t κ ↔
      blkB el cl (D.p t).val (oth el (D.p t).val v.val) κ.val = true := fun t κ => by
    rw [← hx]; exact vBlk_iff_B hel D cl t κ
  unfold wN at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨hmc, Fin.ext h1, fun e => h2 (congrArg Fin.val e), fun e => h3 (congrArg Fin.val e),
    fun e => h4 (congrArg Fin.val e), fun hb => ?_, fun hb => ?_, ?_⟩
  · exact Bool.noConfusion (((hB j _).1 hb).symm.trans h5)
  · exact Bool.noConfusion (((hB k _).1 hb).symm.trans h6)
  rcases h7 with hSU | hS1
  · left
    exact shape_of_all (A := colF (ofList n el hn).m cl (D.p j)) (B := colF (ofList n el hn).m cl (D.p k)) (hC i) hSU
  · right
    obtain ⟨c, hc6, hc⟩ := List.any_eq_true.1 hS1
    have hc6' := List.mem_range.1 hc6
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
      Bool.and_eq_false_imp] at hc
    obtain ⟨⟨⟨⟨⟨⟨hc5, hcj⟩, hck⟩, hsh⟩, hcj'⟩, hck'⟩, hboth⟩ := hc
    let C : Fin 6 := ⟨c, hc6'⟩
    refine ⟨C, fun e => hc5 (congrArg Fin.val e), fun e => hcj (congrArg Fin.val e),
      fun e => hck (congrArg Fin.val e), ?_, fun hv => ?_, fun hv => ?_, ?_⟩
    · rcases hsh with hs | hs
      · exact Or.inl (shape_of_all (A := colF (ofList n el hn).m cl (D.p j)) (B := C) (hC i) hs)
      · exact Or.inr (shape_of_all (A := colF (ofList n el hn).m cl (D.p k)) (B := C) (hC i) hs)
    · exact Bool.noConfusion (((hC j C).1 hv).symm.trans hcj')
    · exact Bool.noConfusion (((hC k C).1 hv).symm.trans hck')
    · rintro ⟨⟨κ, a1, a2, a3, a4⟩, ⟨κ', b1, b2, b3, b4⟩⟩
      have e1 : (List.range 6).any (fun κ => κ != 5 && κ != colN cl (D.p j).val && κ != colN cl (D.p k).val &&
          colB el cl (D.p j).val (oth el (D.p j).val v.val) κ) = true :=
        List.any_eq_true.2 ⟨κ.val, List.mem_range.2 κ.isLt, by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨⟨⟨fun e => a1 (Fin.ext e), fun e => a2 (Fin.ext e)⟩, fun e => a3 (Fin.ext e)⟩, (hC j κ).1 a4⟩⟩
      have e2 : (List.range 6).any (fun κ => κ != 5 && κ != colN cl (D.p j).val && κ != colN cl (D.p k).val &&
          colB el cl (D.p k).val (oth el (D.p k).val v.val) κ) = true :=
        List.any_eq_true.2 ⟨κ'.val, List.mem_range.2 κ'.isLt, by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨⟨⟨fun e => b1 (Fin.ext e), fun e => b2 (Fin.ext e)⟩, fun e => b3 (Fin.ext e)⟩, (hC k κ').1 b4⟩⟩
      exact absurd (hboth e1) (by rw [e2]; decide)

/-! ### the pole checker -/

/-- the six orderings of the base triple -/
def perms3 (a b c : Nat) : List (Nat × Nat × Nat) :=
  [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)]

theorem perm_mem {a b c x y z : Nat} (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c)
    (hz : z = a ∨ z = b ∨ z = c) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : (x, y, z) ∈ perms3 a b c := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | exact absurd rfl hxz | exact absurd rfl hyz | simp [perms3]

theorem perms3_props {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {t : Nat × Nat × Nat}
    (ht : t ∈ perms3 a b c) : (t.1 = a ∨ t.1 = b ∨ t.1 = c) ∧ (t.2.1 = a ∨ t.2.1 = b ∨ t.2.1 = c) ∧
      (t.2.2 = a ∨ t.2.2 = b ∨ t.2.2 = c) ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  simp only [perms3, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hab, hac, hbc⟩
  · exact ⟨Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), hac, hab, Ne.symm hbc⟩
  · exact ⟨Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (Or.inr rfl), Ne.symm hab, hbc, hac⟩
  · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl, hbc, Ne.symm hab, Ne.symm hac⟩
  · exact ⟨Or.inr (Or.inr rfl), Or.inl rfl, Or.inr (Or.inl rfl), Ne.symm hac, Ne.symm hbc, hab⟩
  · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), Or.inl rfl, Ne.symm hbc, Ne.symm hac, Ne.symm hab⟩

/-- **the pole checker**: the edges at `h0` are exactly the distinct edges `a, b, c`; every listed colouring (with
    its neighbour table) is a star colouring of the base ambient and satisfies the colour-`5` perfect matching
    condition; every ordered triple of ports has a W-colouring in the list; every edge `g` not at `h0` and every
    status `s` has a W-colouring at some ordered triple with `[cl(g) = 5] = s` -/
def poleN (n : Nat) (el : List (Nat × Nat)) (h0 a b c : Nat)
    (cs : List (List Nat × List (List (Nat × Nat × Nat)))) : Bool :=
  (List.range el.length).all (fun f => incN el f h0 == (f == a || f == b || f == c)) &&
  (a != b && a != c && b != c) &&
  cs.all (fun q => fastStar2 (n + 3) (splitL n el h0 a b c) q.2 q.1 && pmN n el h0 q.1) &&
  (perms3 a b c).all (fun t => cs.any (fun q => wN el q.1 h0 t.1 t.2.1 t.2.2)) &&
  (List.range el.length).all (fun g => incN el g h0 || [true, false].all (fun s =>
    cs.any (fun q => (colN q.1 g == 5) == s && (perms3 a b c).any (fun t => wN el q.1 h0 t.1 t.2.1 t.2.2))))

/-- **soundness of the pole checker**: every labelling of the pole is dominant -/
theorem dominant_of_poleN (hel : elOK n el = true) (hG : InG (ofList n el hn) (fun _ => True))
    {v : Fin (ofList n el hn).n} {a b c : Nat} {cs : List (List Nat × List (List (Nat × Nat × Nat)))}
    (h : poleN n el v.val a b c cs = true) (D : Ports (fun _ : Fin (ofList n el hn).m => True) v) :
    Dominant D := by
  unfold poleN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hat, ⟨⟨hab, hac⟩, hbc⟩⟩, hcs⟩, hW⟩, hD2⟩ := h
  simp only [bne_iff_ne, ne_eq] at hab hac hbc
  have hat' : ∀ f, f < el.length → (incN el f v.val = true ↔ (f = a ∨ f = b ∨ f = c)) := by
    intro f hf
    have := List.all_eq_true.1 hat f (List.mem_range.2 hf)
    rw [beq_iff_eq] at this
    rw [this]
    simp [or_assoc]
  have hmc : ∀ q ∈ cs, MCPole D (colF (ofList n el hn).m q.1) := by
    intro q hq
    have := List.all_eq_true.1 hcs q hq
    simp only [Bool.and_eq_true] at this
    exact ⟨star_split hel D hab hac hbc hat' this.1, pm_of_pmN hel D this.2⟩
  have hpv : ∀ t, (D.p t).val = a ∨ (D.p t).val = b ∨ (D.p t).val = c := fun t =>
    (hat' _ (D.p t).isLt).1 ((ofList_inc hel).1 (joins_inc_left (D.hj t)))
  have hpd : ∀ s t, s ≠ t → (D.p s).val ≠ (D.p t).val := fun s t hst h => hst (D.pinj _ _ (Fin.ext h))
  have hperm : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ((D.p i).val, (D.p j).val, (D.p k).val) ∈ perms3 a b c := fun i j k hij hik hjk =>
    perm_mem (hpv i) (hpv j) (hpv k) (hpd _ _ hij) (hpd _ _ hik) (hpd _ _ hjk)
  have hcov : ∀ y, (y = a ∨ y = b ∨ y = c) → ∃ s, (D.p s).val = y := by
    intro y hy
    have d01 := hpd 0 1 (by decide)
    have d02 := hpd 0 2 (by decide)
    have d12 := hpd 1 2 (by decide)
    have e0 := hpv 0
    have e1 := hpv 1
    have e2 := hpv 2
    by_cases h0 : (D.p 0).val = y
    · exact ⟨0, h0⟩
    by_cases h1 : (D.p 1).val = y
    · exact ⟨1, h1⟩
    by_cases h2 : (D.p 2).val = y
    · exact ⟨2, h2⟩
    exfalso; omega
  have hrev : ∀ t ∈ perms3 a b c, ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (D.p i).val = t.1 ∧ (D.p j).val = t.2.1 ∧ (D.p k).val = t.2.2 := by
    intro t ht
    have hmem := perms3_props hab hac hbc ht
    obtain ⟨m1, m2, m3, n12, n13, n23⟩ := hmem
    obtain ⟨i, hi⟩ := hcov _ m1
    obtain ⟨j, hj⟩ := hcov _ m2
    obtain ⟨k, hk⟩ := hcov _ m3
    refine ⟨i, j, k, fun e => n12 ?_, fun e => n13 ?_, fun e => n23 ?_, hi, hj, hk⟩
    · rw [← hi, ← hj, e]
    · rw [← hi, ← hk, e]
    · rw [← hj, ← hk, e]
  refine ⟨fun i => ?_, fun g _ hgv s => ?_⟩
  · obtain ⟨j, k, hij, hik, hjk⟩ := fin3_others i
    obtain ⟨q, hq, hw⟩ := List.any_eq_true.1 (List.all_eq_true.1 hW _ (hperm i j k hij hik hjk))
    exact wred_d1 hG hij hik hjk ⟨_, wcol_of_wN hel D (hmc q hq) hw⟩
  · have hg := List.all_eq_true.1 hD2 g.val (List.mem_range.2 g.isLt)
    have hgi : incN el g.val v.val = false := by
      cases h' : incN el g.val v.val
      · rfl
      · exact absurd ((ofList_inc hel).2 h') hgv
    rw [hgi, Bool.false_or] at hg
    have hs := List.all_eq_true.1 hg s (by cases s <;> simp)
    obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 hs
    simp only [Bool.and_eq_true] at hq'
    obtain ⟨hst, hany⟩ := hq'
    obtain ⟨t, ht, hw⟩ := List.any_eq_true.1 hany
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := hrev t ht
    have hst' : colN q.1 g.val = 5 ↔ s = true := by rw [beq_iff_eq] at hst; rw [← hst]; simp
    refine ⟨i, wred_d2 hG hij hik hjk ⟨_, wcol_of_wN hel D (hmc q hq) (by rw [hi, hj, hk]; exact hw),
      fun h5 => hst'.1 (congrArg Fin.val h5), fun hs' => Fin.ext (hst'.2 hs')⟩⟩

end pd2

end RH2F

-- ===== from PD3.lean =====

/-
  PD3.lean — the certificates of SMALL-PD (A): the prism `Rep 7`, K₃,₃ `Rep 8` and V₈ `Rep 25` at every vertex, and
  K₄ with a digon inserted into the edge `0 1` (`Rep 6`) at the vertices `0` and `1`. For each pole the checker
  `poleN` is evaluated by the kernel on three explicit MC pole colourings (star colourings of the base ambient with
  their neighbour tables); `dominant_of_poleN` then gives dominance for every labelling of the ports.
-/

namespace RH2F
open MGraph

/-- `Rep 6` is a member of 𝒢 (loopless, cubic, connected, bridgeless), from spanning-order certificates -/
theorem repG6_inG : InG (repG 6) (fun _ => True) :=
  ofList_inG (n := repN 6) (el := repL 6) (hn := repN_pos 6) (by decide) (by decide +kernel) (r := 0)
    (ord := [2, 3, 4, 1, 5]) (by decide +kernel)
    (ords := [[2, 3, 4, 1, 5], [2, 3, 4, 1, 5], [3, 4, 1, 2, 5], [2, 3, 4, 1, 5], [2, 4, 1, 3, 5], [2, 3, 1, 5, 4], [2, 3, 4, 1, 5], [2, 3, 4, 1, 5], [2, 3, 4, 1, 5]]) (by decide +kernel)

/-- `Rep 7` is a member of 𝒢 (loopless, cubic, connected, bridgeless), from spanning-order certificates -/
theorem repG7_inG : InG (repG 7) (fun _ => True) :=
  ofList_inG (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) (by decide +kernel) (r := 0)
    (ord := [1, 4, 5, 2, 3]) (by decide +kernel)
    (ords := [[4, 5, 2, 3, 1], [1, 4, 5, 3, 2], [1, 4, 5, 2, 3], [1, 4, 5, 2, 3], [1, 4, 5, 2, 3], [1, 4, 5, 2, 3], [1, 5, 2, 3, 4], [1, 4, 5, 2, 3], [1, 4, 2, 3, 5]]) (by decide +kernel)

/-- `Rep 8` is a member of 𝒢 (loopless, cubic, connected, bridgeless), from spanning-order certificates -/
theorem repG8_inG : InG (repG 8) (fun _ => True) :=
  ofList_inG (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) (by decide +kernel) (r := 0)
    (ord := [3, 4, 5, 1, 2]) (by decide +kernel)
    (ords := [[4, 5, 1, 2, 3], [3, 5, 1, 2, 4], [3, 4, 1, 2, 5], [3, 4, 5, 2, 1], [3, 4, 5, 1, 2], [3, 4, 5, 1, 2], [3, 4, 5, 1, 2], [3, 4, 5, 1, 2], [3, 4, 5, 1, 2]]) (by decide +kernel)

/-- `Rep 25` is a member of 𝒢 (loopless, cubic, connected, bridgeless), from spanning-order certificates -/
theorem repG25_inG : InG (repG 25) (fun _ => True) :=
  ofList_inG (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) (by decide +kernel) (r := 0)
    (ord := [1, 2, 3, 5, 7, 6, 4]) (by decide +kernel)
    (ords := [[2, 3, 6, 4, 7, 5, 1], [1, 3, 5, 7, 4, 6, 2], [1, 2, 5, 7, 6, 4, 3], [1, 2, 3, 5, 7, 6, 4], [1, 2, 3, 5, 7, 6, 4], [1, 2, 3, 5, 7, 6, 4], [1, 2, 3, 7, 6, 4, 5], [1, 2, 3, 5, 7, 4, 6], [1, 2, 3, 5, 7, 6, 4], [1, 2, 3, 5, 7, 6, 4], [1, 2, 3, 5, 6, 4, 7], [1, 2, 3, 5, 7, 6, 4]]) (by decide +kernel)

/-- the certificate list for the pole of `Rep 6` at vertex `0` (ports `2`, `4`, `5`) -/
def cs6_0 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 2, 5, 3, 5, 2, 3, 5], [[], [(0, 2, 0), (1, 3, 1), (8, 5, 5)], [(0, 1, 0), (2, 6, 2), (3, 3, 5)], [(1, 1, 1), (3, 2, 5), (4, 7, 3)], [(5, 8, 5), (6, 5, 2), (7, 5, 3)], [(6, 4, 2), (7, 4, 3), (8, 1, 5)], [(2, 2, 2)], [(4, 3, 3)], [(5, 4, 5)]]),
    ([0, 5, 5, 1, 2, 1, 2, 5, 3], [[], [(0, 2, 0), (1, 3, 5), (8, 5, 3)], [(0, 1, 0), (2, 6, 5), (3, 3, 1)], [(1, 1, 5), (3, 2, 1), (4, 7, 2)], [(5, 8, 1), (6, 5, 2), (7, 5, 5)], [(6, 4, 2), (7, 4, 5), (8, 1, 3)], [(2, 2, 5)], [(4, 3, 2)], [(5, 4, 1)]]),
    ([5, 0, 1, 2, 5, 2, 5, 1, 3], [[], [(0, 2, 5), (1, 3, 0), (8, 5, 3)], [(0, 1, 5), (2, 6, 1), (3, 3, 2)], [(1, 1, 0), (3, 2, 2), (4, 7, 5)], [(5, 8, 2), (6, 5, 5), (7, 5, 1)], [(6, 4, 5), (7, 4, 1), (8, 1, 3)], [(2, 2, 1)], [(4, 3, 5)], [(5, 4, 2)]])]

theorem chk6_0 : poleN (repN 6) (repL 6) 0 2 4 5 cs6_0 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 6` at vertex `1` (ports `0`, `1`, `8`) -/
def cs6_1 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 2, 5, 3, 5, 0, 1, 5], [[(2, 2, 2), (4, 3, 3), (5, 4, 5)], [], [(0, 6, 0), (2, 0, 2), (3, 3, 5)], [(1, 7, 1), (3, 2, 5), (4, 0, 3)], [(5, 0, 5), (6, 5, 0), (7, 5, 1)], [(6, 4, 0), (7, 4, 1), (8, 8, 5)], [(0, 2, 0)], [(1, 3, 1)], [(8, 5, 5)]]),
    ([0, 5, 5, 1, 2, 3, 0, 5, 1], [[(2, 2, 5), (4, 3, 2), (5, 4, 3)], [], [(0, 6, 0), (2, 0, 5), (3, 3, 1)], [(1, 7, 5), (3, 2, 1), (4, 0, 2)], [(5, 0, 3), (6, 5, 0), (7, 5, 5)], [(6, 4, 0), (7, 4, 5), (8, 8, 1)], [(0, 2, 0)], [(1, 3, 5)], [(8, 5, 1)]]),
    ([5, 0, 1, 2, 5, 3, 5, 0, 2], [[(2, 2, 1), (4, 3, 5), (5, 4, 3)], [], [(0, 6, 5), (2, 0, 1), (3, 3, 2)], [(1, 7, 0), (3, 2, 2), (4, 0, 5)], [(5, 0, 3), (6, 5, 5), (7, 5, 0)], [(6, 4, 5), (7, 4, 0), (8, 8, 2)], [(0, 2, 5)], [(1, 3, 0)], [(8, 5, 2)]])]

theorem chk6_1 : poleN (repN 6) (repL 6) 1 0 1 8 cs6_1 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 7` at vertex `0` (ports `0`, `6`, `8`) -/
def cs7_0 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 5, 2, 3, 4, 0, 5], [[], [(0, 6, 0), (1, 2, 1), (2, 3, 5)], [(1, 1, 1), (3, 4, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 5, 3)], [(3, 2, 5), (6, 7, 4), (7, 5, 0)], [(5, 3, 3), (7, 4, 0), (8, 8, 5)], [(0, 1, 0)], [(6, 4, 4)], [(8, 5, 5)]]),
    ([0, 5, 1, 2, 3, 5, 5, 0, 4], [[], [(0, 6, 0), (1, 2, 5), (2, 3, 1)], [(1, 1, 5), (3, 4, 2), (4, 3, 3)], [(2, 1, 1), (4, 2, 3), (5, 5, 5)], [(3, 2, 2), (6, 7, 5), (7, 5, 0)], [(5, 3, 5), (7, 4, 0), (8, 8, 4)], [(0, 1, 0)], [(6, 4, 5)], [(8, 5, 4)]]),
    ([5, 0, 1, 2, 5, 3, 0, 5, 1], [[], [(0, 6, 5), (1, 2, 0), (2, 3, 1)], [(1, 1, 0), (3, 4, 2), (4, 3, 5)], [(2, 1, 1), (4, 2, 5), (5, 5, 3)], [(3, 2, 2), (6, 7, 0), (7, 5, 5)], [(5, 3, 3), (7, 4, 5), (8, 8, 1)], [(0, 1, 5)], [(6, 4, 0)], [(8, 5, 1)]])]

theorem chk7_0 : poleN (repN 7) (repL 7) 0 0 6 8 cs7_0 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 7` at vertex `1` (ports `0`, `1`, `2`) -/
def cs7_1 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 5, 0, 2, 3, 4, 5], [[(0, 6, 0), (6, 4, 3), (8, 5, 5)], [], [(1, 7, 1), (3, 4, 5), (4, 3, 0)], [(2, 8, 5), (4, 2, 0), (5, 5, 2)], [(3, 2, 5), (6, 0, 3), (7, 5, 4)], [(5, 3, 2), (7, 4, 4), (8, 0, 5)], [(0, 0, 0)], [(1, 2, 1)], [(2, 3, 5)]]),
    ([0, 5, 1, 2, 0, 5, 5, 3, 4], [[(0, 6, 0), (6, 4, 5), (8, 5, 4)], [], [(1, 7, 5), (3, 4, 2), (4, 3, 0)], [(2, 8, 1), (4, 2, 0), (5, 5, 5)], [(3, 2, 2), (6, 0, 5), (7, 5, 3)], [(5, 3, 5), (7, 4, 3), (8, 0, 4)], [(0, 0, 0)], [(1, 2, 5)], [(2, 3, 1)]]),
    ([5, 0, 1, 2, 5, 3, 0, 5, 1], [[(0, 6, 5), (6, 4, 0), (8, 5, 1)], [], [(1, 7, 0), (3, 4, 2), (4, 3, 5)], [(2, 8, 1), (4, 2, 5), (5, 5, 3)], [(3, 2, 2), (6, 0, 0), (7, 5, 5)], [(5, 3, 3), (7, 4, 5), (8, 0, 1)], [(0, 0, 5)], [(1, 2, 0)], [(2, 3, 1)]])]

theorem chk7_1 : poleN (repN 7) (repL 7) 1 0 1 2 cs7_1 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 7` at vertex `2` (ports `1`, `3`, `4`) -/
def cs7_2 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 5, 2, 3, 1, 2, 5], [[(0, 1, 0), (6, 4, 1), (8, 5, 5)], [(0, 0, 0), (1, 6, 1), (2, 3, 5)], [], [(2, 1, 5), (4, 8, 2), (5, 5, 3)], [(3, 7, 5), (6, 0, 1), (7, 5, 2)], [(5, 3, 3), (7, 4, 2), (8, 0, 5)], [(1, 1, 1)], [(3, 4, 5)], [(4, 3, 2)]]),
    ([0, 5, 1, 1, 2, 5, 5, 3, 4], [[(0, 1, 0), (6, 4, 5), (8, 5, 4)], [(0, 0, 0), (1, 6, 5), (2, 3, 1)], [], [(2, 1, 1), (4, 8, 2), (5, 5, 5)], [(3, 7, 1), (6, 0, 5), (7, 5, 3)], [(5, 3, 5), (7, 4, 3), (8, 0, 4)], [(1, 1, 5)], [(3, 4, 1)], [(4, 3, 2)]]),
    ([5, 0, 1, 1, 5, 2, 3, 5, 4], [[(0, 1, 5), (6, 4, 3), (8, 5, 4)], [(0, 0, 5), (1, 6, 0), (2, 3, 1)], [], [(2, 1, 1), (4, 8, 5), (5, 5, 2)], [(3, 7, 1), (6, 0, 3), (7, 5, 5)], [(5, 3, 2), (7, 4, 5), (8, 0, 4)], [(1, 1, 0)], [(3, 4, 1)], [(4, 3, 5)]])]

theorem chk7_2 : poleN (repN 7) (repL 7) 2 1 3 4 cs7_2 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 7` at vertex `3` (ports `2`, `4`, `5`) -/
def cs7_3 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 5, 2, 1, 3, 4, 5], [[(0, 1, 0), (6, 4, 3), (8, 5, 5)], [(0, 0, 0), (1, 2, 1), (2, 6, 5)], [(1, 1, 1), (3, 4, 5), (4, 7, 2)], [], [(3, 2, 5), (6, 0, 3), (7, 5, 4)], [(5, 8, 1), (7, 4, 4), (8, 0, 5)], [(2, 1, 5)], [(4, 2, 2)], [(5, 5, 1)]]),
    ([0, 5, 1, 2, 3, 5, 5, 1, 3], [[(0, 1, 0), (6, 4, 5), (8, 5, 3)], [(0, 0, 0), (1, 2, 5), (2, 6, 1)], [(1, 1, 5), (3, 4, 2), (4, 7, 3)], [], [(3, 2, 2), (6, 0, 5), (7, 5, 1)], [(5, 8, 5), (7, 4, 1), (8, 0, 3)], [(2, 1, 1)], [(4, 2, 3)], [(5, 5, 5)]]),
    ([5, 0, 1, 2, 5, 0, 3, 5, 4], [[(0, 1, 5), (6, 4, 3), (8, 5, 4)], [(0, 0, 5), (1, 2, 0), (2, 6, 1)], [(1, 1, 0), (3, 4, 2), (4, 7, 5)], [], [(3, 2, 2), (6, 0, 3), (7, 5, 5)], [(5, 8, 0), (7, 4, 5), (8, 0, 4)], [(2, 1, 1)], [(4, 2, 5)], [(5, 5, 0)]])]

theorem chk7_3 : poleN (repN 7) (repL 7) 3 2 4 5 cs7_3 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 7` at vertex `4` (ports `3`, `6`, `7`) -/
def cs7_4 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 5, 2, 3, 1, 2, 5], [[(0, 1, 0), (6, 7, 1), (8, 5, 5)], [(0, 0, 0), (1, 2, 1), (2, 3, 5)], [(1, 1, 1), (3, 6, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 5, 3)], [], [(5, 3, 3), (7, 8, 2), (8, 0, 5)], [(3, 2, 5)], [(6, 0, 1)], [(7, 5, 2)]]),
    ([0, 5, 1, 2, 3, 5, 5, 4, 2], [[(0, 1, 0), (6, 7, 5), (8, 5, 2)], [(0, 0, 0), (1, 2, 5), (2, 3, 1)], [(1, 1, 5), (3, 6, 2), (4, 3, 3)], [(2, 1, 1), (4, 2, 3), (5, 5, 5)], [], [(5, 3, 5), (7, 8, 4), (8, 0, 2)], [(3, 2, 2)], [(6, 0, 5)], [(7, 5, 4)]]),
    ([5, 0, 1, 2, 5, 3, 4, 5, 2], [[(0, 1, 5), (6, 7, 4), (8, 5, 2)], [(0, 0, 5), (1, 2, 0), (2, 3, 1)], [(1, 1, 0), (3, 6, 2), (4, 3, 5)], [(2, 1, 1), (4, 2, 5), (5, 5, 3)], [], [(5, 3, 3), (7, 8, 5), (8, 0, 2)], [(3, 2, 2)], [(6, 0, 4)], [(7, 5, 5)]])]

theorem chk7_4 : poleN (repN 7) (repL 7) 4 3 6 7 cs7_4 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 7` at vertex `5` (ports `5`, `7`, `8`) -/
def cs7_5 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 5, 2, 3, 3, 4, 5], [[(0, 1, 0), (6, 4, 3), (8, 8, 5)], [(0, 0, 0), (1, 2, 1), (2, 3, 5)], [(1, 1, 1), (3, 4, 5), (4, 3, 2)], [(2, 1, 5), (4, 2, 2), (5, 6, 3)], [(3, 2, 5), (6, 0, 3), (7, 7, 4)], [], [(5, 3, 3)], [(7, 4, 4)], [(8, 0, 5)]]),
    ([0, 5, 1, 2, 3, 5, 5, 1, 3], [[(0, 1, 0), (6, 4, 5), (8, 8, 3)], [(0, 0, 0), (1, 2, 5), (2, 3, 1)], [(1, 1, 5), (3, 4, 2), (4, 3, 3)], [(2, 1, 1), (4, 2, 3), (5, 6, 5)], [(3, 2, 2), (6, 0, 5), (7, 7, 1)], [], [(5, 3, 5)], [(7, 4, 1)], [(8, 0, 3)]]),
    ([5, 0, 1, 2, 5, 3, 3, 5, 4], [[(0, 1, 5), (6, 4, 3), (8, 8, 4)], [(0, 0, 5), (1, 2, 0), (2, 3, 1)], [(1, 1, 0), (3, 4, 2), (4, 3, 5)], [(2, 1, 1), (4, 2, 5), (5, 6, 3)], [(3, 2, 2), (6, 0, 3), (7, 7, 5)], [], [(5, 3, 3)], [(7, 4, 5)], [(8, 0, 4)]])]

theorem chk7_5 : poleN (repN 7) (repL 7) 5 5 7 8 cs7_5 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 8` at vertex `0` (ports `0`, `1`, `2`) -/
def cs8_0 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 2, 5, 0, 5, 3, 1], [[], [(3, 3, 2), (4, 4, 5), (5, 5, 0)], [(6, 3, 5), (7, 4, 3), (8, 5, 1)], [(0, 6, 0), (3, 1, 2), (6, 2, 5)], [(1, 7, 1), (4, 1, 5), (7, 2, 3)], [(2, 8, 5), (5, 1, 0), (8, 2, 1)], [(0, 3, 0)], [(1, 4, 1)], [(2, 5, 5)]]),
    ([0, 5, 1, 5, 1, 2, 3, 0, 5], [[], [(3, 3, 5), (4, 4, 1), (5, 5, 2)], [(6, 3, 3), (7, 4, 0), (8, 5, 5)], [(0, 6, 0), (3, 1, 5), (6, 2, 3)], [(1, 7, 5), (4, 1, 1), (7, 2, 0)], [(2, 8, 1), (5, 1, 2), (8, 2, 5)], [(0, 3, 0)], [(1, 4, 5)], [(2, 5, 1)]]),
    ([5, 0, 1, 0, 2, 5, 1, 5, 3], [[], [(3, 3, 0), (4, 4, 2), (5, 5, 5)], [(6, 3, 1), (7, 4, 5), (8, 5, 3)], [(0, 6, 5), (3, 1, 0), (6, 2, 1)], [(1, 7, 0), (4, 1, 2), (7, 2, 5)], [(2, 8, 1), (5, 1, 5), (8, 2, 3)], [(0, 3, 5)], [(1, 4, 0)], [(2, 5, 1)]])]

theorem chk8_0 : poleN (repN 8) (repL 8) 0 0 1 2 cs8_0 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 8` at vertex `1` (ports `3`, `4`, `5`) -/
def cs8_1 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 1, 5, 2, 5, 2, 3], [[(0, 3, 0), (1, 4, 1), (2, 5, 5)], [], [(6, 3, 5), (7, 4, 2), (8, 5, 3)], [(0, 0, 0), (3, 6, 1), (6, 2, 5)], [(1, 0, 1), (4, 7, 5), (7, 2, 2)], [(2, 0, 5), (5, 8, 2), (8, 2, 3)], [(3, 3, 1)], [(4, 4, 5)], [(5, 5, 2)]]),
    ([0, 5, 1, 5, 2, 0, 2, 3, 5], [[(0, 3, 0), (1, 4, 5), (2, 5, 1)], [], [(6, 3, 2), (7, 4, 3), (8, 5, 5)], [(0, 0, 0), (3, 6, 5), (6, 2, 2)], [(1, 0, 5), (4, 7, 2), (7, 2, 3)], [(2, 0, 1), (5, 8, 0), (8, 2, 5)], [(3, 3, 5)], [(4, 4, 2)], [(5, 5, 0)]]),
    ([5, 0, 1, 2, 1, 5, 3, 5, 2], [[(0, 3, 5), (1, 4, 0), (2, 5, 1)], [], [(6, 3, 3), (7, 4, 5), (8, 5, 2)], [(0, 0, 5), (3, 6, 2), (6, 2, 3)], [(1, 0, 0), (4, 7, 1), (7, 2, 5)], [(2, 0, 1), (5, 8, 5), (8, 2, 2)], [(3, 3, 2)], [(4, 4, 1)], [(5, 5, 5)]])]

theorem chk8_1 : poleN (repN 8) (repL 8) 1 3 4 5 cs8_1 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 8` at vertex `2` (ports `6`, `7`, `8`) -/
def cs8_2 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 2, 5, 3, 5, 0, 2], [[(0, 3, 0), (1, 4, 1), (2, 5, 5)], [(3, 3, 2), (4, 4, 5), (5, 5, 3)], [], [(0, 0, 0), (3, 1, 2), (6, 6, 5)], [(1, 0, 1), (4, 1, 5), (7, 7, 0)], [(2, 0, 5), (5, 1, 3), (8, 8, 2)], [(6, 3, 5)], [(7, 4, 0)], [(8, 5, 2)]]),
    ([0, 5, 1, 5, 2, 3, 1, 3, 5], [[(0, 3, 0), (1, 4, 5), (2, 5, 1)], [(3, 3, 5), (4, 4, 2), (5, 5, 3)], [], [(0, 0, 0), (3, 1, 5), (6, 6, 1)], [(1, 0, 5), (4, 1, 2), (7, 7, 3)], [(2, 0, 1), (5, 1, 3), (8, 8, 5)], [(6, 3, 1)], [(7, 4, 3)], [(8, 5, 5)]]),
    ([5, 0, 1, 2, 3, 5, 3, 5, 0], [[(0, 3, 5), (1, 4, 0), (2, 5, 1)], [(3, 3, 2), (4, 4, 3), (5, 5, 5)], [], [(0, 0, 5), (3, 1, 2), (6, 6, 3)], [(1, 0, 0), (4, 1, 3), (7, 7, 5)], [(2, 0, 1), (5, 1, 5), (8, 8, 0)], [(6, 3, 3)], [(7, 4, 5)], [(8, 5, 0)]])]

theorem chk8_2 : poleN (repN 8) (repL 8) 2 6 7 8 cs8_2 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 8` at vertex `3` (ports `0`, `3`, `6`) -/
def cs8_3 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 2, 5, 3, 5, 0, 2], [[(0, 6, 0), (1, 4, 1), (2, 5, 5)], [(3, 7, 2), (4, 4, 5), (5, 5, 3)], [(6, 8, 5), (7, 4, 0), (8, 5, 2)], [], [(1, 0, 1), (4, 1, 5), (7, 2, 0)], [(2, 0, 5), (5, 1, 3), (8, 2, 2)], [(0, 0, 0)], [(3, 1, 2)], [(6, 2, 5)]]),
    ([0, 5, 1, 5, 2, 0, 2, 3, 5], [[(0, 6, 0), (1, 4, 5), (2, 5, 1)], [(3, 7, 5), (4, 4, 2), (5, 5, 0)], [(6, 8, 2), (7, 4, 3), (8, 5, 5)], [], [(1, 0, 5), (4, 1, 2), (7, 2, 3)], [(2, 0, 1), (5, 1, 0), (8, 2, 5)], [(0, 0, 0)], [(3, 1, 5)], [(6, 2, 2)]]),
    ([5, 0, 1, 0, 2, 5, 1, 5, 3], [[(0, 6, 5), (1, 4, 0), (2, 5, 1)], [(3, 7, 0), (4, 4, 2), (5, 5, 5)], [(6, 8, 1), (7, 4, 5), (8, 5, 3)], [], [(1, 0, 0), (4, 1, 2), (7, 2, 5)], [(2, 0, 1), (5, 1, 5), (8, 2, 3)], [(0, 0, 5)], [(3, 1, 0)], [(6, 2, 1)]])]

theorem chk8_3 : poleN (repN 8) (repL 8) 3 0 3 6 cs8_3 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 8` at vertex `4` (ports `1`, `4`, `7`) -/
def cs8_4 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 1, 5, 2, 5, 2, 3], [[(0, 3, 0), (1, 6, 1), (2, 5, 5)], [(3, 3, 1), (4, 7, 5), (5, 5, 2)], [(6, 3, 5), (7, 8, 2), (8, 5, 3)], [(0, 0, 0), (3, 1, 1), (6, 2, 5)], [], [(2, 0, 5), (5, 1, 2), (8, 2, 3)], [(1, 0, 1)], [(4, 1, 5)], [(7, 2, 2)]]),
    ([0, 5, 1, 5, 1, 2, 3, 0, 5], [[(0, 3, 0), (1, 6, 5), (2, 5, 1)], [(3, 3, 5), (4, 7, 1), (5, 5, 2)], [(6, 3, 3), (7, 8, 0), (8, 5, 5)], [(0, 0, 0), (3, 1, 5), (6, 2, 3)], [], [(2, 0, 1), (5, 1, 2), (8, 2, 5)], [(1, 0, 5)], [(4, 1, 1)], [(7, 2, 0)]]),
    ([5, 0, 1, 2, 3, 5, 3, 5, 0], [[(0, 3, 5), (1, 6, 0), (2, 5, 1)], [(3, 3, 2), (4, 7, 3), (5, 5, 5)], [(6, 3, 3), (7, 8, 5), (8, 5, 0)], [(0, 0, 5), (3, 1, 2), (6, 2, 3)], [], [(2, 0, 1), (5, 1, 5), (8, 2, 0)], [(1, 0, 0)], [(4, 1, 3)], [(7, 2, 5)]])]

theorem chk8_4 : poleN (repN 8) (repL 8) 4 1 4 7 cs8_4 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 8` at vertex `5` (ports `2`, `5`, `8`) -/
def cs8_5 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 2, 5, 0, 5, 3, 1], [[(0, 3, 0), (1, 4, 1), (2, 6, 5)], [(3, 3, 2), (4, 4, 5), (5, 7, 0)], [(6, 3, 5), (7, 4, 3), (8, 8, 1)], [(0, 0, 0), (3, 1, 2), (6, 2, 5)], [(1, 0, 1), (4, 1, 5), (7, 2, 3)], [], [(2, 0, 5)], [(5, 1, 0)], [(8, 2, 1)]]),
    ([0, 5, 1, 5, 2, 3, 1, 3, 5], [[(0, 3, 0), (1, 4, 5), (2, 6, 1)], [(3, 3, 5), (4, 4, 2), (5, 7, 3)], [(6, 3, 1), (7, 4, 3), (8, 8, 5)], [(0, 0, 0), (3, 1, 5), (6, 2, 1)], [(1, 0, 5), (4, 1, 2), (7, 2, 3)], [], [(2, 0, 1)], [(5, 1, 3)], [(8, 2, 5)]]),
    ([5, 0, 1, 2, 1, 5, 3, 5, 2], [[(0, 3, 5), (1, 4, 0), (2, 6, 1)], [(3, 3, 2), (4, 4, 1), (5, 7, 5)], [(6, 3, 3), (7, 4, 5), (8, 8, 2)], [(0, 0, 5), (3, 1, 2), (6, 2, 3)], [(1, 0, 0), (4, 1, 1), (7, 2, 5)], [], [(2, 0, 1)], [(5, 1, 5)], [(8, 2, 2)]])]

theorem chk8_5 : poleN (repN 8) (repL 8) 5 2 5 8 cs8_5 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `0` (ports `0`, `1`, `2`) -/
def cs25_0 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 2, 3, 5, 5, 0, 5, 3, 4, 1], [[], [(0, 8, 0), (6, 5, 5), (10, 7, 4)], [(1, 9, 1), (7, 6, 0), (8, 4, 5)], [(2, 10, 5), (9, 4, 3), (11, 7, 1)], [(3, 5, 2), (8, 2, 5), (9, 3, 3)], [(3, 4, 2), (4, 6, 3), (6, 1, 5)], [(4, 5, 3), (5, 7, 5), (7, 2, 0)], [(5, 6, 5), (10, 1, 4), (11, 3, 1)], [(0, 1, 0)], [(1, 2, 1)], [(2, 3, 5)]]),
    ([0, 5, 1, 2, 5, 3, 1, 0, 3, 5, 5, 4], [[], [(0, 8, 0), (6, 5, 1), (10, 7, 5)], [(1, 9, 5), (7, 6, 0), (8, 4, 3)], [(2, 10, 1), (9, 4, 5), (11, 7, 4)], [(3, 5, 2), (8, 2, 3), (9, 3, 5)], [(3, 4, 2), (4, 6, 5), (6, 1, 1)], [(4, 5, 5), (5, 7, 3), (7, 2, 0)], [(5, 6, 3), (10, 1, 5), (11, 3, 4)], [(0, 1, 0)], [(1, 2, 5)], [(2, 3, 1)]]),
    ([5, 0, 1, 5, 2, 3, 0, 5, 1, 4, 2, 5], [[], [(0, 8, 5), (6, 5, 0), (10, 7, 2)], [(1, 9, 0), (7, 6, 5), (8, 4, 1)], [(2, 10, 1), (9, 4, 4), (11, 7, 5)], [(3, 5, 5), (8, 2, 1), (9, 3, 4)], [(3, 4, 5), (4, 6, 2), (6, 1, 0)], [(4, 5, 2), (5, 7, 3), (7, 2, 5)], [(5, 6, 3), (10, 1, 2), (11, 3, 5)], [(0, 1, 5)], [(1, 2, 0)], [(2, 3, 1)]])]

theorem chk25_0 : poleN (repN 25) (repL 25) 0 0 1 2 cs25_0 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `1` (ports `0`, `6`, `10`) -/
def cs25_1 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 0, 2, 5, 5, 3, 5, 2, 1, 4], [[(0, 8, 0), (1, 2, 1), (2, 3, 5)], [], [(1, 0, 1), (7, 6, 3), (8, 4, 5)], [(2, 0, 5), (9, 4, 2), (11, 7, 4)], [(3, 5, 0), (8, 2, 5), (9, 3, 2)], [(3, 4, 0), (4, 6, 2), (6, 9, 5)], [(4, 5, 2), (5, 7, 5), (7, 2, 3)], [(5, 6, 5), (10, 10, 1), (11, 3, 4)], [(0, 0, 0)], [(6, 5, 5)], [(10, 7, 1)]]),
    ([0, 5, 1, 0, 5, 2, 3, 4, 2, 5, 5, 3], [[(0, 8, 0), (1, 2, 5), (2, 3, 1)], [], [(1, 0, 5), (7, 6, 4), (8, 4, 2)], [(2, 0, 1), (9, 4, 5), (11, 7, 3)], [(3, 5, 0), (8, 2, 2), (9, 3, 5)], [(3, 4, 0), (4, 6, 5), (6, 9, 3)], [(4, 5, 5), (5, 7, 2), (7, 2, 4)], [(5, 6, 2), (10, 10, 5), (11, 3, 3)], [(0, 0, 0)], [(6, 5, 3)], [(10, 7, 5)]]),
    ([5, 0, 1, 5, 2, 3, 0, 5, 1, 4, 2, 5], [[(0, 8, 5), (1, 2, 0), (2, 3, 1)], [], [(1, 0, 0), (7, 6, 5), (8, 4, 1)], [(2, 0, 1), (9, 4, 4), (11, 7, 5)], [(3, 5, 5), (8, 2, 1), (9, 3, 4)], [(3, 4, 5), (4, 6, 2), (6, 9, 0)], [(4, 5, 2), (5, 7, 3), (7, 2, 5)], [(5, 6, 3), (10, 10, 2), (11, 3, 5)], [(0, 0, 5)], [(6, 5, 0)], [(10, 7, 2)]])]

theorem chk25_1 : poleN (repN 25) (repL 25) 1 0 6 10 cs25_1 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `2` (ports `1`, `7`, `8`) -/
def cs25_2 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 1, 2, 5, 5, 0, 5, 3, 3, 4], [[(0, 1, 0), (1, 8, 1), (2, 3, 5)], [(0, 0, 0), (6, 5, 5), (10, 7, 3)], [], [(2, 0, 5), (9, 4, 3), (11, 7, 4)], [(3, 5, 1), (8, 10, 5), (9, 3, 3)], [(3, 4, 1), (4, 6, 2), (6, 1, 5)], [(4, 5, 2), (5, 7, 5), (7, 9, 0)], [(5, 6, 5), (10, 1, 3), (11, 3, 4)], [(1, 0, 1)], [(7, 6, 0)], [(8, 4, 5)]]),
    ([0, 5, 1, 2, 5, 3, 1, 0, 3, 5, 5, 4], [[(0, 1, 0), (1, 8, 5), (2, 3, 1)], [(0, 0, 0), (6, 5, 1), (10, 7, 5)], [], [(2, 0, 1), (9, 4, 5), (11, 7, 4)], [(3, 5, 2), (8, 10, 3), (9, 3, 5)], [(3, 4, 2), (4, 6, 5), (6, 1, 1)], [(4, 5, 5), (5, 7, 3), (7, 9, 0)], [(5, 6, 3), (10, 1, 5), (11, 3, 4)], [(1, 0, 5)], [(7, 6, 0)], [(8, 4, 3)]]),
    ([5, 0, 1, 5, 0, 2, 2, 5, 1, 3, 4, 5], [[(0, 1, 5), (1, 8, 0), (2, 3, 1)], [(0, 0, 5), (6, 5, 2), (10, 7, 4)], [], [(2, 0, 1), (9, 4, 3), (11, 7, 5)], [(3, 5, 5), (8, 10, 1), (9, 3, 3)], [(3, 4, 5), (4, 6, 0), (6, 1, 2)], [(4, 5, 0), (5, 7, 2), (7, 9, 5)], [(5, 6, 2), (10, 1, 4), (11, 3, 5)], [(1, 0, 0)], [(7, 6, 5)], [(8, 4, 1)]])]

theorem chk25_2 : poleN (repN 25) (repL 25) 2 1 7 8 cs25_2 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `3` (ports `2`, `9`, `11`) -/
def cs25_3 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 2, 1, 5, 5, 3, 5, 0, 4, 2], [[(0, 1, 0), (1, 2, 1), (2, 8, 5)], [(0, 0, 0), (6, 5, 5), (10, 7, 4)], [(1, 0, 1), (7, 6, 3), (8, 4, 5)], [], [(3, 5, 2), (8, 2, 5), (9, 9, 0)], [(3, 4, 2), (4, 6, 1), (6, 1, 5)], [(4, 5, 1), (5, 7, 5), (7, 2, 3)], [(5, 6, 5), (10, 1, 4), (11, 10, 2)], [(2, 0, 5)], [(9, 4, 0)], [(11, 7, 2)]]),
    ([0, 5, 1, 2, 5, 1, 3, 4, 3, 5, 5, 2], [[(0, 1, 0), (1, 2, 5), (2, 8, 1)], [(0, 0, 0), (6, 5, 3), (10, 7, 5)], [(1, 0, 5), (7, 6, 4), (8, 4, 3)], [], [(3, 5, 2), (8, 2, 3), (9, 9, 5)], [(3, 4, 2), (4, 6, 5), (6, 1, 3)], [(4, 5, 5), (5, 7, 1), (7, 2, 4)], [(5, 6, 1), (10, 1, 5), (11, 10, 2)], [(2, 0, 1)], [(9, 4, 5)], [(11, 7, 2)]]),
    ([5, 0, 1, 5, 2, 1, 3, 5, 4, 0, 2, 5], [[(0, 1, 5), (1, 2, 0), (2, 8, 1)], [(0, 0, 5), (6, 5, 3), (10, 7, 2)], [(1, 0, 0), (7, 6, 5), (8, 4, 4)], [], [(3, 5, 5), (8, 2, 4), (9, 9, 0)], [(3, 4, 5), (4, 6, 2), (6, 1, 3)], [(4, 5, 2), (5, 7, 1), (7, 2, 5)], [(5, 6, 1), (10, 1, 2), (11, 10, 5)], [(2, 0, 1)], [(9, 4, 0)], [(11, 7, 5)]])]

theorem chk25_3 : poleN (repN 25) (repL 25) 3 2 9 11 cs25_3 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `4` (ports `3`, `8`, `9`) -/
def cs25_4 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 1, 2, 5, 5, 0, 5, 2, 3, 4], [[(0, 1, 0), (1, 2, 1), (2, 3, 5)], [(0, 0, 0), (6, 5, 5), (10, 7, 3)], [(1, 0, 1), (7, 6, 0), (8, 9, 5)], [(2, 0, 5), (9, 10, 2), (11, 7, 4)], [], [(3, 8, 1), (4, 6, 2), (6, 1, 5)], [(4, 5, 2), (5, 7, 5), (7, 2, 0)], [(5, 6, 5), (10, 1, 3), (11, 3, 4)], [(3, 5, 1)], [(8, 2, 5)], [(9, 3, 2)]]),
    ([0, 5, 1, 2, 5, 1, 3, 4, 3, 5, 5, 2], [[(0, 1, 0), (1, 2, 5), (2, 3, 1)], [(0, 0, 0), (6, 5, 3), (10, 7, 5)], [(1, 0, 5), (7, 6, 4), (8, 9, 3)], [(2, 0, 1), (9, 10, 5), (11, 7, 2)], [], [(3, 8, 2), (4, 6, 5), (6, 1, 3)], [(4, 5, 5), (5, 7, 1), (7, 2, 4)], [(5, 6, 1), (10, 1, 5), (11, 3, 2)], [(3, 5, 2)], [(8, 2, 3)], [(9, 3, 5)]]),
    ([5, 0, 1, 5, 2, 3, 3, 5, 1, 2, 4, 5], [[(0, 1, 5), (1, 2, 0), (2, 3, 1)], [(0, 0, 5), (6, 5, 3), (10, 7, 4)], [(1, 0, 0), (7, 6, 5), (8, 9, 1)], [(2, 0, 1), (9, 10, 2), (11, 7, 5)], [], [(3, 8, 5), (4, 6, 2), (6, 1, 3)], [(4, 5, 2), (5, 7, 3), (7, 2, 5)], [(5, 6, 3), (10, 1, 4), (11, 3, 5)], [(3, 5, 5)], [(8, 2, 1)], [(9, 3, 2)]])]

theorem chk25_4 : poleN (repN 25) (repL 25) 4 3 8 9 cs25_4 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `5` (ports `3`, `4`, `6`) -/
def cs25_5 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 0, 2, 5, 5, 3, 5, 2, 1, 4], [[(0, 1, 0), (1, 2, 1), (2, 3, 5)], [(0, 0, 0), (6, 10, 5), (10, 7, 1)], [(1, 0, 1), (7, 6, 3), (8, 4, 5)], [(2, 0, 5), (9, 4, 2), (11, 7, 4)], [(3, 8, 0), (8, 2, 5), (9, 3, 2)], [], [(4, 9, 2), (5, 7, 5), (7, 2, 3)], [(5, 6, 5), (10, 1, 1), (11, 3, 4)], [(3, 4, 0)], [(4, 6, 2)], [(6, 1, 5)]]),
    ([0, 5, 1, 0, 5, 1, 2, 2, 3, 5, 5, 4], [[(0, 1, 0), (1, 2, 5), (2, 3, 1)], [(0, 0, 0), (6, 10, 2), (10, 7, 5)], [(1, 0, 5), (7, 6, 2), (8, 4, 3)], [(2, 0, 1), (9, 4, 5), (11, 7, 4)], [(3, 8, 0), (8, 2, 3), (9, 3, 5)], [], [(4, 9, 5), (5, 7, 1), (7, 2, 2)], [(5, 6, 1), (10, 1, 5), (11, 3, 4)], [(3, 4, 0)], [(4, 6, 5)], [(6, 1, 2)]]),
    ([5, 0, 1, 5, 2, 3, 3, 5, 1, 2, 4, 5], [[(0, 1, 5), (1, 2, 0), (2, 3, 1)], [(0, 0, 5), (6, 10, 3), (10, 7, 4)], [(1, 0, 0), (7, 6, 5), (8, 4, 1)], [(2, 0, 1), (9, 4, 2), (11, 7, 5)], [(3, 8, 5), (8, 2, 1), (9, 3, 2)], [], [(4, 9, 2), (5, 7, 3), (7, 2, 5)], [(5, 6, 3), (10, 1, 4), (11, 3, 5)], [(3, 4, 5)], [(4, 6, 2)], [(6, 1, 3)]])]

theorem chk25_5 : poleN (repN 25) (repL 25) 5 3 4 6 cs25_5 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `6` (ports `4`, `5`, `7`) -/
def cs25_6 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 0, 5, 1, 2, 2, 5, 3, 5, 4], [[(0, 1, 0), (1, 2, 1), (2, 3, 5)], [(0, 0, 0), (6, 5, 2), (10, 7, 5)], [(1, 0, 1), (7, 10, 2), (8, 4, 5)], [(2, 0, 5), (9, 4, 3), (11, 7, 4)], [(3, 5, 0), (8, 2, 5), (9, 3, 3)], [(3, 4, 0), (4, 8, 5), (6, 1, 2)], [], [(5, 9, 1), (10, 1, 5), (11, 3, 4)], [(4, 5, 5)], [(5, 7, 1)], [(7, 2, 2)]]),
    ([0, 5, 1, 2, 3, 5, 5, 2, 4, 5, 1, 3], [[(0, 1, 0), (1, 2, 5), (2, 3, 1)], [(0, 0, 0), (6, 5, 5), (10, 7, 1)], [(1, 0, 5), (7, 10, 2), (8, 4, 4)], [(2, 0, 1), (9, 4, 5), (11, 7, 3)], [(3, 5, 2), (8, 2, 4), (9, 3, 5)], [(3, 4, 2), (4, 8, 3), (6, 1, 5)], [], [(5, 9, 5), (10, 1, 1), (11, 3, 3)], [(4, 5, 3)], [(5, 7, 5)], [(7, 2, 2)]]),
    ([5, 0, 1, 5, 0, 2, 2, 5, 1, 3, 4, 5], [[(0, 1, 5), (1, 2, 0), (2, 3, 1)], [(0, 0, 5), (6, 5, 2), (10, 7, 4)], [(1, 0, 0), (7, 10, 5), (8, 4, 1)], [(2, 0, 1), (9, 4, 3), (11, 7, 5)], [(3, 5, 5), (8, 2, 1), (9, 3, 3)], [(3, 4, 5), (4, 8, 0), (6, 1, 2)], [], [(5, 9, 2), (10, 1, 4), (11, 3, 5)], [(4, 5, 0)], [(5, 7, 2)], [(7, 2, 5)]])]

theorem chk25_6 : poleN (repN 25) (repL 25) 6 4 5 7 cs25_6 = true := by decide +kernel

/-- the certificate list for the pole of `Rep 25` at vertex `7` (ports `5`, `10`, `11`) -/
def cs25_7 : List (List Nat × List (List (Nat × Nat × Nat))) :=
  [([0, 1, 5, 0, 5, 2, 3, 4, 5, 2, 5, 3], [[(0, 1, 0), (1, 2, 1), (2, 3, 5)], [(0, 0, 0), (6, 5, 3), (10, 9, 5)], [(1, 0, 1), (7, 6, 4), (8, 4, 5)], [(2, 0, 5), (9, 4, 2), (11, 10, 3)], [(3, 5, 0), (8, 2, 5), (9, 3, 2)], [(3, 4, 0), (4, 6, 5), (6, 1, 3)], [(4, 5, 5), (5, 8, 2), (7, 2, 4)], [], [(5, 6, 2)], [(10, 1, 5)], [(11, 3, 3)]]),
    ([0, 5, 1, 2, 3, 5, 5, 2, 4, 5, 1, 3], [[(0, 1, 0), (1, 2, 5), (2, 3, 1)], [(0, 0, 0), (6, 5, 5), (10, 9, 1)], [(1, 0, 5), (7, 6, 2), (8, 4, 4)], [(2, 0, 1), (9, 4, 5), (11, 10, 3)], [(3, 5, 2), (8, 2, 4), (9, 3, 5)], [(3, 4, 2), (4, 6, 3), (6, 1, 5)], [(4, 5, 3), (5, 8, 5), (7, 2, 2)], [], [(5, 6, 5)], [(10, 1, 1)], [(11, 3, 3)]]),
    ([5, 0, 1, 5, 2, 1, 3, 5, 4, 0, 2, 5], [[(0, 1, 5), (1, 2, 0), (2, 3, 1)], [(0, 0, 5), (6, 5, 3), (10, 9, 2)], [(1, 0, 0), (7, 6, 5), (8, 4, 4)], [(2, 0, 1), (9, 4, 0), (11, 10, 5)], [(3, 5, 5), (8, 2, 4), (9, 3, 0)], [(3, 4, 5), (4, 6, 2), (6, 1, 3)], [(4, 5, 2), (5, 8, 1), (7, 2, 5)], [], [(5, 6, 1)], [(10, 1, 2)], [(11, 3, 5)]])]

theorem chk25_7 : poleN (repN 25) (repL 25) 7 5 10 11 cs25_7 = true := by decide +kernel

/-- every labelling of the pole of `Rep 7` at any vertex is dominant -/
theorem pd_rep7 : ∀ (h0 : Fin (repG 7).n) (E : Ports (fun _ : Fin (repG 7).m => True) h0), Dominant E

  | ⟨0, _⟩ => fun E => dominant_of_poleN (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) repG7_inG chk7_0 E
  | ⟨1, _⟩ => fun E => dominant_of_poleN (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) repG7_inG chk7_1 E
  | ⟨2, _⟩ => fun E => dominant_of_poleN (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) repG7_inG chk7_2 E
  | ⟨3, _⟩ => fun E => dominant_of_poleN (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) repG7_inG chk7_3 E
  | ⟨4, _⟩ => fun E => dominant_of_poleN (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) repG7_inG chk7_4 E
  | ⟨5, _⟩ => fun E => dominant_of_poleN (n := repN 7) (el := repL 7) (hn := repN_pos 7) (by decide) repG7_inG chk7_5 E
  | ⟨j + 6, h⟩ => absurd h (by show ¬ (j + 6 < 6); omega)

/-- every labelling of the pole of `Rep 8` at any vertex is dominant -/
theorem pd_rep8 : ∀ (h0 : Fin (repG 8).n) (E : Ports (fun _ : Fin (repG 8).m => True) h0), Dominant E

  | ⟨0, _⟩ => fun E => dominant_of_poleN (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) repG8_inG chk8_0 E
  | ⟨1, _⟩ => fun E => dominant_of_poleN (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) repG8_inG chk8_1 E
  | ⟨2, _⟩ => fun E => dominant_of_poleN (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) repG8_inG chk8_2 E
  | ⟨3, _⟩ => fun E => dominant_of_poleN (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) repG8_inG chk8_3 E
  | ⟨4, _⟩ => fun E => dominant_of_poleN (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) repG8_inG chk8_4 E
  | ⟨5, _⟩ => fun E => dominant_of_poleN (n := repN 8) (el := repL 8) (hn := repN_pos 8) (by decide) repG8_inG chk8_5 E
  | ⟨j + 6, h⟩ => absurd h (by show ¬ (j + 6 < 6); omega)

/-- every labelling of the pole of `Rep 25` at any vertex is dominant -/
theorem pd_rep25 : ∀ (h0 : Fin (repG 25).n) (E : Ports (fun _ : Fin (repG 25).m => True) h0), Dominant E

  | ⟨0, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_0 E
  | ⟨1, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_1 E
  | ⟨2, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_2 E
  | ⟨3, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_3 E
  | ⟨4, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_4 E
  | ⟨5, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_5 E
  | ⟨6, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_6 E
  | ⟨7, _⟩ => fun E => dominant_of_poleN (n := repN 25) (el := repL 25) (hn := repN_pos 25) (by decide) repG25_inG chk25_7 E
  | ⟨j + 8, h⟩ => absurd h (by show ¬ (j + 8 < 8); omega)

/-- every labelling of the pole of `Rep 6` at the vertices `0`, `1` is dominant -/
theorem pd_rep6 : ∀ (h0 : Fin (repG 6).n), (h0.val = 0 ∨ h0.val = 1) →
    ∀ (E : Ports (fun _ : Fin (repG 6).m => True) h0), Dominant E

  | ⟨0, _⟩ => fun _ E => dominant_of_poleN (n := repN 6) (el := repL 6) (hn := repN_pos 6) (by decide) repG6_inG chk6_0 E
  | ⟨1, _⟩ => fun _ E => dominant_of_poleN (n := repN 6) (el := repL 6) (hn := repN_pos 6) (by decide) repG6_inG chk6_1 E
  | ⟨j + 2, _⟩ => fun hh => absurd hh (by show ¬ (j + 2 = 0 ∨ j + 2 = 1); omega)

/-- **SMALL-PD (A)** (fact 86f2b7c4166011f6) in Lean: every labelling of the ports of the poles of the prism,
    K₃,₃ and V₈ at every vertex and of K₄ with a digon on the edge `0 1` at the ends `0`, `1` of that edge is
    dominant -/
theorem smallpd : SMALLPD := by
  intro k h0 hk E
  rcases hk with rfl | rfl | rfl | ⟨rfl, hh⟩
  · exact pd_rep7 h0 E
  · exact pd_rep8 h0 E
  · exact pd_rep25 h0 E
  · exact pd_rep6 h0 hh E

/-- **layer 26 of the Lean formalization**: SMALL-PD (A) holds; hence Theorem ROOT-CS4 (fact 6010cb59aaf31d7a) and
    its (W-EXT)/(TD-L-TRI) form hold in Lean without the finite hypothesis SMALLPD -/
theorem layer26 :
    SMALLPD ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → FEEXTD10 → FEEXISTD10 → POLE → TDTRI → IID → DMS) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → FEEXTD10 → FEEXISTD10 → WEXT → TDLTRI → IID → DMS) :=
  ⟨smallpd,
   fun hB12 hS14 hB14 hSH hext hex hpole htd hD => rootcs4 hB12 hS14 hB14 hSH smallpd hext hex hpole htd hD,
   fun hB12 hS14 hB14 hSH hext hex hW htdl hD =>
     layer25.2.2.2.2 hB12 hS14 hB14 hSH smallpd hext hex hW htdl hD⟩

end RH2F
