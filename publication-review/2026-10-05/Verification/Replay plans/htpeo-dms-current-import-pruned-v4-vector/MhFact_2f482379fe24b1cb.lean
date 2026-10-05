-- Lean proof of fact 2f482379fe24b1cb (RH2F.smallhostd_of); added by fact_submit, do not edit
import MhFact_57ea4db232a2b7f5
set_option backward.isDefEq.respectTransparency false

/-
  Layer 27 of the Lean formalization (RH2F): the reduction of Lemma SMALLHOST-D (fact d2f6b988c49c84f6) to the
  EX1-fullness of 451 explicit digon insertions of K₄, K₃,₃, Q₃ and V₈ (orbit representatives under the host
  automorphisms), with a kernel-checked orbit coverage, the digon isomorphism, and a shared-walk EX1 certificate
  checker (proved sound).
-/
-- ===== from SH1.lean =====

/-
  SH1.lean — explicit digon insertions and the isomorphism lemma:
  * `digEl n el dl`: the compact digon insertion of the explicit multigraph `ofList n el` at the edge set given by the
    Bool list `dl` (edge `j` with `dl[j]` becomes `(a, u_j)`, `u_j v_j`, `u_j v_j`, `(v_j, b)`, where `u_j = n + 2 r`,
    `v_j = n + 2 r + 1` and `r` is the rank of `j` among the marked edges);
  * `isoFrom_of_vals`: an isomorphism onto `ofList N L` from value-level data;
  * `dig_iso`: an isomorphism `Q → ofList n el` carrying `D` to `dl` extends to `digSet Q D → ofList (digEl n el dl)`.
-/

namespace RH2F
open MGraph
open Classical

section sh1

/-! ### the compact digon insertion of an edge list -/

/-- the number of marked edges -/
def cntT (dl : List Bool) : Nat := dl.count true

/-- the rank of edge `j` among the marked edges -/
def posT (dl : List Bool) (j : Nat) : Nat := (dl.take j).count true

/-- the `r`-th marked edge -/
def nthT (dl : List Bool) (r : Nat) : Nat := ((List.range dl.length).filter (fun j => dl.getD j false)).getD r 0

/-- the edges of the compact digon insertion -/
def digEl (n : Nat) (el : List (Nat × Nat)) (dl : List Bool) : List (Nat × Nat) :=
  (List.range el.length).map (fun j => if dl.getD j false then ((gE el j).1, n + 2 * posT dl j) else gE el j) ++
  (List.range (3 * cntT dl)).map (fun i => if i % 3 = 2 then (n + 2 * (i / 3) + 1, (gE el (nthT dl (i / 3))).2)
    else (n + 2 * (i / 3), n + 2 * (i / 3) + 1))

/-- the Bool sanity checks of a marking: the digon insertion is a loopless edge list on `n + 2 cntT` vertices, the
    marking has one entry per edge, and ranks and marked edges correspond -/
def digOK (n : Nat) (el : List (Nat × Nat)) (dl : List Bool) : Bool :=
  elOK (n + 2 * cntT dl) (digEl n el dl) && dl.length == el.length &&
  (List.range el.length).all (fun j => !dl.getD j false || (Nat.blt (posT dl j) (cntT dl) && nthT dl (posT dl j) == j)) &&
  (List.range (cntT dl)).all (fun r => Nat.blt (nthT dl r) el.length && dl.getD (nthT dl r) false &&
    posT dl (nthT dl r) == r)

theorem length_digEl (n : Nat) (el : List (Nat × Nat)) (dl : List Bool) :
    (digEl n el dl).length = el.length + 3 * cntT dl := by
  simp [digEl]

theorem gE_digEl_lo {n : Nat} {el : List (Nat × Nat)} {dl : List Bool} {j : Nat} (hj : j < el.length) :
    gE (digEl n el dl) j = if dl.getD j false then ((gE el j).1, n + 2 * posT dl j) else gE el j := by
  unfold gE digEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj)]
  simp [List.getElem?_map, List.getElem?_range hj, gE]

theorem gE_digEl_hi {n : Nat} {el : List (Nat × Nat)} {dl : List Bool} {i : Nat} (hi : i < 3 * cntT dl) :
    gE (digEl n el dl) (el.length + i) = if i % 3 = 2 then (n + 2 * (i / 3) + 1, (gE el (nthT dl (i / 3))).2)
      else (n + 2 * (i / 3), n + 2 * (i / 3) + 1) := by
  unfold gE digEl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [List.getElem?_map, List.getElem?_range hi, gE, List.getD_eq_getElem?_getD]

/-- the facts contained in `digOK` -/
theorem digOK_spec {n : Nat} {el : List (Nat × Nat)} {dl : List Bool} (h : digOK n el dl = true) :
    elOK (n + 2 * cntT dl) (digEl n el dl) = true ∧ dl.length = el.length ∧
    (∀ j, j < el.length → dl.getD j false = true → posT dl j < cntT dl ∧ nthT dl (posT dl j) = j) ∧
    (∀ r, r < cntT dl → nthT dl r < el.length ∧ dl.getD (nthT dl r) false = true ∧ posT dl (nthT dl r) = r) := by
  unfold digOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun j hj hd => ?_, fun r hr => ?_⟩
  · have := List.all_eq_true.1 h3 j (List.mem_range.2 hj)
    rw [hd] at this
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨Nat.le_of_ble_eq_true this.1, this.2⟩
  · have := List.all_eq_true.1 h4 r (List.mem_range.2 hr)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨Nat.le_of_ble_eq_true this.1.1, this.1.2, this.2⟩

/-! ### isomorphisms onto explicit edge lists from value-level data -/

/-- an isomorphism from `P` onto `ofList N L` given by value maps `A` (vertices) and `B` (edges) -/
theorem isoFrom_of_vals {X : MGraph} {P : Fin X.m → Prop} {N : Nat} {L : List (Nat × Nat)} {hN : 0 < N}
    (hL : elOK N L = true) (hLpos : 0 < L.length) (A : Fin X.n → Nat) (B : Fin X.m → Nat)
    (hA : ∀ x, meets P x → A x < N) (hB : ∀ f, P f → B f < L.length)
    (hAi : ∀ x y, meets P x → meets P y → A x = A y → x = y) (hBi : ∀ f g, P f → P g → B f = B g → f = g)
    (hBs : ∀ j, j < L.length → ∃ f, P f ∧ B f = j)
    (hJ : ∀ f, P f → gE L (B f) = (A (X.ends f).1, A (X.ends f).2) ∨ gE L (B f) = (A (X.ends f).2, A (X.ends f).1)) :
    IsoFrom P (ofList N L hN) := by
  have hmod : ∀ x, meets P x → A x % N = A x := fun x hx => Nat.mod_eq_of_lt (hA x hx)
  have hmodB : ∀ f, P f → B f % L.length = B f := fun f hf => Nat.mod_eq_of_lt (hB f hf)
  refine ⟨fun x => ⟨A x % N, Nat.mod_lt _ hN⟩, fun f => ⟨B f % L.length, Nat.mod_lt _ hLpos⟩,
    fun x y hx hy h => hAi x y hx hy ?_, fun f g hf hg h => hBi f g hf hg ?_, fun j => ?_, fun f hf => ?_⟩
  · have := congrArg Fin.val h; simp only at this; rwa [hmod x hx, hmod y hy] at this
  · have := congrArg Fin.val h; simp only at this; rwa [hmodB f hf, hmodB g hg] at this
  · obtain ⟨f, hf, hfj⟩ := hBs j.val j.isLt
    refine ⟨f, hf, Fin.ext ?_⟩
    show B f % L.length = j.val
    rw [hmodB f hf, hfj]
  · have hm1 : meets P (X.ends f).1 := ⟨f, hf, Or.inl rfl⟩
    have hm2 : meets P (X.ends f).2 := ⟨f, hf, Or.inr rfl⟩
    have he := ofList_ends (hn := hN) hL ⟨B f % L.length, Nat.mod_lt _ hLpos⟩
    simp only at he
    have hg : gE L (B f % L.length) = gE L (B f) := by rw [hmodB f hf]
    rw [hg] at he
    unfold MGraph.Joins
    rcases hJ f hf with h | h <;> rw [h] at he <;> simp only at he
    · left; exact Prod.ext (Fin.ext (he.1.trans (hmod _ hm1).symm)) (Fin.ext (he.2.trans (hmod _ hm2).symm))
    · right; exact Prod.ext (Fin.ext (he.1.trans (hmod _ hm2).symm)) (Fin.ext (he.2.trans (hmod _ hm1).symm))

/-! ### the digon isomorphism -/

section digiso
variable {X : MGraph} {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}
  (α : Fin X.n → Fin (ofList n el hn).n) (β : Fin X.m → Fin (ofList n el hn).m) (dl : List Bool)

/-- edge `f` keeps its orientation: its first end is mapped to the first end of `β f` -/
def dfw (f : Fin X.m) : Prop := (α (X.ends f).1).val = (gE el (β f).val).1

/-- the value map on the vertices of `digG X D` -/
noncomputable def dA (D : Fin X.m → Prop) (w : Fin (digG X D).n) : Nat :=
  if h : ∃ x, w = dO x then (α (Classical.choose h)).val
  else if h : ∃ f, w = dU f then
    n + 2 * posT dl (β (Classical.choose h)).val + (if dfw α β (Classical.choose h) then 0 else 1)
  else if h : ∃ f, w = dV f then
    n + 2 * posT dl (β (Classical.choose h)).val + (if dfw α β (Classical.choose h) then 1 else 0)
  else 0

/-- the value map on the edges of `digG X D` -/
noncomputable def dB (D : Fin X.m → Prop) (e : Fin (digG X D).m) : Nat :=
  if h : ∃ f, e = eO f then
    (if D (Classical.choose h) ∧ ¬ dfw α β (Classical.choose h) then
      el.length + 3 * posT dl (β (Classical.choose h)).val + 2 else (β (Classical.choose h)).val)
  else if h : ∃ f k, e = eN f k then
    (if (Classical.choose (Classical.choose_spec h)).val = 2 ∧ ¬ dfw α β (Classical.choose h) then
      (β (Classical.choose h)).val
    else el.length + 3 * posT dl (β (Classical.choose h)).val + (Classical.choose (Classical.choose_spec h)).val)
  else 0

variable {D : Fin X.m → Prop}

theorem dA_dO (x : Fin X.n) : dA α β dl D (dO x) = (α x).val := by
  have h : ∃ y, (dO x : Fin (digG X D).n) = dO y := ⟨x, rfl⟩
  unfold dA
  rw [dif_pos h, dO_inj (Classical.choose_spec h).symm]

theorem dA_dU (f : Fin X.m) :
    dA α β dl D (dU f) = n + 2 * posT dl (β f).val + (if dfw α β f then 0 else 1) := by
  have h0 : ¬ ∃ y, (dU f : Fin (digG X D).n) = dO y := fun ⟨y, hy⟩ => dO_ne_dU y f hy.symm
  have h : ∃ g, (dU f : Fin (digG X D).n) = dU g := ⟨f, rfl⟩
  unfold dA
  rw [dif_neg h0, dif_pos h, dU_inj (Classical.choose_spec h).symm]

theorem dA_dV (f : Fin X.m) :
    dA α β dl D (dV f) = n + 2 * posT dl (β f).val + (if dfw α β f then 1 else 0) := by
  have h0 : ¬ ∃ y, (dV f : Fin (digG X D).n) = dO y := fun ⟨y, hy⟩ => dO_ne_dV y f hy.symm
  have h1 : ¬ ∃ g, (dV f : Fin (digG X D).n) = dU g := fun ⟨g, hg⟩ => dU_ne_dV g f hg.symm
  have h : ∃ g, (dV f : Fin (digG X D).n) = dV g := ⟨f, rfl⟩
  unfold dA
  rw [dif_neg h0, dif_neg h1, dif_pos h, dV_inj (Classical.choose_spec h).symm]

theorem dB_eO (f : Fin X.m) : dB α β dl D (eO f) =
    if D f ∧ ¬ dfw α β f then el.length + 3 * posT dl (β f).val + 2 else (β f).val := by
  have h : ∃ g, (eO f : Fin (digG X D).m) = eO g := ⟨f, rfl⟩
  unfold dB
  rw [dif_pos h, eO_inj (Classical.choose_spec h).symm]

theorem dB_eN (f : Fin X.m) (k : Fin 3) : dB α β dl D (eN f k) =
    if k.val = 2 ∧ ¬ dfw α β f then (β f).val else el.length + 3 * posT dl (β f).val + k.val := by
  have h0 : ¬ ∃ g, (eN f k : Fin (digG X D).m) = eO g := fun ⟨g, hg⟩ => eO_ne_eN g f k hg.symm
  have h : ∃ g k', (eN f k : Fin (digG X D).m) = eN g k' := ⟨f, k, rfl⟩
  have hs := Classical.choose_spec (Classical.choose_spec h)
  obtain ⟨e1, e2⟩ := eN_inj hs.symm
  unfold dB
  rw [dif_neg h0, dif_pos h]
  simp only [e2]
  simp only [e1]

end digiso

/-- a host edge joining the images of the ends of `f`, in values -/
theorem host_vals {X : MGraph} {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} (hel : elOK n el = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin X.m → Fin (ofList n el hn).m} {f : Fin X.m}
    (h : (ofList n el hn).Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) :
    gE el (β f).val = ((α (X.ends f).1).val, (α (X.ends f).2).val) ∨
    gE el (β f).val = ((α (X.ends f).2).val, (α (X.ends f).1).val) := by
  have he := ofList_ends (hn := hn) hel (β f)
  rcases h with h | h <;> rw [h] at he <;> simp only at he
  · left; exact Prod.ext he.1.symm he.2.symm
  · right; exact Prod.ext he.1.symm he.2.symm

/-- **the digon isomorphism**: an isomorphism `(α, β)` from `Q` onto `ofList n el` under which `D` corresponds to the
    marking `dl` extends to an isomorphism from `Q^D` onto the compact digon insertion `ofList (digEl n el dl)` -/
theorem dig_iso {X : MGraph} {Q : Fin X.m → Prop} {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}
    (hXl : Loopless X) (hel : elOK n el = true) {dl : List Bool} (hok : digOK n el dl = true)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin X.m → Fin (ofList n el hn).m}
    (hα : ∀ x y, meets Q x → meets Q y → α x = α y → x = y) (hβ : ∀ f g, Q f → Q g → β f = β g → f = g)
    (hs : ∀ j, ∃ f, Q f ∧ β f = j) (hj : ∀ f, Q f → (ofList n el hn).Joins (β f) (α (X.ends f).1) (α (X.ends f).2))
    {D : Fin X.m → Prop} (hD : ∀ f, Q f → (D f ↔ dl.getD (β f).val false = true)) (hN : 0 < n + 2 * cntT dl)
    (hm0 : 0 < el.length) :
    IsoFrom (digSet Q D) (ofList (n + 2 * cntT dl) (digEl n el dl) hN) := by
  obtain ⟨hL, hlen, hP1, hP2⟩ := digOK_spec hok
  have hloop := ofList_loop (hn := hn) hel
  -- positions of the marked edges
  have hpos : ∀ f, Q f → D f → posT dl (β f).val < cntT dl ∧ nthT dl (posT dl (β f).val) = (β f).val :=
    fun f hf hd => hP1 _ (β f).isLt ((hD f hf).1 hd)
  have pinj : ∀ f g, Q f → Q g → D f → D g → posT dl (β f).val = posT dl (β g).val → f = g := by
    intro f g hf hg hdf hdg h
    have e1 := (hpos f hf hdf).2
    have e2 := (hpos g hg hdg).2
    rw [h] at e1
    exact hβ f g hf hg (Fin.ext (e1.symm.trans e2))
  have hm : ∀ f : Fin X.m, (β f).val < el.length := fun f => (β f).isLt
  -- the orientation
  have hor : ∀ f, Q f → (dfw α β f → gE el (β f).val = ((α (X.ends f).1).val, (α (X.ends f).2).val)) ∧
      (¬ dfw α β f → gE el (β f).val = ((α (X.ends f).2).val, (α (X.ends f).1).val)) := by
    intro f hf
    have hl := hloop (β f)
    rcases host_vals hel (hj f hf) with h | h
    · refine ⟨fun _ => h, fun hn' => absurd ?_ hn'⟩
      unfold dfw; rw [h]
    · refine ⟨fun hw => ?_, fun _ => h⟩
      unfold dfw at hw
      rw [h] at hl hw
      simp only at hl hw
      exact absurd hw.symm (fun e => hl (e.symm ▸ rfl))
  have hLpos : 0 < (digEl n el dl).length := by rw [length_digEl]; omega
  have hdl : ∀ f, Q f → D f → dl.getD (β f).val false = true := fun f hf hd => (hD f hf).1 hd
  have hαn : ∀ x : Fin X.n, (α x).val < n := fun x => (α x).isLt
  refine isoFrom_of_vals hL hLpos (dA α β dl D) (dB α β dl D) ?_ ?_ ?_ ?_ ?_ ?_
  · -- vertex values are vertices
    intro w hw
    rcases vert_cases w with ⟨x, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩
    · rw [dA_dO]; have := hαn x; omega
    · obtain ⟨hf, hd⟩ := (meets_dig_dU f).1 hw
      rw [dA_dU]; have := (hpos f hf hd).1; split <;> omega
    · obtain ⟨hf, hd⟩ := (meets_dig_dV f).1 hw
      rw [dA_dV]; have := (hpos f hf hd).1; split <;> omega
  · -- edge values are edges
    intro e he
    rw [length_digEl]
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · have hf := (set_eO Q f).1 he
      rw [dB_eO]; split
      · rename_i hc; have := (hpos f hf hc.1).1; omega
      · have := hm f; omega
    · obtain ⟨hf, hd⟩ := (set_eN Q f k).1 he
      rw [dB_eN]; have := (hpos f hf hd).1; have := k.isLt; have := hm f; split <;> omega
  · -- injective on vertices
    intro w w' hw hw' h
    rcases vert_cases w with ⟨x, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ <;>
      rcases vert_cases w' with ⟨y, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    · rw [dA_dO, dA_dO] at h
      rw [hα x y ((meets_dig_dO hXl x).1 hw) ((meets_dig_dO hXl y).1 hw') (Fin.ext h)]
    · rw [dA_dO, dA_dU] at h; have := hαn x; omega
    · rw [dA_dO, dA_dV] at h; have := hαn x; omega
    · rw [dA_dU, dA_dO] at h; have := hαn y; omega
    · obtain ⟨hf, hd⟩ := (meets_dig_dU f).1 hw
      obtain ⟨hg, hdg⟩ := (meets_dig_dU g).1 hw'
      rw [dA_dU, dA_dU] at h
      have hp : posT dl (β f).val = posT dl (β g).val := by split at h <;> split at h <;> omega
      rw [pinj f g hf hg hd hdg hp]
    · obtain ⟨hf, hd⟩ := (meets_dig_dU f).1 hw
      obtain ⟨hg, hdg⟩ := (meets_dig_dV g).1 hw'
      rw [dA_dU, dA_dV] at h
      have hp : posT dl (β f).val = posT dl (β g).val := by split at h <;> split at h <;> omega
      obtain rfl := pinj f g hf hg hd hdg hp
      exfalso; split at h <;> omega
    · rw [dA_dV, dA_dO] at h; have := hαn y; omega
    · obtain ⟨hf, hd⟩ := (meets_dig_dV f).1 hw
      obtain ⟨hg, hdg⟩ := (meets_dig_dU g).1 hw'
      rw [dA_dV, dA_dU] at h
      have hp : posT dl (β f).val = posT dl (β g).val := by split at h <;> split at h <;> omega
      obtain rfl := pinj f g hf hg hd hdg hp
      exfalso; split at h <;> omega
    · obtain ⟨hf, hd⟩ := (meets_dig_dV f).1 hw
      obtain ⟨hg, hdg⟩ := (meets_dig_dV g).1 hw'
      rw [dA_dV, dA_dV] at h
      have hp : posT dl (β f).val = posT dl (β g).val := by split at h <;> split at h <;> omega
      rw [pinj f g hf hg hd hdg hp]
  · -- injective on edges
    intro e e' he he' h
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩ <;> rcases dig_cases e' with ⟨g, rfl⟩ | ⟨g, k', rfl⟩
    · have hf := (set_eO Q f).1 he
      have hg := (set_eO Q g).1 he'
      rw [dB_eO, dB_eO] at h
      by_cases c1 : D f ∧ ¬ dfw α β f <;> by_cases c2 : D g ∧ ¬ dfw α β g
      · rw [if_pos c1, if_pos c2] at h
        rw [pinj f g hf hg c1.1 c2.1 (by omega)]
      · rw [if_pos c1, if_neg c2] at h; have := hm g; omega
      · rw [if_neg c1, if_pos c2] at h; have := hm f; omega
      · rw [if_neg c1, if_neg c2] at h
        rw [hβ f g hf hg (Fin.ext h)]
    · have hf := (set_eO Q f).1 he
      obtain ⟨hg, hdg⟩ := (set_eN Q g k').1 he'
      rw [dB_eO, dB_eN] at h
      by_cases c1 : D f ∧ ¬ dfw α β f <;> by_cases c2 : k'.val = 2 ∧ ¬ dfw α β g
      · rw [if_pos c1, if_pos c2] at h; have := hm g; omega
      · rw [if_pos c1, if_neg c2] at h
        have hk : k'.val = 2 := by have := k'.isLt; omega
        obtain rfl := pinj f g hf hg c1.1 hdg (by omega)
        exact absurd ⟨hk, c1.2⟩ c2
      · rw [if_neg c1, if_pos c2] at h
        obtain rfl := hβ f g hf hg (Fin.ext h)
        exact absurd ⟨hdg, c2.2⟩ c1
      · rw [if_neg c1, if_neg c2] at h; have := hm f; omega
    · obtain ⟨hf, hdf⟩ := (set_eN Q f k).1 he
      have hg := (set_eO Q g).1 he'
      rw [dB_eN, dB_eO] at h
      by_cases c1 : k.val = 2 ∧ ¬ dfw α β f <;> by_cases c2 : D g ∧ ¬ dfw α β g
      · rw [if_pos c1, if_pos c2] at h; have := hm f; omega
      · rw [if_pos c1, if_neg c2] at h
        obtain rfl := hβ f g hf hg (Fin.ext h)
        exact absurd ⟨hdf, c1.2⟩ c2
      · rw [if_neg c1, if_pos c2] at h
        have hk : k.val = 2 := by have := k.isLt; omega
        obtain rfl := pinj f g hf hg hdf c2.1 (by omega)
        exact absurd ⟨hk, c2.2⟩ c1
      · rw [if_neg c1, if_neg c2] at h; have := hm g; omega
    · obtain ⟨hf, hdf⟩ := (set_eN Q f k).1 he
      obtain ⟨hg, hdg⟩ := (set_eN Q g k').1 he'
      rw [dB_eN, dB_eN] at h
      by_cases c1 : k.val = 2 ∧ ¬ dfw α β f <;> by_cases c2 : k'.val = 2 ∧ ¬ dfw α β g
      · rw [if_pos c1, if_pos c2] at h
        obtain rfl := hβ f g hf hg (Fin.ext h)
        rw [show k = k' from Fin.ext (c1.1.trans c2.1.symm)]
      · rw [if_pos c1, if_neg c2] at h; have := hm f; omega
      · rw [if_neg c1, if_pos c2] at h; have := hm g; omega
      · rw [if_neg c1, if_neg c2] at h
        have hk := k.isLt
        have hk' := k'.isLt
        obtain rfl := pinj f g hf hg hdf hdg (by omega)
        rw [show k = k' from Fin.ext (by omega)]
  · -- surjective on edges
    intro j hj
    rw [length_digEl] at hj
    by_cases hjm : j < el.length
    · obtain ⟨f, hf, hfj⟩ := hs ⟨j, hjm⟩
      have hfv : (β f).val = j := by rw [hfj]
      by_cases hd : D f
      · by_cases hw : dfw α β f
        · exact ⟨eO f, (set_eO Q f).2 hf, by rw [dB_eO, if_neg (fun h => h.2 hw), hfv]⟩
        · exact ⟨eN f 2, (set_eN Q f 2).2 ⟨hf, hd⟩, by rw [dB_eN, if_pos ⟨rfl, hw⟩, hfv]⟩
      · exact ⟨eO f, (set_eO Q f).2 hf, by rw [dB_eO, if_neg (fun h => hd h.1), hfv]⟩
    · have hr : (j - el.length) / 3 < cntT dl := by omega
      obtain ⟨hr1, hr2, hr3⟩ := hP2 _ hr
      obtain ⟨f, hf, hfj⟩ := hs ⟨nthT dl ((j - el.length) / 3), hr1⟩
      have hfv : (β f).val = nthT dl ((j - el.length) / 3) := by rw [hfj]
      have hd : D f := (hD f hf).2 (by rw [hfv]; exact hr2)
      have hpf : posT dl (β f).val = (j - el.length) / 3 := by rw [hfv]; exact hr3
      by_cases hk : (j - el.length) % 3 = 2 ∧ ¬ dfw α β f
      · exact ⟨eO f, (set_eO Q f).2 hf, by rw [dB_eO, if_pos ⟨hd, hk.2⟩, hpf]; omega⟩
      · refine ⟨eN f ⟨(j - el.length) % 3, Nat.mod_lt _ (by decide)⟩, (set_eN Q f _).2 ⟨hf, hd⟩, ?_⟩
        rw [dB_eN, if_neg hk, hpf]
        show el.length + 3 * ((j - el.length) / 3) + (j - el.length) % 3 = j
        omega
  · -- ends
    intro e he
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · have hf := (set_eO Q f).1 he
      by_cases hd : D f
      · have hp := hpos f hf hd
        rw [ends_eO_D hd, dA_dO, dA_dU]
        by_cases hw : dfw α β f
        · left
          rw [dB_eO, if_neg (fun h => h.2 hw), gE_digEl_lo (hm f), if_pos (hdl f hf hd), if_pos hw,
            (hor f hf).1 hw]
          rfl
        · right
          rw [dB_eO, if_pos ⟨hd, hw⟩, if_neg hw, Nat.add_assoc, gE_digEl_hi (by omega),
            if_pos (by omega), show (3 * posT dl (β f).val + 2) / 3 = posT dl (β f).val by omega, hp.2,
            (hor f hf).2 hw]
      · rw [ends_eO_nD hd, dA_dO, dA_dO, dB_eO, if_neg (fun h => hd h.1), gE_digEl_lo (hm f),
          if_neg (fun h => hd ((hD f hf).2 h))]
        exact host_vals hel (hj f hf)
    · obtain ⟨hf, hd⟩ := (set_eN Q f k).1 he
      have hp := hpos f hf hd
      rcases k_cases k with rfl | hk
      · rw [ends_eN2, dA_dV, dA_dO]
        by_cases hw : dfw α β f
        · left
          rw [dB_eN, if_neg (fun h => h.2 hw), if_pos hw]
          show gE (digEl n el dl) (el.length + 3 * posT dl (β f).val + 2) = _
          rw [Nat.add_assoc, gE_digEl_hi (by omega), if_pos (by omega),
            show (3 * posT dl (β f).val + 2) / 3 = posT dl (β f).val by omega, hp.2, (hor f hf).1 hw]
        · right
          rw [dB_eN, if_pos ⟨rfl, hw⟩, if_neg hw, gE_digEl_lo (hm f), if_pos (hdl f hf hd), (hor f hf).2 hw]
          rfl
      · have hk2 : k.val ≠ 2 := fun h => hk (Fin.ext h)
        have hk3 := k.isLt
        rw [ends_eN01 f k hk, dA_dU, dA_dV, dB_eN, if_neg (fun h => hk2 h.1), Nat.add_assoc,
          gE_digEl_hi (by omega), if_neg (by omega),
          show (3 * posT dl (β f).val + k.val) / 3 = posT dl (β f).val by omega]
        by_cases hw : dfw α β f
        · left; rw [if_pos hw, if_pos hw]; rfl
        · right; rw [if_neg hw, if_neg hw]; rfl

end sh1

end RH2F

-- ===== from SH1b.lean =====

/-
  SH1b.lean — `digOK` holds for every marking of the right length (no per-marking kernel check needed): the marked
  indices form a duplicate-free increasing list `tIdx`, `posT` is the number of marked indices below `j`, and
  `nthT` reads `tIdx`.
-/

namespace RH2F
open MGraph

section markings
variable (dl : List Bool)

/-- the marked indices in increasing order -/
def tIdx : List Nat := (List.range dl.length).filter (fun i => dl.getD i false)

theorem nthT_eq (r : Nat) : nthT dl r = (tIdx dl).getD r 0 := rfl

theorem posT_eq : ∀ j, j ≤ dl.length → posT dl j = ((List.range j).filter (fun i => dl.getD i false)).length
  | 0, _ => by simp [posT]
  | j + 1, hj => by
    have ih := posT_eq j (by omega)
    unfold posT at ih ⊢
    rw [List.take_succ, List.count_append, ih, List.range_succ, List.filter_append, List.length_append]
    have hlt : j < dl.length := by omega
    rw [List.getElem?_eq_getElem hlt]
    have hg : dl.getD j false = dl[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
    cases h : dl[j] <;> simp [List.filter_cons, List.getElem?_eq_getElem hlt, h]

theorem cntT_eq : cntT dl = (tIdx dl).length := by
  have := posT_eq dl dl.length (le_refl _)
  unfold posT at this
  rw [List.take_length] at this
  exact this

/-- `tIdx` splits at a marked index `j`: `tIdx = A ++ j :: B` with `|A| = posT j` -/
theorem tIdx_split {j : Nat} (hj : j < dl.length) (hm : dl.getD j false = true) :
    ∃ B, tIdx dl = (List.range j).filter (fun i => dl.getD i false) ++ j :: B := by
  unfold tIdx
  have hsplit : dl.length = j + (dl.length - j) := by omega
  rw [hsplit, List.range_add, List.filter_append]
  have hpos : 0 < dl.length - j := by omega
  obtain ⟨k, hk⟩ : ∃ k, dl.length - j = k + 1 := ⟨dl.length - j - 1, by omega⟩
  rw [hk, List.range_succ_eq_map, List.map_cons, List.filter_cons]
  simp only [Nat.add_zero, hm, if_true]
  exact ⟨_, rfl⟩

theorem tIdx_nodup : (tIdx dl).Nodup := List.Nodup.filter _ List.nodup_range

theorem mem_tIdx {x : Nat} : x ∈ tIdx dl ↔ x < dl.length ∧ dl.getD x false = true := by
  unfold tIdx; simp [List.mem_filter, List.mem_range]

theorem marked_facts {j : Nat} (hj : j < dl.length) (hm : dl.getD j false = true) :
    posT dl j < cntT dl ∧ nthT dl (posT dl j) = j := by
  obtain ⟨B, hB⟩ := tIdx_split dl hj hm
  have hp := posT_eq dl j (le_of_lt hj)
  rw [cntT_eq, nthT_eq, hB, hp]
  refine ⟨by simp, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem rank_facts {r : Nat} (hr : r < cntT dl) :
    nthT dl r < dl.length ∧ dl.getD (nthT dl r) false = true ∧ posT dl (nthT dl r) = r := by
  rw [cntT_eq] at hr
  have hx : (tIdx dl).getD r 0 = (tIdx dl)[r] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
  have hmem := (mem_tIdx dl).1 (List.getElem_mem hr)
  rw [nthT_eq, hx]
  refine ⟨hmem.1, hmem.2, ?_⟩
  obtain ⟨hlt, hcnt⟩ := marked_facts dl hmem.1 hmem.2
  rw [nthT_eq] at hcnt
  rw [cntT_eq] at hlt
  have hx2 : (tIdx dl).getD (posT dl (tIdx dl)[r]) 0 = (tIdx dl)[posT dl (tIdx dl)[r]] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  rw [hx2] at hcnt
  exact ((tIdx_nodup dl).getElem_inj_iff).1 hcnt

end markings

/-- **every marking of the right length passes `digOK`** -/
theorem digOK_of {n : Nat} {el : List (Nat × Nat)} (hel : elOK n el = true) {dl : List Bool}
    (hlen : dl.length = el.length) : digOK n el dl = true := by
  unfold digOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨⟨?_, hlen⟩, fun j hj => ?_⟩, fun r hr => ?_⟩
  · unfold elOK digEl
    rw [List.all_append, Bool.and_eq_true, List.all_map, List.all_map, List.all_eq_true, List.all_eq_true]
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · have hj' := List.mem_range.1 hj
      have hge := gE_lt hel hj'
      simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      split
      · rename_i hm
        have := (marked_facts dl (by omega) hm).1
        simp only
        refine ⟨⟨by omega, by omega⟩, by omega⟩
      · have hl := List.all_eq_true.1 hel (el.getD j (0, 0)) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; exact List.getElem_mem hj')
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hl
        exact ⟨⟨by unfold gE; omega, by unfold gE; omega⟩, hl.2⟩
    · have hi' := List.mem_range.1 hi
      have hr : i / 3 < cntT dl := by omega
      have hk := rank_facts dl hr
      have hge := gE_lt hel (show nthT dl (i / 3) < el.length by rw [← hlen]; exact hk.1)
      simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      split <;> simp only <;> refine ⟨⟨by omega, by omega⟩, by omega⟩
  · cases hm : dl.getD j false
    · exact Or.inl rfl
    · right
      have := marked_facts dl (by omega) hm
      exact ⟨Nat.ble_eq_true_of_le this.1 |> fun h => by simpa using this.1, by simpa using this.2⟩
  · have := rank_facts dl hr
    refine ⟨⟨by simpa [hlen] using this.1, this.2.1⟩, by simpa using this.2.2⟩

end RH2F

-- ===== from EX3.lean =====

/-
  EX3.lean — a shared-walk EX1 certificate for three colourings at once. The three colours of an edge are packed
  as `c0 + 8 c1 + 64 c2`; one neighbour table (edge, other end, packed colours) serves all three colourings, and one
  enumeration of 4-edge walks checks all three. `ex3_sound`: a passed `ex3` check implies the library check `exCert`
  (fact ebeb33c568dfe4e4) for the three projected colourings, hence `EX1FullH` by `ex1Full_of_cert`.
-/

namespace RH2F
open MGraph

section ex3

/-- colour `i` of a packed triple -/
def dgc (i x : Nat) : Nat := x / 8 ^ i % 8 % 6

/-- the projection of a table entry to colour `i` -/
def projT3 (i : Nat) (t : Nat × Nat × Nat) : Nat × Nat × Nat := (t.1, t.2.1, dgc i t.2.2)

def projNB3 (i : Nat) (nb : List (List (Nat × Nat × Nat))) : List (List (Nat × Nat × Nat)) :=
  nb.map (fun row => row.map (projT3 i))

def projCL3 (i : Nat) (pc : List Nat) : List Nat := pc.map (dgc i)

/-- the table contains every edge at both ends, with its packed colours -/
def nbOK3 (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  (List.range el.length).all (fun e =>
    (nb.getD (gE el e).1 []).contains (e, (gE el e).2, pc.getD e 0) &&
    (nb.getD (gE el e).2 []).contains (e, (gE el e).1, pc.getD e 0))

def properNB3 (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  (List.range n).all (fun v => (nb.getD v []).all (fun a => (nb.getD v []).all (fun b =>
    Nat.beq a.1 b.1 || (!Nat.beq (dgc 0 a.2.2) (dgc 0 b.2.2) && !Nat.beq (dgc 1 a.2.2) (dgc 1 b.2.2) &&
      !Nat.beq (dgc 2 a.2.2) (dgc 2 b.2.2)))))

/-- colour `i` is bad on the walk `t1 t2 t3 t4` -/
def bad3 (i : Nat) (t1 t2 t3 t4 : Nat × Nat × Nat) : Bool :=
  Nat.beq (dgc i t1.2.2) (dgc i t3.2.2) && Nat.beq (dgc i t2.2.2) (dgc i t4.2.2)

def walk3 (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  (List.range n).all fun v0 => (nb.getD v0 []).all fun t1 =>
    (nb.getD t1.2.1 []).all fun t2 => Nat.beq t2.2.1 v0 || (nb.getD t2.2.1 []).all fun t3 =>
      (!Nat.beq (dgc 0 t1.2.2) (dgc 0 t3.2.2) && !Nat.beq (dgc 1 t1.2.2) (dgc 1 t3.2.2) &&
        !Nat.beq (dgc 2 t1.2.2) (dgc 2 t3.2.2)) || Nat.beq t3.2.1 t1.2.1 || (nb.getD t3.2.1 []).all fun t4 =>
        !((bad3 0 t1 t2 t3 t4 || bad3 1 t1 t2 t3 t4 || bad3 2 t1 t2 t3 t4) && !Nat.beq v0 t3.2.1 &&
          !Nat.beq t1.2.1 t4.2.1 && !Nat.beq t2.2.1 t4.2.1 && !Nat.beq t3.2.1 t4.2.1 && !Nat.beq v0 t1.2.1 &&
          !Nat.beq t1.2.1 t2.2.1 && !Nat.beq t2.2.1 t3.2.1)

def nbSound3 (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  (List.range n).all (fun v => (nb.getD v []).all (fun t => Nat.blt t.1 el.length &&
    ((Nat.beq (gE el t.1).1 v && Nat.beq (gE el t.1).2 t.2.1) || (Nat.beq (gE el t.1).1 t.2.1 && Nat.beq (gE el t.1).2 v)) &&
    Nat.beq t.2.2 (pc.getD t.1 0)))

def pmNB3 (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  (List.range n).all (fun v =>
    Nat.beq ((nb.getD v []).filter (fun t => Nat.beq (dgc 0 t.2.2) 5)).length 1 &&
    Nat.beq ((nb.getD v []).filter (fun t => Nat.beq (dgc 1 t.2.2) 5)).length 1 &&
    Nat.beq ((nb.getD v []).filter (fun t => Nat.beq (dgc 2 t.2.2) 5)).length 1)

def cover3 (el : List (Nat × Nat)) (pc : List Nat) : Bool :=
  (List.range el.length).all (fun e =>
    (Nat.beq (dgc 0 (pc.getD e 0)) 5 || Nat.beq (dgc 1 (pc.getD e 0)) 5 || Nat.beq (dgc 2 (pc.getD e 0)) 5) &&
    (!Nat.beq (dgc 0 (pc.getD e 0)) 5 || !Nat.beq (dgc 1 (pc.getD e 0)) 5 || !Nat.beq (dgc 2 (pc.getD e 0)) 5))

/-- **the shared-walk EX1 certificate** -/
def ex3 (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  elOK n el && nbOK3 el nb pc && properNB3 n nb && walk3 n nb && nbSound3 n el nb pc && pmNB3 n nb && cover3 el pc

/-! ### soundness: projection to the library check -/

theorem dgc_mod (i x : Nat) : dgc i x % 6 = dgc i x := by unfold dgc; exact Nat.mod_mod _ _

theorem getD_projNB3 (i : Nat) (nb : List (List (Nat × Nat × Nat))) (v : Nat) :
    (projNB3 i nb).getD v [] = (nb.getD v []).map (projT3 i) := by
  unfold projNB3
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases nb[v]? <;> rfl

theorem colN_projCL3 (i : Nat) (pc : List Nat) (e : Nat) : colN (projCL3 i pc) e = dgc i (pc.getD e 0) := by
  unfold colN projCL3
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases pc[e]? with
  | none => simp [dgc]
  | some x => simp [dgc_mod]

theorem nbOK_proj {el : List (Nat × Nat)} {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (h : nbOK3 el nb pc = true) (i : Nat) : nbOK el (projNB3 i nb) (projCL3 i pc) = true := by
  unfold nbOK3 at h; unfold nbOK
  rw [List.all_eq_true] at h ⊢
  intro e he
  have h1 := h e he
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h1 ⊢
  rw [getD_projNB3, getD_projNB3, colN_projCL3]
  exact ⟨List.mem_map.2 ⟨_, h1.1, rfl⟩, List.mem_map.2 ⟨_, h1.2, rfl⟩⟩

theorem properNB_proj {n : Nat} {nb : List (List (Nat × Nat × Nat))} (h : properNB3 n nb = true) (i : Nat)
    (hi : i = 0 ∨ i = 1 ∨ i = 2) : properNB n (projNB3 i nb) = true := by
  unfold properNB3 at h; unfold properNB
  simp only [List.all_eq_true, getD_projNB3, List.all_map, Function.comp_def] at h ⊢
  intro v hv a ha b hb
  have h3 := h v hv a ha b hb
  simp only [projT3, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h3 ⊢
  rcases h3 with h3 | ⟨⟨h30, h31⟩, h32⟩
  · exact Or.inl h3
  · right
    rcases hi with rfl | rfl | rfl
    · exact h30
    · exact h31
    · exact h32

theorem walk_proj {n : Nat} {nb : List (List (Nat × Nat × Nat))} (h : walk3 n nb = true) (i : Nat)
    (hi : i = 0 ∨ i = 1 ∨ i = 2) : walkNB n (projNB3 i nb) = true := by
  unfold walk3 at h; unfold walkNB
  rw [List.all_eq_true] at h ⊢
  intro v0 hv0
  have h1 := h v0 hv0
  rw [getD_projNB3, List.all_map, List.all_eq_true]
  rw [List.all_eq_true] at h1
  intro t1 ht1
  have h2 := h1 t1 ht1
  simp only [Function.comp, projT3] at h2 ⊢
  rw [getD_projNB3, List.all_map, List.all_eq_true]
  rw [List.all_eq_true] at h2
  intro t2 ht2
  have h3 := h2 t2 ht2
  simp only [Function.comp, projT3, Bool.or_eq_true] at h3 ⊢
  rcases h3 with h3 | h3
  · exact Or.inl h3
  right
  rw [getD_projNB3, List.all_map, List.all_eq_true]
  rw [List.all_eq_true] at h3
  intro t3 ht3
  have h4 := h3 t3 ht3
  simp only [Function.comp, projT3, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h4 ⊢
  -- colour i of t1 and t3
  by_cases hc : Nat.beq (dgc i t1.2.2) (dgc i t3.2.2) = true
  · rcases h4 with (⟨⟨a0, a1⟩, a2⟩ | h4) | h4
    · exfalso
      rcases hi with rfl | rfl | rfl
      · rw [a0] at hc; exact Bool.noConfusion hc
      · rw [a1] at hc; exact Bool.noConfusion hc
      · rw [a2] at hc; exact Bool.noConfusion hc
    · exact Or.inl (Or.inr h4)
    · right
      rw [getD_projNB3, List.all_map, List.all_eq_true]
      rw [List.all_eq_true] at h4
      intro t4 ht4
      have h5 := h4 t4 ht4
      simp only [Function.comp, projT3] at h5 ⊢
      rw [Bool.not_eq_true'] at h5 ⊢
      cases hb : Nat.beq (dgc i t2.2.2) (dgc i t4.2.2)
      · simp
      · have hbad : (bad3 0 t1 t2 t3 t4 || bad3 1 t1 t2 t3 t4 || bad3 2 t1 t2 t3 t4) = true := by
          rcases hi with rfl | rfl | rfl <;> simp [bad3, hc, hb]
        rw [hbad] at h5
        simpa using h5
  · left; left
    exact Bool.eq_false_iff.2 hc

theorem nbSound_proj {n : Nat} {el : List (Nat × Nat)} {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (h : nbSound3 n el nb pc = true) (i : Nat) : nbSound n el (projNB3 i nb) (projCL3 i pc) = true := by
  unfold nbSound3 at h; unfold nbSound
  rw [List.all_eq_true] at h ⊢
  intro v hv
  have h1 := h v hv
  rw [getD_projNB3, List.all_map, List.all_eq_true]
  rw [List.all_eq_true] at h1
  intro t ht
  have h2 := h1 t ht
  simp only [Function.comp, projT3, Bool.and_eq_true] at h2 ⊢
  refine ⟨h2.1, ?_⟩
  rw [colN_projCL3, Nat.eq_of_beq_eq_true h2.2]
  exact Nat.beq_refl _

theorem pmNB_proj {n : Nat} {nb : List (List (Nat × Nat × Nat))} (h : pmNB3 n nb = true) (i : Nat)
    (hi : i = 0 ∨ i = 1 ∨ i = 2) : pmNB n (projNB3 i nb) = true := by
  unfold pmNB3 at h; unfold pmNB
  rw [List.all_eq_true] at h ⊢
  intro v hv
  have h1 := h v hv
  rw [getD_projNB3, List.filter_map, List.length_map]
  simp only [Bool.and_eq_true] at h1
  rcases hi with rfl | rfl | rfl
  · exact h1.1.1
  · exact h1.1.2
  · exact h1.2

/-- **soundness of the shared-walk certificate**: it implies the library check for the three projected
    colourings -/
theorem ex3_sound {n : Nat} {el : List (Nat × Nat)} {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (h : ex3 n el nb pc = true) :
    exCert n el [(projNB3 0 nb, projCL3 0 pc), (projNB3 1 nb, projCL3 1 pc), (projNB3 2 nb, projCL3 2 pc)] = true := by
  unfold ex3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hel, hnb⟩, hpr⟩, hw⟩, hs⟩, hpm⟩, hcov⟩ := h
  have one : ∀ i, (i = 0 ∨ i = 1 ∨ i = 2) →
      (fastStar2 n el (projNB3 i nb) (projCL3 i pc) = true ∧ nbSound n el (projNB3 i nb) (projCL3 i pc) = true) ∧
        pmNB n (projNB3 i nb) = true := by
    intro i hi
    refine ⟨⟨?_, nbSound_proj hs i⟩, pmNB_proj hpm i hi⟩
    unfold fastStar2
    rw [hel, nbOK_proj hnb i, properNB_proj hpr i hi, walk_proj hw i hi]
    rfl
  unfold exCert
  rw [Bool.and_eq_true]
  constructor
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨one 0 (Or.inl rfl), one 1 (Or.inr (Or.inl rfl)), one 2 (Or.inr (Or.inr rfl))⟩
  · unfold cover3 at hcov
    rw [List.all_eq_true] at hcov ⊢
    intro e he
    have hc := hcov e he
    simp only [List.any_cons, List.any_nil, Bool.or_false, colN_projCL3]
    simpa [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using hc

theorem ex1Full_of_ex3 {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} {nb : List (List (Nat × Nat × Nat))}
    {pc : List Nat} (h : ex3 n el nb pc = true) : EX1FullH (ofList n el hn) :=
  ex1Full_of_cert (ex3_sound h)

end ex3

end RH2F

-- ===== from EX3R.lean =====

/-
  EX3R.lean — kernel-efficient forms of the checks: `List.all`, `List.any`, `List.getD`, `∀ v < n` and filtered
  lengths written with the recursors `List.rec` / `Nat.rec` (structural recursion compiles to `brecOn`, which the
  kernel evaluates with a large constant overhead). `ex3R_imp`: the recursor form of the shared-walk certificate
  implies `ex3`.
-/

namespace RH2F
open MGraph

section recforms

/-- `List.all` by the recursor -/
def allR {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => p x && ih) l

/-- `List.any` by the recursor -/
def anyR {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => p x || ih) l

/-- `List.getD` by the recursor -/
def getR {α : Type} (l : List α) (i : Nat) (d : α) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.casesOn (motive := fun _ => α) i x (fun i' => ih i')) l i

/-- `∀ v < n, p v` by the recursor -/
def rangeAll (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun v ih => ih && p v) n

/-- the number of entries satisfying `p` -/
def cntR {α : Type} (p : α → Bool) (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => (if p x then 1 else 0) + ih) l

theorem allR_eq {α : Type} (p : α → Bool) : ∀ l : List α, allR p l = l.all p
  | [] => rfl
  | x :: l => by
    show (p x && allR p l) = (x :: l).all p
    rw [allR_eq p l, List.all_cons]

theorem anyR_eq {α : Type} (p : α → Bool) : ∀ l : List α, anyR p l = l.any p
  | [] => rfl
  | x :: l => by
    show (p x || anyR p l) = (x :: l).any p
    rw [anyR_eq p l, List.any_cons]

theorem getR_eq {α : Type} : ∀ (l : List α) (i : Nat) (d : α), getR l i d = l.getD i d
  | [], _, _ => by simp [getR]
  | x :: l, 0, d => rfl
  | x :: l, i + 1, d => by
    show getR l i d = (x :: l).getD (i + 1) d
    rw [getR_eq l i d]; simp

theorem rangeAll_eq (p : Nat → Bool) : ∀ n, rangeAll n p = (List.range n).all p
  | 0 => rfl
  | n + 1 => by
    show (rangeAll n p && p n) = (List.range (n + 1)).all p
    rw [rangeAll_eq p n, List.range_succ, List.all_append]
    simp

theorem cntR_eq {α : Type} (p : α → Bool) : ∀ l : List α, cntR p l = (l.filter p).length
  | [] => rfl
  | x :: l => by
    show (if p x then 1 else 0) + cntR p l = ((x :: l).filter p).length
    rw [cntR_eq p l, List.filter_cons]
    cases p x <;> simp [Nat.add_comm]

end recforms

section ex3r

/-- membership of the triple `(e, y, c)` in a table row, componentwise -/
def memT (e y c : Nat) (row : List (Nat × Nat × Nat)) : Bool :=
  anyR (fun t => Nat.beq t.1 e && Nat.beq t.2.1 y && Nat.beq t.2.2 c) row

def gER (el : List (Nat × Nat)) (e : Nat) : Nat × Nat := getR el e (0, 0)

def nbOK3R (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  rangeAll el.length (fun e =>
    memT e (gER el e).2 (getR pc e 0) (getR nb (gER el e).1 []) &&
    memT e (gER el e).1 (getR pc e 0) (getR nb (gER el e).2 []))

def properNB3R (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  rangeAll n (fun v => allR (fun a => allR (fun b =>
    Nat.beq a.1 b.1 || (!Nat.beq (dgc 0 a.2.2) (dgc 0 b.2.2) && !Nat.beq (dgc 1 a.2.2) (dgc 1 b.2.2) &&
      !Nat.beq (dgc 2 a.2.2) (dgc 2 b.2.2))) (getR nb v [])) (getR nb v []))

def walk3R (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  rangeAll n fun v0 => allR (fun t1 =>
    allR (fun t2 => Nat.beq t2.2.1 v0 || allR (fun t3 =>
      (!Nat.beq (dgc 0 t1.2.2) (dgc 0 t3.2.2) && !Nat.beq (dgc 1 t1.2.2) (dgc 1 t3.2.2) &&
        !Nat.beq (dgc 2 t1.2.2) (dgc 2 t3.2.2)) || Nat.beq t3.2.1 t1.2.1 || allR (fun t4 =>
        !((bad3 0 t1 t2 t3 t4 || bad3 1 t1 t2 t3 t4 || bad3 2 t1 t2 t3 t4) && !Nat.beq v0 t3.2.1 &&
          !Nat.beq t1.2.1 t4.2.1 && !Nat.beq t2.2.1 t4.2.1 && !Nat.beq t3.2.1 t4.2.1 && !Nat.beq v0 t1.2.1 &&
          !Nat.beq t1.2.1 t2.2.1 && !Nat.beq t2.2.1 t3.2.1)) (getR nb t3.2.1 [])) (getR nb t2.2.1 []))
      (getR nb t1.2.1 [])) (getR nb v0 [])

def nbSound3R (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  rangeAll n (fun v => allR (fun t => Nat.blt t.1 el.length &&
    ((Nat.beq (gER el t.1).1 v && Nat.beq (gER el t.1).2 t.2.1) || (Nat.beq (gER el t.1).1 t.2.1 && Nat.beq (gER el t.1).2 v)) &&
    Nat.beq t.2.2 (getR pc t.1 0)) (getR nb v []))

def pmNB3R (n : Nat) (nb : List (List (Nat × Nat × Nat))) : Bool :=
  rangeAll n (fun v =>
    Nat.beq (cntR (fun t => Nat.beq (dgc 0 t.2.2) 5) (getR nb v [])) 1 &&
    Nat.beq (cntR (fun t => Nat.beq (dgc 1 t.2.2) 5) (getR nb v [])) 1 &&
    Nat.beq (cntR (fun t => Nat.beq (dgc 2 t.2.2) 5) (getR nb v [])) 1)

def cover3R (el : List (Nat × Nat)) (pc : List Nat) : Bool :=
  rangeAll el.length (fun e =>
    (Nat.beq (dgc 0 (getR pc e 0)) 5 || Nat.beq (dgc 1 (getR pc e 0)) 5 || Nat.beq (dgc 2 (getR pc e 0)) 5) &&
    (!Nat.beq (dgc 0 (getR pc e 0)) 5 || !Nat.beq (dgc 1 (getR pc e 0)) 5 || !Nat.beq (dgc 2 (getR pc e 0)) 5))

def elOKR (n : Nat) (el : List (Nat × Nat)) : Bool :=
  allR (fun e => e.1 < n && e.2 < n && e.1 != e.2) el

/-- **the shared-walk EX1 certificate, kernel-efficient form** -/
def ex3R (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  elOKR n el && nbOK3R el nb pc && properNB3R n nb && walk3R n nb && nbSound3R n el nb pc && pmNB3R n nb &&
    cover3R el pc

theorem memT_imp {e y c : Nat} {row : List (Nat × Nat × Nat)} (h : memT e y c row = true) :
    row.contains (e, y, c) = true := by
  unfold memT at h
  rw [anyR_eq, List.any_eq_true] at h
  obtain ⟨t, ht, h⟩ := h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [List.contains_iff_mem]
  have : t = (e, y, c) := by
    obtain ⟨a, b, d⟩ := t
    simp only at h1 h2 h3
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]
  rw [← this]; exact ht

theorem elOKR_eq (n : Nat) (el : List (Nat × Nat)) : elOKR n el = elOK n el := by
  unfold elOKR elOK
  rw [allR_eq]

/-- **the kernel-efficient certificate implies the plain one** -/
theorem ex3R_imp {n : Nat} {el : List (Nat × Nat)} {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (h : ex3R n el nb pc = true) : ex3 n el nb pc = true := by
  unfold ex3R at h
  unfold ex3
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨⟨⟨⟨⟨⟨(elOKR_eq n el) ▸ h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold nbOK3R at h2; unfold nbOK3
    rw [rangeAll_eq] at h2
    rw [List.all_eq_true] at h2 ⊢
    intro e he
    have := h2 e he
    simp only [Bool.and_eq_true, gER, getR_eq] at this ⊢
    exact ⟨memT_imp this.1, memT_imp this.2⟩
  · unfold properNB3R at h3; unfold properNB3
    simpa only [rangeAll_eq, allR_eq, getR_eq] using h3
  · unfold walk3R at h4; unfold walk3
    simpa only [rangeAll_eq, allR_eq, getR_eq] using h4
  · unfold nbSound3R at h5; unfold nbSound3
    simpa only [rangeAll_eq, allR_eq, getR_eq, gER, gE] using h5
  · unfold pmNB3R at h6; unfold pmNB3
    simpa only [rangeAll_eq, cntR_eq, getR_eq] using h6
  · unfold cover3R at h7; unfold cover3
    simpa only [rangeAll_eq, getR_eq] using h7

theorem ex1Full_of_ex3R {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n} {nb : List (List (Nat × Nat × Nat))}
    {pc : List Nat} (h : ex3R n el nb pc = true) : EX1FullH (ofList n el hn) :=
  ex1Full_of_ex3 (ex3R_imp h)

end ex3r

end RH2F

-- ===== from SH2b.lean =====

/-
  SH2.lean — the reduction of SMALLHOST-D to finitely many explicit digon insertions:
  * `IsoC`: the data of an isomorphism (`IsoFrom` with named maps);
  * binary codes of markings;
  * `autOK` and `isoC_aut`: composing an isomorphism with a checked automorphism of the target;
  * `count_dl`: the marking `dl` of the host edges induced by `D` through an isomorphism, with `|Q ∩ D| = cntT dl`;
  * `tri_excl`: a c4c edge set is not isomorphic to an explicit multigraph with a 3-edge-cut having two vertices on
    each side.
-/

namespace RH2F
open MGraph
open Classical

section sh2

/-- the named data of an isomorphism `(α, β)` from `Q` onto `H` (the body of `IsoFrom`) -/
def IsoC {X H : MGraph} (Q : Fin X.m → Prop) (α : Fin X.n → Fin H.n) (β : Fin X.m → Fin H.m) : Prop :=
  (∀ x y, meets Q x → meets Q y → α x = α y → x = y) ∧ (∀ f g, Q f → Q g → β f = β g → f = g) ∧
  (∀ j, ∃ f, Q f ∧ β f = j) ∧ (∀ f, Q f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2))

/-! ### binary codes of markings -/

/-- the code `Σ dl[j] 2^j` of a marking -/
def codeB : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * codeB l

/-- the marking of length `m` with code `c` -/
def decodeB : Nat → Nat → List Bool
  | 0, _ => []
  | m + 1, c => (c % 2 == 1) :: decodeB m (c / 2)

theorem decode_code : ∀ l : List Bool, decodeB l.length (codeB l) = l
  | [] => rfl
  | b :: l => by
    simp only [List.length_cons, decodeB, codeB]
    have h1 : (((if b then 1 else 0) + 2 * codeB l) % 2 == 1) = b := by cases b <;> simp
    have h2 : ((if b then 1 else 0) + 2 * codeB l) / 2 = codeB l := by cases b <;> simp <;> omega
    rw [h1, h2, decode_code l]

theorem code_lt : ∀ l : List Bool, codeB l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have := code_lt l
    simp only [codeB, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

/-! ### automorphisms of an explicit multigraph -/

/-- `a = (sv, se)` is an automorphism of `ofList n el`: `sv` an injective self-map of the vertices, `se` a
    bijection of the edges, and every edge `j` is mapped to an edge joining the images of the ends of `j` -/
def autOK (n : Nat) (el : List (Nat × Nat)) (a : List Nat × List Nat) : Bool :=
  (List.range n).all (fun x => Nat.blt (a.1.getD x 0) n) &&
  (List.range n).all (fun x => (List.range n).all (fun y => a.1.getD x 0 != a.1.getD y 0 || x == y)) &&
  (List.range el.length).all (fun j => Nat.blt (a.2.getD j 0) el.length) &&
  (List.range el.length).all (fun i => (List.range el.length).all (fun j => a.2.getD i 0 != a.2.getD j 0 || i == j)) &&
  (List.range el.length).all (fun j => (List.range el.length).any (fun i => a.2.getD i 0 == j)) &&
  (List.range el.length).all (fun j =>
    ((gE el (a.2.getD j 0)).1 == a.1.getD (gE el j).1 0 && (gE el (a.2.getD j 0)).2 == a.1.getD (gE el j).2 0) ||
    ((gE el (a.2.getD j 0)).1 == a.1.getD (gE el j).2 0 && (gE el (a.2.getD j 0)).2 == a.1.getD (gE el j).1 0))

/-- **composition with an automorphism** -/
theorem isoC_aut {X : MGraph} {Q : Fin X.m → Prop} {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}
    (hel : elOK n el = true) {a : List Nat × List Nat} (ha : autOK n el a = true) (hm0 : 0 < el.length)
    {α : Fin X.n → Fin (ofList n el hn).n} {β : Fin X.m → Fin (ofList n el hn).m} (h : IsoC Q α β) :
    ∃ (α2 : Fin X.n → Fin (ofList n el hn).n) (β2 : Fin X.m → Fin (ofList n el hn).m), IsoC Q α2 β2 ∧
      ∀ f, (β2 f).val = a.2.getD (β f).val 0 := by
  obtain ⟨hα, hβ, hs, hj⟩ := h
  unfold autOK at ha
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at ha
  obtain ⟨⟨⟨⟨⟨hv1, hv2⟩, he1⟩, he2⟩, he3⟩, he4⟩ := ha
  have hvlt : ∀ x, x < n → Nat.blt (a.1.getD x 0) n = true := hv1
  have hvlt' : ∀ x, x < n → a.1.getD x 0 < n := fun x hx => Nat.le_of_ble_eq_true (hvlt x hx)
  have helt : ∀ j, j < el.length → a.2.getD j 0 < el.length := fun j hj => Nat.le_of_ble_eq_true (he1 j hj)
  let α2 : Fin X.n → Fin (ofList n el hn).n := fun x => ⟨a.1.getD (α x).val 0 % n, Nat.mod_lt _ hn⟩
  let β2 : Fin X.m → Fin (ofList n el hn).m := fun f => ⟨a.2.getD (β f).val 0 % el.length, Nat.mod_lt _ hm0⟩
  have hα2 : ∀ x, (α2 x).val = a.1.getD (α x).val 0 := fun x => Nat.mod_eq_of_lt (hvlt' _ (α x).isLt)
  have hβ2 : ∀ f, (β2 f).val = a.2.getD (β f).val 0 := fun f => Nat.mod_eq_of_lt (helt _ (β f).isLt)
  refine ⟨α2, β2, ⟨fun x y hx hy hxy => ?_, fun f g hf hg hfg => ?_, fun j => ?_, fun f hf => ?_⟩, hβ2⟩
  · have e := congrArg Fin.val hxy
    rw [hα2, hα2] at e
    have := hv2 _ (α x).isLt _ (α y).isLt
    exact hα x y hx hy (Fin.ext (Classical.byContradiction fun hne => (this.resolve_right hne) e))
  · have e := congrArg Fin.val hfg
    rw [hβ2, hβ2] at e
    have := he2 _ (β f).isLt _ (β g).isLt
    exact hβ f g hf hg (Fin.ext (Classical.byContradiction fun hne => (this.resolve_right hne) e))
  · obtain ⟨i, hi, hij⟩ := he3 j.val j.isLt
    obtain ⟨f, hf, hfi⟩ := hs ⟨i, hi⟩
    refine ⟨f, hf, Fin.ext ?_⟩
    rw [hβ2, hfi]; exact hij
  · have hb := host_vals hel (hj f hf)
    have hc := he4 _ (β f).isLt
    have he := ofList_ends (hn := hn) hel (β2 f)
    rw [hβ2] at he
    unfold MGraph.Joins
    rcases hb with hb | hb <;> rw [hb] at hc <;> simp only at hc
    · rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · left; exact Prod.ext (Fin.ext (he.1.trans (c1.trans (hα2 _).symm))) (Fin.ext (he.2.trans (c2.trans (hα2 _).symm)))
      · right; exact Prod.ext (Fin.ext (he.1.trans (c1.trans (hα2 _).symm))) (Fin.ext (he.2.trans (c2.trans (hα2 _).symm)))
    · rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · right; exact Prod.ext (Fin.ext (he.1.trans (c1.trans (hα2 _).symm))) (Fin.ext (he.2.trans (c2.trans (hα2 _).symm)))
      · left; exact Prod.ext (Fin.ext (he.1.trans (c1.trans (hα2 _).symm))) (Fin.ext (he.2.trans (c2.trans (hα2 _).symm)))

/-! ### the marking induced by `D` and its count -/

theorem count_ofFn : ∀ (m : Nat) (g : Fin m → Bool), (List.ofFn g).count true = cntF m (fun j => g j = true)
  | 0, _ => rfl
  | m + 1, g => by
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append, count_ofFn m, cntF_succ]
    cases h : g (Fin.last m) <;> simp [h]

/-- the marking of the host edges induced by `D` through an isomorphism, and its properties -/
theorem count_dl {X H : MGraph} {Q D : Fin X.m → Prop} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m}
    (h : IsoC Q α β) :
    ∃ dl : List Bool, dl.length = H.m ∧ (∀ f, Q f → (D f ↔ dl.getD (β f).val false = true)) ∧
      cntF X.m (fun d => Q d ∧ D d) = cntT dl := by
  obtain ⟨_, hβ, hs, _⟩ := h
  let W : Fin H.m → Prop := fun j => ∃ f, Q f ∧ β f = j ∧ D f
  refine ⟨List.ofFn (fun j => decide (W j)), by simp, fun f hf => ?_, ?_⟩
  · have hlt : (β f).val < (List.ofFn (fun j => decide (W j))).length := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
    simp only [decide_eq_true_eq]
    constructor
    · intro hd; exact ⟨f, hf, rfl, hd⟩
    · rintro ⟨g, hg, hgf, hd⟩
      rwa [hβ g f hg hf hgf] at hd
  · unfold cntT
    rw [count_ofFn, cntF_congr _ _ W (fun j => decide_eq_true_iff), cntF_eq_card, cntF_eq_card]
    rw [← Finset.card_image_of_injOn (f := β)]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, W]
      constructor
      · rintro ⟨f, ⟨hf, hd⟩, rfl⟩; exact ⟨f, hf, rfl, hd⟩
      · rintro ⟨f, hf, rfl, hd⟩; exact ⟨f, ⟨hf, hd⟩, rfl⟩
    · intro f hf g hg hfg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf hg
      exact hβ f g hf.1 hg.1 hfg

/-! ### excluding explicit multigraphs with a cyclic 3-edge-cut -/

/-- a 3-edge-cut `S` of `ofList n el` with the given vertices `t1 ≠ t2` in `S` and `u1 ≠ u2` outside, each with a
    listed incident edge -/
def cutOK3 (n : Nat) (el : List (Nat × Nat)) (S : List Bool) (t1 t2 u1 u2 et1 et2 eu1 eu2 : Nat) : Bool :=
  ((List.range el.length).filter (fun j => S.getD (gE el j).1 false != S.getD (gE el j).2 false)).length == 3 &&
  Nat.blt t1 n && Nat.blt t2 n && Nat.blt u1 n && Nat.blt u2 n && t1 != t2 && u1 != u2 &&
  S.getD t1 false && S.getD t2 false && !S.getD u1 false && !S.getD u2 false &&
  Nat.blt et1 el.length && Nat.blt et2 el.length && Nat.blt eu1 el.length && Nat.blt eu2 el.length &&
  incN el et1 t1 && incN el et2 t2 && incN el eu1 u1 && incN el eu2 u2

theorem tri_excl {Y : MGraph} {Q : Fin Y.m → Prop} {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}
    (hel : elOK n el = true) (hC : C4C Y Q) {α : Fin Y.n → Fin (ofList n el hn).n}
    {β : Fin Y.m → Fin (ofList n el hn).m} (h : IsoC Q α β) {S : List Bool} {t1 t2 u1 u2 et1 et2 eu1 eu2 : Nat}
    (ht : cutOK3 n el S t1 t2 u1 u2 et1 et2 eu1 eu2 = true) : False := by
  obtain ⟨hα, hβ, hs, hj⟩ := h
  unfold cutOK3 at ht
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcr, ht1⟩, ht2⟩, hu1⟩, hu2⟩, htt⟩, huu⟩, hSt1⟩, hSt2⟩, hSu1⟩, hSu2⟩, he1⟩, he2⟩, he3⟩, he4⟩,
    hi1⟩, hi2⟩, hi3⟩, hi4⟩ := ht
  let S' : Fin Y.n → Bool := fun x => S.getD (α x).val false
  -- crossing edges correspond
  have hcross : ∀ f, Q f → (Crosses Q S' f ↔
      (S.getD (gE el (β f).val).1 false ≠ S.getD (gE el (β f).val).2 false)) := by
    intro f hf
    unfold Crosses
    rcases host_vals hel (hj f hf) with hb | hb <;> rw [hb] <;> simp only [S']
    · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
    · exact ⟨fun h => fun e => h.2 e.symm, fun h => ⟨hf, fun e => h e.symm⟩⟩
  -- the three crossing host edges
  obtain ⟨j1, j2, j3, hL⟩ := list_three hcr
  have hmem : ∀ j, j ∈ (List.range el.length).filter
      (fun j => S.getD (gE el j).1 false != S.getD (gE el j).2 false) ↔
      j < el.length ∧ S.getD (gE el j).1 false ≠ S.getD (gE el j).2 false := by
    intro j; simp [List.mem_filter, List.mem_range]
  have hnd : ((List.range el.length).filter
      (fun j => S.getD (gE el j).1 false != S.getD (gE el j).2 false)).Nodup := List.Nodup.filter _ List.nodup_range
  rw [hL] at hmem hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨n12, n13⟩, n23⟩ := hnd
  have c1 := (hmem j1).1 (by simp)
  have c2 := (hmem j2).1 (by simp)
  have c3 := (hmem j3).1 (by simp)
  obtain ⟨f1, hf1, hb1⟩ := hs ⟨j1, c1.1⟩
  obtain ⟨f2, hf2, hb2⟩ := hs ⟨j2, c2.1⟩
  obtain ⟨f3, hf3, hb3⟩ := hs ⟨j3, c3.1⟩
  have v1 : (β f1).val = j1 := by rw [hb1]
  have v2 : (β f2).val = j2 := by rw [hb2]
  have v3 : (β f3).val = j3 := by rw [hb3]
  have h3 : ThreeCut Q S' := by
    refine ⟨f1, f2, f3, fun e => n12 (by rw [← v1, ← v2, e]), fun e => n13 (by rw [← v1, ← v3, e]),
      fun e => n23 (by rw [← v2, ← v3, e]), (hcross f1 hf1).2 (by rw [v1]; exact c1.2),
      (hcross f2 hf2).2 (by rw [v2]; exact c2.2), (hcross f3 hf3).2 (by rw [v3]; exact c3.2), fun d hd => ?_⟩
    have hdQ := hd.1
    have hx := (hmem (β d).val).2 ⟨(β d).isLt, (hcross d hdQ).1 hd⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with e | e | e
    · exact Or.inl (hβ d f1 hdQ hf1 (Fin.ext (e.trans v1.symm)))
    · exact Or.inr (Or.inl (hβ d f2 hdQ hf2 (Fin.ext (e.trans v2.symm))))
    · exact Or.inr (Or.inr (hβ d f3 hdQ hf3 (Fin.ext (e.trans v3.symm))))
  -- a host vertex with a listed incident edge has a preimage meeting `Q`
  have pre : ∀ t e, t < n → e < el.length → incN el e t = true →
      ∃ x, meets Q x ∧ (α x).val = t := by
    intro t e ht he hi
    obtain ⟨f, hf, hfe⟩ := hs ⟨e, he⟩
    have hv : (β f).val = e := by rw [hfe]
    unfold incN at hi
    simp only [Bool.or_eq_true, beq_iff_eq] at hi
    rw [← hv] at hi
    rcases host_vals hel (hj f hf) with hb | hb <;> rw [hb] at hi <;> simp only at hi
    · rcases hi with e1 | e1
      · exact ⟨_, ⟨f, hf, Or.inl rfl⟩, e1⟩
      · exact ⟨_, ⟨f, hf, Or.inr rfl⟩, e1⟩
    · rcases hi with e1 | e1
      · exact ⟨_, ⟨f, hf, Or.inr rfl⟩, e1⟩
      · exact ⟨_, ⟨f, hf, Or.inl rfl⟩, e1⟩
  obtain ⟨x1, mx1, ax1⟩ := pre t1 et1 (Nat.le_of_ble_eq_true ht1) (Nat.le_of_ble_eq_true he1) hi1
  obtain ⟨x2, mx2, ax2⟩ := pre t2 et2 (Nat.le_of_ble_eq_true ht2) (Nat.le_of_ble_eq_true he2) hi2
  obtain ⟨y1, my1, ay1⟩ := pre u1 eu1 (Nat.le_of_ble_eq_true hu1) (Nat.le_of_ble_eq_true he3) hi3
  obtain ⟨y2, my2, ay2⟩ := pre u2 eu2 (Nat.le_of_ble_eq_true hu2) (Nat.le_of_ble_eq_true he4) hi4
  have sx1 : S' x1 = true := by simp only [S']; rw [ax1]; exact hSt1
  have sx2 : S' x2 = true := by simp only [S']; rw [ax2]; exact hSt2
  have sy1 : S' y1 = false := by simp only [S']; rw [ay1]; exact hSu1
  have sy2 : S' y2 = false := by simp only [S']; rw [ay2]; exact hSu2
  rcases hC.2.2 S' h3 with h1 | h1
  · have := cntF_one_uniq (W := fun v => meets Q v ∧ S' v = true) (le_of_eq h1) ⟨mx1, sx1⟩ ⟨mx2, sx2⟩
    exact htt (by rw [← ax1, ← ax2, this])
  · have := cntF_one_uniq (W := fun v => meets Q v ∧ S' v = false) (le_of_eq h1) ⟨my1, sy1⟩ ⟨my2, sy2⟩
    exact huu (by rw [← ay1, ← ay2, this])

end sh2

end RH2F

-- ===== from SH3b.lean =====

/-
  SH3b.lean — the orbit coverage by a bitset: for the host automorphisms (edge maps `se`) and the representative
  codes `rc`, the bitset `orSet` has bit `c` set exactly for the codes `c` of the markings `j ↦ rc[se[j]]`; `covR`
  checks that every marking code with `n + 2 |dl| ≥ 16` is set (`orbit_sound`). Also: the recursor form of the
  automorphism check, and the code-based main case of SMALLHOST-D.
-/

namespace RH2F
open MGraph
open Classical

section bits

/-- bit `j` of `x` -/
def bitN (x j : Nat) : Nat := x / 2 ^ j % 2

theorem bitN_lt (x j : Nat) : bitN x j < 2 := Nat.mod_lt _ (by decide)

theorem bitN_eq (x j : Nat) : bitN x j = if x.testBit j then 1 else 0 := by
  unfold bitN
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem bitN_zero_of (b N : Nat) (hb : b < 2) : bitN (b + 2 * N) 0 = b := by
  unfold bitN; simp; omega

theorem bitN_succ_of (b N j : Nat) (hb : b < 2) : bitN (b + 2 * N) (j + 1) = bitN N j := by
  unfold bitN
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
  have : (b + 2 * N) / 2 = N := by omega
  rw [this]

theorem bit_codeB : ∀ (dl : List Bool) (j : Nat), bitN (codeB dl) j = if dl.getD j false then 1 else 0
  | [], j => by simp [codeB, bitN]
  | b :: l, 0 => by
    simp only [codeB]
    rw [bitN_zero_of _ _ (by cases b <;> simp)]
    cases b <;> simp
  | b :: l, j + 1 => by
    simp only [codeB]
    rw [bitN_succ_of _ _ _ (by cases b <;> simp), bit_codeB l j]
    simp

theorem length_decodeB : ∀ (m c : Nat), (decodeB m c).length = m
  | 0, _ => rfl
  | m + 1, c => by simp [decodeB, length_decodeB m]

theorem getD_decodeB : ∀ (m c s : Nat), s < m → ((decodeB m c).getD s false = true ↔ bitN c s = 1)
  | 0, _, _, h => absurd h (by omega)
  | m + 1, c, 0, _ => by
    simp only [decodeB, List.getD_cons_zero, beq_iff_eq]
    unfold bitN; simp
  | m + 1, c, s + 1, h => by
    simp only [decodeB, List.getD_cons_succ]
    rw [getD_decodeB m (c / 2) s (by omega)]
    unfold bitN
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, ← Nat.div_div_eq_div_mul]

/-- the number of set bits of `c` below `m` -/
def popc (c : Nat) (m : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun j ih => ih + bitN c j) m

theorem popc_codeB (dl : List Bool) : ∀ m, m ≤ dl.length → popc (codeB dl) m = (dl.take m).count true
  | 0, _ => by simp [popc]
  | m + 1, hm => by
    show popc (codeB dl) m + bitN (codeB dl) m = _
    rw [popc_codeB dl m (by omega), bit_codeB, List.take_succ, List.count_append]
    have hlt : m < dl.length := by omega
    rw [List.getElem?_eq_getElem hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    cases dl[m] <;> simp

/-- the code of the marking `j ↦ rc[se[j]]` -/
def imgC (rc : Nat) (se : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun s _ ih => bitN rc s + 2 * ih) se

theorem bit_imgC (rc : Nat) : ∀ (se : List Nat) (j : Nat), j < se.length → bitN (imgC rc se) j = bitN rc (se.getD j 0)
  | [], _, h => absurd h (by simp)
  | s :: rest, 0, _ => by
    show bitN (bitN rc s + 2 * imgC rc rest) 0 = _
    rw [bitN_zero_of _ _ (bitN_lt _ _)]; rfl
  | s :: rest, j + 1, h => by
    show bitN (bitN rc s + 2 * imgC rc rest) (j + 1) = _
    rw [bitN_succ_of _ _ _ (bitN_lt _ _), bit_imgC rc rest j (by simpa using h)]
    rfl

/-- the bitset of all codes `imgC rc se`, `se ∈ SE`, `rc ∈ RC` -/
def orIn (se : List Nat) (RC : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a) (fun rc _ ih a => ih (a ||| 2 ^ imgC rc se)) RC acc

def orOut (SE : List (List Nat)) (RC : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a) (fun se _ ih a => ih (orIn se RC a)) SE acc

def orSet (SE : List (List Nat)) (RC : List Nat) : Nat := orOut SE RC 0

theorem orIn_bit (se : List Nat) : ∀ (RC : List Nat) (acc c : Nat), (orIn se RC acc).testBit c = true →
    acc.testBit c = true ∨ ∃ rc ∈ RC, imgC rc se = c
  | [], acc, c, h => Or.inl h
  | rc :: RC, acc, c, h => by
    rcases orIn_bit se RC (acc ||| 2 ^ imgC rc se) c h with h1 | ⟨r, hr, e⟩
    · rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨rc, List.mem_cons_self, of_decide_eq_true h1⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, e⟩

theorem orOut_bit (RC : List Nat) : ∀ (SE : List (List Nat)) (acc c : Nat), (orOut SE RC acc).testBit c = true →
    acc.testBit c = true ∨ ∃ se ∈ SE, ∃ rc ∈ RC, imgC rc se = c
  | [], acc, c, h => Or.inl h
  | se :: SE, acc, c, h => by
    rcases orOut_bit RC SE (orIn se RC acc) c h with h1 | ⟨s, hs, r, hr, e⟩
    · rcases orIn_bit se RC acc c h1 with h2 | ⟨r, hr, e⟩
      · exact Or.inl h2
      · exact Or.inr ⟨se, List.mem_cons_self, r, hr, e⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, r, hr, e⟩

theorem orSet_bit {SE : List (List Nat)} {RC : List Nat} {c : Nat} (h : (orSet SE RC).testBit c = true) :
    ∃ se ∈ SE, ∃ rc ∈ RC, imgC rc se = c := by
  rcases orOut_bit RC SE 0 c h with h1 | h1
  · simp at h1
  · exact h1

/-- every marking code with `n + 2 |dl| ≥ 16` lies in the bitset `B` -/
def covR (n m B : Nat) : Bool :=
  rangeAll (2 ^ m) (fun c => Nat.blt (n + 2 * popc c m) 16 || Nat.beq (bitN B c) 1)

/-- **soundness of the orbit coverage** -/
theorem orbit_sound {n m : Nat} {SE : List (List Nat)} {RC : List Nat} (h : covR n m (orSet SE RC) = true)
    (hSE : ∀ se ∈ SE, se.length = m) (dl : List Bool) (hl : dl.length = m) (h16 : 16 ≤ n + 2 * cntT dl) :
    ∃ se ∈ SE, ∃ rc ∈ RC, ∀ j, j < m → (bitN rc (se.getD j 0) = 1 ↔ dl.getD j false = true) := by
  unfold covR at h
  rw [rangeAll_eq, List.all_eq_true] at h
  have hc : codeB dl < 2 ^ m := hl ▸ code_lt dl
  have h1 := h (codeB dl) (List.mem_range.2 hc)
  have hpop : popc (codeB dl) m = cntT dl := by
    rw [popc_codeB dl m (by omega), ← hl, List.take_length]; rfl
  rw [hpop] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd (Nat.le_of_ble_eq_true h1) (by omega)
  · rw [bitN_eq] at h1
    have hb : (orSet SE RC).testBit (codeB dl) = true := by
      cases h2 : (orSet SE RC).testBit (codeB dl)
      · rw [h2] at h1; simp at h1
      · rfl
    obtain ⟨se, hse, rc, hrc, e⟩ := orSet_bit hb
    refine ⟨se, hse, rc, hrc, fun j hj => ?_⟩
    have e1 := bit_imgC rc se j (by rw [hSE se hse]; exact hj)
    rw [e, bit_codeB] at e1
    rw [← e1]
    cases dl.getD j false <;> simp

end bits

/-! ### the automorphism check, recursor form -/

def autOKR (n : Nat) (el : List (Nat × Nat)) (a : List Nat × List Nat) : Bool :=
  rangeAll n (fun x => Nat.blt (getR a.1 x 0) n) &&
  rangeAll n (fun x => rangeAll n (fun y => getR a.1 x 0 != getR a.1 y 0 || x == y)) &&
  rangeAll el.length (fun j => Nat.blt (getR a.2 j 0) el.length) &&
  rangeAll el.length (fun i => rangeAll el.length (fun j => getR a.2 i 0 != getR a.2 j 0 || i == j)) &&
  rangeAll el.length (fun j => anyR (fun i => getR a.2 i 0 == j) (List.range el.length)) &&
  rangeAll el.length (fun j =>
    ((gER el (getR a.2 j 0)).1 == getR a.1 (gER el j).1 0 && (gER el (getR a.2 j 0)).2 == getR a.1 (gER el j).2 0) ||
    ((gER el (getR a.2 j 0)).1 == getR a.1 (gER el j).2 0 && (gER el (getR a.2 j 0)).2 == getR a.1 (gER el j).1 0)) &&
  Nat.beq a.2.length el.length

theorem autOKR_imp {n : Nat} {el : List (Nat × Nat)} {a : List Nat × List Nat} (h : autOKR n el a = true) :
    autOK n el a = true ∧ a.2.length = el.length := by
  unfold autOKR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, Nat.eq_of_beq_eq_true h2⟩
  unfold autOK
  simpa only [rangeAll_eq, getR_eq, anyR_eq, gER, gE, Bool.and_eq_true] using h1

/-! ### the main case, with representative codes -/

/-- the compact digon insertion of the host `Rep k` at the marking with code `rc` -/
def digOfCode (k rc : Nat) : MGraph :=
  ofList (repN k + 2 * cntT (decodeB (repL k).length rc)) (digEl (repN k) (repL k) (decodeB (repL k).length rc))
    (Nat.lt_of_lt_of_le (repN_pos k) (Nat.le_add_right _ _))

theorem main_code {Y : MGraph} {Q D : Fin Y.m → Prop} (hC : C4C Y Q) {k : Nat}
    (h16 : 16 ≤ repN k + 2 * cntF Y.m (fun d => Q d ∧ D d)) (hiso : IsoFrom Q (repG k))
    (hel : elOK (repN k) (repL k) = true) (hm0 : 0 < (repL k).length)
    {AUT : List (List Nat × List Nat)} (haut : allR (autOKR (repN k) (repL k)) AUT = true)
    {RC : List Nat} (hcov : covR (repN k) (repL k).length (orSet (AUT.map Prod.snd) RC) = true)
    (hfull : ∀ rc ∈ RC, EX1FullH (digOfCode k rc)) : EX1On (digSet Q D) := by
  obtain ⟨α, β, hc⟩ := hiso
  obtain ⟨dl, hlen, hD, hcnt⟩ := count_dl (D := D) (show IsoC Q α β from hc)
  have h16' : 16 ≤ repN k + 2 * cntT dl := by rw [← hcnt]; exact h16
  rw [allR_eq, List.all_eq_true] at haut
  have hSE : ∀ se ∈ AUT.map Prod.snd, se.length = (repL k).length := by
    intro se hse
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hse
    exact (autOKR_imp (haut a ha)).2
  obtain ⟨se, hse, rc, hrc, hbits⟩ := orbit_sound hcov hSE dl hlen h16'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hse
  have hA := (autOKR_imp (haut a ha)).1
  obtain ⟨α2, β2, hc2, hβ2⟩ := isoC_aut (hn := repN_pos k) hel hA hm0 (show IsoC Q α β from hc)
  have hse_lt : ∀ j, j < (repL k).length → a.2.getD j 0 < (repL k).length := by
    intro j hj
    unfold autOK at hA
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hA
    exact Nat.le_of_ble_eq_true (hA.1.1.1.2 j hj)
  have hD2 : ∀ f, Q f → (D f ↔ (decodeB (repL k).length rc).getD (β2 f).val false = true) := by
    intro f hf
    have hb := (β f).isLt
    change (β f).val < (repL k).length at hb
    rw [hD f hf, hβ2 f, getD_decodeB _ _ _ (hse_lt _ hb), hbits _ hb]
  have hI := dig_iso hC.1.1 hel (digOK_of hel (length_decodeB _ _)) hc2.1 hc2.2.1 hc2.2.2.1 hc2.2.2.2 hD2
    (Nat.lt_of_lt_of_le (repN_pos k) (Nat.le_add_right _ _)) hm0
  exact ex1On_of_iso hI (hfull rc hrc)

end RH2F

-- ===== from SH4.lean =====

/-
  SH4.lean — the data of the four hosts K₄ = Rep 3, K₃,₃ = Rep 8, Q₃ = Rep 24, V₈ = Rep 25: automorphisms
  (vertex map, edge map) and the codes of the representative markings; the kernel checks of the automorphisms and of
  the orbit coverage; the chunk checker for EX1 certificates; and SMALLHOST-D from the certificates
  (`smallhostd_of`).
-/

namespace RH2F
open MGraph
open Classical

section sh4

/-- automorphisms of the hosts: (vertex map, edge map) -/
def shAut : Nat → List (List Nat × List Nat)
  | 3 => [([0, 1, 2, 3], [0, 1, 2, 3, 4, 5]), ([0, 1, 3, 2], [0, 2, 1, 5, 4, 3]), ([0, 2, 1, 3], [3, 1, 4, 0, 2, 5]), ([0, 2, 3, 1], [3, 4, 1, 5, 2, 0]), ([0, 3, 1, 2], [5, 2, 4, 0, 1, 3]), ([0, 3, 2, 1], [5, 4, 2, 3, 1, 0]), ([1, 0, 2, 3], [0, 3, 5, 1, 4, 2]), ([1, 0, 3, 2], [0, 5, 3, 2, 4, 1]), ([1, 2, 0, 3], [1, 3, 4, 0, 5, 2]), ([1, 2, 3, 0], [1, 4, 3, 2, 5, 0]), ([1, 3, 0, 2], [2, 5, 4, 0, 3, 1]), ([1, 3, 2, 0], [2, 4, 5, 1, 3, 0]), ([2, 0, 1, 3], [3, 0, 5, 1, 2, 4]), ([2, 0, 3, 1], [3, 5, 0, 4, 2, 1]), ([2, 1, 0, 3], [1, 0, 2, 3, 5, 4]), ([2, 1, 3, 0], [1, 2, 0, 4, 5, 3]), ([2, 3, 0, 1], [4, 5, 2, 3, 0, 1]), ([2, 3, 1, 0], [4, 2, 5, 1, 0, 3]), ([3, 0, 1, 2], [5, 0, 3, 2, 1, 4]), ([3, 0, 2, 1], [5, 3, 0, 4, 1, 2]), ([3, 1, 0, 2], [2, 0, 1, 5, 3, 4]), ([3, 1, 2, 0], [2, 1, 0, 4, 3, 5]), ([3, 2, 0, 1], [4, 3, 1, 5, 0, 2]), ([3, 2, 1, 0], [4, 1, 3, 2, 0, 5])]
  | 8 => [([0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7, 8]), ([0, 1, 2, 3, 5, 4], [0, 2, 1, 3, 5, 4, 6, 8, 7]), ([0, 1, 2, 4, 3, 5], [1, 0, 2, 4, 3, 5, 7, 6, 8]), ([0, 1, 2, 4, 5, 3], [1, 2, 0, 4, 5, 3, 7, 8, 6]), ([0, 1, 2, 5, 3, 4], [2, 0, 1, 5, 3, 4, 8, 6, 7]), ([0, 1, 2, 5, 4, 3], [2, 1, 0, 5, 4, 3, 8, 7, 6]), ([0, 2, 1, 3, 4, 5], [0, 1, 2, 6, 7, 8, 3, 4, 5]), ([0, 2, 1, 3, 5, 4], [0, 2, 1, 6, 8, 7, 3, 5, 4]), ([0, 2, 1, 4, 3, 5], [1, 0, 2, 7, 6, 8, 4, 3, 5]), ([0, 2, 1, 4, 5, 3], [1, 2, 0, 7, 8, 6, 4, 5, 3]), ([0, 2, 1, 5, 3, 4], [2, 0, 1, 8, 6, 7, 5, 3, 4]), ([0, 2, 1, 5, 4, 3], [2, 1, 0, 8, 7, 6, 5, 4, 3]), ([1, 0, 2, 3, 4, 5], [3, 4, 5, 0, 1, 2, 6, 7, 8]), ([1, 0, 2, 3, 5, 4], [3, 5, 4, 0, 2, 1, 6, 8, 7]), ([1, 0, 2, 4, 3, 5], [4, 3, 5, 1, 0, 2, 7, 6, 8]), ([1, 0, 2, 4, 5, 3], [4, 5, 3, 1, 2, 0, 7, 8, 6]), ([1, 0, 2, 5, 3, 4], [5, 3, 4, 2, 0, 1, 8, 6, 7]), ([1, 0, 2, 5, 4, 3], [5, 4, 3, 2, 1, 0, 8, 7, 6]), ([1, 2, 0, 3, 4, 5], [3, 4, 5, 6, 7, 8, 0, 1, 2]), ([1, 2, 0, 3, 5, 4], [3, 5, 4, 6, 8, 7, 0, 2, 1]), ([1, 2, 0, 4, 3, 5], [4, 3, 5, 7, 6, 8, 1, 0, 2]), ([1, 2, 0, 4, 5, 3], [4, 5, 3, 7, 8, 6, 1, 2, 0]), ([1, 2, 0, 5, 3, 4], [5, 3, 4, 8, 6, 7, 2, 0, 1]), ([1, 2, 0, 5, 4, 3], [5, 4, 3, 8, 7, 6, 2, 1, 0]), ([2, 0, 1, 3, 4, 5], [6, 7, 8, 0, 1, 2, 3, 4, 5]), ([2, 0, 1, 3, 5, 4], [6, 8, 7, 0, 2, 1, 3, 5, 4]), ([2, 0, 1, 4, 3, 5], [7, 6, 8, 1, 0, 2, 4, 3, 5]), ([2, 0, 1, 4, 5, 3], [7, 8, 6, 1, 2, 0, 4, 5, 3]), ([2, 0, 1, 5, 3, 4], [8, 6, 7, 2, 0, 1, 5, 3, 4]), ([2, 0, 1, 5, 4, 3], [8, 7, 6, 2, 1, 0, 5, 4, 3]), ([2, 1, 0, 3, 4, 5], [6, 7, 8, 3, 4, 5, 0, 1, 2]), ([2, 1, 0, 3, 5, 4], [6, 8, 7, 3, 5, 4, 0, 2, 1]), ([2, 1, 0, 4, 3, 5], [7, 6, 8, 4, 3, 5, 1, 0, 2]), ([2, 1, 0, 4, 5, 3], [7, 8, 6, 4, 5, 3, 1, 2, 0]), ([2, 1, 0, 5, 3, 4], [8, 6, 7, 5, 3, 4, 2, 0, 1]), ([2, 1, 0, 5, 4, 3], [8, 7, 6, 5, 4, 3, 2, 1, 0]), ([3, 4, 5, 0, 1, 2], [0, 3, 6, 1, 4, 7, 2, 5, 8]), ([3, 4, 5, 0, 2, 1], [0, 6, 3, 1, 7, 4, 2, 8, 5]), ([3, 4, 5, 1, 0, 2], [3, 0, 6, 4, 1, 7, 5, 2, 8]), ([3, 4, 5, 1, 2, 0], [3, 6, 0, 4, 7, 1, 5, 8, 2]), ([3, 4, 5, 2, 0, 1], [6, 0, 3, 7, 1, 4, 8, 2, 5]), ([3, 4, 5, 2, 1, 0], [6, 3, 0, 7, 4, 1, 8, 5, 2]), ([3, 5, 4, 0, 1, 2], [0, 3, 6, 2, 5, 8, 1, 4, 7]), ([3, 5, 4, 0, 2, 1], [0, 6, 3, 2, 8, 5, 1, 7, 4]), ([3, 5, 4, 1, 0, 2], [3, 0, 6, 5, 2, 8, 4, 1, 7]), ([3, 5, 4, 1, 2, 0], [3, 6, 0, 5, 8, 2, 4, 7, 1]), ([3, 5, 4, 2, 0, 1], [6, 0, 3, 8, 2, 5, 7, 1, 4]), ([3, 5, 4, 2, 1, 0], [6, 3, 0, 8, 5, 2, 7, 4, 1]), ([4, 3, 5, 0, 1, 2], [1, 4, 7, 0, 3, 6, 2, 5, 8]), ([4, 3, 5, 0, 2, 1], [1, 7, 4, 0, 6, 3, 2, 8, 5]), ([4, 3, 5, 1, 0, 2], [4, 1, 7, 3, 0, 6, 5, 2, 8]), ([4, 3, 5, 1, 2, 0], [4, 7, 1, 3, 6, 0, 5, 8, 2]), ([4, 3, 5, 2, 0, 1], [7, 1, 4, 6, 0, 3, 8, 2, 5]), ([4, 3, 5, 2, 1, 0], [7, 4, 1, 6, 3, 0, 8, 5, 2]), ([4, 5, 3, 0, 1, 2], [1, 4, 7, 2, 5, 8, 0, 3, 6]), ([4, 5, 3, 0, 2, 1], [1, 7, 4, 2, 8, 5, 0, 6, 3]), ([4, 5, 3, 1, 0, 2], [4, 1, 7, 5, 2, 8, 3, 0, 6]), ([4, 5, 3, 1, 2, 0], [4, 7, 1, 5, 8, 2, 3, 6, 0]), ([4, 5, 3, 2, 0, 1], [7, 1, 4, 8, 2, 5, 6, 0, 3]), ([4, 5, 3, 2, 1, 0], [7, 4, 1, 8, 5, 2, 6, 3, 0]), ([5, 3, 4, 0, 1, 2], [2, 5, 8, 0, 3, 6, 1, 4, 7]), ([5, 3, 4, 0, 2, 1], [2, 8, 5, 0, 6, 3, 1, 7, 4]), ([5, 3, 4, 1, 0, 2], [5, 2, 8, 3, 0, 6, 4, 1, 7]), ([5, 3, 4, 1, 2, 0], [5, 8, 2, 3, 6, 0, 4, 7, 1]), ([5, 3, 4, 2, 0, 1], [8, 2, 5, 6, 0, 3, 7, 1, 4]), ([5, 3, 4, 2, 1, 0], [8, 5, 2, 6, 3, 0, 7, 4, 1]), ([5, 4, 3, 0, 1, 2], [2, 5, 8, 1, 4, 7, 0, 3, 6]), ([5, 4, 3, 0, 2, 1], [2, 8, 5, 1, 7, 4, 0, 6, 3]), ([5, 4, 3, 1, 0, 2], [5, 2, 8, 4, 1, 7, 3, 0, 6]), ([5, 4, 3, 1, 2, 0], [5, 8, 2, 4, 7, 1, 3, 6, 0]), ([5, 4, 3, 2, 0, 1], [8, 2, 5, 7, 1, 4, 6, 0, 3]), ([5, 4, 3, 2, 1, 0], [8, 5, 2, 7, 4, 1, 6, 3, 0])]
  | 24 => [([0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]), ([0, 1, 3, 2, 4, 5, 7, 6], [0, 2, 1, 3, 5, 4, 7, 6, 10, 11, 8, 9]), ([0, 2, 1, 3, 4, 6, 5, 7], [1, 0, 2, 4, 3, 5, 8, 9, 6, 7, 11, 10]), ([0, 2, 3, 1, 4, 6, 7, 5], [1, 2, 0, 4, 5, 3, 9, 8, 11, 10, 6, 7]), ([0, 3, 1, 2, 4, 7, 5, 6], [2, 0, 1, 5, 3, 4, 10, 11, 7, 6, 9, 8]), ([0, 3, 2, 1, 4, 7, 6, 5], [2, 1, 0, 5, 4, 3, 11, 10, 9, 8, 7, 6]), ([1, 0, 6, 7, 5, 4, 2, 3], [0, 6, 7, 3, 8, 10, 1, 2, 4, 11, 5, 9]), ([1, 0, 7, 6, 5, 4, 3, 2], [0, 7, 6, 3, 10, 8, 2, 1, 5, 9, 4, 11]), ([1, 6, 0, 7, 5, 2, 4, 3], [6, 0, 7, 8, 3, 10, 4, 11, 1, 2, 9, 5]), ([1, 6, 7, 0, 5, 2, 3, 4], [6, 7, 0, 8, 10, 3, 11, 4, 9, 5, 1, 2]), ([1, 7, 0, 6, 5, 3, 4, 2], [7, 0, 6, 10, 3, 8, 5, 9, 2, 1, 11, 4]), ([1, 7, 6, 0, 5, 3, 2, 4], [7, 6, 0, 10, 8, 3, 9, 5, 11, 4, 2, 1]), ([2, 0, 5, 7, 6, 4, 1, 3], [1, 8, 9, 4, 6, 11, 0, 2, 3, 10, 5, 7]), ([2, 0, 7, 5, 6, 4, 3, 1], [1, 9, 8, 4, 11, 6, 2, 0, 5, 7, 3, 10]), ([2, 5, 0, 7, 6, 1, 4, 3], [8, 1, 9, 6, 4, 11, 3, 10, 0, 2, 7, 5]), ([2, 5, 7, 0, 6, 1, 3, 4], [8, 9, 1, 6, 11, 4, 10, 3, 7, 5, 0, 2]), ([2, 7, 0, 5, 6, 3, 4, 1], [9, 1, 8, 11, 4, 6, 5, 7, 2, 0, 10, 3]), ([2, 7, 5, 0, 6, 3, 1, 4], [9, 8, 1, 11, 6, 4, 7, 5, 10, 3, 2, 0]), ([3, 0, 5, 6, 7, 4, 1, 2], [2, 10, 11, 5, 7, 9, 0, 1, 3, 8, 4, 6]), ([3, 0, 6, 5, 7, 4, 2, 1], [2, 11, 10, 5, 9, 7, 1, 0, 4, 6, 3, 8]), ([3, 5, 0, 6, 7, 1, 4, 2], [10, 2, 11, 7, 5, 9, 3, 8, 0, 1, 6, 4]), ([3, 5, 6, 0, 7, 1, 2, 4], [10, 11, 2, 7, 9, 5, 8, 3, 6, 4, 0, 1]), ([3, 6, 0, 5, 7, 2, 4, 1], [11, 2, 10, 9, 5, 7, 4, 6, 1, 0, 8, 3]), ([3, 6, 5, 0, 7, 2, 1, 4], [11, 10, 2, 9, 7, 5, 6, 4, 8, 3, 1, 0]), ([4, 5, 6, 7, 0, 1, 2, 3], [3, 4, 5, 0, 1, 2, 8, 10, 6, 11, 7, 9]), ([4, 5, 7, 6, 0, 1, 3, 2], [3, 5, 4, 0, 2, 1, 10, 8, 7, 9, 6, 11]), ([4, 6, 5, 7, 0, 2, 1, 3], [4, 3, 5, 1, 0, 2, 6, 11, 8, 10, 9, 7]), ([4, 6, 7, 5, 0, 2, 3, 1], [4, 5, 3, 1, 2, 0, 11, 6, 9, 7, 8, 10]), ([4, 7, 5, 6, 0, 3, 1, 2], [5, 3, 4, 2, 0, 1, 7, 9, 10, 8, 11, 6]), ([4, 7, 6, 5, 0, 3, 2, 1], [5, 4, 3, 2, 1, 0, 9, 7, 11, 6, 10, 8]), ([5, 2, 3, 4, 1, 6, 7, 0], [8, 10, 3, 6, 7, 0, 9, 1, 11, 2, 4, 5]), ([5, 2, 4, 3, 1, 6, 0, 7], [8, 3, 10, 6, 0, 7, 1, 9, 4, 5, 11, 2]), ([5, 3, 2, 4, 1, 7, 6, 0], [10, 8, 3, 7, 6, 0, 11, 2, 9, 1, 5, 4]), ([5, 3, 4, 2, 1, 7, 0, 6], [10, 3, 8, 7, 0, 6, 2, 11, 5, 4, 9, 1]), ([5, 4, 2, 3, 1, 0, 6, 7], [3, 8, 10, 0, 6, 7, 4, 5, 1, 9, 2, 11]), ([5, 4, 3, 2, 1, 0, 7, 6], [3, 10, 8, 0, 7, 6, 5, 4, 2, 11, 1, 9]), ([6, 1, 3, 4, 2, 5, 7, 0], [6, 11, 4, 8, 9, 1, 7, 0, 10, 2, 3, 5]), ([6, 1, 4, 3, 2, 5, 0, 7], [6, 4, 11, 8, 1, 9, 0, 7, 3, 5, 10, 2]), ([6, 3, 1, 4, 2, 7, 5, 0], [11, 6, 4, 9, 8, 1, 10, 2, 7, 0, 5, 3]), ([6, 3, 4, 1, 2, 7, 0, 5], [11, 4, 6, 9, 1, 8, 2, 10, 5, 3, 7, 0]), ([6, 4, 1, 3, 2, 0, 5, 7], [4, 6, 11, 1, 8, 9, 3, 5, 0, 7, 2, 10]), ([6, 4, 3, 1, 2, 0, 7, 5], [4, 11, 6, 1, 9, 8, 5, 3, 2, 10, 0, 7]), ([7, 1, 2, 4, 3, 5, 6, 0], [7, 9, 5, 10, 11, 2, 6, 0, 8, 1, 3, 4]), ([7, 1, 4, 2, 3, 5, 0, 6], [7, 5, 9, 10, 2, 11, 0, 6, 3, 4, 8, 1]), ([7, 2, 1, 4, 3, 6, 5, 0], [9, 7, 5, 11, 10, 2, 8, 1, 6, 0, 4, 3]), ([7, 2, 4, 1, 3, 6, 0, 5], [9, 5, 7, 11, 2, 10, 1, 8, 4, 3, 6, 0]), ([7, 4, 1, 2, 3, 0, 5, 6], [5, 7, 9, 2, 10, 11, 3, 4, 0, 6, 1, 8]), ([7, 4, 2, 1, 3, 0, 6, 5], [5, 9, 7, 2, 11, 10, 4, 3, 1, 8, 0, 6])]
  | 25 => [([0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]), ([0, 2, 1, 3, 7, 6, 5, 4], [1, 0, 2, 5, 4, 3, 7, 6, 10, 11, 8, 9]), ([1, 0, 5, 7, 6, 2, 4, 3], [0, 6, 10, 7, 8, 9, 1, 3, 4, 5, 2, 11]), ([1, 5, 0, 7, 3, 4, 2, 6], [6, 0, 10, 9, 8, 7, 3, 1, 2, 11, 4, 5]), ([2, 0, 6, 4, 5, 1, 7, 3], [1, 7, 8, 6, 10, 11, 0, 5, 4, 3, 2, 9]), ([2, 6, 0, 4, 3, 7, 1, 5], [7, 1, 8, 11, 10, 6, 5, 0, 2, 9, 4, 3]), ([3, 4, 7, 0, 1, 5, 6, 2], [9, 11, 2, 6, 4, 7, 3, 5, 10, 0, 8, 1]), ([3, 7, 4, 0, 2, 6, 5, 1], [11, 9, 2, 7, 4, 6, 5, 3, 8, 1, 10, 0]), ([4, 3, 5, 2, 6, 7, 1, 0], [9, 3, 8, 5, 10, 0, 11, 6, 4, 7, 2, 1]), ([4, 5, 3, 2, 0, 1, 7, 6], [3, 9, 8, 0, 10, 5, 6, 11, 2, 1, 4, 7]), ([5, 1, 4, 6, 2, 0, 3, 7], [6, 3, 4, 1, 2, 11, 0, 9, 8, 7, 10, 5]), ([5, 4, 1, 6, 7, 3, 0, 2], [3, 6, 4, 11, 2, 1, 9, 0, 10, 5, 8, 7]), ([6, 2, 7, 5, 1, 0, 3, 4], [7, 5, 4, 0, 2, 9, 1, 11, 10, 6, 8, 3]), ([6, 7, 2, 5, 4, 3, 0, 1], [5, 7, 4, 9, 2, 0, 11, 1, 8, 3, 10, 6]), ([7, 3, 6, 1, 5, 4, 2, 0], [11, 5, 10, 3, 8, 1, 9, 7, 4, 6, 2, 0]), ([7, 6, 3, 1, 0, 2, 4, 5], [5, 11, 10, 1, 8, 3, 7, 9, 2, 0, 4, 6])]
  | _ => []

/-- the codes `Σ dl[j] 2^j` of the representative markings of the hosts -/
def shRC : Nat → List Nat
  | 3 => [63]
  | 8 => [496, 504, 484, 468, 244, 500, 220, 476, 508, 238, 494, 510, 511]
  | 24 => [3840, 3712, 3456, 3968, 4032, 3616, 3360, 2848, 1824, 3872, 2720, 3744, 2464, 1440, 3488, 928, 2976, 1952, 4000, 2400, 3424, 864, 2912, 1888, 3936, 992, 3040, 4064, 1328, 3376, 3888, 3248, 1712, 3760, 432, 2480, 1456, 3504, 944, 2992, 1968, 4016, 240, 2288, 1264, 3312, 2800, 1776, 3824, 1520, 3568, 4080, 1336, 3384, 3896, 2744, 3768, 2488, 3512, 1976, 4024, 4088, 3748, 2468, 3492, 4004, 356, 2404, 3428, 2916, 1892, 3940, 4068, 404, 2452, 1428, 3476, 2964, 1940, 3988, 1620, 3668, 1876, 3924, 1492, 3540, 2004, 4052, 3508, 4020, 1396, 3444, 1908, 3956, 1780, 3828, 500, 2548, 1524, 3572, 3060, 2036, 4084, 2460, 3484, 2972, 1948, 3996, 3932, 988, 3036, 4060, 4028, 3452, 1916, 3964, 1020, 3068, 4092, 1526, 3574, 4086, 3822, 2542, 3566, 4078, 3582, 4094, 4095]
  | 25 => [3840, 3712, 3456, 2944, 1920, 3968, 3264, 2752, 1728, 3776, 1472, 3520, 4032, 3616, 3360, 2848, 3872, 2720, 3744, 2976, 4000, 3168, 2656, 1632, 3680, 2400, 1376, 3424, 864, 2912, 1888, 3936, 2272, 1248, 3296, 736, 2784, 1760, 3808, 480, 2528, 1504, 3552, 992, 3040, 2016, 4064, 3600, 3344, 3856, 3216, 2704, 1680, 3728, 2448, 1424, 3472, 912, 2960, 1936, 3984, 3280, 2768, 1744, 3792, 1488, 3536, 4048, 3120, 3632, 3376, 816, 2864, 1840, 3888, 3248, 688, 2736, 1712, 3760, 1456, 3504, 944, 2992, 1968, 4016, 1136, 3184, 2672, 1648, 3696, 368, 2416, 1392, 3440, 880, 2928, 1904, 3952, 3312, 752, 2800, 1776, 3824, 496, 2544, 1520, 3568, 1008, 3056, 2032, 4080, 3368, 3880, 3240, 680, 2728, 1704, 3752, 3496, 936, 2984, 1960, 4008, 232, 2280, 1256, 3304, 2792, 1768, 3816, 1512, 3560, 4072, 3384, 3896, 3256, 1720, 3768, 3512, 952, 3000, 1976, 4024, 248, 2296, 1272, 3320, 2808, 1784, 3832, 1528, 3576, 4088, 2756, 1732, 3780, 1476, 3524, 4036, 356, 2404, 1380, 3428, 868, 2916, 1892, 3940, 740, 2788, 1764, 3812, 2532, 1508, 3556, 996, 3044, 2020, 4068, 1300, 3348, 3860, 3732, 3476, 1940, 3988, 2772, 3796, 3540, 4052, 3892, 3764, 4020, 1396, 3444, 2932, 1908, 3956, 756, 2804, 1780, 3828, 3572, 1012, 3060, 2036, 4084, 1708, 3756, 1964, 4012, 236, 2284, 1260, 3308, 2796, 1772, 3820, 1516, 3564, 4076, 1980, 4028, 252, 2300, 1276, 3324, 2812, 1788, 3836, 1532, 3580, 4092, 2754, 3778, 3010, 4034, 610, 2658, 1634, 3682, 2914, 1890, 3938, 2786, 3810, 3042, 4066, 3794, 3026, 4050, 1650, 3698, 882, 2930, 1906, 3954, 3826, 1010, 3058, 2034, 4082, 2762, 3786, 3018, 4042, 3306, 746, 2794, 1770, 3818, 3562, 1002, 3050, 2026, 4074, 3802, 2522, 3546, 3034, 4058, 3706, 3962, 1786, 3834, 3578, 1018, 3066, 2042, 4090, 4054, 1910, 3958, 4086, 1774, 3822, 3566, 2030, 4078, 4062, 2046, 4094, 2795, 3819, 4075, 3835, 4091, 4095]
  | _ => []

theorem sh_aut3 : allR (autOKR (repN 3) (repL 3)) (shAut 3) = true := by decide +kernel
theorem sh_cov3 : covR (repN 3) (repL 3).length (orSet ((shAut 3).map Prod.snd) (shRC 3)) = true := by
  decide +kernel

theorem sh_aut8 : allR (autOKR (repN 8) (repL 8)) (shAut 8) = true := by decide +kernel
theorem sh_cov8 : covR (repN 8) (repL 8).length (orSet ((shAut 8).map Prod.snd) (shRC 8)) = true := by
  decide +kernel

theorem sh_aut24 : allR (autOKR (repN 24) (repL 24)) (shAut 24) = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem sh_cov24 : covR (repN 24) (repL 24).length (orSet ((shAut 24).map Prod.snd) (shRC 24)) = true := by
  decide +kernel

theorem sh_aut25 : allR (autOKR (repN 25) (repL 25)) (shAut 25) = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem sh_cov25 : covR (repN 25) (repL 25).length (orSet ((shAut 25).map Prod.snd) (shRC 25)) = true := by
  decide +kernel


/-- EX1-fullness of all representatives of the host `k` -/
def RepsFullK (k : Nat) : Prop := ∀ rc ∈ shRC k, EX1FullH (digOfCode k rc)

/-- the chunk checker: the `j`-th certificate `(nb, pc)` of `cs` checks the representative `i + j` of host `k` -/
def chunkAux (k : Nat) (cs : List (List (List (Nat × Nat × Nat)) × List Nat)) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun q _ ih i => ex3R (repN k + 2 * cntT (decodeB (repL k).length (getR (shRC k) i 0)))
       (digEl (repN k) (repL k) (decodeB (repL k).length (getR (shRC k) i 0))) q.1 q.2 && ih (i + 1)) cs i

theorem chunk_sound (k : Nat) : ∀ (cs : List (List (List (Nat × Nat × Nat)) × List Nat)) (i : Nat),
    chunkAux k cs i = true → ∀ j, j < cs.length → EX1FullH (digOfCode k ((shRC k).getD (i + j) 0))
  | [], _, _, j, hj => absurd hj (by simp)
  | q :: cs, i, h, j, hj => by
    have h' : (ex3R (repN k + 2 * cntT (decodeB (repL k).length (getR (shRC k) i 0)))
       (digEl (repN k) (repL k) (decodeB (repL k).length (getR (shRC k) i 0))) q.1 q.2 && chunkAux k cs (i + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases j with
    | zero =>
      rw [getR_eq] at h'
      exact ex1Full_of_ex3R h'.1
    | succ j =>
      have := chunk_sound k cs (i + 1) h'.2 j (by simpa using hj)
      rwa [show i + (j + 1) = i + 1 + j by omega]

theorem range_block {P : Nat → Prop} {a n : Nat} (h : ∀ j, j < n → P (a + j)) :
    ∀ r, a ≤ r → r < a + n → P r := by
  intro r h1 h2
  have := h (r - a) (by omega)
  rwa [show a + (r - a) = r by omega] at this

theorem range_join {P : Nat → Prop} {a b c : Nat} (h1 : ∀ r, a ≤ r → r < b → P r)
    (h2 : ∀ r, b ≤ r → r < c → P r) : ∀ r, a ≤ r → r < c → P r := by
  intro r ha hc
  by_cases hb : r < b
  · exact h1 r ha hb
  · exact h2 r (by omega) hc

theorem repsFull_of (k : Nat) (h : ∀ r, r < (shRC k).length → EX1FullH (digOfCode k ((shRC k).getD r 0))) :
    RepsFullK k := by
  intro rc hrc
  obtain ⟨r, hr, e⟩ := List.getElem_of_mem hrc
  have := h r hr
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some, e] at this

theorem k25_cases {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 25) : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨
    k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 := by omega

/-- **SMALLHOST-D from the EX1-fullness of the representatives** -/
theorem smallhostd_of (h3 : RepsFullK 3) (h8 : RepsFullK 8) (h24 : RepsFullK 24) (h25 : RepsFullK 25) :
    SMALLHOSTD := by
  intro Y Q D hC hS h8' h16
  have hG := hC.1
  have hpos : 0 < vcount Q := by
    by_contra h0
    have h0' : vcount Q = 0 := by omega
    have hno : ∀ f, ¬ Q f := fun f hf => by
      have := cntF_le_of_mem _ (meets Q) (i := (Y.ends f).1) ⟨f, hf, Or.inl rfl⟩
      unfold vcount at h0'; omega
    have : cntF Y.m (fun d => Q d ∧ D d) = 0 := cntF_eq_zero _ _ (fun f h => hno f h.1)
    omega
  obtain ⟨k, hk1, hk25, hkn, hiso⟩ := cls _ Y Q hG rfl hpos h8'
  rcases k25_cases hk1 hk25 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (simple_of_iso hiso hS (p := ⟨0, by decide⟩) (q := ⟨1, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨0, by decide⟩) (q := ⟨1, by decide⟩) (by decide) (by decide)).elim
  · exact main_code hC (by rw [hkn]; exact h16) hiso (by decide) (by decide) sh_aut3 sh_cov3 h3
  · exact (simple_of_iso hiso hS (p := ⟨0, by decide⟩) (q := ⟨1, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨2, by decide⟩) (q := ⟨3, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨6, by decide⟩) (q := ⟨7, by decide⟩) (by decide) (by decide)).elim
  · obtain ⟨α, β, hc⟩ := hiso
    exact (tri_excl (hn := repN_pos 7) (el := repL 7) (by decide) hC (show IsoC Q α β from hc) (S := [true, false, false, false, true, true]) (t1 := 0) (t2 := 4) (u1 := 1) (u2 := 2) (et1 := 0) (et2 := 3) (eu1 := 0) (eu2 := 1) (by decide)).elim
  · exact main_code hC (by rw [hkn]; exact h16) hiso (by decide) (by decide) sh_aut8 sh_cov8 h8
  · exact (simple_of_iso hiso hS (p := ⟨1, by decide⟩) (q := ⟨2, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨0, by decide⟩) (q := ⟨1, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨1, by decide⟩) (q := ⟨2, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨1, by decide⟩) (q := ⟨2, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨5, by decide⟩) (q := ⟨6, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨5, by decide⟩) (q := ⟨6, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨9, by decide⟩) (q := ⟨10, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨5, by decide⟩) (q := ⟨6, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨5, by decide⟩) (q := ⟨6, by decide⟩) (by decide) (by decide)).elim
  · obtain ⟨α, β, hc⟩ := hiso
    exact (tri_excl (hn := repN_pos 18) (el := repL 18) (by decide) hC (show IsoC Q α β from hc) (S := [true, false, true, true, false, false, false, false]) (t1 := 0) (t2 := 2) (u1 := 1) (u2 := 4) (et1 := 2) (et2 := 0) (eu1 := 0) (eu2 := 5) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨9, by decide⟩) (q := ⟨10, by decide⟩) (by decide) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨9, by decide⟩) (q := ⟨10, by decide⟩) (by decide) (by decide)).elim
  · obtain ⟨α, β, hc⟩ := hiso
    exact (tri_excl (hn := repN_pos 21) (el := repL 21) (by decide) hC (show IsoC Q α β from hc) (S := [true, false, false, false, false, false, true, true]) (t1 := 0) (t2 := 6) (u1 := 1) (u2 := 2) (et1 := 0) (et2 := 6) (eu1 := 0) (eu2 := 1) (by decide)).elim
  · exact (simple_of_iso hiso hS (p := ⟨9, by decide⟩) (q := ⟨10, by decide⟩) (by decide) (by decide)).elim
  · obtain ⟨α, β, hc⟩ := hiso
    exact (tri_excl (hn := repN_pos 23) (el := repL 23) (by decide) hC (show IsoC Q α β from hc) (S := [true, false, false, false, false, false, true, true]) (t1 := 0) (t2 := 6) (u1 := 1) (u2 := 2) (et1 := 0) (et2 := 1) (eu1 := 3) (eu2 := 6) (by decide)).elim
  · exact main_code hC (by rw [hkn]; exact h16) hiso (by decide) (by decide) sh_aut24 sh_cov24 h24
  · exact main_code hC (by rw [hkn]; exact h16) hiso (by decide) (by decide) sh_aut25 sh_cov25 h25

end sh4

end RH2F
