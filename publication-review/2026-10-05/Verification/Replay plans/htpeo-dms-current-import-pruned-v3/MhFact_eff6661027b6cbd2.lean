-- Lean proof of fact eff6661027b6cbd2 (RH2F.layer31a); added by fact_submit, do not edit
import MhFact_54ed0ff9a1ed26b6
set_option backward.isDefEq.respectTransparency false

-- ===== from DC1.lean =====
/-
  DC1 — `isoFrom_of_rep`: a plain correspondence `Rep (subEn X P) Z Q'` (fact 6c78409a046a3fe7) followed by
  `IsoFrom Q' H` gives `IsoFrom P H`.
-/

namespace RH2F
open MGraph
open Classical

section dc1

/-! ### from a plain correspondence to `IsoFrom` -/

/-- `Rep (subEn X P) Z Q'` followed by `IsoFrom Q' H` gives `IsoFrom P H` -/
theorem isoFrom_of_rep {X Z H : MGraph} {P : Fin X.m → Prop} {Q' : Fin Z.m → Prop}
    (R : RH2Fid.Rep (RH2Fid.subEn X P) Z Q') (hI : IsoFrom Q' H) (hHn : 0 < H.n) (hHm : 0 < H.m) :
    IsoFrom P H := by
  obtain ⟨α', β', hα', hβ', hs', hj'⟩ := hI
  -- `φ v` meets `Q'`
  have hφm : ∀ v : RH2Fid.SubV X P, meets Q' (R.φ v) := by
    intro v
    obtain ⟨f, hf, hfv⟩ := v.2
    let e : RH2Fid.SubE X P := ⟨f, hf⟩
    refine ⟨R.ψ e, R.ψP e, (R.inc_iff e v).2 ?_⟩
    show v ∈ RH2Fid.subEn X P e
    unfold RH2Fid.subEn
    rcases hfv with h | h
    · have : v = ⟨(X.ends f).1, f, hf, Or.inl rfl⟩ := Subtype.ext h.symm
      rw [this]; exact Sym2.mem_mk_left _ _
    · have : v = ⟨(X.ends f).2, f, hf, Or.inr rfl⟩ := Subtype.ext h.symm
      rw [this]; exact Sym2.mem_mk_right _ _
  let α : Fin X.n → Fin H.n := fun x => if h : meets P x then α' (R.φ ⟨x, h⟩) else ⟨0, hHn⟩
  let β : Fin X.m → Fin H.m := fun f => if h : P f then β' (R.ψ ⟨f, h⟩) else ⟨0, hHm⟩
  have hαv : ∀ x (h : meets P x), α x = α' (R.φ ⟨x, h⟩) := fun x h => by simp only [α, dif_pos h]
  have hβv : ∀ f (h : P f), β f = β' (R.ψ ⟨f, h⟩) := fun f h => by simp only [β, dif_pos h]
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy h
    rw [hαv x hx, hαv y hy] at h
    have := R.φinj _ _ (hα' _ _ (hφm _) (hφm _) h)
    exact congrArg Subtype.val this
  · intro f g hf hg h
    rw [hβv f hf, hβv g hg] at h
    have := R.ψinj _ _ (hβ' _ _ (R.ψP _) (R.ψP _) h)
    exact congrArg Subtype.val this
  · intro j
    obtain ⟨f', hf', rfl⟩ := hs' j
    obtain ⟨e, rfl⟩ := R.ψsurj f' hf'
    exact ⟨e.1, e.2, by rw [hβv e.1 e.2]⟩
  · intro f hf
    let e : RH2Fid.SubE X P := ⟨f, hf⟩
    have ms : meets P (X.ends f).1 := ⟨f, hf, Or.inl rfl⟩
    have mt : meets P (X.ends f).2 := ⟨f, hf, Or.inr rfl⟩
    rw [hβv f hf, hαv _ ms, hαv _ mt]
    have hj := hj' _ (R.ψP e)
    have hjs : Z.Joins (R.ψ e) (R.φ ⟨(X.ends f).1, ms⟩) (R.φ ⟨(X.ends f).2, mt⟩) :=
      (R.joins_iff e _ _).2 rfl
    rcases joins_unique (Or.inl rfl : Z.Joins (R.ψ e) (Z.ends (R.ψ e)).1 (Z.ends (R.ψ e)).2) hjs with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hj
    · rw [← h1, ← h2]; exact Or.symm hj

end dc1

end RH2F

-- ===== from DC0.lean =====
/-
  DC0 — orbit coverage of the digon sets of a fixed size by a bitset, enumerating only the markings of that size.
  * `scB p k d acc`: `p (acc + c)` for every `c < 2^k` with exactly `d` set bits below `k` (pruned recursion);
    `scB_sound`.
  * `covS q lo hi m B`: every marking code with `m` bits and `lo ≤ q + 2 |dl| ≤ …`, `|dl| ≤ hi`, is set in `B`;
    `orbit_sound2` (with `B = orSet` of the automorphism images of the representative codes).
  * `dig_class_code`, `digClassC`: the property-free classification of digon insertions with representative codes.
-/

namespace RH2F
open MGraph
open Classical

section dc0

/-! ### bits below `k` -/

theorem bitN_add_high (a b k j : Nat) (hj : j < k) : bitN (a + 2 ^ k * b) j = bitN a j := by
  unfold bitN
  have e1 : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
    have : k - j = (k - j - 1) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm]; rfl
  have hk : 2 ^ k * b = 2 ^ j * (2 * (2 ^ (k - j - 1) * b)) := by
    rw [e1, e2, Nat.mul_assoc, Nat.mul_assoc]
  rw [hk, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_left]

theorem popc_add_high (a b k : Nat) : ∀ i, i ≤ k → popc (a + 2 ^ k * b) i = popc a i
  | 0, _ => rfl
  | i + 1, hi => by
    show popc (a + 2 ^ k * b) i + bitN (a + 2 ^ k * b) i = popc a i + bitN a i
    rw [popc_add_high a b k i (by omega), bitN_add_high a b k i (by omega)]

theorem popc_le (c : Nat) : ∀ k, popc c k ≤ k
  | 0 => le_refl _
  | k + 1 => by
    show popc c k + bitN c k ≤ k + 1
    have := popc_le c k
    have := bitN_lt c k
    omega

/-! ### the pruned enumeration of the markings of size `d` -/

/-- `p (acc + c)` for every `c < 2^k` with exactly `d` set bits among the bits `0, …, k − 1` -/
def scB (p : Nat → Bool) (k : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun d acc => !(Nat.beq d 0) || p acc)
    (fun k ih d acc => (Nat.blt k d || ih d acc) && (Nat.beq d 0 || ih (d - 1) (acc + 2 ^ k))) k

theorem scB_sound (p : Nat → Bool) : ∀ (k d acc : Nat), scB p k d acc = true →
    ∀ c, c < 2 ^ k → popc c k = d → p (acc + c) = true
  | 0, d, acc, h, c, hc, hd => by
    have hc0 : c = 0 := by simpa using hc
    subst hc0
    have hd0 : d = 0 := by rw [← hd]; rfl
    subst hd0
    have h' : (!(Nat.beq 0 0) || p acc) = true := h
    simpa using h'
  | k + 1, d, acc, h, c, hc, hd => by
    have h' : ((Nat.blt k d || scB p k d acc) && (Nat.beq d 0 || scB p k (d - 1) (acc + 2 ^ k))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    -- split `c` at bit `k`
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hsplit : c = c % 2 ^ k + 2 ^ k * (c / 2 ^ k) := (Nat.mod_add_div c (2 ^ k)).symm
    have hq : c / 2 ^ k < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]; rw [Nat.pow_succ] at hc; omega
    have hr : c % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
    have hbit : bitN c k = c / 2 ^ k := by
      unfold bitN; exact Nat.mod_eq_of_lt hq
    have hpk : popc c k = popc (c % 2 ^ k) k := by
      conv_lhs => rw [hsplit]
      exact popc_add_high _ _ k k (le_refl _)
    have hd' : popc c (k + 1) = popc c k + bitN c k := rfl
    rcases (by omega : c / 2 ^ k = 0 ∨ c / 2 ^ k = 1) with hb | hb
    · -- bit `k` of `c` is 0
      have hck : c = c % 2 ^ k := by rw [hsplit, hb]; simp
      rw [hbit, hb, hpk] at hd'
      rcases h1 with h1 | h1
      · exfalso
        have := popc_le (c % 2 ^ k) k
        have := Nat.le_of_ble_eq_true h1
        omega
      · have := scB_sound p k d acc h1 (c % 2 ^ k) hr (by omega)
        rw [← hck] at this; exact this
    · -- bit `k` of `c` is 1
      rw [hbit, hb, hpk] at hd'
      rcases h2 with h2 | h2
      · exfalso; have := Nat.eq_of_beq_eq_true h2; omega
      · have := scB_sound p k (d - 1) (acc + 2 ^ k) h2 (c % 2 ^ k) hr (by omega)
        have e : acc + 2 ^ k + c % 2 ^ k = acc + c := by
          conv_rhs => rw [hsplit, hb]
          omega
        rw [e] at this; exact this

/-! ### orbit coverage with bounded size -/

/-- every marking code `c < 2^m` with `lo ≤ q + 2 popc c m` and `popc c m ≤ hi` is set in `B` -/
def covS (q lo hi m B : Nat) : Bool :=
  rangeAll (hi + 1) (fun d => Nat.blt (q + 2 * d) lo || scB (fun c => Nat.beq (bitN B c) 1) m d 0)

theorem orbit_sound2 {q lo hi m : Nat} {SE : List (List Nat)} {RC : List Nat}
    (h : covS q lo hi m (orSet SE RC) = true) (hSE : ∀ se ∈ SE, se.length = m) (dl : List Bool)
    (hl : dl.length = m) (hlo : lo ≤ q + 2 * cntT dl) (hhi : cntT dl ≤ hi) :
    ∃ se ∈ SE, ∃ rc ∈ RC, ∀ j, j < m → (bitN rc (se.getD j 0) = 1 ↔ dl.getD j false = true) := by
  unfold covS at h
  rw [rangeAll_eq, List.all_eq_true] at h
  have h1 := h (cntT dl) (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true] at h1
  have hc : codeB dl < 2 ^ m := hl ▸ code_lt dl
  have hpop : popc (codeB dl) m = cntT dl := by
    rw [popc_codeB dl m (by omega), ← hl, List.take_length]; rfl
  rcases h1 with h1 | h1
  · exact absurd (Nat.le_of_ble_eq_true h1) (by omega)
  · have h2 := scB_sound _ m (cntT dl) 0 h1 (codeB dl) hc hpop
    rw [Nat.zero_add] at h2
    have h3 : bitN (orSet SE RC) (codeB dl) = 1 := Nat.eq_of_beq_eq_true h2
    rw [bitN_eq] at h3
    have hb : (orSet SE RC).testBit (codeB dl) = true := by
      cases h4 : (orSet SE RC).testBit (codeB dl)
      · rw [h4] at h3; simp at h3
      · rfl
    obtain ⟨se, hse, rc, hrc, e⟩ := orSet_bit hb
    refine ⟨se, hse, rc, hrc, fun j hj => ?_⟩
    have e1 := bit_imgC rc se j (by rw [hSE se hse]; exact hj)
    rw [e, bit_codeB] at e1
    rw [← e1]
    cases dl.getD j false <;> simp

/-! ### the classification of digon insertions with representative codes -/

/-- the digon insertion of the host `el` (`q` vertices) at the marking with code `rc` -/
def digGrC (q : Nat) (hq : 0 < q) (el : List (Nat × Nat)) (rc : Nat) : MGraph :=
  ofList (q + 2 * cntT (decodeB el.length rc)) (digEl q el (decodeB el.length rc))
    (Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _))

theorem dig_class_code {Y : MGraph} {Q D : Fin Y.m → Prop} (hloop : Loopless Y) {q lo hi : Nat}
    {el : List (Nat × Nat)} {hq : 0 < q} (hiso : IsoFrom Q (ofList q el hq)) (hel : elOK q el = true)
    (hm0 : 0 < el.length) (hlo : lo ≤ q + 2 * cntF Y.m (fun d => Q d ∧ D d))
    (hhi : cntF Y.m (fun d => Q d ∧ D d) ≤ hi)
    {AUT : List (List Nat × List Nat)} (haut : allR (autOKR q el) AUT = true)
    {RC : List Nat} (hcov : covS q lo hi el.length (orSet (AUT.map Prod.snd) RC) = true) :
    ∃ rc ∈ RC, IsoFrom (digSet Q D) (digGrC q hq el rc) := by
  obtain ⟨α, β, hc⟩ := hiso
  obtain ⟨dl, hlen, hD, hcnt⟩ := count_dl (D := D) (show IsoC Q α β from hc)
  rw [allR_eq, List.all_eq_true] at haut
  have hSE : ∀ se ∈ AUT.map Prod.snd, se.length = el.length := by
    intro se hse
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hse
    exact (autOKR_imp (haut a ha)).2
  have hlen' : dl.length = el.length := hlen
  obtain ⟨se, hse, rc, hrc, hbits⟩ := orbit_sound2 hcov hSE dl hlen' (by rw [← hcnt]; exact hlo)
    (by rw [← hcnt]; exact hhi)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hse
  have hA := (autOKR_imp (haut a ha)).1
  obtain ⟨α2, β2, hc2, hβ2⟩ := isoC_aut (hn := hq) hel hA hm0 (show IsoC Q α β from hc)
  have hse_lt : ∀ j, j < el.length → a.2.getD j 0 < el.length := by
    intro j hj
    unfold autOK at hA
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hA
    exact Nat.le_of_ble_eq_true (hA.1.1.1.2 j hj)
  have hD2 : ∀ f, Q f → (D f ↔ (decodeB el.length rc).getD (β2 f).val false = true) := by
    intro f hf
    have hb := (β f).isLt
    change (β f).val < el.length at hb
    rw [hD f hf, hβ2 f, getD_decodeB _ _ _ (hse_lt _ hb), hbits _ hb]
  exact ⟨rc, hrc, dig_iso hloop hel (digOK_of hel (length_decodeB _ _)) hc2.1 hc2.2.1 hc2.2.2.1 hc2.2.2.2 hD2
    (Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _)) hm0⟩

/-- the coverage check for all hosts of a list `L` with `q` vertices: `AUTS[k]` are automorphisms of `L[k]` and the
    codes `RCS[k]` cover all markings with `lo ≤ q + 2 d`, `d ≤ hi` -/
def covAllC (q lo hi : Nat) (L : List (List (Nat × Nat))) (AUTS : List (List (List Nat × List Nat)))
    (RCS : List (List Nat)) : Bool :=
  rangeAll L.length (fun k => elOK q (getR L k []) && Nat.blt 0 (getR L k []).length &&
    allR (autOKR q (getR L k [])) (getR AUTS k []) &&
    covS q lo hi (getR L k []).length (orSet ((getR AUTS k []).map Prod.snd) (getR RCS k [])))

/-- **classification of the digon insertions of the members of 𝒮 with `q` vertices** -/
theorem digClassC {q lo hi : Nat} {hq : 0 < q} {L : List (List (Nat × Nat))}
    {AUTS : List (List (List Nat × List Nat))} {RCS : List (List Nat)} (hc : covAllC q lo hi L AUTS RCS = true)
    (hcls : ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → vcount Q = q →
      ∃ k, k < L.length ∧ IsoFrom Q (ofList q (L.getD k []) hq)) :
    ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q → vcount Q = q → lo ≤ q + 2 * cntF Y.m (fun f => Q f ∧ D f) →
      cntF Y.m (fun f => Q f ∧ D f) ≤ hi →
      ∃ k, k < L.length ∧ ∃ rc ∈ RCS.getD k [], IsoFrom (digSet Q D) (digGrC q hq (L.getD k []) rc) := by
  intro Y Q D hS hv hlo hhi
  obtain ⟨k, hk, hiso⟩ := hcls Y Q hS hv
  unfold covAllC at hc
  rw [rangeAll_eq, List.all_eq_true] at hc
  have hck := hc k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, getR_eq] at hck
  obtain ⟨⟨⟨hel, hm0⟩, haut⟩, hcov⟩ := hck
  obtain ⟨rc, hrc, hI⟩ := dig_class_code hS.1.1 hiso hel (Nat.le_of_ble_eq_true hm0) hlo hhi haut hcov
  exact ⟨k, hk, rc, hrc, hI⟩

end dc0

end RH2F

-- ===== from DC2.lean =====
/-
  DC2 — a kernel-cheap automorphism check.  An automorphism of the host `el` (`n ≤ 16` vertices) is given by a vertex
  permutation code `V` (base-16 digits `sv V x`) and an edge map list `E`; `autOKB` checks both permutations by OR-masks
  and the end compatibility through the base-256 edge code `encE el`.  `autOK_of_autOKB`: it implies the list check
  `autOK` of fact 2f482379fe24b1cb for the vertex list `(List.range n).map (sv V)`.
  `covAllB`, `digClassB`: the classification of digon insertions with these automorphisms.
-/

namespace RH2F
open MGraph
open Classical

section dc2

/-- the OR of the bits `2 ^ x`, `x ∈ l` -/
def orList (l : List Nat) : Nat := List.rec (motive := fun _ => Nat) 0 (fun x _ ih => ih ||| 2 ^ x) l

theorem testBit_orList : ∀ (l : List Nat) (b : Nat), (orList l).testBit b = true ↔ b ∈ l
  | [], b => by simp [orList, Nat.zero_testBit]
  | x :: l, b => by
    show (orList l ||| 2 ^ x).testBit b = true ↔ _
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, testBit_orList l b, decide_eq_true_iff,
      List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

/-- the end compatibility of the edge map `E` (from position `j` on) with the vertex map `sv V` -/
def compatGo (ELC V : Nat) : List Nat → Nat → Bool :=
  fun l => List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun x _ ih j =>
    ((Nat.beq (dgt ELC 256 x % 16) (sv V (dgt ELC 256 j % 16)) &&
        Nat.beq (dgt ELC 256 x / 16) (sv V (dgt ELC 256 j / 16))) ||
      (Nat.beq (dgt ELC 256 x % 16) (sv V (dgt ELC 256 j / 16)) &&
        Nat.beq (dgt ELC 256 x / 16) (sv V (dgt ELC 256 j % 16)))) && ih (j + 1)) l

theorem compatGo_get (ELC V : Nat) : ∀ (l : List Nat) (j0 : Nat), compatGo ELC V l j0 = true →
    ∀ r, r < l.length →
      ((Nat.beq (dgt ELC 256 (l.getD r 0) % 16) (sv V (dgt ELC 256 (j0 + r) % 16)) &&
          Nat.beq (dgt ELC 256 (l.getD r 0) / 16) (sv V (dgt ELC 256 (j0 + r) / 16))) ||
        (Nat.beq (dgt ELC 256 (l.getD r 0) % 16) (sv V (dgt ELC 256 (j0 + r) / 16)) &&
          Nat.beq (dgt ELC 256 (l.getD r 0) / 16) (sv V (dgt ELC 256 (j0 + r) % 16)))) = true
  | [], _, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | x :: l, j0, h, r, hr => by
    have h' : (((Nat.beq (dgt ELC 256 x % 16) (sv V (dgt ELC 256 j0 % 16)) &&
        Nat.beq (dgt ELC 256 x / 16) (sv V (dgt ELC 256 j0 / 16))) ||
      (Nat.beq (dgt ELC 256 x % 16) (sv V (dgt ELC 256 j0 / 16)) &&
        Nat.beq (dgt ELC 256 x / 16) (sv V (dgt ELC 256 j0 % 16)))) && compatGo ELC V l (j0 + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases r with
    | zero => simpa using h'.1
    | succ r =>
      have := compatGo_get ELC V l (j0 + 1) h'.2 r (by simp at hr; omega)
      rw [show j0 + 1 + r = j0 + (r + 1) by omega] at this
      simpa using this

/-- **the automorphism check**: `sv V` permutes `{0, …, n − 1}`, `E` permutes `{0, …, m − 1}`, and `E` maps every
    edge onto an edge joining the images of its ends (edge code `ELC`) -/
def autOKB (n m ELC V : Nat) (E : List Nat) : Bool :=
  permB n V && Nat.beq E.length m && Nat.beq (orList E) (2 ^ m - 1) && compatGo ELC V E 0

theorem autOK_of_autOKB {n : Nat} {el : List (Nat × Nat)} (hel : elOK n el = true) (hn16 : n ≤ 16)
    {V : Nat} {E : List Nat} (h : autOKB n el.length (encE el) V E = true) :
    autOK n el ((List.range n).map (sv V), E) = true ∧ E.length = el.length := by
  unfold autOKB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hp, hlen⟩, hor⟩, hcomp⟩ := h
  have hlen' : E.length = el.length := Nat.eq_of_beq_eq_true hlen
  have hor' : orList E = 2 ^ el.length - 1 := Nat.eq_of_beq_eq_true hor
  obtain ⟨hvlt, hvsurj⟩ := permB_sound hp
  have hsmall := small_of_elOK hel hn16
  have dE := dgt_encE el hsmall
  -- the vertex list
  have ha1 : ∀ x, x < n → ((List.range n).map (sv V)).getD x 0 = sv V x := by
    intro x hx
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx]; rfl
  -- the vertex map is injective on `{0, …, n − 1}`
  let σ : Fin n → Fin n := fun x => ⟨sv V x.val, hvlt x.val x.isLt⟩
  have σsurj : Function.Surjective σ := fun b => by
    obtain ⟨x, hx, h⟩ := hvsurj b.val b.isLt
    exact ⟨⟨x, hx⟩, Fin.ext h⟩
  have σinj : Function.Injective σ := Finite.injective_iff_surjective.2 σsurj
  -- the edge map
  have hEmem : ∀ b, b ∈ E ↔ b < el.length := by
    intro b
    rw [← testBit_orList, hor', Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  have hEget : ∀ j, j < el.length → E.getD j 0 < el.length ∧ E.getD j 0 ∈ E := by
    intro j hj
    have hj' : j < E.length := by omega
    have hm : E.getD j 0 ∈ E := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; exact List.getElem_mem hj'
    exact ⟨(hEmem _).1 hm, hm⟩
  let τ : Fin el.length → Fin el.length := fun j => ⟨E.getD j.val 0, (hEget j.val j.isLt).1⟩
  have τsurj : Function.Surjective τ := fun b => by
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem ((hEmem b.val).2 b.isLt)
    refine ⟨⟨i, by omega⟩, Fin.ext ?_⟩
    show E.getD i 0 = b.val
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
  have τinj : Function.Injective τ := Finite.injective_iff_surjective.2 τsurj
  refine ⟨?_, hlen'⟩
  unfold autOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun j hj => ?_⟩, fun i hi j hj => ?_⟩, fun j hj => ?_⟩,
    fun j hj => ?_⟩
  · rw [ha1 x hx]; simpa using hvlt x hx
  · by_cases hxy : x = y
    · exact Or.inr hxy
    · left
      rw [ha1 x hx, ha1 y hy]
      intro h
      exact hxy (congrArg Fin.val (σinj (Fin.ext h : σ ⟨x, hx⟩ = σ ⟨y, hy⟩)))
  · simpa using (hEget j hj).1
  · by_cases hij : i = j
    · exact Or.inr hij
    · left
      intro h
      exact hij (congrArg Fin.val (τinj (Fin.ext h : τ ⟨i, hi⟩ = τ ⟨j, hj⟩)))
  · obtain ⟨i, hi⟩ := τsurj ⟨j, hj⟩
    exact ⟨i.val, i.isLt, congrArg Fin.val hi⟩
  · have hc := compatGo_get (encE el) V E 0 hcomp j (by omega)
    rw [Nat.zero_add] at hc
    have hx := (hEget j hj).1
    have d1 := dE _ hx
    have d2 := dE j hj
    rw [d1.1, d1.2, d2.1, d2.2] at hc
    have gj := gE_mem hel hj
    rw [ha1 _ gj.1, ha1 _ gj.2.1]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
    · exact Or.inr ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

/-! ### the classification of digon insertions with the cheap automorphism check -/

/-- the coverage check for all hosts of `L`: for host `k` with edge code `encE L[k]`, the automorphisms `AUTS[k]`
    (vertex codes, edge lists) pass `autOKB`, and the representative codes `RCS[k]` cover all markings with
    `lo ≤ q + 2 d`, `d ≤ hi` -/
def covAllB (q lo hi : Nat) (L : List (List (Nat × Nat))) (AUTS : List (List (Nat × List Nat)))
    (RCS : List (List Nat)) : Bool :=
  rangeAll L.length (fun k => elOK q (getR L k []) && Nat.blt 0 (getR L k []).length &&
    allR (fun a => autOKB q (getR L k []).length (encE (getR L k [])) a.1 a.2) (getR AUTS k []) &&
    covS q lo hi (getR L k []).length (orSet ((getR AUTS k []).map Prod.snd) (getR RCS k [])))

theorem digClassB {q lo hi : Nat} {hq : 0 < q} (hq16 : q ≤ 16) {L : List (List (Nat × Nat))}
    {AUTS : List (List (Nat × List Nat))} {RCS : List (List Nat)} (hc : covAllB q lo hi L AUTS RCS = true)
    (hcls : ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → vcount Q = q →
      ∃ k, k < L.length ∧ IsoFrom Q (ofList q (L.getD k []) hq)) :
    ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q → vcount Q = q → lo ≤ q + 2 * cntF Y.m (fun f => Q f ∧ D f) →
      cntF Y.m (fun f => Q f ∧ D f) ≤ hi →
      ∃ k, k < L.length ∧ ∃ rc ∈ RCS.getD k [], IsoFrom (digSet Q D) (digGrC q hq (L.getD k []) rc) := by
  intro Y Q D hS hv hlo hhi
  obtain ⟨k, hk, hiso⟩ := hcls Y Q hS hv
  unfold covAllB at hc
  rw [rangeAll_eq, List.all_eq_true] at hc
  have hck := hc k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, getR_eq] at hck
  obtain ⟨⟨⟨hel, hm0⟩, haut⟩, hcov⟩ := hck
  -- the automorphisms in list form
  let AUT : List (List Nat × List Nat) := (AUTS.getD k []).map (fun a => ((List.range q).map (sv a.1), a.2))
  have haut' : allR (autOKR q (L.getD k [])) AUT = true := by
    rw [allR_eq, List.all_eq_true]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rw [allR_eq, List.all_eq_true] at haut
    have := autOK_of_autOKB hel hq16 (haut b hb)
    unfold autOKR
    simp only [Bool.and_eq_true]
    refine ⟨?_, nbeq_true this.2⟩
    have h1 := this.1
    unfold autOK at h1
    simpa only [rangeAll_eq, getR_eq, anyR_eq, gER, gE, Bool.and_eq_true] using h1
  have hmap : AUT.map Prod.snd = (AUTS.getD k []).map Prod.snd := by
    simp [AUT, List.map_map, Function.comp_def]
  rw [← hmap] at hcov
  obtain ⟨rc, hrc, hI⟩ := dig_class_code hS.1.1 hiso hel (Nat.le_of_ble_eq_true hm0) hlo hhi haut' hcov
  exact ⟨k, hk, rc, hrc, hI⟩

end dc2

end RH2F

-- ===== from DC3.lean =====
/-
  DC3 — the digon insertions without digons (`|Q ∩ D| = 0`) need no automorphisms, and the passage from a
  2-cut-reduced member of 𝒢 to a digon insertion of a member of 𝒮 (H-ASM (a) converse, fact c3375be11cf311ee).
-/

namespace RH2F
open MGraph
open Classical

section dc3

/-- the marking with code `0` has no marked edge -/
theorem decodeB_zero : ∀ (m j : Nat), (decodeB m 0).getD j false = false
  | 0, _ => rfl
  | m + 1, 0 => by simp [decodeB]
  | m + 1, j + 1 => by simp only [decodeB, List.getD_cons_succ]; exact decodeB_zero m j

theorem dig_class_zero {Y : MGraph} {Q D : Fin Y.m → Prop} (hloop : Loopless Y) {q : Nat} {el : List (Nat × Nat)}
    {hq : 0 < q} (hiso : IsoFrom Q (ofList q el hq)) (hel : elOK q el = true) (hm0 : 0 < el.length)
    (h0 : cntF Y.m (fun d => Q d ∧ D d) = 0) : IsoFrom (digSet Q D) (digGrC q hq el 0) := by
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := hiso
  have hD : ∀ f, Q f → (D f ↔ (decodeB el.length 0).getD (β f).val false = true) := by
    intro f hf
    rw [decodeB_zero]
    constructor
    · intro hd
      have := cntF_le_of_mem Y.m (fun d => Q d ∧ D d) (i := f) ⟨hf, hd⟩
      omega
    · intro h; exact absurd h (by decide)
  exact dig_iso hloop hel (digOK_of hel (length_decodeB _ _)) hα hβ hs hj hD
    (Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _)) hm0

/-- all hosts of a classification list, without digons -/
theorem digClassZ {q : Nat} {hq : 0 < q} {L : List (List (Nat × Nat))}
    (hL : ∀ k, k < L.length → elOK q (L.getD k []) = true ∧ 0 < (L.getD k []).length)
    (hcls : ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → vcount Q = q →
      ∃ k, k < L.length ∧ IsoFrom Q (ofList q (L.getD k []) hq)) :
    ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q → vcount Q = q → cntF Y.m (fun f => Q f ∧ D f) = 0 →
      ∃ k, k < L.length ∧ IsoFrom (digSet Q D) (digGrC q hq (L.getD k []) 0) := by
  intro Y Q D hS hv h0
  obtain ⟨k, hk, hiso⟩ := hcls Y Q hS hv
  exact ⟨k, hk, dig_class_zero hS.1.1 hiso (hL k hk).1 (hL k hk).2 h0⟩

/-- the listed hosts of `repsB` data are loopless edge lists with edges -/
theorem hostsOK_of_repsB {q m : Nat} {L : List (List (Nat × Nat))} (h : repsB q m L = true) (hm : 0 < m) :
    ∀ k, k < L.length → elOK q (L.getD k []) = true ∧ 0 < (L.getD k []).length := by
  intro k hk
  obtain ⟨h1, h2, _⟩ := repsB_get h hk
  exact ⟨h1, by omega⟩

/-- **from 𝒟 to digon insertions of 𝒮**: a 2-cut-reduced member `P` of 𝒢 with `10 ≤ |V(P)|` has `Y, Q, D` with
    `Q ∈ 𝒮`, `|V(Q)|` even and at least 4, `|V(P)| = |V(Q)| + 2 |Q ∩ D|`, and every `IsoFrom (digSet Q D) H` onto a
    multigraph `H` with a vertex and an edge gives `IsoFrom P H` -/
theorem to_dig {X : MGraph} {P : Fin X.m → Prop} (hG : InG X P) (h2 : TwoCutReducedOn P) (h10 : 10 ≤ vcount P) :
    ∃ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q ∧ 4 ≤ vcount Q ∧ vcount Q % 2 = 0 ∧
      vcount P = vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) ∧
      ∀ H : MGraph, IsoFrom (digSet Q D) H → 0 < H.n → 0 < H.m → IsoFrom P H := by
  obtain ⟨Y, Q, D, hS, h4, hv, ⟨R⟩, _⟩ := hasm_converse hG h2 h10
  exact ⟨Y, Q, D, hS, h4, vcount_even' hS.1, hv, fun H hI hn hm => isoFrom_of_rep R hI hn hm⟩

end dc3

end RH2F

-- ===== from DC4.lean =====
/-
  DC4 — digon-free ends.  `DFree P v`: no two distinct `P`-edges join `v` to the same vertex.
  * `dfree_of_eligible`: both ends of an eligible edge (fact f7fb58786d241d68: no parallel edge, in no 2-edge-cut) of a
    member of 𝒢 are digon-free (a digon `v y` at an end `v ≠` the other end gives the 2-edge-cut `{v, y}` crossed by `g`);
  * `dfree_iso`: digon-freeness transfers along `IsoFrom` to the image in the target multigraph (all edges).
-/

namespace RH2F
open MGraph
open Classical

section dc4
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `v` is digon-free in `P` -/
def DFree (P : Fin X.m → Prop) (v : Fin X.n) : Prop :=
  ∀ f f' y, P f → P f' → X.Joins f v y → X.Joins f' v y → f = f'

/-- an end of an eligible edge is digon-free (the end `v`, the other end `w`) -/
theorem dfree_end (hG : InG X P) {g : Fin X.m} (hg : P g) {v w : Fin X.n} (hvw : X.Joins g v w)
    (hpar : ∀ h, P h → h ≠ g → ¬ X.Joins h v w) (hcut : ∀ S, TwoCut P S → ¬ Crosses P S g) : DFree P v := by
  intro f f' y hf hf' jf jf'
  by_contra hne
  have hloop := hG.1
  have hcub := hG.2.2.2
  have hvy : v ≠ y := MGraph.ne_of_joins hloop jf
  have hvw' : v ≠ w := MGraph.ne_of_joins hloop hvw
  by_cases hyw : y = w
  · subst hyw
    by_cases hfg : f = g
    · subst hfg; exact hpar f' hf' (Ne.symm hne) jf'
    · exact hpar f hf hfg jf
  -- `f`, `f'` differ from `g`
  have hfg : f ≠ g := fun h => by
    subst h; rcases joins_unique jf hvw with ⟨_, h⟩ | ⟨h, _⟩
    · exact hyw h
    · exact hvw' h
  have hf'g : f' ≠ g := fun h => by
    subst h; rcases joins_unique jf' hvw with ⟨_, h⟩ | ⟨h, _⟩
    · exact hyw h
    · exact hvw' h
  -- the third edge `h` at `y`
  obtain ⟨b1, b2, hb1, hb2, ib1, ib2, b12, b1f, b2f, hally⟩ := two_others hcub hf (joins_inc_right jf)
  have hf'y : f' = b1 ∨ f' = b2 := by
    rcases hally f' hf' (joins_inc_right jf') with h | h | h
    · exact absurd h.symm hne
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨h, hh, ih, hhf, hhf', hally'⟩ : ∃ h, P h ∧ X.Inc h y ∧ h ≠ f ∧ h ≠ f' ∧
      ∀ d, P d → X.Inc d y → d = f ∨ d = f' ∨ d = h := by
    rcases hf'y with rfl | rfl
    · exact ⟨b2, hb2, ib2, b2f, Ne.symm b12, fun d hd hdy => by
        rcases hally d hd hdy with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)⟩
    · exact ⟨b1, hb1, ib1, b1f, b12, fun d hd hdy => by
        rcases hally d hd hdy with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)⟩
  -- the edges at `v`
  obtain ⟨a1, a2, ha1, ha2, ia1, ia2, a12, a1g, a2g, hallv⟩ := two_others hcub hg (joins_inc_left hvw)
  have hv3 : ∀ d, P d → X.Inc d v → d = g ∨ d = f ∨ d = f' := by
    intro d hd hdv
    have hf1 := hallv f hf (joins_inc_left jf)
    have hf1' := hallv f' hf' (joins_inc_left jf')
    rcases hallv d hd hdv with h | h | h
    · exact Or.inl h
    · rcases hf1 with h1 | h1 | h1
      · exact absurd h1 hfg
      · exact Or.inr (Or.inl (h.trans h1.symm))
      · rcases hf1' with h2 | h2 | h2
        · exact absurd h2 hf'g
        · exact Or.inr (Or.inr (h.trans h2.symm))
        · exact absurd (h1.trans h2.symm) hne
    · rcases hf1 with h1 | h1 | h1
      · exact absurd h1 hfg
      · rcases hf1' with h2 | h2 | h2
        · exact absurd h2 hf'g
        · exact absurd (h1.trans h2.symm) hne
        · exact Or.inr (Or.inr (h.trans h2.symm))
      · exact Or.inr (Or.inl (h.trans h1.symm))
  -- `h` avoids `v`, `g` avoids `y`
  have hhv : ¬ X.Inc h v := fun hi => by
    rcases hv3 h hh hi with e | e | e
    · subst e
      rcases inc_of_joins hvw ih with e' | e'
      · exact hvy e'.symm
      · exact hyw e'
    · exact hhf e
    · exact hhf' e
  -- the side `{v, y}`
  let S : Fin X.n → Bool := fun u => decide (u = v ∨ u = y)
  have Sv : S v = true := by simp [S]
  have Sy : S y = true := by simp [S]
  have Sw : S w = false := by simp [S]; exact ⟨Ne.symm hvw', Ne.symm hyw⟩
  have hcg : Crosses P S g := by
    refine ⟨hg, ?_⟩
    rcases hvw with e | e <;> rw [e] <;> simp [Sv, Sw]
  obtain ⟨z, jh⟩ : ∃ z, X.Joins h y z := sc_joins_of_inc ih
  have hzy : z ≠ y := fun e => MGraph.ne_of_joins hloop jh e.symm
  have hzv : z ≠ v := fun e => hhv (by rw [← e]; exact joins_inc_right jh)
  have Sz : S z = false := by simp [S]; exact ⟨hzv, hzy⟩
  have hch : Crosses P S h := by
    refine ⟨hh, ?_⟩
    rcases jh with e | e <;> rw [e] <;> simp [Sy, Sz]
  have hgh : g ≠ h := fun e => by subst e; exact hhv (joins_inc_left hvw)
  apply hcut S ⟨g, h, hgh, hcg, hch, ?_⟩ hcg
  intro d ⟨hd, hcr⟩
  -- a crossing edge has exactly one end in `{v, y}`
  have hin : X.Inc d v ∨ X.Inc d y := by
    by_cases h1 : X.Inc d v
    · exact Or.inl h1
    by_cases h2 : X.Inc d y
    · exact Or.inr h2
    exfalso
    apply hcr
    have e1 : S (X.ends d).1 = false := by
      simp only [S, decide_eq_false_iff_not, not_or]
      exact ⟨fun e => h1 (Or.inl e), fun e => h2 (Or.inl e)⟩
    have e2 : S (X.ends d).2 = false := by
      simp only [S, decide_eq_false_iff_not, not_or]
      exact ⟨fun e => h1 (Or.inr e), fun e => h2 (Or.inr e)⟩
    rw [e1, e2]
  have fin : ∀ e : Fin X.m, X.Joins e v y → ¬ Crosses P S e := by
    intro e je ⟨_, hc⟩
    apply hc
    rcases je with e' | e' <;> rw [e'] <;> simp [Sv, Sy]
  rcases hin with hdv | hdy
  · rcases hv3 d hd hdv with e | e | e
    · exact Or.inl e
    · exact absurd ⟨hd, hcr⟩ (e ▸ fin f jf)
    · exact absurd ⟨hd, hcr⟩ (e ▸ fin f' jf')
  · rcases hally' d hd hdy with e | e | e
    · exact absurd ⟨hd, hcr⟩ (e ▸ fin f jf)
    · exact absurd ⟨hd, hcr⟩ (e ▸ fin f' jf')
    · exact Or.inr e

/-- **both ends of an eligible edge are digon-free** -/
theorem dfree_of_eligible (hG : InG X P) {g : Fin X.m} (hE : Eligible P g) :
    DFree P (X.ends g).1 ∧ DFree P (X.ends g).2 := by
  obtain ⟨hg, hpar, hcut⟩ := hE
  refine ⟨dfree_end hG hg (Or.inl rfl) hpar hcut, dfree_end hG hg (Or.inr rfl) (fun h hh hne j => hpar h hh hne ?_) hcut⟩
  exact Or.symm j

/-- **digon-freeness along an isomorphism**: the image of a digon-free vertex of `P` is digon-free in `H` -/
theorem dfree_iso {H : MGraph} {α : Fin X.n → Fin H.n} {β : Fin X.m → Fin H.m}
    (hα : ∀ x y, meets P x → meets P y → α x = α y → x = y) (hs : ∀ j, ∃ f, P f ∧ β f = j)
    (hj : ∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2)) {v : Fin X.n} (hv : meets P v)
    (hD : DFree P v) : DFree (fun _ : Fin H.m => True) (α v) := by
  intro e e' y _ _ je je'
  obtain ⟨f, hf, rfl⟩ := hs e
  obtain ⟨f', hf', rfl⟩ := hs e'
  -- the preimage of `α v` on `f` is `v`, the other end maps to `y`
  have side : ∀ d, P d → H.Joins (β d) (α v) y → ∃ w, X.Joins d v w ∧ α w = y := by
    intro d hd jd
    have jd0 := hj d hd
    have m1 : meets P (X.ends d).1 := ⟨d, hd, Or.inl rfl⟩
    have m2 : meets P (X.ends d).2 := ⟨d, hd, Or.inr rfl⟩
    rcases joins_unique jd0 jd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hα _ _ m1 hv h1
      exact ⟨(X.ends d).2, Or.inl (by rw [← this]), h2⟩
    · have := hα _ _ m2 hv h2
      exact ⟨(X.ends d).1, Or.inr (by rw [← this]), h1⟩
  obtain ⟨w, jw, hw⟩ := side f hf je
  obtain ⟨w', jw', hw'⟩ := side f' hf' je'
  have mw : meets P w := ⟨f, hf, joins_inc_right jw⟩
  have mw' : meets P w' := ⟨f', hf', joins_inc_right jw'⟩
  have := hα _ _ mw mw' (hw.trans hw'.symm)
  subst this
  rw [hD f f' w hf hf' jw jw']

end dc4

end RH2F

-- ===== from LX1.lean =====
/-
  LX1 — the local extension to the leaf graph T(P, g).  A star 6-colouring `c` of `P` is extended to T(P, g) by
  `s x ↦ α`, `x t ↦ β`, `x ℓ ↦ 5` (`s, t` the ends of `g`).  The extension is a star colouring as soon as a short list
  of local conditions (walks of at most three edges from `s` or `t` avoiding `g`) holds: every 4-edge path or 4-cycle of
  T(P, g) through a new edge is one of seven shapes, each excluded by one condition.
-/

namespace RH2F
open MGraph

section lx
variable {X : MGraph} {g : Fin X.m}

/-! ### the edges and vertices of the leaf graph -/

theorem lf_cases (e : Fin (leafG X g).m) : (∃ f : Fin X.m, e = oldE g f) ∨ e = newE g 0 (by decide) ∨
    e = newE g 1 (by decide) ∨ e = newE g 2 (by decide) := by
  have he : e.val < X.m + 3 := e.isLt
  by_cases h : e.val < X.m
  · exact Or.inl ⟨⟨e.val, h⟩, Fin.ext rfl⟩
  · right
    rcases (by omega : e.val = X.m ∨ e.val = X.m + 1 ∨ e.val = X.m + 2) with h' | h' | h'
    · exact Or.inl (Fin.ext (by simp [newE, h']))
    · exact Or.inr (Or.inl (Fin.ext (by simp [newE, h'])))
    · exact Or.inr (Or.inr (Fin.ext (by simp [newE, h'])))

theorem jn_of_ends {G : MGraph} {e : Fin G.m} {A B p q : Fin G.n} (he : G.ends e = (A, B)) (h : G.Joins e p q) :
    (p = A ∧ q = B) ∨ (p = B ∧ q = A) := by
  rcases h with h | h <;> rw [he] at h <;> simp only [Prod.mk.injEq] at h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

theorem jn_old {f : Fin X.m} {p q : Fin (leafG X g).n} (h : (leafG X g).Joins (oldE g f) p q) :
    ∃ a b, p = lv a ∧ q = lv b ∧ X.Joins f a b := by
  rcases jn_of_ends (ends_old g f) h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact ⟨_, _, hp, hq, Or.inl rfl⟩
  · exact ⟨_, _, hp, hq, Or.inr rfl⟩

theorem jn_new0 {p q : Fin (leafG X g).n} (h : (leafG X g).Joins (newE g 0 (by decide)) p q) :
    (p = lv (X.ends g).1 ∧ q = vx X) ∨ (p = vx X ∧ q = lv (X.ends g).1) :=
  jn_of_ends (ends_new0 g) h

theorem jn_new1 {p q : Fin (leafG X g).n} (h : (leafG X g).Joins (newE g 1 (by decide)) p q) :
    (p = vx X ∧ q = lv (X.ends g).2) ∨ (p = lv (X.ends g).2 ∧ q = vx X) :=
  jn_of_ends (ends_new1 g) h

theorem jn_new2 {p q : Fin (leafG X g).n} (h : (leafG X g).Joins (newE g 2 (by decide)) p q) :
    (p = vx X ∧ q = vl X) ∨ (p = vl X ∧ q = vx X) :=
  jn_of_ends (ends_new2 g) h

theorem inc_of_ends {G : MGraph} {e : Fin G.m} {A B z : Fin G.n} (he : G.ends e = (A, B)) (h : G.Inc e z) :
    z = A ∨ z = B := by
  rcases h with h | h <;> rw [he] at h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem vx_ne_lv (a : Fin X.n) : vx X ≠ (lv a : Fin (X.n + 2)) := fun h => lv_ne_vx a h.symm
theorem vl_ne_lv (a : Fin X.n) : vl X ≠ (lv a : Fin (X.n + 2)) := fun h => lv_ne_vl a h.symm
theorem vl_ne_vx (X : MGraph) : vl X ≠ vx X := fun h => vx_ne_vl X h.symm

theorem newE_ne01 : newE g 0 (by decide) ≠ newE g 1 (by decide) := by
  intro h; have := congrArg Fin.val h; simp [newE] at this
theorem newE_ne02 : newE g 0 (by decide) ≠ newE g 2 (by decide) := by
  intro h; have := congrArg Fin.val h; simp [newE] at this
theorem newE_ne12 : newE g 1 (by decide) ≠ newE g 2 (by decide) := by
  intro h; have := congrArg Fin.val h; simp [newE] at this
/-! ### the extended colouring -/

/-- the extension of `c` to T(P, g): old edges keep their colour, `s x ↦ α`, `x t ↦ β`, `x ℓ ↦ 5` -/
def extC (c : Fin X.m → Fin 6) (g : Fin X.m) (α β : Fin 6) : Fin (leafG X g).m → Fin 6 :=
  fun e => if h : e.val < X.m then c ⟨e.val, h⟩ else if e.val = X.m then α else if e.val = X.m + 1 then β else 5

theorem extC_old (c : Fin X.m → Fin 6) (α β : Fin 6) (f : Fin X.m) : extC c g α β (oldE g f) = c f := by
  simp [extC, oldE, f.isLt]
theorem extC_new0 (c : Fin X.m → Fin 6) (α β : Fin 6) : extC c g α β (newE g 0 (by decide)) = α := by
  simp [extC, newE]
theorem extC_new1 (c : Fin X.m → Fin 6) (α β : Fin 6) : extC c g α β (newE g 1 (by decide)) = β := by
  simp [extC, newE]
theorem extC_new2 (c : Fin X.m → Fin 6) (α β : Fin 6) : extC c g α β (newE g 2 (by decide)) = 5 := by
  simp [extC, newE]

/-! ### the local conditions -/

variable {P : Fin X.m → Prop}

/-- the local conditions at the end `v` of `g`, with own new colour `A` (on the new edge at `v`) and the other new
    colour `B`: (i) no `P`-edge at `v` other than `g` has colour `A`; for every walk `v f1 y f2 z` of `P`-edges other than
    `g` with `f2 ≠ f1`: (ii) not `c f1 = 5 ∧ c f2 = A`; (iii) not `c f1 = B ∧ c f2 = A`; (iv) for every further `P`-edge
    `f3 ≠ f2` (other than `g`) at `z`, not `c f2 = A ∧ c f3 = c f1` -/
def LocOK (P : Fin X.m → Prop) (c : Fin X.m → Fin 6) (g : Fin X.m) (v : Fin X.n) (A B : Fin 6) : Prop :=
  (∀ f, P f → f ≠ g → X.Inc f v → c f ≠ A) ∧
  (∀ f1 f2 y z, P f1 → P f2 → f1 ≠ g → f2 ≠ g → f2 ≠ f1 → X.Joins f1 v y → X.Joins f2 y z →
    ¬ (c f1 = 5 ∧ c f2 = A) ∧ ¬ (c f1 = B ∧ c f2 = A) ∧
    ∀ f3 w, P f3 → f3 ≠ g → f3 ≠ f2 → X.Joins f3 z w → ¬ (c f2 = A ∧ c f3 = c f1))

/-- the cross condition: no `P`-edge at `s` of colour `β` together with a `P`-edge at `t` of colour `α` -/
def LeafCrossOK (P : Fin X.m → Prop) (c : Fin X.m → Fin 6) (g : Fin X.m) (α β : Fin 6) : Prop :=
  ∀ f f', P f → P f' → f ≠ g → f' ≠ g → X.Inc f (X.ends g).1 → X.Inc f' (X.ends g).2 → ¬ (c f = β ∧ c f' = α)

/-! ### walks through the new vertex `x` -/

section raw
variable {c : Fin X.m → Fin 6} {α β : Fin 6}

theorem ne_of_path {G : MGraph} {e e' : Fin G.m} {a b c : Fin G.n} (h : G.Joins e a b) (h' : G.Joins e' b c)
    (hab : a ≠ b) (hac : a ≠ c) : e ≠ e' := by
  intro heq; subst heq
  rcases joins_unique h h' with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hab h1
  · exact hac h1

/-- a 4-edge path or 4-cycle of T(P, g) (given by its data) through `x` at position 0, 1 or 2 is not bicoloured -/
theorem raw_x (hst : (X.ends g).1 ≠ (X.ends g).2) (hs : LocOK P c g (X.ends g).1 α β)
    (ht : LocOK P c g (X.ends g).2 β α) (hx : LeafCrossOK P c g α β)
    {v0 v1 v2 v3 v4 : Fin (leafG X g).n} {e1 e2 e3 e4 : Fin (leafG X g).m}
    (h1 : (leafG X g).Joins e1 v0 v1) (h2 : (leafG X g).Joins e2 v1 v2) (h3 : (leafG X g).Joins e3 v2 v3)
    (h4 : (leafG X g).Joins e4 v3 v4)
    (d01 : v0 ≠ v1) (d02 : v0 ≠ v2) (d03 : v0 ≠ v3) (d12 : v1 ≠ v2) (d13 : v1 ≠ v3) (d14 : v1 ≠ v4)
    (d23 : v2 ≠ v3) (d24 : v2 ≠ v4) (d34 : v3 ≠ v4)
    (p1 : leafSet P g e1) (p2 : leafSet P g e2) (p3 : leafSet P g e3) (p4 : leafSet P g e4)
    (b1 : extC c g α β e1 = extC c g α β e3) (b2 : extC c g α β e2 = extC c g α β e4)
    (hxpos : v0 = vx X ∨ v1 = vx X ∨ v2 = vx X) : False := by
  have lvs : ∀ a b : Fin X.n, (lv a : Fin (X.n + 2)) = lv b → a = b := fun a b h => lv_inj h
  have hts : (X.ends g).2 ≠ (X.ends g).1 := fun h => hst h.symm
  have e12 := ne_of_path h1 h2 d01 d02
  have e23 := ne_of_path h2 h3 d12 d13
  have e34 := ne_of_path h3 h4 d23 d24
  have e24 : e2 ≠ e4 := by
    intro heq; subst heq
    rcases joins_unique h2 h4 with ⟨h', _⟩ | ⟨h', _⟩
    · exact d13 h'
    · exact d14 h'
  -- an old edge never meets `x` or `ℓ`
  have oldx : ∀ (f : Fin X.m) (p q : Fin (leafG X g).n), (leafG X g).Joins (oldE g f) p q →
      p ≠ vx X ∧ q ≠ vx X ∧ p ≠ vl X ∧ q ≠ vl X := by
    intro f p q h
    obtain ⟨a, b, rfl, rfl, _⟩ := jn_old h
    exact ⟨lv_ne_vx a, lv_ne_vx b, lv_ne_vl a, lv_ne_vl b⟩
  -- the continuation `v y1 y2 (y3)` of old edges from an old vertex `v`: shared by all shapes
  -- (two old edges e3, e4 after an old vertex v2 = lv a, where neither may be new)
  rcases hxpos with hv | hv | hv
  · -- `x = v0`
    subst hv
    rcases lf_cases e1 with ⟨f0, rfl⟩ | rfl | rfl | rfl
    · exact (oldx f0 _ _ h1).1 rfl
    · -- `e1 = s x` (colour α), `v1 = s`
      rcases jn_new0 h1 with ⟨h, _⟩ | ⟨_, hv1⟩
      · exact absurd h (vx_ne_lv _)
      subst hv1
      rcases lf_cases e2 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨a, y1, ha, rfl, j1⟩ := jn_old h2
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e3 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y2, ha2, rfl, j2⟩ := jn_old h3
          have ha2' := lvs _ _ ha2; subst ha2'
          have n21 : f2 ≠ f1 := fun h => e23 (by rw [h])
          rw [set_old] at p2 p3
          rcases lf_cases e4 with ⟨f3, rfl⟩ | rfl | rfl | rfl
          · obtain ⟨a3, y3, ha3, rfl, j3⟩ := jn_old h4
            have ha3' := lvs _ _ ha3; subst ha3'
            have n32 : f3 ≠ f2 := fun h => e34 (by rw [h])
            rw [set_old] at p4
            rw [extC_new0, extC_old] at b1
            rw [extC_old, extC_old] at b2
            exact (hs.2 f1 f2 y1 y2 p2.1 p3.1 p2.2 p3.2 n21 j1 j2).2.2 f3 y3 p4.1 p4.2 n32 j3 ⟨b1.symm, b2.symm⟩
          · rcases jn_new0 h4 with ⟨h, _⟩ | ⟨h, _⟩
            · exact d13 (by rw [h])
            · exact absurd h (lv_ne_vx _)
          · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨h, _⟩
            · exact absurd h (lv_ne_vx _)
            · -- the 4-cycle `x s y1 t x`
              have hy2 := lvs _ _ h; subst hy2
              rw [extC_new0, extC_old] at b1
              rw [extC_old, extC_new1] at b2
              exact hx f1 f2 p2.1 p3.1 p2.2 p3.2 (joins_inc_left j1) (joins_inc_right j2) ⟨b2, b1.symm⟩
          · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
            · exact absurd h (lv_ne_vx _)
            · exact absurd h (lv_ne_vl _)
        · rcases jn_new0 h3 with ⟨h, _⟩ | ⟨h, _⟩
          · exact d12 (by rw [h])
          · exact absurd h (lv_ne_vx _)
        · rcases jn_new1 h3 with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h (lv_ne_vx _)
          · exact d03 h.symm
        · rcases jn_new2 h3 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · exact e12 rfl
      · rcases jn_new1 h2 with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h (lv_ne_vx _)
        · exact d02 h.symm
      · rcases jn_new2 h2 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    · -- `e1 = x t` (colour β), `v1 = t`
      rcases jn_new1 h1 with ⟨_, hv1⟩ | ⟨h, _⟩
      swap
      · exact absurd h (vx_ne_lv _)
      subst hv1
      rcases lf_cases e2 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨a, y1, ha, rfl, j1⟩ := jn_old h2
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e3 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y2, ha2, rfl, j2⟩ := jn_old h3
          have ha2' := lvs _ _ ha2; subst ha2'
          have n21 : f2 ≠ f1 := fun h => e23 (by rw [h])
          rw [set_old] at p2 p3
          rcases lf_cases e4 with ⟨f3, rfl⟩ | rfl | rfl | rfl
          · obtain ⟨a3, y3, ha3, rfl, j3⟩ := jn_old h4
            have ha3' := lvs _ _ ha3; subst ha3'
            have n32 : f3 ≠ f2 := fun h => e34 (by rw [h])
            rw [set_old] at p4
            rw [extC_new1, extC_old] at b1
            rw [extC_old, extC_old] at b2
            exact (ht.2 f1 f2 y1 y2 p2.1 p3.1 p2.2 p3.2 n21 j1 j2).2.2 f3 y3 p4.1 p4.2 n32 j3 ⟨b1.symm, b2.symm⟩
          · rcases jn_new0 h4 with ⟨h, _⟩ | ⟨h, _⟩
            · -- the 4-cycle `x t y1 s x`
              have hy2 := lvs _ _ h; subst hy2
              rw [extC_new1, extC_old] at b1
              rw [extC_old, extC_new0] at b2
              exact hx f2 f1 p3.1 p2.1 p3.2 p2.2 (joins_inc_right j2) (joins_inc_left j1) ⟨b1.symm, b2⟩
            · exact absurd h (lv_ne_vx _)
          · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨h, _⟩
            · exact absurd h (lv_ne_vx _)
            · exact d13 (by rw [h])
          · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
            · exact absurd h (lv_ne_vx _)
            · exact absurd h (lv_ne_vl _)
        · rcases jn_new0 h3 with ⟨_, h'⟩ | ⟨h, _⟩
          · exact d03 h'.symm
          · exact absurd h (lv_ne_vx _)
        · rcases jn_new1 h3 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact d12 (by rw [h])
        · rcases jn_new2 h3 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · rcases jn_new0 h2 with ⟨h, _⟩ | ⟨h, _⟩
        · exact hts (lvs _ _ h)
        · exact absurd h (lv_ne_vx _)
      · exact e12 rfl
      · rcases jn_new2 h2 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    · -- `e1 = x ℓ`, `v1 = ℓ`: no second edge at `ℓ`
      rcases jn_new2 h1 with ⟨_, hv1⟩ | ⟨h, _⟩
      swap
      · exact vx_ne_vl X h
      subst hv1
      rcases lf_cases e2 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h2).2.2.1 rfl
      · rcases jn_new0 h2 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · rcases jn_new1 h2 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · exact e12 rfl
  · -- `x = v1`: `e1` and `e2` are new
    subst hv
    have e1new : e1 = newE g 0 (by decide) ∨ e1 = newE g 1 (by decide) ∨ e1 = newE g 2 (by decide) := by
      rcases lf_cases e1 with ⟨f0, rfl⟩ | h | h
      · exact absurd rfl (oldx f0 _ _ h1).2.1
      · exact Or.inl h
      · exact Or.inr h
    have e2new : e2 = newE g 0 (by decide) ∨ e2 = newE g 1 (by decide) ∨ e2 = newE g 2 (by decide) := by
      rcases lf_cases e2 with ⟨f0, rfl⟩ | h | h
      · exact absurd rfl (oldx f0 _ _ h2).1
      · exact Or.inl h
      · exact Or.inr h
    rcases e1new with rfl | rfl | rfl <;> rcases e2new with rfl | rfl | rfl
    · exact e12 rfl
    · -- `s x t y3 y4`
      rcases jn_new0 h1 with ⟨hv0, _⟩ | ⟨h, _⟩
      swap
      · exact d01 h
      rcases jn_new1 h2 with ⟨_, hv2⟩ | ⟨h, _⟩
      swap
      · exact absurd h (vx_ne_lv _)
      subst hv0; subst hv2
      rcases lf_cases e3 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨a, y1, ha, rfl, j1⟩ := jn_old h3
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e4 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y2, ha2, rfl, j2⟩ := jn_old h4
          have ha2' := lvs _ _ ha2; subst ha2'
          have n21 : f2 ≠ f1 := fun h => e34 (by rw [h])
          rw [set_old] at p3 p4
          rw [extC_new0, extC_old] at b1
          rw [extC_new1, extC_old] at b2
          exact (ht.2 f1 f2 y1 y2 p3.1 p4.1 p3.2 p4.2 n21 j1 j2).2.1 ⟨b1.symm, b2.symm⟩
        · rcases jn_new0 h4 with ⟨_, h⟩ | ⟨h, _⟩
          · exact d14 h.symm
          · exact absurd h (lv_ne_vx _)
        · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact d23 (by rw [h])
        · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · rcases jn_new0 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact hts (lvs _ _ h)
        · exact absurd h (lv_ne_vx _)
      · exact e23 rfl
      · rcases jn_new2 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    · -- `s x ℓ`: no edge after `ℓ`
      rcases jn_new2 h2 with ⟨_, hv2⟩ | ⟨h, _⟩
      swap
      · exact vx_ne_vl X h
      subst hv2
      rcases lf_cases e3 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h3).2.2.1 rfl
      · rcases jn_new0 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · rcases jn_new1 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · exact e23 rfl
    · -- `t x s y3 y4`
      rcases jn_new1 h1 with ⟨h, _⟩ | ⟨hv0, _⟩
      · exact d01 (by rw [h])
      rcases jn_new0 h2 with ⟨h, _⟩ | ⟨_, hv2⟩
      · exact absurd h (vx_ne_lv _)
      subst hv0; subst hv2
      rcases lf_cases e3 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨a, y1, ha, rfl, j1⟩ := jn_old h3
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e4 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y2, ha2, rfl, j2⟩ := jn_old h4
          have ha2' := lvs _ _ ha2; subst ha2'
          have n21 : f2 ≠ f1 := fun h => e34 (by rw [h])
          rw [set_old] at p3 p4
          rw [extC_new1, extC_old] at b1
          rw [extC_new0, extC_old] at b2
          exact (hs.2 f1 f2 y1 y2 p3.1 p4.1 p3.2 p4.2 n21 j1 j2).2.1 ⟨b1.symm, b2.symm⟩
        · rcases jn_new0 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact d23 (by rw [h])
          · exact absurd h (lv_ne_vx _)
        · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h (lv_ne_vx _)
          · exact d14 h.symm
        · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · exact e23 rfl
      · rcases jn_new1 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact hst (lvs _ _ h)
      · rcases jn_new2 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    · exact e12 rfl
    · -- `t x ℓ`
      rcases jn_new2 h2 with ⟨_, hv2⟩ | ⟨h, _⟩
      swap
      · exact vx_ne_vl X h
      subst hv2
      rcases lf_cases e3 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h3).2.2.1 rfl
      · rcases jn_new0 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · rcases jn_new1 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · exact e23 rfl
    · -- `ℓ x s y3 y4`
      rcases jn_new2 h1 with ⟨h, _⟩ | ⟨hv0, _⟩
      · exact d01 (by rw [h])
      rcases jn_new0 h2 with ⟨h, _⟩ | ⟨_, hv2⟩
      · exact absurd h (vx_ne_lv _)
      subst hv0; subst hv2
      rcases lf_cases e3 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨a, y1, ha, rfl, j1⟩ := jn_old h3
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e4 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y2, ha2, rfl, j2⟩ := jn_old h4
          have ha2' := lvs _ _ ha2; subst ha2'
          have n21 : f2 ≠ f1 := fun h => e34 (by rw [h])
          rw [set_old] at p3 p4
          rw [extC_new2, extC_old] at b1
          rw [extC_new0, extC_old] at b2
          exact (hs.2 f1 f2 y1 y2 p3.1 p4.1 p3.2 p4.2 n21 j1 j2).1 ⟨b1.symm, b2.symm⟩
        · rcases jn_new0 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact d23 (by rw [h])
          · exact absurd h (lv_ne_vx _)
        · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h (lv_ne_vx _)
          · exact d14 h.symm
        · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · exact e23 rfl
      · rcases jn_new1 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact hst (lvs _ _ h)
      · rcases jn_new2 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    · -- `ℓ x t y3 y4`
      rcases jn_new2 h1 with ⟨h, _⟩ | ⟨hv0, _⟩
      · exact d01 (by rw [h])
      rcases jn_new1 h2 with ⟨_, hv2⟩ | ⟨h, _⟩
      swap
      · exact absurd h (vx_ne_lv _)
      subst hv0; subst hv2
      rcases lf_cases e3 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨a, y1, ha, rfl, j1⟩ := jn_old h3
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e4 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y2, ha2, rfl, j2⟩ := jn_old h4
          have ha2' := lvs _ _ ha2; subst ha2'
          have n21 : f2 ≠ f1 := fun h => e34 (by rw [h])
          rw [set_old] at p3 p4
          rw [extC_new2, extC_old] at b1
          rw [extC_new1, extC_old] at b2
          exact (ht.2 f1 f2 y1 y2 p3.1 p4.1 p3.2 p4.2 n21 j1 j2).1 ⟨b1.symm, b2.symm⟩
        · rcases jn_new0 h4 with ⟨_, h⟩ | ⟨h, _⟩
          · exact d14 h.symm
          · exact absurd h (lv_ne_vx _)
        · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact d23 (by rw [h])
        · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · rcases jn_new0 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact hts (lvs _ _ h)
        · exact absurd h (lv_ne_vx _)
      · exact e23 rfl
      · rcases jn_new2 h3 with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    · exact e12 rfl
  · -- `x = v2`: `e2` and `e3` are new
    subst hv
    have e2new : e2 = newE g 0 (by decide) ∨ e2 = newE g 1 (by decide) ∨ e2 = newE g 2 (by decide) := by
      rcases lf_cases e2 with ⟨f0, rfl⟩ | h | h
      · exact absurd rfl (oldx f0 _ _ h2).2.1
      · exact Or.inl h
      · exact Or.inr h
    have e3new : e3 = newE g 0 (by decide) ∨ e3 = newE g 1 (by decide) ∨ e3 = newE g 2 (by decide) := by
      rcases lf_cases e3 with ⟨f0, rfl⟩ | h | h
      · exact absurd rfl (oldx f0 _ _ h3).1
      · exact Or.inl h
      · exact Or.inr h
    rcases e2new with rfl | rfl | rfl <;> rcases e3new with rfl | rfl | rfl
    · exact e23 rfl
    · -- `y s x t z`
      rcases jn_new0 h2 with ⟨hv1, _⟩ | ⟨h, _⟩
      swap
      · exact d12 h
      rcases jn_new1 h3 with ⟨_, hv3⟩ | ⟨h, _⟩
      swap
      · exact absurd h (vx_ne_lv _)
      subst hv1; subst hv3
      rcases lf_cases e1 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨y0, a, rfl, ha, j1⟩ := jn_old h1
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e4 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y4, ha2, rfl, j2⟩ := jn_old h4
          have ha2' := lvs _ _ ha2; subst ha2'
          rw [set_old] at p4
          have p1' : P f1 ∧ f1 ≠ g := (set_old P g f1).1 p1
          rw [extC_old, extC_new1] at b1
          rw [extC_new0, extC_old] at b2
          exact hx f1 f2 p1'.1 p4.1 p1'.2 p4.2 (joins_inc_right j1) (joins_inc_left j2) ⟨b1, b2.symm⟩
        · exact e24 rfl
        · exact e34 rfl
        · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · exact e12 rfl
      · rcases jn_new1 h1 with ⟨h, _⟩ | ⟨_, h'⟩
        · exact d02 h
        · exact absurd h' (lv_ne_vx _)
      · rcases jn_new2 h1 with ⟨h, _⟩ | ⟨_, h⟩
        · exact d02 h
        · exact absurd h (lv_ne_vx _)
    · -- `ℓ` at `v3`: no edge after `ℓ`
      rcases jn_new2 h3 with ⟨_, hv3⟩ | ⟨h, _⟩
      swap
      · exact vx_ne_vl X h
      subst hv3
      rcases lf_cases e4 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h4).2.2.1 rfl
      · rcases jn_new0 h4 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · exact e34 rfl
    · -- `y t x s z`
      rcases jn_new1 h2 with ⟨h, _⟩ | ⟨hv1, _⟩
      · exact d12 (by rw [h])
      rcases jn_new0 h3 with ⟨h, _⟩ | ⟨_, hv3⟩
      · exact absurd h (vx_ne_lv _)
      subst hv1; subst hv3
      rcases lf_cases e1 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · obtain ⟨y0, a, rfl, ha, j1⟩ := jn_old h1
        have ha' := lvs _ _ ha; subst ha'
        rcases lf_cases e4 with ⟨f2, rfl⟩ | rfl | rfl | rfl
        · obtain ⟨a2, y4, ha2, rfl, j2⟩ := jn_old h4
          have ha2' := lvs _ _ ha2; subst ha2'
          rw [set_old] at p4
          have p1' : P f1 ∧ f1 ≠ g := (set_old P g f1).1 p1
          rw [extC_old, extC_new0] at b1
          rw [extC_new1, extC_old] at b2
          exact hx f2 f1 p4.1 p1'.1 p4.2 p1'.2 (joins_inc_left j2) (joins_inc_right j1) ⟨b2.symm, b1⟩
        · exact e34 rfl
        · exact e24 rfl
        · rcases jn_new2 h4 with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h (lv_ne_vx _)
          · exact absurd h (lv_ne_vl _)
      · rcases jn_new0 h1 with ⟨_, h'⟩ | ⟨h, _⟩
        · exact absurd h' (lv_ne_vx _)
        · exact d02 h
      · exact e12 rfl
      · rcases jn_new2 h1 with ⟨h, _⟩ | ⟨_, h⟩
        · exact d02 h
        · exact absurd h (lv_ne_vx _)
    · exact e23 rfl
    · -- `ℓ` at `v3`
      rcases jn_new2 h3 with ⟨_, hv3⟩ | ⟨h, _⟩
      swap
      · exact vx_ne_vl X h
      subst hv3
      rcases lf_cases e4 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h4).2.2.1 rfl
      · rcases jn_new0 h4 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · rcases jn_new1 h4 with ⟨h, _⟩ | ⟨h, _⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · exact e34 rfl
    · -- `ℓ` at `v1`: no edge before `ℓ`
      rcases jn_new2 h2 with ⟨h, _⟩ | ⟨hv1, _⟩
      · exact d12 (by rw [h])
      subst hv1
      rcases lf_cases e1 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h1).2.2.2 rfl
      · rcases jn_new0 h1 with ⟨_, h⟩ | ⟨_, h⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · rcases jn_new1 h1 with ⟨_, h⟩ | ⟨_, h⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · exact e12 rfl
    · rcases jn_new2 h2 with ⟨h, _⟩ | ⟨hv1, _⟩
      · exact d12 (by rw [h])
      subst hv1
      rcases lf_cases e1 with ⟨f1, rfl⟩ | rfl | rfl | rfl
      · exact (oldx f1 _ _ h1).2.2.2 rfl
      · rcases jn_new0 h1 with ⟨_, h⟩ | ⟨_, h⟩
        · exact vl_ne_vx X h
        · exact vl_ne_lv _ h
      · rcases jn_new1 h1 with ⟨_, h⟩ | ⟨_, h⟩
        · exact vl_ne_lv _ h
        · exact vl_ne_vx X h
      · exact e12 rfl
    · exact e23 rfl

/-- a 4-edge path or 4-cycle of T(P, g) avoiding `x` is a walk of `P` and not bicoloured -/
theorem raw_nox (hc : StarOn P 6 c)
    {v0 v1 v2 v3 v4 : Fin (leafG X g).n} {e1 e2 e3 e4 : Fin (leafG X g).m}
    (h1 : (leafG X g).Joins e1 v0 v1) (h2 : (leafG X g).Joins e2 v1 v2) (h3 : (leafG X g).Joins e3 v2 v3)
    (h4 : (leafG X g).Joins e4 v3 v4)
    (d01 : v0 ≠ v1) (d02 : v0 ≠ v2) (d03 : v0 ≠ v3) (d12 : v1 ≠ v2) (d13 : v1 ≠ v3) (d14 : v1 ≠ v4)
    (d23 : v2 ≠ v3) (d24 : v2 ≠ v4) (d34 : v3 ≠ v4)
    (p1 : leafSet P g e1) (p2 : leafSet P g e2) (p3 : leafSet P g e3) (p4 : leafSet P g e4)
    (b1 : extC c g α β e1 = extC c g α β e3) (b2 : extC c g α β e2 = extC c g α β e4)
    (n0 : v0 ≠ vx X) (n1 : v1 ≠ vx X) (n2 : v2 ≠ vx X) (n3 : v3 ≠ vx X) (n4 : v4 ≠ vx X) : False := by
  have lvs : ∀ a b : Fin X.n, (lv a : Fin (X.n + 2)) = lv b → a = b := fun a b h => lv_inj h
  have oldof : ∀ (e : Fin (leafG X g).m) (p q : Fin (leafG X g).n), (leafG X g).Joins e p q → p ≠ vx X →
      q ≠ vx X → ∃ f, e = oldE g f := by
    intro e p q h hp hq
    rcases lf_cases e with ⟨f, rfl⟩ | rfl | rfl | rfl
    · exact ⟨f, rfl⟩
    · rcases jn_new0 h with ⟨_, h'⟩ | ⟨h', _⟩
      · exact absurd h' hq
      · exact absurd h' hp
    · rcases jn_new1 h with ⟨h', _⟩ | ⟨_, h'⟩
      · exact absurd h' hp
      · exact absurd h' hq
    · rcases jn_new2 h with ⟨h', _⟩ | ⟨_, h'⟩
      · exact absurd h' hp
      · exact absurd h' hq
  obtain ⟨f1, rfl⟩ := oldof e1 _ _ h1 n0 n1
  obtain ⟨f2, rfl⟩ := oldof e2 _ _ h2 n1 n2
  obtain ⟨f3, rfl⟩ := oldof e3 _ _ h3 n2 n3
  obtain ⟨f4, rfl⟩ := oldof e4 _ _ h4 n3 n4
  obtain ⟨a0, a1, rfl, rfl, j1⟩ := jn_old h1
  obtain ⟨a1', a2, ha1, rfl, j2⟩ := jn_old h2
  have e1' := lvs _ _ ha1; subst e1'
  obtain ⟨a2', a3, ha2, rfl, j3⟩ := jn_old h3
  have e2' := lvs _ _ ha2; subst e2'
  obtain ⟨a3', a4, ha3, rfl, j4⟩ := jn_old h4
  have e3' := lvs _ _ ha3; subst e3'
  rw [set_old] at p1 p2 p3 p4
  rw [extC_old, extC_old] at b1 b2
  exact hc.2 ⟨a0, a1, a2, a3, a4, f1, f2, f3, f4, j1, j2, j3, j4,
    fun h => d01 (congrArg lv h), fun h => d02 (congrArg lv h), fun h => d03 (congrArg lv h),
    fun h => d12 (congrArg lv h), fun h => d13 (congrArg lv h), fun h => d14 (congrArg lv h),
    fun h => d23 (congrArg lv h), fun h => d24 (congrArg lv h), fun h => d34 (congrArg lv h)⟩
    p1.1 p2.1 p3.1 p4.1 ⟨b1, b2⟩

theorem inc_old' {f : Fin X.m} {z : Fin (leafG X g).n} (h : (leafG X g).Inc (oldE g f) z) :
    ∃ y, z = lv y ∧ X.Inc f y := by
  rcases inc_of_ends (ends_old g f) h with h' | h'
  · exact ⟨_, h', Or.inl rfl⟩
  · exact ⟨_, h', Or.inr rfl⟩

/-- an old edge and a new edge meeting in T(P, g) -/
theorem ext_proper_on (hs : LocOK P c g (X.ends g).1 α β) (ht : LocOK P c g (X.ends g).2 β α)
    {f : Fin X.m} {e : Fin (leafG X g).m} (hf : leafSet P g (oldE g f)) (he : ¬ ∃ f', e = oldE g f')
    {z : Fin (leafG X g).n} (h1 : (leafG X g).Inc (oldE g f) z) (h2 : (leafG X g).Inc e z) :
    extC c g α β (oldE g f) ≠ extC c g α β e := by
  rw [set_old] at hf
  obtain ⟨y, rfl, hy⟩ := inc_old' h1
  rw [extC_old]
  rcases lf_cases e with ⟨f', rfl⟩ | rfl | rfl | rfl
  · exact absurd ⟨f', rfl⟩ he
  · rcases inc_of_ends (ends_new0 g) h2 with h | h
    · have := lv_inj h; subst this; rw [extC_new0]; exact hs.1 f hf.1 hf.2 hy
    · exact absurd h (lv_ne_vx _)
  · rcases inc_of_ends (ends_new1 g) h2 with h | h
    · exact absurd h (lv_ne_vx _)
    · have := lv_inj h; subst this; rw [extC_new1]; exact ht.1 f hf.1 hf.2 hy
  · rcases inc_of_ends (ends_new2 g) h2 with h | h
    · exact absurd h (lv_ne_vx _)
    · exact absurd h (lv_ne_vl _)

theorem ext_new_ne (hab : α ≠ β) (ha5 : α ≠ 5) (hb5 : β ≠ 5) {a b : Fin (leafG X g).m}
    (ha : ¬ ∃ f, a = oldE g f) (hb : ¬ ∃ f, b = oldE g f) (hne : a ≠ b) :
    extC c g α β a ≠ extC c g α β b := by
  rcases lf_cases a with ⟨f, rfl⟩ | rfl | rfl | rfl
  · exact absurd ⟨f, rfl⟩ ha
  all_goals rcases lf_cases b with ⟨f, rfl⟩ | rfl | rfl | rfl
  all_goals first
    | exact absurd ⟨_, rfl⟩ hb
    | exact absurd rfl hne
    | simp only [extC_new0, extC_new1, extC_new2]
  all_goals first | exact hab | exact ha5 | exact hb5 | exact Ne.symm hab | exact Ne.symm ha5 | exact Ne.symm hb5

/-- **local extension to the leaf graph**: if `c` is a star 6-colouring of `P` and the local conditions hold at both
    ends of `g`, then the extension `s x ↦ α`, `x t ↦ β`, `x ℓ ↦ 5` is a star 6-colouring of T(P, g) -/
theorem leaf_ext (hc : StarOn P 6 c) (hst : (X.ends g).1 ≠ (X.ends g).2) (hab : α ≠ β) (ha5 : α ≠ 5)
    (hb5 : β ≠ 5) (hs : LocOK P c g (X.ends g).1 α β) (ht : LocOK P c g (X.ends g).2 β α)
    (hx : LeafCrossOK P c g α β) : StarOn (leafSet P g) 6 (extC c g α β) := by
  refine ⟨?_, ?_⟩
  · rintro a b ⟨hne, z, ha, hb⟩ pa pb
    by_cases hao : ∃ f, a = oldE g f
    · obtain ⟨f, rfl⟩ := hao
      by_cases hbo : ∃ f', b = oldE g f'
      · obtain ⟨f', rfl⟩ := hbo
        rw [set_old] at pa pb
        obtain ⟨y, rfl, hy⟩ := inc_old' ha
        obtain ⟨y', hyy, hy'⟩ := inc_old' hb
        have := lv_inj hyy; subst this
        rw [extC_old, extC_old]
        exact hc.1 f f' ⟨fun h => hne (by rw [h]), y, hy, hy'⟩ pa.1 pb.1
      · exact ext_proper_on hs ht pa hbo ha hb
    · by_cases hbo : ∃ f', b = oldE g f'
      · obtain ⟨f', rfl⟩ := hbo
        exact Ne.symm (ext_proper_on hs ht pb hao hb ha)
      · exact ext_new_ne hab ha5 hb5 hao hbo hne
  · intro w p1 p2 p3 p4 hb
    obtain ⟨b1, b2⟩ := hb
    by_cases h012 : w.v0 = vx X ∨ w.v1 = vx X ∨ w.v2 = vx X
    · exact raw_x hst hs ht hx w.h1 w.h2 w.h3 w.h4 w.d01 w.d02 w.d03 w.d12 w.d13 w.d14 w.d23 w.d24 w.d34
        p1 p2 p3 p4 b1 b2 h012
    · by_cases h34 : w.v3 = vx X ∨ w.v4 = vx X
      · exact raw_x hst hs ht hx (Or.symm w.h4) (Or.symm w.h3) (Or.symm w.h2) (Or.symm w.h1)
          (Ne.symm w.d34) (Ne.symm w.d24) (Ne.symm w.d14) (Ne.symm w.d23) (Ne.symm w.d13) (Ne.symm w.d03)
          (Ne.symm w.d12) (Ne.symm w.d02) (Ne.symm w.d01) p4 p3 p2 p1 b2.symm b1.symm
          (by rcases h34 with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h)
      · push_neg at h012 h34
        exact raw_nox hc w.h1 w.h2 w.h3 w.h4 w.d01 w.d02 w.d03 w.d12 w.d13 w.d14 w.d23 w.d24 w.d34
          p1 p2 p3 p4 b1 b2 h012.1 h012.2.1 h012.2.2 h34.1 h34.2

/-- the vertices of the leaf graph -/
theorem lf_vcases (z : Fin (leafG X g).n) : (∃ y : Fin X.n, z = lv y) ∨ z = vx X ∨ z = vl X := by
  have hz : z.val < X.n + 2 := z.isLt
  by_cases h : z.val < X.n
  · exact Or.inl ⟨⟨z.val, h⟩, Fin.ext (by simp [lv])⟩
  · right
    rcases (by omega : z.val = X.n ∨ z.val = X.n + 1) with h' | h'
    · exact Or.inl (Fin.ext (by simp [vx, h']))
    · exact Or.inr (Fin.ext (by simp [vl, h']))

/-- **MC form**: if in addition every vertex of `P` meets exactly one `P`-edge of colour `5` and `c g ≠ 5`, the same
    holds for the extension on T(P, g) -/
theorem leaf_ext_mc (hmc : MCol P c) (hg : P g) (hg5 : c g ≠ 5) (hst : (X.ends g).1 ≠ (X.ends g).2)
    (hab : α ≠ β) (ha5 : α ≠ 5) (hb5 : β ≠ 5) (hs : LocOK P c g (X.ends g).1 α β)
    (ht : LocOK P c g (X.ends g).2 β α) (hx : LeafCrossOK P c g α β) : MCol (leafSet P g) (extC c g α β) := by
  refine ⟨leaf_ext hmc.1 hst hab ha5 hb5 hs ht hx, ?_⟩
  intro z hz
  have n2set : leafSet P g (newE g 2 (by decide)) := set_new P g 2 (by decide)
  rcases lf_vcases z with ⟨y, rfl⟩ | rfl | rfl
  · -- an old vertex: its colour-5 edge in `P` is not `g`
    have hmy : meets P y := by
      obtain ⟨e, he, hinc⟩ := hz
      rcases lf_cases e with ⟨f, rfl⟩ | rfl | rfl | rfl
      · rw [set_old] at he
        obtain ⟨y', hyy, hy'⟩ := inc_old' hinc
        have := lv_inj hyy; subst this
        exact ⟨f, he.1, hy'⟩
      · rcases inc_of_ends (ends_new0 g) hinc with h | h
        · have := lv_inj h; subst this; exact ⟨g, hg, Or.inl rfl⟩
        · exact absurd h (lv_ne_vx _)
      · rcases inc_of_ends (ends_new1 g) hinc with h | h
        · exact absurd h (lv_ne_vx _)
        · have := lv_inj h; subst this; exact ⟨g, hg, Or.inr rfl⟩
      · rcases inc_of_ends (ends_new2 g) hinc with h | h
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
    obtain ⟨a, ha, hay, ha5', huniq⟩ := hmc.2 y hmy
    have hag : a ≠ g := fun h => hg5 (h ▸ ha5')
    refine ⟨oldE g a, (set_old P g a).2 ⟨ha, hag⟩, ?_, by rw [extC_old]; exact ha5', ?_⟩
    · rcases hay with h | h
      · exact Or.inl (by rw [ends_old, h])
      · exact Or.inr (by rw [ends_old, h])
    · intro b hb hinc hb5'
      rcases lf_cases b with ⟨f, rfl⟩ | rfl | rfl | rfl
      · rw [set_old] at hb
        rw [extC_old] at hb5'
        obtain ⟨y', hyy, hy'⟩ := inc_old' hinc
        have := lv_inj hyy; subst this
        rw [huniq f hb.1 hy' hb5']
      · rw [extC_new0] at hb5'; exact absurd hb5' ha5
      · rw [extC_new1] at hb5'; exact absurd hb5' hb5
      · rcases inc_of_ends (ends_new2 g) hinc with h | h
        · exact absurd h (lv_ne_vx _)
        · exact absurd h (lv_ne_vl _)
  · -- `x`: its colour-5 edge is `x ℓ`
    refine ⟨newE g 2 (by decide), n2set, by rw [MGraph.Inc, ends_new2]; exact Or.inl rfl, extC_new2 c α β, ?_⟩
    intro b hb hinc hb5'
    rcases lf_cases b with ⟨f, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨y', hyy, _⟩ := inc_old' hinc
      exact absurd hyy.symm (lv_ne_vx _)
    · rw [extC_new0] at hb5'; exact absurd hb5' ha5
    · rw [extC_new1] at hb5'; exact absurd hb5' hb5
    · rfl
  · -- `ℓ`: its only edge is `x ℓ`
    refine ⟨newE g 2 (by decide), n2set, by rw [MGraph.Inc, ends_new2]; exact Or.inr rfl, extC_new2 c α β, ?_⟩
    intro b _ hinc _
    rcases lf_cases b with ⟨f, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨y', hyy, _⟩ := inc_old' hinc
      exact absurd hyy.symm (lv_ne_vl _)
    · rcases inc_of_ends (ends_new0 g) hinc with h | h
      · exact absurd h.symm (lv_ne_vl _)
      · exact absurd h (vl_ne_vx X)
    · rcases inc_of_ends (ends_new1 g) hinc with h | h
      · exact absurd h (vl_ne_vx X)
      · exact absurd h.symm (lv_ne_vl _)
    · rfl

end raw

end lx

end RH2F

-- ===== from LX2.lean =====
/-
  LX2 — certificates for the representatives: several shared-walk tables (three packed colourings each, colour 5 a
  perfect matching), EX1-fullness from a cover condition across the tables, and leaf data per edge: a table, a
  colouring of it and the two new colours `α`, `β` of the local extension (LX1), or a proof mark that an end of the
  edge is not digon-free.
-/

namespace RH2F
open MGraph
open Classical

section lx2

/-- the shared-walk table checks without the cover condition -/
def ex3core (n : Nat) (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (pc : List Nat) : Bool :=
  elOKR n el && nbOK3R el nb pc && properNB3R n nb && walk3R n nb && nbSound3R n el nb pc && pmNB3R n nb

theorem ex3core_imp {n : Nat} {el : List (Nat × Nat)} {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (h : ex3core n el nb pc = true) :
    elOK n el = true ∧ nbOK3 el nb pc = true ∧ properNB3 n nb = true ∧ walk3 n nb = true ∧
      nbSound3 n el nb pc = true ∧ pmNB3 n nb = true := by
  have h' : ex3R n el nb pc = true ∨ True := Or.inr trivial
  clear h'
  unfold ex3core at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨(elOKR_eq n el) ▸ h1, ?_, ?_, ?_, ?_, ?_⟩
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

variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

/-- the projected colouring `i` of a core table is a star 6-colouring whose colour class `5` is a perfect matching -/
theorem proj_ok {nb : List (List (Nat × Nat × Nat))} {pc : List Nat} (h : ex3core n el nb pc = true) {i : Nat}
    (hi : i = 0 ∨ i = 1 ∨ i = 2) :
    fastStar2 n el (projNB3 i nb) (projCL3 i pc) = true ∧ nbSound n el (projNB3 i nb) (projCL3 i pc) = true ∧
      pmNB n (projNB3 i nb) = true := by
  obtain ⟨hel, hnb, hpr, hw, hs, hpm⟩ := ex3core_imp h
  refine ⟨?_, nbSound_proj hs i, pmNB_proj hpm i hi⟩
  unfold fastStar2
  rw [hel, nbOK_proj hnb i, properNB_proj hpr i hi, walk_proj hw i hi]
  rfl

/-- every edge at `x` is in the table row of `x`, with its other end and its packed colours -/
theorem mem_nb3 (hel : elOK n el = true) {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (hnb : nbOK3 el nb pc = true) {e : Fin (ofList n el hn).m} {x y : Fin n} (h : (ofList n el hn).Joins e x y) :
    (e.val, y.val, pc.getD e.val 0) ∈ nb.getD x.val [] := by
  have h1 := List.all_eq_true.1 hnb e.val (List.mem_range.2 e.isLt)
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h1
  have he := ofList_ends (hn := hn) hel e
  rcases h with h | h <;> rw [h] at he <;> simp only at he <;> obtain ⟨e1, e2⟩ := he
  · rw [e1, e2]; exact h1.1
  · rw [e1, e2]; exact h1.2

theorem allR_mem {α : Type} {p : α → Bool} {l : List α} (h : allR p l = true) {x : α} (hx : x ∈ l) : p x = true := by
  rw [allR_eq, List.all_eq_true] at h; exact h x hx

theorem colF_proj (i : Nat) (pc : List Nat) (m : Nat) (e : Fin m) :
    (colF m (projCL3 i pc) e).val = dgc i (pc.getD e.val 0) := by
  show colN (projCL3 i pc) e.val = _
  rw [colN_projCL3]

/-! ### the local conditions from the table -/

/-- the local conditions at `v` for colouring `i`, own colour `A`, other colour `B`, edge `g` removed -/
def locB (nb : List (List (Nat × Nat × Nat))) (i g v A B : Nat) : Bool :=
  allR (fun t1 => Nat.beq t1.1 g || (!Nat.beq (dgc i t1.2.2) A &&
    allR (fun t2 => Nat.beq t2.1 g || Nat.beq t2.1 t1.1 ||
      (!(Nat.beq (dgc i t1.2.2) 5 && Nat.beq (dgc i t2.2.2) A) &&
       !(Nat.beq (dgc i t1.2.2) B && Nat.beq (dgc i t2.2.2) A) &&
       allR (fun t3 => Nat.beq t3.1 g || Nat.beq t3.1 t2.1 ||
         !(Nat.beq (dgc i t2.2.2) A && Nat.beq (dgc i t3.2.2) (dgc i t1.2.2))) (getR nb t2.2.1 [])))
      (getR nb t1.2.1 []))) (getR nb v [])

/-- the cross condition for colouring `i` -/
def crossB (nb : List (List (Nat × Nat × Nat))) (i g s t α β : Nat) : Bool :=
  allR (fun t1 => Nat.beq t1.1 g || allR (fun t2 => Nat.beq t2.1 g ||
    !(Nat.beq (dgc i t1.2.2) β && Nat.beq (dgc i t2.2.2) α)) (getR nb t [])) (getR nb s [])

theorem fin_ne_of_val {m : Nat} {a b : Fin m} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem locB_sound (hel : elOK n el = true) {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (hnb : nbOK3 el nb pc = true) {i : Nat} {g : Fin (ofList n el hn).m} {v : Fin n} {A B : Fin 6}
    (h : locB nb i g.val v.val A.val B.val = true) :
    LocOK (fun _ => True) (colF (ofList n el hn).m (projCL3 i pc)) g v A B := by
  have cv : ∀ (e : Fin (ofList n el hn).m) (C : Fin 6), colF (ofList n el hn).m (projCL3 i pc) e = C →
      dgc i (pc.getD e.val 0) = C.val := by
    intro e C hC; rw [← colF_proj i pc _ e, hC]
  unfold locB at h
  simp only [getR_eq] at h
  refine ⟨fun f _ hfg hinc => ?_, fun f1 f2 y z _ _ h1g h2g h21 j1 j2 => ?_⟩
  · obtain ⟨y, jy⟩ := joins_of_inc hinc
    have hc := allR_mem h (mem_nb3 (hn := hn) hel hnb jy)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with hc | ⟨hc, _⟩
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc)) hfg
    · intro e
      rw [nbeq_true (cv f A e)] at hc
      exact absurd hc (by decide)
  · have hc := allR_mem h (mem_nb3 (hn := hn) hel hnb j1)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with hc | ⟨_, hc⟩
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc)) h1g
    have hc2 := allR_mem hc (mem_nb3 (hn := hn) hel hnb j2)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc2
    rcases hc2 with (hc2 | hc2) | ⟨⟨h5, hB⟩, h3⟩
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc2)) h2g
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc2)) h21
    refine ⟨fun ⟨e1, e2⟩ => ?_, fun ⟨e1, e2⟩ => ?_, fun f3 w _ h3g h32 j3 ⟨e1, e2⟩ => ?_⟩
    · have e1' : dgc i (pc.getD f1.val 0) = 5 := cv f1 5 e1
      rw [nbeq_true e1', nbeq_true (cv f2 A e2)] at h5
      exact absurd h5 (by decide)
    · rw [nbeq_true (cv f1 B e1), nbeq_true (cv f2 A e2)] at hB
      exact absurd hB (by decide)
    · have hc3 := allR_mem h3 (mem_nb3 (hn := hn) hel hnb j3)
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc3
      rcases hc3 with (hc3 | hc3) | hc3
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc3)) h3g
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc3)) h32
      · have e2' : dgc i (pc.getD f3.val 0) = dgc i (pc.getD f1.val 0) := by
          rw [← colF_proj i pc _ f3, ← colF_proj i pc _ f1, e2]
        rw [nbeq_true (cv f2 A e1), nbeq_true e2'] at hc3
        exact absurd hc3 (by decide)

theorem crossB_sound (hel : elOK n el = true) {nb : List (List (Nat × Nat × Nat))} {pc : List Nat}
    (hnb : nbOK3 el nb pc = true) {i : Nat} {g : Fin (ofList n el hn).m} {α β : Fin 6}
    (h : crossB nb i g.val ((ofList n el hn).ends g).1.val ((ofList n el hn).ends g).2.val α.val β.val = true) :
    LeafCrossOK (fun _ => True) (colF (ofList n el hn).m (projCL3 i pc)) g α β := by
  have cv : ∀ (e : Fin (ofList n el hn).m) (C : Fin 6), colF (ofList n el hn).m (projCL3 i pc) e = C →
      dgc i (pc.getD e.val 0) = C.val := by
    intro e C hC; rw [← colF_proj i pc _ e, hC]
  intro f f' _ _ hfg hf'g hfs hft ⟨e1, e2⟩
  obtain ⟨y, jy⟩ := joins_of_inc hfs
  obtain ⟨y', jy'⟩ := joins_of_inc hft
  unfold crossB at h
  simp only [getR_eq] at h
  have hc := allR_mem h (mem_nb3 (hn := hn) hel hnb jy)
  simp only [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc)) hfg
  have hc2 := allR_mem hc (mem_nb3 (hn := hn) hel hnb jy')
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc2
  rcases hc2 with hc2 | hc2
  · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc2)) hf'g
  · rw [nbeq_true (cv f β e1), nbeq_true (cv f' α e2)] at hc2
    exact absurd hc2 (by decide)

/-- the leaf check of edge `j` with colouring `i` of a core table and new colours `α`, `β` -/
def leafChkB (el : List (Nat × Nat)) (nb : List (List (Nat × Nat × Nat))) (i j α β : Nat) : Bool :=
  Nat.blt α 5 && Nat.blt β 5 && !Nat.beq α β &&
  locB nb i j (gER el j).1 α β && locB nb i j (gER el j).2 β α && crossB nb i j (gER el j).1 (gER el j).2 α β

theorem leaf_of_leafChkB {nb : List (List (Nat × Nat × Nat))} {pc : List Nat} (hcore : ex3core n el nb pc = true)
    {i : Nat} (hi : i = 0 ∨ i = 1 ∨ i = 2) {j : Fin (ofList n el hn).m} {α β : Nat}
    (h : leafChkB el nb i j.val α β = true) : Colourable (leafSet (fun _ : Fin (ofList n el hn).m => True) j) 6 := by
  obtain ⟨hel, hnb, _, _, _, _⟩ := ex3core_imp hcore
  obtain ⟨hst, _, _⟩ := proj_ok hcore hi
  have hstar := star_of_fast2 (hn := hn) hst
  unfold leafChkB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨ha5, hb5⟩, hab⟩, hls⟩, hlt⟩, hcr⟩ := h
  have ha : α < 5 := Nat.le_of_ble_eq_true ha5
  have hb : β < 5 := Nat.le_of_ble_eq_true hb5
  let A : Fin 6 := ⟨α, by omega⟩
  let B : Fin 6 := ⟨β, by omega⟩
  have he := ofList_ends (hn := hn) hel j
  have hs : ((ofList n el hn).ends j).1.val = (gER el j.val).1 := by rw [he.1, gER, getR_eq]; rfl
  have ht : ((ofList n el hn).ends j).2.val = (gER el j.val).2 := by rw [he.2, gER, getR_eq]; rfl
  have hloop := ofList_loop (hn := hn) hel
  have hst' : ((ofList n el hn).ends j).1 ≠ ((ofList n el hn).ends j).2 := fun e =>
    hloop j (by rw [← he.1, ← he.2, e])
  refine ⟨extC (colF _ (projCL3 i pc)) j A B, leaf_ext hstar hst' ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro e; exact absurd (nbeq_true (congrArg Fin.val e)) (by rw [hab]; decide)
  · intro e; have := congrArg Fin.val e; simp [A] at this; omega
  · intro e; have := congrArg Fin.val e; simp [B] at this; omega
  · exact locB_sound hel hnb (A := A) (B := B) (by rw [hs]; exact hls)
  · exact locB_sound hel hnb (A := B) (B := A) (by rw [ht]; exact hlt)
  · exact crossB_sound hel hnb (α := A) (β := B) (by rw [hs, ht]; exact hcr)

end lx2

end RH2F

-- ===== from LX3.lean =====
/-
  LX3 — the certificate of one representative `ofList n el`: core tables `TS` (three packed colourings each),
  the EX1 cover across the tables, and leaf data `LD` with one entry `(t, i, α, β)` per edge: table `t`, colouring `i`,
  new colours `α`, `β`; an entry with `t ≥ |TS|` marks an edge with an end that is not digon-free.
  `repChk_sound`: EX1-fullness, and a star 6-colouring of T(H, j) for every edge `j` with digon-free ends.
-/

namespace RH2F
open MGraph
open Classical

section lx3
variable {n : Nat} {el : List (Nat × Nat)} {hn : 0 < n}

abbrev Tab := List (List (Nat × Nat × Nat)) × List Nat

/-- some colouring of some table has colour 5 on `e`, and some has not -/
def coverM (el : List (Nat × Nat)) (TS : List Tab) : Bool :=
  rangeAll el.length (fun e =>
    anyR (fun T => Nat.beq (dgc 0 (getR T.2 e 0)) 5 || Nat.beq (dgc 1 (getR T.2 e 0)) 5 ||
      Nat.beq (dgc 2 (getR T.2 e 0)) 5) TS &&
    anyR (fun T => !Nat.beq (dgc 0 (getR T.2 e 0)) 5 || !Nat.beq (dgc 1 (getR T.2 e 0)) 5 ||
      !Nat.beq (dgc 2 (getR T.2 e 0)) 5) TS)

/-- two distinct table entries at `v` with the same other end: `v` is not digon-free -/
def ndfB (nb : List (List (Nat × Nat × Nat))) (v : Nat) : Bool :=
  anyR (fun a => anyR (fun b => !Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1) (getR nb v [])) (getR nb v [])

/-- the leaf entries -/
def leafAll (el : List (Nat × Nat)) (TS : List Tab) (LD : List (Nat × Nat × Nat × Nat)) : Bool :=
  rangeAll el.length (fun j =>
    (Nat.blt (getR LD j (0, 0, 0, 0)).1 TS.length && Nat.blt (getR LD j (0, 0, 0, 0)).2.1 3 &&
      leafChkB el (getR TS (getR LD j (0, 0, 0, 0)).1 ([], [])).1 (getR LD j (0, 0, 0, 0)).2.1 j
        (getR LD j (0, 0, 0, 0)).2.2.1 (getR LD j (0, 0, 0, 0)).2.2.2) ||
    ndfB (getR TS 0 ([], [])).1 (gER el j).1 || ndfB (getR TS 0 ([], [])).1 (gER el j).2)

/-- **the certificate of a representative** -/
def repChk (n : Nat) (el : List (Nat × Nat)) (TS : List Tab) (LD : List (Nat × Nat × Nat × Nat)) : Bool :=
  Nat.blt 0 TS.length && allR (fun T => ex3core n el T.1 T.2) TS && coverM el TS && leafAll el TS LD

theorem getR_mem {α : Type} {l : List α} {k : Nat} {d : α} (hk : k < l.length) : getR l k d ∈ l := by
  rw [getR_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

theorem anyR_mem {α : Type} {p : α → Bool} {l : List α} (h : anyR p l = true) : ∃ x ∈ l, p x = true := by
  rw [anyR_eq, List.any_eq_true] at h; exact h

/-- **EX1-fullness** from the core tables and the cover -/
theorem ex1Full_of_rep {TS : List Tab} (hc : allR (fun T => ex3core n el T.1 T.2) TS = true)
    (hcov : coverM el TS = true) : EX1FullH (ofList n el hn) := by
  intro j t
  have hj : j.val < el.length := j.isLt
  unfold coverM at hcov
  rw [rangeAll_eq, List.all_eq_true] at hcov
  have h1 := hcov j.val (List.mem_range.2 hj)
  rw [Bool.and_eq_true] at h1
  -- a table and a colouring with the required status of `j`
  have pick : ∃ T ∈ TS, ∃ i, (i = 0 ∨ i = 1 ∨ i = 2) ∧ (dgc i (T.2.getD j.val 0) = 5 ↔ t = true) := by
    cases t
    · obtain ⟨T, hT, hc⟩ := anyR_mem h1.2
      rw [getR_eq] at hc
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc
      refine ⟨T, hT, ?_⟩
      rcases hc with (hc | hc) | hc
      · exact ⟨0, Or.inl rfl, fun h => absurd (nbeq_true h) (by rw [hc]; decide), fun h => absurd h (by decide)⟩
      · exact ⟨1, Or.inr (Or.inl rfl), fun h => absurd (nbeq_true h) (by rw [hc]; decide),
          fun h => absurd h (by decide)⟩
      · exact ⟨2, Or.inr (Or.inr rfl), fun h => absurd (nbeq_true h) (by rw [hc]; decide),
          fun h => absurd h (by decide)⟩
    · obtain ⟨T, hT, hc⟩ := anyR_mem h1.1
      rw [getR_eq] at hc
      simp only [Bool.or_eq_true] at hc
      refine ⟨T, hT, ?_⟩
      rcases hc with (hc | hc) | hc
      · exact ⟨0, Or.inl rfl, fun _ => rfl, fun _ => Nat.eq_of_beq_eq_true hc⟩
      · exact ⟨1, Or.inr (Or.inl rfl), fun _ => rfl, fun _ => Nat.eq_of_beq_eq_true hc⟩
      · exact ⟨2, Or.inr (Or.inr rfl), fun _ => rfl, fun _ => Nat.eq_of_beq_eq_true hc⟩
  obtain ⟨T, hT, i, hi, hst⟩ := pick
  have hcore := allR_mem hc hT
  obtain ⟨hstar, hsd, hpm⟩ := proj_ok hcore hi
  have hst' := hstar
  unfold fastStar2 at hst'
  simp only [Bool.and_eq_true] at hst'
  refine ⟨colF _ (projCL3 i T.2), star_of_fast2 (hn := hn) hstar,
    fun p => pm_of_nb (hn := hn) hst'.1.1.1 hst'.1.1.2 hsd hpm p, ?_⟩
  rw [Fin.ext_iff]
  show colN (projCL3 i T.2) j.val = 5 ↔ t = true
  rw [colN_projCL3]; exact hst

/-- two distinct edges at `v` with the same other end -/
theorem not_dfree_of_ndfB {nb : List (List (Nat × Nat × Nat))} {pc : List Nat} (hel : elOK n el = true)
    (hs : nbSound3 n el nb pc = true) {v : Fin n} (h : ndfB nb v.val = true) :
    ¬ DFree (fun _ : Fin (ofList n el hn).m => True) v := by
  intro hD
  unfold ndfB at h
  obtain ⟨a, ha, h'⟩ := anyR_mem h
  obtain ⟨b, hb, h''⟩ := anyR_mem h'
  rw [getR_eq] at ha hb
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h''
  obtain ⟨hab, hy⟩ := h''
  have sound : ∀ t ∈ nb.getD v.val [], ∃ e : Fin (ofList n el hn).m, e.val = t.1 ∧ ∃ y : Fin n,
      y.val = t.2.1 ∧ (ofList n el hn).Joins e v y := by
    intro t ht
    have h1 := List.all_eq_true.1 hs v.val (List.mem_range.2 v.isLt)
    have h2 := List.all_eq_true.1 h1 t ht
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h2
    obtain ⟨⟨hlt, hj⟩, _⟩ := h2
    have hlt' := Nat.le_of_ble_eq_true hlt
    let e : Fin (ofList n el hn).m := ⟨t.1, hlt'⟩
    have he := ofList_ends (hn := hn) hel e
    have gm := gE_mem hel hlt'
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := Nat.eq_of_beq_eq_true h1
      have e2 := Nat.eq_of_beq_eq_true h2
      refine ⟨e, rfl, ⟨t.2.1, by rw [← e2]; exact gm.2.1⟩, rfl, Or.inl ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · rw [he.1]; exact e1
      · rw [he.2]; exact e2
    · have e1 := Nat.eq_of_beq_eq_true h1
      have e2 := Nat.eq_of_beq_eq_true h2
      refine ⟨e, rfl, ⟨t.2.1, by rw [← e1]; exact gm.1⟩, rfl, Or.inr ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · rw [he.1]; exact e1
      · rw [he.2]; exact e2
  obtain ⟨ea, hea, ya, hya, ja⟩ := sound a ha
  obtain ⟨eb, heb, yb, hyb, jb⟩ := sound b hb
  have hyy : ya = yb := Fin.ext (by rw [hya, hyb]; exact Nat.eq_of_beq_eq_true hy)
  subst hyy
  have := hD ea eb ya trivial trivial ja jb
  rw [← hea, ← heb, this] at hab
  exact absurd hab (by simp)

/-- **the certificate of a representative is sound** -/
theorem repChk_sound {TS : List Tab} {LD : List (Nat × Nat × Nat × Nat)} (h : repChk n el TS LD = true) :
    EX1FullH (ofList n el hn) ∧ ∀ j : Fin (ofList n el hn).m,
      DFree (fun _ : Fin (ofList n el hn).m => True) ((ofList n el hn).ends j).1 →
      DFree (fun _ : Fin (ofList n el hn).m => True) ((ofList n el hn).ends j).2 →
      Colourable (leafSet (fun _ : Fin (ofList n el hn).m => True) j) 6 := by
  unfold repChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpos, hc⟩, hcov⟩, hleaf⟩ := h
  refine ⟨ex1Full_of_rep hc hcov, fun j hs ht => ?_⟩
  have hj : j.val < el.length := j.isLt
  unfold leafAll at hleaf
  rw [rangeAll_eq, List.all_eq_true] at hleaf
  have h1 := hleaf j.val (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h1
  have T0 : getR TS 0 ([], []) ∈ TS := getR_mem (Nat.le_of_ble_eq_true hpos)
  have core0 := allR_mem hc T0
  obtain ⟨hel, _, _, _, hsd0, _⟩ := ex3core_imp core0
  have he := ofList_ends (hn := hn) hel j
  rcases h1 with (⟨⟨ht1, hi⟩, hl⟩ | hn1) | hn2
  · have hT := getR_mem (d := (([], []) : Tab)) (Nat.le_of_ble_eq_true ht1)
    have hcore := allR_mem hc hT
    have hi' : (getR LD j.val (0, 0, 0, 0)).2.1 = 0 ∨ (getR LD j.val (0, 0, 0, 0)).2.1 = 1 ∨
        (getR LD j.val (0, 0, 0, 0)).2.1 = 2 := by
      have := Nat.le_of_ble_eq_true hi; omega
    exact leaf_of_leafChkB hcore hi' hl
  · exfalso
    apply not_dfree_of_ndfB (hn := hn) hel hsd0 (v := ((ofList n el hn).ends j).1) _ hs
    rw [he.1]; simp only [gER, getR_eq, gE] at hn1 ⊢; exact hn1
  · exfalso
    apply not_dfree_of_ndfB (hn := hn) hel hsd0 (v := ((ofList n el hn).ends j).2) _ ht
    rw [he.2]; simp only [gER, getR_eq, gE] at hn2 ⊢; exact hn2

end lx3

end RH2F

-- ===== from LX4.lean =====
/-
  LX4 — `GoodH H` (EX1-full, and T(H, j) star 6-colourable for every edge `j` with digon-free ends), certificates for
  ranges of hosts, and the transfer to a member `P` isomorphic to `H`: EX1-goodness and star 6-colourability of T(P, g)
  for every eligible edge `g`.
-/

namespace RH2F
open MGraph
open Classical

section lx4

/-- EX1-full, and T(H, j) star 6-colourable for every edge `j` whose ends are digon-free -/
def GoodH (H : MGraph) : Prop :=
  EX1FullH H ∧ ∀ j : Fin H.m, DFree (fun _ : Fin H.m => True) (H.ends j).1 →
    DFree (fun _ : Fin H.m => True) (H.ends j).2 → Colourable (leafSet (fun _ : Fin H.m => True) j) 6

abbrev Cert := Nat × List Tab × List (Nat × Nat × Nat × Nat)

/-- the certificates `C` (code, tables, leaf data) of representatives of the host `el` with `q` vertices -/
def hostCert (q : Nat) (el : List (Nat × Nat)) (C : List Cert) : Bool :=
  allR (fun c => repChk (q + 2 * cntT (decodeB el.length c.1)) (digEl q el (decodeB el.length c.1)) c.2.1 c.2.2) C

theorem hostCert_sound {q : Nat} {hq : 0 < q} {el : List (Nat × Nat)} {C : List Cert} (h : hostCert q el C = true) :
    ∀ c ∈ C, GoodH (digGrC q hq el c.1) := by
  intro c hc
  exact repChk_sound (allR_mem h hc)

/-- every listed code has a certificate -/
def codesIn (RC : List Nat) (C : List Cert) : Bool := allR (fun rc => anyR (fun c => Nat.beq c.1 rc) C) RC

/-- certificates for the hosts `k0, k0 + 1, …` of `L` with the representative codes `RCS` -/
def certRange (q : Nat) (L : List (List (Nat × Nat))) (RCS : List (List Nat)) (k0 : Nat) (CS : List (List Cert)) :
    Bool :=
  rangeAll CS.length (fun r => hostCert q (getR L (k0 + r) []) (getR CS r []) &&
    codesIn (getR RCS (k0 + r) []) (getR CS r []))

theorem certRange_sound {q : Nat} {hq : 0 < q} {L : List (List (Nat × Nat))} {RCS : List (List Nat)} {k0 : Nat}
    {CS : List (List Cert)} (h : certRange q L RCS k0 CS = true) :
    ∀ k, k0 ≤ k → k < k0 + CS.length → ∀ rc ∈ RCS.getD k [], GoodH (digGrC q hq (L.getD k []) rc) := by
  intro k hk0 hk1 rc hrc
  unfold certRange at h
  rw [rangeAll_eq, List.all_eq_true] at h
  have h1 := h (k - k0) (List.mem_range.2 (by omega))
  rw [show k0 + (k - k0) = k by omega, Bool.and_eq_true] at h1
  obtain ⟨hc, hcodes⟩ := h1
  rw [getR_eq, getR_eq] at hc hcodes
  have hr := allR_mem hcodes hrc
  obtain ⟨c, hcC, hcr⟩ := anyR_mem hr
  have := hostCert_sound (hq := hq) hc c hcC
  rw [Nat.eq_of_beq_eq_true hcr] at this
  exact this

/-! ### transfer to an isomorphic member -/

/-- **from a good representative**: if `P` is isomorphic to a good `H`, then `P` is EX1-good and T(P, g) is star
    6-colourable for every eligible edge `g` -/
theorem concl_of_iso {X : MGraph} {P : Fin X.m → Prop} (hG : InG X P) {H : MGraph} (hI : IsoFrom P H)
    (hH : GoodH H) : EX1On P ∧ ∀ g, Eligible P g → Colourable (leafSet P g) 6 := by
  refine ⟨ex1On_of_iso hI hH.1, fun g hE => ?_⟩
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := hI
  have hg := hE.1
  obtain ⟨ds, dt⟩ := dfree_of_eligible hG hE
  have ms : meets P (X.ends g).1 := ⟨g, hg, Or.inl rfl⟩
  have mt : meets P (X.ends g).2 := ⟨g, hg, Or.inr rfl⟩
  have Ds := dfree_iso hα hs hj ms ds
  have Dt := dfree_iso hα hs hj mt dt
  have hjg := hj g hg
  apply leaf_of_iso hG.1 hα hβ hj hg
  rcases hjg with e | e
  · apply hH.2 (β g) <;> rw [e]
    · exact Ds
    · exact Dt
  · apply hH.2 (β g) <;> rw [e]
    · exact Dt
    · exact Ds

theorem digGrC_pos {q : Nat} (hq : 0 < q) (el : List (Nat × Nat)) (hm : 0 < el.length) (rc : Nat) :
    0 < (digGrC q hq el rc).n ∧ 0 < (digGrC q hq el rc).m := by
  refine ⟨?_, ?_⟩
  · show 0 < q + 2 * cntT (decodeB el.length rc); omega
  · show 0 < (digEl q el (decodeB el.length rc)).length
    rw [length_digEl]; omega

end lx4

end RH2F

-- ===== from LX5.lean =====
namespace RH2F
open MGraph
open Classical

/-- **Layer 31a**: (1) the local extension to the leaf graph; (2) soundness of the representative certificates;
    (3) the classification of digon insertions by covering codes; (4) the passage from 2-cut-reduced members of 𝒢 to
    digon insertions of members of 𝒮; (5) the transfer from a good representative -/
theorem layer31a :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (c : Fin X.m → Fin 6) (g : Fin X.m) (α β : Fin 6),
      StarOn P 6 c → (X.ends g).1 ≠ (X.ends g).2 → α ≠ β → α ≠ 5 → β ≠ 5 →
      LocOK P c g (X.ends g).1 α β → LocOK P c g (X.ends g).2 β α → LeafCrossOK P c g α β →
      StarOn (leafSet P g) 6 (extC c g α β)) ∧
    (∀ (n : Nat) (el : List (Nat × Nat)) (hn : 0 < n) (TS : List Tab) (LD : List (Nat × Nat × Nat × Nat)),
      repChk n el TS LD = true → GoodH (ofList n el hn)) ∧
    (∀ (q lo hi : Nat) (hq : 0 < q), q ≤ 16 → ∀ (L : List (List (Nat × Nat))) (AUTS : List (List (Nat × List Nat)))
      (RCS : List (List Nat)), covAllB q lo hi L AUTS RCS = true →
      (∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → vcount Q = q →
        ∃ k, k < L.length ∧ IsoFrom Q (ofList q (L.getD k []) hq)) →
      ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q → vcount Q = q → lo ≤ q + 2 * cntF Y.m (fun f => Q f ∧ D f) →
        cntF Y.m (fun f => Q f ∧ D f) ≤ hi →
        ∃ k, k < L.length ∧ ∃ rc ∈ RCS.getD k [], IsoFrom (digSet Q D) (digGrC q hq (L.getD k []) rc)) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → TwoCutReducedOn P → 10 ≤ vcount P →
      ∃ (Y : MGraph) (Q D : Fin Y.m → Prop), InS Y Q ∧ 4 ≤ vcount Q ∧ vcount Q % 2 = 0 ∧
        vcount P = vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) ∧
        ∀ H : MGraph, IsoFrom (digSet Q D) H → 0 < H.n → 0 < H.m → IsoFrom P H) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (H : MGraph), InG X P → IsoFrom P H → GoodH H →
      EX1On P ∧ ∀ g, Eligible P g → Colourable (leafSet P g) 6) :=
  ⟨fun _ _ _ _ _ _ hc hst hab ha5 hb5 hs ht hx => leaf_ext hc hst hab ha5 hb5 hs ht hx,
   fun _ _ _ _ _ h => repChk_sound h,
   fun _ _ _ _ hq16 _ _ _ hc hcls => digClassB hq16 hc hcls,
   fun _ _ hG h2 h10 => to_dig hG h2 h10,
   fun _ _ _ hG hI hH => concl_of_iso hG hI hH⟩

end RH2F
