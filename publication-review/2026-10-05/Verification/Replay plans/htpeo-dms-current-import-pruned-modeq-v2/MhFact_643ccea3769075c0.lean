-- Lean proof of fact 643ccea3769075c0 (RH2F.layer5); added by fact_submit, do not edit
import MhFact_341b6e5e1be16205



-- ===== from RH2Iso.lean =====
/-
  RH2Iso.lean — isomorphisms of an edge set `P` onto a concrete multigraph `H` (maps from `P` to `H`), concrete
  isomorphisms between explicit multigraphs (checked by a Bool checker), and composition.
-/

namespace RH2F
open MGraph
open Classical

section iso
variable {X : MGraph}

/-- `P` is isomorphic to `H` (all of whose edges are hit), by a vertex map `α` injective on the vertices of `P` and an
    edge map `β` injective on `P`, onto the edges of `H`, respecting incidence -/
def IsoFrom (P : Fin X.m → Prop) (H : MGraph) : Prop :=
  ∃ (α : Fin X.n → Fin H.n) (β : Fin X.m → Fin H.m),
    (∀ x y, meets P x → meets P y → α x = α y → x = y) ∧
    (∀ f g, P f → P g → β f = β g → f = g) ∧
    (∀ j, ∃ f, P f ∧ β f = j) ∧
    (∀ f, P f → H.Joins (β f) (α (X.ends f).1) (α (X.ends f).2))

/-- an isomorphism of explicit multigraphs -/
def ConcIso (H H' : MGraph) : Prop :=
  ∃ (σ : Fin H.n → Fin H'.n) (τ : Fin H.m → Fin H'.m), (∀ a b, σ a = σ b → a = b) ∧
    (∀ e e', τ e = τ e' → e = e') ∧ (∀ j, ∃ e, τ e = j) ∧ (∀ e, H'.Joins (τ e) (σ (H.ends e).1) (σ (H.ends e).2))

theorem joins_map {H H' : MGraph} {σ : Fin H.n → Fin H'.n} {τ : Fin H.m → Fin H'.m}
    (hj : ∀ e, H'.Joins (τ e) (σ (H.ends e).1) (σ (H.ends e).2)) {e : Fin H.m} {p q : Fin H.n}
    (h : H.Joins e p q) : H'.Joins (τ e) (σ p) (σ q) := by
  rcases h with h | h <;> have := hj e <;> rw [h] at this
  · exact this
  · exact Or.symm this

theorem isoFrom_trans {P : Fin X.m → Prop} {H H' : MGraph} (h : IsoFrom P H) (h' : ConcIso H H') :
    IsoFrom P H' := by
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := h
  obtain ⟨σ, τ, hσ, hτ, hτs, hτj⟩ := h'
  refine ⟨fun x => σ (α x), fun f => τ (β f), fun x y hx hy h => hα x y hx hy (hσ _ _ h),
    fun f g hf hg h => hβ f g hf hg (hτ _ _ h), fun j => ?_, fun f hf => joins_map hτj (hj f hf)⟩
  obtain ⟨e, rfl⟩ := hτs j
  obtain ⟨f, hf, rfl⟩ := hs e
  exact ⟨f, hf, rfl⟩

/-! ### a checker for concrete isomorphisms -/

/-- the image of `i` under a list (default 0, reduced mod `n`) -/
def lget (l : List Nat) (n : Nat) (hn : 0 < n) (i : Nat) : Fin n := ⟨l.getD i 0 % n, Nat.mod_lt _ hn⟩

def allFin (n : Nat) (p : Fin n → Bool) : Bool := (List.finRange n).all p

theorem allFin_sound {n : Nat} {p : Fin n → Bool} (h : allFin n p = true) : ∀ i, p i = true :=
  fun i => List.all_eq_true.1 h i (mem_finRange' i)

/-- the Bool check of a concrete isomorphism `H → H'` given by vertex images `s` and edge images `t` -/
def isoChk (H H' : MGraph) (hn : 0 < H'.n) (hm : 0 < H'.m) (s t : List Nat) : Bool :=
  allFin H.n (fun a => allFin H.n (fun b => !(lget s H'.n hn a.val == lget s H'.n hn b.val) || a == b)) &&
  allFin H.m (fun e => allFin H.m (fun e' => !(lget t H'.m hm e.val == lget t H'.m hm e'.val) || e == e')) &&
  allFin H'.m (fun j => (List.finRange H.m).any (fun e => lget t H'.m hm e.val == j)) &&
  allFin H.m (fun e =>
    (H'.ends (lget t H'.m hm e.val) == (lget s H'.n hn (H.ends e).1.val, lget s H'.n hn (H.ends e).2.val)) ||
    (H'.ends (lget t H'.m hm e.val) == (lget s H'.n hn (H.ends e).2.val, lget s H'.n hn (H.ends e).1.val)))

theorem concIso_of_chk {H H' : MGraph} {hn : 0 < H'.n} {hm : 0 < H'.m} {s t : List Nat}
    (h : isoChk H H' hn hm s t = true) : ConcIso H H' := by
  simp only [isoChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun a => lget s H'.n hn a.val, fun e => lget t H'.m hm e.val, fun a b hab => ?_, fun e e' hee => ?_,
    fun j => ?_, fun e => ?_⟩
  · have := allFin_sound (allFin_sound h1 a) b
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hab h
    · exact h
  · have := allFin_sound (allFin_sound h2 e) e'
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd hee h
    · exact h
  · have := allFin_sound h3 j
    obtain ⟨e, _, he⟩ := List.any_eq_true.1 this
    exact ⟨e, by simpa using he⟩
  · have := allFin_sound h4 e
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h

end iso

end RH2F

-- ===== from RH2Reps.lean =====
/-
  RH2Reps.lean — the 25 representatives Rep01–Rep25 of fact be9b0c62ac86fc55 as multigraphs, and the constructions
  Sub (replace an edge by a path through a digon) and Inf (replace a vertex by a triangle) of fact 7922314679f8733d §1.
-/

namespace RH2F
open MGraph

/-- the edge list of `Rep k` -/
def repL : Nat → List (Nat × Nat)
  | 1 => [(0,1), (0,1), (0,1)]
  | 2 => [(0,1), (0,1), (0,2), (2,3), (2,3), (3,1)]
  | 3 => [(0,1), (2,1), (3,1), (0,2), (2,3), (0,3)]
  | 4 => [(0,1), (0,1), (2,3), (2,3), (3,1), (0,4), (4,5), (4,5), (5,2)]
  | 5 => [(0,1), (0,2), (2,3), (2,3), (3,1), (0,4), (4,5), (4,5), (5,1)]
  | 6 => [(2,1), (3,1), (0,2), (2,3), (0,3), (0,4), (4,5), (4,5), (5,1)]
  | 7 => [(0,1), (2,1), (3,1), (4,2), (2,3), (5,3), (0,4), (4,5), (0,5)]
  | 8 => [(0,3), (0,4), (0,5), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5)]
  | 9 => [(0,1), (2,3), (2,3), (3,1), (0,4), (4,5), (4,5), (5,2), (0,6), (6,7), (6,7), (7,1)]
  | 10 => [(0,1), (0,1), (2,3), (2,3), (0,4), (4,5), (4,5), (5,2), (3,6), (6,7), (6,7), (7,1)]
  | 11 => [(0,2), (2,3), (2,3), (3,1), (0,4), (4,5), (4,5), (5,1), (0,6), (6,7), (6,7), (7,1)]
  | 12 => [(0,1), (2,3), (2,3), (3,1), (0,4), (4,5), (4,5), (5,1), (0,6), (6,7), (6,7), (7,2)]
  | 13 => [(0,1), (0,2), (2,3), (3,1), (0,4), (4,5), (4,5), (5,1), (2,6), (6,7), (6,7), (7,3)]
  | 14 => [(2,1), (3,1), (0,2), (2,3), (0,3), (4,5), (4,5), (5,1), (0,6), (6,7), (6,7), (7,4)]
  | 15 => [(2,1), (3,1), (0,2), (2,3), (0,3), (0,4), (4,5), (5,1), (4,6), (6,7), (6,7), (7,5)]
  | 16 => [(2,1), (3,1), (0,2), (0,3), (0,4), (4,5), (4,5), (5,1), (2,6), (6,7), (6,7), (7,3)]
  | 17 => [(2,1), (3,1), (2,3), (0,3), (0,4), (4,5), (4,5), (5,1), (0,6), (6,7), (6,7), (7,2)]
  | 18 => [(2,1), (3,1), (0,2), (2,3), (0,3), (0,4), (6,5), (7,5), (5,1), (4,6), (6,7), (4,7)]
  | 19 => [(0,1), (3,1), (4,2), (2,3), (5,3), (0,4), (4,5), (0,5), (2,6), (6,7), (6,7), (7,1)]
  | 20 => [(2,1), (3,1), (4,2), (2,3), (5,3), (0,4), (4,5), (0,5), (0,6), (6,7), (6,7), (7,1)]
  | 21 => [(0,1), (2,1), (3,1), (4,2), (2,3), (5,3), (6,4), (4,5), (7,5), (0,6), (6,7), (0,7)]
  | 22 => [(0,4), (0,5), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (0,6), (6,7), (6,7), (7,3)]
  | 23 => [(0,3), (6,4), (7,5), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (0,6), (6,7), (0,7)]
  | 24 => [(0,1), (0,2), (0,3), (4,5), (4,6), (4,7), (1,6), (1,7), (2,5), (2,7), (3,5), (3,6)]
  | 25 => [(0,1), (0,2), (0,3), (4,5), (5,6), (6,7), (5,1), (6,2), (4,2), (4,3), (7,1), (7,3)]
  | _ => [(0,1),(0,1),(0,1)]

/-- the number of vertices of `Rep k` -/
def repN : Nat → Nat
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | 8 => 6
  | 9 => 8
  | 10 => 8
  | 11 => 8
  | 12 => 8
  | 13 => 8
  | 14 => 8
  | 15 => 8
  | 16 => 8
  | 17 => 8
  | 18 => 8
  | 19 => 8
  | 20 => 8
  | 21 => 8
  | 22 => 8
  | 23 => 8
  | 24 => 8
  | 25 => 8
  | _ => 2

theorem repN_pos (k : Nat) : 0 < repN k := by
  unfold repN; split <;> decide

/-- `Rep k` as a multigraph on `Fin (repN k)` -/
def repG (k : Nat) : MGraph := ofList (repN k) (repL k) (repN_pos k)

/-! ### Sub and Inf -/

section subinf
variable (H : MGraph)

def nv0 : Fin (H.n + 2) := Fin.natAdd H.n ⟨0, by decide⟩
def nv1 : Fin (H.n + 2) := Fin.natAdd H.n ⟨1, by decide⟩
def ov (v : Fin H.n) : Fin (H.n + 2) := Fin.castAdd 2 v

/-- `Sub(H, i)`: edge `i = xy` becomes `x N0`; new edges `N0 N1`, `N0 N1`, `N1 y` (indices `m`, `m+1`, `m+2`) -/
def subG (i : Fin H.m) : MGraph where
  n := H.n + 2
  m := H.m + 3
  ends := fun e =>
    if h : e.val < H.m then
      (if e.val = i.val then (ov H (H.ends i).1, nv0 H) else (ov H (H.ends ⟨e.val, h⟩).1, ov H (H.ends ⟨e.val, h⟩).2))
    else if e.val = H.m then (nv0 H, nv1 H)
    else if e.val = H.m + 1 then (nv0 H, nv1 H)
    else (nv1 H, ov H (H.ends i).2)

/-- replace the end `t` of an edge by `N` -/
def repl (t : Fin H.n) (N : Fin (H.n + 2)) (p : Fin H.n × Fin H.n) : Fin (H.n + 2) × Fin (H.n + 2) :=
  (if p.1 = t then N else ov H p.1, if p.2 = t then N else ov H p.2)

/-- `Inf(H, t)` with the edges `i2`, `i3` at `t` moved to `N0`, `N1`; new edges `t N0`, `N0 N1`, `t N1` -/
def infG (t : Fin H.n) (i2 i3 : Fin H.m) : MGraph where
  n := H.n + 2
  m := H.m + 3
  ends := fun e =>
    if h : e.val < H.m then
      (if e.val = i2.val then repl H t (nv0 H) (H.ends i2)
       else if e.val = i3.val then repl H t (nv1 H) (H.ends i3)
       else (ov H (H.ends ⟨e.val, h⟩).1, ov H (H.ends ⟨e.val, h⟩).2))
    else if e.val = H.m then (ov H t, nv0 H)
    else if e.val = H.m + 1 then (nv0 H, nv1 H)
    else (ov H t, nv1 H)

end subinf

end RH2F

-- ===== from RH2Dig.lean =====
/-
  RH2Dig.lean — Lemmas 1 and 2 of fact 7922314679f8733d (B8) in Lean 4.20 core: no triple edges, and the digon
  reduction `H ≅ Sub(K, i)`.
-/

namespace RH2F
open MGraph
open Classical

section dig
variable {X : MGraph} {P : Fin X.m → Prop}

/-- **Lemma 1** (no triple edges): three distinct edges joining `u, v` in a connected cubic `P` force `P` to have
    only the two vertices `u, v` -/
theorem no_triple (hG : InG X P) {u v : Fin X.n} {a b c : Fin X.m} (ha : P a) (hb : P b) (hc : P c)
    (ja : X.Joins a u v) (jb : X.Joins b u v) (jc : X.Joins c u v) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    vcount P ≤ 2 := by
  have huv : u ≠ v := ne_of_joins hG.1 ja
  -- every edge at `u` or `v` is one of `a, b, c`
  have cov : ∀ d w, P d → X.Inc d w → (w = u ∨ w = v) → d = a ∨ d = b ∨ d = c := by
    intro d w hd hdw hw
    obtain ⟨p, q, r, _, _, _, _, _, _, _, _, _, hall⟩ := hG.2.2.2 w ⟨a, ha, by
      rcases hw with rfl | rfl; exact joins_inc_left ja; exact joins_inc_right ja⟩
    have ia : X.Inc a w := by rcases hw with rfl | rfl; exact joins_inc_left ja; exact joins_inc_right ja
    have ib : X.Inc b w := by rcases hw with rfl | rfl; exact joins_inc_left jb; exact joins_inc_right jb
    have ic : X.Inc c w := by rcases hw with rfl | rfl; exact joins_inc_left jc; exact joins_inc_right jc
    apply Classical.byContradiction
    intro hne
    simp only [not_or] at hne
    rcases hall a ha ia with e1 | e1 | e1 <;> rcases hall b hb ib with e2 | e2 | e2 <;>
      rcases hall c hc ic with e3 | e3 | e3 <;> rcases hall d hd hdw with e4 | e4 | e4 <;>
      first
      | exact hab (e1.trans e2.symm) | exact hac (e1.trans e3.symm) | exact hbc (e2.trans e3.symm)
      | exact hne.1 (e4.trans e1.symm) | exact hne.2.1 (e4.trans e2.symm) | exact hne.2.2 (e4.trans e3.symm)
  -- the labelling of `{u, v}` separates no edge
  let U : Fin X.n → Bool := fun w => decide (w = u ∨ w = v)
  have ends_uv : ∀ d, (d = a ∨ d = b ∨ d = c) → U (X.ends d).1 = true ∧ U (X.ends d).2 = true := by
    have key : ∀ d, X.Joins d u v → U (X.ends d).1 = true ∧ U (X.ends d).2 = true := by
      intro d hj; rcases hj with h | h <;> rw [h] <;> simp [U]
    rintro d (rfl | rfl | rfl)
    · exact key _ ja
    · exact key _ jb
    · exact key _ jc
  have hsep : ∀ d, P d → U (X.ends d).1 = U (X.ends d).2 := by
    intro d hd
    by_cases h1 : U (X.ends d).1 = true
    · have hw : (X.ends d).1 = u ∨ (X.ends d).1 = v := by simpa [U] using h1
      have := ends_uv d (cov d _ hd (Or.inl rfl) hw)
      rw [this.1, this.2]
    · by_cases h2 : U (X.ends d).2 = true
      · have hw : (X.ends d).2 = u ∨ (X.ends d).2 = v := by simpa [U] using h2
        have := ends_uv d (cov d _ hd (Or.inr rfl) hw)
        exact absurd this.1 h1
      · simp only [Bool.not_eq_true] at h1 h2; rw [h1, h2]
  -- hence every vertex of `P` is `u` or `v`
  have hall : ∀ w, meets P w → w = u ∨ w = v := by
    rintro w ⟨d, hd, hdw⟩
    have := hG.2.1 U hsep d a hd ha
    have hua : U (X.ends a).1 = true := (ends_uv a (Or.inl rfl)).1
    rw [hua] at this
    have hd1 : U (X.ends d).1 = true := this
    have hd2 : U (X.ends d).2 = true := (hsep d hd) ▸ hd1
    rcases hdw with h | h
    · rw [← h]; simpa [U] using hd1
    · rw [← h]; simpa [U] using hd2
  have := cntF_mono X.n (meets P) (fun w => w = u ∨ w = v) hall
  rw [cntF_pair X.n huv] at this
  exact this

/-! ### ends of `Sub(H, i)` -/

section subends
variable (H : MGraph) (i : Fin H.m)

def se (e : Fin H.m) : Fin (subG H i).m := Fin.castAdd 3 e
def sm0 : Fin (subG H i).m := ⟨H.m, by show H.m < H.m + 3; omega⟩
def sm1 : Fin (subG H i).m := ⟨H.m + 1, by show H.m + 1 < H.m + 3; omega⟩
def sm2 : Fin (subG H i).m := ⟨H.m + 2, by show H.m + 2 < H.m + 3; omega⟩

theorem subG_ends_i : (subG H i).ends (se H i i) = (ov H (H.ends i).1, nv0 H) := by
  simp [subG, se]

theorem subG_ends_old {e : Fin H.m} (h : e ≠ i) :
    (subG H i).ends (se H i e) = (ov H (H.ends e).1, ov H (H.ends e).2) := by
  have h' : e.val ≠ i.val := fun h'' => h (Fin.ext h'')
  simp [subG, se, h']

theorem subG_ends_m0 : (subG H i).ends (sm0 H i) = (nv0 H, nv1 H) := by simp [subG, sm0]
theorem subG_ends_m1 : (subG H i).ends (sm1 H i) = (nv0 H, nv1 H) := by
  simp [subG, sm1]; intro h; exact absurd h (by omega)
theorem subG_ends_m2 : (subG H i).ends (sm2 H i) = (nv1 H, ov H (H.ends i).2) := by
  simp [subG, sm2]; intro h; exact absurd h (by omega)

theorem sub_edge_cases (j : Fin (subG H i).m) :
    (∃ e, j = se H i e) ∨ j = sm0 H i ∨ j = sm1 H i ∨ j = sm2 H i := by
  have hj : j.val < H.m + 3 := j.isLt
  by_cases h : j.val < H.m
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · by_cases h0 : j.val = H.m
    · exact Or.inr (Or.inl (Fin.ext h0))
    · by_cases h1 : j.val = H.m + 1
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h1)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by show j.val = H.m + 2; omega))))

theorem se_inj {e e' : Fin H.m} (h : se H i e = se H i e') : e = e' := by
  have := congrArg Fin.val h; exact Fin.ext (by simpa [se] using this)
theorem se_ne_m0 (e : Fin H.m) : se H i e ≠ sm0 H i := fun h => by
  have := congrArg Fin.val h; simp [se, sm0] at this; omega
theorem se_ne_m1 (e : Fin H.m) : se H i e ≠ sm1 H i := fun h => by
  have := congrArg Fin.val h; simp [se, sm1] at this; omega
theorem se_ne_m2 (e : Fin H.m) : se H i e ≠ sm2 H i := fun h => by
  have := congrArg Fin.val h; simp [se, sm2] at this; omega
theorem sm01 : sm0 H i ≠ sm1 H i := fun h => by have := congrArg Fin.val h; simp [sm0, sm1] at this
theorem sm02 : sm0 H i ≠ sm2 H i := fun h => by have := congrArg Fin.val h; simp [sm0, sm2] at this
theorem sm12 : sm1 H i ≠ sm2 H i := fun h => by have := congrArg Fin.val h; simp [sm1, sm2] at this

theorem ov_inj {a b : Fin H.n} (h : ov H a = ov H b) : a = b := Fin.ext (by simpa [ov] using congrArg Fin.val h)
theorem ov_ne0 (a : Fin H.n) : ov H a ≠ nv0 H := fun h => by have := congrArg Fin.val h; simp [ov, nv0] at this; omega
theorem ov_ne1 (a : Fin H.n) : ov H a ≠ nv1 H := fun h => by have := congrArg Fin.val h; simp [ov, nv1] at this; omega
theorem nv01 : nv0 H ≠ nv1 H := fun h => by have := congrArg Fin.val h; simp [nv0, nv1] at this

end subends

/-- joining is transported through a vertex map -/
theorem joins_ends_of {Y : MGraph} {f : Fin X.m} {e : Fin Y.m} {φ : Fin X.n → Fin Y.n} {a b : Fin X.n}
    (hf : X.Joins f a b) (he : Y.Joins e (φ a) (φ b)) : Y.Joins e (φ (X.ends f).1) (φ (X.ends f).2) := by
  rcases hf with h | h <;> rw [h]
  · exact he
  · exact Or.symm he

/-- **lifting through a digon** (one orientation): an isomorphism of `P` minus the digon (with the new edge `x0 y0`
    sent to `i`) extends to an isomorphism of `P` onto `Sub(H, i)` -/
theorem subLift {H : MGraph} {u0 v0 x0 y0 : Fin X.n} {d1 d2 g0 h0 : Fin X.m}
    (hd1 : P d1) (hd2 : P d2) (hg0 : P g0) (hh0 : P h0)
    (j1 : X.Joins d1 u0 v0) (j2 : X.Joins d2 u0 v0) (jg : X.Joins g0 u0 x0) (jh : X.Joins h0 v0 y0) (d12 : d1 ≠ d2)
    (cov0 : ∀ d, P d → X.Inc d u0 → d = d1 ∨ d = d2 ∨ d = g0)
    (cov1 : ∀ d, P d → X.Inc d v0 → d = d1 ∨ d = d2 ∨ d = h0)
    (huv : u0 ≠ v0) (hxu : x0 ≠ u0) (hxv : x0 ≠ v0) (hyu : y0 ≠ u0) (hyv : y0 ≠ v0)
    (α' : Fin X.n → Fin H.n) (γ : Fin X.m → Fin H.m) (i : Fin H.m)
    (ha : ∀ x y, meets P x → meets P y → x ≠ u0 → x ≠ v0 → y ≠ u0 → y ≠ v0 → α' x = α' y → x = y)
    (hb : ∀ f g, P f → P g → ¬ X.Inc f u0 → ¬ X.Inc f v0 → ¬ X.Inc g u0 → ¬ X.Inc g v0 → γ f = γ g → f = g)
    (hbi : ∀ f, P f → ¬ X.Inc f u0 → ¬ X.Inc f v0 → γ f ≠ i)
    (hs : ∀ j, j ≠ i → ∃ f, P f ∧ ¬ X.Inc f u0 ∧ ¬ X.Inc f v0 ∧ γ f = j)
    (hj : ∀ f, P f → ¬ X.Inc f u0 → ¬ X.Inc f v0 → H.Joins (γ f) (α' (X.ends f).1) (α' (X.ends f).2))
    (hi : H.ends i = (α' x0, α' y0)) :
    IsoFrom P (subG H i) := by
  -- the edges at `u0`, `v0`
  have hg0h0 : g0 ≠ h0 := by
    intro h; subst h
    rcases inc_of_joins jh (joins_inc_left jg) with h' | h'
    · exact huv h'
    · exact hyu h'.symm
  have d1g : d1 ≠ g0 := by
    intro h; subst h
    rcases joins_unique j1 jg with ⟨_, h'⟩ | ⟨_, h'⟩
    · exact hxv h'.symm
    · exact huv h'.symm
  have d2g : d2 ≠ g0 := by
    intro h; subst h
    rcases joins_unique j2 jg with ⟨_, h'⟩ | ⟨_, h'⟩
    · exact hxv h'.symm
    · exact huv h'.symm
  have d1h : d1 ≠ h0 := by
    intro h; subst h
    rcases joins_unique j1 jh with ⟨h', _⟩ | ⟨h', _⟩
    · exact huv h'
    · exact hyu h'.symm
  have d2h : d2 ≠ h0 := by
    intro h; subst h
    rcases joins_unique j2 jh with ⟨h', _⟩ | ⟨h', _⟩
    · exact huv h'
    · exact hyu h'.symm
  -- an edge not among `d1, d2, g0, h0` avoids `u0` and `v0`
  have away : ∀ f, P f → f ≠ d1 → f ≠ d2 → f ≠ g0 → f ≠ h0 → ¬ X.Inc f u0 ∧ ¬ X.Inc f v0 := by
    intro f hf n1 n2 ng nh
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases cov0 f hf h with h' | h' | h'
      · exact n1 h'
      · exact n2 h'
      · exact ng h'
    · rcases cov1 f hf h with h' | h' | h'
      · exact n1 h'
      · exact n2 h'
      · exact nh h'
  let α : Fin X.n → Fin (subG H i).n := fun w => if w = u0 then nv0 H else if w = v0 then nv1 H else ov H (α' w)
  let β : Fin X.m → Fin (subG H i).m := fun f =>
    if f = g0 then se H i i else if f = d1 then sm0 H i else if f = d2 then sm1 H i
    else if f = h0 then sm2 H i else se H i (γ f)
  have αu : α u0 = nv0 H := by simp [α]; rfl
  have αv : α v0 = nv1 H := by simp [α, Ne.symm huv]; rfl
  have αo : ∀ w, w ≠ u0 → w ≠ v0 → α w = ov H (α' w) := fun w h1 h2 => by simp [α, h1, h2]; rfl
  have βg : β g0 = se H i i := by simp [β]
  have β1 : β d1 = sm0 H i := by simp [β, d1g]
  have β2 : β d2 = sm1 H i := by simp [β, d2g, Ne.symm d12]
  have βh : β h0 = sm2 H i := by simp [β, Ne.symm hg0h0, Ne.symm d1h, Ne.symm d2h]
  have βo : ∀ f, f ≠ d1 → f ≠ d2 → f ≠ g0 → f ≠ h0 → β f = se H i (γ f) := fun f n1 n2 ng nh => by
    simp [β, n1, n2, ng, nh]
  -- vertices of `P` other than `u0`, `v0`
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · intro a b ha' hb' hab
    by_cases hau : a = u0
    · by_cases hbu : b = u0
      · rw [hau, hbu]
      · by_cases hbv : b = v0
        · rw [hau, αu, hbv, αv] at hab; exact absurd hab (nv01 H)
        · rw [hau, αu, αo b hbu hbv] at hab; exact absurd hab.symm (ov_ne0 H _)
    · by_cases hav : a = v0
      · by_cases hbu : b = u0
        · rw [hav, αv, hbu, αu] at hab; exact absurd hab.symm (nv01 H)
        · by_cases hbv : b = v0
          · rw [hav, hbv]
          · rw [hav, αv, αo b hbu hbv] at hab; exact absurd hab.symm (ov_ne1 H _)
      · by_cases hbu : b = u0
        · rw [αo a hau hav, hbu, αu] at hab; exact absurd hab (ov_ne0 H _)
        · by_cases hbv : b = v0
          · rw [αo a hau hav, hbv, αv] at hab; exact absurd hab (ov_ne1 H _)
          · rw [αo a hau hav, αo b hbu hbv] at hab
            exact ha a b ha' hb' hau hav hbu hbv (ov_inj H hab)
  · -- injectivity of `β` on `P`
    have img : ∀ f, P f → (f = g0 ∧ β f = se H i i) ∨ (f = d1 ∧ β f = sm0 H i) ∨ (f = d2 ∧ β f = sm1 H i) ∨
        (f = h0 ∧ β f = sm2 H i) ∨ (¬ X.Inc f u0 ∧ ¬ X.Inc f v0 ∧ β f = se H i (γ f)) := by
      intro f hf
      by_cases ng : f = g0
      · exact Or.inl ⟨ng, ng ▸ βg⟩
      by_cases n1 : f = d1
      · exact Or.inr (Or.inl ⟨n1, n1 ▸ β1⟩)
      by_cases n2 : f = d2
      · exact Or.inr (Or.inr (Or.inl ⟨n2, n2 ▸ β2⟩))
      by_cases nh : f = h0
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨nh, nh ▸ βh⟩)))
      obtain ⟨a1, a2⟩ := away f hf n1 n2 ng nh
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, βo f n1 n2 ng nh⟩)))
    intro f g hf hg hfg
    rcases img f hf with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨fu, fv, e1⟩ <;>
    rcases img g hg with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨gu, gv, e2⟩ <;>
    first
    | rfl
    | (rw [e1, e2] at hfg; first
    | exact absurd hfg (se_ne_m0 H i _) | exact absurd hfg (se_ne_m1 H i _) | exact absurd hfg (se_ne_m2 H i _)
    | exact absurd hfg.symm (se_ne_m0 H i _) | exact absurd hfg.symm (se_ne_m1 H i _)
    | exact absurd hfg.symm (se_ne_m2 H i _)
    | exact absurd hfg (sm01 H i) | exact absurd hfg (sm02 H i) | exact absurd hfg (sm12 H i)
    | exact absurd hfg.symm (sm01 H i) | exact absurd hfg.symm (sm02 H i) | exact absurd hfg.symm (sm12 H i)
    | exact absurd (se_inj H i hfg).symm (hbi _ hg gu gv) | exact absurd (se_inj H i hfg) (hbi _ hf fu fv)
    | exact hb f g hf hg fu fv gu gv (se_inj H i hfg))
  · -- surjectivity
    intro j
    rcases sub_edge_cases H i j with ⟨e, rfl⟩ | rfl | rfl | rfl
    · by_cases hei : e = i
      · subst hei; exact ⟨g0, hg0, βg⟩
      · obtain ⟨f, hf, fu, fv, rfl⟩ := hs e hei
        have n1 : f ≠ d1 := fun h => fu (h ▸ joins_inc_left j1)
        have n2 : f ≠ d2 := fun h => fu (h ▸ joins_inc_left j2)
        have ng : f ≠ g0 := fun h => fu (h ▸ joins_inc_left jg)
        have nh : f ≠ h0 := fun h => fv (h ▸ joins_inc_left jh)
        exact ⟨f, hf, βo f n1 n2 ng nh⟩
    · exact ⟨d1, hd1, β1⟩
    · exact ⟨d2, hd2, β2⟩
    · exact ⟨h0, hh0, βh⟩
  · -- incidences
    intro f hf
    by_cases ng : f = g0
    · subst ng
      rw [βg]
      apply joins_ends_of jg
      rw [αu, αo x0 hxu hxv]
      show (subG H i).Joins (se H i i) (nv0 H) (ov H (α' x0))
      exact Or.inr (by rw [subG_ends_i, hi]; rfl)
    by_cases n1 : f = d1
    · subst n1; rw [β1]; apply joins_ends_of j1; rw [αu, αv]; exact Or.inl (subG_ends_m0 H i)
    by_cases n2 : f = d2
    · subst n2; rw [β2]; apply joins_ends_of j2; rw [αu, αv]; exact Or.inl (subG_ends_m1 H i)
    by_cases nh : f = h0
    · subst nh
      rw [βh]
      apply joins_ends_of jh
      rw [αv, αo y0 hyu hyv]
      exact Or.inl (by rw [subG_ends_m2, hi]; rfl)
    obtain ⟨fu, fv⟩ := away f hf n1 n2 ng nh
    rw [βo f n1 n2 ng nh]
    have e1u : (X.ends f).1 ≠ u0 := fun h => fu (Or.inl h)
    have e1v : (X.ends f).1 ≠ v0 := fun h => fv (Or.inl h)
    have e2u : (X.ends f).2 ≠ u0 := fun h => fu (Or.inr h)
    have e2v : (X.ends f).2 ≠ v0 := fun h => fv (Or.inr h)
    rw [αo _ e1u e1v, αo _ e2u e2v]
    have hne : γ f ≠ i := hbi f hf fu fv
    rcases hj f hf fu fv with h | h
    · exact Or.inl (by rw [subG_ends_old H i hne, h]; rfl)
    · exact Or.inr (by rw [subG_ends_old H i hne, h]; rfl)

/-- cubicity transported along an edge map that is a bijection between the edges at `w` and at `w'` -/
theorem cubic_at_of_map {Y : MGraph} {Q : Fin Y.m → Prop} (hcub : CubicOn P) {w : Fin X.n} {w' : Fin Y.n}
    (hw : meets P w) (φ : Fin X.m → Fin Y.m) (h1 : ∀ d, P d → X.Inc d w → Q (φ d) ∧ Y.Inc (φ d) w')
    (h2 : ∀ d d', P d → P d' → X.Inc d w → X.Inc d' w → φ d = φ d' → d = d')
    (h3 : ∀ j, Q j → Y.Inc j w' → ∃ d, P d ∧ X.Inc d w ∧ φ d = j) :
    ∃ a b c, Q a ∧ Q b ∧ Q c ∧ Y.Inc a w' ∧ Y.Inc b w' ∧ Y.Inc c w' ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ d, Q d → Y.Inc d w' → d = a ∨ d = b ∨ d = c := by
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ := hcub w hw
  refine ⟨φ p, φ q, φ r, (h1 p hp ip).1, (h1 q hq iq).1, (h1 r hr ir).1, (h1 p hp ip).2, (h1 q hq iq).2,
    (h1 r hr ir).2, fun h => dpq (h2 _ _ hp hq ip iq h), fun h => dpr (h2 _ _ hp hr ip ir h),
    fun h => dqr (h2 _ _ hq hr iq ir h), fun j hj hjw => ?_⟩
  obtain ⟨d, hd, hdw, rfl⟩ := h3 j hj hjw
  rcases hall d hd hdw with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- the reduced edge set of a digon: `P` without the edges at `u, v`, plus the new edge `x y` -/
def digP (P : Fin X.m → Prop) (u v x y : Fin X.n) : Fin (addEdge X x y).m → Prop :=
  fun i => i = Fin.last X.m ∨ ∃ d, i = Fin.castSucc d ∧ P d ∧ ¬ X.Inc d u ∧ ¬ X.Inc d v

/-- the data of a digon `u v` of `P` with its outer edges `gu = u x`, `gv = v y` -/
structure DigData (P : Fin X.m → Prop) where
  u : Fin X.n
  v : Fin X.n
  x : Fin X.n
  y : Fin X.n
  d1 : Fin X.m
  d2 : Fin X.m
  gu : Fin X.m
  gv : Fin X.m
  hd1 : P d1
  hd2 : P d2
  hgu : P gu
  hgv : P gv
  j1 : X.Joins d1 u v
  j2 : X.Joins d2 u v
  ju : X.Joins gu u x
  jv : X.Joins gv v y
  d12 : d1 ≠ d2
  covu : ∀ d, P d → X.Inc d u → d = d1 ∨ d = d2 ∨ d = gu
  covv : ∀ d, P d → X.Inc d v → d = d1 ∨ d = d2 ∨ d = gv
  huv : u ≠ v
  hxu : x ≠ u
  hxv : x ≠ v
  hyu : y ≠ u
  hyv : y ≠ v
  hxy : x ≠ y

/-- a digon of a member of 𝒢 with at least four vertices has distinct outer neighbours (Lemmas 1, 2) -/
theorem digData_of (hG : InG X P) (h4 : 4 ≤ vcount P) {u v : Fin X.n} {d1 d2 : Fin X.m} (hd1 : P d1) (hd2 : P d2)
    (j1 : X.Joins d1 u v) (j2 : X.Joins d2 u v) (d12 : d1 ≠ d2) : ∃ D : DigData P, D.u = u ∧ D.v = v := by
  have huv : u ≠ v := ne_of_joins hG.1 j1
  obtain ⟨gu, hgu, igu, gud1, gud2, covu⟩ := third_edge hG.2.2.2 hd1 hd2 (joins_inc_left j1) (joins_inc_left j2) d12
  obtain ⟨gv, hgv, igv, gvd1, gvd2, covv⟩ := third_edge hG.2.2.2 hd1 hd2 (joins_inc_right j1) (joins_inc_right j2) d12
  obtain ⟨x, ju⟩ := joins_of_inc igu
  obtain ⟨y, jv⟩ := joins_of_inc igv
  have hxu : x ≠ u := fun h => ne_of_joins hG.1 ju h.symm
  have hyv : y ≠ v := fun h => ne_of_joins hG.1 jv h.symm
  have hxv : x ≠ v := by
    intro h; subst h
    have := no_triple hG hd1 hd2 hgu j1 j2 ju d12 (Ne.symm gud1) (Ne.symm gud2); omega
  have hyu : y ≠ u := by
    intro h; subst h
    have := no_triple hG hd1 hd2 hgv j1 j2 (Or.symm jv) d12 (Ne.symm gvd1) (Ne.symm gvd2); omega
  have hgg : gu ≠ gv := by
    intro h; subst h
    rcases inc_of_joins jv (joins_inc_left ju) with h' | h'
    · exact huv h'
    · exact hyu h'.symm
  have hxy : x ≠ y := by
    intro hxy
    subst hxy
    obtain ⟨h, hh, ihx, hgu', hgv', covx⟩ :=
      third_edge hG.2.2.2 hgu hgv (joins_inc_right ju) (joins_inc_right jv) hgg
    obtain ⟨z, jz⟩ := joins_of_inc ihx
    have hzx : z ≠ x := fun h' => ne_of_joins hG.1 jz h'.symm
    have hzu : z ≠ u := by
      intro h'; subst h'
      rcases covu h hh (joins_inc_right jz) with h'' | h'' | h''
      · subst h''; rcases inc_of_joins j1 ihx with h3 | h3
        · exact hxu h3
        · exact hxv h3
      · subst h''; rcases inc_of_joins j2 ihx with h3 | h3
        · exact hxu h3
        · exact hxv h3
      · exact hgu' h''
    have hzv : z ≠ v := by
      intro h'; subst h'
      rcases covv h hh (joins_inc_right jz) with h'' | h'' | h''
      · subst h''; rcases inc_of_joins j1 ihx with h3 | h3
        · exact hxu h3
        · exact hxv h3
      · subst h''; rcases inc_of_joins j2 ihx with h3 | h3
        · exact hxu h3
        · exact hxv h3
      · exact hgv' h''
    -- the labelling of `{u, v, x}`: only `h` crosses it
    let U : Fin X.n → Bool := fun w => decide (w = u ∨ w = v ∨ w = x)
    have Uin : ∀ w, (w = u ∨ w = v ∨ w = x) → U w = true := fun w hw => by simp [U, hw]
    have Uout : ∀ w, w ≠ u → w ≠ v → w ≠ x → U w = false := fun w h1 h2 h3 => by simp [U, h1, h2, h3]
    apply bridgeless_sep hG.2.2.1 hh U
    · rcases jz with h' | h' <;> rw [h'] <;>
        simp only [Uin x (Or.inr (Or.inr rfl)), Uout z hzu hzv hzx] <;> decide
    · intro d hd hdh
      have both : ∀ a b, X.Joins d a b → (a = u ∨ a = v ∨ a = x) → (b = u ∨ b = v ∨ b = x) →
          U (X.ends d).1 = U (X.ends d).2 := by
        intro a b hj ha hb
        rcases hj with h' | h' <;> rw [h'] <;> simp only [Uin a ha, Uin b hb]
      by_cases hdu : X.Inc d u
      · rcases covu d hd hdu with rfl | rfl | rfl
        · exact both _ _ j1 (Or.inl rfl) (Or.inr (Or.inl rfl))
        · exact both _ _ j2 (Or.inl rfl) (Or.inr (Or.inl rfl))
        · exact both _ _ ju (Or.inl rfl) (Or.inr (Or.inr rfl))
      by_cases hdv : X.Inc d v
      · rcases covv d hd hdv with rfl | rfl | rfl
        · exact both _ _ j1 (Or.inl rfl) (Or.inr (Or.inl rfl))
        · exact both _ _ j2 (Or.inl rfl) (Or.inr (Or.inl rfl))
        · exact both _ _ jv (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      by_cases hdx : X.Inc d x
      · rcases covx d hd hdx with rfl | rfl | rfl
        · exact absurd (joins_inc_left ju) hdu
        · exact absurd (joins_inc_left jv) hdv
        · exact absurd rfl hdh
      · have n1 : (X.ends d).1 ≠ u ∧ (X.ends d).1 ≠ v ∧ (X.ends d).1 ≠ x :=
          ⟨fun h' => hdu (Or.inl h'), fun h' => hdv (Or.inl h'), fun h' => hdx (Or.inl h')⟩
        have n2 : (X.ends d).2 ≠ u ∧ (X.ends d).2 ≠ v ∧ (X.ends d).2 ≠ x :=
          ⟨fun h' => hdu (Or.inr h'), fun h' => hdv (Or.inr h'), fun h' => hdx (Or.inr h')⟩
        rw [Uout _ n1.1 n1.2.1 n1.2.2, Uout _ n2.1 n2.2.1 n2.2.2]
  exact ⟨⟨u, v, x, y, d1, d2, gu, gv, hd1, hd2, hgu, hgv, j1, j2, ju, jv, d12, covu, covv, huv, hxu, hxv, hyu, hyv,
    hxy⟩, rfl, rfl⟩

namespace DigData
variable (D : DigData P)

theorem hgg : D.gu ≠ D.gv := by
  intro h
  have := D.jv; rw [← h] at this
  rcases inc_of_joins this (joins_inc_left D.ju) with h' | h'
  · exact D.huv h'
  · exact D.hyu h'.symm

theorem gu_at {w : Fin X.n} (h : X.Inc D.gu w) : w = D.u ∨ w = D.x := inc_of_joins D.ju h
theorem gv_at {w : Fin X.n} (h : X.Inc D.gv w) : w = D.v ∨ w = D.y := inc_of_joins D.jv h

/-- an edge of `P` at a vertex `w ≠ u, v` is `gu` (then `w = x`), `gv` (then `w = y`) or avoids `u, v` -/
theorem at_w {d : Fin X.m} {w : Fin X.n} (hd : P d) (hdw : X.Inc d w) (hwu : w ≠ D.u) (hwv : w ≠ D.v) :
    (d = D.gu ∧ w = D.x) ∨ (d = D.gv ∧ w = D.y) ∨ (¬ X.Inc d D.u ∧ ¬ X.Inc d D.v) := by
  by_cases hdu : X.Inc d D.u
  · rcases D.covu d hd hdu with rfl | rfl | rfl
    · rcases inc_of_joins D.j1 hdw with h | h
      · exact absurd h hwu
      · exact absurd h hwv
    · rcases inc_of_joins D.j2 hdw with h | h
      · exact absurd h hwu
      · exact absurd h hwv
    · rcases D.gu_at hdw with h | h
      · exact absurd h hwu
      · exact Or.inl ⟨rfl, h⟩
  by_cases hdv : X.Inc d D.v
  · rcases D.covv d hd hdv with rfl | rfl | rfl
    · rcases inc_of_joins D.j1 hdw with h | h
      · exact absurd h hwu
      · exact absurd h hwv
    · rcases inc_of_joins D.j2 hdw with h | h
      · exact absurd h hwu
      · exact absurd h hwv
    · rcases D.gv_at hdw with h | h
      · exact absurd h hwv
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
  exact Or.inr (Or.inr ⟨hdu, hdv⟩)

theorem meets_digP (w : Fin X.n) :
    @meets (addEdge X D.x D.y) (digP P D.u D.v D.x D.y) w ↔ meets P w ∧ w ≠ D.u ∧ w ≠ D.v := by
  constructor
  · rintro ⟨i, hi, hiw⟩
    rcases hi with rfl | ⟨d, rfl, hd, hdu, hdv⟩
    · rcases addEdge_inc_new.1 hiw with rfl | rfl
      · exact ⟨⟨D.gu, D.hgu, joins_inc_right D.ju⟩, D.hxu, D.hxv⟩
      · exact ⟨⟨D.gv, D.hgv, joins_inc_right D.jv⟩, D.hyu, D.hyv⟩
    · have hdw := addEdge_inc_old.1 hiw
      exact ⟨⟨d, hd, hdw⟩, fun h => hdu (h ▸ hdw), fun h => hdv (h ▸ hdw)⟩
  · rintro ⟨⟨d, hd, hdw⟩, hwu, hwv⟩
    rcases D.at_w hd hdw hwu hwv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨hdu, hdv⟩
    · exact ⟨Fin.last X.m, Or.inl rfl, addEdge_inc_new.2 (Or.inl rfl)⟩
    · exact ⟨Fin.last X.m, Or.inl rfl, addEdge_inc_new.2 (Or.inr rfl)⟩
    · exact ⟨Fin.castSucc d, Or.inr ⟨d, rfl, hd, hdu, hdv⟩, addEdge_inc_old.2 hdw⟩

theorem vcount_digP : vcount (digP P D.u D.v D.x D.y) + 2 = vcount P := by
  unfold vcount
  show cntF X.n (@meets (addEdge X D.x D.y) (digP P D.u D.v D.x D.y)) + 2 = cntF X.n (meets P)
  rw [cntF_congr X.n _ _ D.meets_digP, cntF_split X.n (meets P) (fun w => w = D.u ∨ w = D.v)]
  rw [cntF_congr X.n (fun w => meets P w ∧ (w = D.u ∨ w = D.v)) (fun w => w = D.u ∨ w = D.v)
    (fun w => ⟨fun h => h.2, fun h => ⟨h.elim (fun h' => h' ▸ ⟨D.d1, D.hd1, joins_inc_left D.j1⟩)
      (fun h' => h' ▸ ⟨D.d1, D.hd1, joins_inc_right D.j1⟩), h⟩⟩)]
  rw [cntF_pair X.n D.huv, cntF_congr X.n (fun w => meets P w ∧ w ≠ D.u ∧ w ≠ D.v)
    (fun w => meets P w ∧ ¬ (w = D.u ∨ w = D.v)) (fun w => by simp only [not_or])]
  omega

theorem inG_digP (hG : InG X P) : InG (addEdge X D.x D.y) (digP P D.u D.v D.x D.y) := by
  classical
  refine ⟨addEdge_loopless hG.1 D.hxy, ?_, ?_, ?_⟩
  · -- connected
    intro U hU i j hi hj
    have hxy : U D.x = U D.y := by have := hU _ (Or.inl rfl); rwa [addEdge_ends_new] at this
    let U' : Fin X.n → Bool := fun w => if w = D.u ∨ w = D.v then U D.x else U w
    have U'uv : ∀ w, (w = D.u ∨ w = D.v) → U' w = U D.x := fun w hw => by simp [U', hw]
    have U'o : ∀ w, w ≠ D.u → w ≠ D.v → U' w = U w := fun w h1 h2 => by simp [U', h1, h2]
    have hU' : ∀ d, P d → U' (X.ends d).1 = U' (X.ends d).2 := by
      intro d hd
      have pair : ∀ a b, X.Joins d a b → U' a = U' b → U' (X.ends d).1 = U' (X.ends d).2 := by
        intro a b hj hab; rcases hj with h | h <;> rw [h]
        · exact hab
        · exact hab.symm
      by_cases hdu : X.Inc d D.u
      · rcases D.covu d hd hdu with rfl | rfl | rfl
        · exact pair _ _ D.j1 (by rw [U'uv _ (Or.inl rfl), U'uv _ (Or.inr rfl)])
        · exact pair _ _ D.j2 (by rw [U'uv _ (Or.inl rfl), U'uv _ (Or.inr rfl)])
        · exact pair _ _ D.ju (by rw [U'uv _ (Or.inl rfl), U'o _ D.hxu D.hxv])
      by_cases hdv : X.Inc d D.v
      · rcases D.covv d hd hdv with rfl | rfl | rfl
        · exact pair _ _ D.j1 (by rw [U'uv _ (Or.inl rfl), U'uv _ (Or.inr rfl)])
        · exact pair _ _ D.j2 (by rw [U'uv _ (Or.inl rfl), U'uv _ (Or.inr rfl)])
        · exact pair _ _ D.jv (by rw [U'uv _ (Or.inr rfl), U'o _ D.hyu D.hyv, hxy])
      · rw [U'o _ (fun h => hdu (Or.inl h)) (fun h => hdv (Or.inl h)),
          U'o _ (fun h => hdu (Or.inr h)) (fun h => hdv (Or.inr h))]
        have := hU _ (Or.inr ⟨d, rfl, hd, hdu, hdv⟩); rwa [addEdge_ends_old] at this
    have key : ∀ k, digP P D.u D.v D.x D.y k → U ((addEdge X D.x D.y).ends k).1 = U' (X.ends D.gu).1 := by
      intro k hk
      have hgu1 : U' (X.ends D.gu).1 = U D.x := by
        rcases D.ju with h | h <;> rw [h]
        · exact U'uv _ (Or.inl rfl)
        · exact U'o _ D.hxu D.hxv
      rcases hk with rfl | ⟨d, rfl, hd, hdu, hdv⟩
      · rw [addEdge_ends_new, hgu1]
      · rw [addEdge_ends_old, ← U'o _ (fun h => hdu (Or.inl h)) (fun h => hdv (Or.inl h))]
        exact hG.2.1 U' hU' d D.gu hd D.hgu
    rw [key i hi, key j hj]
  · -- bridgeless
    intro e he B
    have sep := B.sep
    have hu := B.hu
    have hv := B.hv
    let V : Fin X.n → Bool := fun w => if w = D.u ∨ w = D.v then B.U D.x else B.U w
    have Vuv : ∀ w, (w = D.u ∨ w = D.v) → V w = B.U D.x := fun w hw => by simp [V, hw]
    have Vo : ∀ w, w ≠ D.u → w ≠ D.v → V w = B.U w := fun w h1 h2 => by simp [V, h1, h2]
    have pairV : ∀ d a b, X.Joins d a b → V a = V b → V (X.ends d).1 = V (X.ends d).2 := by
      intro d a b hj hab; rcases hj with h | h <;> rw [h]
      · exact hab
      · exact hab.symm
    have others : ∀ d, P d → ¬ X.Inc d D.u → ¬ X.Inc d D.v → Fin.castSucc d ≠ e →
        V (X.ends d).1 = V (X.ends d).2 := by
      intro d hd hdu hdv hne
      rw [Vo _ (fun h => hdu (Or.inl h)) (fun h => hdv (Or.inl h)),
        Vo _ (fun h => hdu (Or.inr h)) (fun h => hdv (Or.inr h))]
      have := sep _ (Or.inr ⟨d, rfl, hd, hdu, hdv⟩) hne; rwa [addEdge_ends_old] at this
    rcases he with rfl | ⟨d0, rfl, hd0, hd0u, hd0v⟩
    · -- `e = x y`: then `gv` is a bridge of `P`
      rw [addEdge_ends_new] at hu hv
      apply bridgeless_sep hG.2.2.1 D.hgv V
      · rcases D.jv with h | h <;> rw [h] <;> simp only [Vuv _ (Or.inr rfl), Vo _ D.hyu D.hyv, hu, hv] <;> decide
      · intro d hd hdg
        by_cases hdu : X.Inc d D.u
        · rcases D.covu d hd hdu with rfl | rfl | rfl
          · exact pairV _ _ _ D.j1 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.j2 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.ju (by rw [Vuv _ (Or.inl rfl), Vo _ D.hxu D.hxv])
        by_cases hdv : X.Inc d D.v
        · rcases D.covv d hd hdv with rfl | rfl | rfl
          · exact pairV _ _ _ D.j1 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.j2 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact absurd rfl hdg
        exact others d hd hdu hdv (castSucc_ne_last d)
    · -- `e` an old edge `d0`: then `d0` is a bridge of `P`
      rw [addEdge_ends_old] at hu hv
      have hxy : B.U D.x = B.U D.y := by
        have := sep _ (Or.inl rfl) (fun h => castSucc_ne_last d0 h.symm); rwa [addEdge_ends_new] at this
      apply bridgeless_sep hG.2.2.1 hd0 V
      · rw [Vo _ (fun h => hd0u (Or.inl h)) (fun h => hd0v (Or.inl h)),
          Vo _ (fun h => hd0u (Or.inr h)) (fun h => hd0v (Or.inr h)), hu, hv]; decide
      · intro d hd hdd
        by_cases hdu : X.Inc d D.u
        · rcases D.covu d hd hdu with rfl | rfl | rfl
          · exact pairV _ _ _ D.j1 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.j2 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.ju (by rw [Vuv _ (Or.inl rfl), Vo _ D.hxu D.hxv])
        by_cases hdv : X.Inc d D.v
        · rcases D.covv d hd hdv with rfl | rfl | rfl
          · exact pairV _ _ _ D.j1 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.j2 (by rw [Vuv _ (Or.inl rfl), Vuv _ (Or.inr rfl)])
          · exact pairV _ _ _ D.jv (by rw [Vuv _ (Or.inr rfl), Vo _ D.hyu D.hyv, hxy])
        exact others d hd hdu hdv (fun h => hdd (castSucc_inj' h))
  · -- cubic
    intro w hw
    obtain ⟨hwP, hwu, hwv⟩ := (D.meets_digP w).1 hw
    let φ : Fin X.m → Fin (addEdge X D.x D.y).m := fun d =>
      if d = D.gu ∨ d = D.gv then Fin.last X.m else Fin.castSucc d
    have φl : ∀ d, (d = D.gu ∨ d = D.gv) → φ d = Fin.last X.m := fun d h => by simp [φ, h]; rfl
    have φo : ∀ d, ¬ (d = D.gu ∨ d = D.gv) → φ d = Fin.castSucc d := fun d h => by simp [φ, h]; rfl
    apply cubic_at_of_map hG.2.2.2 hwP φ
    · intro d hd hdw
      rcases D.at_w hd hdw hwu hwv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hdu, hdv⟩
      · rw [φl _ (Or.inl rfl)]; exact ⟨Or.inl rfl, addEdge_inc_new.2 (Or.inl rfl)⟩
      · rw [φl _ (Or.inr rfl)]; exact ⟨Or.inl rfl, addEdge_inc_new.2 (Or.inr rfl)⟩
      · have hn : ¬ (d = D.gu ∨ d = D.gv) := by
          rintro (rfl | rfl)
          · exact hdu (joins_inc_left D.ju)
          · exact hdv (joins_inc_left D.jv)
        rw [φo _ hn]; exact ⟨Or.inr ⟨d, rfl, hd, hdu, hdv⟩, addEdge_inc_old.2 hdw⟩
    · have notg : ∀ d, ¬ X.Inc d D.u → ¬ X.Inc d D.v → ¬ (d = D.gu ∨ d = D.gv) := by
        intro d hdu hdv h
        rcases h with rfl | rfl
        · exact hdu (joins_inc_left D.ju)
        · exact hdv (joins_inc_left D.jv)
      intro d d' hd hd' hdw hd'w heq
      rcases D.at_w hd hdw hwu hwv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hdu, hdv⟩ <;>
        rcases D.at_w hd' hd'w hwu hwv with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨hdu', hdv'⟩
      · rfl
      · exact absurd h D.hxy
      · rw [φl _ (Or.inl rfl), φo _ (notg d' hdu' hdv')] at heq
        exact absurd heq.symm (castSucc_ne_last _)
      · exact absurd h.symm D.hxy
      · rfl
      · rw [φl _ (Or.inr rfl), φo _ (notg d' hdu' hdv')] at heq
        exact absurd heq.symm (castSucc_ne_last _)
      · rw [φl _ (Or.inl rfl), φo _ (notg d hdu hdv)] at heq
        exact absurd heq (castSucc_ne_last _)
      · rw [φl _ (Or.inr rfl), φo _ (notg d hdu hdv)] at heq
        exact absurd heq (castSucc_ne_last _)
      · rw [φo _ (notg d hdu hdv), φo _ (notg d' hdu' hdv')] at heq
        exact castSucc_inj' heq
    · intro j hj hjw
      rcases hj with rfl | ⟨d, rfl, hd, hdu, hdv⟩
      · rcases addEdge_inc_new.1 hjw with rfl | rfl
        · exact ⟨D.gu, D.hgu, joins_inc_right D.ju, φl _ (Or.inl rfl)⟩
        · exact ⟨D.gv, D.hgv, joins_inc_right D.jv, φl _ (Or.inr rfl)⟩
      · refine ⟨d, hd, addEdge_inc_old.1 hjw, φo _ ?_⟩
        rintro (rfl | rfl)
        · exact hdu (joins_inc_left D.ju)
        · exact hdv (joins_inc_left D.jv)

/-- **Lemma 2** (lifting): an isomorphism of the reduced graph onto `H` gives `P ≅ Sub(H, i)` -/
theorem lift {H : MGraph} (h : IsoFrom (digP P D.u D.v D.x D.y) H) : ∃ i, IsoFrom P (subG H i) := by
  obtain ⟨α', β', hα, hβ, hs, hj⟩ := h
  let i := β' (Fin.last X.m)
  have mdig : ∀ w, meets P w → w ≠ D.u → w ≠ D.v → @meets (addEdge X D.x D.y) (digP P D.u D.v D.x D.y) w :=
    fun w hw h1 h2 => (D.meets_digP w).2 ⟨hw, h1, h2⟩
  have pdig : ∀ f, P f → ¬ X.Inc f D.u → ¬ X.Inc f D.v → digP P D.u D.v D.x D.y (Fin.castSucc f) :=
    fun f hf h1 h2 => Or.inr ⟨f, rfl, hf, h1, h2⟩
  have ha : ∀ a b, meets P a → meets P b → a ≠ D.u → a ≠ D.v → b ≠ D.u → b ≠ D.v → α' a = α' b → a = b :=
    fun a b ha' hb' h1 h2 h3 h4 h => hα a b (mdig a ha' h1 h2) (mdig b hb' h3 h4) h
  have hb : ∀ f g, P f → P g → ¬ X.Inc f D.u → ¬ X.Inc f D.v → ¬ X.Inc g D.u → ¬ X.Inc g D.v →
      β' (Fin.castSucc f) = β' (Fin.castSucc g) → f = g :=
    fun f g hf hg h1 h2 h3 h4 h => castSucc_inj' (hβ _ _ (pdig f hf h1 h2) (pdig g hg h3 h4) h)
  have hbi : ∀ f, P f → ¬ X.Inc f D.u → ¬ X.Inc f D.v → β' (Fin.castSucc f) ≠ i :=
    fun f hf h1 h2 h => castSucc_ne_last f (hβ _ _ (pdig f hf h1 h2) (Or.inl rfl) h)
  have hsur : ∀ j, j ≠ i → ∃ f, P f ∧ ¬ X.Inc f D.u ∧ ¬ X.Inc f D.v ∧ β' (Fin.castSucc f) = j := by
    intro j hji
    obtain ⟨k, hk, rfl⟩ := hs j
    rcases hk with rfl | ⟨f, rfl, hf, h1, h2⟩
    · exact absurd rfl hji
    · exact ⟨f, hf, h1, h2, rfl⟩
  have hjo : ∀ f, P f → ¬ X.Inc f D.u → ¬ X.Inc f D.v →
      H.Joins (β' (Fin.castSucc f)) (α' (X.ends f).1) (α' (X.ends f).2) := by
    intro f hf h1 h2
    have := hj _ (pdig f hf h1 h2)
    rwa [addEdge_ends_old] at this
  have hji : H.Joins i (α' D.x) (α' D.y) := by
    have := hj _ (Or.inl rfl); rwa [addEdge_ends_new] at this
  rcases hji with hi | hi
  · exact ⟨i, subLift D.hd1 D.hd2 D.hgu D.hgv D.j1 D.j2 D.ju D.jv D.d12 D.covu D.covv D.huv D.hxu D.hxv D.hyu D.hyv
      α' (fun f => β' (Fin.castSucc f)) i ha hb hbi hsur hjo hi⟩
  · exact ⟨i, subLift D.hd1 D.hd2 D.hgv D.hgu (Or.symm D.j1) (Or.symm D.j2) D.jv D.ju D.d12 D.covv D.covu
      (Ne.symm D.huv) D.hyv D.hyu D.hxv D.hxu α' (fun f => β' (Fin.castSucc f)) i
      (fun a b ha' hb' h1 h2 h3 h4 h => ha a b ha' hb' h2 h1 h4 h3 h)
      (fun f g hf hg h1 h2 h3 h4 h => hb f g hf hg h2 h1 h4 h3 h)
      (fun f hf h1 h2 => hbi f hf h2 h1)
      (fun j hj' => by obtain ⟨f, hf, h1, h2, h3⟩ := hsur j hj'; exact ⟨f, hf, h2, h1, h3⟩)
      (fun f hf h1 h2 => hjo f hf h2 h1) hi⟩

end DigData

end dig

end RH2F

-- ===== from RH2Tri.lean =====
/-
  RH2Tri.lean — Lemma 3 of fact 7922314679f8733d (B8) in Lean 4.20 core: the triangle reduction `H ≅ Inf(K, t)`.
-/

namespace RH2F
open MGraph
open Classical

/-! ### ends of `Inf(H, s, i2, i3)` -/

section infends
variable (H : MGraph) (s : Fin H.n) (i2 i3 : Fin H.m)

def ie (e : Fin H.m) : Fin (infG H s i2 i3).m := Fin.castAdd 3 e
def im0 : Fin (infG H s i2 i3).m := ⟨H.m, by show H.m < H.m + 3; omega⟩
def im1 : Fin (infG H s i2 i3).m := ⟨H.m + 1, by show H.m + 1 < H.m + 3; omega⟩
def im2 : Fin (infG H s i2 i3).m := ⟨H.m + 2, by show H.m + 2 < H.m + 3; omega⟩

theorem infG_ends_i2 : (infG H s i2 i3).ends (ie H s i2 i3 i2) = repl H s (nv0 H) (H.ends i2) := by
  simp [infG, ie]

theorem infG_ends_i3 (h : i3 ≠ i2) : (infG H s i2 i3).ends (ie H s i2 i3 i3) = repl H s (nv1 H) (H.ends i3) := by
  have h' : i3.val ≠ i2.val := fun h'' => h (Fin.ext h'')
  simp [infG, ie, h']

theorem infG_ends_old {e : Fin H.m} (h2 : e ≠ i2) (h3 : e ≠ i3) :
    (infG H s i2 i3).ends (ie H s i2 i3 e) = (ov H (H.ends e).1, ov H (H.ends e).2) := by
  have h2' : e.val ≠ i2.val := fun h'' => h2 (Fin.ext h'')
  have h3' : e.val ≠ i3.val := fun h'' => h3 (Fin.ext h'')
  simp [infG, ie, h2', h3']

theorem infG_ends_m0 : (infG H s i2 i3).ends (im0 H s i2 i3) = (ov H s, nv0 H) := by simp [infG, im0]
theorem infG_ends_m1 : (infG H s i2 i3).ends (im1 H s i2 i3) = (nv0 H, nv1 H) := by
  simp [infG, im1]; intro h; exact absurd h (by omega)
theorem infG_ends_m2 : (infG H s i2 i3).ends (im2 H s i2 i3) = (ov H s, nv1 H) := by
  simp [infG, im2]; intro h; exact absurd h (by omega)

theorem inf_edge_cases (j : Fin (infG H s i2 i3).m) :
    (∃ e, j = ie H s i2 i3 e) ∨ j = im0 H s i2 i3 ∨ j = im1 H s i2 i3 ∨ j = im2 H s i2 i3 := by
  have hj : j.val < H.m + 3 := j.isLt
  by_cases h : j.val < H.m
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · by_cases h0 : j.val = H.m
    · exact Or.inr (Or.inl (Fin.ext h0))
    · by_cases h1 : j.val = H.m + 1
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h1)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by show j.val = H.m + 2; omega))))

theorem ie_inj {e e' : Fin H.m} (h : ie H s i2 i3 e = ie H s i2 i3 e') : e = e' := by
  have := congrArg Fin.val h; exact Fin.ext (by simpa [ie] using this)
theorem ie_ne_m0 (e : Fin H.m) : ie H s i2 i3 e ≠ im0 H s i2 i3 := fun h => by
  have := congrArg Fin.val h; simp [ie, im0] at this; omega
theorem ie_ne_m1 (e : Fin H.m) : ie H s i2 i3 e ≠ im1 H s i2 i3 := fun h => by
  have := congrArg Fin.val h; simp [ie, im1] at this; omega
theorem ie_ne_m2 (e : Fin H.m) : ie H s i2 i3 e ≠ im2 H s i2 i3 := fun h => by
  have := congrArg Fin.val h; simp [ie, im2] at this; omega
theorem im01 : im0 H s i2 i3 ≠ im1 H s i2 i3 := fun h => by have := congrArg Fin.val h; simp [im0, im1] at this
theorem im02 : im0 H s i2 i3 ≠ im2 H s i2 i3 := fun h => by have := congrArg Fin.val h; simp [im0, im2] at this
theorem im12 : im1 H s i2 i3 ≠ im2 H s i2 i3 := fun h => by have := congrArg Fin.val h; simp [im1, im2] at this

/-- `repl` on an edge joining `s` and `p ≠ s` -/
theorem repl_joins {e : Fin H.m} {p : Fin H.n} (hj : H.Joins e s p) (hp : p ≠ s) (N : Fin (H.n + 2)) :
    repl H s N (H.ends e) = (N, ov H p) ∨ repl H s N (H.ends e) = (ov H p, N) := by
  rcases hj with h | h <;> rw [h]
  · left; simp [repl, hp]
  · right; simp [repl, hp]

end infends

section tri
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `X` with a new vertex `t = Fin.last X.n` and new edges `t a'`, `t b'`, `t c'` (indices `m`, `m+1`, `m+2`) -/
def triG (X : MGraph) (a' b' c' : Fin X.n) : MGraph where
  n := X.n + 1
  m := X.m + 3
  ends := fun e =>
    if h : e.val < X.m then (Fin.castSucc (X.ends ⟨e.val, h⟩).1, Fin.castSucc (X.ends ⟨e.val, h⟩).2)
    else if e.val = X.m then (Fin.last X.n, Fin.castSucc a')
    else if e.val = X.m + 1 then (Fin.last X.n, Fin.castSucc b')
    else (Fin.last X.n, Fin.castSucc c')

section triends
variable (X) (a' b' c' : Fin X.n)
def te (d : Fin X.m) : Fin (triG X a' b' c').m := Fin.castAdd 3 d
def tm0 : Fin (triG X a' b' c').m := ⟨X.m, by show X.m < X.m + 3; omega⟩
def tm1 : Fin (triG X a' b' c').m := ⟨X.m + 1, by show X.m + 1 < X.m + 3; omega⟩
def tm2 : Fin (triG X a' b' c').m := ⟨X.m + 2, by show X.m + 2 < X.m + 3; omega⟩

theorem triG_ends_old (d : Fin X.m) :
    (triG X a' b' c').ends (te X a' b' c' d) = (Fin.castSucc (X.ends d).1, Fin.castSucc (X.ends d).2) := by
  simp [triG, te]
theorem triG_ends_m0 : (triG X a' b' c').ends (tm0 X a' b' c') = (Fin.last X.n, Fin.castSucc a') := by
  simp [triG, tm0]
theorem triG_ends_m1 : (triG X a' b' c').ends (tm1 X a' b' c') = (Fin.last X.n, Fin.castSucc b') := by
  simp [triG, tm1]; intro h; exact absurd h (by omega)
theorem triG_ends_m2 : (triG X a' b' c').ends (tm2 X a' b' c') = (Fin.last X.n, Fin.castSucc c') := by
  simp [triG, tm2]; intro h; exact absurd h (by omega)

theorem tri_edge_cases (j : Fin (triG X a' b' c').m) :
    (∃ d, j = te X a' b' c' d) ∨ j = tm0 X a' b' c' ∨ j = tm1 X a' b' c' ∨ j = tm2 X a' b' c' := by
  have hj : j.val < X.m + 3 := j.isLt
  by_cases h : j.val < X.m
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · by_cases h0 : j.val = X.m
    · exact Or.inr (Or.inl (Fin.ext h0))
    · by_cases h1 : j.val = X.m + 1
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h1)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by show j.val = X.m + 2; omega))))

theorem te_inj {d d' : Fin X.m} (h : te X a' b' c' d = te X a' b' c' d') : d = d' := by
  have := congrArg Fin.val h; exact Fin.ext (by simpa [te] using this)
theorem te_ne0 (d : Fin X.m) : te X a' b' c' d ≠ tm0 X a' b' c' := fun h => by
  have := congrArg Fin.val h; simp [te, tm0] at this; omega
theorem te_ne1 (d : Fin X.m) : te X a' b' c' d ≠ tm1 X a' b' c' := fun h => by
  have := congrArg Fin.val h; simp [te, tm1] at this; omega
theorem te_ne2 (d : Fin X.m) : te X a' b' c' d ≠ tm2 X a' b' c' := fun h => by
  have := congrArg Fin.val h; simp [te, tm2] at this; omega
theorem tm01 : tm0 X a' b' c' ≠ tm1 X a' b' c' := fun h => by have := congrArg Fin.val h; simp [tm0, tm1] at this
theorem tm02 : tm0 X a' b' c' ≠ tm2 X a' b' c' := fun h => by have := congrArg Fin.val h; simp [tm0, tm2] at this
theorem tm12 : tm1 X a' b' c' ≠ tm2 X a' b' c' := fun h => by have := congrArg Fin.val h; simp [tm1, tm2] at this
end triends

theorem castSucc_ne_lastV {n : Nat} (v : Fin n) : Fin.castSucc v ≠ Fin.last n := castSucc_ne_last v

/-- the reduced edge set of a triangle `a b c`: the edges avoiding `a, b, c` and the three new edges at `t` -/
def triP (P : Fin X.m → Prop) (a b c a' b' c' : Fin X.n) : Fin (triG X a' b' c').m → Prop :=
  fun i => i = tm0 X a' b' c' ∨ i = tm1 X a' b' c' ∨ i = tm2 X a' b' c' ∨
    ∃ d, i = te X a' b' c' d ∧ P d ∧ ¬ X.Inc d a ∧ ¬ X.Inc d b ∧ ¬ X.Inc d c

/-- the data of a triangle `a b c` of `P` with its outer edges `ea = a a'`, `eb = b b'`, `ec = c c'` -/
structure TriData (P : Fin X.m → Prop) where
  a : Fin X.n
  b : Fin X.n
  c : Fin X.n
  a' : Fin X.n
  b' : Fin X.n
  c' : Fin X.n
  ab : Fin X.m
  bc : Fin X.m
  ca : Fin X.m
  ea : Fin X.m
  eb : Fin X.m
  ec : Fin X.m
  hab : P ab
  hbc : P bc
  hca : P ca
  hea : P ea
  heb : P eb
  hec : P ec
  jab : X.Joins ab a b
  jbc : X.Joins bc b c
  jca : X.Joins ca c a
  jea : X.Joins ea a a'
  jeb : X.Joins eb b b'
  jec : X.Joins ec c c'
  cova : ∀ d, P d → X.Inc d a → d = ab ∨ d = ca ∨ d = ea
  covb : ∀ d, P d → X.Inc d b → d = ab ∨ d = bc ∨ d = eb
  covc : ∀ d, P d → X.Inc d c → d = bc ∨ d = ca ∨ d = ec
  a'a : a' ≠ a
  a'b : a' ≠ b
  a'c : a' ≠ c
  b'a : b' ≠ a
  b'b : b' ≠ b
  b'c : b' ≠ c
  c'a : c' ≠ a
  c'b : c' ≠ b
  c'c : c' ≠ c
  nab : a ≠ b
  nbc : b ≠ c
  nac : a ≠ c

/-- simple: two distinct edges of `P` never join the same two vertices -/
def SimpleP (P : Fin X.m → Prop) : Prop :=
  ∀ f g x y, P f → P g → X.Joins f x y → X.Joins g x y → f = g

/-- **Lemma 3** (data): a triangle of a simple member of 𝒢 -/
theorem triData_of (hG : InG X P) (hS : SimpleP P) {a b c : Fin X.n} {ab bc ca : Fin X.m}
    (hab : P ab) (hbc : P bc) (hca : P ca) (jab : X.Joins ab a b) (jbc : X.Joins bc b c) (jca : X.Joins ca c a) :
    ∃ T : TriData P, T.a = a ∧ T.b = b ∧ T.c = c := by
  have nab : a ≠ b := ne_of_joins hG.1 jab
  have nbc : b ≠ c := ne_of_joins hG.1 jbc
  have nac : a ≠ c := fun h => ne_of_joins hG.1 jca h.symm
  have abca : ab ≠ ca := by
    intro h; subst h
    rcases joins_unique jab jca with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact nac h1
    · exact nbc h2
  have abbc : ab ≠ bc := by
    intro h; subst h
    rcases joins_unique jab jbc with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact nab h1
    · exact nac h1
  have bcca : bc ≠ ca := by
    intro h; subst h
    rcases joins_unique jbc jca with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact nbc h1
    · exact nab h1.symm
  obtain ⟨ea, hea, iea, eaab, eaca, cova⟩ := third_edge hG.2.2.2 hab hca (joins_inc_left jab) (joins_inc_right jca) abca
  obtain ⟨eb, heb, ieb, ebab, ebbc, covb⟩ := third_edge hG.2.2.2 hab hbc (joins_inc_right jab) (joins_inc_left jbc) abbc
  obtain ⟨ec, hec, iec, ecbc, ecca, covc⟩ := third_edge hG.2.2.2 hbc hca (joins_inc_right jbc) (joins_inc_left jca) bcca
  obtain ⟨a', jea⟩ := joins_of_inc iea
  obtain ⟨b', jeb⟩ := joins_of_inc ieb
  obtain ⟨c', jec⟩ := joins_of_inc iec
  have a'a : a' ≠ a := fun h => ne_of_joins hG.1 jea h.symm
  have b'b : b' ≠ b := fun h => ne_of_joins hG.1 jeb h.symm
  have c'c : c' ≠ c := fun h => ne_of_joins hG.1 jec h.symm
  have a'b : a' ≠ b := fun h => eaab (hS _ _ _ _ hea hab (h ▸ jea) jab)
  have a'c : a' ≠ c := fun h => eaca (hS _ _ _ _ hea hca (h ▸ jea) (Or.symm jca))
  have b'a : b' ≠ a := fun h => ebab (hS _ _ _ _ heb hab (h ▸ jeb) (Or.symm jab))
  have b'c : b' ≠ c := fun h => ebbc (hS _ _ _ _ heb hbc (h ▸ jeb) jbc)
  have c'a : c' ≠ a := fun h => ecca (hS _ _ _ _ hec hca (h ▸ jec) jca)
  have c'b : c' ≠ b := fun h => ecbc (hS _ _ _ _ hec hbc (h ▸ jec) (Or.symm jbc))
  refine ⟨⟨a, b, c, a', b', c', ab, bc, ca, ea, eb, ec, hab, hbc, hca, hea, heb, hec, jab, jbc, jca, jea, jeb, jec,
    fun d hd hda => ?_, fun d hd hdb => ?_, fun d hd hdc => ?_, a'a, a'b, a'c, b'a, b'b, b'c, c'a, c'b, c'c,
    nab, nbc, nac⟩, rfl, rfl, rfl⟩
  · rcases cova d hd hda with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases covb d hd hdb with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases covc d hd hdc with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

namespace TriData
variable (T : TriData P)

/-- an edge of `P` at a vertex `w ∉ {a, b, c}` is an outer edge (then `w` is its outer end) or avoids `a, b, c` -/
theorem at_w {d : Fin X.m} {w : Fin X.n} (hd : P d) (hdw : X.Inc d w) (ha : w ≠ T.a) (hb : w ≠ T.b)
    (hc : w ≠ T.c) :
    (d = T.ea ∧ w = T.a') ∨ (d = T.eb ∧ w = T.b') ∨ (d = T.ec ∧ w = T.c') ∨
      (¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c) := by
  have tri : ∀ {e : Fin X.m} {p q : Fin X.n}, X.Joins e p q → X.Inc e w → p ≠ w → q ≠ w → False :=
    fun hj hw hp hq => by rcases inc_of_joins hj hw with h | h; exact hp h.symm; exact hq h.symm
  by_cases hda : X.Inc d T.a
  · rcases T.cova d hd hda with rfl | rfl | rfl
    · exact (tri T.jab hdw (Ne.symm ha) (Ne.symm hb)).elim
    · exact (tri T.jca hdw (Ne.symm hc) (Ne.symm ha)).elim
    · rcases inc_of_joins T.jea hdw with h | h
      · exact absurd h ha
      · exact Or.inl ⟨rfl, h⟩
  by_cases hdb : X.Inc d T.b
  · rcases T.covb d hd hdb with rfl | rfl | rfl
    · exact absurd (joins_inc_left T.jab) hda
    · exact (tri T.jbc hdw (Ne.symm hb) (Ne.symm hc)).elim
    · rcases inc_of_joins T.jeb hdw with h | h
      · exact absurd h hb
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
  by_cases hdc : X.Inc d T.c
  · rcases T.covc d hd hdc with rfl | rfl | rfl
    · exact absurd (joins_inc_left T.jbc) hdb
    · exact absurd (joins_inc_right T.jca) hda
    · rcases inc_of_joins T.jec hdw with h | h
      · exact absurd h hc
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
  exact Or.inr (Or.inr (Or.inr ⟨hda, hdb, hdc⟩))

theorem meets_triP_old (w : Fin X.n) :
    @meets (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c') (Fin.castSucc w) ↔
      meets P w ∧ w ≠ T.a ∧ w ≠ T.b ∧ w ≠ T.c := by
  have hla : ∀ z : Fin X.n, Fin.castSucc z ≠ Fin.last X.n := castSucc_ne_lastV
  constructor
  · rintro ⟨i, hi, hiw⟩
    rcases hi with rfl | rfl | rfl | ⟨d, rfl, hd, h1, h2, h3⟩
    · unfold Inc at hiw; rw [triG_ends_m0] at hiw
      rcases hiw with h | h
      · exact absurd h.symm (hla w)
      · have hw : w = T.a' := castSucc_inj' h.symm
        subst hw; exact ⟨⟨T.ea, T.hea, joins_inc_right T.jea⟩, T.a'a, T.a'b, T.a'c⟩
    · unfold Inc at hiw; rw [triG_ends_m1] at hiw
      rcases hiw with h | h
      · exact absurd h.symm (hla w)
      · have hw : w = T.b' := castSucc_inj' h.symm
        subst hw; exact ⟨⟨T.eb, T.heb, joins_inc_right T.jeb⟩, T.b'a, T.b'b, T.b'c⟩
    · unfold Inc at hiw; rw [triG_ends_m2] at hiw
      rcases hiw with h | h
      · exact absurd h.symm (hla w)
      · have hw : w = T.c' := castSucc_inj' h.symm
        subst hw; exact ⟨⟨T.ec, T.hec, joins_inc_right T.jec⟩, T.c'a, T.c'b, T.c'c⟩
    · unfold Inc at hiw; rw [triG_ends_old] at hiw
      have hdw : X.Inc d w := by
        rcases hiw with h | h
        · exact Or.inl (castSucc_inj' h)
        · exact Or.inr (castSucc_inj' h)
      exact ⟨⟨d, hd, hdw⟩, fun h => h1 (h ▸ hdw), fun h => h2 (h ▸ hdw), fun h => h3 (h ▸ hdw)⟩
  · rintro ⟨⟨d, hd, hdw⟩, ha, hb, hc⟩
    rcases T.at_w hd hdw ha hb hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h1, h2, h3⟩
    · exact ⟨_, Or.inl rfl, by unfold Inc; rw [triG_ends_m0]; exact Or.inr rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by unfold Inc; rw [triG_ends_m1]; exact Or.inr rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by unfold Inc; rw [triG_ends_m2]; exact Or.inr rfl⟩
    · refine ⟨_, Or.inr (Or.inr (Or.inr ⟨d, rfl, hd, h1, h2, h3⟩)), ?_⟩
      unfold Inc; rw [triG_ends_old]
      rcases hdw with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])

theorem meets_triP_last :
    @meets (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c') (Fin.last X.n) :=
  ⟨_, Or.inl rfl, by unfold Inc; rw [triG_ends_m0]; exact Or.inl rfl⟩

theorem vcount_triP : vcount (triP P T.a T.b T.c T.a' T.b' T.c') + 2 = vcount P := by
  unfold vcount
  have h1 := cntF_succ X.n (@meets (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c'))
  rw [if_pos T.meets_triP_last, cntF_congr X.n _ _ T.meets_triP_old] at h1
  refine (congrArg (· + 2) h1).trans ?_
  rw [cntF_split X.n (meets P) (fun w => w = T.a ∨ w = T.b ∨ w = T.c)]
  have hm : ∀ w, (w = T.a ∨ w = T.b ∨ w = T.c) → meets P w := by
    rintro w (rfl | rfl | rfl)
    · exact ⟨T.ab, T.hab, joins_inc_left T.jab⟩
    · exact ⟨T.ab, T.hab, joins_inc_right T.jab⟩
    · exact ⟨T.bc, T.hbc, joins_inc_right T.jbc⟩
  have h3 : cntF X.n (fun w => meets P w ∧ (w = T.a ∨ w = T.b ∨ w = T.c)) = 3 := by
    rw [cntF_congr X.n _ (fun w => w = T.a ∨ w = T.b ∨ w = T.c) (fun w => ⟨fun h => h.2, fun h => ⟨hm w h, h⟩⟩)]
    rw [cntF_split X.n _ (fun w => w = T.a)]
    rw [cntF_congr X.n (fun w => (w = T.a ∨ w = T.b ∨ w = T.c) ∧ w = T.a) (fun w => w = T.a)
      (fun w => ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩)]
    rw [cntF_congr X.n (fun w => (w = T.a ∨ w = T.b ∨ w = T.c) ∧ ¬ w = T.a) (fun w => w = T.b ∨ w = T.c)
      (fun w => ⟨fun h => h.1.resolve_left h.2, fun h => ⟨Or.inr h, fun h' => by
        rcases h with rfl | rfl
        · exact T.nab h'.symm
        · exact T.nac h'.symm⟩⟩)]
    rw [cntF_single, cntF_pair X.n T.nbc]
  rw [h3, cntF_congr X.n (fun w => meets P w ∧ w ≠ T.a ∧ w ≠ T.b ∧ w ≠ T.c)
    (fun w => meets P w ∧ ¬ (w = T.a ∨ w = T.b ∨ w = T.c)) (fun w => by simp only [not_or])]
  omega

theorem ea_ne_eb : T.ea ≠ T.eb := by
  intro h
  have := T.jeb; rw [← h] at this
  rcases inc_of_joins T.jea (joins_inc_left this) with h' | h'
  · exact T.nab h'.symm
  · exact T.a'b h'.symm
theorem ea_ne_ec : T.ea ≠ T.ec := by
  intro h
  have := T.jec; rw [← h] at this
  rcases inc_of_joins T.jea (joins_inc_left this) with h' | h'
  · exact T.nac h'.symm
  · exact T.a'c h'.symm
theorem eb_ne_ec : T.eb ≠ T.ec := by
  intro h
  have := T.jec; rw [← h] at this
  rcases inc_of_joins T.jeb (joins_inc_left this) with h' | h'
  · exact T.nbc h'.symm
  · exact T.b'c h'.symm

theorem inG_triP (hG : InG X P) : InG (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c') := by
  classical
  have hla : ∀ z : Fin X.n, Fin.castSucc z ≠ Fin.last X.n := castSucc_ne_lastV
  have tri3 : ∀ w, (w = T.a ∨ w = T.b ∨ w = T.c) → ∀ d, P d → X.Inc d w →
      d = T.ab ∨ d = T.bc ∨ d = T.ca ∨ d = T.ea ∨ d = T.eb ∨ d = T.ec := by
    rintro w (rfl | rfl | rfl) d hd hdw
    · rcases T.cova d hd hdw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases T.covb d hd hdw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases T.covc d hd hdw with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have atT : ∀ d, P d → ¬ (¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c) →
      d = T.ab ∨ d = T.bc ∨ d = T.ca ∨ d = T.ea ∨ d = T.eb ∨ d = T.ec := by
    intro d hd h
    by_cases ha : X.Inc d T.a
    · exact tri3 _ (Or.inl rfl) d hd ha
    by_cases hb : X.Inc d T.b
    · exact tri3 _ (Or.inr (Or.inl rfl)) d hd hb
    by_cases hc : X.Inc d T.c
    · exact tri3 _ (Or.inr (Or.inr rfl)) d hd hc
    exact absurd ⟨ha, hb, hc⟩ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- loopless
    intro e
    rcases tri_edge_cases X T.a' T.b' T.c' e with ⟨d, rfl⟩ | rfl | rfl | rfl
    · rw [triG_ends_old]; intro h; exact hG.1 d (castSucc_inj' h)
    · rw [triG_ends_m0]; exact fun h => hla _ h.symm
    · rw [triG_ends_m1]; exact fun h => hla _ h.symm
    · rw [triG_ends_m2]; exact fun h => hla _ h.symm
  · -- connected
    intro U hU i j hi hj
    have h0 : U (Fin.last X.n) = U (Fin.castSucc T.a') := by
      have := hU _ (Or.inl rfl); rwa [triG_ends_m0] at this
    have h1 : U (Fin.last X.n) = U (Fin.castSucc T.b') := by
      have := hU _ (Or.inr (Or.inl rfl)); rwa [triG_ends_m1] at this
    have h2 : U (Fin.last X.n) = U (Fin.castSucc T.c') := by
      have := hU _ (Or.inr (Or.inr (Or.inl rfl))); rwa [triG_ends_m2] at this
    let U' : Fin X.n → Bool := fun w => if w = T.a ∨ w = T.b ∨ w = T.c then U (Fin.last X.n) else U (Fin.castSucc w)
    have U'T : ∀ w, (w = T.a ∨ w = T.b ∨ w = T.c) → U' w = U (Fin.last X.n) := fun w h => by simp [U', h]
    have U'o : ∀ w, ¬ (w = T.a ∨ w = T.b ∨ w = T.c) → U' w = U (Fin.castSucc w) := fun w h => by simp [U', h]
    have pair : ∀ d a b, X.Joins d a b → U' a = U' b → U' (X.ends d).1 = U' (X.ends d).2 := by
      intro d a b hjd hab; rcases hjd with h | h <;> rw [h]
      · exact hab
      · exact hab.symm
    have hU' : ∀ d, P d → U' (X.ends d).1 = U' (X.ends d).2 := by
      intro d hd
      by_cases hin : ¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c
      · obtain ⟨ha, hb, hc⟩ := hin
        have n1 : ¬ ((X.ends d).1 = T.a ∨ (X.ends d).1 = T.b ∨ (X.ends d).1 = T.c) := by
          rintro (h | h | h)
          · exact ha (Or.inl h)
          · exact hb (Or.inl h)
          · exact hc (Or.inl h)
        have n2 : ¬ ((X.ends d).2 = T.a ∨ (X.ends d).2 = T.b ∨ (X.ends d).2 = T.c) := by
          rintro (h | h | h)
          · exact ha (Or.inr h)
          · exact hb (Or.inr h)
          · exact hc (Or.inr h)
        rw [U'o _ n1, U'o _ n2]
        have := hU _ (Or.inr (Or.inr (Or.inr ⟨d, rfl, hd, ha, hb, hc⟩))); rwa [triG_ends_old] at this
      · have tA : U' T.a = U (Fin.last X.n) := U'T _ (Or.inl rfl)
        have tB : U' T.b = U (Fin.last X.n) := U'T _ (Or.inr (Or.inl rfl))
        have tC : U' T.c = U (Fin.last X.n) := U'T _ (Or.inr (Or.inr rfl))
        rcases atT d hd hin with rfl | rfl | rfl | rfl | rfl | rfl
        · exact pair _ _ _ T.jab (by rw [tA, tB])
        · exact pair _ _ _ T.jbc (by rw [tB, tC])
        · exact pair _ _ _ T.jca (by rw [tC, tA])
        · exact pair _ _ _ T.jea (by rw [tA, U'o _ (by rintro (h | h | h); exact T.a'a h; exact T.a'b h
                                                       exact T.a'c h), h0])
        · exact pair _ _ _ T.jeb (by rw [tB, U'o _ (by rintro (h | h | h); exact T.b'a h; exact T.b'b h
                                                       exact T.b'c h), h1])
        · exact pair _ _ _ T.jec (by rw [tC, U'o _ (by rintro (h | h | h); exact T.c'a h; exact T.c'b h
                                                       exact T.c'c h), h2])
    have key : ∀ k, triP P T.a T.b T.c T.a' T.b' T.c' k →
        U ((triG X T.a' T.b' T.c').ends k).1 = U (Fin.last X.n) := by
      intro k hk
      rcases hk with rfl | rfl | rfl | ⟨d, rfl, hd, ha, hb, hc⟩
      · rw [triG_ends_m0]
      · rw [triG_ends_m1]
      · rw [triG_ends_m2]
      · rw [triG_ends_old]
        have n1 : ¬ ((X.ends d).1 = T.a ∨ (X.ends d).1 = T.b ∨ (X.ends d).1 = T.c) := by
          rintro (h | h | h)
          · exact ha (Or.inl h)
          · exact hb (Or.inl h)
          · exact hc (Or.inl h)
        rw [← U'o _ n1, hG.2.1 U' hU' d T.ab hd T.hab]
        rcases T.jab with h | h <;> rw [h]
        · exact U'T _ (Or.inl rfl)
        · exact U'T _ (Or.inr (Or.inl rfl))
    rw [key i hi, key j hj]
  · -- bridgeless
    intro e he B
    have sep := B.sep
    have hu := B.hu
    have hv := B.hv
    let V : Fin X.n → Bool := fun w =>
      if w = T.a ∨ w = T.b ∨ w = T.c then B.U (Fin.last X.n) else B.U (Fin.castSucc w)
    have VT : ∀ w, (w = T.a ∨ w = T.b ∨ w = T.c) → V w = B.U (Fin.last X.n) := fun w h => by simp [V, h]
    have Vo : ∀ w, ¬ (w = T.a ∨ w = T.b ∨ w = T.c) → V w = B.U (Fin.castSucc w) := fun w h => by simp [V, h]
    have na' : ¬ (T.a' = T.a ∨ T.a' = T.b ∨ T.a' = T.c) := by
      rintro (h | h | h)
      · exact T.a'a h
      · exact T.a'b h
      · exact T.a'c h
    have nb' : ¬ (T.b' = T.a ∨ T.b' = T.b ∨ T.b' = T.c) := by
      rintro (h | h | h)
      · exact T.b'a h
      · exact T.b'b h
      · exact T.b'c h
    have nc' : ¬ (T.c' = T.a ∨ T.c' = T.b ∨ T.c' = T.c) := by
      rintro (h | h | h)
      · exact T.c'a h
      · exact T.c'b h
      · exact T.c'c h
    have pairV : ∀ d a b, X.Joins d a b → V a = V b → V (X.ends d).1 = V (X.ends d).2 := by
      intro d a b hjd hab; rcases hjd with h | h <;> rw [h]
      · exact hab
      · exact hab.symm
    have tA : V T.a = B.U (Fin.last X.n) := VT _ (Or.inl rfl)
    have tB : V T.b = B.U (Fin.last X.n) := VT _ (Or.inr (Or.inl rfl))
    have tC : V T.c = B.U (Fin.last X.n) := VT _ (Or.inr (Or.inr rfl))
    have avoid : ∀ d, ¬ X.Inc d T.a → ¬ X.Inc d T.b → ¬ X.Inc d T.c →
        (¬ ((X.ends d).1 = T.a ∨ (X.ends d).1 = T.b ∨ (X.ends d).1 = T.c)) ∧
        (¬ ((X.ends d).2 = T.a ∨ (X.ends d).2 = T.b ∨ (X.ends d).2 = T.c)) := by
      intro d ha hb hc
      refine ⟨?_, ?_⟩ <;> rintro (h | h | h)
      · exact ha (Or.inl h)
      · exact hb (Or.inl h)
      · exact hc (Or.inl h)
      · exact ha (Or.inr h)
      · exact hb (Or.inr h)
      · exact hc (Or.inr h)
    have others : ∀ d, P d → ¬ X.Inc d T.a → ¬ X.Inc d T.b → ¬ X.Inc d T.c → te X T.a' T.b' T.c' d ≠ e →
        V (X.ends d).1 = V (X.ends d).2 := by
      intro d hd ha hb hc hne
      obtain ⟨n1, n2⟩ := avoid d ha hb hc
      rw [Vo _ n1, Vo _ n2]
      have := sep _ (Or.inr (Or.inr (Or.inr ⟨d, rfl, hd, ha, hb, hc⟩))) hne; rwa [triG_ends_old] at this
    -- the outer ends lie on the side of `t` unless the separated edge is theirs
    have outer : ∀ (k : Fin (triG X T.a' T.b' T.c').m) (z : Fin X.n),
        (triG X T.a' T.b' T.c').ends k = (Fin.last X.n, Fin.castSucc z) → triP P T.a T.b T.c T.a' T.b' T.c' k →
        k ≠ e → B.U (Fin.castSucc z) = B.U (Fin.last X.n) := by
      intro k z hk hkP hne
      have := sep k hkP hne; rw [hk] at this; exact this.symm
    -- the edges of `P` other than a chosen one do not cross `V`
    have noncross : ∀ (g : Fin X.m), P g → (∀ d, P d → d ≠ g → V (X.ends d).1 = V (X.ends d).2) →
        V (X.ends g).1 ≠ V (X.ends g).2 → False := fun g hg hsep hne =>
      bridgeless_sep hG.2.2.1 hg V hne (fun d hd hdg => hsep d hd hdg)
    rcases he with rfl | rfl | rfl | ⟨d0, rfl, hd0, h0a, h0b, h0c⟩
    · rw [triG_ends_m0] at hu hv
      have hb' := outer _ _ (triG_ends_m1 X T.a' T.b' T.c') (Or.inr (Or.inl rfl)) (tm01 X _ _ _).symm
      have hc' := outer _ _ (triG_ends_m2 X T.a' T.b' T.c') (Or.inr (Or.inr (Or.inl rfl))) (tm02 X _ _ _).symm
      apply noncross T.ea T.hea
      · intro d hd hde
        by_cases hin : ¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c
        · exact others d hd hin.1 hin.2.1 hin.2.2 (te_ne0 X _ _ _ d)
        · rcases atT d hd hin with rfl | rfl | rfl | rfl | rfl | rfl
          · exact pairV _ _ _ T.jab (by rw [tA, tB])
          · exact pairV _ _ _ T.jbc (by rw [tB, tC])
          · exact pairV _ _ _ T.jca (by rw [tC, tA])
          · exact absurd rfl hde
          · exact pairV _ _ _ T.jeb (by rw [tB, Vo _ nb', hb'])
          · exact pairV _ _ _ T.jec (by rw [tC, Vo _ nc', hc'])
      · rcases T.jea with h | h <;> rw [h] <;> simp only [tA, Vo _ na', hu, hv] <;> decide
    · rw [triG_ends_m1] at hu hv
      have ha' := outer _ _ (triG_ends_m0 X T.a' T.b' T.c') (Or.inl rfl) (tm01 X _ _ _)
      have hc' := outer _ _ (triG_ends_m2 X T.a' T.b' T.c') (Or.inr (Or.inr (Or.inl rfl))) (tm12 X _ _ _).symm
      apply noncross T.eb T.heb
      · intro d hd hde
        by_cases hin : ¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c
        · exact others d hd hin.1 hin.2.1 hin.2.2 (te_ne1 X _ _ _ d)
        · rcases atT d hd hin with rfl | rfl | rfl | rfl | rfl | rfl
          · exact pairV _ _ _ T.jab (by rw [tA, tB])
          · exact pairV _ _ _ T.jbc (by rw [tB, tC])
          · exact pairV _ _ _ T.jca (by rw [tC, tA])
          · exact pairV _ _ _ T.jea (by rw [tA, Vo _ na', ha'])
          · exact absurd rfl hde
          · exact pairV _ _ _ T.jec (by rw [tC, Vo _ nc', hc'])
      · rcases T.jeb with h | h <;> rw [h] <;> simp only [tB, Vo _ nb', hu, hv] <;> decide
    · rw [triG_ends_m2] at hu hv
      have ha' := outer _ _ (triG_ends_m0 X T.a' T.b' T.c') (Or.inl rfl) (tm02 X _ _ _)
      have hb' := outer _ _ (triG_ends_m1 X T.a' T.b' T.c') (Or.inr (Or.inl rfl)) (tm12 X _ _ _)
      apply noncross T.ec T.hec
      · intro d hd hde
        by_cases hin : ¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c
        · exact others d hd hin.1 hin.2.1 hin.2.2 (te_ne2 X _ _ _ d)
        · rcases atT d hd hin with rfl | rfl | rfl | rfl | rfl | rfl
          · exact pairV _ _ _ T.jab (by rw [tA, tB])
          · exact pairV _ _ _ T.jbc (by rw [tB, tC])
          · exact pairV _ _ _ T.jca (by rw [tC, tA])
          · exact pairV _ _ _ T.jea (by rw [tA, Vo _ na', ha'])
          · exact pairV _ _ _ T.jeb (by rw [tB, Vo _ nb', hb'])
          · exact absurd rfl hde
      · rcases T.jec with h | h <;> rw [h] <;> simp only [tC, Vo _ nc', hu, hv] <;> decide
    · rw [triG_ends_old] at hu hv
      have ha' := outer _ _ (triG_ends_m0 X T.a' T.b' T.c') (Or.inl rfl) (te_ne0 X _ _ _ d0).symm
      have hb' := outer _ _ (triG_ends_m1 X T.a' T.b' T.c') (Or.inr (Or.inl rfl)) (te_ne1 X _ _ _ d0).symm
      have hc' := outer _ _ (triG_ends_m2 X T.a' T.b' T.c') (Or.inr (Or.inr (Or.inl rfl))) (te_ne2 X _ _ _ d0).symm
      apply noncross d0 hd0
      · intro d hd hde
        by_cases hin : ¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c
        · exact others d hd hin.1 hin.2.1 hin.2.2 (fun h => hde (te_inj X _ _ _ h))
        · rcases atT d hd hin with rfl | rfl | rfl | rfl | rfl | rfl
          · exact pairV _ _ _ T.jab (by rw [tA, tB])
          · exact pairV _ _ _ T.jbc (by rw [tB, tC])
          · exact pairV _ _ _ T.jca (by rw [tC, tA])
          · exact pairV _ _ _ T.jea (by rw [tA, Vo _ na', ha'])
          · exact pairV _ _ _ T.jeb (by rw [tB, Vo _ nb', hb'])
          · exact pairV _ _ _ T.jec (by rw [tC, Vo _ nc', hc'])
      · obtain ⟨n1, n2⟩ := avoid d0 h0a h0b h0c
        rw [Vo _ n1, Vo _ n2, hu, hv]; decide
  · -- cubic
    intro w' hw'
    by_cases hwl : w' = Fin.last X.n
    · subst hwl
      refine ⟨tm0 X T.a' T.b' T.c', tm1 X T.a' T.b' T.c', tm2 X T.a' T.b' T.c', Or.inl rfl, Or.inr (Or.inl rfl),
        Or.inr (Or.inr (Or.inl rfl)), ?_, ?_, ?_, tm01 X _ _ _, tm02 X _ _ _, tm12 X _ _ _, ?_⟩
      · unfold Inc; rw [triG_ends_m0]; exact Or.inl rfl
      · unfold Inc; rw [triG_ends_m1]; exact Or.inl rfl
      · unfold Inc; rw [triG_ends_m2]; exact Or.inl rfl
      · intro j hj hjl
        rcases hj with h | h | h | ⟨d, rfl, _, _, _, _⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exfalso; unfold Inc at hjl; rw [triG_ends_old] at hjl
          rcases hjl with h | h
          · exact hla _ h
          · exact hla _ h
    · -- an old vertex
      obtain ⟨w, rfl⟩ : ∃ w : Fin X.n, w' = Fin.castSucc w := by
        refine ⟨⟨w'.val, ?_⟩, Fin.ext rfl⟩
        have h1 : w'.val < X.n + 1 := w'.isLt
        have hne : w'.val ≠ X.n := fun h => hwl (Fin.ext h)
        omega
      obtain ⟨hwP, ha, hb, hc⟩ := (T.meets_triP_old w).1 hw'
      let φ : Fin X.m → Fin (triG X T.a' T.b' T.c').m := fun d =>
        if d = T.ea then tm0 X T.a' T.b' T.c' else if d = T.eb then tm1 X T.a' T.b' T.c'
        else if d = T.ec then tm2 X T.a' T.b' T.c' else te X T.a' T.b' T.c' d
      have φa : φ T.ea = tm0 X T.a' T.b' T.c' := by simp [φ]
      have φb : φ T.eb = tm1 X T.a' T.b' T.c' := by simp [φ, Ne.symm T.ea_ne_eb]
      have φc : φ T.ec = tm2 X T.a' T.b' T.c' := by simp [φ, Ne.symm T.ea_ne_ec, Ne.symm T.eb_ne_ec]
      have φo : ∀ d, d ≠ T.ea → d ≠ T.eb → d ≠ T.ec → φ d = te X T.a' T.b' T.c' d := fun d h1 h2 h3 => by
        simp [φ, h1, h2, h3]
      have awayE : ∀ d, ¬ X.Inc d T.a → ¬ X.Inc d T.b → ¬ X.Inc d T.c → d ≠ T.ea ∧ d ≠ T.eb ∧ d ≠ T.ec :=
        fun d ha' hb' hc' => ⟨fun h => ha' (h ▸ joins_inc_left T.jea), fun h => hb' (h ▸ joins_inc_left T.jeb),
          fun h => hc' (h ▸ joins_inc_left T.jec)⟩
      apply cubic_at_of_map hG.2.2.2 hwP φ
      · intro d hd hdw
        rcases T.at_w hd hdw ha hb hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩
        · rw [φa]; exact ⟨Or.inl rfl, by unfold Inc; rw [triG_ends_m0]; exact Or.inr rfl⟩
        · rw [φb]; exact ⟨Or.inr (Or.inl rfl), by unfold Inc; rw [triG_ends_m1]; exact Or.inr rfl⟩
        · rw [φc]; exact ⟨Or.inr (Or.inr (Or.inl rfl)), by unfold Inc; rw [triG_ends_m2]; exact Or.inr rfl⟩
        · obtain ⟨n1, n2, n3⟩ := awayE d h1 h2 h3
          rw [φo d n1 n2 n3]
          refine ⟨Or.inr (Or.inr (Or.inr ⟨d, rfl, hd, h1, h2, h3⟩)), ?_⟩
          unfold Inc; rw [triG_ends_old]
          rcases hdw with h | h
          · exact Or.inl (by rw [h]; first | done | rfl)
          · exact Or.inr (by rw [h])
      · intro d d' hd hd' hdw hd'w heq
        have cls : ∀ g, P g → X.Inc g w → (g = T.ea ∧ φ g = tm0 X T.a' T.b' T.c') ∨
            (g = T.eb ∧ φ g = tm1 X T.a' T.b' T.c') ∨ (g = T.ec ∧ φ g = tm2 X T.a' T.b' T.c') ∨
            φ g = te X T.a' T.b' T.c' g := by
          intro g hg hgw
          rcases T.at_w hg hgw ha hb hc with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨rfl, φa⟩
          · exact Or.inr (Or.inl ⟨rfl, φb⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, φc⟩))
          · obtain ⟨n1, n2, n3⟩ := awayE g h1 h2 h3
            exact Or.inr (Or.inr (Or.inr (φo g n1 n2 n3)))
        rcases cls d hd hdw with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | e1 <;>
          rcases cls d' hd' hd'w with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | e2 <;>
          first
          | rfl
          | (rw [e1, e2] at heq; first
            | exact absurd heq (tm01 X _ _ _) | exact absurd heq (tm02 X _ _ _) | exact absurd heq (tm12 X _ _ _)
            | exact absurd heq.symm (tm01 X _ _ _) | exact absurd heq.symm (tm02 X _ _ _)
            | exact absurd heq.symm (tm12 X _ _ _)
            | exact absurd heq (te_ne0 X _ _ _ _).symm | exact absurd heq (te_ne1 X _ _ _ _).symm
            | exact absurd heq (te_ne2 X _ _ _ _).symm
            | exact absurd heq (te_ne0 X _ _ _ _) | exact absurd heq (te_ne1 X _ _ _ _)
            | exact absurd heq (te_ne2 X _ _ _ _)
            | exact te_inj X _ _ _ heq)
      · intro j hj hjw
        unfold Inc at hjw
        rcases hj with rfl | rfl | rfl | ⟨d, rfl, hd, h1, h2, h3⟩
        · rw [triG_ends_m0] at hjw
          rcases hjw with h | h
          · exact absurd h.symm (hla w)
          · have := castSucc_inj' h; subst this
            exact ⟨T.ea, T.hea, joins_inc_right T.jea, φa⟩
        · rw [triG_ends_m1] at hjw
          rcases hjw with h | h
          · exact absurd h.symm (hla w)
          · have := castSucc_inj' h; subst this
            exact ⟨T.eb, T.heb, joins_inc_right T.jeb, φb⟩
        · rw [triG_ends_m2] at hjw
          rcases hjw with h | h
          · exact absurd h.symm (hla w)
          · have := castSucc_inj' h; subst this
            exact ⟨T.ec, T.hec, joins_inc_right T.jec, φc⟩
        · rw [triG_ends_old] at hjw
          obtain ⟨n1, n2, n3⟩ := awayE d h1 h2 h3
          refine ⟨d, hd, ?_, φo d n1 n2 n3⟩
          rcases hjw with h | h
          · exact Or.inl (castSucc_inj' h)
          · exact Or.inr (castSucc_inj' h)

/-- **Lemma 3** (lifting): an isomorphism of the reduced graph onto `H` gives `P ≅ Inf(H, s, i2, i3)` for the image
    `s` of `t` and two distinct edges `i2`, `i3` at `s` -/
theorem lift {H : MGraph} (h : IsoFrom (triP P T.a T.b T.c T.a' T.b' T.c') H) :
    ∃ s i2 i3, i2 ≠ i3 ∧ H.Inc i2 s ∧ H.Inc i3 s ∧ IsoFrom P (infG H s i2 i3) := by
  classical
  obtain ⟨α', β', hα, hβ, hs, hj⟩ := h
  have hla : ∀ z : Fin X.n, Fin.castSucc z ≠ Fin.last X.n := castSucc_ne_lastV
  let s := α' (Fin.last X.n)
  let i1 := β' (tm0 X T.a' T.b' T.c')
  let i2 := β' (tm1 X T.a' T.b' T.c')
  let i3 := β' (tm2 X T.a' T.b' T.c')
  have tP0 : triP P T.a T.b T.c T.a' T.b' T.c' (tm0 X T.a' T.b' T.c') := Or.inl rfl
  have tP1 : triP P T.a T.b T.c T.a' T.b' T.c' (tm1 X T.a' T.b' T.c') := Or.inr (Or.inl rfl)
  have tP2 : triP P T.a T.b T.c T.a' T.b' T.c' (tm2 X T.a' T.b' T.c') := Or.inr (Or.inr (Or.inl rfl))
  have i12 : i1 ≠ i2 := fun h => tm01 X _ _ _ (hβ _ _ tP0 tP1 h)
  have i13 : i1 ≠ i3 := fun h => tm02 X _ _ _ (hβ _ _ tP0 tP2 h)
  have i23 : i2 ≠ i3 := fun h => tm12 X _ _ _ (hβ _ _ tP1 tP2 h)
  have ml : @meets (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c') (Fin.last X.n) := T.meets_triP_last
  have mo : ∀ w, meets P w → w ≠ T.a → w ≠ T.b → w ≠ T.c →
      @meets (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c') (Fin.castSucc w) :=
    fun w hw h1 h2 h3 => (T.meets_triP_old w).2 ⟨hw, h1, h2, h3⟩
  have mA : meets P T.a' := ⟨T.ea, T.hea, joins_inc_right T.jea⟩
  have mB : meets P T.b' := ⟨T.eb, T.heb, joins_inc_right T.jeb⟩
  have mC : meets P T.c' := ⟨T.ec, T.hec, joins_inc_right T.jec⟩
  have sne : ∀ w, meets P w → w ≠ T.a → w ≠ T.b → w ≠ T.c → α' (Fin.castSucc w) ≠ s :=
    fun w hw h1 h2 h3 h => hla w (hα _ _ (mo w hw h1 h2 h3) ml h)
  have j0 : H.Joins i1 s (α' (Fin.castSucc T.a')) := by
    have := hj _ tP0; rwa [triG_ends_m0] at this
  have j1' : H.Joins i2 s (α' (Fin.castSucc T.b')) := by
    have := hj _ tP1; rwa [triG_ends_m1] at this
  have j2' : H.Joins i3 s (α' (Fin.castSucc T.c')) := by
    have := hj _ tP2; rwa [triG_ends_m2] at this
  refine ⟨s, i2, i3, i23, joins_inc_left j1', joins_inc_left j2', ?_⟩
  -- the maps
  let α : Fin X.n → Fin (infG H s i2 i3).n := fun w =>
    if w = T.a then ov H s else if w = T.b then nv0 H else if w = T.c then nv1 H else ov H (α' (Fin.castSucc w))
  let β : Fin X.m → Fin (infG H s i2 i3).m := fun d =>
    if d = T.ab then im0 H s i2 i3 else if d = T.bc then im1 H s i2 i3 else if d = T.ca then im2 H s i2 i3
    else if d = T.ea then ie H s i2 i3 i1 else if d = T.eb then ie H s i2 i3 i2
    else if d = T.ec then ie H s i2 i3 i3 else ie H s i2 i3 (β' (te X T.a' T.b' T.c' d))
  have αa : α T.a = ov H s := by simp [α]; rfl
  have αb : α T.b = nv0 H := by simp [α, Ne.symm T.nab]; rfl
  have αc : α T.c = nv1 H := by simp [α, Ne.symm T.nac, Ne.symm T.nbc]; rfl
  have αo : ∀ w, w ≠ T.a → w ≠ T.b → w ≠ T.c → α w = ov H (α' (Fin.castSucc w)) := fun w h1 h2 h3 => by
    simp [α, h1, h2, h3]; rfl
  -- distinctness of the six special edges
  have e_ab_bc : T.ab ≠ T.bc := by
    intro h; have := T.jbc; rw [← h] at this
    rcases joins_unique T.jab this with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact T.nab h1
    · exact T.nac h1
  have e_ab_ca : T.ab ≠ T.ca := by
    intro h; have := T.jca; rw [← h] at this
    rcases joins_unique T.jab this with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact T.nac h1
    · exact T.nbc h2
  have e_bc_ca : T.bc ≠ T.ca := by
    intro h; have := T.jca; rw [← h] at this
    rcases joins_unique T.jbc this with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact T.nbc h1
    · exact T.nab h1.symm
  have tri_ne_e : ∀ d, (d = T.ab ∨ d = T.bc ∨ d = T.ca) → d ≠ T.ea ∧ d ≠ T.eb ∧ d ≠ T.ec := by
    have nf : ∀ {e f : Fin X.m} {p q r z : Fin X.n}, X.Joins e p q → X.Joins f r z → p ≠ r → p ≠ z → e ≠ f :=
      fun he hf hpr hpz h => by
        subst h; rcases inc_of_joins hf (joins_inc_left he) with h' | h'
        · exact hpr h'
        · exact hpz h'
    rintro d (rfl | rfl | rfl)
    · exact ⟨nf (Or.symm T.jab) T.jea (Ne.symm T.nab) (Ne.symm T.a'b), nf T.jab T.jeb T.nab (Ne.symm T.b'a),
        nf T.jab T.jec T.nac (Ne.symm T.c'a)⟩
    · exact ⟨nf T.jbc T.jea (Ne.symm T.nab) (Ne.symm T.a'b), nf (Or.symm T.jbc) T.jeb (Ne.symm T.nbc) (Ne.symm T.b'c),
        nf T.jbc T.jec T.nbc (Ne.symm T.c'b)⟩
    · exact ⟨nf T.jca T.jea (Ne.symm T.nac) (Ne.symm T.a'c), nf T.jca T.jeb T.nbc.symm (Ne.symm T.b'c),
        nf (Or.symm T.jca) T.jec T.nac (Ne.symm T.c'a)⟩
  have βab : β T.ab = im0 H s i2 i3 := by simp [β]
  have βbc : β T.bc = im1 H s i2 i3 := by simp [β, Ne.symm e_ab_bc]
  have βca : β T.ca = im2 H s i2 i3 := by simp [β, Ne.symm e_ab_ca, Ne.symm e_bc_ca]
  obtain ⟨ab_ea, ab_eb, ab_ec⟩ := tri_ne_e _ (Or.inl rfl)
  obtain ⟨bc_ea, bc_eb, bc_ec⟩ := tri_ne_e _ (Or.inr (Or.inl rfl))
  obtain ⟨ca_ea, ca_eb, ca_ec⟩ := tri_ne_e _ (Or.inr (Or.inr rfl))
  have βea : β T.ea = ie H s i2 i3 i1 := by
    simp only [β, if_neg (Ne.symm ab_ea), if_neg (Ne.symm bc_ea), if_neg (Ne.symm ca_ea), if_pos rfl, ↓reduceIte]
  have βeb : β T.eb = ie H s i2 i3 i2 := by
    simp only [β, if_neg (Ne.symm ab_eb), if_neg (Ne.symm bc_eb), if_neg (Ne.symm ca_eb),
      if_neg (Ne.symm T.ea_ne_eb), if_pos rfl, ↓reduceIte]
  have βec : β T.ec = ie H s i2 i3 i3 := by
    simp only [β, if_neg (Ne.symm ab_ec), if_neg (Ne.symm bc_ec), if_neg (Ne.symm ca_ec),
      if_neg (Ne.symm T.ea_ne_ec), if_neg (Ne.symm T.eb_ne_ec), if_pos rfl, ↓reduceIte]
  have βo : ∀ d, ¬ X.Inc d T.a → ¬ X.Inc d T.b → ¬ X.Inc d T.c →
      β d = ie H s i2 i3 (β' (te X T.a' T.b' T.c' d)) := by
    intro d ha hb hc
    have n1 : d ≠ T.ab := fun h => ha (h ▸ joins_inc_left T.jab)
    have n2 : d ≠ T.bc := fun h => hb (h ▸ joins_inc_left T.jbc)
    have n3 : d ≠ T.ca := fun h => hc (h ▸ joins_inc_left T.jca)
    have n4 : d ≠ T.ea := fun h => ha (h ▸ joins_inc_left T.jea)
    have n5 : d ≠ T.eb := fun h => hb (h ▸ joins_inc_left T.jeb)
    have n6 : d ≠ T.ec := fun h => hc (h ▸ joins_inc_left T.jec)
    simp only [β, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]
  -- classification of vertices and edges of `P`
  have vcls : ∀ w, meets P w → (w = T.a ∧ α w = ov H s) ∨ (w = T.b ∧ α w = nv0 H) ∨ (w = T.c ∧ α w = nv1 H) ∨
      (w ≠ T.a ∧ w ≠ T.b ∧ w ≠ T.c ∧ α w = ov H (α' (Fin.castSucc w)) ∧ α' (Fin.castSucc w) ≠ s) := by
    intro w hw
    by_cases h1 : w = T.a
    · exact Or.inl ⟨h1, h1 ▸ αa⟩
    by_cases h2 : w = T.b
    · exact Or.inr (Or.inl ⟨h2, h2 ▸ αb⟩)
    by_cases h3 : w = T.c
    · exact Or.inr (Or.inr (Or.inl ⟨h3, h3 ▸ αc⟩))
    exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, αo w h1 h2 h3, sne w hw h1 h2 h3⟩))
  have awayT : ∀ d, P d → ¬ (d = T.ab ∨ d = T.bc ∨ d = T.ca ∨ d = T.ea ∨ d = T.eb ∨ d = T.ec) →
      ¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c := by
    intro d hd hn
    refine ⟨fun h => hn ?_, fun h => hn ?_, fun h => hn ?_⟩
    · rcases T.cova d hd h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · rcases T.covb d hd h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · rcases T.covc d hd h with h' | h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
  have teP : ∀ d, P d → ¬ X.Inc d T.a → ¬ X.Inc d T.b → ¬ X.Inc d T.c →
      triP P T.a T.b T.c T.a' T.b' T.c' (te X T.a' T.b' T.c' d) :=
    fun d hd h1 h2 h3 => Or.inr (Or.inr (Or.inr ⟨d, rfl, hd, h1, h2, h3⟩))
  have ecls : ∀ d, P d → (d = T.ab ∧ β d = im0 H s i2 i3) ∨ (d = T.bc ∧ β d = im1 H s i2 i3) ∨
      (d = T.ca ∧ β d = im2 H s i2 i3) ∨ (d = T.ea ∧ β d = ie H s i2 i3 i1) ∨ (d = T.eb ∧ β d = ie H s i2 i3 i2) ∨
      (d = T.ec ∧ β d = ie H s i2 i3 i3) ∨
      (¬ X.Inc d T.a ∧ ¬ X.Inc d T.b ∧ ¬ X.Inc d T.c ∧ β d = ie H s i2 i3 (β' (te X T.a' T.b' T.c' d)) ∧
        β' (te X T.a' T.b' T.c' d) ≠ i1 ∧ β' (te X T.a' T.b' T.c' d) ≠ i2 ∧ β' (te X T.a' T.b' T.c' d) ≠ i3) := by
    intro d hd
    by_cases h1 : d = T.ab
    · exact Or.inl ⟨h1, h1 ▸ βab⟩
    by_cases h2 : d = T.bc
    · exact Or.inr (Or.inl ⟨h2, h2 ▸ βbc⟩)
    by_cases h3 : d = T.ca
    · exact Or.inr (Or.inr (Or.inl ⟨h3, h3 ▸ βca⟩))
    by_cases h4 : d = T.ea
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, h4 ▸ βea⟩)))
    by_cases h5 : d = T.eb
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, h5 ▸ βeb⟩))))
    by_cases h6 : d = T.ec
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, h6 ▸ βec⟩)))))
    obtain ⟨ha, hb, hc⟩ := awayT d hd (by
      rintro (h | h | h | h | h | h)
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact h4 h
      · exact h5 h
      · exact h6 h)
    have tP := teP d hd ha hb hc
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, βo d ha hb hc,
      fun h => te_ne0 X _ _ _ d (hβ _ _ tP tP0 h), fun h => te_ne1 X _ _ _ d (hβ _ _ tP tP1 h),
      fun h => te_ne2 X _ _ _ d (hβ _ _ tP tP2 h)⟩)))))
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · -- `α` is injective on the vertices of `P`
    intro x y hx hy hxy
    rcases vcls x hx with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨x1, x2, x3, e1, n1⟩ <;>
    rcases vcls y hy with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨y1, y2, y3, e2, n2⟩ <;>
    first
    | rfl
    | (rw [e1, e2] at hxy; first
      | exact absurd hxy (ov_ne0 H _) | exact absurd hxy (ov_ne1 H _) | exact absurd hxy.symm (ov_ne0 H _)
      | exact absurd hxy.symm (ov_ne1 H _) | exact absurd hxy (nv01 H) | exact absurd hxy.symm (nv01 H)
      | exact absurd (ov_inj H hxy).symm n2 | exact absurd (ov_inj H hxy) n1
      | exact castSucc_inj' (hα _ _ (mo x hx x1 x2 x3) (mo y hy y1 y2 y3) (ov_inj H hxy)))
  · -- `β` is injective on `P`
    intro f g hf hg hfg
    rcases ecls f hf with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ |
        ⟨fa, fb, fc, e1, f1, f2, f3⟩ <;>
    rcases ecls g hg with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨rfl, e2⟩ |
        ⟨ga, gb, gc, e2, g1, g2, g3⟩ <;>
    first
    | rfl
    | (rw [e1, e2] at hfg; first
      | exact absurd hfg (im01 H s i2 i3) | exact absurd hfg (im02 H s i2 i3) | exact absurd hfg (im12 H s i2 i3)
      | exact absurd hfg.symm (im01 H s i2 i3) | exact absurd hfg.symm (im02 H s i2 i3)
      | exact absurd hfg.symm (im12 H s i2 i3)
      | exact absurd hfg (ie_ne_m0 H s i2 i3 _).symm | exact absurd hfg (ie_ne_m1 H s i2 i3 _).symm
      | exact absurd hfg (ie_ne_m2 H s i2 i3 _).symm
      | exact absurd hfg (ie_ne_m0 H s i2 i3 _) | exact absurd hfg (ie_ne_m1 H s i2 i3 _)
      | exact absurd hfg (ie_ne_m2 H s i2 i3 _)
      | exact absurd (ie_inj H s i2 i3 hfg) i12 | exact absurd (ie_inj H s i2 i3 hfg) i13
      | exact absurd (ie_inj H s i2 i3 hfg) i23
      | exact absurd (ie_inj H s i2 i3 hfg).symm i12 | exact absurd (ie_inj H s i2 i3 hfg).symm i13
      | exact absurd (ie_inj H s i2 i3 hfg).symm i23
      | exact absurd (ie_inj H s i2 i3 hfg).symm g1 | exact absurd (ie_inj H s i2 i3 hfg).symm g2
      | exact absurd (ie_inj H s i2 i3 hfg).symm g3
      | exact absurd (ie_inj H s i2 i3 hfg) f1 | exact absurd (ie_inj H s i2 i3 hfg) f2
      | exact absurd (ie_inj H s i2 i3 hfg) f3
      | exact te_inj X _ _ _ (hβ _ _ (teP f hf fa fb fc) (teP g hg ga gb gc) (ie_inj H s i2 i3 hfg)))
  · -- `β` is onto the edges of `Inf(H, s, i2, i3)`
    intro j
    rcases inf_edge_cases H s i2 i3 j with ⟨e, rfl⟩ | rfl | rfl | rfl
    · by_cases h1 : e = i1
      · exact ⟨T.ea, T.hea, h1 ▸ βea⟩
      by_cases h2 : e = i2
      · exact ⟨T.eb, T.heb, h2 ▸ βeb⟩
      by_cases h3 : e = i3
      · exact ⟨T.ec, T.hec, h3 ▸ βec⟩
      obtain ⟨k, hk, rfl⟩ := hs e
      rcases hk with rfl | rfl | rfl | ⟨d, rfl, hd, ha, hb, hc⟩
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact absurd rfl h3
      · exact ⟨d, hd, βo d ha hb hc⟩
    · exact ⟨T.ab, T.hab, βab⟩
    · exact ⟨T.bc, T.hbc, βbc⟩
    · exact ⟨T.ca, T.hca, βca⟩
  · -- incidences
    have nA : ¬ (T.a' = T.a) ∧ ¬ (T.a' = T.b) ∧ ¬ (T.a' = T.c) := ⟨T.a'a, T.a'b, T.a'c⟩
    have nB : ¬ (T.b' = T.a) ∧ ¬ (T.b' = T.b) ∧ ¬ (T.b' = T.c) := ⟨T.b'a, T.b'b, T.b'c⟩
    have nC : ¬ (T.c' = T.a) ∧ ¬ (T.c' = T.b) ∧ ¬ (T.c' = T.c) := ⟨T.c'a, T.c'b, T.c'c⟩
    intro f hf
    rcases ecls f hf with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨rfl, e1⟩ |
        ⟨fa, fb, fc, e1, f1, f2, f3⟩ <;> rw [e1]
    · apply joins_ends_of T.jab; rw [αa, αb]; exact Or.inl (infG_ends_m0 H s i2 i3)
    · apply joins_ends_of T.jbc; rw [αb, αc]; exact Or.inl (infG_ends_m1 H s i2 i3)
    · apply joins_ends_of T.jca; rw [αc, αa]; exact Or.inr (infG_ends_m2 H s i2 i3)
    · apply joins_ends_of T.jea
      rw [αa, αo _ nA.1 nA.2.1 nA.2.2]
      rw [show (infG H s i2 i3).Joins (ie H s i2 i3 i1) (ov H s) (ov H (α' (Fin.castSucc T.a'))) ↔
          H.Joins i1 s (α' (Fin.castSucc T.a')) from by
        unfold Joins; rw [infG_ends_old H s i2 i3 i12 i13]
        constructor
        · rintro (h | h)
          · exact Or.inl (Prod.ext (ov_inj H (congrArg Prod.fst h)) (ov_inj H (congrArg Prod.snd h)))
          · exact Or.inr (Prod.ext (ov_inj H (congrArg Prod.fst h)) (ov_inj H (congrArg Prod.snd h)))
        · rintro (h | h)
          · exact Or.inl (by rw [h]; first | done | rfl)
          · exact Or.inr (by rw [h]; rfl)]
      exact j0
    · apply joins_ends_of T.jeb
      rw [αb, αo _ nB.1 nB.2.1 nB.2.2]
      have hne := sne T.b' mB nB.1 nB.2.1 nB.2.2
      rcases repl_joins H s j1' hne (nv0 H) with h | h
      · exact Or.inl (by rw [infG_ends_i2, h]; rfl)
      · exact Or.inr (by rw [infG_ends_i2, h]; rfl)
    · apply joins_ends_of T.jec
      rw [αc, αo _ nC.1 nC.2.1 nC.2.2]
      have hne := sne T.c' mC nC.1 nC.2.1 nC.2.2
      rcases repl_joins H s j2' hne (nv1 H) with h | h
      · exact Or.inl (by rw [infG_ends_i3 H s i2 i3 (Ne.symm i23), h]; rfl)
      · exact Or.inr (by rw [infG_ends_i3 H s i2 i3 (Ne.symm i23), h]; rfl)
    · have n1 : ¬ ((X.ends f).1 = T.a) ∧ ¬ ((X.ends f).1 = T.b) ∧ ¬ ((X.ends f).1 = T.c) :=
        ⟨fun h => fa (Or.inl h), fun h => fb (Or.inl h), fun h => fc (Or.inl h)⟩
      have n2 : ¬ ((X.ends f).2 = T.a) ∧ ¬ ((X.ends f).2 = T.b) ∧ ¬ ((X.ends f).2 = T.c) :=
        ⟨fun h => fa (Or.inr h), fun h => fb (Or.inr h), fun h => fc (Or.inr h)⟩
      rw [αo _ n1.1 n1.2.1 n1.2.2, αo _ n2.1 n2.2.1 n2.2.2]
      have hjf := hj _ (teP f hf fa fb fc)
      rw [triG_ends_old] at hjf
      rcases hjf with h | h
      · exact Or.inl (by rw [infG_ends_old H s i2 i3 f2 f3, h]; rfl)
      · exact Or.inr (by rw [infG_ends_old H s i2 i3 f2 f3, h]; rfl)

end TriData

end tri

end RH2F

-- ===== from RH2ClsData.lean =====
/-
  RH2ClsData.lean — the concrete part of §4 of fact 7922314679f8733d (B8): every `Sub(Rep_j, i)` and every
  `Inf(Rep_j, s, i2, i3)` (all orderings of the edges at `s`) of a representative with at most 6 vertices is isomorphic
  to a representative with two more vertices, or (for `Inf`) has two parallel edges.  Data generated by
  workers/lean/rh2/cls/gen2.py; checked by `decide +kernel`.
-/

namespace RH2F
open MGraph

theorem repM_pos (k : Nat) : 0 < (repG k).m := by
  show 0 < (repL k).length
  unfold repL; split <;> decide

/-- the target and the isomorphism data of `Sub(Rep_j, i)` -/
def subD : Nat → Nat → Nat × List Nat × List Nat
  | 1, 0 => (2, [0, 1, 2, 3], [2, 0, 1, 3, 4, 5])
  | 1, 1 => (2, [0, 1, 2, 3], [0, 2, 1, 3, 4, 5])
  | 1, 2 => (2, [0, 1, 2, 3], [0, 1, 2, 3, 4, 5])
  | 2, 0 => (5, [0, 1, 2, 3, 4, 5], [5, 0, 1, 2, 3, 4, 6, 7, 8])
  | 2, 1 => (5, [0, 1, 2, 3, 4, 5], [0, 5, 1, 2, 3, 4, 6, 7, 8])
  | 2, 2 => (4, [0, 1, 2, 3, 4, 5], [0, 1, 5, 2, 3, 4, 6, 7, 8])
  | 2, 3 => (5, [2, 3, 0, 1, 4, 5], [2, 3, 1, 5, 0, 4, 6, 7, 8])
  | 2, 4 => (5, [2, 3, 0, 1, 4, 5], [2, 3, 1, 0, 5, 4, 6, 7, 8])
  | 2, 5 => (4, [0, 1, 4, 5, 2, 3], [0, 1, 5, 6, 7, 8, 2, 3, 4])
  | 3, 0 => (6, [0, 1, 2, 3, 4, 5], [5, 0, 1, 2, 3, 4, 6, 7, 8])
  | 3, 1 => (6, [2, 0, 1, 3, 5, 4], [2, 8, 4, 0, 1, 3, 6, 7, 5])
  | 3, 2 => (6, [2, 0, 3, 1, 5, 4], [2, 4, 8, 3, 1, 0, 6, 7, 5])
  | 3, 3 => (6, [0, 2, 1, 3, 4, 5], [2, 0, 3, 5, 1, 4, 6, 7, 8])
  | 3, 4 => (6, [2, 3, 0, 1, 4, 5], [3, 4, 1, 2, 5, 0, 6, 7, 8])
  | 3, 5 => (6, [0, 2, 3, 1, 4, 5], [2, 3, 0, 4, 1, 5, 6, 7, 8])
  | 4, 0 => (9, [0, 1, 2, 3, 4, 5, 6, 7], [8, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 4, 1 => (9, [0, 1, 2, 3, 4, 5, 6, 7], [0, 8, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 4, 2 => (9, [2, 3, 0, 1, 5, 4, 6, 7], [1, 2, 8, 0, 3, 7, 5, 6, 4, 9, 10, 11])
  | 4, 3 => (9, [2, 3, 0, 1, 5, 4, 6, 7], [1, 2, 0, 8, 3, 7, 5, 6, 4, 9, 10, 11])
  | 4, 4 => (10, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 8, 4, 5, 6, 7, 9, 10, 11])
  | 4, 5 => (10, [0, 1, 6, 7, 2, 3, 4, 5], [0, 1, 9, 10, 11, 4, 2, 3, 8, 5, 6, 7])
  | 4, 6 => (9, [3, 2, 4, 5, 1, 0, 7, 6], [1, 2, 5, 6, 7, 3, 11, 0, 4, 9, 10, 8])
  | 4, 7 => (9, [3, 2, 4, 5, 1, 0, 7, 6], [1, 2, 5, 6, 7, 3, 0, 11, 4, 9, 10, 8])
  | 4, 8 => (10, [0, 1, 6, 7, 4, 5, 2, 3], [0, 1, 9, 10, 11, 4, 5, 6, 7, 2, 3, 8])
  | 5, 0 => (11, [0, 1, 2, 3, 4, 5, 6, 7], [8, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 5, 1 => (9, [0, 1, 2, 3, 6, 7, 4, 5], [0, 4, 1, 2, 3, 8, 9, 10, 11, 5, 6, 7])
  | 5, 2 => (13, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 8, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 5, 3 => (13, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 8, 3, 4, 5, 6, 7, 9, 10, 11])
  | 5, 4 => (9, [0, 1, 4, 5, 6, 7, 2, 3], [0, 4, 5, 6, 7, 8, 9, 10, 11, 1, 2, 3])
  | 5, 5 => (9, [0, 1, 6, 7, 2, 3, 4, 5], [0, 8, 9, 10, 11, 4, 1, 2, 3, 5, 6, 7])
  | 5, 6 => (13, [0, 1, 4, 5, 2, 3, 6, 7], [0, 4, 5, 6, 7, 1, 8, 2, 3, 9, 10, 11])
  | 5, 7 => (13, [0, 1, 4, 5, 2, 3, 6, 7], [0, 4, 5, 6, 7, 1, 2, 8, 3, 9, 10, 11])
  | 5, 8 => (9, [0, 1, 6, 7, 4, 5, 2, 3], [0, 8, 9, 10, 11, 4, 5, 6, 7, 1, 2, 3])
  | 6, 0 => (17, [1, 0, 2, 3, 5, 4, 7, 6], [11, 3, 0, 2, 1, 7, 5, 6, 4, 9, 10, 8])
  | 6, 1 => (17, [1, 0, 3, 2, 5, 4, 7, 6], [3, 11, 1, 2, 0, 7, 5, 6, 4, 9, 10, 8])
  | 6, 2 => (17, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 8, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 6, 3 => (16, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 8, 3, 4, 5, 6, 7, 9, 10, 11])
  | 6, 4 => (17, [0, 1, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 8, 4, 5, 6, 7, 9, 10, 11])
  | 6, 5 => (14, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11])
  | 6, 6 => (15, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 8, 6, 7, 9, 10, 11])
  | 6, 7 => (15, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11])
  | 6, 8 => (14, [0, 1, 2, 3, 6, 7, 4, 5], [0, 1, 2, 3, 4, 8, 9, 10, 11, 5, 6, 7])
  | 7, 0 => (20, [0, 1, 2, 3, 4, 5, 6, 7], [8, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 7, 1 => (19, [0, 1, 2, 3, 4, 5, 6, 7], [0, 8, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 7, 2 => (19, [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 8, 4, 3, 2, 7, 6, 5, 9, 10, 11])
  | 7, 3 => (20, [2, 4, 0, 5, 1, 3, 7, 6], [2, 5, 6, 11, 7, 4, 0, 1, 3, 9, 10, 8])
  | 7, 4 => (19, [5, 3, 1, 2, 0, 4, 7, 6], [4, 1, 3, 0, 11, 2, 7, 5, 6, 9, 10, 8])
  | 7, 5 => (20, [2, 4, 5, 0, 3, 1, 7, 6], [2, 6, 5, 4, 7, 11, 3, 1, 0, 9, 10, 8])
  | 7, 6 => (19, [1, 0, 4, 5, 2, 3, 7, 6], [0, 5, 7, 2, 6, 4, 11, 3, 1, 9, 10, 8])
  | 7, 7 => (19, [3, 5, 0, 4, 1, 2, 7, 6], [4, 7, 6, 0, 5, 2, 1, 11, 3, 9, 10, 8])
  | 7, 8 => (19, [1, 0, 5, 4, 3, 2, 7, 6], [0, 7, 5, 4, 6, 2, 1, 3, 11, 9, 10, 8])
  | 8, 0 => (22, [0, 1, 2, 3, 4, 5, 6, 7], [8, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11])
  | 8, 1 => (22, [0, 1, 2, 4, 3, 5, 6, 7], [0, 8, 1, 3, 2, 4, 6, 5, 7, 9, 10, 11])
  | 8, 2 => (22, [0, 1, 2, 4, 5, 3, 6, 7], [0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11])
  | 8, 3 => (22, [1, 0, 2, 3, 4, 5, 6, 7], [2, 3, 4, 8, 0, 1, 5, 6, 7, 9, 10, 11])
  | 8, 4 => (22, [1, 0, 2, 4, 3, 5, 6, 7], [3, 2, 4, 0, 8, 1, 6, 5, 7, 9, 10, 11])
  | 8, 5 => (22, [1, 0, 2, 4, 5, 3, 6, 7], [3, 4, 2, 0, 1, 8, 6, 7, 5, 9, 10, 11])
  | 8, 6 => (22, [1, 2, 0, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6, 7, 8, 0, 1, 9, 10, 11])
  | 8, 7 => (22, [1, 2, 0, 4, 3, 5, 6, 7], [3, 2, 4, 6, 5, 7, 0, 8, 1, 9, 10, 11])
  | 8, 8 => (22, [1, 2, 0, 4, 5, 3, 6, 7], [3, 4, 2, 6, 7, 5, 0, 1, 8, 9, 10, 11])
  | _, _ => (1, [], [])

/-- the target (0: two parallel edges) and the data of `Inf(Rep_j, s, i2, i3)` -/
def infD : Nat → Nat → Nat → Nat → Nat × List Nat × List Nat
  | 1, 0, 0, 1 => (3, [0, 1, 2, 3], [1, 2, 0, 3, 4, 5])
  | 1, 0, 0, 2 => (3, [0, 1, 2, 3], [1, 0, 2, 3, 4, 5])
  | 1, 0, 1, 0 => (3, [0, 1, 2, 3], [2, 1, 0, 3, 4, 5])
  | 1, 0, 1, 2 => (3, [0, 1, 2, 3], [0, 1, 2, 3, 4, 5])
  | 1, 0, 2, 0 => (3, [0, 1, 2, 3], [2, 0, 1, 3, 4, 5])
  | 1, 0, 2, 1 => (3, [0, 1, 2, 3], [0, 2, 1, 3, 4, 5])
  | 1, 1, 0, 1 => (3, [0, 1, 2, 3], [3, 5, 0, 1, 4, 2])
  | 1, 1, 0, 2 => (3, [0, 1, 2, 3], [3, 0, 5, 1, 4, 2])
  | 1, 1, 1, 0 => (3, [0, 1, 2, 3], [5, 3, 0, 1, 4, 2])
  | 1, 1, 1, 2 => (3, [0, 1, 2, 3], [0, 3, 5, 1, 4, 2])
  | 1, 1, 2, 0 => (3, [0, 1, 2, 3], [5, 0, 3, 1, 4, 2])
  | 1, 1, 2, 1 => (3, [0, 1, 2, 3], [0, 5, 3, 1, 4, 2])
  | 2, 0, 0, 1 => (0, [3, 4], [])
  | 2, 0, 0, 2 => (0, [3, 4], [])
  | 2, 0, 1, 0 => (0, [3, 4], [])
  | 2, 0, 1, 2 => (0, [3, 4], [])
  | 2, 0, 2, 0 => (0, [3, 4], [])
  | 2, 0, 2, 1 => (0, [3, 4], [])
  | 2, 1, 0, 1 => (0, [3, 4], [])
  | 2, 1, 0, 5 => (0, [3, 4], [])
  | 2, 1, 1, 0 => (0, [3, 4], [])
  | 2, 1, 1, 5 => (0, [3, 4], [])
  | 2, 1, 5, 0 => (0, [3, 4], [])
  | 2, 1, 5, 1 => (0, [3, 4], [])
  | 2, 2, 2, 3 => (0, [0, 1], [])
  | 2, 2, 2, 4 => (0, [0, 1], [])
  | 2, 2, 3, 2 => (0, [0, 1], [])
  | 2, 2, 3, 4 => (0, [0, 1], [])
  | 2, 2, 4, 2 => (0, [0, 1], [])
  | 2, 2, 4, 3 => (0, [0, 1], [])
  | 2, 3, 3, 4 => (0, [0, 1], [])
  | 2, 3, 3, 5 => (0, [0, 1], [])
  | 2, 3, 4, 3 => (0, [0, 1], [])
  | 2, 3, 4, 5 => (0, [0, 1], [])
  | 2, 3, 5, 3 => (0, [0, 1], [])
  | 2, 3, 5, 4 => (0, [0, 1], [])
  | 3, 0, 0, 3 => (7, [0, 2, 3, 1, 4, 5], [3, 4, 1, 5, 2, 0, 6, 7, 8])
  | 3, 0, 0, 5 => (7, [0, 2, 1, 3, 4, 5], [3, 1, 4, 0, 2, 5, 6, 7, 8])
  | 3, 0, 3, 0 => (7, [0, 2, 3, 1, 5, 4], [3, 4, 1, 5, 2, 0, 8, 7, 6])
  | 3, 0, 3, 5 => (7, [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7, 8])
  | 3, 0, 5, 0 => (7, [0, 2, 1, 3, 5, 4], [3, 1, 4, 0, 2, 5, 8, 7, 6])
  | 3, 0, 5, 3 => (7, [0, 1, 2, 3, 5, 4], [0, 1, 2, 3, 4, 5, 8, 7, 6])
  | 3, 1, 0, 1 => (7, [0, 2, 5, 4, 1, 3], [0, 5, 3, 8, 7, 6, 1, 2, 4])
  | 3, 1, 0, 2 => (7, [0, 2, 4, 5, 1, 3], [0, 3, 5, 6, 7, 8, 1, 2, 4])
  | 3, 1, 1, 0 => (7, [0, 2, 5, 4, 3, 1], [0, 5, 3, 8, 7, 6, 4, 2, 1])
  | 3, 1, 1, 2 => (7, [0, 1, 4, 5, 2, 3], [0, 3, 5, 6, 7, 8, 1, 4, 2])
  | 3, 1, 2, 0 => (7, [0, 2, 4, 5, 3, 1], [0, 3, 5, 6, 7, 8, 4, 2, 1])
  | 3, 1, 2, 1 => (7, [0, 1, 4, 5, 3, 2], [0, 3, 5, 6, 7, 8, 2, 4, 1])
  | 3, 2, 1, 3 => (7, [0, 4, 3, 5, 2, 1], [6, 3, 7, 0, 5, 8, 4, 1, 2])
  | 3, 2, 1, 4 => (7, [0, 4, 1, 5, 2, 3], [6, 3, 7, 0, 5, 8, 1, 4, 2])
  | 3, 2, 3, 1 => (7, [0, 4, 3, 5, 1, 2], [6, 3, 7, 0, 5, 8, 2, 1, 4])
  | 3, 2, 3, 4 => (7, [0, 4, 2, 5, 1, 3], [6, 3, 7, 0, 5, 8, 1, 2, 4])
  | 3, 2, 4, 1 => (7, [0, 4, 1, 5, 3, 2], [6, 3, 7, 0, 5, 8, 2, 4, 1])
  | 3, 2, 4, 3 => (7, [0, 4, 2, 5, 3, 1], [6, 3, 7, 0, 5, 8, 4, 2, 1])
  | 3, 3, 2, 4 => (7, [0, 4, 5, 1, 2, 3], [6, 7, 3, 8, 5, 0, 1, 4, 2])
  | 3, 3, 2, 5 => (7, [0, 4, 5, 3, 2, 1], [6, 7, 3, 8, 5, 0, 4, 1, 2])
  | 3, 3, 4, 2 => (7, [0, 4, 5, 1, 3, 2], [6, 7, 3, 8, 5, 0, 2, 4, 1])
  | 3, 3, 4, 5 => (7, [0, 4, 5, 2, 3, 1], [6, 7, 3, 8, 5, 0, 4, 2, 1])
  | 3, 3, 5, 2 => (7, [0, 4, 5, 3, 1, 2], [6, 7, 3, 8, 5, 0, 2, 1, 4])
  | 3, 3, 5, 4 => (7, [0, 4, 5, 2, 1, 3], [6, 7, 3, 8, 5, 0, 1, 2, 4])
  | 4, 0, 0, 1 => (0, [2, 3], [])
  | 4, 0, 0, 5 => (0, [2, 3], [])
  | 4, 0, 1, 0 => (0, [2, 3], [])
  | 4, 0, 1, 5 => (0, [2, 3], [])
  | 4, 0, 5, 0 => (0, [2, 3], [])
  | 4, 0, 5, 1 => (0, [2, 3], [])
  | 4, 1, 0, 1 => (0, [2, 3], [])
  | 4, 1, 0, 4 => (0, [2, 3], [])
  | 4, 1, 1, 0 => (0, [2, 3], [])
  | 4, 1, 1, 4 => (0, [2, 3], [])
  | 4, 1, 4, 0 => (0, [2, 3], [])
  | 4, 1, 4, 1 => (0, [2, 3], [])
  | 4, 2, 2, 3 => (0, [0, 1], [])
  | 4, 2, 2, 8 => (0, [0, 1], [])
  | 4, 2, 3, 2 => (0, [0, 1], [])
  | 4, 2, 3, 8 => (0, [0, 1], [])
  | 4, 2, 8, 2 => (0, [0, 1], [])
  | 4, 2, 8, 3 => (0, [0, 1], [])
  | 4, 3, 2, 3 => (0, [0, 1], [])
  | 4, 3, 2, 4 => (0, [0, 1], [])
  | 4, 3, 3, 2 => (0, [0, 1], [])
  | 4, 3, 3, 4 => (0, [0, 1], [])
  | 4, 3, 4, 2 => (0, [0, 1], [])
  | 4, 3, 4, 3 => (0, [0, 1], [])
  | 4, 4, 5, 6 => (0, [0, 1], [])
  | 4, 4, 5, 7 => (0, [0, 1], [])
  | 4, 4, 6, 5 => (0, [0, 1], [])
  | 4, 4, 6, 7 => (0, [0, 1], [])
  | 4, 4, 7, 5 => (0, [0, 1], [])
  | 4, 4, 7, 6 => (0, [0, 1], [])
  | 4, 5, 6, 7 => (0, [0, 1], [])
  | 4, 5, 6, 8 => (0, [0, 1], [])
  | 4, 5, 7, 6 => (0, [0, 1], [])
  | 4, 5, 7, 8 => (0, [0, 1], [])
  | 4, 5, 8, 6 => (0, [0, 1], [])
  | 4, 5, 8, 7 => (0, [0, 1], [])
  | 5, 0, 0, 1 => (0, [2, 3], [])
  | 5, 0, 0, 5 => (0, [2, 3], [])
  | 5, 0, 1, 0 => (0, [2, 3], [])
  | 5, 0, 1, 5 => (0, [2, 3], [])
  | 5, 0, 5, 0 => (0, [2, 3], [])
  | 5, 0, 5, 1 => (0, [2, 3], [])
  | 5, 1, 0, 4 => (0, [2, 3], [])
  | 5, 1, 0, 8 => (0, [2, 3], [])
  | 5, 1, 4, 0 => (0, [2, 3], [])
  | 5, 1, 4, 8 => (0, [2, 3], [])
  | 5, 1, 8, 0 => (0, [2, 3], [])
  | 5, 1, 8, 4 => (0, [2, 3], [])
  | 5, 2, 1, 2 => (0, [6, 7], [])
  | 5, 2, 1, 3 => (0, [6, 7], [])
  | 5, 2, 2, 1 => (0, [6, 7], [])
  | 5, 2, 2, 3 => (0, [6, 7], [])
  | 5, 2, 3, 1 => (0, [6, 7], [])
  | 5, 2, 3, 2 => (0, [6, 7], [])
  | 5, 3, 2, 3 => (0, [6, 7], [])
  | 5, 3, 2, 4 => (0, [6, 7], [])
  | 5, 3, 3, 2 => (0, [6, 7], [])
  | 5, 3, 3, 4 => (0, [6, 7], [])
  | 5, 3, 4, 2 => (0, [6, 7], [])
  | 5, 3, 4, 3 => (0, [6, 7], [])
  | 5, 4, 5, 6 => (0, [2, 3], [])
  | 5, 4, 5, 7 => (0, [2, 3], [])
  | 5, 4, 6, 5 => (0, [2, 3], [])
  | 5, 4, 6, 7 => (0, [2, 3], [])
  | 5, 4, 7, 5 => (0, [2, 3], [])
  | 5, 4, 7, 6 => (0, [2, 3], [])
  | 5, 5, 6, 7 => (0, [2, 3], [])
  | 5, 5, 6, 8 => (0, [2, 3], [])
  | 5, 5, 7, 6 => (0, [2, 3], [])
  | 5, 5, 7, 8 => (0, [2, 3], [])
  | 5, 5, 8, 6 => (0, [2, 3], [])
  | 5, 5, 8, 7 => (0, [2, 3], [])
  | 6, 0, 2, 4 => (0, [6, 7], [])
  | 6, 0, 2, 5 => (0, [6, 7], [])
  | 6, 0, 4, 2 => (0, [6, 7], [])
  | 6, 0, 4, 5 => (0, [6, 7], [])
  | 6, 0, 5, 2 => (0, [6, 7], [])
  | 6, 0, 5, 4 => (0, [6, 7], [])
  | 6, 1, 0, 1 => (0, [6, 7], [])
  | 6, 1, 0, 8 => (0, [6, 7], [])
  | 6, 1, 1, 0 => (0, [6, 7], [])
  | 6, 1, 1, 8 => (0, [6, 7], [])
  | 6, 1, 8, 0 => (0, [6, 7], [])
  | 6, 1, 8, 1 => (0, [6, 7], [])
  | 6, 2, 0, 2 => (0, [6, 7], [])
  | 6, 2, 0, 3 => (0, [6, 7], [])
  | 6, 2, 2, 0 => (0, [6, 7], [])
  | 6, 2, 2, 3 => (0, [6, 7], [])
  | 6, 2, 3, 0 => (0, [6, 7], [])
  | 6, 2, 3, 2 => (0, [6, 7], [])
  | 6, 3, 1, 3 => (0, [6, 7], [])
  | 6, 3, 1, 4 => (0, [6, 7], [])
  | 6, 3, 3, 1 => (0, [6, 7], [])
  | 6, 3, 3, 4 => (0, [6, 7], [])
  | 6, 3, 4, 1 => (0, [6, 7], [])
  | 6, 3, 4, 3 => (0, [6, 7], [])
  | 6, 4, 5, 6 => (18, [0, 1, 2, 3, 6, 5, 4, 7], [0, 1, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10])
  | 6, 4, 5, 7 => (18, [0, 1, 2, 3, 6, 5, 4, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10])
  | 6, 4, 6, 5 => (18, [0, 1, 2, 3, 6, 5, 7, 4], [0, 1, 2, 3, 4, 5, 7, 6, 8, 10, 11, 9])
  | 6, 4, 6, 7 => (18, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
  | 6, 4, 7, 5 => (18, [0, 1, 2, 3, 6, 5, 7, 4], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 9])
  | 6, 4, 7, 6 => (18, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11])
  | 6, 5, 6, 7 => (18, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 9, 11, 8, 6, 10, 7])
  | 6, 5, 6, 8 => (18, [0, 1, 2, 3, 4, 6, 7, 5], [0, 1, 2, 3, 4, 5, 11, 9, 8, 10, 7, 6])
  | 6, 5, 7, 6 => (18, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 11, 9, 8, 6, 10, 7])
  | 6, 5, 7, 8 => (18, [0, 1, 2, 3, 4, 6, 7, 5], [0, 1, 2, 3, 4, 5, 9, 11, 8, 10, 7, 6])
  | 6, 5, 8, 6 => (18, [0, 1, 2, 3, 4, 6, 5, 7], [0, 1, 2, 3, 4, 5, 11, 9, 8, 6, 7, 10])
  | 6, 5, 8, 7 => (18, [0, 1, 2, 3, 4, 6, 5, 7], [0, 1, 2, 3, 4, 5, 9, 11, 8, 6, 7, 10])
  | 7, 0, 0, 6 => (21, [2, 0, 7, 6, 5, 4, 1, 3], [0, 11, 9, 8, 10, 6, 5, 7, 3, 1, 2, 4])
  | 7, 0, 0, 8 => (21, [2, 0, 6, 7, 4, 5, 1, 3], [0, 9, 11, 6, 10, 8, 3, 7, 5, 1, 2, 4])
  | 7, 0, 6, 0 => (21, [2, 0, 7, 6, 5, 4, 3, 1], [0, 11, 9, 8, 10, 6, 5, 7, 3, 4, 2, 1])
  | 7, 0, 6, 8 => (21, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
  | 7, 0, 8, 0 => (21, [2, 0, 6, 7, 4, 5, 3, 1], [0, 9, 11, 6, 10, 8, 3, 7, 5, 4, 2, 1])
  | 7, 0, 8, 6 => (21, [0, 1, 2, 3, 4, 5, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 10, 9])
  | 7, 1, 0, 1 => (21, [0, 2, 5, 4, 7, 6, 1, 3], [0, 5, 3, 8, 7, 6, 11, 10, 9, 1, 2, 4])
  | 7, 1, 0, 2 => (21, [0, 2, 4, 5, 6, 7, 1, 3], [0, 3, 5, 6, 7, 8, 9, 10, 11, 1, 2, 4])
  | 7, 1, 1, 0 => (21, [0, 2, 5, 4, 7, 6, 3, 1], [0, 5, 3, 8, 7, 6, 11, 10, 9, 4, 2, 1])
  | 7, 1, 1, 2 => (21, [0, 1, 4, 5, 6, 7, 2, 3], [0, 3, 5, 6, 7, 8, 9, 10, 11, 1, 4, 2])
  | 7, 1, 2, 0 => (21, [0, 2, 4, 5, 6, 7, 3, 1], [0, 3, 5, 6, 7, 8, 9, 10, 11, 4, 2, 1])
  | 7, 1, 2, 1 => (21, [0, 1, 4, 5, 6, 7, 3, 2], [0, 3, 5, 6, 7, 8, 9, 10, 11, 2, 4, 1])
  | 7, 2, 1, 3 => (21, [2, 4, 7, 5, 1, 3, 6, 0], [3, 6, 7, 0, 8, 5, 1, 2, 4, 10, 9, 11])
  | 7, 2, 1, 4 => (21, [2, 4, 0, 5, 1, 3, 6, 7], [3, 6, 7, 0, 8, 5, 1, 2, 4, 9, 10, 11])
  | 7, 2, 3, 1 => (21, [2, 4, 7, 5, 1, 3, 0, 6], [3, 6, 7, 0, 8, 5, 1, 2, 4, 11, 9, 10])
  | 7, 2, 3, 4 => (21, [2, 4, 6, 5, 1, 3, 0, 7], [3, 6, 7, 0, 8, 5, 1, 2, 4, 9, 11, 10])
  | 7, 2, 4, 1 => (21, [2, 4, 0, 5, 1, 3, 7, 6], [3, 6, 7, 0, 8, 5, 1, 2, 4, 11, 10, 9])
  | 7, 2, 4, 3 => (21, [2, 4, 6, 5, 1, 3, 7, 0], [3, 6, 7, 0, 8, 5, 1, 2, 4, 10, 11, 9])
  | 7, 3, 2, 4 => (21, [2, 4, 5, 0, 3, 1, 6, 7], [3, 7, 6, 5, 8, 0, 4, 2, 1, 9, 10, 11])
  | 7, 3, 2, 5 => (21, [2, 4, 5, 7, 3, 1, 6, 0], [3, 7, 6, 5, 8, 0, 4, 2, 1, 10, 9, 11])
  | 7, 3, 4, 2 => (21, [2, 4, 5, 0, 3, 1, 7, 6], [3, 7, 6, 5, 8, 0, 4, 2, 1, 11, 10, 9])
  | 7, 3, 4, 5 => (21, [2, 4, 5, 6, 3, 1, 7, 0], [3, 7, 6, 5, 8, 0, 4, 2, 1, 10, 11, 9])
  | 7, 3, 5, 2 => (21, [2, 4, 5, 7, 3, 1, 0, 6], [3, 7, 6, 5, 8, 0, 4, 2, 1, 11, 9, 10])
  | 7, 3, 5, 4 => (21, [2, 4, 5, 6, 3, 1, 0, 7], [3, 7, 6, 5, 8, 0, 4, 2, 1, 9, 11, 10])
  | 7, 4, 3, 6 => (21, [4, 2, 1, 3, 7, 5, 0, 6], [3, 1, 4, 0, 2, 5, 6, 8, 7, 11, 9, 10])
  | 7, 4, 3, 7 => (21, [4, 2, 1, 3, 6, 5, 0, 7], [3, 1, 4, 0, 2, 5, 6, 8, 7, 9, 11, 10])
  | 7, 4, 6, 3 => (21, [4, 2, 1, 3, 7, 5, 6, 0], [3, 1, 4, 0, 2, 5, 6, 8, 7, 10, 9, 11])
  | 7, 4, 6, 7 => (21, [4, 2, 1, 3, 0, 5, 6, 7], [3, 1, 4, 0, 2, 5, 6, 8, 7, 9, 10, 11])
  | 7, 4, 7, 3 => (21, [4, 2, 1, 3, 6, 5, 7, 0], [3, 1, 4, 0, 2, 5, 6, 8, 7, 10, 11, 9])
  | 7, 4, 7, 6 => (21, [4, 2, 1, 3, 0, 5, 7, 6], [3, 1, 4, 0, 2, 5, 6, 8, 7, 11, 10, 9])
  | 7, 5, 5, 7 => (21, [4, 2, 3, 1, 5, 6, 0, 7], [3, 4, 1, 5, 2, 0, 7, 8, 6, 9, 11, 10])
  | 7, 5, 5, 8 => (21, [4, 2, 3, 1, 5, 7, 0, 6], [3, 4, 1, 5, 2, 0, 7, 8, 6, 11, 9, 10])
  | 7, 5, 7, 5 => (21, [4, 2, 3, 1, 5, 6, 7, 0], [3, 4, 1, 5, 2, 0, 7, 8, 6, 10, 11, 9])
  | 7, 5, 7, 8 => (21, [4, 2, 3, 1, 5, 0, 7, 6], [3, 4, 1, 5, 2, 0, 7, 8, 6, 11, 10, 9])
  | 7, 5, 8, 5 => (21, [4, 2, 3, 1, 5, 7, 6, 0], [3, 4, 1, 5, 2, 0, 7, 8, 6, 10, 9, 11])
  | 7, 5, 8, 7 => (21, [4, 2, 3, 1, 5, 0, 6, 7], [3, 4, 1, 5, 2, 0, 7, 8, 6, 9, 10, 11])
  | 8, 0, 0, 1 => (23, [0, 1, 2, 4, 5, 3, 6, 7], [1, 2, 0, 4, 5, 3, 7, 8, 6, 9, 10, 11])
  | 8, 0, 0, 2 => (23, [0, 1, 2, 4, 3, 5, 6, 7], [1, 0, 2, 4, 3, 5, 7, 6, 8, 9, 10, 11])
  | 8, 0, 1, 0 => (23, [0, 1, 2, 4, 5, 3, 7, 6], [1, 2, 0, 4, 5, 3, 7, 8, 6, 11, 10, 9])
  | 8, 0, 1, 2 => (23, [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
  | 8, 0, 2, 0 => (23, [0, 1, 2, 4, 3, 5, 7, 6], [1, 0, 2, 4, 3, 5, 7, 6, 8, 11, 10, 9])
  | 8, 0, 2, 1 => (23, [0, 1, 2, 3, 4, 5, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 10, 9])
  | 8, 1, 3, 4 => (23, [1, 0, 2, 4, 5, 3, 6, 7], [4, 5, 3, 1, 2, 0, 7, 8, 6, 9, 10, 11])
  | 8, 1, 3, 5 => (23, [1, 0, 2, 4, 3, 5, 6, 7], [4, 3, 5, 1, 0, 2, 7, 6, 8, 9, 10, 11])
  | 8, 1, 4, 3 => (23, [1, 0, 2, 4, 5, 3, 7, 6], [4, 5, 3, 1, 2, 0, 7, 8, 6, 11, 10, 9])
  | 8, 1, 4, 5 => (23, [1, 0, 2, 3, 4, 5, 6, 7], [3, 4, 5, 0, 1, 2, 6, 7, 8, 9, 10, 11])
  | 8, 1, 5, 3 => (23, [1, 0, 2, 4, 3, 5, 7, 6], [4, 3, 5, 1, 0, 2, 7, 6, 8, 11, 10, 9])
  | 8, 1, 5, 4 => (23, [1, 0, 2, 3, 4, 5, 7, 6], [3, 4, 5, 0, 1, 2, 6, 7, 8, 11, 10, 9])
  | 8, 2, 6, 7 => (23, [1, 2, 0, 4, 5, 3, 6, 7], [4, 5, 3, 7, 8, 6, 1, 2, 0, 9, 10, 11])
  | 8, 2, 6, 8 => (23, [1, 2, 0, 4, 3, 5, 6, 7], [4, 3, 5, 7, 6, 8, 1, 0, 2, 9, 10, 11])
  | 8, 2, 7, 6 => (23, [1, 2, 0, 4, 5, 3, 7, 6], [4, 5, 3, 7, 8, 6, 1, 2, 0, 11, 10, 9])
  | 8, 2, 7, 8 => (23, [1, 2, 0, 3, 4, 5, 6, 7], [3, 4, 5, 6, 7, 8, 0, 1, 2, 9, 10, 11])
  | 8, 2, 8, 6 => (23, [1, 2, 0, 4, 3, 5, 7, 6], [4, 3, 5, 7, 6, 8, 1, 0, 2, 11, 10, 9])
  | 8, 2, 8, 7 => (23, [1, 2, 0, 3, 4, 5, 7, 6], [3, 4, 5, 6, 7, 8, 0, 1, 2, 11, 10, 9])
  | 8, 3, 0, 3 => (23, [3, 4, 5, 7, 1, 2, 0, 6], [0, 3, 6, 1, 4, 7, 2, 5, 8, 11, 9, 10])
  | 8, 3, 0, 6 => (23, [3, 4, 5, 6, 1, 2, 0, 7], [0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 11, 10])
  | 8, 3, 3, 0 => (23, [3, 4, 5, 7, 1, 2, 6, 0], [0, 3, 6, 1, 4, 7, 2, 5, 8, 10, 9, 11])
  | 8, 3, 3, 6 => (23, [3, 4, 5, 0, 1, 2, 6, 7], [0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 10, 11])
  | 8, 3, 6, 0 => (23, [3, 4, 5, 6, 1, 2, 7, 0], [0, 3, 6, 1, 4, 7, 2, 5, 8, 10, 11, 9])
  | 8, 3, 6, 3 => (23, [3, 4, 5, 0, 1, 2, 7, 6], [0, 3, 6, 1, 4, 7, 2, 5, 8, 11, 10, 9])
  | 8, 4, 1, 4 => (23, [3, 4, 5, 1, 7, 2, 0, 6], [3, 0, 6, 4, 1, 7, 5, 2, 8, 11, 9, 10])
  | 8, 4, 1, 7 => (23, [3, 4, 5, 1, 6, 2, 0, 7], [3, 0, 6, 4, 1, 7, 5, 2, 8, 9, 11, 10])
  | 8, 4, 4, 1 => (23, [3, 4, 5, 1, 7, 2, 6, 0], [3, 0, 6, 4, 1, 7, 5, 2, 8, 10, 9, 11])
  | 8, 4, 4, 7 => (23, [3, 4, 5, 1, 0, 2, 6, 7], [3, 0, 6, 4, 1, 7, 5, 2, 8, 9, 10, 11])
  | 8, 4, 7, 1 => (23, [3, 4, 5, 1, 6, 2, 7, 0], [3, 0, 6, 4, 1, 7, 5, 2, 8, 10, 11, 9])
  | 8, 4, 7, 4 => (23, [3, 4, 5, 1, 0, 2, 7, 6], [3, 0, 6, 4, 1, 7, 5, 2, 8, 11, 10, 9])
  | 8, 5, 2, 5 => (23, [3, 4, 5, 1, 2, 7, 0, 6], [3, 6, 0, 4, 7, 1, 5, 8, 2, 11, 9, 10])
  | 8, 5, 2, 8 => (23, [3, 4, 5, 1, 2, 6, 0, 7], [3, 6, 0, 4, 7, 1, 5, 8, 2, 9, 11, 10])
  | 8, 5, 5, 2 => (23, [3, 4, 5, 1, 2, 7, 6, 0], [3, 6, 0, 4, 7, 1, 5, 8, 2, 10, 9, 11])
  | 8, 5, 5, 8 => (23, [3, 4, 5, 1, 2, 0, 6, 7], [3, 6, 0, 4, 7, 1, 5, 8, 2, 9, 10, 11])
  | 8, 5, 8, 2 => (23, [3, 4, 5, 1, 2, 6, 7, 0], [3, 6, 0, 4, 7, 1, 5, 8, 2, 10, 11, 9])
  | 8, 5, 8, 5 => (23, [3, 4, 5, 1, 2, 0, 7, 6], [3, 6, 0, 4, 7, 1, 5, 8, 2, 11, 10, 9])
  | _, _, _, _ => (0, [], [])

/-- the Bool check for `Sub(Rep_j, i)` -/
def subChk (j : Nat) : Bool :=
  allFin (repG j).m (fun i =>
    repN (subD j i.val).1 == repN j + 2 &&
    isoChk (subG (repG j) i) (repG (subD j i.val).1) (repN_pos _) (repM_pos _) (subD j i.val).2.1 (subD j i.val).2.2)

/-- two distinct parallel edges `p`, `q` of a multigraph (Bool) -/
def parChk (H : MGraph) (p q : Nat) : Bool :=
  if hp : p < H.m then if hq : q < H.m then
    (p != q) && ((H.ends ⟨p, hp⟩ == H.ends ⟨q, hq⟩) || (H.ends ⟨p, hp⟩ == ((H.ends ⟨q, hq⟩).2, (H.ends ⟨q, hq⟩).1)))
  else false else false

/-- the Bool check for `Inf(Rep_j, s, i2, i3)` -/
def infChk (j : Nat) : Bool :=
  allFin (repG j).n (fun s => allFin (repG j).m (fun i2 => allFin (repG j).m (fun i3 =>
    !(i2 != i3 && ((repG j).ends i2).1 == s || i2 != i3 && ((repG j).ends i2).2 == s) ||
    !(((repG j).ends i3).1 == s || ((repG j).ends i3).2 == s) ||
    (let d := infD j s.val i2.val i3.val
     if d.1 == 0 then parChk (infG (repG j) s i2 i3) (d.2.1.getD 0 0) (d.2.1.getD 1 0)
     else repN d.1 == repN j + 2 &&
       isoChk (infG (repG j) s i2 i3) (repG d.1) (repN_pos _) (repM_pos _) d.2.1 d.2.2))))

theorem subChk_1 : subChk 1 = true := by decide +kernel
theorem infChk_1 : infChk 1 = true := by decide +kernel
theorem subChk_2 : subChk 2 = true := by decide +kernel
theorem infChk_2 : infChk 2 = true := by decide +kernel
theorem subChk_3 : subChk 3 = true := by decide +kernel
theorem infChk_3 : infChk 3 = true := by decide +kernel
theorem subChk_4 : subChk 4 = true := by decide +kernel
theorem infChk_4 : infChk 4 = true := by decide +kernel
theorem subChk_5 : subChk 5 = true := by decide +kernel
theorem infChk_5 : infChk 5 = true := by decide +kernel
theorem subChk_6 : subChk 6 = true := by decide +kernel
theorem infChk_6 : infChk 6 = true := by decide +kernel
theorem subChk_7 : subChk 7 = true := by decide +kernel
theorem infChk_7 : infChk 7 = true := by decide +kernel
theorem subChk_8 : subChk 8 = true := by decide +kernel
theorem infChk_8 : infChk 8 = true := by decide +kernel

end RH2F

namespace RH2F
open MGraph

/-- **Layer 5 of the Lean formalization of RH2** (towards Theorem B8, fact 7922314679f8733d, §4–§5): the digon
    reduction (Lemmas 1, 2), the triangle reduction (Lemma 3) with their lifting of isomorphisms to `Sub(H, i)` and
    `Inf(H, s, i2, i3)`, and the concrete isomorphism tables for `Sub`/`Inf` of the representatives with at most 6
    vertices (checked by `decide +kernel`). -/
theorem layer5 :
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → 4 ≤ vcount P → ∀ (u v : Fin X.n) (d1 d2 : Fin X.m),
      P d1 → P d2 → X.Joins d1 u v → X.Joins d2 u v → d1 ≠ d2 →
      ∃ D : DigData P, InG (addEdge X D.x D.y) (digP P D.u D.v D.x D.y) ∧
        vcount (digP P D.u D.v D.x D.y) + 2 = vcount P ∧
        ∀ H : MGraph, IsoFrom (digP P D.u D.v D.x D.y) H → ∃ i, IsoFrom P (subG H i)) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → SimpleP P → ∀ (a b c : Fin X.n) (ab bc ca : Fin X.m),
      P ab → P bc → P ca → X.Joins ab a b → X.Joins bc b c → X.Joins ca c a →
      ∃ T : TriData P, InG (triG X T.a' T.b' T.c') (triP P T.a T.b T.c T.a' T.b' T.c') ∧
        vcount (triP P T.a T.b T.c T.a' T.b' T.c') + 2 = vcount P ∧
        ∀ H : MGraph, IsoFrom (triP P T.a T.b T.c T.a' T.b' T.c') H →
          ∃ s i2 i3, i2 ≠ i3 ∧ H.Inc i2 s ∧ H.Inc i3 s ∧ IsoFrom P (infG H s i2 i3)) ∧
    (∀ j, 1 ≤ j → j ≤ 8 → subChk j = true ∧ infChk j = true) := by
  refine ⟨fun X P hG h4 u v d1 d2 hd1 hd2 j1 j2 d12 => ?_, fun X P hG hS a b c ab bc ca hab hbc hca jab jbc jca => ?_,
    fun j h1 h8 => ?_⟩
  · obtain ⟨D, _, _⟩ := digData_of hG h4 hd1 hd2 j1 j2 d12
    exact ⟨D, D.inG_digP hG, D.vcount_digP, fun H h => D.lift h⟩
  · obtain ⟨T, _, _, _⟩ := triData_of hG hS hab hbc hca jab jbc jca
    exact ⟨T, T.inG_triP hG, T.vcount_triP, fun H h => T.lift h⟩
  · rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨subChk_1, infChk_1⟩
    · exact ⟨subChk_2, infChk_2⟩
    · exact ⟨subChk_3, infChk_3⟩
    · exact ⟨subChk_4, infChk_4⟩
    · exact ⟨subChk_5, infChk_5⟩
    · exact ⟨subChk_6, infChk_6⟩
    · exact ⟨subChk_7, infChk_7⟩
    · exact ⟨subChk_8, infChk_8⟩

end RH2F
