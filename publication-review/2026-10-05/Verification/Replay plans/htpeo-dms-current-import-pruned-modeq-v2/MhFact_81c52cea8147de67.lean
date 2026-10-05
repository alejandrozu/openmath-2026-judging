-- Lean proof of fact 81c52cea8147de67 (RH2F.layer16); added by fact_submit, do not edit
import MhFact_413193082c4b8758
set_option backward.isDefEq.respectTransparency false

/-
  IV2.lean — the digon insertion H^D (facts fdd83999b9ec10e2, 898eb5ab55d140fe): for an edge set `P` of `X` and a
  set `D` of edges, every edge `ab ∈ D` is replaced by two new vertices `u, v` and the edges `a u`, `u v`, `u v`, `v b`.
  All digon insertions of `X` live in one ambient `digG X D` (two potential new vertices and three potential new edges
  per edge of `X`).
-/

namespace RH2F
open MGraph
open Classical

section digdef
variable {X : MGraph}

/-- old vertex `x` -/
def dO (x : Fin X.n) : Fin (X.n + 2 * X.m) := Fin.castAdd (2 * X.m) x
/-- the new vertex `u_d` (next to the first end of `d`) -/
def dU (d : Fin X.m) : Fin (X.n + 2 * X.m) := ⟨X.n + 2 * d.val, by have := d.isLt; omega⟩
/-- the new vertex `v_d` (next to the second end of `d`) -/
def dV (d : Fin X.m) : Fin (X.n + 2 * X.m) := ⟨X.n + 2 * d.val + 1, by have := d.isLt; omega⟩
/-- old edge `d` -/
def eO (d : Fin X.m) : Fin (X.m + 3 * X.m) := Fin.castAdd (3 * X.m) d
/-- the new edges of `d`: `k = 0, 1` the two parallel edges `u_d v_d`, `k = 2` the edge `v_d b` -/
def eN (d : Fin X.m) (k : Fin 3) : Fin (X.m + 3 * X.m) := ⟨X.m + 3 * d.val + k.val, by have := d.isLt; have := k.isLt; omega⟩

variable (X) in
/-- the ambient of the digon insertions `X^D` -/
noncomputable def digG (D : Fin X.m → Prop) : MGraph where
  n := X.n + 2 * X.m
  m := X.m + 3 * X.m
  ends := fun e =>
    if h : e.val < X.m then
      (if D ⟨e.val, h⟩ then (dO (X.ends ⟨e.val, h⟩).1, dU ⟨e.val, h⟩)
        else (dO (X.ends ⟨e.val, h⟩).1, dO (X.ends ⟨e.val, h⟩).2))
    else
      (if (e.val - X.m) % 3 = 2 then (dV ⟨(e.val - X.m) / 3, by have := e.isLt; omega⟩,
          dO (X.ends ⟨(e.val - X.m) / 3, by have := e.isLt; omega⟩).2)
        else (dU ⟨(e.val - X.m) / 3, by have := e.isLt; omega⟩, dV ⟨(e.val - X.m) / 3, by have := e.isLt; omega⟩))

/-- the edge set of `P^D`: the old edges of `P` and the new edges of the edges of `P ∩ D` -/
def digSet (P D : Fin X.m → Prop) : Fin (digG X D).m → Prop :=
  fun e => if h : e.val < X.m then P ⟨e.val, h⟩
    else P ⟨(e.val - X.m) / 3, by have := e.isLt; change e.val < X.m + 3 * X.m at this; omega⟩ ∧
      D ⟨(e.val - X.m) / 3, by have := e.isLt; change e.val < X.m + 3 * X.m at this; omega⟩

variable {D : Fin X.m → Prop}

theorem ends_eO (d : Fin X.m) : (digG X D).ends (eO d) =
    if D d then (dO (X.ends d).1, dU d) else (dO (X.ends d).1, dO (X.ends d).2) := by
  simp [digG, eO, d.isLt]

theorem ends_eO_D {d : Fin X.m} (h : D d) : (digG X D).ends (eO d) = (dO (X.ends d).1, dU d) := by
  rw [ends_eO, if_pos h]
theorem ends_eO_nD {d : Fin X.m} (h : ¬ D d) : (digG X D).ends (eO d) = (dO (X.ends d).1, dO (X.ends d).2) := by
  rw [ends_eO, if_neg h]

theorem eN_div (d : Fin X.m) (k : Fin 3) : ((eN d k).val - X.m) / 3 = d.val := by
  simp only [eN]; have := k.isLt; omega
theorem eN_mod (d : Fin X.m) (k : Fin 3) : ((eN d k).val - X.m) % 3 = k.val := by
  simp only [eN]; have := k.isLt; omega

theorem ends_eN01 (d : Fin X.m) (k : Fin 3) (hk : k ≠ 2) : (digG X D).ends (eN d k) = (dU d, dV d) := by
  have hk' : k.val ≠ 2 := fun h => hk (Fin.ext h)
  have hlt : ¬ (eN d k).val < X.m := by simp only [eN]; omega
  have hd : (⟨((eN d k).val - X.m) / 3, by have := (eN d k).isLt; omega⟩ : Fin X.m) = d := Fin.ext (eN_div d k)
  simp only [digG, dif_neg hlt]
  rw [if_neg (by rw [eN_mod]; exact hk'), hd]

theorem ends_eN2 (d : Fin X.m) : (digG X D).ends (eN d 2) = (dV d, dO (X.ends d).2) := by
  have hlt : ¬ (eN d 2).val < X.m := by simp only [eN]; omega
  have hd : (⟨((eN d 2).val - X.m) / 3, by have := (eN d 2).isLt; omega⟩ : Fin X.m) = d := Fin.ext (eN_div d 2)
  simp only [digG, dif_neg hlt]
  rw [if_pos (by rw [eN_mod]; rfl), hd]

theorem set_eO (P : Fin X.m → Prop) (d : Fin X.m) : digSet P D (eO d) ↔ P d := by
  simp [digSet, eO, d.isLt]

theorem set_eN (P : Fin X.m → Prop) (d : Fin X.m) (k : Fin 3) : digSet P D (eN d k) ↔ P d ∧ D d := by
  have hlt : ¬ (eN d k).val < X.m := by simp only [eN]; omega
  have hd : (⟨((eN d k).val - X.m) / 3, by have := (eN d k).isLt; omega⟩ : Fin X.m) = d := Fin.ext (eN_div d k)
  simp only [digSet, dif_neg hlt]
  rw [hd]

theorem dig_cases (e : Fin (digG X D).m) : (∃ d, e = eO d) ∨ ∃ d k, e = eN d k := by
  by_cases h : e.val < X.m
  · exact Or.inl ⟨⟨e.val, h⟩, Fin.ext rfl⟩
  · have he := e.isLt
    refine Or.inr ⟨⟨(e.val - X.m) / 3, by show (e.val - X.m) / 3 < X.m; change e.val < X.m + 3 * X.m at he; omega⟩,
      ⟨(e.val - X.m) % 3, Nat.mod_lt _ (by decide)⟩, Fin.ext ?_⟩
    simp only [eN]; omega

theorem vert_cases (w : Fin (digG X D).n) : (∃ x, w = dO x) ∨ (∃ d, w = dU d) ∨ ∃ d, w = dV d := by
  have hw := w.isLt
  change w.val < X.n + 2 * X.m at hw
  by_cases h : w.val < X.n
  · exact Or.inl ⟨⟨w.val, h⟩, Fin.ext rfl⟩
  · by_cases h2 : (w.val - X.n) % 2 = 0
    · exact Or.inr (Or.inl ⟨⟨(w.val - X.n) / 2, by omega⟩, Fin.ext (by simp only [dU]; omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨(w.val - X.n) / 2, by omega⟩, Fin.ext (by simp only [dV]; omega)⟩)

theorem dO_inj {x y : Fin X.n} (h : (dO x : Fin (X.n + 2 * X.m)) = dO y) : x = y := by
  simp only [dO] at h; exact Fin.ext (by simpa using congrArg Fin.val h)
theorem dU_inj {d d' : Fin X.m} (h : (dU d : Fin (X.n + 2 * X.m)) = dU d') : d = d' := by
  have := congrArg Fin.val h; simp only [dU] at this; exact Fin.ext (by omega)
theorem dV_inj {d d' : Fin X.m} (h : (dV d : Fin (X.n + 2 * X.m)) = dV d') : d = d' := by
  have := congrArg Fin.val h; simp only [dV] at this; exact Fin.ext (by omega)
theorem dO_ne_dU (x : Fin X.n) (d : Fin X.m) : (dO x : Fin (X.n + 2 * X.m)) ≠ dU d := by
  intro h; have := congrArg Fin.val h; simp only [dO, dU, Fin.coe_castAdd] at this; have := x.isLt; omega
theorem dO_ne_dV (x : Fin X.n) (d : Fin X.m) : (dO x : Fin (X.n + 2 * X.m)) ≠ dV d := by
  intro h; have := congrArg Fin.val h; simp only [dO, dV, Fin.coe_castAdd] at this; have := x.isLt; omega
theorem dU_ne_dV (d d' : Fin X.m) : (dU d : Fin (X.n + 2 * X.m)) ≠ dV d' := by
  intro h; have := congrArg Fin.val h; simp only [dU, dV] at this; omega

theorem eO_inj {d d' : Fin X.m} (h : (eO d : Fin (X.m + 3 * X.m)) = eO d') : d = d' := by
  simp only [eO] at h; exact Fin.ext (by simpa using congrArg Fin.val h)
theorem eN_inj {d d' : Fin X.m} {k k' : Fin 3} (h : (eN d k : Fin (X.m + 3 * X.m)) = eN d' k') : d = d' ∧ k = k' := by
  have := congrArg Fin.val h; simp only [eN] at this
  have := k.isLt; have := k'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
theorem eO_ne_eN (d d' : Fin X.m) (k : Fin 3) : (eO d : Fin (X.m + 3 * X.m)) ≠ eN d' k := by
  intro h; have := congrArg Fin.val h; simp only [eO, eN, Fin.coe_castAdd] at this; have := d.isLt; omega

end digdef

section digthm
variable {X : MGraph} {D : Fin X.m → Prop}

/-! ### incidences -/

theorem inc_eO_dO {d : Fin X.m} {x : Fin X.n} :
    (digG X D).Inc (eO d) (dO x) ↔ (X.ends d).1 = x ∨ (¬ D d ∧ (X.ends d).2 = x) := by
  unfold Inc
  by_cases h : D d
  · rw [ends_eO_D h]; simp only
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (dO_inj h1)
      · exact absurd h1.symm (dO_ne_dU _ _)
    · rintro (h1 | ⟨h1, _⟩)
      · exact Or.inl (by rw [h1])
      · exact absurd h h1
  · rw [ends_eO_nD h]; simp only
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (dO_inj h1)
      · exact Or.inr ⟨h, dO_inj h1⟩
    · rintro (h1 | ⟨_, h1⟩)
      · exact Or.inl (by rw [h1])
      · exact Or.inr (by rw [h1])

theorem inc_eO_dU {d d' : Fin X.m} : (digG X D).Inc (eO d) (dU d') ↔ D d ∧ d = d' := by
  unfold Inc
  by_cases h : D d
  · rw [ends_eO_D h]; simp only
    constructor
    · rintro (h1 | h1)
      · exact absurd h1 (dO_ne_dU _ _)
      · exact ⟨h, dU_inj h1⟩
    · rintro ⟨_, rfl⟩; exact Or.inr rfl
  · rw [ends_eO_nD h]; simp only
    constructor
    · rintro (h1 | h1) <;> exact absurd h1 (dO_ne_dU _ _)
    · rintro ⟨h1, _⟩; exact absurd h1 h

theorem not_inc_eO_dV {d d' : Fin X.m} : ¬ (digG X D).Inc (eO d) (dV d') := by
  unfold Inc
  rw [ends_eO]
  split_ifs <;> simp only <;> rintro (h1 | h1)
  · exact dO_ne_dV _ _ h1
  · exact dU_ne_dV _ _ h1
  · exact dO_ne_dV _ _ h1
  · exact dO_ne_dV _ _ h1

theorem k_cases (k : Fin 3) : k = 2 ∨ k ≠ 2 := by
  by_cases h : k = 2
  · exact Or.inl h
  · exact Or.inr h

theorem inc_eN_dO {d : Fin X.m} {k : Fin 3} {x : Fin X.n} :
    (digG X D).Inc (eN d k) (dO x) ↔ k = 2 ∧ (X.ends d).2 = x := by
  unfold Inc
  rcases k_cases k with rfl | hk
  · rw [ends_eN2]
    constructor
    · rintro (h1 | h1)
      · exact absurd h1.symm (dO_ne_dV _ _)
      · exact ⟨rfl, dO_inj h1⟩
    · rintro ⟨_, h1⟩; exact Or.inr (by show dO (X.ends d).2 = dO x; rw [h1])
  · rw [ends_eN01 d k hk]; simp only
    constructor
    · rintro (h1 | h1)
      · exact absurd h1.symm (dO_ne_dU _ _)
      · exact absurd h1.symm (dO_ne_dV _ _)
    · rintro ⟨h1, _⟩; exact absurd h1 hk

theorem inc_eN_dU {d d' : Fin X.m} {k : Fin 3} : (digG X D).Inc (eN d k) (dU d') ↔ k ≠ 2 ∧ d = d' := by
  unfold Inc
  rcases k_cases k with rfl | hk
  · rw [ends_eN2]; simp only
    constructor
    · rintro (h1 | h1)
      · exact absurd h1.symm (dU_ne_dV _ _)
      · exact absurd h1 (dO_ne_dU _ _)
    · rintro ⟨h1, _⟩; exact absurd rfl h1
  · rw [ends_eN01 d k hk]; simp only
    constructor
    · rintro (h1 | h1)
      · exact ⟨hk, dU_inj h1⟩
      · exact absurd h1 (dU_ne_dV _ _).symm
    · rintro ⟨_, rfl⟩; exact Or.inl rfl

theorem inc_eN_dV {d d' : Fin X.m} {k : Fin 3} : (digG X D).Inc (eN d k) (dV d') ↔ d = d' := by
  unfold Inc
  rcases k_cases k with rfl | hk
  · rw [ends_eN2]; simp only
    constructor
    · rintro (h1 | h1)
      · exact dV_inj h1
      · exact absurd h1 (dO_ne_dV _ _)
    · rintro rfl; exact Or.inl rfl
  · rw [ends_eN01 d k hk]; simp only
    constructor
    · rintro (h1 | h1)
      · exact absurd h1 (dU_ne_dV _ _)
      · exact dV_inj h1
    · rintro rfl; exact Or.inr rfl

/-! ### H^D is loopless, cubic, connected and bridgeless -/

theorem dig_loopless (hloop : Loopless X) : Loopless (digG X D) := by
  intro e
  rcases dig_cases e with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
  · rw [ends_eO]
    split_ifs
    · exact dO_ne_dU _ _
    · exact fun h => hloop d (dO_inj h)
  · rcases k_cases k with rfl | hk
    · rw [ends_eN2]; exact fun h => dO_ne_dV _ _ h.symm
    · rw [ends_eN01 d k hk]; exact dU_ne_dV _ _

/-- the edge of `P^D` at `x` coming from the edge `f` of `P` at `x` -/
noncomputable def stub (f : Fin X.m) (x : Fin X.n) : Fin (digG X D).m :=
  if (X.ends f).1 = x then eO f else if D f then eN f 2 else eO f

theorem stub_set {P : Fin X.m → Prop} {f : Fin X.m} (hf : P f) (x : Fin X.n) : digSet P D (stub (D := D) f x) := by
  unfold stub
  split_ifs with h1 h2
  · exact (set_eO P f).2 hf
  · exact (set_eN P f 2).2 ⟨hf, h2⟩
  · exact (set_eO P f).2 hf

theorem stub_inc {f : Fin X.m} {x : Fin X.n} (hx : X.Inc f x) : (digG X D).Inc (stub (D := D) f x) (dO x) := by
  unfold stub
  split_ifs with h1 h2
  · exact inc_eO_dO.2 (Or.inl h1)
  · exact inc_eN_dO.2 ⟨rfl, hx.resolve_left h1⟩
  · exact inc_eO_dO.2 (Or.inr ⟨h2, hx.resolve_left h1⟩)

theorem stub_inj {f g : Fin X.m} {x : Fin X.n}
    (h : stub (D := D) f x = stub (D := D) g x) : f = g := by
  unfold stub at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | exact eO_inj h
    | exact (eN_inj h).1
    | exact absurd h (eO_ne_eN _ _ _)
    | exact absurd h.symm (eO_ne_eN _ _ _)

/-- every edge of `P^D` at an old vertex `x` is the stub of an edge of `P` at `x` -/
theorem at_dO {P : Fin X.m → Prop} (hloop : Loopless X) {e : Fin (digG X D).m} {x : Fin X.n}
    (he : digSet P D e) (hx : (digG X D).Inc e (dO x)) : ∃ f, P f ∧ X.Inc f x ∧ e = stub f x := by
  rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
  · have hf := (set_eO P f).1 he
    rcases inc_eO_dO.1 hx with h1 | ⟨h2, h1⟩
    · exact ⟨f, hf, Or.inl h1, by unfold stub; rw [if_pos h1]⟩
    · refine ⟨f, hf, Or.inr h1, ?_⟩
      unfold stub
      rw [if_neg (fun h => hloop f (h.trans h1.symm)), if_neg h2]
  · obtain ⟨hf, hD⟩ := (set_eN P f k).1 he
    obtain ⟨rfl, h1⟩ := inc_eN_dO.1 hx
    refine ⟨f, hf, Or.inr h1, ?_⟩
    unfold stub
    rw [if_neg (fun h => hloop f (h.trans h1.symm)), if_pos hD]

theorem dig_cubic (hloop : Loopless X) {P : Fin X.m → Prop} (hcub : CubicOn P) : CubicOn (digSet P D) := by
  rintro w ⟨e0, he0, hw⟩
  rcases vert_cases w with ⟨x, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
  · obtain ⟨f0, hf0, hf0x, _⟩ := at_dO hloop he0 hw
    obtain ⟨a, b, c, ha, hb, hc, iax, ibx, icx, dab, dac, dbc, hall⟩ := hcub x ⟨f0, hf0, hf0x⟩
    refine ⟨stub a x, stub b x, stub c x, stub_set ha x, stub_set hb x, stub_set hc x, stub_inc iax, stub_inc ibx,
      stub_inc icx, fun h => dab (stub_inj h), fun h => dac (stub_inj h),
      fun h => dbc (stub_inj h), ?_⟩
    intro e he hex
    obtain ⟨f, hf, hfx, rfl⟩ := at_dO hloop he hex
    rcases hall f hf hfx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · -- `u_d`: the edges `eO d`, `eN d 0`, `eN d 1`
    have hPD : P d ∧ D d := by
      rcases dig_cases e0 with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
      · obtain ⟨h1, rfl⟩ := inc_eO_dU.1 hw; exact ⟨(set_eO P f).1 he0, h1⟩
      · obtain ⟨_, rfl⟩ := inc_eN_dU.1 hw; exact (set_eN P f k).1 he0
    refine ⟨eO d, eN d 0, eN d 1, (set_eO P d).2 hPD.1, (set_eN P d 0).2 hPD, (set_eN P d 1).2 hPD,
      inc_eO_dU.2 ⟨hPD.2, rfl⟩, inc_eN_dU.2 ⟨by decide, rfl⟩, inc_eN_dU.2 ⟨by decide, rfl⟩,
      eO_ne_eN _ _ _, eO_ne_eN _ _ _, fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this, ?_⟩
    intro e _ hex
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · obtain ⟨_, rfl⟩ := inc_eO_dU.1 hex; exact Or.inl rfl
    · obtain ⟨hk, rfl⟩ := inc_eN_dU.1 hex
      have : k = 0 ∨ k = 1 := by
        rcases k with ⟨k, hk3⟩
        have : k ≠ 2 := fun h => hk (Fin.ext h)
        simp only [Fin.ext_iff]; omega
      rcases this with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · -- `v_d`: the edges `eN d 0`, `eN d 1`, `eN d 2`
    have hPD : P d ∧ D d := by
      rcases dig_cases e0 with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
      · exact absurd hw not_inc_eO_dV
      · obtain rfl := inc_eN_dV.1 hw; exact (set_eN P f k).1 he0
    refine ⟨eN d 0, eN d 1, eN d 2, (set_eN P d 0).2 hPD, (set_eN P d 1).2 hPD, (set_eN P d 2).2 hPD,
      inc_eN_dV.2 rfl, inc_eN_dV.2 rfl, inc_eN_dV.2 rfl,
      fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this,
      fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this,
      fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this, ?_⟩
    intro e _ hex
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · exact absurd hex not_inc_eO_dV
    · obtain rfl := inc_eN_dV.1 hex
      have : k = 0 ∨ k = 1 ∨ k = 2 := by
        rcases k with ⟨k, hk3⟩
        simp only [Fin.ext_iff]; omega
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-! ### walks along the path of an edge -/

/-- the path of an edge `d = ab` in `X^D`: `a u_d`, `u_d v_d`, `v_d b` if `D d`, otherwise the edge itself -/
def onPath (d : Fin X.m) (e : Fin (digG X D).m) : Prop := e = eO d ∨ ∃ k, e = eN d k

theorem onPath_inj {d d' : Fin X.m} {e : Fin (digG X D).m} (h : onPath d e) (h' : onPath d' e) : d = d' := by
  rcases h with rfl | ⟨k, rfl⟩ <;> rcases h' with h' | ⟨k', h'⟩
  · exact eO_inj h'
  · exact absurd h' (eO_ne_eN _ _ _)
  · exact absurd h'.symm (eO_ne_eN _ _ _)
  · exact (eN_inj h').1

/-- a 2-colouring constant on the path edges of `d` has equal values at the two ends of `d` -/
theorem path_const {P : Fin X.m → Prop} (U : Fin (digG X D).n → Bool) {d : Fin X.m} (hd : P d)
    (hU : ∀ e, digSet P D e → onPath d e → U ((digG X D).ends e).1 = U ((digG X D).ends e).2) :
    U (dO (X.ends d).1) = U (dO (X.ends d).2) ∧ (D d → U (dU d) = U (dO (X.ends d).1) ∧ U (dV d) = U (dO (X.ends d).1)) := by
  by_cases hD : D d
  · have h0 := hU (eO d) ((set_eO P d).2 hd) (Or.inl rfl)
    have h1 := hU (eN d 0) ((set_eN P d 0).2 ⟨hd, hD⟩) (Or.inr ⟨0, rfl⟩)
    have h2 := hU (eN d 2) ((set_eN P d 2).2 ⟨hd, hD⟩) (Or.inr ⟨2, rfl⟩)
    rw [ends_eO_D hD] at h0
    rw [ends_eN01 d 0 (by decide)] at h1
    rw [ends_eN2] at h2
    exact ⟨h0.trans (h1.trans h2), fun _ => ⟨h0.symm, (h0.trans h1).symm⟩⟩
  · have h0 := hU (eO d) ((set_eO P d).2 hd) (Or.inl rfl)
    rw [ends_eO_nD hD] at h0
    exact ⟨h0, fun h => absurd h hD⟩

theorem dig_connected {P : Fin X.m → Prop} (hconn : ConnectedOn P) : ConnectedOn (digSet P D) := by
  intro U hU e e' he he'
  have hP := hconn (fun x => U (dO x)) (fun f hf => (path_const U hf (fun e he _ => hU e he)).1)
  have key : ∀ e, digSet P D e → ∃ f, P f ∧ U ((digG X D).ends e).1 = U (dO (X.ends f).1) := by
    intro e he
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · refine ⟨f, (set_eO P f).1 he, ?_⟩
      rw [ends_eO]; split_ifs <;> rfl
    · obtain ⟨hf, hD⟩ := (set_eN P f k).1 he
      have hc := (path_const U hf (fun e he _ => hU e he)).2 hD
      refine ⟨f, hf, ?_⟩
      rcases k_cases k with rfl | hk
      · rw [ends_eN2]; exact hc.2
      · rw [ends_eN01 f k hk]; exact hc.1
  obtain ⟨f, hf, h1⟩ := key e he
  obtain ⟨g, hg, h2⟩ := key e' he'
  rw [h1, h2]; exact hP f g hf hg

theorem dig_bridgeless {P : Fin X.m → Prop} (hbr : BridgelessOn P) : BridgelessOn (digSet P D) := by
  intro e he B
  have hsep : ∀ e', digSet P D e' → e' ≠ e → B.U ((digG X D).ends e').1 = B.U ((digG X D).ends e').2 :=
    fun e' he' hne => B.sep e' he' hne
  -- the old edge `f` of the path through `e` gets a bridge cut
  have cut : ∀ f, P f → onPath f e → B.U (dO (X.ends f).1) = true → B.U (dO (X.ends f).2) = false → False := by
    intro f hf hfe h1 h2
    apply hbr f hf
    exact { U := fun x => B.U (dO x)
            hu := h1
            hv := h2
            sep := fun g hg hne => (path_const B.U hg (fun e' he' hp => hsep e' he' (fun h => hne
              (onPath_inj (h ▸ hp) hfe)))).1 }
  have hu := B.hu; have hv := B.hv
  rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
  · have hf := (set_eO P f).1 he
    by_cases hD : D f
    · rw [ends_eO_D hD] at hu hv
      have h1 := hsep (eN f 0) ((set_eN P f 0).2 ⟨hf, hD⟩) (fun h => eO_ne_eN _ _ _ h.symm)
      have h2 := hsep (eN f 2) ((set_eN P f 2).2 ⟨hf, hD⟩) (fun h => eO_ne_eN _ _ _ h.symm)
      rw [ends_eN01 f 0 (by decide)] at h1
      rw [ends_eN2] at h2
      exact cut f hf (Or.inl rfl) hu (by rw [← h2, ← h1]; exact hv)
    · rw [ends_eO_nD hD] at hu hv
      exact cut f hf (Or.inl rfl) hu hv
  · obtain ⟨hf, hD⟩ := (set_eN P f k).1 he
    rcases k_cases k with rfl | hk
    · rw [ends_eN2] at hu hv
      have h1 := hsep (eN f 0) ((set_eN P f 0).2 ⟨hf, hD⟩) (fun h => by
        have := (eN_inj h).2; simp [Fin.ext_iff] at this)
      have h0 := hsep (eO f) ((set_eO P f).2 hf) (fun h => eO_ne_eN _ _ _ h)
      rw [ends_eN01 f 0 (by decide)] at h1
      rw [ends_eO_D hD] at h0
      exact cut f hf (Or.inr ⟨2, rfl⟩) (by rw [h0, h1]; exact hu) hv
    · -- the other parallel edge of the digon
      let k' : Fin 3 := if k = 0 then 1 else 0
      have hk' : k' ≠ 2 := by simp only [k']; split_ifs <;> decide
      have hkk : eN f k' ≠ eN f k := fun h => by
        have := (eN_inj h).2
        simp only [k'] at this
        split_ifs at this with h0
        · rw [h0] at this; exact absurd this (by decide)
        · exact h0 this.symm
      have h1 := hsep (eN f k') ((set_eN P f k').2 ⟨hf, hD⟩) hkk
      rw [ends_eN01 f k' hk'] at h1
      rw [ends_eN01 f k hk] at hu hv
      rw [h1] at hu; rw [hu] at hv; exact Bool.noConfusion hv

/-! ### counting -/

theorem meets_dig_dO (hloop : Loopless X) {P : Fin X.m → Prop} (x : Fin X.n) :
    meets (digSet P D) (dO x) ↔ meets P x := by
  constructor
  · rintro ⟨e, he, hex⟩
    obtain ⟨f, hf, hfx, _⟩ := at_dO hloop he hex
    exact ⟨f, hf, hfx⟩
  · rintro ⟨f, hf, hfx⟩
    exact ⟨stub f x, stub_set hf x, stub_inc hfx⟩

theorem meets_dig_dU {P : Fin X.m → Prop} (d : Fin X.m) : meets (digSet P D) (dU d) ↔ P d ∧ D d := by
  constructor
  · rintro ⟨e, he, hed⟩
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · obtain ⟨h1, rfl⟩ := inc_eO_dU.1 hed; exact ⟨(set_eO P f).1 he, h1⟩
    · obtain ⟨_, rfl⟩ := inc_eN_dU.1 hed; exact (set_eN P f k).1 he
  · intro h
    exact ⟨eN d 0, (set_eN P d 0).2 h, inc_eN_dU.2 ⟨by decide, rfl⟩⟩

theorem meets_dig_dV {P : Fin X.m → Prop} (d : Fin X.m) : meets (digSet P D) (dV d) ↔ P d ∧ D d := by
  constructor
  · rintro ⟨e, he, hed⟩
    rcases dig_cases e with ⟨f, rfl⟩ | ⟨f, k, rfl⟩
    · exact absurd hed not_inc_eO_dV
    · obtain rfl := inc_eN_dV.1 hed; exact (set_eN P f k).1 he
  · intro h
    exact ⟨eN d 0, (set_eN P d 0).2 h, inc_eN_dV.2 rfl⟩

/-- `|V(P^D)| = |V(P)| + 2 |P ∩ D|` -/
theorem vcount_dig (hloop : Loopless X) {P : Fin X.m → Prop} :
    vcount (digSet P D) = vcount P + 2 * cntF X.m (fun d => P d ∧ D d) := by
  unfold vcount
  let A : Finset (Fin X.m) := Finset.univ.filter (fun d => P d ∧ D d)
  have hA : cntF X.m (fun d => P d ∧ D d) = A.card := by rw [cntF_eq_card]; convert rfl
  rw [cntF_eq_card, cntF_eq_card, hA]
  have hset : Finset.univ.filter (meets (digSet P D)) =
      (Finset.univ.filter (meets P)).image dO ∪ (A.image dU ∪ A.image dV) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, A]
    rcases vert_cases w with ⟨x, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
    · rw [meets_dig_dO hloop]
      constructor
      · intro h; exact Or.inl ⟨x, h, rfl⟩
      · rintro (⟨y, hy, h⟩ | ⟨y, _, h⟩ | ⟨y, _, h⟩)
        · rw [dO_inj h] at hy; exact hy
        · exact absurd h.symm (dO_ne_dU _ _)
        · exact absurd h.symm (dO_ne_dV _ _)
    · rw [meets_dig_dU]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨d, h, rfl⟩)
      · rintro (⟨y, _, h⟩ | ⟨y, hy, h⟩ | ⟨y, _, h⟩)
        · exact absurd h (dO_ne_dU _ _)
        · rw [← dU_inj h]; exact hy
        · exact absurd h (dU_ne_dV _ _).symm
    · rw [meets_dig_dV]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨d, h, rfl⟩)
      · rintro (⟨y, _, h⟩ | ⟨y, _, h⟩ | ⟨y, hy, h⟩)
        · exact absurd h (dO_ne_dV _ _)
        · exact absurd h (dU_ne_dV _ _)
        · rw [← dV_inj h]; exact hy
  rw [hset, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (fun a b h => dO_inj h), Finset.card_image_of_injective _ (fun a b h => dU_inj h),
    Finset.card_image_of_injective _ (fun a b h => dV_inj h)]
  · omega
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_image] at hw hw'
    obtain ⟨a, _, rfl⟩ := hw
    obtain ⟨b, _, h⟩ := hw'
    exact dU_ne_dV _ _ h.symm
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_union, Finset.mem_image] at hw hw'
    obtain ⟨a, _, rfl⟩ := hw
    rcases hw' with ⟨b, _, h⟩ | ⟨b, _, h⟩
    · exact dO_ne_dU _ _ h.symm
    · exact dO_ne_dV _ _ h.symm

/-! ### 2-cut-reducedness -/

theorem ends_meets1 {P : Fin X.m → Prop} {d : Fin X.m} (hd : P d) : meets P (X.ends d).1 := ⟨d, hd, Or.inl rfl⟩
theorem ends_meets2 {P : Fin X.m → Prop} {d : Fin X.m} (hd : P d) : meets P (X.ends d).2 := ⟨d, hd, Or.inr rfl⟩

/-- **H^D is 2-cut-reduced** if `H` has no 2-edge-cut: every 2-edge-cut of `P^D` cuts off one digon `{u_d, v_d}` -/
theorem dig_2cr {P : Fin X.m → Prop} (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) : TwoCutReducedOn (digSet P D) := by
  intro S ⟨f1, f2, hne, c1, c2, hall⟩
  -- three distinct crossing edges are impossible
  have no3 : ∀ a b c, RH2F.Crosses (digSet P D) S a → RH2F.Crosses (digSet P D) S b →
      RH2F.Crosses (digSet P D) S c → a ≠ b → a ≠ c → b ≠ c → False := by
    intro a b c ha hb hc hab hac hbc
    rcases hall a ha with rfl | rfl <;> rcases hall b hb with rfl | rfl <;> rcases hall c hc with rfl | rfl <;>
      simp_all
  have cr : ∀ e, digSet P D e → S ((digG X D).ends e).1 ≠ S ((digG X D).ends e).2 → RH2F.Crosses (digSet P D) S e :=
    fun e he h => ⟨he, h⟩
  let SH : Fin X.n → Bool := fun x => S (dO x)
  -- a crossing `P`-edge has a crossing edge on its path
  have pathX : ∀ d, P d → SH (X.ends d).1 ≠ SH (X.ends d).2 → ∃ e, onPath d e ∧ RH2F.Crosses (digSet P D) S e := by
    intro d hd hne'
    by_contra hno
    apply hne'
    refine (path_const S hd (fun e he hp => ?_)).1
    by_contra h
    exact hno ⟨e, hp, he, h⟩
  -- step 1: all old vertices meeting `P` lie on one side
  have step1 : ∀ x y, meets P x → meets P y → SH x = SH y := by
    intro x y hx hy
    by_contra hxy
    have ex1 : ∃ d1, P d1 ∧ SH (X.ends d1).1 ≠ SH (X.ends d1).2 := by
      by_contra hno
      have hno' : ∀ f, P f → SH (X.ends f).1 = SH (X.ends f).2 := fun f hf => by
        by_contra h; exact hno ⟨f, hf, h⟩
      have hc := hG.2.1 SH hno'
      have atv : ∀ v f, P f → X.Inc f v → SH v = SH (X.ends f).1 := by
        intro v f hf hv
        rcases hv with h | h
        · rw [h]
        · rw [← h, hno' f hf]
      obtain ⟨fx, hfx, ifx⟩ := hx
      obtain ⟨fy, hfy, ify⟩ := hy
      exact hxy ((atv x fx hfx ifx).trans ((hc fx fy hfx hfy).trans (atv y fy hfy ify).symm))
    obtain ⟨d1, hd1, hc1⟩ := ex1
    have ex2 : ∃ d2, P d2 ∧ d2 ≠ d1 ∧ SH (X.ends d2).1 ≠ SH (X.ends d2).2 := by
      by_contra hno
      apply hG.2.2.1 d1 hd1
      exact { U := fun v => decide (SH v = SH (X.ends d1).1)
              hu := by simp
              hv := by simp only [decide_eq_false_iff_not]; exact fun h => hc1 h.symm
              sep := fun g hg hgne => by
                have : SH (X.ends g).1 = SH (X.ends g).2 := by
                  by_contra h; exact hno ⟨g, hg, hgne, h⟩
                simp only [this] }
    obtain ⟨d2, hd2, h21, hc2⟩ := ex2
    have ex3 : ∃ d3, P d3 ∧ d3 ≠ d1 ∧ d3 ≠ d2 ∧ SH (X.ends d3).1 ≠ SH (X.ends d3).2 := by
      by_contra hno
      apply h3 SH
      refine ⟨d1, d2, fun h => h21 h.symm, ⟨hd1, hc1⟩, ⟨hd2, hc2⟩, fun d hd => ?_⟩
      by_contra h
      push_neg at h
      exact hno ⟨d, hd.1, h.1, h.2, hd.2⟩
    obtain ⟨d3, hd3, h31, h32, hc3⟩ := ex3
    obtain ⟨e1, p1, x1⟩ := pathX d1 hd1 hc1
    obtain ⟨e2, p2, x2⟩ := pathX d2 hd2 hc2
    obtain ⟨e3, p3, x3⟩ := pathX d3 hd3 hc3
    exact no3 e1 e2 e3 x1 x2 x3 (fun h => h21 (onPath_inj p1 (h ▸ p2)).symm)
      (fun h => h31 (onPath_inj p1 (h ▸ p3)).symm) (fun h => h32 (onPath_inj p2 (h ▸ p3)).symm)
  -- the side of the old vertices
  obtain ⟨dA, hdA⟩ : ∃ d, P d := by
    rcases dig_cases f1 with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
    · exact ⟨d, (set_eO P d).1 c1.1⟩
    · exact ⟨d, ((set_eN P d k).1 c1.1).1⟩
  let b0 := SH (X.ends dA).1
  have hb0 : ∀ x, meets P x → S (dO x) = b0 := fun x hx => step1 x _ hx (ends_meets1 hdA)
  -- claim A: the two vertices of a digon lie on the same side
  have claimA : ∀ d, P d → D d → S (dU d) = S (dV d) := by
    intro d hd hD
    by_contra huv
    have x0 : RH2F.Crosses (digSet P D) S (eN d 0) :=
      cr _ ((set_eN P d 0).2 ⟨hd, hD⟩) (by rw [ends_eN01 d 0 (by decide)]; exact huv)
    have x1 : RH2F.Crosses (digSet P D) S (eN d 1) :=
      cr _ ((set_eN P d 1).2 ⟨hd, hD⟩) (by rw [ends_eN01 d 1 (by decide)]; exact huv)
    have n01 : eN d 0 ≠ eN d 1 := fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this
    by_cases hu : S (dU d) = b0
    · have x2 : RH2F.Crosses (digSet P D) S (eN d 2) :=
        cr _ ((set_eN P d 2).2 ⟨hd, hD⟩) (by
          rw [ends_eN2, hb0 _ (ends_meets2 hd)]; intro h; exact huv (hu.trans h.symm))
      exact no3 _ _ _ x0 x1 x2 n01 (fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this)
        (fun h => by have := (eN_inj h).2; simp [Fin.ext_iff] at this)
    · have x2 : RH2F.Crosses (digSet P D) S (eO d) :=
        cr _ ((set_eO P d).2 hd) (by rw [ends_eO_D hD, hb0 _ (ends_meets1 hd)]; exact fun h => hu h.symm)
      exact no3 _ _ _ x0 x1 x2 n01 (fun h => eO_ne_eN _ _ _ h.symm) (fun h => eO_ne_eN _ _ _ h.symm)
  -- claim B: some digon lies on the other side
  obtain ⟨d0, hd0, hD0, hu0⟩ : ∃ d, P d ∧ D d ∧ S (dU d) ≠ b0 := by
    rcases dig_cases f1 with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
    · have hd := (set_eO P d).1 c1.1
      have h2 := c1.2
      by_cases hD : D d
      · rw [ends_eO_D hD, hb0 _ (ends_meets1 hd)] at h2
        exact ⟨d, hd, hD, fun h => h2 h.symm⟩
      · rw [ends_eO_nD hD, hb0 _ (ends_meets1 hd), hb0 _ (ends_meets2 hd)] at h2
        exact absurd rfl h2
    · obtain ⟨hd, hD⟩ := (set_eN P d k).1 c1.1
      have h2 := c1.2
      rcases k_cases k with rfl | hk
      · rw [ends_eN2, hb0 _ (ends_meets2 hd)] at h2
        exact ⟨d, hd, hD, by rw [claimA d hd hD]; exact h2⟩
      · rw [ends_eN01 d k hk] at h2
        exact absurd (claimA d hd hD) h2
  -- claim C: it is the only one
  have claimC : ∀ d, P d → D d → S (dU d) ≠ b0 → d = d0 := by
    intro d hd hD hu
    by_contra hne'
    have x0 : RH2F.Crosses (digSet P D) S (eO d0) :=
      cr _ ((set_eO P d0).2 hd0) (by rw [ends_eO_D hD0, hb0 _ (ends_meets1 hd0)]; exact fun h => hu0 h.symm)
    have x1 : RH2F.Crosses (digSet P D) S (eN d0 2) :=
      cr _ ((set_eN P d0 2).2 ⟨hd0, hD0⟩) (by
        rw [ends_eN2, hb0 _ (ends_meets2 hd0), ← claimA d0 hd0 hD0]; exact hu0)
    have x2 : RH2F.Crosses (digSet P D) S (eO d) :=
      cr _ ((set_eO P d).2 hd) (by rw [ends_eO_D hD, hb0 _ (ends_meets1 hd)]; exact fun h => hu h.symm)
    exact no3 _ _ _ x0 x1 x2 (eO_ne_eN _ _ _) (fun h => hne' (eO_inj h).symm) (fun h => eO_ne_eN _ _ _ h.symm)
  -- the side of `u_{d0}` consists of `u_{d0}` and `v_{d0}`
  have hside : ∀ w, (meets (digSet P D) w ∧ S w = S (dU d0)) ↔ (w = dU d0 ∨ w = dV d0) := by
    intro w
    constructor
    · rintro ⟨hm, hs⟩
      rcases vert_cases w with ⟨x, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · rw [hb0 x ((meets_dig_dO hG.1 x).1 hm)] at hs; exact absurd hs.symm hu0
      · obtain ⟨hd, hD⟩ := (meets_dig_dU d).1 hm
        exact Or.inl (by rw [claimC d hd hD (by rw [hs]; exact hu0)])
      · obtain ⟨hd, hD⟩ := (meets_dig_dV d).1 hm
        exact Or.inr (by rw [claimC d hd hD (by rw [claimA d hd hD, hs]; exact hu0)])
    · rintro (rfl | rfl)
      · exact ⟨(meets_dig_dU d0).2 ⟨hd0, hD0⟩, rfl⟩
      · exact ⟨(meets_dig_dV d0).2 ⟨hd0, hD0⟩, (claimA d0 hd0 hD0).symm⟩
  have hcnt : scount (digSet P D) S (S (dU d0)) = 2 := by
    unfold scount
    rw [cntF_congr _ _ _ hside]
    exact cntF_pair _ (dU_ne_dV _ _)
  cases h : S (dU d0)
  · rw [h] at hcnt; exact Or.inr hcnt
  · rw [h] at hcnt; exact Or.inl hcnt

end digthm

section classes
variable {X : MGraph}

/-- exactly three distinct edges of `P` cross `S` -/
def ThreeCut (P : Fin X.m → Prop) (S : Fin X.n → Bool) : Prop :=
  ∃ e1 e2 e3, e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3 ∧ RH2F.Crosses P S e1 ∧ RH2F.Crosses P S e2 ∧ RH2F.Crosses P S e3 ∧
    ∀ d, RH2F.Crosses P S d → d = e1 ∨ d = e2 ∨ d = e3

/-- `P ∈ 𝒮`: a simple 3-edge-connected cubic multigraph (connected, bridgeless, no 2-edge-cut) -/
def InS (X : MGraph) (P : Fin X.m → Prop) : Prop := InG X P ∧ SimpleP P ∧ ∀ S, ¬ TwoCut P S

/-- `P` is cyclically 4-edge-connected (cut form, for cubic multigraphs): a member of 𝒢 without 2-edge-cuts all of
    whose 3-edge-cuts have a side with one vertex -/
def C4C (X : MGraph) (P : Fin X.m → Prop) : Prop :=
  InG X P ∧ (∀ S, ¬ TwoCut P S) ∧ ∀ S, ThreeCut P S → scount P S true = 1 ∨ scount P S false = 1

/-- `(C4C-DOM-D)₁₀`, in the strong form: for every c4c `P` on at least 10 vertices, every `D` and every vertex `v` of
    `P^D` whose three edges join it to three distinct vertices, the pole `Q(P^D, v)` is dominant -/
def C4CDOMD10 : Prop :=
  ∀ (X : MGraph) (P : Fin X.m → Prop), C4C X P → 10 ≤ vcount P → ∀ (D : Fin X.m → Prop) (v : Fin (digG X D).n)
    (Dp : Ports (digSet P D) v), Dominant Dp

/-- **H-ASM (a), forward**: for `P` with no 2-edge-cut in 𝒢 (in particular `P ∈ 𝒮`) and every `D`, `P^D ∈ 𝒢`, it is
    2-cut-reduced and has `|V(P)| + 2 |P ∩ D|` vertices -/
theorem dig_class {P : Fin X.m → Prop} (hG : InG X P) (h3 : ∀ S, ¬ TwoCut P S) (D : Fin X.m → Prop) :
    InG (digG X D) (digSet P D) ∧ TwoCutReducedOn (digSet P D) ∧
      vcount (digSet P D) = vcount P + 2 * cntF X.m (fun d => P d ∧ D d) :=
  ⟨⟨dig_loopless hG.1, dig_connected hG.2.1, dig_bridgeless hG.2.2.1, dig_cubic hG.1 hG.2.2.2⟩,
   dig_2cr hG h3, vcount_dig hG.1⟩

/-- **H-RED13 (a)**: (POLE) implies (C4C-DOM-D)₁₀ -/
theorem hred13a (hpole : POLE) : C4CDOMD10 := by
  intro X P hc h10 D v Dp
  obtain ⟨hG, h2r, hcnt⟩ := dig_class hc.1 hc.2.1 D
  exact hpole _ _ hG (by rw [hcnt]; omega) h2r v Dp

end classes

end RH2F


/-
  IV3.lean — cycles in edge sets, and the equivalence of the cut form `C4C` of cyclic 4-edge-connectivity with the
  prose definition (connected; for every set R of at most three edges, at most one component of X − R contains a
  cycle) for loopless cubic multigraphs.
-/

namespace RH2F
open MGraph
open Classical

section cycles
variable {X : MGraph}

/-- the successor of an index of a cycle of length `k + 2` -/
def nx {k : Nat} (i : Fin (k + 2)) : Fin (k + 2) := ⟨(i.val + 1) % (k + 2), Nat.mod_lt _ (by omega)⟩

/-- `Q` contains a cycle: `k + 2 ≥ 2` pairwise distinct vertices `v i` and pairwise distinct edges `e i` of `Q`, the
    edge `e i` joining `v i` and `v (i + 1)` (indices modulo `k + 2`) -/
def HasCycle (Q : Fin X.m → Prop) : Prop :=
  ∃ (k : Nat) (v : Fin (k + 2) → Fin X.n) (e : Fin (k + 2) → Fin X.m), (∀ i j, v i = v j → i = j) ∧
    (∀ i j, e i = e j → i = j) ∧ ∀ i, Q (e i) ∧ X.Joins (e i) (v i) (v (nx i))

theorem hasCycle_mono {Q Q' : Fin X.m → Prop} (h : ∀ f, Q f → Q' f) (hc : HasCycle Q) : HasCycle Q' := by
  obtain ⟨k, v, e, hv, he, hq⟩ := hc
  exact ⟨k, v, e, hv, he, fun i => ⟨h _ (hq i).1, (hq i).2⟩⟩

/-! ### minimum degree two gives a cycle (a no-return walk and the pigeonhole principle) -/

section walk
variable (Q : Fin X.m → Prop) (h2 : ∀ v f, Q f → X.Inc f v → ∃ g, Q g ∧ X.Inc g v ∧ g ≠ f)

/-- one step of the no-return walk: leave the current vertex along another edge of `Q` -/
noncomputable def nxt (st : Fin X.n × Fin X.m) : Fin X.n × Fin X.m :=
  if h : Q st.2 ∧ X.Inc st.2 st.1 then
    (other (Classical.choose (h2 _ _ h.1 h.2)) st.1, Classical.choose (h2 _ _ h.1 h.2))
  else st

/-- the no-return walk from the second end of `f0` -/
noncomputable def wk (f0 : Fin X.m) : Nat → Fin X.n × Fin X.m
  | 0 => ((X.ends f0).2, f0)
  | t + 1 => nxt Q h2 (wk f0 t)

theorem nxt_spec {st : Fin X.n × Fin X.m} (h : Q st.2 ∧ X.Inc st.2 st.1) :
    Q (nxt Q h2 st).2 ∧ X.Inc (nxt Q h2 st).2 (nxt Q h2 st).1 ∧ (nxt Q h2 st).2 ≠ st.2 ∧
      X.Joins (nxt Q h2 st).2 st.1 (nxt Q h2 st).1 := by
  unfold nxt
  rw [dif_pos h]
  obtain ⟨hq, hi, hne⟩ := Classical.choose_spec (h2 _ _ h.1 h.2)
  have hj := joins_other hi
  exact ⟨hq, joins_inc_right hj, hne, hj⟩

theorem wk_inv {f0 : Fin X.m} (hf0 : Q f0) : ∀ t, Q (wk Q h2 f0 t).2 ∧ X.Inc (wk Q h2 f0 t).2 (wk Q h2 f0 t).1
  | 0 => ⟨hf0, Or.inr rfl⟩
  | t + 1 => by
    have := nxt_spec Q h2 (wk_inv hf0 t)
    exact ⟨this.1, this.2.1⟩

theorem wk_step {f0 : Fin X.m} (hf0 : Q f0) (t : Nat) :
    (wk Q h2 f0 (t + 1)).2 ≠ (wk Q h2 f0 t).2 ∧
      X.Joins (wk Q h2 f0 (t + 1)).2 (wk Q h2 f0 t).1 (wk Q h2 f0 (t + 1)).1 := by
  have := nxt_spec Q h2 (wk_inv Q h2 hf0 t)
  exact ⟨this.2.2.1, this.2.2.2⟩

end walk

/-- **minimum degree two gives a cycle** -/
theorem hasCycle_of_deg2 (hloop : Loopless X) {Q : Fin X.m → Prop} {f0 : Fin X.m} (hf0 : Q f0)
    (h2 : ∀ v f, Q f → X.Inc f v → ∃ g, Q g ∧ X.Inc g v ∧ g ≠ f) : HasCycle Q := by
  let w : Nat → Fin X.n := fun t => (wk Q h2 f0 t).1
  -- a repetition among the first `X.n + 1` vertices
  have hex : ∃ j, ∃ i < j, w i = w j := by
    obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (X.n + 1) => w t.val)
      (by simp)
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact ⟨b.val, a.val, h, heq⟩
    · exact ⟨a.val, b.val, h, heq.symm⟩
  let j0 := Nat.find hex
  obtain ⟨i0, hi0, hw0⟩ := Nat.find_spec hex
  have hinj : ∀ a b, a < j0 → b < j0 → w a = w b → a = b := by
    intro a b ha hb hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Nat.find_min hex hb ⟨a, h, hab⟩
    · exact Nat.find_min hex ha ⟨b, h, hab.symm⟩
  -- the cycle has length `L = j0 - i0 ≥ 2`
  have hL : 2 ≤ j0 - i0 := by
    by_contra h
    have h1 : j0 = i0 + 1 := by omega
    have hj := (wk_step Q h2 hf0 i0).2
    rw [← h1] at hj
    have : (X.ends (wk Q h2 f0 j0).2).1 ≠ (X.ends (wk Q h2 f0 j0).2).2 := hloop _
    apply this
    rcases hj with hj | hj <;> rw [hj] <;> simp only <;> first | exact hw0 | exact hw0.symm
  obtain ⟨k, hk⟩ : ∃ k, j0 - i0 = k + 2 := ⟨j0 - i0 - 2, by omega⟩
  let v : Fin (k + 2) → Fin X.n := fun r => w (i0 + r.val)
  let e : Fin (k + 2) → Fin X.m := fun r => (wk Q h2 f0 (i0 + r.val + 1)).2
  have hv : ∀ r s : Fin (k + 2), v r = v s → r = s := fun r s h =>
    Fin.ext (by have := hinj _ _ (by omega) (by omega) h; omega)
  have hjoin : ∀ r : Fin (k + 2), X.Joins (e r) (v r) (v (nx r)) := by
    intro r
    have hj := (wk_step Q h2 hf0 (i0 + r.val)).2
    have hnx : v (nx r) = w (i0 + r.val + 1) := by
      simp only [v, nx]
      by_cases hr : r.val + 1 < k + 2
      · rw [Nat.mod_eq_of_lt hr]; rfl
      · have : r.val + 1 = k + 2 := by omega
        rw [this, Nat.mod_self, Nat.add_zero, show i0 + r.val + 1 = j0 by omega]
        exact hw0
    rw [hnx]; exact hj
  refine ⟨k, v, e, hv, fun r s hrs => ?_, fun r => ⟨(wk_inv Q h2 hf0 _).1, hjoin r⟩⟩
  -- distinct edges: equal edges have the same pair of ends
  refine Classical.byContradiction fun hne => ?_
  rcases joins_unique (hjoin r) (hrs ▸ hjoin s) with ⟨h1, _⟩ | ⟨h1, h2'⟩
  · exact hne (hv _ _ h1)
  · have e1 := hv _ _ h1
    have e2 := hv _ _ h2'
    -- `r = s + 1` and `s = r + 1` modulo `k + 2`: the cycle has length 2 and `e r`, `e s` are consecutive
    have hr := congrArg Fin.val e1
    have hs := congrArg Fin.val e2
    simp only [nx] at hr hs
    have hk0 : k = 0 := by
      have := r.isLt; have := s.isLt
      rcases Nat.lt_or_ge (s.val + 1) (k + 2) with h | h <;> rcases Nat.lt_or_ge (r.val + 1) (k + 2) with h' | h'
      · rw [Nat.mod_eq_of_lt h] at hr; rw [Nat.mod_eq_of_lt h'] at hs; omega
      · rw [Nat.mod_eq_of_lt h] at hr
        rw [show r.val + 1 = k + 2 by omega, Nat.mod_self] at hs; omega
      · rw [show s.val + 1 = k + 2 by omega, Nat.mod_self] at hr
        rw [Nat.mod_eq_of_lt h'] at hs; omega
      · omega
    subst hk0
    have := r.isLt; have := s.isLt
    have hrs' : r.val ≠ s.val := fun h => hne (Fin.ext h)
    -- the two edges are consecutive steps of the walk
    rcases Nat.lt_or_gt_of_ne hrs' with h | h
    · have hr0 : r.val = 0 := by omega
      have hs1 : s.val = 1 := by omega
      have := (wk_step Q h2 hf0 (i0 + 1)).1
      apply this
      have hrs2 : e s = e r := hrs.symm
      simp only [e, hr0, hs1] at hrs2
      exact hrs2
    · have hr1 : r.val = 1 := by omega
      have hs0 : s.val = 0 := by omega
      have := (wk_step Q h2 hf0 (i0 + 1)).1
      apply this
      simp only [e, hr1, hs0] at hrs
      exact hrs

/-! ### at least as many edges as vertices gives a cycle -/

theorem two_le_vcount (hloop : Loopless X) {Q : Fin X.m → Prop} {f : Fin X.m} (hf : Q f) : 2 ≤ vcount Q := by
  unfold vcount
  have h := cntF_pair X.n (hloop f)
  rw [← h]
  apply cntF_mono
  rintro w (rfl | rfl)
  · exact ⟨f, hf, Or.inl rfl⟩
  · exact ⟨f, hf, Or.inr rfl⟩

theorem hasCycle_of_count (hloop : Loopless X) :
    ∀ (n : Nat) (Q : Fin X.m → Prop), cntF X.m Q = n → 1 ≤ n → vcount Q ≤ n → HasCycle Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hn h1 hv
  by_cases hdeg : ∀ v f, Q f → X.Inc f v → ∃ g, Q g ∧ X.Inc g v ∧ g ≠ f
  · obtain ⟨f0, hf0⟩ := cntF_pos X.m Q (by omega)
    exact hasCycle_of_deg2 hloop hf0 hdeg
  · push_neg at hdeg
    obtain ⟨v, f, hf, hfv, huniq⟩ := hdeg
    let Q' : Fin X.m → Prop := fun g => Q g ∧ g ≠ f
    have hcnt : cntF X.m Q' + 1 = n := by
      rw [← hn, cntF_split X.m Q (fun g => g ≠ f)]
      congr 1
      rw [← cntF_single X.m f]
      apply cntF_congr
      intro g
      constructor
      · rintro rfl; exact ⟨hf, fun h => h rfl⟩
      · rintro ⟨_, h⟩; exact not_not.1 h
    have hvc : vcount Q' + 1 ≤ vcount Q := by
      unfold vcount
      rw [cntF_split X.n (meets Q) (fun w => w = v)]
      have e1 : cntF X.n (fun w => meets Q w ∧ w = v) = 1 := by
        rw [← cntF_single X.n v]
        apply cntF_congr
        intro w
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro rfl; exact ⟨⟨f, hf, hfv⟩, rfl⟩
      have e2 : cntF X.n (meets Q') ≤ cntF X.n (fun w => meets Q w ∧ ¬ w = v) := by
        apply cntF_mono
        rintro w ⟨g, ⟨hg, hgf⟩, hgw⟩
        refine ⟨⟨g, hg, hgw⟩, ?_⟩
        rintro rfl
        exact hgf (huniq g hg hgw)
      omega
    by_cases hn1 : n = 1
    · subst hn1
      have := two_le_vcount hloop hf
      omega
    · have hc := ih (n - 1) (by omega) Q' (by omega) (by omega) (by omega)
      exact hasCycle_mono (fun g hg => hg.1) hc

/-! ### the handshake count on one side of a cut of a cubic edge set -/

/-- the edges of `P` with both ends on side `b` of `S` -/
def inner (P : Fin X.m → Prop) (S : Fin X.n → Bool) (b : Bool) : Fin X.m → Prop :=
  fun f => P f ∧ S (X.ends f).1 = b ∧ S (X.ends f).2 = b

theorem side_handshake (hloop : Loopless X) {P : Fin X.m → Prop} (hcub : CubicOn P) (S : Fin X.n → Bool) (b : Bool) :
    3 * scount P S b = 2 * cntF X.m (inner P S b) + cntF X.m (RH2F.Crosses P S) := by
  -- double counting of the incidences `(v, f)` with `v` on side `b`, `f ∈ P` at `v`
  let I : Fin X.n → Fin X.m → Prop := fun v f => (meets P v ∧ S v = b) ∧ P f ∧ X.Inc f v
  have hv : ∀ v, (Finset.univ.filter (fun f => I v f)).card = if meets P v ∧ S v = b then 3 else 0 := by
    intro v
    by_cases hw : meets P v ∧ S v = b
    · rw [if_pos hw]
      obtain ⟨a, b', c, ha, hb, hc, iav, ibv, icv, dab, dac, dbc, hall⟩ := hcub v hw.1
      apply Finset.card_eq_three.2
      refine ⟨a, b', c, dab, dac, dbc, ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, I]
      constructor
      · rintro ⟨_, hf, hfv⟩; exact hall f hf hfv
      · rintro (rfl | rfl | rfl)
        · exact ⟨hw, ha, iav⟩
        · exact ⟨hw, hb, ibv⟩
        · exact ⟨hw, hc, icv⟩
    · rw [if_neg hw]
      apply Finset.card_eq_zero.2
      apply Finset.filter_false_of_mem
      intro f _ h; exact hw h.1
  have hf : ∀ f, (Finset.univ.filter (fun v => I v f)).card =
      (if inner P S b f then 2 else 0) + (if RH2F.Crosses P S f then 1 else 0) := by
    intro f
    by_cases hP : P f
    · have hne : (X.ends f).1 ≠ (X.ends f).2 := hloop f
      have hset : Finset.univ.filter (fun v => I v f) =
          (if S (X.ends f).1 = b then {(X.ends f).1} else ∅) ∪ (if S (X.ends f).2 = b then {(X.ends f).2} else ∅) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, I]
        constructor
        · rintro ⟨⟨_, hs⟩, _, hv'⟩
          rcases hv' with h | h
          · left; rw [if_pos (by rw [h]; exact hs)]; exact Finset.mem_singleton.2 h.symm
          · right; rw [if_pos (by rw [h]; exact hs)]; exact Finset.mem_singleton.2 h.symm
        · rintro (h | h)
          · split_ifs at h with h1
            · rw [Finset.mem_singleton.1 h]; exact ⟨⟨⟨f, hP, Or.inl rfl⟩, h1⟩, hP, Or.inl rfl⟩
            · simp at h
          · split_ifs at h with h1
            · rw [Finset.mem_singleton.1 h]; exact ⟨⟨⟨f, hP, Or.inr rfl⟩, h1⟩, hP, Or.inr rfl⟩
            · simp at h
      rw [hset]
      unfold inner RH2F.Crosses
      by_cases h1 : S (X.ends f).1 = b <;> by_cases h2 : S (X.ends f).2 = b
      · rw [if_pos h1, if_pos h2, Finset.card_union_of_disjoint (Finset.disjoint_singleton.2 hne), if_pos ⟨hP, h1, h2⟩,
          if_neg (fun h => h.2 (h1.trans h2.symm))]; simp
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2.2), if_pos ⟨hP, fun h => h2 (h ▸ h1)⟩]; simp
      · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.2.1), if_pos ⟨hP, fun h => h1 (h.symm ▸ h2)⟩]; simp
      · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.2.1)]
        have : ¬ (P f ∧ S (X.ends f).1 ≠ S (X.ends f).2) := by
          rintro ⟨_, h⟩
          cases hb : b <;> cases h3 : S (X.ends f).1 <;> cases h4 : S (X.ends f).2 <;> simp_all
        rw [if_neg this]; simp
    · have e1 : Finset.univ.filter (fun v => I v f) = ∅ := by
        apply Finset.filter_false_of_mem; intro v _ h; exact hP h.2.1
      rw [e1, if_neg (fun h => hP h.1), if_neg (fun h => hP h.1)]; rfl
  -- the two counts of the incidences
  have hsum := Finset.sum_comm (s := (Finset.univ : Finset (Fin X.n))) (t := (Finset.univ : Finset (Fin X.m)))
    (f := fun v f => if I v f then 1 else 0)
  have hv' : ∀ v, ∑ f : Fin X.m, (if I v f then 1 else 0) = if meets P v ∧ S v = b then 3 else 0 := fun v => by
    rw [← hv v, Finset.card_filter]
  have hf' : ∀ f, ∑ v : Fin X.n, (if I v f then 1 else 0) =
      (if inner P S b f then 2 else 0) + (if RH2F.Crosses P S f then 1 else 0) := fun f => by
    rw [← hf f, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun v _ => hv' v), Finset.sum_congr rfl (fun f _ => hf' f)] at hsum
  unfold scount
  rw [cntF_eq_card, cntF_eq_card, cntF_eq_card, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [Finset.sum_add_distrib] at hsum
  have e3 : ∑ v : Fin X.n, (if meets P v ∧ S v = b then 3 else 0) = 3 * ∑ v : Fin X.n, (if meets P v ∧ S v = b then 1 else 0) := by
    rw [Finset.mul_sum]; congr 1; ext v; split_ifs <;> rfl
  have e2 : ∑ f : Fin X.m, (if inner P S b f then 2 else 0) = 2 * ∑ f : Fin X.m, (if inner P S b f then 1 else 0) := by
    rw [Finset.mul_sum]; congr 1; ext f; split_ifs <;> rfl
  rw [e3, e2] at hsum
  convert hsum using 4

end cycles

section c4c
variable {X : MGraph}

/-- **c4c, prose form**: `P` is connected, and for every set `R` of at most three edges, at most one component of
    `P − R` contains a cycle, i.e. no vertex 2-colouring that is constant on the ends of every edge of `P − R` has a
    cycle of `P − R` on each side -/
def C4Cc (X : MGraph) (P : Fin X.m → Prop) : Prop :=
  ConnectedOn P ∧ ∀ (R : Fin X.m → Prop), (∃ r1 r2 r3, ∀ f, R f → f = r1 ∨ f = r2 ∨ f = r3) →
    ∀ U : Fin X.n → Bool, (∀ f, P f → ¬ R f → U (X.ends f).1 = U (X.ends f).2) →
      ¬ (HasCycle (fun f => P f ∧ ¬ R f ∧ U (X.ends f).1 = true) ∧
         HasCycle (fun f => P f ∧ ¬ R f ∧ U (X.ends f).1 = false))

theorem cntF_triple (n : Nat) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cntF n (fun k => k = a ∨ k = b ∨ k = c) = 3 := by
  rw [cntF_split n _ (fun k => k = c)]
  have e1 : cntF n (fun k => (k = a ∨ k = b ∨ k = c) ∧ k = c) = 1 := by
    rw [← cntF_single n c]; apply cntF_congr; intro k
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; exact ⟨Or.inr (Or.inr rfl), rfl⟩
  have e2 : cntF n (fun k => (k = a ∨ k = b ∨ k = c) ∧ ¬ k = c) = 2 := by
    rw [← cntF_pair n hab]; apply cntF_congr; intro k
    constructor
    · rintro ⟨h | h | h, h'⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hac⟩
      · exact ⟨Or.inr (Or.inl rfl), hbc⟩
  omega

/-- a cycle of `P` all of whose edges have their first end on side `b` (and constant ends) gives two vertices on
    side `b` -/
theorem two_le_side {P Q : Fin X.m → Prop} {U : Fin X.n → Bool} {b : Bool}
    (hQ : ∀ f, Q f → P f ∧ U (X.ends f).1 = b ∧ U (X.ends f).2 = b) (hc : HasCycle Q) : 2 ≤ scount P U b := by
  obtain ⟨k, v, e, hv, _, hq⟩ := hc
  have h01 : v 0 ≠ v 1 := fun h => by have := congrArg Fin.val (hv _ _ h); simp at this
  have side : ∀ i, meets P (v i) ∧ U (v i) = b := by
    intro i
    obtain ⟨hPe, h1, h2⟩ := hQ _ (hq i).1
    refine ⟨⟨e i, hPe, joins_inc_left (hq i).2⟩, ?_⟩
    rcases (hq i).2 with h | h <;> rw [h] at h1 h2
    · exact h1
    · exact h2
  unfold scount
  rw [← cntF_pair X.n h01]
  apply cntF_mono
  rintro w (rfl | rfl)
  · exact side 0
  · exact side 1

theorem cycle_const {P R : Fin X.m → Prop} {U : Fin X.n → Bool} (hU : ∀ f, P f → ¬ R f → U (X.ends f).1 = U (X.ends f).2)
    (b : Bool) : ∀ f, (P f ∧ ¬ R f ∧ U (X.ends f).1 = b) → P f ∧ U (X.ends f).1 = b ∧ U (X.ends f).2 = b :=
  fun f ⟨hP, hR, h1⟩ => ⟨hP, h1, (hU f hP hR) ▸ h1⟩

theorem side_nonempty {P : Fin X.m → Prop} {S : Fin X.n → Bool} {e : Fin X.m} (he : RH2F.Crosses P S e) (b : Bool) :
    1 ≤ scount P S b := by
  obtain ⟨hP, hne⟩ := he
  unfold scount
  by_cases h : S (X.ends e).1 = b
  · exact cntF_le_of_mem X.n _ (i := (X.ends e).1) ⟨⟨e, hP, Or.inl rfl⟩, h⟩
  · have h2 : S (X.ends e).2 = b := by
      cases hb : b <;> cases h3 : S (X.ends e).1 <;> cases h4 : S (X.ends e).2 <;> simp_all
    exact cntF_le_of_mem X.n _ (i := (X.ends e).2) ⟨⟨e, hP, Or.inr rfl⟩, h2⟩

/-- both sides of a cut crossed by `c ≥ 1` edges of a loopless cubic `P` contain a cycle if each has at least `c`
    vertices -/
theorem both_cyc (hloop : Loopless X) {P : Fin X.m → Prop} (hcub : CubicOn P) (S : Fin X.n → Bool) (c : Nat)
    (hc : cntF X.m (RH2F.Crosses P S) = c) (hc1 : 1 ≤ c) (hn : ∀ b, c ≤ scount P S b) (b : Bool) :
    HasCycle (inner P S b) := by
  have hh := side_handshake hloop hcub S b
  have hvb : vcount (inner P S b) ≤ scount P S b := by
    unfold vcount scount
    apply cntF_mono
    rintro w ⟨f, ⟨hP, h1, h2⟩, hw⟩
    refine ⟨⟨f, hP, hw⟩, ?_⟩
    rcases hw with h | h
    · rw [← h]; exact h1
    · rw [← h]; exact h2
  have := hn b
  exact hasCycle_of_count hloop _ (inner P S b) rfl (by omega) (by omega)

/-- **the cut form of cyclic 4-edge-connectivity is the prose form** (for loopless cubic edge sets) -/
theorem c4c_iff (hloop : Loopless X) {P : Fin X.m → Prop} (hcub : CubicOn P) : C4C X P ↔ C4Cc X P := by
  constructor
  · rintro ⟨hG, h2c, h3c⟩
    refine ⟨hG.2.1, ?_⟩
    rintro R ⟨r1, r2, r3, hR⟩ U hU ⟨cT, cF⟩
    have hcr : ∀ f, RH2F.Crosses P U f → f = r1 ∨ f = r2 ∨ f = r3 := fun f hf =>
      hR f (Classical.byContradiction fun hr => hf.2 (hU f hf.1 hr))
    have nT := two_le_side (cycle_const hU true) cT
    have nF := two_le_side (cycle_const hU false) cF
    by_cases h0 : ∃ a, RH2F.Crosses P U a
    · obtain ⟨a, ha⟩ := h0
      by_cases h1 : ∃ b, RH2F.Crosses P U b ∧ b ≠ a
      · obtain ⟨b, hb, hba⟩ := h1
        by_cases h2 : ∃ c, RH2F.Crosses P U c ∧ c ≠ a ∧ c ≠ b
        · obtain ⟨c, hc, hca, hcb⟩ := h2
          have h3 : ThreeCut P U := by
            refine ⟨a, b, c, hba.symm, hca.symm, hcb.symm, ha, hb, hc, fun d hd => ?_⟩
            have hd' := hcr d hd; have ha' := hcr a ha; have hb' := hcr b hb; have hc' := hcr c hc
            rcases hd' with rfl | rfl | rfl <;> rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
              rcases hc' with rfl | rfl | rfl <;> simp_all
          rcases h3c U h3 with h | h <;> omega
        · push_neg at h2
          exact h2c U ⟨a, b, hba.symm, ha, hb, fun d hd => by
            by_contra h; push_neg at h; exact absurd (h2 d hd h.1) h.2⟩
      · push_neg at h1
        apply hG.2.2.1 a ha.1
        exact { U := fun v => decide (U v = U (X.ends a).1)
                hu := by simp
                hv := by simp only [decide_eq_false_iff_not]; exact fun h => ha.2 h.symm
                sep := fun g hg hga => by
                  have : U (X.ends g).1 = U (X.ends g).2 := by
                    by_contra h; exact hga (h1 g ⟨hg, h⟩)
                  simp only [this] }
    · push_neg at h0
      have hc := hG.2.1 U (fun f hf => by by_contra h; exact h0 f ⟨hf, h⟩)
      obtain ⟨k, v, e, _, _, hq⟩ := cT
      obtain ⟨k', v', e', _, _, hq'⟩ := cF
      have := hc (e 0) (e' 0) (hq 0).1.1 (hq' 0).1.1
      rw [(hq 0).1.2.2, (hq' 0).1.2.2] at this
      exact Bool.noConfusion this
  · rintro ⟨hconn, hC⟩
    -- a small cut with cycles on both sides is impossible
    have no_small : ∀ S (r1 r2 r3 : Fin X.m), (∀ f, RH2F.Crosses P S f → f = r1 ∨ f = r2 ∨ f = r3) →
        HasCycle (inner P S true) → HasCycle (inner P S false) → False := by
      intro S r1 r2 r3 hr cT cF
      apply hC (RH2F.Crosses P S) ⟨r1, r2, r3, hr⟩ S (fun f hf hn => by by_contra h; exact hn ⟨hf, h⟩)
      refine ⟨hasCycle_mono (fun f hf => ⟨hf.1, fun h => h.2 (hf.2.1.trans hf.2.2.symm), hf.2.1⟩) cT,
        hasCycle_mono (fun f hf => ⟨hf.1, fun h => h.2 (hf.2.1.trans hf.2.2.symm), hf.2.1⟩) cF⟩
    have hbr : BridgelessOn P := by
      intro e he B
      have hcr : ∀ f, RH2F.Crosses P B.U f ↔ f = e := by
        intro f
        constructor
        · rintro ⟨hf, hne⟩; by_contra h; exact hne (B.sep f hf h)
        · rintro rfl; exact ⟨he, by rw [B.hu, B.hv]; decide⟩
      have hc : cntF X.m (RH2F.Crosses P B.U) = 1 := by
        rw [cntF_congr _ _ _ hcr, cntF_single]
      have hx := (hcr e).2 rfl
      have hn : ∀ b, 1 ≤ scount P B.U b := fun b => side_nonempty hx b
      exact no_small B.U e e e (fun f hf => Or.inl ((hcr f).1 hf))
        (both_cyc hloop hcub _ 1 hc le_rfl hn true) (both_cyc hloop hcub _ 1 hc le_rfl hn false)
    have h2c : ∀ S, ¬ TwoCut P S := by
      rintro S ⟨e1, e2, hne, c1, c2, hall⟩
      have hc : cntF X.m (RH2F.Crosses P S) = 2 := by
        rw [← cntF_pair X.m hne]; apply cntF_congr; intro f
        constructor
        · exact hall f
        · rintro (rfl | rfl)
          · exact c1
          · exact c2
      have hn : ∀ b, 2 ≤ scount P S b := by
        intro b
        have hh := side_handshake hloop hcub S b
        have := side_nonempty c1 b
        omega
      exact no_small S e1 e2 e2 (fun f hf => (hall f hf).imp id Or.inl)
        (both_cyc hloop hcub _ 2 hc (by decide) hn true) (both_cyc hloop hcub _ 2 hc (by decide) hn false)
    refine ⟨⟨hloop, hconn, hbr, hcub⟩, h2c, ?_⟩
    rintro S ⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hall⟩
    by_contra hcon
    push_neg at hcon
    have hc : cntF X.m (RH2F.Crosses P S) = 3 := by
      rw [← cntF_triple X.m d12 d13 d23]; apply cntF_congr; intro f
      constructor
      · exact hall f
      · rintro (rfl | rfl | rfl)
        · exact c1
        · exact c2
        · exact c3
    have hn : ∀ b, 3 ≤ scount P S b := by
      intro b
      have hh := side_handshake hloop hcub S b
      have := side_nonempty c1 b
      have hb1 : scount P S b ≠ 1 := by cases b; exact hcon.2; exact hcon.1
      omega
    exact no_small S e1 e2 e3 hall (both_cyc hloop hcub _ 3 hc (by decide) hn true)
      (both_cyc hloop hcub _ 3 hc (by decide) hn false)

end c4c


end RH2F

namespace RH2F
open MGraph

/-- **Layer 16 of the Lean formalization** (digon layer): H-ASM (fact fdd83999b9ec10e2) (a), forward direction, for
    every edge set without 2-edge-cuts in 𝒢 (in particular for 𝒮); the cut form `C4C` of cyclic 4-edge-connectivity
    is the prose definition `C4Cc`; and H-RED13 (fact da66a84c773b73b3) (a): (POLE) implies (C4C-DOM-D)₁₀. -/
theorem layer16 :
    (∀ (X : MGraph) (P : Fin X.m → Prop), InG X P → (∀ S, ¬ TwoCut P S) → ∀ D : Fin X.m → Prop,
      InG (digG X D) (digSet P D) ∧ TwoCutReducedOn (digSet P D) ∧
        vcount (digSet P D) = vcount P + 2 * cntF X.m (fun d => P d ∧ D d)) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop), Loopless X → CubicOn P → (C4C X P ↔ C4Cc X P)) ∧
    (POLE → C4CDOMD10) :=
  ⟨fun _ _ hG h3 D => dig_class hG h3 D, fun _ _ hl hc => c4c_iff hl hc, hred13a⟩

end RH2F
