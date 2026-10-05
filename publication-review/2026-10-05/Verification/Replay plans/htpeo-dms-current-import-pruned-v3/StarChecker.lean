/-
  StarChecker.lean — a verified *efficient* star-colouring checker (incidence lists instead of the 9-fold explicit
  quantification of `StarCert.lean`), in two directions:

    * `starOn_of_check`   : `starCheck G P c = true → StarOn P k c`   — every walk is enumerated through the
                            incidence lists (`mem_incList`, `mem_endsOf_of_joins`), so a passing check is a proof;
    * `not_star_of_walk`, `not_star_of_adj` : an explicit bicoloured walk, or two adjacent equally coloured edges,
                            given as raw numbers and checked by `walkViol` / `adjViol`, refutes `StarOn`.

  Together they let a finite obstruction ("this colouring of the outside is star, and none of the finitely many
  repairs is") be certified by `native_decide` in seconds instead of never.
-/
import StarCert
import StarReduce

namespace MGraph
variable (G : MGraph)

/-! ### incidence lists -/

def incList (x : Fin G.n) : List (Fin G.m) := (List.finRange G.m).filter (fun e => decide (G.Inc e x))

theorem mem_incList {e : Fin G.m} {x : Fin G.n} (h : G.Inc e x) : e ∈ G.incList x := by
  unfold incList
  exact List.mem_filter.2 ⟨mem_finRange' e, decide_eq_true h⟩

def endsOf (e : Fin G.m) : List (Fin G.n) := [(G.ends e).1, (G.ends e).2]

theorem mem_endsOf_of_joins {e : Fin G.m} {x y : Fin G.n} (h : G.Joins e x y) : y ∈ G.endsOf e := by
  unfold endsOf
  rcases h with h | h <;> rw [h] <;> simp

/-! ### the positive checker -/

/-- `true` unless the nine-tuple is a bicoloured `P`-walk -/
def walkOK {k : Nat} (P : Fin G.m → Bool) (c : Fin G.m → Fin k) (v0 v1 v2 v3 v4 : Fin G.n)
    (e1 e2 e3 e4 : Fin G.m) : Bool :=
  !(P e1 && P e2 && P e3 && P e4 &&
    decide (G.Joins e1 v0 v1) && decide (G.Joins e2 v1 v2) && decide (G.Joins e3 v2 v3) &&
    decide (G.Joins e4 v3 v4) &&
    (v0 != v1) && (v0 != v2) && (v0 != v3) && (v1 != v2) && (v1 != v3) && (v1 != v4) && (v2 != v3) &&
    (v2 != v4) && (v3 != v4) && (c e1 == c e3) && (c e2 == c e4))

def properCheck {k : Nat} (P : Fin G.m → Bool) (c : Fin G.m → Fin k) : Bool :=
  (List.finRange G.n).all fun x => (G.incList x).all fun a => (G.incList x).all fun b =>
    (a == b) || !(P a && P b) || (c a != c b)

def walkCheck {k : Nat} (P : Fin G.m → Bool) (c : Fin G.m → Fin k) : Bool :=
  (List.finRange G.n).all fun v0 => (G.incList v0).all fun e1 => (G.endsOf e1).all fun v1 =>
    (G.incList v1).all fun e2 => (G.endsOf e2).all fun v2 => (G.incList v2).all fun e3 =>
      (G.endsOf e3).all fun v3 => (G.incList v3).all fun e4 => (G.endsOf e4).all fun v4 =>
        G.walkOK P c v0 v1 v2 v3 v4 e1 e2 e3 e4

def starCheck {k : Nat} (P : Fin G.m → Bool) (c : Fin G.m → Fin k) : Bool :=
  G.properCheck P c && G.walkCheck P c

theorem starOn_of_check {k : Nat} (P : Fin G.m → Bool) (c : Fin G.m → Fin k) (h : G.starCheck P c = true) :
    StarOn (fun e => P e = true) k c := by
  unfold starCheck at h
  rcases Bool.and_eq_true_iff.1 h with ⟨hp, hw⟩
  constructor
  · intro a b hab ha hb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    unfold properCheck at hp
    have h1 := List.all_eq_true.1 hp x (mem_finRange' x)
    have h2 := List.all_eq_true.1 h1 a (G.mem_incList hax)
    have h3 := List.all_eq_true.1 h2 b (G.mem_incList hbx)
    have e1 : (a == b) = false := beq_eq_false_iff_ne.2 hne
    have e2 : (P a && P b) = true := Bool.and_eq_true_iff.2 ⟨ha, hb⟩
    have e3 : (c a != c b) = false := by rw [heq]; exact bne_self_eq_false _
    rw [e1, e2, e3] at h3
    simp at h3
  · intro w h1 h2 h3 h4 hb
    unfold walkCheck at hw
    have s0 := List.all_eq_true.1 hw w.v0 (mem_finRange' w.v0)
    have s1 := List.all_eq_true.1 s0 w.e1 (G.mem_incList w.inc_e1_v0)
    have s2 := List.all_eq_true.1 s1 w.v1 (G.mem_endsOf_of_joins w.h1)
    have s3 := List.all_eq_true.1 s2 w.e2 (G.mem_incList w.inc_e2_v1)
    have s4 := List.all_eq_true.1 s3 w.v2 (G.mem_endsOf_of_joins w.h2)
    have s5 := List.all_eq_true.1 s4 w.e3 (G.mem_incList w.inc_e3_v2)
    have s6 := List.all_eq_true.1 s5 w.v3 (G.mem_endsOf_of_joins w.h3)
    have s7 := List.all_eq_true.1 s6 w.e4 (G.mem_incList w.inc_e4_v3)
    have s8 := List.all_eq_true.1 s7 w.v4 (G.mem_endsOf_of_joins w.h4)
    unfold walkOK at s8
    rw [Bool.not_eq_true'] at s8
    have : (P w.e1 && P w.e2 && P w.e3 && P w.e4 &&
        decide (G.Joins w.e1 w.v0 w.v1) && decide (G.Joins w.e2 w.v1 w.v2) && decide (G.Joins w.e3 w.v2 w.v3) &&
        decide (G.Joins w.e4 w.v3 w.v4) &&
        (w.v0 != w.v1) && (w.v0 != w.v2) && (w.v0 != w.v3) && (w.v1 != w.v2) && (w.v1 != w.v3) &&
        (w.v1 != w.v4) && (w.v2 != w.v3) && (w.v2 != w.v4) && (w.v3 != w.v4) &&
        (c w.e1 == c w.e3) && (c w.e2 == c w.e4)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, w.h1⟩, w.h2⟩, w.h3⟩, w.h4⟩, w.d01⟩, w.d02⟩, w.d03⟩, w.d12⟩,
        w.d13⟩, w.d14⟩, w.d23⟩, w.d24⟩, w.d34⟩, hb.1⟩, hb.2⟩
    rw [this] at s8
    cases s8

/-- the same for the whole edge set -/
theorem star_of_check {k : Nat} (c : Fin G.m → Fin k) (h : G.starCheck (fun _ => true) c = true) : Star k c :=
  let h' := G.starOn_of_check (fun _ => true) c h
  ⟨fun a b hab _ _ => h'.1 a b hab rfl rfl, fun w _ _ _ _ => h'.2 w rfl rfl rfl rfl⟩

/-! ### the negative checker: explicit violations given as numbers -/

def walkBody {k : Nat} (c : Fin G.m → Fin k) (V0 V1 V2 V3 V4 : Fin G.n) (E1 E2 E3 E4 : Fin G.m) : Bool :=
  decide (G.Joins E1 V0 V1) && decide (G.Joins E2 V1 V2) && decide (G.Joins E3 V2 V3) &&
  decide (G.Joins E4 V3 V4) &&
  (V0 != V1) && (V0 != V2) && (V0 != V3) && (V1 != V2) && (V1 != V3) && (V1 != V4) && (V2 != V3) &&
  (V2 != V4) && (V3 != V4) && (c E1 == c E3) && (c E2 == c E4)

def walkViol {k : Nat} (c : Fin G.m → Fin k) (v0 v1 v2 v3 v4 e1 e2 e3 e4 : Nat) : Bool :=
  if h : v0 < G.n ∧ v1 < G.n ∧ v2 < G.n ∧ v3 < G.n ∧ v4 < G.n ∧ e1 < G.m ∧ e2 < G.m ∧ e3 < G.m ∧ e4 < G.m then
    G.walkBody c ⟨v0, h.1⟩ ⟨v1, h.2.1⟩ ⟨v2, h.2.2.1⟩ ⟨v3, h.2.2.2.1⟩ ⟨v4, h.2.2.2.2.1⟩
      ⟨e1, h.2.2.2.2.2.1⟩ ⟨e2, h.2.2.2.2.2.2.1⟩ ⟨e3, h.2.2.2.2.2.2.2.1⟩ ⟨e4, h.2.2.2.2.2.2.2.2⟩
  else false

theorem not_star_of_walkBody {k : Nat} (c : Fin G.m → Fin k) (V0 V1 V2 V3 V4 : Fin G.n) (E1 E2 E3 E4 : Fin G.m)
    (h : G.walkBody c V0 V1 V2 V3 V4 E1 E2 E3 E4 = true) : ¬ Star k c := by
  intro hs
  unfold walkBody at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨j1, j2⟩, j3⟩, j4⟩, d01⟩, d02⟩, d03⟩, d12⟩, d13⟩, d14⟩, d23⟩, d24⟩, d34⟩, b13⟩, b24⟩ := h
  exact hs.2 ⟨V0, V1, V2, V3, V4, E1, E2, E3, E4, j1, j2, j3, j4, d01, d02, d03, d12, d13, d14, d23, d24, d34⟩
    trivial trivial trivial trivial ⟨b13, b24⟩

theorem not_star_of_walk {k : Nat} (c : Fin G.m → Fin k) (v0 v1 v2 v3 v4 e1 e2 e3 e4 : Nat)
    (h : G.walkViol c v0 v1 v2 v3 v4 e1 e2 e3 e4 = true) : ¬ Star k c := by
  by_cases hlt : v0 < G.n ∧ v1 < G.n ∧ v2 < G.n ∧ v3 < G.n ∧ v4 < G.n ∧ e1 < G.m ∧ e2 < G.m ∧ e3 < G.m ∧ e4 < G.m
  · unfold walkViol at h
    rw [dif_pos hlt] at h
    exact G.not_star_of_walkBody c _ _ _ _ _ _ _ _ _ h
  · unfold walkViol at h
    rw [dif_neg hlt] at h
    cases h

def adjBody {k : Nat} (c : Fin G.m → Fin k) (E F : Fin G.m) (X : Fin G.n) : Bool :=
  (E != F) && decide (G.Inc E X) && decide (G.Inc F X) && (c E == c F)

def adjViol {k : Nat} (c : Fin G.m → Fin k) (e f x : Nat) : Bool :=
  if h : e < G.m ∧ f < G.m ∧ x < G.n then G.adjBody c ⟨e, h.1⟩ ⟨f, h.2.1⟩ ⟨x, h.2.2⟩ else false

theorem not_star_of_adjBody {k : Nat} (c : Fin G.m → Fin k) (E F : Fin G.m) (X : Fin G.n)
    (h : G.adjBody c E F X = true) : ¬ Star k c := by
  intro hs
  unfold adjBody at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hne, hex⟩, hfx⟩, heq⟩ := h
  exact hs.1 E F ⟨hne, X, hex, hfx⟩ trivial trivial heq

theorem not_star_of_adj {k : Nat} (c : Fin G.m → Fin k) (e f x : Nat) (h : G.adjViol c e f x = true) :
    ¬ Star k c := by
  by_cases hlt : e < G.m ∧ f < G.m ∧ x < G.n
  · unfold adjViol at h
    rw [dif_pos hlt] at h
    exact G.not_star_of_adjBody c _ _ _ h
  · unfold adjViol at h
    rw [dif_neg hlt] at h
    cases h

/-- a colouring is refuted by a list of candidate violations if some candidate checks out -/
def refuted {k : Nat} (c : Fin G.m → Fin k) (adjs : List (Nat × Nat × Nat))
    (walks : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)) : Bool :=
  adjs.any (fun t => G.adjViol c t.1 t.2.1 t.2.2) ||
  walks.any (fun t => G.walkViol c t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
    t.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2)

theorem not_star_of_refuted {k : Nat} (c : Fin G.m → Fin k) (adjs) (walks) (h : G.refuted c adjs walks = true) :
    ¬ Star k c := by
  unfold refuted at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain ⟨t, _, ht⟩ := List.any_eq_true.1 h
    exact G.not_star_of_adj c _ _ _ ht
  · obtain ⟨t, _, ht⟩ := List.any_eq_true.1 h
    exact G.not_star_of_walk c _ _ _ _ _ _ _ _ _ ht

end MGraph
