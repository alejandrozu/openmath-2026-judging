-- Lean proof of fact 6c78409a046a3fe7 (RH2Fid.fidelity_bundle); added by fact_submit, do not edit
import MhFact_3e79907cfcc0085b
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
set_option backward.isDefEq.respectTransparency false

/-!
  Statement fidelity of the Lean RH2 theorem `RH2F.rh2_final : RH2F.Hyp → RH2F.II → RH2F.DMS` (fact 3e79907c).

  Part 1: plain definitions, stated for an arbitrary finite multigraph given as a vertex type `V`, an edge type `E`
  and an incidence map `en : E → Sym2 V` (the unordered pair of ends of each edge; parallel edges are distinct
  elements of `E` with the same image; a loop is an edge whose pair is diagonal).  Nothing here uses the library's
  `MGraph` encoding.
-/

namespace RH2Fid
open MGraph
open Classical

section plain
variable {V E : Type} (en : E → Sym2 V)

/-- no edge is a loop -/
def LooplessP : Prop := ∀ e, ¬ (en e).IsDiag

/-- the degree of `x`: the number of edges incident with `x` (for a loopless multigraph) -/
noncomputable def deg [Fintype E] (x : V) : ℕ := (Finset.univ.filter (fun e => x ∈ en e)).card

/-- every vertex has degree at most 3 -/
def MaxDeg3 [Fintype E] : Prop := ∀ x, deg en x ≤ 3

/-- cubic: every vertex is incident with exactly three edges -/
def CubicP [Fintype E] : Prop := ∀ x, deg en x = 3

/-- (i) distinct edges with a common endpoint get different colours -/
def ProperP {K : Type} (c : E → K) : Prop := ∀ e f, e ≠ f → (∃ x, x ∈ en e ∧ x ∈ en f) → c e ≠ c f

/-- a path with exactly 4 edges `e1 e2 e3 e4` on 5 distinct vertices `v0 … v4` (`e_i` joins `v_{i-1}` and `v_i`) -/
def IsPath4 (v0 v1 v2 v3 v4 : V) (e1 e2 e3 e4 : E) : Prop :=
  v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧
  en e1 = s(v0, v1) ∧ en e2 = s(v1, v2) ∧ en e3 = s(v2, v3) ∧ en e4 = s(v3, v4)

/-- a cycle with exactly 4 edges `e1 e2 e3 e4` on 4 distinct vertices `v0 … v3` (`e4` joins `v3` and `v0`) -/
def IsCycle4 (v0 v1 v2 v3 : V) (e1 e2 e3 e4 : E) : Prop :=
  v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
  en e1 = s(v0, v1) ∧ en e2 = s(v1, v2) ∧ en e3 = s(v2, v3) ∧ en e4 = s(v3, v0)

/-- star edge colouring (definition star-edge-colouring@v2): (i) proper, including parallel edges, and (ii) no path
    and no cycle with exactly 4 edges on distinct vertices with `c e1 = c e3` and `c e2 = c e4` -/
def StarP {K : Type} (c : E → K) : Prop :=
  ProperP en c ∧
  (∀ v0 v1 v2 v3 v4 e1 e2 e3 e4, IsPath4 en v0 v1 v2 v3 v4 e1 e2 e3 e4 → ¬ (c e1 = c e3 ∧ c e2 = c e4)) ∧
  (∀ v0 v1 v2 v3 e1 e2 e3 e4, IsCycle4 en v0 v1 v2 v3 e1 e2 e3 e4 → ¬ (c e1 = c e3 ∧ c e2 = c e4))

/-- a star edge colouring with the 6 colours `1, …, 6` exists -/
def Star6P : Prop := ∃ c : E → ℕ, (∀ e, 1 ≤ c e ∧ c e ≤ 6) ∧ StarP en c

/-- one step along an edge of `F` -/
def Step (F : E → Prop) (a b : V) : Prop := ∃ e, F e ∧ en e = s(a, b)

/-- `a` and `b` are joined by a walk using edges of `F` -/
def Conn (F : E → Prop) : V → V → Prop := Relation.ReflTransGen (Step en F)

theorem step_symm (F : E → Prop) : Symmetric (Step en F) := by
  intro a b ⟨e, he, h⟩
  exact ⟨e, he, by rw [h, Sym2.eq_swap]⟩

theorem conn_symm (F : E → Prop) {a b : V} (h : Conn en F a b) : Conn en F b a :=
  by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (step_symm en F hbc) ih

theorem conn_equiv (F : E → Prop) : Equivalence (Conn en F) :=
  ⟨fun _ => Relation.ReflTransGen.refl, fun h => conn_symm en F h, fun h1 h2 => h1.trans h2⟩

/-- the connected components of the spanning submultigraph with edge set `F` -/
def connSetoid (F : E → Prop) : Setoid V := ⟨Conn en F, conn_equiv en F⟩

/-- the number of connected components of the spanning submultigraph with edge set `F` -/
noncomputable def numComp (F : E → Prop) : ℕ := Nat.card (Quotient (connSetoid en F))

/-- a bridge: deleting it increases the number of connected components -/
def IsBridge (e : E) : Prop := numComp en (fun _ => True) < numComp en (fun f => f ≠ e)

/-- no edge is a bridge -/
def BridgelessP : Prop := ∀ e, ¬ IsBridge en e

/-- connected: any two vertices are joined by a walk -/
def ConnectedP : Prop := ∀ u v, Conn en (fun _ => True) u v

/-- a perfect matching: pairwise vertex-disjoint edges covering every vertex -/
def IsPM (N : E → Prop) : Prop :=
  (∀ e f, N e → N f → e ≠ f → ∀ x, x ∈ en e → x ∉ en f) ∧ ∀ x, ∃ e, N e ∧ x ∈ en e

/-- `N = c⁻¹(μ)` for some colour `μ ∈ {1, …, 6}` -/
def ColourClass6 (N : E → Prop) (c : E → ℕ) : Prop := ∃ μ, 1 ≤ μ ∧ μ ≤ 6 ∧ ∀ f, N f ↔ c f = μ

/-- `[g ∈ N]` -/
noncomputable def ind (N : E → Prop) (g : E) : ℕ := if N g then 1 else 0

/-- EX1-good (as in contract P11-H) -/
def EX1GoodP : Prop :=
  ∀ (g : E) (t : ℕ), t ≤ 1 → (∃ N, IsPM en N ∧ ind N g = t) →
    ∃ N, IsPM en N ∧ ind N g = t ∧ ∃ c : E → ℕ, (∀ e, 1 ≤ c e ∧ c e ≤ 6) ∧ StarP en c ∧ ColourClass6 N c

/-- edge `e` has one endpoint in `S` and the other outside `S` -/
def Cross (S : V → Prop) (e : E) : Prop := ∃ a b, en e = s(a, b) ∧ S a ∧ ¬ S b

/-- 2-cut-reduced (as in contract P11-H) -/
def TwoCutReducedP [Fintype V] [Fintype E] : Prop :=
  ∀ S : V → Prop, (Finset.univ.filter (Cross en S)).card = 2 →
    (Finset.univ.filter S).card = 2 ∨ (Finset.univ.filter (fun v => ¬ S v)).card = 2

/-- the leaf graph T(G0, g) for an edge `g` with ends `s`, `t`: vertices `V ⊕ Fin 2` (`x = inr 0`, `ℓ = inr 1`),
    edges `{e // e ≠ g} ⊕ Fin 3`; the old edges keep their ends, the new edges are `sx`, `xt`, `xℓ` -/
def enT (g : E) (s t : V) : {e // e ≠ g} ⊕ Fin 3 → Sym2 (V ⊕ Fin 2)
  | Sum.inl e => Sym2.map Sum.inl (en e.1)
  | Sum.inr i => if i = 0 then s(Sum.inl s, Sum.inr 0) else if i = 1 then s(Sum.inr 0, Sum.inl t)
      else s(Sum.inr 0, Sum.inr 1)

end plain

/-- ROOT-DMS-2, plain form: every finite loopless multigraph of maximum degree at most 3 has a star edge colouring
    with the colours 1, …, 6 -/
def DMSP : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V), LooplessP en → MaxDeg3 en → Star6P en

/-- (II) of contract P15-LEAF-II, plain form -/
def IIP : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V), LooplessP en → BridgelessP en → CubicP en →
    ∀ (g : E) (s t : V), en g = s(s, t) → Star6P (enT en g s t)

/-- (H) of contract P11-H, plain form -/
def HP : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (en : E → Sym2 V), LooplessP en → ConnectedP en → BridgelessP en →
    CubicP en → 10 ≤ Fintype.card V → TwoCutReducedP en → EX1GoodP en

/-! ## Colour relabelling -/

section colours
variable {V E : Type} (en : E → Sym2 V)

theorem starP_congr {K L : Type} (c : E → K) (d : E → L) (h : ∀ e f, c e = c f ↔ d e = d f) :
    StarP en c ↔ StarP en d := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun e f hne hx heq => h1 e f hne hx ((h e f).2 heq), ?_, ?_⟩
    · intro v0 v1 v2 v3 v4 e1 e2 e3 e4 hp ⟨b1, b2⟩
      exact h2 v0 v1 v2 v3 v4 e1 e2 e3 e4 hp ⟨(h _ _).2 b1, (h _ _).2 b2⟩
    · intro v0 v1 v2 v3 e1 e2 e3 e4 hp ⟨b1, b2⟩
      exact h3 v0 v1 v2 v3 e1 e2 e3 e4 hp ⟨(h _ _).2 b1, (h _ _).2 b2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun e f hne hx heq => h1 e f hne hx ((h e f).1 heq), ?_, ?_⟩
    · intro v0 v1 v2 v3 v4 e1 e2 e3 e4 hp ⟨b1, b2⟩
      exact h2 v0 v1 v2 v3 v4 e1 e2 e3 e4 hp ⟨(h _ _).1 b1, (h _ _).1 b2⟩
    · intro v0 v1 v2 v3 e1 e2 e3 e4 hp ⟨b1, b2⟩
      exact h3 v0 v1 v2 v3 e1 e2 e3 e4 hp ⟨(h _ _).1 b1, (h _ _).1 b2⟩

/-- colours `Fin 6` → `1, …, 6` -/
def toN (c : E → Fin 6) : E → ℕ := fun e => (c e).val + 1

/-- colours `1, …, 6` → `Fin 6` -/
def ofN (c : E → ℕ) : E → Fin 6 := fun e => ⟨(c e - 1) % 6, Nat.mod_lt _ (by decide)⟩

theorem toN_range (c : E → Fin 6) (e : E) : 1 ≤ toN c e ∧ toN c e ≤ 6 := by
  unfold toN; have := (c e).isLt; omega

theorem star6P_iff : Star6P en ↔ ∃ c : E → Fin 6, StarP en c := by
  constructor
  · rintro ⟨c, hr, hs⟩
    refine ⟨ofN c, (starP_congr en c (ofN c) ?_).1 hs⟩
    intro e f
    have he := hr e; have hf := hr f
    unfold ofN; rw [Fin.mk.injEq]; omega
  · rintro ⟨c, hs⟩
    refine ⟨toN c, toN_range c, (starP_congr en c (toN c) ?_).1 hs⟩
    intro e f
    unfold toN; rw [Fin.ext_iff]; omega

end colours

/-! ## Part 2: the correspondence between a plain multigraph and an edge set of an `MGraph` -/

theorem joins_iff_sym2 (X : MGraph) (f : Fin X.m) (x y : Fin X.n) :
    X.Joins f x y ↔ s((X.ends f).1, (X.ends f).2) = s(x, y) := by
  unfold MGraph.Joins
  rcases X.ends f with ⟨a, b⟩
  simp only [Sym2.eq_iff, Prod.mk.injEq]

theorem inc_iff_sym2 (X : MGraph) (f : Fin X.m) (x : Fin X.n) :
    X.Inc f x ↔ x ∈ s((X.ends f).1, (X.ends f).2) := by
  unfold MGraph.Inc
  rw [Sym2.mem_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem sym2_rep {V : Type} (z : Sym2 V) : ∃ a b, z = s(a, b) :=
  Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) z

/-- `R : Rep en X P`: the plain multigraph `(V, E, en)` is the multigraph with edge set `P` of `X`, via an injective
    vertex map `φ` and an injective edge map `ψ` whose image is `P`, respecting ends; every vertex of `X` that meets
    `P` is in the image of `φ` -/
structure Rep {V E : Type} (en : E → Sym2 V) (X : MGraph) (P : Fin X.m → Prop) where
  φ : V → Fin X.n
  ψ : E → Fin X.m
  φinj : ∀ a b, φ a = φ b → a = b
  ψinj : ∀ e f, ψ e = ψ f → e = f
  ψP : ∀ e, P (ψ e)
  ψsurj : ∀ f, P f → ∃ e, ψ e = f
  φsurj : ∀ x f, P f → X.Inc f x → ∃ v, φ v = x
  hend : ∀ e, s((X.ends (ψ e)).1, (X.ends (ψ e)).2) = Sym2.map φ (en e)

namespace Rep
variable {V E : Type} {en : E → Sym2 V} {X : MGraph} {P : Fin X.m → Prop} (R : Rep en X P)

theorem φinj' : Function.Injective R.φ := fun a b h => R.φinj a b h

theorem joins_iff (e : E) (a b : V) : X.Joins (R.ψ e) (R.φ a) (R.φ b) ↔ en e = s(a, b) := by
  rw [joins_iff_sym2, R.hend, ← Sym2.map_pair_eq]
  exact (Sym2.map.injective R.φinj').eq_iff

theorem inc_iff (e : E) (a : V) : X.Inc (R.ψ e) (R.φ a) ↔ a ∈ en e := by
  rw [inc_iff_sym2, R.hend, Sym2.mem_map]
  constructor
  · rintro ⟨b, hb, h⟩; rw [R.φinj b a h] at hb; exact hb
  · intro h; exact ⟨a, h, rfl⟩

theorem inc_vert {e : E} {x : Fin X.n} (h : X.Inc (R.ψ e) x) : ∃ v, R.φ v = x := R.φsurj x _ (R.ψP e) h

/-- the ends of `ψ e` are the images of the ends of `e`, in one of the two orders -/
theorem ends_cases {e : E} {a b : V} (h : en e = s(a, b)) :
    ((X.ends (R.ψ e)).1 = R.φ a ∧ (X.ends (R.ψ e)).2 = R.φ b) ∨
    ((X.ends (R.ψ e)).1 = R.φ b ∧ (X.ends (R.ψ e)).2 = R.φ a) := by
  have := R.hend e
  rw [h, Sym2.map_pair_eq, Sym2.eq_iff] at this
  exact this

theorem joins_of {e : E} {x y : Fin X.n} (h : X.Joins (R.ψ e) x y) :
    ∃ a b, R.φ a = x ∧ R.φ b = y ∧ en e = s(a, b) := by
  have hx : X.Inc (R.ψ e) x := by
    show (X.ends _).1 = x ∨ (X.ends _).2 = x
    rcases h with h | h <;> rw [h] <;> simp
  have hy : X.Inc (R.ψ e) y := by
    show (X.ends _).1 = y ∨ (X.ends _).2 = y
    rcases h with h | h <;> rw [h] <;> simp
  obtain ⟨a, rfl⟩ := R.inc_vert hx
  obtain ⟨b, rfl⟩ := R.inc_vert hy
  exact ⟨a, b, rfl, rfl, (R.joins_iff e a b).1 h⟩

/-- **star colourings correspond**: `StarOn P k c` (library definition) iff `c ∘ ψ` is a star colouring of the plain
    multigraph -/
theorem starOn_iff {k : Nat} (c : Fin X.m → Fin k) : StarOn P k c ↔ StarP en (fun e => c (R.ψ e)) := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro e f hne ⟨x, hx1, hx2⟩ heq
      exact hs.1 (R.ψ e) (R.ψ f) ⟨fun h => hne (R.ψinj e f h), R.φ x, (R.inc_iff e x).2 hx1,
        (R.inc_iff f x).2 hx2⟩ (R.ψP e) (R.ψP f) heq
    · intro v0 v1 v2 v3 v4 e1 e2 e3 e4 hp hb
      obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34, h1, h2, h3, h4⟩ := hp
      have ne : ∀ a b, a ≠ b → R.φ a ≠ R.φ b := fun a b h h' => h (R.φinj a b h')
      exact hs.2 ⟨R.φ v0, R.φ v1, R.φ v2, R.φ v3, R.φ v4, R.ψ e1, R.ψ e2, R.ψ e3, R.ψ e4,
        (R.joins_iff _ _ _).2 h1, (R.joins_iff _ _ _).2 h2, (R.joins_iff _ _ _).2 h3, (R.joins_iff _ _ _).2 h4,
        ne _ _ d01, ne _ _ d02, ne _ _ d03, ne _ _ d12, ne _ _ d13, ne _ _ d14, ne _ _ d23, ne _ _ d24, ne _ _ d34⟩
        (R.ψP _) (R.ψP _) (R.ψP _) (R.ψP _) hb
    · intro v0 v1 v2 v3 e1 e2 e3 e4 hp hb
      obtain ⟨d01, d02, d03, d12, d13, d23, h1, h2, h3, h4⟩ := hp
      have ne : ∀ a b, a ≠ b → R.φ a ≠ R.φ b := fun a b h h' => h (R.φinj a b h')
      exact hs.2 ⟨R.φ v0, R.φ v1, R.φ v2, R.φ v3, R.φ v0, R.ψ e1, R.ψ e2, R.ψ e3, R.ψ e4,
        (R.joins_iff _ _ _).2 h1, (R.joins_iff _ _ _).2 h2, (R.joins_iff _ _ _).2 h3, (R.joins_iff _ _ _).2 h4,
        ne _ _ d01, ne _ _ d02, ne _ _ d03, ne _ _ d12, ne _ _ d13, ne _ _ d01.symm, ne _ _ d23, ne _ _ d02.symm,
        ne _ _ d03.symm⟩
        (R.ψP _) (R.ψP _) (R.ψP _) (R.ψP _) hb
  · rintro ⟨hp, hpath, hcyc⟩
    constructor
    · intro a b ⟨hne, x, hax, hbx⟩ ha hb heq
      obtain ⟨e, rfl⟩ := R.ψsurj a ha
      obtain ⟨f, rfl⟩ := R.ψsurj b hb
      obtain ⟨u, rfl⟩ := R.inc_vert hax
      exact hp e f (fun h => hne (by rw [h])) ⟨u, (R.inc_iff e u).1 hax, (R.inc_iff f u).1 hbx⟩ heq
    · intro w h1 h2 h3 h4 hb
      obtain ⟨p1, hp1⟩ := R.ψsurj _ h1
      obtain ⟨p2, hp2⟩ := R.ψsurj _ h2
      obtain ⟨p3, hp3⟩ := R.ψsurj _ h3
      obtain ⟨p4, hp4⟩ := R.ψsurj _ h4
      have j1 := w.h1; have j2 := w.h2; have j3 := w.h3; have j4 := w.h4
      rw [← hp1] at j1; rw [← hp2] at j2; rw [← hp3] at j3; rw [← hp4] at j4
      obtain ⟨u0, u1, hu0, hu1, k1⟩ := R.joins_of j1
      obtain ⟨u1', u2, hu1', hu2, k2⟩ := R.joins_of j2
      obtain ⟨u2', u3, hu2', hu3, k3⟩ := R.joins_of j3
      obtain ⟨u3', u4, hu3', hu4, k4⟩ := R.joins_of j4
      have e1 : u1' = u1 := R.φinj _ _ (hu1'.trans hu1.symm)
      have e2 : u2' = u2 := R.φinj _ _ (hu2'.trans hu2.symm)
      have e3 : u3' = u3 := R.φinj _ _ (hu3'.trans hu3.symm)
      subst e1 e2 e3
      have ne : ∀ a b (x y : Fin X.n), R.φ a = x → R.φ b = y → x ≠ y → a ≠ b := by
        intro a b x y ha hb hxy hab; subst hab; exact hxy (ha.symm.trans hb)
      have hb' : c (R.ψ p1) = c (R.ψ p3) ∧ c (R.ψ p2) = c (R.ψ p4) := by
        rw [hp1, hp2, hp3, hp4]; exact hb
      by_cases h04 : u0 = u4
      · subst h04
        exact hcyc u0 u1' u2' u3' p1 p2 p3 p4
          ⟨ne _ _ _ _ hu0 hu1 w.d01, ne _ _ _ _ hu0 hu2 w.d02, ne _ _ _ _ hu0 hu3 w.d03,
           ne _ _ _ _ hu1 hu2 w.d12, ne _ _ _ _ hu1 hu3 w.d13, ne _ _ _ _ hu2 hu3 w.d23, k1, k2, k3, k4⟩ hb'
      · exact hpath u0 u1' u2' u3' u4 p1 p2 p3 p4
          ⟨ne _ _ _ _ hu0 hu1 w.d01, ne _ _ _ _ hu0 hu2 w.d02, ne _ _ _ _ hu0 hu3 w.d03, h04,
           ne _ _ _ _ hu1 hu2 w.d12, ne _ _ _ _ hu1 hu3 w.d13, ne _ _ _ _ hu1 hu4 w.d14,
           ne _ _ _ _ hu2 hu3 w.d23, ne _ _ _ _ hu2 hu4 w.d24, ne _ _ _ _ hu3 hu4 w.d34, k1, k2, k3, k4⟩ hb'

/-- a colouring of the plain edges, extended to all edges of `X` (default colour `d` off the image of `ψ`) -/
noncomputable def liftC {K : Type} (d : K) (c : E → K) : Fin X.m → K :=
  fun f => if h : ∃ e, R.ψ e = f then c (Classical.choose h) else d

theorem liftC_ψ {K : Type} (d : K) (c : E → K) (e : E) : R.liftC d c (R.ψ e) = c e := by
  unfold liftC
  have h : ∃ e', R.ψ e' = R.ψ e := ⟨e, rfl⟩
  rw [dif_pos h, R.ψinj _ _ (Classical.choose_spec h)]

/-- an edge set of the plain multigraph as an edge set of `X` -/
def liftN (N : E → Prop) : Fin X.m → Prop := fun f => ∃ e, R.ψ e = f ∧ N e

theorem liftN_ψ (N : E → Prop) (e : E) : R.liftN N (R.ψ e) ↔ N e := by
  constructor
  · rintro ⟨e', h, hn⟩; rw [← R.ψinj _ _ h]; exact hn
  · intro h; exact ⟨e, rfl, h⟩

theorem liftN_P (N : E → Prop) (f : Fin X.m) (h : R.liftN N f) : P f := by
  obtain ⟨e, rfl, _⟩ := h; exact R.ψP e

include R in
theorem colourable_iff {k : Nat} (hk : 0 < k) : Colourable P k ↔ ∃ c : E → Fin k, StarP en c := by
  constructor
  · rintro ⟨c, hc⟩; exact ⟨_, (R.starOn_iff c).1 hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨R.liftC ⟨0, hk⟩ c, (R.starOn_iff _).2 ?_⟩
    have : (fun e => R.liftC ⟨0, hk⟩ c (R.ψ e)) = c := funext fun e => R.liftC_ψ _ c e
    rw [this]; exact hc

end Rep


/-! ## Part 3: transfer of the graph-class notions along a `Rep` -/

section helpers

theorem exists_four {α : Type} [DecidableEq α] (s : Finset α) (h : 3 < s.card) :
    ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < s.card)
  have h2 : 2 < (s.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.1 h2
  rw [Finset.mem_erase] at hb hc hd
  exact ⟨a, b, c, d, ha, hb.2, hc.2, hd.2, hb.1.symm, hc.1.symm, hd.1.symm, hbc, hbd, hcd⟩

theorem four_le_card {α : Type} [DecidableEq α] (s : Finset α) {a b c d : α} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hd : d ∈ s) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : 4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a, b, c, d} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_insert_of_notMem (by simp [hcd]),
      Finset.card_singleton]
  exact h4 ▸ Finset.card_le_card hsub

theorem cntF_eq : ∀ (n : ℕ) (W : Fin n → Prop), RH2F.cntF n W = (Finset.univ.filter W).card := by
  intro n
  induction n with
  | zero => intro W; rfl
  | succ n ih =>
    intro W
    rw [RH2F.cntF_succ, ih, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

end helpers

namespace Rep
variable {V E : Type} {en : E → Sym2 V} {X : MGraph} {P : Fin X.m → Prop} (R : Rep en X P)

/-! ### perfect matchings and colour classes -/

include R in
theorem pmOn_iff (hV : ∀ v, ∃ e, v ∈ en e) (N : Fin X.m → Prop) (hN : ∀ f, N f → P f) :
    RH2F.PMOn P N ↔ IsPM en (fun e => N (R.ψ e)) := by
  constructor
  · rintro ⟨_, hcov⟩
    constructor
    · intro e f he hf hne x hxe hxf
      obtain ⟨a, _, _, hu⟩ := hcov (R.φ x) ⟨R.ψ e, R.ψP e, (R.inc_iff e x).2 hxe⟩
      have h1 := hu (R.ψ e) he ((R.inc_iff e x).2 hxe)
      have h2 := hu (R.ψ f) hf ((R.inc_iff f x).2 hxf)
      exact hne (R.ψinj _ _ (h1.trans h2.symm))
    · intro x
      obtain ⟨e, hxe⟩ := hV x
      obtain ⟨a, ha, hax, _⟩ := hcov (R.φ x) ⟨R.ψ e, R.ψP e, (R.inc_iff e x).2 hxe⟩
      obtain ⟨e', rfl⟩ := R.ψsurj a (hN a ha)
      exact ⟨e', ha, (R.inc_iff e' x).1 hax⟩
  · rintro ⟨hdis, hcov⟩
    refine ⟨hN, ?_⟩
    rintro x ⟨f, hf, hfx⟩
    obtain ⟨u, rfl⟩ := R.φsurj x f hf hfx
    obtain ⟨e, he, hue⟩ := hcov u
    refine ⟨R.ψ e, he, (R.inc_iff e u).2 hue, ?_⟩
    intro d hd hdu
    obtain ⟨e', rfl⟩ := R.ψsurj d (hN d hd)
    by_contra hne
    exact hdis e' e hd he (fun h => hne (by rw [h])) u ((R.inc_iff e' u).1 hdu) hue

theorem classOn_iff (N : Fin X.m → Prop) (c : Fin X.m → Fin 6) :
    RH2F.ClassOn P N c ↔ ColourClass6 (fun e => N (R.ψ e)) (toN (fun e => c (R.ψ e))) := by
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ.val + 1, by omega, by have := μ.isLt; omega, fun e => ?_⟩
    show N (R.ψ e) ↔ (c (R.ψ e)).val + 1 = μ.val + 1
    rw [hμ (R.ψ e) (R.ψP e), Fin.ext_iff]; omega
  · rintro ⟨μ, h1, h6, hμ⟩
    refine ⟨⟨μ - 1, by omega⟩, fun f hf => ?_⟩
    obtain ⟨e, rfl⟩ := R.ψsurj f hf
    have := hμ e
    simp only [toN] at this
    rw [this, Fin.ext_iff]; simp only; omega

/-! ### cubic and maximum degree -/

include R in
theorem cubicOn_of [Fintype E] (h : CubicP en) : CubicOn P := by
  rintro x ⟨f, hf, hfx⟩
  obtain ⟨v, rfl⟩ := R.φsurj x f hf hfx
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.1 (h v)
  have mem : ∀ e, v ∈ en e ↔ e = a ∨ e = b ∨ e = c := by
    intro e
    have := congrArg (e ∈ ·) hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
      eq_iff_iff] at this
    exact this
  have ina : v ∈ en a := (mem a).2 (Or.inl rfl)
  have inb : v ∈ en b := (mem b).2 (Or.inr (Or.inl rfl))
  have inc : v ∈ en c := (mem c).2 (Or.inr (Or.inr rfl))
  refine ⟨R.ψ a, R.ψ b, R.ψ c, R.ψP a, R.ψP b, R.ψP c, (R.inc_iff _ _).2 ina, (R.inc_iff _ _).2 inb,
    (R.inc_iff _ _).2 inc, fun h => hab (R.ψinj _ _ h), fun h => hac (R.ψinj _ _ h),
    fun h => hbc (R.ψinj _ _ h), ?_⟩
  intro d hd hdx
  obtain ⟨e, rfl⟩ := R.ψsurj d hd
  rcases (mem e).1 ((R.inc_iff e v).1 hdx) with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

include R in
theorem cubicP_of [Fintype E] (hV : ∀ v, ∃ e, v ∈ en e) (h : CubicOn P) : CubicP en := by
  intro v
  obtain ⟨e0, he0⟩ := hV v
  obtain ⟨a, b, c, ha, hb, hc, hax, hbx, hcx, hab, hac, hbc, hall⟩ :=
    h (R.φ v) ⟨R.ψ e0, R.ψP e0, (R.inc_iff e0 v).2 he0⟩
  obtain ⟨a', rfl⟩ := R.ψsurj a ha
  obtain ⟨b', rfl⟩ := R.ψsurj b hb
  obtain ⟨c', rfl⟩ := R.ψsurj c hc
  apply Finset.card_eq_three.2
  refine ⟨a', b', c', fun h => hab (by rw [h]), fun h => hac (by rw [h]), fun h => hbc (by rw [h]), ?_⟩
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hve
    rcases hall (R.ψ e) (R.ψP e) ((R.inc_iff e v).2 hve) with h | h | h
    · exact Or.inl (R.ψinj _ _ h)
    · exact Or.inr (Or.inl (R.ψinj _ _ h))
    · exact Or.inr (Or.inr (R.ψinj _ _ h))
  · rintro (rfl | rfl | rfl)
    · exact (R.inc_iff _ v).1 hax
    · exact (R.inc_iff _ v).1 hbx
    · exact (R.inc_iff _ v).1 hcx

include R in
theorem subcubic_of [Fintype E] (hP : ∀ f, P f) (h : MaxDeg3 en) : Subcubic X := by
  intro x a b c d hax hbx hcx hdx hab hac had hbc hbd hcd
  obtain ⟨a', rfl⟩ := R.ψsurj a (hP a)
  obtain ⟨b', rfl⟩ := R.ψsurj b (hP b)
  obtain ⟨c', rfl⟩ := R.ψsurj c (hP c)
  obtain ⟨d', rfl⟩ := R.ψsurj d (hP d)
  obtain ⟨v, rfl⟩ := R.inc_vert hax
  have h4 := four_le_card (Finset.univ.filter (fun e => v ∈ en e))
    (a := a') (b := b') (c := c') (d := d')
    (by simpa using (R.inc_iff _ v).1 hax) (by simpa using (R.inc_iff _ v).1 hbx)
    (by simpa using (R.inc_iff _ v).1 hcx) (by simpa using (R.inc_iff _ v).1 hdx)
    (fun h => hab (by rw [h])) (fun h => hac (by rw [h])) (fun h => had (by rw [h]))
    (fun h => hbc (by rw [h])) (fun h => hbd (by rw [h])) (fun h => hcd (by rw [h]))
  have := h v
  unfold deg at this
  omega

include R in
theorem maxDeg3_of [Fintype E] (h : Subcubic X) : MaxDeg3 en := by
  intro v
  by_contra hlt
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four (Finset.univ.filter (fun e => v ∈ en e)) (by unfold deg at hlt; omega)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc hd
  exact h (R.φ v) (R.ψ a) (R.ψ b) (R.ψ c) (R.ψ d) ((R.inc_iff _ _).2 ha) ((R.inc_iff _ _).2 hb)
    ((R.inc_iff _ _).2 hc) ((R.inc_iff _ _).2 hd) (fun h => hab (R.ψinj _ _ h)) (fun h => hac (R.ψinj _ _ h))
    (fun h => had (R.ψinj _ _ h)) (fun h => hbc (R.ψinj _ _ h)) (fun h => hbd (R.ψinj _ _ h))
    (fun h => hcd (R.ψinj _ _ h))

/-! ### walks, cuts, connectivity -/

/-- a vertex 2-colouring constant on the edges of `P` other than `ψ e₀` (if any) is constant along walks of the
    plain multigraph avoiding `e₀` -/
theorem const_of_conn (F : E → Prop) (U : Fin X.n → Bool)
    (hU : ∀ e, F e → U (X.ends (R.ψ e)).1 = U (X.ends (R.ψ e)).2) {a b : V} (h : Conn en F a b) :
    U (R.φ a) = U (R.φ b) := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨e, he, hen⟩ := hst
    rw [ih]
    rcases R.ends_cases hen with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hU e he; rw [h1, h2] at this; exact this
    · have := hU e he; rw [h1, h2] at this; exact this.symm

theorem decide_φ (Q : V → Prop) (a : V) :
    decide (∃ a', R.φ a' = R.φ a ∧ Q a') = decide (Q a) := by
  apply decide_eq_decide.2
  constructor
  · rintro ⟨a', h, hq⟩; rw [← R.φinj _ _ h]; exact hq
  · intro h; exact ⟨a, rfl, h⟩

/-- the reachability 2-colouring from `b0` along walks avoiding the edges not in `F` -/
noncomputable def reachU (F : E → Prop) (b0 : V) : Fin X.n → Bool :=
  fun y => decide (∃ a, R.φ a = y ∧ Conn en F b0 a)

theorem reachU_φ (F : E → Prop) (b0 a : V) : R.reachU F b0 (R.φ a) = decide (Conn en F b0 a) :=
  R.decide_φ _ a

theorem reachU_const (F : E → Prop) (b0 : V) (e : E) (he : F e) :
    R.reachU F b0 (X.ends (R.ψ e)).1 = R.reachU F b0 (X.ends (R.ψ e)).2 := by
  obtain ⟨a, b, hab⟩ := sym2_rep (en e)
  have hs : Step en F a b := ⟨e, he, hab⟩
  have hs' : Step en F b a := step_symm en F hs
  have key : decide (Conn en F b0 a) = decide (Conn en F b0 b) :=
    decide_eq_decide.2 ⟨fun h => h.tail hs, fun h => h.tail hs'⟩
  rcases R.ends_cases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, R.reachU_φ, R.reachU_φ]; exact key
  · rw [h1, h2, R.reachU_φ, R.reachU_φ]; exact key.symm

/-- a bridge cut of `P` at `ψ e` from a pair of ends not joined avoiding `e` -/
noncomputable def mkCut (e : E) (b0 b1 : V) (h1 : (X.ends (R.ψ e)).1 = R.φ b0)
    (h2 : (X.ends (R.ψ e)).2 = R.φ b1) (hn : ¬ Conn en (fun f => f ≠ e) b0 b1) : X.CutOn P (R.ψ e) where
  U := R.reachU (fun f => f ≠ e) b0
  hu := by rw [h1, R.reachU_φ]; exact decide_eq_true Relation.ReflTransGen.refl
  hv := by rw [h2, R.reachU_φ]; exact decide_eq_false hn
  sep := by
    intro f hf hfe
    obtain ⟨f', rfl⟩ := R.ψsurj f hf
    exact R.reachU_const _ b0 f' (fun h => hfe (by rw [h]))

theorem cut_iff (e : E) {u v : V} (h : en e = s(u, v)) :
    Nonempty (X.CutOn P (R.ψ e)) ↔ ¬ Conn en (fun f => f ≠ e) u v := by
  constructor
  · rintro ⟨B⟩ hc
    have key := R.const_of_conn (fun f => f ≠ e) B.U (fun f hf => B.sep (R.ψ f) (R.ψP f)
      (fun h => hf (R.ψinj _ _ h))) hc
    have hu := B.hu; have hv := B.hv
    rcases R.ends_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hu; rw [h2] at hv; rw [hu, hv] at key; exact Bool.noConfusion key
    · rw [h1] at hu; rw [h2] at hv; rw [hu, hv] at key; exact Bool.noConfusion key
  · intro hn
    rcases R.ends_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨R.mkCut e u v h1 h2 hn⟩
    · exact ⟨R.mkCut e v u h1 h2 (fun hc => hn (conn_symm en _ hc))⟩

end Rep

/-- **bridges**: deleting `e = uv` increases the number of connected components iff `u` and `v` are not joined by
    a walk avoiding `e` -/
theorem bridge_iff {V E : Type} [Finite V] (en : E → Sym2 V) (e : E) {u v : V} (h : en e = s(u, v)) :
    IsBridge en e ↔ ¬ Conn en (fun f => f ≠ e) u v := by
  have mono : ∀ a b, Conn en (fun f => f ≠ e) a b → Conn en (fun _ => True) a b := fun a b hab =>
    by
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail (let ⟨f, _, hf⟩ := hbc; ⟨f, trivial, hf⟩)
  let π : Quotient (connSetoid en (fun f => f ≠ e)) → Quotient (connSetoid en (fun _ => True)) :=
    Quotient.lift (fun a => Quotient.mk (connSetoid en (fun _ => True)) a)
      (fun a b hab => Quotient.sound (mono a b hab))
  have hsurj : Function.Surjective π := by
    intro q
    induction q using Quotient.ind with
    | _ a => exact ⟨Quotient.mk _ a, rfl⟩
  haveI := Fintype.ofFinite (Quotient (connSetoid en (fun f => f ≠ e)))
  haveI := Fintype.ofFinite (Quotient (connSetoid en (fun _ => True)))
  unfold IsBridge numComp
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  constructor
  · intro hlt hc
    have back : ∀ a b, Conn en (fun _ => True) a b → Conn en (fun f => f ≠ e) a b := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hst ih =>
        obtain ⟨f, _, hf⟩ := hst
        by_cases hfe : f = e
        · subst hfe
          rw [h, Sym2.eq_iff] at hf
          rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ih.trans hc
          · exact ih.trans (conn_symm en _ hc)
        · exact ih.tail ⟨f, hfe, hf⟩
    have hinj : Function.Injective π := by
      intro q1 q2
      induction q1 using Quotient.ind with
      | _ a =>
      induction q2 using Quotient.ind with
      | _ b =>
      intro hq
      exact Quotient.sound (back a b (Quotient.exact hq))
    have := Fintype.card_congr (Equiv.ofBijective π ⟨hinj, hsurj⟩)
    omega
  · intro hn
    apply Fintype.card_lt_of_surjective_not_injective π hsurj
    intro hinj
    apply hn
    have : π (Quotient.mk _ u) = π (Quotient.mk _ v) :=
      Quotient.sound (Relation.ReflTransGen.single ⟨e, trivial, h⟩)
    exact Quotient.exact (hinj this)

namespace Rep
variable {V E : Type} {en : E → Sym2 V} {X : MGraph} {P : Fin X.m → Prop} (R : Rep en X P)

include R in
theorem bridgeless_iff [Finite V] : BridgelessOn P ↔ BridgelessP en := by
  constructor
  · intro hb e hbr
    obtain ⟨u, v, huv⟩ := sym2_rep (en e)
    obtain ⟨B⟩ := (R.cut_iff e huv).2 ((bridge_iff en e huv).1 hbr)
    exact hb (R.ψ e) (R.ψP e) B
  · intro hb f hf B
    obtain ⟨e, rfl⟩ := R.ψsurj f hf
    obtain ⟨u, v, huv⟩ := sym2_rep (en e)
    exact hb e ((bridge_iff en e huv).2 ((R.cut_iff e huv).1 ⟨B⟩))

include R in
theorem connectedOn_of (h : ConnectedP en) : ConnectedOn P := by
  intro U hU f g hf hg
  obtain ⟨e1, rfl⟩ := R.ψsurj f hf
  obtain ⟨e2, rfl⟩ := R.ψsurj g hg
  obtain ⟨a1, ha1⟩ := R.inc_vert (e := e1) (x := (X.ends (R.ψ e1)).1) (Or.inl rfl)
  obtain ⟨a2, ha2⟩ := R.inc_vert (e := e2) (x := (X.ends (R.ψ e2)).1) (Or.inl rfl)
  rw [← ha1, ← ha2]
  exact R.const_of_conn (fun _ => True) U (fun e _ => hU (R.ψ e) (R.ψP e)) (h a1 a2)

include R in
theorem connectedP_of (hV : ∀ v, ∃ e, v ∈ en e) (h : ConnectedOn P) : ConnectedP en := by
  intro u v
  by_contra hn
  have hU : ∀ f, P f → R.reachU (fun _ => True) u (X.ends f).1 = R.reachU (fun _ => True) u (X.ends f).2 := by
    intro f hf
    obtain ⟨e, rfl⟩ := R.ψsurj f hf
    exact R.reachU_const _ u e trivial
  have atEnd : ∀ (e : E) (a : V), a ∈ en e →
      R.reachU (fun _ => True) u (X.ends (R.ψ e)).1 = R.reachU (fun _ => True) u (R.φ a) := by
    intro e a ha
    rcases (R.inc_iff e a).2 ha with h1 | h1
    · rw [h1]
    · rw [hU _ (R.ψP e), h1]
  obtain ⟨e1, h1⟩ := hV u
  obtain ⟨e2, h2⟩ := hV v
  have := h (R.reachU (fun _ => True) u) hU (R.ψ e1) (R.ψ e2) (R.ψP e1) (R.ψP e2)
  rw [atEnd e1 u h1, atEnd e2 v h2, R.reachU_φ, R.reachU_φ] at this
  have hu : decide (Conn en (fun _ => True) u u) = true := decide_eq_true Relation.ReflTransGen.refl
  have hv : decide (Conn en (fun _ => True) u v) = false := decide_eq_false hn
  rw [hu, hv] at this
  exact Bool.noConfusion this

/-! ### counting and 2-edge-cuts -/

include R in
theorem image_meets [Fintype V] (hV : ∀ v, ∃ e, v ∈ en e) :
    Finset.univ.filter (RH2F.meets P) = Finset.univ.image R.φ := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hfx⟩; exact R.φsurj x f hf hfx
  · rintro ⟨v, -, rfl⟩
    obtain ⟨e, he⟩ := hV v
    exact ⟨R.ψ e, R.ψP e, (R.inc_iff e v).2 he⟩

include R in
theorem vcount_eq [Fintype V] (hV : ∀ v, ∃ e, v ∈ en e) : RH2F.vcount P = Fintype.card V := by
  unfold RH2F.vcount
  rw [cntF_eq, R.image_meets hV, Finset.card_image_of_injective _ R.φinj', Finset.card_univ]

include R in
theorem scount_eq [Fintype V] (hV : ∀ v, ∃ e, v ∈ en e) (S : Fin X.n → Bool) (b : Bool) :
    RH2F.scount P S b = (Finset.univ.filter (fun v => S (R.φ v) = b)).card := by
  unfold RH2F.scount
  rw [cntF_eq, ← Finset.card_image_of_injective _ R.φinj']
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨f, hf, hfx⟩, hs⟩
    obtain ⟨v, rfl⟩ := R.φsurj x f hf hfx
    exact ⟨v, hs, rfl⟩
  · rintro ⟨v, hs, rfl⟩
    obtain ⟨e, he⟩ := hV v
    exact ⟨⟨R.ψ e, R.ψP e, (R.inc_iff e v).2 he⟩, hs⟩

theorem crosses_iff (S : Fin X.n → Bool) (e : E) :
    RH2F.Crosses P S (R.ψ e) ↔ Cross en (fun v => S (R.φ v) = true) e := by
  obtain ⟨a, b, hab⟩ := sym2_rep (en e)
  unfold RH2F.Crosses Cross
  constructor
  · rintro ⟨_, hne⟩
    have key : S (R.φ a) ≠ S (R.φ b) := by
      rcases R.ends_cases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hne
      · exact hne
      · exact fun h => hne h.symm
    cases ha : S (R.φ a) <;> cases hb : S (R.φ b) <;> rw [ha, hb] at key
    · exact absurd rfl key
    · exact ⟨b, a, by rw [hab, Sym2.eq_swap], hb, by show ¬ (S (R.φ a) = true); rw [ha]; exact Bool.false_ne_true⟩
    · exact ⟨a, b, hab, ha, by show ¬ (S (R.φ b) = true); rw [hb]; exact Bool.false_ne_true⟩
    · exact absurd rfl key
  · rintro ⟨a', b', hab', ha', hb'⟩
    refine ⟨R.ψP e, ?_⟩
    rcases R.ends_cases hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> intro heq <;> apply hb' <;>
      show S (R.φ b') = true
    · rw [← heq]; exact ha'
    · rw [heq]; exact ha'

theorem twoCut_iff [Fintype E] (S : Fin X.n → Bool) :
    RH2F.TwoCut P S ↔ (Finset.univ.filter (Cross en (fun v => S (R.φ v) = true))).card = 2 := by
  constructor
  · rintro ⟨f1, f2, hne, c1, c2, hall⟩
    obtain ⟨a, rfl⟩ := R.ψsurj f1 c1.1
    obtain ⟨b, rfl⟩ := R.ψsurj f2 c2.1
    apply Finset.card_eq_two.2
    refine ⟨a, b, fun h => hne (by rw [h]), ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      rcases hall (R.ψ x) ((R.crosses_iff S x).2 hx) with h | h
      · exact Or.inl (R.ψinj _ _ h)
      · exact Or.inr (R.ψinj _ _ h)
    · rintro (rfl | rfl)
      · exact (R.crosses_iff S _).1 c1
      · exact (R.crosses_iff S _).1 c2
  · intro h
    obtain ⟨a, b, hne, hs⟩ := Finset.card_eq_two.1 h
    have mem : ∀ x, Cross en (fun v => S (R.φ v) = true) x ↔ x = a ∨ x = b := by
      intro x
      have := congrArg (x ∈ ·) hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        eq_iff_iff] at this
      exact this
    refine ⟨R.ψ a, R.ψ b, fun h => hne (R.ψinj _ _ h), (R.crosses_iff S a).2 ((mem a).2 (Or.inl rfl)),
      (R.crosses_iff S b).2 ((mem b).2 (Or.inr rfl)), ?_⟩
    intro d hd
    obtain ⟨x, rfl⟩ := R.ψsurj d hd.1
    rcases (mem x).1 ((R.crosses_iff S x).1 hd) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

include R in
theorem twoCutReduced_iff [Fintype V] [Fintype E] (hV : ∀ v, ∃ e, v ∈ en e) :
    RH2F.TwoCutReducedOn P ↔ TwoCutReducedP en := by
  constructor
  · intro h S' hc
    let S : Fin X.n → Bool := fun y => decide (∃ v, R.φ v = y ∧ S' v)
    have hS : ∀ v, S (R.φ v) = true ↔ S' v := by
      intro v
      simp only [S, decide_eq_true_iff]
      exact ⟨fun ⟨a', h, hq⟩ => R.φinj _ _ h ▸ hq, fun h => ⟨v, rfl, h⟩⟩
    have hfun : (fun v => S (R.φ v) = true) = S' := funext fun v => propext (hS v)
    have htc : RH2F.TwoCut P S := by rw [R.twoCut_iff, hfun]; exact hc
    rcases h S htc with h1 | h1
    · left
      rw [R.scount_eq hV] at h1
      rw [← h1]; congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (hS v).symm
    · right
      rw [R.scount_eq hV] at h1
      rw [← h1]; congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hS v]; cases S (R.φ v) <;> simp
  · intro h S hc
    rw [R.twoCut_iff] at hc
    rcases h _ hc with h1 | h1
    · left; rw [R.scount_eq hV]; convert h1
    · right; rw [R.scount_eq hV, ← h1]; congr 1; ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases S (R.φ v) <;> simp

end Rep


/-! ## Part 4: the two encodings and the leaf graph -/

section sub
variable (X : MGraph) (P : Fin X.m → Prop)

/-- the vertices meeting `P` -/
abbrev SubV := {x : Fin X.n // RH2F.meets P x}
/-- the edges of `P` -/
abbrev SubE := {f : Fin X.m // P f}

/-- the plain multigraph of the edge set `P` of `X`: vertices meeting `P`, edges of `P`, the same ends -/
def subEn (f : SubE X P) : Sym2 (SubV X P) :=
  s(⟨(X.ends f.1).1, f.1, f.2, Or.inl rfl⟩, ⟨(X.ends f.1).2, f.1, f.2, Or.inr rfl⟩)

def subRep : Rep (subEn X P) X P where
  φ := Subtype.val
  ψ := Subtype.val
  φinj := fun _ _ h => Subtype.ext h
  ψinj := fun _ _ h => Subtype.ext h
  ψP := fun e => e.2
  ψsurj := fun f hf => ⟨⟨f, hf⟩, rfl⟩
  φsurj := fun x f hf hx => ⟨⟨x, f, hf, hx⟩, rfl⟩
  hend := fun e => by simp [subEn, Sym2.map_pair_eq]

theorem sub_hV : ∀ v : SubV X P, ∃ e, v ∈ subEn X P e := by
  rintro ⟨x, f, hf, hx⟩
  refine ⟨⟨f, hf⟩, ?_⟩
  unfold subEn
  rw [Sym2.mem_iff]
  rcases hx with h | h
  · exact Or.inl (Subtype.ext h.symm)
  · exact Or.inr (Subtype.ext h.symm)

theorem sub_loopless (h : Loopless X) : LooplessP (subEn X P) := by
  intro e hd
  unfold subEn at hd
  rw [Sym2.mk_isDiag_iff] at hd
  exact h e.1 (congrArg Subtype.val hd)

end sub

section enc
variable {V E : Type} [Fintype V] [Fintype E]

/-- the encoding of a plain multigraph with an orientation `o` of its edges as an `MGraph` on `Fin |V|`, `Fin |E|` -/
noncomputable def encG (o : E → V × V) : MGraph where
  n := Fintype.card V
  m := Fintype.card E
  ends := fun f => (Fintype.equivFin V (o ((Fintype.equivFin E).symm f)).1,
    Fintype.equivFin V (o ((Fintype.equivFin E).symm f)).2)

theorem encG_ends (o : E → V × V) (e : E) :
    (encG o).ends (Fintype.equivFin E e) = (Fintype.equivFin V (o e).1, Fintype.equivFin V (o e).2) := by
  simp [encG]

noncomputable def encRep (en : E → Sym2 V) (o : E → V × V) (ho : ∀ e, s((o e).1, (o e).2) = en e) :
    Rep en (encG o) (fun _ => True) where
  φ := Fintype.equivFin V
  ψ := Fintype.equivFin E
  φinj := fun _ _ h => (Fintype.equivFin V).injective h
  ψinj := fun _ _ h => (Fintype.equivFin E).injective h
  ψP := fun _ => trivial
  ψsurj := fun f _ => ⟨(Fintype.equivFin E).symm f, by simp⟩
  φsurj := fun x _ _ _ => ⟨(Fintype.equivFin V).symm x, by simp⟩
  hend := fun e => by rw [encG_ends, ← ho e, Sym2.map_pair_eq]

theorem enc_loopless (en : E → Sym2 V) (o : E → V × V) (ho : ∀ e, s((o e).1, (o e).2) = en e)
    (h : LooplessP en) : Loopless (encG o) := by
  intro f heq
  obtain ⟨e, rfl⟩ := (Fintype.equivFin E).surjective f
  rw [encG_ends] at heq
  apply h e
  rw [← ho e, Sym2.mk_isDiag_iff]
  exact (Fintype.equivFin V).injective heq

/-- a default orientation -/
noncomputable def ori (en : E → Sym2 V) (e : E) : V × V :=
  (Classical.choose (sym2_rep (en e)), Classical.choose (Classical.choose_spec (sym2_rep (en e))))

omit [Fintype V] [Fintype E] in
theorem ori_spec (en : E → Sym2 V) (e : E) : s((ori en e).1, (ori en e).2) = en e :=
  (Classical.choose_spec (Classical.choose_spec (sym2_rep (en e)))).symm

/-- the default orientation, except that `g` is oriented from `s` to `t` -/
noncomputable def oriG (en : E → Sym2 V) (g : E) (s t : V) (e : E) : V × V := if e = g then (s, t) else ori en e

omit [Fintype V] [Fintype E] in
theorem oriG_spec (en : E → Sym2 V) (g : E) (s t : V) (h : en g = s(s, t)) (e : E) :
    s((oriG en g s t e).1, (oriG en g s t e).2) = en e := by
  unfold oriG
  by_cases he : e = g
  · subst he; rw [if_pos rfl]; exact h.symm
  · rw [if_neg he]; exact ori_spec en e

omit [Fintype V] in
theorem cubic_hV (en : E → Sym2 V) (h : CubicP en) : ∀ v, ∃ e, v ∈ en e := by
  intro v
  obtain ⟨e, he⟩ := Finset.card_pos.1 (by have := h v; unfold deg at this; omega :
    0 < (Finset.univ.filter (fun e => v ∈ en e)).card)
  exact ⟨e, (Finset.mem_filter.1 he).2⟩

end enc

section leaf
variable {V E : Type} {en : E → Sym2 V} {X : MGraph} {P : Fin X.m → Prop} (R : Rep en X P) (g : E) (s t : V)

/-- the vertex map of the leaf graph: old vertices, `x ↦ vx`, `ℓ ↦ vl` -/
def φT : V ⊕ Fin 2 → Fin (RH2F.leafG X (R.ψ g)).n
  | Sum.inl v => RH2F.lv (R.φ v)
  | Sum.inr i => if i = 0 then RH2F.vx X else RH2F.vl X

/-- the edge map of the leaf graph: old edges, `sx ↦ newE 0`, `xt ↦ newE 1`, `xℓ ↦ newE 2` -/
def ψT : {e // e ≠ g} ⊕ Fin 3 → Fin (RH2F.leafG X (R.ψ g)).m
  | Sum.inl e => RH2F.oldE (R.ψ g) (R.ψ e.1)
  | Sum.inr i => RH2F.newE (R.ψ g) i.val i.isLt

theorem leaf_cases' (f : Fin (RH2F.leafG X (R.ψ g)).m) :
    (∃ d, f = RH2F.oldE (R.ψ g) d) ∨ ∃ i : Fin 3, f = RH2F.newE (R.ψ g) i.val i.isLt := by
  have hf : f.val < X.m + 3 := f.isLt
  by_cases h : f.val < X.m
  · exact Or.inl ⟨⟨f.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨f.val - X.m, by omega⟩, Fin.ext (by simp [RH2F.newE]; omega)⟩

theorem ends_newE (i : Fin 3) : (RH2F.leafG X (R.ψ g)).ends (RH2F.newE (R.ψ g) i.val i.isLt) =
    if i = 0 then (RH2F.lv (X.ends (R.ψ g)).1, RH2F.vx X) else if i = 1 then (RH2F.vx X, RH2F.lv (X.ends (R.ψ g)).2)
    else (RH2F.vx X, RH2F.vl X) := by
  have hi := i.isLt
  by_cases h0 : i = 0
  · subst h0; rw [if_pos rfl]; exact RH2F.ends_new0 _
  · by_cases h1 : i = 1
    · subst h1; rw [if_neg (by decide), if_pos rfl]; exact RH2F.ends_new1 _
    · have h2 : i = 2 := by
        apply Fin.ext
        have := Fin.val_ne_of_ne h0; have := Fin.val_ne_of_ne h1; simp at *; omega
      subst h2; rw [if_neg (by decide), if_neg (by decide)]; exact RH2F.ends_new2 _

/-- **the leaf graphs correspond**: if `ψ g` is oriented from `φ s` to `φ t`, the plain leaf graph `T(G0, g)` is the
    edge set `leafSet P (ψ g)` of the library's leaf graph `leafG X (ψ g)` -/
def leafRep (hg : X.ends (R.ψ g) = (R.φ s, R.φ t)) :
    Rep (enT en g s t) (RH2F.leafG X (R.ψ g)) (RH2F.leafSet P (R.ψ g)) where
  φ := φT R g
  ψ := ψT R g
  φinj := by
    have h01 : ∀ i j : Fin 2, (if i = 0 then RH2F.vx X else RH2F.vl X) =
        (if j = 0 then RH2F.vx X else RH2F.vl X) → i = j := by
      intro i j h
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      · rw [hi, hj]
      · rw [if_pos hi, if_neg hj] at h; exact absurd h (RH2F.vx_ne_vl X)
      · rw [if_neg hi, if_pos hj] at h; exact absurd h.symm (RH2F.vx_ne_vl X)
      · apply Fin.ext
        have := Fin.val_ne_of_ne hi; have := Fin.val_ne_of_ne hj; have := i.isLt; have := j.isLt
        simp at *; omega
    rintro (a | i) (b | j) h
    · exact congrArg Sum.inl (R.φinj _ _ (RH2F.lv_inj h))
    · exfalso; simp only [φT] at h
      by_cases hj : j = 0
      · rw [if_pos hj] at h; exact RH2F.lv_ne_vx _ h
      · rw [if_neg hj] at h; exact RH2F.lv_ne_vl _ h
    · exfalso; simp only [φT] at h
      by_cases hi : i = 0
      · rw [if_pos hi] at h; exact RH2F.lv_ne_vx _ h.symm
      · rw [if_neg hi] at h; exact RH2F.lv_ne_vl _ h.symm
    · exact congrArg Sum.inr (h01 i j h)
  ψinj := by
    rintro (a | i) (b | j) h
    · have := congrArg Fin.val h
      simp only [ψT, RH2F.oldE] at this
      exact congrArg Sum.inl (Subtype.ext (R.ψinj _ _ (Fin.ext this)))
    · exfalso; have := congrArg Fin.val h
      simp only [ψT, RH2F.oldE, RH2F.newE] at this
      have := (R.ψ a.1).isLt; omega
    · exfalso; have := congrArg Fin.val h
      simp only [ψT, RH2F.oldE, RH2F.newE] at this
      have := (R.ψ b.1).isLt; omega
    · have := congrArg Fin.val h
      simp only [ψT, RH2F.newE] at this
      exact congrArg Sum.inr (Fin.ext (by omega))
  ψP := by
    rintro (e | i)
    · show RH2F.leafSet P (R.ψ g) (RH2F.oldE (R.ψ g) (R.ψ e.1))
      rw [RH2F.set_old]
      exact ⟨R.ψP _, fun h => e.2 (R.ψinj _ _ h)⟩
    · exact RH2F.set_new P _ i.val i.isLt
  ψsurj := by
    intro f hf
    rcases leaf_cases' R g f with ⟨d, rfl⟩ | ⟨i, rfl⟩
    · rw [RH2F.set_old] at hf
      obtain ⟨e, rfl⟩ := R.ψsurj d hf.1
      exact ⟨Sum.inl ⟨e, fun h => hf.2 (by rw [h])⟩, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩
  φsurj := by
    intro y f hf hy
    rcases leaf_cases' R g f with ⟨d, rfl⟩ | ⟨i, rfl⟩
    · rw [RH2F.set_old] at hf
      obtain ⟨e, rfl⟩ := R.ψsurj d hf.1
      unfold MGraph.Inc at hy
      rw [RH2F.ends_old] at hy
      rcases hy with hy | hy
      · obtain ⟨a, ha⟩ := R.inc_vert (e := e) (x := (X.ends (R.ψ e)).1) (Or.inl rfl)
        exact ⟨Sum.inl a, by rw [← hy, ← ha]; rfl⟩
      · obtain ⟨a, ha⟩ := R.inc_vert (e := e) (x := (X.ends (R.ψ e)).2) (Or.inr rfl)
        exact ⟨Sum.inl a, by rw [← hy, ← ha]; rfl⟩
    · unfold MGraph.Inc at hy
      rw [ends_newE, hg] at hy
      have hx : φT R g (Sum.inr 0) = RH2F.vx X := rfl
      have hl : φT R g (Sum.inr 1) = RH2F.vl X := rfl
      have hs' : φT R g (Sum.inl s) = RH2F.lv (R.φ s) := rfl
      have ht' : φT R g (Sum.inl t) = RH2F.lv (R.φ t) := rfl
      by_cases h0 : i = 0
      · rw [if_pos h0] at hy
        rcases hy with hy | hy
        · exact ⟨Sum.inl s, hs'.trans hy⟩
        · exact ⟨Sum.inr 0, hx.trans hy⟩
      · by_cases h1 : i = 1
        · rw [if_neg h0, if_pos h1] at hy
          rcases hy with hy | hy
          · exact ⟨Sum.inr 0, hx.trans hy⟩
          · exact ⟨Sum.inl t, ht'.trans hy⟩
        · rw [if_neg h0, if_neg h1] at hy
          rcases hy with hy | hy
          · exact ⟨Sum.inr 0, hx.trans hy⟩
          · exact ⟨Sum.inr 1, hl.trans hy⟩
  hend := by
    rintro (e | i)
    · show s(((RH2F.leafG X (R.ψ g)).ends (RH2F.oldE (R.ψ g) (R.ψ e.1))).1,
          ((RH2F.leafG X (R.ψ g)).ends (RH2F.oldE (R.ψ g) (R.ψ e.1))).2) =
        Sym2.map (φT R g) (Sym2.map Sum.inl (en e.1))
      rw [RH2F.ends_old, Sym2.map_map]
      have : (φT R g ∘ Sum.inl) = (RH2F.lv (X := X)) ∘ R.φ := rfl
      rw [this, ← Sym2.map_map, ← R.hend, Sym2.map_pair_eq]
    · show s(((RH2F.leafG X (R.ψ g)).ends (RH2F.newE (R.ψ g) i.val i.isLt)).1,
          ((RH2F.leafG X (R.ψ g)).ends (RH2F.newE (R.ψ g) i.val i.isLt)).2) = Sym2.map (φT R g) (enT en g s t (Sum.inr i))
      rw [ends_newE, hg]
      simp only [enT]
      by_cases h0 : i = 0
      · rw [if_pos h0, if_pos h0, Sym2.map_pair_eq]; rfl
      · by_cases h1 : i = 1
        · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1, Sym2.map_pair_eq]; rfl
        · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1, Sym2.map_pair_eq]; rfl

end leaf


/-! ## Part 5: the three equivalences -/

theorem starOn_of_all {X : MGraph} {k : Nat} {c : Fin X.m → Fin k} (h : StarOn (fun _ => True) k c)
    (Q : Fin X.m → Prop) : StarOn Q k c :=
  ⟨fun a b hab _ _ => h.1 a b hab trivial trivial, fun w _ _ _ _ => h.2 w trivial trivial trivial trivial⟩

/-- **DMS**: the Lean conclusion `RH2F.DMS` is exactly ROOT-DMS-2 -/
theorem dms_iff : RH2F.DMS ↔ DMSP := by
  constructor
  · intro hD V E _ _ en hl hdeg
    let R := encRep en (ori en) (ori_spec en)
    have hc := hD (encG (ori en)) (R.subcubic_of (fun _ => trivial) hdeg)
      (enc_loopless en (ori en) (ori_spec en) hl) (fun _ => True)
    exact (star6P_iff en).2 ((R.colourable_iff (by decide)).1 hc)
  · intro hD G hsub hloop Q
    let R := subRep G (fun _ => True)
    have h := hD (SubV G (fun _ => True)) (SubE G (fun _ => True)) (subEn G (fun _ => True))
      (sub_loopless G _ hloop) (R.maxDeg3_of hsub)
    obtain ⟨c, hc⟩ := (R.colourable_iff (by decide)).2 ((star6P_iff _).1 h)
    exact ⟨c, starOn_of_all hc Q⟩

/-- **(II)**: the Lean hypothesis `RH2F.II` is exactly (II) of contract P15-LEAF-II -/
theorem ii_iff : RH2F.II ↔ IIP := by
  constructor
  · intro hII V E _ _ en hl hb hc g s t hst
    let o := oriG en g s t
    have ho := oriG_spec en g s t hst
    let R := encRep en o ho
    have hg : (encG o).ends (R.ψ g) = (R.φ s, R.φ t) := by
      show (encG o).ends (Fintype.equivFin E g) = _
      rw [encG_ends]
      simp only [o, oriG, if_pos rfl]
      rfl
    have hcol := hII (encG o) (fun _ => True) (enc_loopless en o ho hl) (R.bridgeless_iff.2 hb)
      (R.cubicOn_of hc) (R.ψ g) trivial
    exact (star6P_iff _).2 (((leafRep R g s t hg).colourable_iff (by decide)).1 hcol)
  · intro hII X P hloop hbr hcub g hg
    let R := subRep X P
    let g' : SubE X P := ⟨g, hg⟩
    let s' : SubV X P := ⟨(X.ends g).1, g, hg, Or.inl rfl⟩
    let t' : SubV X P := ⟨(X.ends g).2, g, hg, Or.inr rfl⟩
    have h := hII (SubV X P) (SubE X P) (subEn X P) (sub_loopless X P hloop) (R.bridgeless_iff.1 hbr)
      (R.cubicP_of (sub_hV X P) hcub) g' s' t' rfl
    exact ((leafRep R g' s' t' rfl).colourable_iff (by decide)).2 ((star6P_iff _).1 h)

/-- the ℕ-status `[g ∈ N] = t` for `t ≤ 1` against the Bool status of `EX1On` -/
theorem ind_iff {E : Type} (N : E → Prop) (g : E) (t : ℕ) (ht : t ≤ 1) : ind N g = t ↔ (N g ↔ decide (t = 1) = true) := by
  unfold ind
  by_cases hN : N g
  · rw [if_pos hN]; simp only [hN, true_iff, decide_eq_true_eq]; omega
  · rw [if_neg hN]; simp only [hN, false_iff, decide_eq_true_eq]; omega

theorem ind_bool {E : Type} (N : E → Prop) (g : E) (t : Bool) : (N g ↔ t = true) ↔ ind N g = (if t then 1 else 0) := by
  unfold ind
  cases t <;> by_cases hN : N g <;> simp [hN]

/-- **(H)**: the Lean hypothesis `RH2F.Hyp` is exactly (H) of contract P11-H -/
theorem hyp_iff : RH2F.Hyp ↔ HP := by
  constructor
  · intro hH V E _ _ en hl hconn hb hc hn h2c
    let R := encRep en (ori en) (ori_spec en)
    have hV := cubic_hV en hc
    have hin : RH2F.InG (encG (ori en)) (fun _ => True) :=
      ⟨enc_loopless en _ (ori_spec en) hl, R.connectedOn_of hconn, R.bridgeless_iff.2 hb, R.cubicOn_of hc⟩
    have hex := hH (encG (ori en)) (fun _ => True) hin (by rw [R.vcount_eq hV]; exact hn)
      ((R.twoCutReduced_iff hV).2 h2c)
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
  · rintro hH X P ⟨hloop, hconn, hbr, hcub⟩ hn h2c
    let R := subRep X P
    have hV := sub_hV X P
    have hex := hH (SubV X P) (SubE X P) (subEn X P) (sub_loopless X P hloop) (R.connectedP_of hV hconn)
      (R.bridgeless_iff.1 hbr) (R.cubicP_of hV hcub) (by rw [← R.vcount_eq hV]; exact hn)
      ((R.twoCutReduced_iff hV).1 h2c)
    intro g hg t ⟨N, hpm, hst⟩
    let g' : SubE X P := ⟨g, hg⟩
    have hpm' := (R.pmOn_iff hV N hpm.1).1 hpm
    have hind : ind (fun e => N (R.ψ e)) g' = (if t then 1 else 0) := (ind_bool _ g' t).1 hst
    obtain ⟨N'', hpm'', hind'', c, hr, hsc, hcl⟩ :=
      hex g' (if t then 1 else 0) (by cases t <;> simp) ⟨_, hpm', hind⟩
    have hfun : (fun e => R.liftN N'' (R.ψ e)) = N'' := funext fun e => propext (R.liftN_ψ N'' e)
    refine ⟨R.liftN N'', (R.pmOn_iff hV _ (R.liftN_P N'')).2 (by rw [hfun]; exact hpm''), ?_,
      R.liftC 0 (ofN c), ?_, ?_⟩
    · have := (ind_bool N'' g' t).2 hind''
      show R.liftN N'' (R.ψ g') ↔ t = true
      rw [R.liftN_ψ]; exact this
    · rw [R.starOn_iff]
      have : (fun e => R.liftC 0 (ofN c) (R.ψ e)) = ofN c := funext fun e => R.liftC_ψ _ _ e
      rw [this]
      exact (starP_congr _ c (ofN c) (fun e f => by
        have := hr e; have := hr f; unfold ofN; rw [Fin.ext_iff]; simp only; omega)).1 hsc
    · rw [R.classOn_iff]
      have h1 : (fun e => R.liftC 0 (ofN c) (R.ψ e)) = ofN c := funext fun e => R.liftC_ψ _ _ e
      have h2 : toN (ofN c) = c := funext fun e => by
        have := hr e; unfold toN ofN; simp only; omega
      rw [h1, h2, hfun]; exact hcl

/-- **Statement fidelity of fact 3e79907c.** The three propositions of `RH2F.rh2_final : Hyp → II → DMS` are
    equivalent to the plain statements (H) (contract P11-H), (II) (contract P15-LEAF-II) and ROOT-DMS-2 -/
theorem fidelity : (RH2F.Hyp ↔ HP) ∧ (RH2F.II ↔ IIP) ∧ (RH2F.DMS ↔ DMSP) := ⟨hyp_iff, ii_iff, dms_iff⟩

/-- RH2 (fact 6bfcd4d5) for the plain statements: (H) ∧ (II) ⇒ ROOT-DMS-2 -/
theorem rh2_plain : HP → IIP → DMSP := fun hH hII =>
  dms_iff.1 (RH2F.rh2_final (hyp_iff.2 hH) (ii_iff.2 hII))

end RH2Fid

namespace RH2Fid
open MGraph
open Classical

/-! ## Part 6: witnesses (sanity checks of the definitions on small multigraphs, positive and negative) -/

/-- the plain reading of an `MGraph` with all its edges: vertices `Fin n`, edges `Fin m`, unordered ends -/
def fullEn (G : MGraph) (f : Fin G.m) : Sym2 (Fin G.n) := s((G.ends f).1, (G.ends f).2)

def fullRep (G : MGraph) : Rep (fullEn G) G (fun _ => True) where
  φ := id
  ψ := id
  φinj := fun _ _ h => h
  ψinj := fun _ _ h => h
  ψP := fun _ => trivial
  ψsurj := fun f _ => ⟨f, rfl⟩
  φsurj := fun x _ _ _ => ⟨x, rfl⟩
  hend := fun e => by simp [fullEn]

section checks
variable (G : MGraph)

theorem full_hV (h : ∀ x : Fin G.n, ∃ f : Fin G.m, G.Inc f x) : ∀ v, ∃ e, v ∈ fullEn G e := by
  intro v
  obtain ⟨f, hf⟩ := h v
  exact ⟨f, ((fullRep G).inc_iff f v).1 hf⟩

/-- cubic, from a table `t x` of the three edges at each vertex -/
theorem cubicOn_of_table (t : Fin G.n → Fin G.m × Fin G.m × Fin G.m)
    (h : ∀ x, G.Inc (t x).1 x ∧ G.Inc (t x).2.1 x ∧ G.Inc (t x).2.2 x ∧ (t x).1 ≠ (t x).2.1 ∧
      (t x).1 ≠ (t x).2.2 ∧ (t x).2.1 ≠ (t x).2.2 ∧
      ∀ d, G.Inc d x → d = (t x).1 ∨ d = (t x).2.1 ∨ d = (t x).2.2) :
    CubicOn (G := G) (fun _ => True) := by
  intro x _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h x
  exact ⟨_, _, _, trivial, trivial, trivial, h1, h2, h3, h4, h5, h6, fun d _ hd => h7 d hd⟩

/-- bridgeless, from: every vertex 2-colouring separating the ends of an edge `e` separates the ends of another
    edge -/
theorem bridgeless_of_check
    (h : ∀ e : Fin G.m, ∀ U : Fin G.n → Bool, U (G.ends e).1 = true → U (G.ends e).2 = false →
      ∃ f : Fin G.m, f ≠ e ∧ U (G.ends f).1 ≠ U (G.ends f).2) :
    BridgelessOn (G := G) (fun _ => True) := by
  intro e _ B
  obtain ⟨f, hne, hf⟩ := h e B.U B.hu B.hv
  exact hf (B.sep f trivial hne)

theorem connectedOn_of_check
    (h : ∀ U : Fin G.n → Bool, (∀ f : Fin G.m, U (G.ends f).1 = U (G.ends f).2) →
      ∀ f g : Fin G.m, U (G.ends f).1 = U (G.ends g).1) :
    ConnectedOn (G := G) (fun _ => True) := fun U hU f g _ _ => h U (fun f => hU f trivial) f g

/-- no 2-edge-cut at all (hence 2-cut-reduced) -/
theorem twoCutReduced_of_check
    (h : ∀ S : Fin G.n → Bool, (Finset.univ.filter (fun f : Fin G.m => S (G.ends f).1 ≠ S (G.ends f).2)).card ≠ 2) :
    RH2F.TwoCutReducedOn (X := G) (fun _ => True) := by
  intro S ⟨e1, e2, hne, c1, c2, hall⟩
  exfalso
  apply h S
  apply Finset.card_eq_two.2
  refine ⟨e1, e2, hne, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hf; exact hall f ⟨trivial, hf⟩
  · rintro (rfl | rfl)
    · exact c1.2
    · exact c2.2

/-- a vertex index taken mod `n` -/
def finN (h0 : 0 < G.n) (i : Nat) : Fin G.n := ⟨i % G.n, Nat.mod_lt _ h0⟩

/-- `walkB ok a l b`: the vertex list `a :: l` is a walk ending at `b` whose steps use edges `f` with `ok f` -/
def walkB (ok : Fin G.m → Bool) : Fin G.n → List (Fin G.n) → Fin G.n → Bool
  | a, [], b => decide (a = b)
  | a, c :: l, b => (List.finRange G.m).any (fun f => ok f && (decide (G.ends f = (a, c)) ||
      decide (G.ends f = (c, a)))) && walkB ok c l b

theorem walkB_sound (ok : Fin G.m → Bool) (U : Fin G.n → Bool)
    (hU : ∀ f, ok f = true → U (G.ends f).1 = U (G.ends f).2) :
    ∀ (l : List (Fin G.n)) (a b : Fin G.n), walkB G ok a l b = true → U a = U b
  | [], a, b, h => by
    simp only [walkB, decide_eq_true_eq] at h; rw [h]
  | c :: l, a, b, h => by
    simp only [walkB, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨f, _, hf⟩, hl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hok, hj⟩ := hf
    have h1 := hU f hok
    have hac : U a = U c := by
      rcases hj with hj | hj <;> rw [hj] at h1
      · exact h1
      · exact h1.symm
    rw [hac]; exact walkB_sound ok U hU l c b hl

/-- bridgeless, from a walk around every edge `e` (from one end to the other, avoiding `e`) -/
theorem bridgeless_of_walks (h0 : 0 < G.n) (W : List (List Nat))
    (hW : (List.finRange G.m).all (fun e => walkB G (fun f => f != e) (G.ends e).1
      ((W.getD e.val []).map (finN G h0)) (G.ends e).2) = true) :
    BridgelessOn (G := G) (fun _ => True) := by
  intro e _ B
  have he := List.all_eq_true.1 hW e (List.mem_finRange e)
  have := walkB_sound G (fun f => f != e) B.U (fun f hf => B.sep f trivial (by simpa using hf)) _ _ _ he
  rw [B.hu, B.hv] at this
  exact Bool.noConfusion this

/-- connected, from walks from vertex `0` to every vertex -/
theorem connectedOn_of_walks (h0 : 0 < G.n) (W : List (List Nat))
    (hW : (List.finRange G.n).all (fun v => walkB G (fun _ => true) (finN G h0 0)
      ((W.getD v.val []).map (finN G h0)) v) = true) :
    ConnectedOn (G := G) (fun _ => True) := by
  intro U hU f g _ _
  have key : ∀ v, U (finN G h0 0) = U v := fun v =>
    walkB_sound G (fun _ => true) U (fun f _ => hU f trivial) _ _ _ (List.all_eq_true.1 hW v (List.mem_finRange v))
  rw [← key (G.ends f).1, ← key (G.ends g).1]

/-- the position of the pair `i < j` in the list of pairs of `Fin m` in lexicographic order -/
def pairIdx (m i j : Nat) : Nat := i * m - i * (i + 1) / 2 + (j - i - 1)

/-- no 2-edge-cut (hence 2-cut-reduced), from walks from vertex `0` to every vertex avoiding any two edges -/
theorem twoCutReduced_of_walks (h0 : 0 < G.n) (T : List (List (List Nat)))
    (hT : (List.finRange G.m).all (fun e1 => (List.finRange G.m).all (fun e2 => !(decide (e1.val < e2.val)) ||
      (List.finRange G.n).all (fun v => walkB G (fun f => f != e1 && f != e2) (finN G h0 0)
        (((T.getD (pairIdx G.m e1.val e2.val) []).getD v.val []).map (finN G h0)) v))) = true) :
    RH2F.TwoCutReducedOn (X := G) (fun _ => True) := by
  intro S ⟨e1, e2, hne, c1, c2, hall⟩
  exfalso
  have key : ∀ a b : Fin G.m, a.val < b.val → (∀ d, d ≠ a → d ≠ b → S (G.ends d).1 = S (G.ends d).2) →
      S (G.ends a).1 = S (G.ends a).2 := by
    intro a b hab hS
    have ha := List.all_eq_true.1 hT a (List.mem_finRange a)
    have hb := List.all_eq_true.1 ha b (List.mem_finRange b)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    rcases hb with hb | hb
    · exact absurd hab hb
    have hv : ∀ v, S (finN G h0 0) = S v := fun v =>
      walkB_sound G _ S (fun f hf => by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
        exact hS f hf.1 hf.2) _ _ _ (List.all_eq_true.1 hb v (List.mem_finRange v))
    rw [← hv (G.ends a).1, ← hv (G.ends a).2]
  have hS : ∀ d, d ≠ e1 → d ≠ e2 → S (G.ends d).1 = S (G.ends d).2 := by
    intro d h1 h2
    by_contra hc
    rcases hall d ⟨trivial, hc⟩ with h | h
    · exact h1 h
    · exact h2 h
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact c1.2 (key e1 e2 h hS)
  · exact c2.2 (key e2 e1 h (fun d h1 h2 => hS d h2 h1))

/-- a table of three edges per vertex, from a list of index triples -/
def tab3 (hm : 0 < G.m) (l : List (Nat × Nat × Nat)) (x : Fin G.n) : Fin G.m × Fin G.m × Fin G.m :=
  let p := l.getD x.val (0, 0, 0)
  (⟨p.1 % G.m, Nat.mod_lt _ hm⟩, ⟨p.2.1 % G.m, Nat.mod_lt _ hm⟩, ⟨p.2.2 % G.m, Nat.mod_lt _ hm⟩)

end checks

/-! certificates (walks found by breadth-first search, fid/gencert.py) -/
-- wK4
def br_wK4 : List (List Nat) := [[2, 1], [1, 2], [1, 3], [0, 2], [0, 3], [0, 3]]
def cn_wK4 : List (List Nat) := [[], [1], [2], [3]]
-- k33
def br_k33 : List (List Nat) := [[4, 1, 3], [4, 0, 3], [4, 0, 3], [3, 1, 4], [3, 0, 4], [3, 0, 4], [3, 1, 5], [3, 0, 5], [3, 0, 5]]
def cn_k33 : List (List Nat) := [[], [3, 1], [3, 2], [3], [4], [5]]
def tc_k33 : List (List (List Nat)) := [[[], [4, 1], [4, 2], [4, 2, 3], [4], [5]], [[], [4, 1], [4, 2], [4, 1, 3], [4], [5]], [[], [5, 1], [5, 2], [5, 1, 3], [5, 1, 4], [5]], [[], [5, 1], [4, 2], [4, 2, 3], [4], [5]], [[], [4, 1], [5, 2], [4, 1, 3], [4], [5]], [[], [4, 1], [4, 2], [4, 1, 3], [4], [4, 1, 5]], [[], [4, 1], [4, 2], [4, 1, 3], [4], [5]], [[], [4, 1], [4, 2], [4, 1, 3], [4], [5]], [[], [4, 1], [4, 2], [3], [4], [5]], [[], [5, 1], [3, 2], [3], [3, 2, 4], [5]], [[], [5, 1], [3, 2], [3], [4], [5]], [[], [4, 1], [3, 2], [3], [4], [5]], [[], [4, 1], [3, 2], [3], [4], [3, 2, 5]], [[], [4, 1], [3, 2], [3], [4], [5]], [[], [4, 1], [3, 2], [3], [4], [5]], [[], [3, 1], [5, 2], [3], [3, 1, 4], [5]], [[], [3, 1], [4, 2], [3], [4], [5]], [[], [3, 1], [5, 2], [3], [4], [5]], [[], [3, 1], [4, 2], [3], [4], [3, 1, 5]], [[], [3, 1], [4, 2], [3], [4], [5]], [[], [3, 1], [4, 2], [3], [4], [5]], [[], [3, 1], [3, 2], [3], [3, 2, 4], [5]], [[], [3, 1], [3, 2], [3], [3, 1, 4], [5]], [[], [3, 1], [3, 2], [3], [3, 1, 4], [3, 1, 5]], [[], [3, 1], [3, 2], [3], [3, 1, 4], [5]], [[], [3, 1], [3, 2], [3], [3, 1, 4], [5]], [[], [3, 1], [3, 2], [3], [4], [5]], [[], [3, 1], [3, 2], [3], [4], [3, 1, 5]], [[], [3, 1], [3, 2], [3], [4], [5]], [[], [3, 1], [3, 2], [3], [4], [5]], [[], [3, 1], [3, 2], [3], [4], [3, 1, 5]], [[], [3, 1], [3, 2], [3], [4], [5]], [[], [3, 1], [3, 2], [3], [4], [5]], [[], [3, 1], [3, 2], [3], [4], [3, 2, 5]], [[], [3, 1], [3, 2], [3], [4], [3, 1, 5]], [[], [3, 1], [3, 2], [3], [4], [5]]]
-- wPrism
def br_wPrism : List (List Nat) := [[2, 1], [0, 2], [1, 0], [5, 4], [3, 5], [4, 3], [1, 4, 3], [0, 3, 4], [1, 4, 5]]
def cn_wPrism : List (List Nat) := [[], [1], [2], [3], [1, 4], [2, 5]]
-- wDig
def br_wDig : List (List Nat) := [[1], [1], [0, 3, 2], [3], [3], [2, 1, 0]]
def cn_wDig : List (List Nat) := [[], [1], [1, 2], [3]]
-- wD8
def br_wD8 : List (List Nat) := [[2, 1], [1, 2], [0, 2], [2, 3], [1, 3], [6, 5], [5, 6], [4, 6], [6, 7], [5, 7], [1, 0, 7, 5, 4], [5, 4, 3, 1, 0]]
def cn_wD8 : List (List Nat) := [[], [1], [2], [1, 3], [1, 3, 4], [7, 5], [7, 6], [7]]
-- wPet
def br_wPet : List (List Nat) := [[4, 3, 2, 1], [0, 4, 3, 2], [1, 0, 4, 3], [2, 1, 0, 4], [3, 2, 1, 0], [1, 2, 7, 5], [0, 4, 9, 6], [1, 0, 5, 7], [2, 1, 6, 8], [3, 2, 7, 9], [0, 1, 2, 7], [2, 1, 6, 9], [4, 3, 8, 6], [1, 0, 5, 8], [3, 2, 7, 5]]
def cn_wPet : List (List Nat) := [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]]
def tc_wPet : List (List (List Nat)) := [[[], [4, 9, 6, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 9, 6, 1], [5, 7, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 9, 6, 1], [5, 7, 2], [5, 8, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [5, 7, 2, 1], [5, 7, 2], [5, 8, 3], [5, 7, 9, 4], [5], [5, 8, 6], [5, 7], [5, 8], [5, 7, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [4, 3, 8, 5], [4, 9, 6], [4, 9, 7], [4, 3, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [5, 8, 6], [5, 7], [5, 8], [5, 7, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [4, 9, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [5, 8, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [4, 3, 2, 1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [4, 3, 8], [4, 9]], [[], [1], [5, 7, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [5, 7, 2], [5, 8, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [5, 7, 2], [5, 8, 3], [1, 6, 9, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [1, 6, 8, 5], [1, 6], [4, 9, 7], [1, 6, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [4, 9, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [4, 3, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [5, 8, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [5, 8, 3], [1, 6, 9, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 6, 9, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [5, 8, 6], [5, 7], [5, 8], [5, 7, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [1, 2, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [5, 8], [5, 7, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [5], [1, 6], [5, 7], [1, 6, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [4, 9, 6], [1, 2, 7], [4, 3, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 6, 8, 5], [1, 6], [4, 9, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 6, 8, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [4, 3, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [1, 2, 7, 5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [5, 8, 6], [5, 7], [5, 8], [5, 7, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [5, 8, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [4, 9, 6], [5, 7], [4, 3, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [4, 9, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [5, 7, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [1, 6, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [1, 2, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [5, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [1, 6, 8], [4, 9]], [[], [1], [1, 2], [4, 3], [4], [5], [1, 6], [5, 7], [4, 3, 8], [4, 9]]]


/-! ### K₄ -/

/-- K₄ -/
def wK4 : MGraph := ofList 4 [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)] (by decide)

def cK4 : Fin wK4.m → Fin 6 := colOf wK4 [0, 1, 2, 3, 4, 5]
/-- the proper 3-edge-colouring of K₄ (its 1-factorisation); it has a bicoloured 4-cycle -/
def cK4bad : Fin wK4.m → Fin 6 := colOf wK4 [0, 1, 2, 2, 1, 0]

theorem wK4_loopless : Loopless wK4 := by unfold Loopless; decide +kernel
theorem wK4_hV : ∀ v, ∃ e, v ∈ fullEn wK4 e := full_hV wK4 (by decide +kernel)
theorem wK4_cubic : CubicOn (G := wK4) (fun _ => True) :=
  cubicOn_of_table wK4 (tab3 wK4 (by decide) [(0,1,2), (0,3,4), (1,3,5), (2,4,5)]) (by decide +kernel)
theorem wK4_bridgeless : BridgelessOn (G := wK4) (fun _ => True) := bridgeless_of_walks wK4 (by decide) br_wK4 (by decide +kernel)
theorem wK4_connected : ConnectedOn (G := wK4) (fun _ => True) := connectedOn_of_walks wK4 (by decide) cn_wK4 (by decide +kernel)
theorem wK4_star : Star (G := wK4) 6 cK4 := wK4.star_of_check cK4 (by decide +kernel)
theorem wK4_bad : ¬ Star (G := wK4) 6 cK4bad := wK4.not_star_of_walk cK4bad 0 1 3 2 0 0 4 5 1 (by decide +kernel)

/-- the plain reading of the same facts -/
theorem wK4_plain : LooplessP (fullEn wK4) ∧ CubicP (fullEn wK4) ∧ BridgelessP (fullEn wK4) ∧
    ConnectedP (fullEn wK4) ∧ StarP (fullEn wK4) cK4 ∧ ¬ StarP (fullEn wK4) cK4bad := by
  refine ⟨fun e h => wK4_loopless e (by unfold fullEn at h; exact Sym2.mk_isDiag_iff.1 h),
    (fullRep wK4).cubicP_of wK4_hV wK4_cubic, (fullRep wK4).bridgeless_iff.1 wK4_bridgeless,
    (fullRep wK4).connectedP_of wK4_hV wK4_connected, (fullRep wK4).starOn_iff cK4 |>.1 wK4_star, ?_⟩
  -- directly from the plain definition: the 4-cycle 0 1 3 2 with edges 01, 13, 32, 20 is bicoloured
  intro h
  exact h.2.2 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨1, by decide⟩
    (by unfold IsCycle4 fullEn; decide) ⟨rfl, rfl⟩


/-! ### K₃,₃ (library `MGraph.k33`, colouring `k33Col`) -/

/-- `k33Col` with edge 1 recoloured: edges 0 = (0,3) and 1 = (1,3) share vertex 3 and colour 0 -/
def cK33bad : Fin k33.m → Fin 6 := colOf k33 [0, 0, 2, 1, 3, 4, 2, 4, 5]

theorem wK33_cubic : CubicOn (G := k33) (fun _ => True) :=
  cubicOn_of_table k33 (tab3 k33 (by decide) [(0,3,6), (1,4,7), (2,5,8), (0,1,2), (3,4,5), (6,7,8)]) (by decide +kernel)
theorem wK33_bridgeless : BridgelessOn (G := k33) (fun _ => True) := bridgeless_of_walks k33 (by decide) br_k33 (by decide +kernel)
theorem wK33_2cr : RH2F.TwoCutReducedOn (X := k33) (fun _ => True) := twoCutReduced_of_walks k33 (by decide) tc_k33 (by decide +kernel)
theorem wK33_bad : ¬ Star (G := k33) 6 cK33bad := k33.not_star_of_adj cK33bad 0 1 3 (by decide +kernel)

theorem wK33_plain : StarP (fullEn k33) k33Col ∧ ¬ StarP (fullEn k33) cK33bad ∧
    TwoCutReducedP (fullEn k33) := by
  refine ⟨(fullRep k33).starOn_iff k33Col |>.1 k33_star6, ?_,
    ((fullRep k33).twoCutReduced_iff (full_hV k33 (by decide +kernel))).1 wK33_2cr⟩
  intro h
  exact h.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) ⟨⟨3, by decide⟩, by unfold fullEn; decide,
    by unfold fullEn; decide⟩ (by decide)

/-! ### the prism K₃ □ K₂ -/

def wPrism : MGraph := ofList 6 [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)] (by decide)
def cPrism : Fin wPrism.m → Fin 6 := colOf wPrism [0, 1, 2, 0, 1, 2, 3, 4, 5]
/-- a proper 3-edge-colouring; the path 0 1 2 5 4 (edges 01, 12, 25, 54) is bicoloured -/
def cPrismBad : Fin wPrism.m → Fin 6 := colOf wPrism [0, 1, 2, 0, 1, 2, 1, 2, 0]

theorem wPrism_cubic : CubicOn (G := wPrism) (fun _ => True) :=
  cubicOn_of_table wPrism (tab3 wPrism (by decide) [(0,2,6), (0,1,7), (1,2,8), (3,5,6), (3,4,7), (4,5,8)])
    (by decide +kernel)
theorem wPrism_bridgeless : BridgelessOn (G := wPrism) (fun _ => True) := bridgeless_of_walks wPrism (by decide) br_wPrism (by decide +kernel)
theorem wPrism_star : Star (G := wPrism) 6 cPrism := wPrism.star_of_check cPrism (by decide +kernel)
theorem wPrism_bad : ¬ Star (G := wPrism) 6 cPrismBad := wPrism.not_star_of_walk cPrismBad 0 1 2 5 4 0 1 8 4 (by decide +kernel)

theorem wPrism_plain : StarP (fullEn wPrism) cPrism ∧ ¬ StarP (fullEn wPrism) cPrismBad := by
  refine ⟨(fullRep wPrism).starOn_iff cPrism |>.1 wPrism_star, ?_⟩
  intro h
  exact h.2.1 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨5, by decide⟩ ⟨4, by decide⟩ ⟨0, by decide⟩
    ⟨1, by decide⟩ ⟨8, by decide⟩ ⟨4, by decide⟩ (by unfold IsPath4 fullEn; decide) ⟨by decide, by decide⟩

/-! ### a digon multigraph: C₄ with two opposite edges doubled -/

def wDig : MGraph := ofList 4 [(0,1),(0,1),(1,2),(2,3),(2,3),(3,0)] (by decide)
def cDig : Fin wDig.m → Fin 6 := colOf wDig [0, 1, 2, 0, 1, 3]
/-- the two parallel edges 0 and 1 get the same colour -/
def cDigBad : Fin wDig.m → Fin 6 := colOf wDig [0, 0, 2, 0, 1, 3]

theorem wDig_loopless : Loopless wDig := by unfold Loopless; decide +kernel
theorem wDig_cubic : CubicOn (G := wDig) (fun _ => True) :=
  cubicOn_of_table wDig (tab3 wDig (by decide) [(0,1,5), (0,1,2), (2,3,4), (3,4,5)]) (by decide +kernel)
theorem wDig_bridgeless : BridgelessOn (G := wDig) (fun _ => True) := bridgeless_of_walks wDig (by decide) br_wDig (by decide +kernel)
theorem wDig_star : Star (G := wDig) 6 cDig := wDig.star_of_check cDig (by decide +kernel)
theorem wDig_bad : ¬ Star (G := wDig) 6 cDigBad := wDig.not_star_of_adj cDigBad 0 1 0 (by decide +kernel)

theorem wDig_plain : CubicP (fullEn wDig) ∧ BridgelessP (fullEn wDig) ∧ StarP (fullEn wDig) cDig ∧
    ¬ StarP (fullEn wDig) cDigBad := by
  have hV := full_hV wDig (by decide +kernel)
  refine ⟨(fullRep wDig).cubicP_of hV wDig_cubic, (fullRep wDig).bridgeless_iff.1 wDig_bridgeless,
    (fullRep wDig).starOn_iff cDig |>.1 wDig_star, ?_⟩
  -- the parallel edges 0 and 1 are distinct edges with a common end
  intro h
  exact h.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) ⟨⟨0, by decide⟩, by unfold fullEn; decide,
    by unfold fullEn; decide⟩ (by decide)

/-! ### a pendant edge: the leaf graph T(K₄, g) for g = 01 -/

def g0 : Fin wK4.m := ⟨0, by decide⟩
/-- colours of the leaf graph edges: old edge 0 (= g, not an edge of T) gets 5, old edges 1–5, then sx, xt, xℓ -/
def cLeaf : Fin (RH2F.leafG wK4 g0).m → Fin 6 := colOf (RH2F.leafG wK4 g0) [5, 0, 1, 1, 2, 3, 4, 5, 0]

def leafB : Fin (RH2F.leafG wK4 g0).m → Bool := fun e => decide (e.val ≠ 0)

theorem leafB_eq : (fun e => leafB e = true) = RH2F.leafSet (fun _ => True) g0 := by
  funext e
  apply propext
  unfold leafB RH2F.leafSet
  by_cases h : e.val < wK4.m
  · rw [dif_pos h]
    simp only [decide_eq_true_iff, true_and, ne_eq, Fin.ext_iff, g0]
  · rw [dif_neg h]
    simp only [decide_eq_true_iff, iff_true]
    intro h0; apply h; rw [h0]; decide

theorem wLeaf_star : StarOn (RH2F.leafSet (fun _ => True) g0) 6 cLeaf := by
  rw [← leafB_eq]
  exact (RH2F.leafG wK4 g0).starOn_of_check leafB cLeaf (by decide +kernel)

theorem wLeaf_vl_only : ∀ f : Fin (RH2F.leafG wK4 g0).m, (RH2F.leafG wK4 g0).Inc f (RH2F.vl wK4) →
    f = RH2F.newE g0 2 (by decide) := by decide +kernel

/-- T(K₄, g) is not cubic: `ℓ` meets one edge -/
theorem wLeaf_not_cubic : ¬ CubicOn (RH2F.leafSet (fun _ => True) g0) := by
  intro h
  obtain ⟨a, b, _, _, _, _, ha, hb, _, hab, _⟩ := h (RH2F.vl wK4)
    ⟨RH2F.newE g0 2 (by decide), RH2F.set_new _ _ _ _, by decide⟩
  exact hab ((wLeaf_vl_only a ha).trans (wLeaf_vl_only b hb).symm)

/-- the pendant edge `xℓ` is a bridge cut -/
def leafCut : (RH2F.leafG wK4 g0).CutOn (RH2F.leafSet (fun _ => True) g0) (RH2F.newE g0 2 (by decide)) where
  U := fun y => decide (y ≠ RH2F.vl wK4)
  hu := by decide
  hv := by decide
  sep := by
    have : ∀ f : Fin (RH2F.leafG wK4 g0).m, f ≠ RH2F.newE g0 2 (by decide) →
        decide (((RH2F.leafG wK4 g0).ends f).1 ≠ RH2F.vl wK4) =
          decide (((RH2F.leafG wK4 g0).ends f).2 ≠ RH2F.vl wK4) := by
      decide +kernel
    exact fun f _ hf => this f hf

theorem wLeaf_not_bridgeless : ¬ BridgelessOn (RH2F.leafSet (fun _ => True) g0) :=
  fun h => h _ (RH2F.set_new _ _ _ _) leafCut

/-- the plain reading: `T(K₄, 01)` (plain construction `enT`) is star 6-colourable, not cubic, and its pendant edge
    `xℓ` is a bridge (deleting it increases the number of components) -/
theorem wLeaf_plain :
    Star6P (enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩) ∧
    ¬ CubicP (enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩) ∧
    IsBridge (enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩) (Sum.inr 2) := by
  have hg : wK4.ends ((fullRep wK4).ψ g0) = ((fullRep wK4).φ ⟨0, by decide⟩, (fullRep wK4).φ ⟨1, by decide⟩) := by
    decide
  let RT := leafRep (fullRep wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩ hg
  refine ⟨(star6P_iff _).2 ((RT.colourable_iff (by decide)).1 ⟨cLeaf, wLeaf_star⟩),
    fun h => wLeaf_not_cubic (RT.cubicOn_of h), ?_⟩
  have h2 : enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩ (Sum.inr 2) = s(Sum.inr 0, Sum.inr 1) := rfl
  exact (bridge_iff _ _ h2).2 ((RT.cut_iff (Sum.inr 2) h2).1 ⟨leafCut⟩)


/-! ### the hypotheses of (H): a negative instance (a nontrivial 2-edge-cut) and a positive one (Petersen) -/

/-- two diamonds joined in a ring: a connected bridgeless cubic simple graph on 8 vertices with the 2-edge-cut
    {34, 70} whose two sides have 4 vertices each -/
def wD8 : MGraph :=
  ofList 8 [(0,1),(0,2),(1,2),(1,3),(2,3),(4,5),(4,6),(5,6),(5,7),(6,7),(3,4),(7,0)] (by decide)

theorem wD8_inG : RH2F.InG wD8 (fun _ => True) :=
  ⟨by unfold Loopless; decide +kernel, connectedOn_of_walks wD8 (by decide) cn_wD8 (by decide +kernel), bridgeless_of_walks wD8 (by decide) br_wD8 (by decide +kernel),
    cubicOn_of_table wD8 (tab3 wD8 (by decide) [(0,1,11), (0,2,3), (1,2,4), (3,4,10), (5,6,10), (5,7,8), (6,7,9),
      (8,9,11)]) (by decide +kernel)⟩

def sD8 : Fin wD8.n → Bool := fun v => decide (v.val < 4)

theorem wD8_not_2cr : ¬ RH2F.TwoCutReducedOn (X := wD8) (fun _ => True) := by
  have hV := full_hV wD8 (by decide +kernel)
  intro h
  have hall : ∀ d : Fin wD8.m, sD8 (wD8.ends d).1 ≠ sD8 (wD8.ends d).2 → d = ⟨10, by decide⟩ ∨ d = ⟨11, by decide⟩ := by
    decide +kernel
  have htc : RH2F.TwoCut (X := wD8) (fun _ => True) sD8 :=
    ⟨⟨10, by decide⟩, ⟨11, by decide⟩, by decide, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
      fun d hd => hall d hd.2⟩
  rcases h sD8 htc with h1 | h1 <;> rw [(fullRep wD8).scount_eq hV] at h1 <;> revert h1 <;> decide +kernel

theorem wD8_plain : ¬ TwoCutReducedP (fullEn wD8) := fun h =>
  wD8_not_2cr (((fullRep wD8).twoCutReduced_iff (full_hV wD8 (by decide +kernel))).2 h)

/-- the Petersen graph -/
def wPet : MGraph := ofList 10 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),
  (8,5)] (by decide)

theorem wPet_inG : RH2F.InG wPet (fun _ => True) :=
  ⟨by unfold Loopless; decide +kernel, connectedOn_of_walks wPet (by decide) cn_wPet (by decide +kernel), bridgeless_of_walks wPet (by decide) br_wPet (by decide +kernel),
    cubicOn_of_table wPet (tab3 wPet (by decide) [(0,4,5), (0,1,6), (1,2,7), (2,3,8), (3,4,9), (5,10,14), (6,12,13),
      (7,10,11), (8,13,14), (9,11,12)]) (by decide +kernel)⟩

theorem wPet_vcount : RH2F.vcount (X := wPet) (fun _ => True) = 10 := by
  rw [(fullRep wPet).vcount_eq (full_hV wPet (by decide +kernel)), Fintype.card_fin]; rfl

theorem wPet_2cr : RH2F.TwoCutReducedOn (X := wPet) (fun _ => True) := twoCutReduced_of_walks wPet (by decide) tc_wPet (by decide +kernel)

/-- the premise of `RH2F.Hyp` is satisfiable (so `Hyp` is not vacuous): the Petersen graph meets it -/
theorem hyp_premise_witness : RH2F.InG wPet (fun _ => True) ∧ 10 ≤ RH2F.vcount (X := wPet) (fun _ => True) ∧
    RH2F.TwoCutReducedOn (X := wPet) (fun _ => True) := ⟨wPet_inG, by rw [wPet_vcount], wPet_2cr⟩

end RH2Fid

namespace RH2Fid
open MGraph

/-- **Statement fidelity of fact 3e79907c (bundle).**
    (1) `RH2F.Hyp ↔ HP`, `RH2F.II ↔ IIP`, `RH2F.DMS ↔ DMSP` (the plain statements (H) of P11-H, (II) of P15-LEAF-II,
        ROOT-DMS-2 over arbitrary finite vertex and edge types);
    (2) hence `HP → IIP → DMSP` (RH2 for the plain statements);
    (3) witnesses: K₄ (plain: loopless, cubic, bridgeless, connected, a star colouring; the 1-factorisation is not
        star: bicoloured 4-cycle), K₃,₃ (a star colouring; a colouring with two equal colours at a vertex is not star;
        2-cut-reduced), the prism (a star colouring; a proper 3-edge-colouring with a bicoloured 4-edge path is not
        star), C₄ with two opposite edges doubled (cubic, bridgeless, a star colouring; equal colours on two parallel
        edges is not star), the leaf graph T(K₄, 01) (star 6-colourable, not cubic, its pendant edge xℓ is a bridge),
        the ring of two diamonds (not 2-cut-reduced), and the Petersen graph (it satisfies the premise of `RH2F.Hyp`). -/
theorem fidelity_bundle :
    ((RH2F.Hyp ↔ HP) ∧ (RH2F.II ↔ IIP) ∧ (RH2F.DMS ↔ DMSP)) ∧ (HP → IIP → DMSP) ∧
    ((LooplessP (fullEn wK4) ∧ CubicP (fullEn wK4) ∧ BridgelessP (fullEn wK4) ∧ ConnectedP (fullEn wK4) ∧
        StarP (fullEn wK4) cK4 ∧ ¬ StarP (fullEn wK4) cK4bad) ∧
      (StarP (fullEn k33) k33Col ∧ ¬ StarP (fullEn k33) cK33bad ∧ TwoCutReducedP (fullEn k33)) ∧
      (StarP (fullEn wPrism) cPrism ∧ ¬ StarP (fullEn wPrism) cPrismBad) ∧
      (CubicP (fullEn wDig) ∧ BridgelessP (fullEn wDig) ∧ StarP (fullEn wDig) cDig ∧ ¬ StarP (fullEn wDig) cDigBad) ∧
      (Star6P (enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩) ∧
        ¬ CubicP (enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩) ∧
        IsBridge (enT (fullEn wK4) g0 ⟨0, by decide⟩ ⟨1, by decide⟩) (Sum.inr 2)) ∧
      (RH2F.InG wD8 (fun _ => True) ∧ ¬ TwoCutReducedP (fullEn wD8)) ∧
      (RH2F.InG wPet (fun _ => True) ∧ 10 ≤ RH2F.vcount (X := wPet) (fun _ => True) ∧
        RH2F.TwoCutReducedOn (X := wPet) (fun _ => True))) :=
  ⟨fidelity, rh2_plain, wK4_plain, wK33_plain, wPrism_plain, wDig_plain, wLeaf_plain, ⟨wD8_inG, wD8_plain⟩,
    hyp_premise_witness⟩

end RH2Fid
