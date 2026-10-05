-- Lean proof of fact 33aabc50b1cec1ba (RH2F.layer22); added by fact_submit, do not edit
import MhFact_30194dab4e05fdcf
set_option backward.isDefEq.respectTransparency false


/-
  TB1.lean — the triangle-with-digon piece as the true side of a 3-edge-cut `K` (the Setting of Lemma M6B-LIFT,
  fact ab4a4377238c0765, and of Lemma TRI-BRICK-EX, fact bd9a25a5df6fd97a): the ends `y_i` (apex), `y_j`, `y_k` of the
  cut edges on the true side, two further vertices `u`, `v`, and the edges `t12 = y_i y_j`, `t13 = y_i y_k`,
  `a = y_j u`, two parallel edges `d1`, `d2` joining `u` and `v`, `b = v y_k`. Derived: the edges at each vertex of
  the piece.
-/

namespace RH2F
open MGraph
open Classical

section cubicx
variable {X : MGraph} {P : Fin X.m → Prop}

/-- at a vertex of a cubic edge set, three distinct edges are all the edges -/
theorem cubic_exact (hcub : CubicOn P) {x : Fin X.n} {f1 f2 f3 : Fin X.m} (h1 : P f1) (h2 : P f2) (h3 : P f3)
    (i1 : X.Inc f1 x) (i2 : X.Inc f2 x) (i3 : X.Inc f3 x) (d12 : f1 ≠ f2) (d13 : f1 ≠ f3) (d23 : f2 ≠ f3) :
    ∀ g, P g → X.Inc g x → g = f1 ∨ g = f2 ∨ g = f3 := by
  obtain ⟨a, b, c, _, _, _, _, _, _, dab, dac, dbc, hall⟩ := hcub x ⟨f1, h1, i1⟩
  intro g hg hgx
  by_contra hne
  push_neg at hne
  obtain ⟨n1, n2, n3⟩ := hne
  have e1 := hall f1 h1 i1
  have e2 := hall f2 h2 i2
  have e3 := hall f3 h3 i3
  have eg := hall g hg hgx
  rcases eg with rfl | rfl | rfl <;> rcases e1 with rfl | rfl | rfl <;> rcases e2 with rfl | rfl | rfl <;>
    rcases e3 with rfl | rfl | rfl <;>
    first
      | exact d12 rfl | exact d13 rfl | exact d23 rfl | exact n1 rfl | exact n2 rfl | exact n3 rfl

/-- edges with different end pairs are different -/
theorem ne_of_joins {f g : Fin X.m} {x y x' y' : Fin X.n} (hf : X.Joins f x y) (hg : X.Joins g x' y')
    (h : ¬ ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) : f ≠ g := by
  rintro rfl; exact h (joins_unique hf hg)

end cubicx

section piece
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the triangle-with-digon piece as the true side of `K`, with apex `K.y i` -/
structure TriPiece (K : Cut3 P) (i j k : Fin 3) where
  hij : i ≠ j
  hik : i ≠ k
  hjk : j ≠ k
  u : Fin X.n
  v : Fin X.n
  t12 : Fin X.m
  t13 : Fin X.m
  a : Fin X.m
  d1 : Fin X.m
  d2 : Fin X.m
  b : Fin X.m
  p12 : P t12
  p13 : P t13
  pa : P a
  pd1 : P d1
  pd2 : P d2
  pb : P b
  j12 : X.Joins t12 (K.y i) (K.y j)
  j13 : X.Joins t13 (K.y i) (K.y k)
  ja : X.Joins a (K.y j) u
  jd1 : X.Joins d1 u v
  jd2 : X.Joins d2 u v
  jb : X.Joins b v (K.y k)
  dd : d1 ≠ d2
  su : K.S u = true
  sv : K.S v = true
  uy : ∀ t, u ≠ K.y t
  vy : ∀ t, v ≠ K.y t
  uv : u ≠ v
  side : ∀ x, K.S x = true → meets P x → x = K.y i ∨ x = K.y j ∨ x = K.y k ∨ x = u ∨ x = v

theorem Cut3.yne' (K : Cut3 P) {s t : Fin 3} (h : s ≠ t) : K.y s ≠ K.y t := fun e => h (K.yinj _ _ e)

theorem Cut3.wy' (K : Cut3 P) (s t : Fin 3) : K.w s ≠ K.y t := fun e => by
  have := K.sw s; rw [e, K.sy t] at this; exact absurd this (by decide)

namespace TriPiece
variable {K : Cut3 P} {i j k : Fin 3} (T : TriPiece K i j k)
include T

theorem yne {s t : Fin 3} (h : s ≠ t) : K.y s ≠ K.y t := K.yne' h
theorem wu (s : Fin 3) : K.w s ≠ T.u := fun e => by have := K.sw s; rw [e, T.su] at this; exact absurd this (by decide)
theorem wv (s : Fin 3) : K.w s ≠ T.v := fun e => by have := K.sw s; rw [e, T.sv] at this; exact absurd this (by decide)

/-! distinctness of the edges of the piece -/

theorem e_ne_inner {s : Fin 3} {f : Fin X.m} {x y : Fin X.n} (hf : X.Joins f x y) (hx : K.S x = true)
    (hy : K.S y = true) : K.e s ≠ f := by
  rintro rfl
  rcases joins_unique (K.hj s) hf with ⟨_, h⟩ | ⟨_, h⟩
  · have := K.sw s; rw [h, hy] at this; exact absurd this (by decide)
  · have := K.sw s; rw [h, hx] at this; exact absurd this (by decide)

theorem n12_13 : T.t12 ≠ T.t13 := ne_of_joins T.j12 T.j13 (by
  rintro (⟨_, h2⟩ | ⟨h1, _⟩)
  · exact T.yne T.hjk h2
  · exact T.yne T.hik h1)
theorem n12_a : T.t12 ≠ T.a := ne_of_joins T.j12 T.ja (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.yne T.hij h1
  · exact T.uy i h1.symm)
theorem n13_b : T.t13 ≠ T.b := ne_of_joins T.j13 T.jb (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.vy i h1.symm
  · exact T.yne T.hik h1)
theorem na_d1 : T.a ≠ T.d1 := ne_of_joins T.ja T.jd1 (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.uy j h1.symm
  · exact T.vy j h1.symm)
theorem na_d2 : T.a ≠ T.d2 := ne_of_joins T.ja T.jd2 (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.uy j h1.symm
  · exact T.vy j h1.symm)
theorem nb_d1 : T.b ≠ T.d1 := ne_of_joins T.jb T.jd1 (by
  rintro (⟨h1, _⟩ | ⟨_, h2⟩)
  · exact T.uv h1.symm
  · exact T.uy k h2.symm)
theorem nb_d2 : T.b ≠ T.d2 := ne_of_joins T.jb T.jd2 (by
  rintro (⟨h1, _⟩ | ⟨_, h2⟩)
  · exact T.uv h1.symm
  · exact T.uy k h2.symm)
theorem na_b : T.a ≠ T.b := ne_of_joins T.ja T.jb (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.vy j h1.symm
  · exact T.yne T.hjk h1)

theorem ei_12 : K.e i ≠ T.t12 := T.e_ne_inner T.j12 (K.sy i) (K.sy j)
theorem ei_13 : K.e i ≠ T.t13 := T.e_ne_inner T.j13 (K.sy i) (K.sy k)
theorem ej_12 : K.e j ≠ T.t12 := T.e_ne_inner T.j12 (K.sy i) (K.sy j)
theorem ej_a : K.e j ≠ T.a := T.e_ne_inner T.ja (K.sy j) T.su
theorem ek_13 : K.e k ≠ T.t13 := T.e_ne_inner T.j13 (K.sy i) (K.sy k)
theorem ek_b : K.e k ≠ T.b := T.e_ne_inner T.jb T.sv (K.sy k)

/-! the edges at the vertices of the piece -/

theorem at_yi (hG : InG X P) : ∀ f, P f → X.Inc f (K.y i) → f = K.e i ∨ f = T.t12 ∨ f = T.t13 :=
  cubic_exact hG.2.2.2 (K.hP i) T.p12 T.p13 (joins_inc_left (K.hj i)) (joins_inc_left T.j12)
    (joins_inc_left T.j13) T.ei_12 T.ei_13 T.n12_13
theorem at_yj (hG : InG X P) : ∀ f, P f → X.Inc f (K.y j) → f = K.e j ∨ f = T.t12 ∨ f = T.a :=
  cubic_exact hG.2.2.2 (K.hP j) T.p12 T.pa (joins_inc_left (K.hj j)) (joins_inc_right T.j12)
    (joins_inc_left T.ja) T.ej_12 T.ej_a T.n12_a
theorem at_yk (hG : InG X P) : ∀ f, P f → X.Inc f (K.y k) → f = K.e k ∨ f = T.t13 ∨ f = T.b :=
  cubic_exact hG.2.2.2 (K.hP k) T.p13 T.pb (joins_inc_left (K.hj k)) (joins_inc_right T.j13)
    (joins_inc_right T.jb) T.ek_13 T.ek_b T.n13_b
theorem at_u (hG : InG X P) : ∀ f, P f → X.Inc f T.u → f = T.a ∨ f = T.d1 ∨ f = T.d2 :=
  cubic_exact hG.2.2.2 T.pa T.pd1 T.pd2 (joins_inc_right T.ja) (joins_inc_left T.jd1) (joins_inc_left T.jd2)
    T.na_d1 T.na_d2 T.dd
theorem at_v (hG : InG X P) : ∀ f, P f → X.Inc f T.v → f = T.d1 ∨ f = T.d2 ∨ f = T.b :=
  cubic_exact hG.2.2.2 T.pd1 T.pd2 T.pb (joins_inc_right T.jd1) (joins_inc_right T.jd2) (joins_inc_left T.jb)
    T.dd T.nb_d1.symm T.nb_d2.symm

/-- the edges inside the piece -/
theorem inA_cases (hG : InG X P) {f : Fin X.m} (hf : K.inA f) :
    f = T.t12 ∨ f = T.t13 ∨ f = T.a ∨ f = T.d1 ∨ f = T.d2 ∨ f = T.b := by
  have hx := T.side _ hf.2.1 ⟨f, hf.1, Or.inl rfl⟩
  have hnc : ∀ s, f ≠ K.e s := fun s e => K.not_inA_of_cut ⟨s, e⟩ hf
  rcases hx with hx | hx | hx | hx | hx
  · rcases T.at_yi hG f hf.1 (Or.inl hx) with h | h | h
    · exact absurd h (hnc i)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases T.at_yj hG f hf.1 (Or.inl hx) with h | h | h
    · exact absurd h (hnc j)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases T.at_yk hG f hf.1 (Or.inl hx) with h | h | h
    · exact absurd h (hnc k)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases T.at_u hG f hf.1 (Or.inl hx) with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases T.at_v hG f hf.1 (Or.inl hx) with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem inA_t12 : K.inA T.t12 := ⟨T.p12, by rcases T.j12 with h | h <;> rw [h] <;> simp [K.sy]⟩
theorem inA_t13 : K.inA T.t13 := ⟨T.p13, by rcases T.j13 with h | h <;> rw [h] <;> simp [K.sy]⟩
theorem inA_a : K.inA T.a := ⟨T.pa, by rcases T.ja with h | h <;> rw [h] <;> simp [K.sy, T.su]⟩
theorem inA_d1 : K.inA T.d1 := ⟨T.pd1, by rcases T.jd1 with h | h <;> rw [h] <;> simp [T.su, T.sv]⟩
theorem inA_d2 : K.inA T.d2 := ⟨T.pd2, by rcases T.jd2 with h | h <;> rw [h] <;> simp [T.su, T.sv]⟩
theorem inA_b : K.inA T.b := ⟨T.pb, by rcases T.jb with h | h <;> rw [h] <;> simp [K.sy, T.sv]⟩

end TriPiece

end piece

end RH2F


/-
  TB2.lean — concrete data for Lemma TRI-BRICK-EX: the contraction `H6` of the far side (the piece plus a hub `z_P`,
  vertices `z_P, y1, y2, y3, u, v` = `0, …, 5`, edges `z_P y1, z_P y2, z_P y3, y1y2, y1y3, y2u, δ, δ′, vy3`), its four
  MC colourings of Step 3 of fact bd9a25a5df6fd97a, the piece with its three cut edges `H9` (vertices
  `y1, y2, y3, u, v, w1, w2, w3` = `0, …, 7`) and the two star colourings of Lemma M6B-LIFT (fact ab4a4377238c0765)
  in normalized colours, and the invariance of star colourings under an injective renaming of the colours.
-/

namespace RH2F
open MGraph
open Classical

/-- a star colouring stays a star colouring under an injective renaming of the colours -/
theorem starOn_comp_inj {G : MGraph} {Q : Fin G.m → Prop} {k : Nat} {c : Fin G.m → Fin k} (σ : Fin k → Fin k)
    (hσ : ∀ a b, σ a = σ b → a = b) (h : StarOn Q k c) : StarOn Q k (fun e => σ (c e)) := by
  refine ⟨fun a b hab ha hb e => h.1 a b hab ha hb (hσ _ _ e), fun w h1 h2 h3 h4 hb => h.2 w h1 h2 h3 h4 ?_⟩
  exact ⟨hσ _ _ hb.1, hσ _ _ hb.2⟩

/-- a colouring from a list -/
def colL (m : Nat) (l : List Nat) : Fin m → Fin 6 := fun e => ⟨l.getD e.val 0 % 6, Nat.mod_lt _ (by decide)⟩

/-- the Bool check that colour `5` is a perfect matching of the whole multigraph -/
def pmCheck (G : MGraph) (c : Fin G.m → Fin 6) : Bool :=
  (List.finRange G.n).all fun x => ((List.finRange G.m).filter fun e => decide (G.Inc e x) && c e == 5).length == 1

theorem mcol_of_check {G : MGraph} {c : Fin G.m → Fin 6} (hs : G.starCheck (fun _ => true) c = true)
    (hp : pmCheck G c = true) : MCol (fun _ : Fin G.m => True) c := by
  refine ⟨(star_iff 6 c).2 ((star_iff 6 c).1 (G.star_of_check c hs)), fun x _ => ?_⟩
  have hx := List.all_eq_true.1 hp x (mem_finRange' x)
  simp only [beq_iff_eq] at hx
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hx
  have ha' : a ∈ (List.finRange G.m).filter fun e => decide (G.Inc e x) && c e == 5 := by rw [ha]; simp
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha'
  refine ⟨a, trivial, ha'.2.1, ha'.2.2, fun b _ hbx hb5 => ?_⟩
  have hb : b ∈ (List.finRange G.m).filter fun e => decide (G.Inc e x) && c e == 5 := by
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨mem_finRange' b, hbx, hb5⟩
  rw [ha] at hb
  simpa using hb

/-! ### `H6`: the contraction of the far side -/

def h6L : List (Nat × Nat) := [(0,1), (0,2), (0,3), (1,2), (1,3), (2,4), (4,5), (4,5), (5,3)]
def H6 : MGraph := ofList 6 h6L (by decide)

theorem h6_m : H6.m = 9 := rfl
theorem h6_n : H6.n = 6 := rfl

/-- the colourings `c_{2,δ}`, `c_{2,δ′}`, `c_{3,δ}`, `c_{3,δ′}` of Step 3 (colour `6` of the prose is `5`, colour `k`
    of the prose is `k − 1`) -/
def c2d : List Nat := [0, 5, 2, 1, 5, 3, 5, 0, 4]
def c2d' : List Nat := [0, 5, 2, 1, 5, 3, 0, 5, 4]
def c3d : List Nat := [0, 2, 5, 5, 1, 4, 5, 0, 3]
def c3d' : List Nat := [0, 2, 5, 5, 1, 4, 0, 5, 3]

theorem h6_c2d : MCol (fun _ : Fin H6.m => True) (colL H6.m c2d) := mcol_of_check (by decide) (by decide)
theorem h6_c2d' : MCol (fun _ : Fin H6.m => True) (colL H6.m c2d') := mcol_of_check (by decide) (by decide)
theorem h6_c3d : MCol (fun _ : Fin H6.m => True) (colL H6.m c3d) := mcol_of_check (by decide) (by decide)
theorem h6_c3d' : MCol (fun _ : Fin H6.m => True) (colL H6.m c3d') := mcol_of_check (by decide) (by decide)

/-! ### `H9`: the piece with its three cut edges -/

/-- edges `e1 = y1w1, e2 = y2w2, e3 = y3w3, y1y2, y1y3, y2u, δ, δ′, vy3` -/
def h9L : List (Nat × Nat) := [(0,5), (1,6), (2,7), (0,1), (0,2), (1,3), (3,4), (3,4), (4,2)]
def H9 : MGraph := ofList 8 h9L (by decide)

/-- the colourings of Lemma M6B-LIFT in normalized colours `a2 = 0, a3 = 1, Π = {2, 3}, ζ = 4`: case (a)
    `c(y1y2) = a3, c(y1y3) = ζ`, case (b) `c(y1y2) = ζ, c(y1y3) = a2` -/
def c9a : List Nat := [5, 0, 1, 1, 4, 5, 2, 3, 5]
def c9b : List Nat := [5, 0, 1, 4, 0, 5, 2, 3, 5]

theorem h9_ca : Star 6 (colL H9.m c9a) := H9.star_of_check _ (by decide)
theorem h9_cb : Star 6 (colL H9.m c9b) := H9.star_of_check _ (by decide)

end RH2F


/-
  TB3.lean — transporting colourings of the concrete graphs `H6`, `H9` along explicit injective lists of vertices and
  edges: the MC colourings of `X_P = K.flip.cont` (the contraction of the far side of the piece) and the star colourings
  of the piece with its cut edges (`K.pole`).
-/

namespace RH2F
open MGraph
open Classical

section listemb
variable {Y H : MGraph}

/-- the index of `x` in the list `vs` (or `d`) -/
noncomputable def idxOf {α : Type} {n : Nat} (vs : Fin n → α) (d : Fin n) (x : α) : Fin n :=
  if h : ∃ s, vs s = x then Classical.choose h else d

theorem idxOf_eq {α : Type} {n : Nat} {vs : Fin n → α} (hvs : ∀ s t, vs s = vs t → s = t) (d : Fin n) (s : Fin n) :
    idxOf vs d (vs s) = s := by
  unfold idxOf
  have h : ∃ s', vs s' = vs s := ⟨s, rfl⟩
  rw [dif_pos h]
  exact hvs _ _ (Classical.choose_spec h)

/-- **MC colourings along a list embedding** -/
theorem mcol_of_listEmb {Q : Fin Y.m → Prop} (hn : 0 < H.n) (hm : 0 < H.m) (vs : Fin H.n → Fin Y.n)
    (es : Fin H.m → Fin Y.m) (hvs : ∀ s t, vs s = vs t → s = t) (hes : ∀ s t, es s = es t → s = t)
    (hQ : ∀ e, Q e ↔ ∃ t, e = es t) (hj : ∀ t, Y.Joins (es t) (vs (H.ends t).1) (vs (H.ends t).2))
    {c : Fin H.m → Fin 6} (hc : MCol (fun _ => True) c) :
    ∃ c' : Fin Y.m → Fin 6, MCol Q c' ∧ ∀ t, c' (es t) = c t := by
  let ρ : Fin Y.n → Fin H.n := idxOf vs ⟨0, hn⟩
  let μ : Fin Y.m → Fin H.m := idxOf es ⟨0, hm⟩
  have hρv : ∀ s, ρ (vs s) = s := idxOf_eq hvs _
  have hμe : ∀ t, μ (es t) = t := idxOf_eq hes _
  have hmv : ∀ x, meets Q x → ∃ s, x = vs s := by
    rintro x ⟨e, he, hex⟩
    obtain ⟨t, rfl⟩ := (hQ e).1 he
    rcases inc_of_joins (hj t) hex with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  refine ⟨fun e => c (μ e), mcol_emb ρ μ ?_ ?_ (fun _ _ => trivial) ?_ ?_ hc, fun t => by simp only [hμe]⟩
  · intro x y hx hy h
    obtain ⟨s, rfl⟩ := hmv x hx
    obtain ⟨s', rfl⟩ := hmv y hy
    rw [hρv, hρv] at h; rw [h]
  · intro a b ha hb h
    obtain ⟨t, rfl⟩ := (hQ a).1 ha
    obtain ⟨t', rfl⟩ := (hQ b).1 hb
    rw [hμe, hμe] at h; rw [h]
  · intro a ha
    obtain ⟨t, rfl⟩ := (hQ a).1 ha
    rw [hμe]
    rcases hj t with h | h <;> rw [h]
    · simp only [hρv]; exact Or.inl rfl
    · simp only [hρv]; exact Or.inr rfl
  · intro x _ b _ _
    exact ⟨es b, (hQ _).2 ⟨b, rfl⟩, hμe b⟩

/-- **star colourings along a list embedding** -/
theorem starOn_of_listEmb {Q : Fin Y.m → Prop} {k : Nat} (hn : 0 < H.n) (hm : 0 < H.m) (vs : Fin H.n → Fin Y.n)
    (es : Fin H.m → Fin Y.m) (hvs : ∀ s t, vs s = vs t → s = t) (hes : ∀ s t, es s = es t → s = t)
    (hQ : ∀ e, Q e → ∃ t, e = es t) (hj : ∀ t, Y.Joins (es t) (vs (H.ends t).1) (vs (H.ends t).2))
    {c : Fin H.m → Fin k} (hc : Star k c) :
    ∃ c' : Fin Y.m → Fin k, StarOn Q k c' ∧ ∀ t, c' (es t) = c t := by
  let ρ : Fin Y.n → Fin H.n := idxOf vs ⟨0, hn⟩
  let μ : Fin Y.m → Fin H.m := idxOf es ⟨0, hm⟩
  have hρv : ∀ s, ρ (vs s) = s := idxOf_eq hvs _
  have hμe : ∀ t, μ (es t) = t := idxOf_eq hes _
  refine ⟨fun e => c (μ e), starOn_embed ρ μ ?_ ?_ (fun _ _ => trivial) ?_ hc, fun t => by simp only [hμe]⟩
  · intro x y a b ha hb hax hby h
    obtain ⟨t, rfl⟩ := hQ a ha
    obtain ⟨t', rfl⟩ := hQ b hb
    have ex : ∃ s, x = vs s := by
      rcases inc_of_joins (hj t) hax with e | e
      · exact ⟨_, e⟩
      · exact ⟨_, e⟩
    have ey : ∃ s, y = vs s := by
      rcases inc_of_joins (hj t') hby with e | e
      · exact ⟨_, e⟩
      · exact ⟨_, e⟩
    obtain ⟨s, rfl⟩ := ex
    obtain ⟨s', rfl⟩ := ey
    rw [hρv, hρv] at h; rw [h]
  · intro a b ha hb h
    obtain ⟨t, rfl⟩ := hQ a ha
    obtain ⟨t', rfl⟩ := hQ b hb
    rw [hμe, hμe] at h; rw [h]
  · intro a ha
    obtain ⟨t, rfl⟩ := hQ a ha
    rw [hμe]
    rcases hj t with h | h <;> rw [h]
    · simp only [hρv]; exact Or.inl rfl
    · simp only [hρv]; exact Or.inr rfl

end listemb

end RH2F


/-
  TB4.lean — the embeddings of `H6` into the contraction `X_P = K.flip.cont` of the far side and of `H9` into the
  piece with its cut edges, for a triangle-with-digon piece `T` on the true side of `K`.
-/

namespace RH2F
open MGraph
open Classical

theorem fin3_cases : ∀ i j k t : Fin 3, i ≠ j → i ≠ k → j ≠ k → t = i ∨ t = j ∨ t = k := by decide

section emb
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)
include T

theorem n12_d1 : T.t12 ≠ T.d1 := ne_of_joins T.j12 T.jd1 (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.uy i h1.symm
  · exact T.vy i h1.symm)
theorem n12_d2 : T.t12 ≠ T.d2 := ne_of_joins T.j12 T.jd2 (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.uy i h1.symm
  · exact T.vy i h1.symm)
theorem n12_b : T.t12 ≠ T.b := ne_of_joins T.j12 T.jb (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.vy i h1.symm
  · exact T.yne T.hik h1)
theorem n13_a : T.t13 ≠ T.a := ne_of_joins T.j13 T.ja (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.yne T.hij h1
  · exact T.uy i h1.symm)
theorem n13_d1 : T.t13 ≠ T.d1 := ne_of_joins T.j13 T.jd1 (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.uy i h1.symm
  · exact T.vy i h1.symm)
theorem n13_d2 : T.t13 ≠ T.d2 := ne_of_joins T.j13 T.jd2 (by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact T.uy i h1.symm
  · exact T.vy i h1.symm)

/-! ### `H6` into `X_P` -/

/-- the vertices `z_P, y_i, y_j, y_k, u, v` of `X_P` -/
def vs6 : Fin H6.n → Fin (addHub X K.flip.w).n :=
  ![hub K.flip.w, hv K.flip.w (K.y i), hv K.flip.w (K.y j), hv K.flip.w (K.y k), hv K.flip.w T.u, hv K.flip.w T.v]

/-- the edges `z_P y_i, z_P y_j, z_P y_k, t12, t13, a, d1, d2, b` of `X_P` -/
def es6 : Fin H6.m → Fin (addHub X K.flip.w).m :=
  ![hNew K.flip.w i, hNew K.flip.w j, hNew K.flip.w k, hOld K.flip.w T.t12, hOld K.flip.w T.t13,
    hOld K.flip.w T.a, hOld K.flip.w T.d1, hOld K.flip.w T.d2, hOld K.flip.w T.b]

theorem vs6_inj : ∀ s t, T.vs6 s = T.vs6 t → s = t := by
  have y1 := T.yne T.hij; have y2 := T.yne T.hik; have y3 := T.yne T.hjk
  have u1 := T.uy i; have u2 := T.uy j; have u3 := T.uy k
  have v1 := T.vy i; have v2 := T.vy j; have v3 := T.vy k
  have uv := T.uv
  have hh : ∀ a : Fin X.n, hub K.flip.w ≠ hv K.flip.w a := fun a h => hv_ne_hub _ a h.symm
  have hi : ∀ a b : Fin X.n, hv K.flip.w a = hv K.flip.w b ↔ a = b := fun a b => ⟨hv_inj _, fun h => by rw [h]⟩
  intro s t h
  have hinj : Function.Injective T.vs6 := by
    apply List.nodup_ofFn.1
    simp [vs6, List.ofFn_succ, hh, hi, y1, y2, y3, Ne.symm u1, Ne.symm u2, Ne.symm u3, Ne.symm v1, Ne.symm v2,
      Ne.symm v3, uv]
  exact hinj h

theorem es6_inj : ∀ s t, T.es6 s = T.es6 t → s = t := by
  have hno : ∀ (t : Fin 3) (d : Fin X.m), hNew K.flip.w t ≠ hOld K.flip.w d := fun t d h => hOld_ne_hNew _ d t h.symm
  have hoi : ∀ a b : Fin X.m, hOld K.flip.w a = hOld K.flip.w b ↔ a = b := fun a b => ⟨hOld_inj _, fun h => by rw [h]⟩
  have hni : ∀ a b : Fin 3, hNew K.flip.w a = hNew K.flip.w b ↔ a = b := fun a b => ⟨hNew_inj _, fun h => by rw [h]⟩
  intro s t h
  have hinj : Function.Injective T.es6 := by
    apply List.nodup_ofFn.1
    simp [es6, List.ofFn_succ, hno, hoi, hni, T.hij, T.hik, T.hjk, T.n12_13, T.n12_a, T.n12_d1, T.n12_d2, T.n12_b,
      T.n13_a, T.n13_d1, T.n13_d2, T.n13_b, T.na_d1, T.na_d2, T.na_b, T.dd, Ne.symm T.nb_d1, Ne.symm T.nb_d2]
  exact hinj h

theorem cont6_iff (hG : InG X P) : ∀ e, K.flip.cont e ↔ ∃ t, e = T.es6 t := by
  intro e
  constructor
  · rintro (⟨d, rfl, hd⟩ | ⟨t, rfl⟩)
    · have hd' : K.inA d := (Cut3.flip_flip_inA K).1 hd
      rcases T.inA_cases hG hd' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨3, by decide⟩, rfl⟩
      · exact ⟨⟨4, by decide⟩, rfl⟩
      · exact ⟨⟨5, by decide⟩, rfl⟩
      · exact ⟨⟨6, by decide⟩, rfl⟩
      · exact ⟨⟨7, by decide⟩, rfl⟩
      · exact ⟨⟨8, by decide⟩, rfl⟩
    · rcases fin3_cases i j k t T.hij T.hik T.hjk with rfl | rfl | rfl
      · exact ⟨⟨0, by decide⟩, rfl⟩
      · exact ⟨⟨1, by decide⟩, rfl⟩
      · exact ⟨⟨2, by decide⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    have o : ∀ d, K.inA d → K.flip.cont (hOld K.flip.w d) := fun d hd =>
      Or.inl ⟨d, rfl, (Cut3.flip_flip_inA K).2 hd⟩
    fin_cases t
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact o _ T.inA_t12
    · exact o _ T.inA_t13
    · exact o _ T.inA_a
    · exact o _ T.inA_d1
    · exact o _ T.inA_d2
    · exact o _ T.inA_b

theorem joins6 : ∀ t, (addHub X K.flip.w).Joins (T.es6 t) (T.vs6 (H6.ends t).1) (T.vs6 (H6.ends t).2) := by
  have hn : ∀ s : Fin 3, (addHub X K.flip.w).Joins (hNew K.flip.w s) (hub K.flip.w) (hv K.flip.w (K.y s)) :=
    fun s => Or.inl (hub_ends_new K.flip.w s)
  intro t
  fin_cases t
  · exact hn i
  · exact hn j
  · exact hn k
  · exact hub_joins_old _ T.j12
  · exact hub_joins_old _ T.j13
  · exact hub_joins_old _ T.ja
  · exact hub_joins_old _ T.jd1
  · exact hub_joins_old _ T.jd2
  · exact hub_joins_old _ T.jb

/-- **the MC colourings of `X_P`** from those of `H6` -/
theorem mcol6 (hG : InG X P) {c : Fin H6.m → Fin 6} (hc : MCol (fun _ => True) c) :
    ∃ c' : Fin (addHub X K.flip.w).m → Fin 6, MCol K.flip.cont c' ∧ ∀ t, c' (T.es6 t) = c t :=
  mcol_of_listEmb (by decide) (by decide) T.vs6 T.es6 T.vs6_inj T.es6_inj (T.cont6_iff hG) T.joins6 hc

/-! ### `H9` into the piece with its cut edges -/

/-- the vertices `y_i, y_j, y_k, u, v, w_i, w_j, w_k` -/
def vs9 : Fin H9.n → Fin X.n := ![K.y i, K.y j, K.y k, T.u, T.v, K.w i, K.w j, K.w k]

/-- the edges `e_i, e_j, e_k, t12, t13, a, d1, d2, b` -/
def es9 : Fin H9.m → Fin X.m := ![K.e i, K.e j, K.e k, T.t12, T.t13, T.a, T.d1, T.d2, T.b]

theorem vs9_inj : ∀ s t, T.vs9 s = T.vs9 t → s = t := by
  have y1 := T.yne T.hij; have y2 := T.yne T.hik; have y3 := T.yne T.hjk
  have u1 := T.uy i; have u2 := T.uy j; have u3 := T.uy k
  have v1 := T.vy i; have v2 := T.vy j; have v3 := T.vy k
  have uv := T.uv
  have wy : ∀ s t, K.y t ≠ K.w s := fun s t h => K.wy' s t h.symm
  have wu : ∀ s, T.u ≠ K.w s := fun s h => T.wu s h.symm
  have wv : ∀ s, T.v ≠ K.w s := fun s h => T.wv s h.symm
  have ww : ∀ s t, K.w s = K.w t ↔ s = t := fun s t => ⟨K.winj s t, fun h => by rw [h]⟩
  intro s t h
  have hinj : Function.Injective T.vs9 := by
    apply List.nodup_ofFn.1
    simp [vs9, List.ofFn_succ, y1, y2, y3, Ne.symm u1, Ne.symm u2, Ne.symm u3, Ne.symm v1, Ne.symm v2, Ne.symm v3,
      uv, wy, wu, wv, ww, T.hij, T.hik, T.hjk]
  exact hinj h

theorem es9_inj : ∀ s t, T.es9 s = T.es9 t → s = t := by
  have c12 : ∀ s, K.e s ≠ T.t12 := fun s => T.e_ne_inner T.j12 (K.sy i) (K.sy j)
  have c13 : ∀ s, K.e s ≠ T.t13 := fun s => T.e_ne_inner T.j13 (K.sy i) (K.sy k)
  have ca : ∀ s, K.e s ≠ T.a := fun s => T.e_ne_inner T.ja (K.sy j) T.su
  have cd1 : ∀ s, K.e s ≠ T.d1 := fun s => T.e_ne_inner T.jd1 T.su T.sv
  have cd2 : ∀ s, K.e s ≠ T.d2 := fun s => T.e_ne_inner T.jd2 T.su T.sv
  have cb : ∀ s, K.e s ≠ T.b := fun s => T.e_ne_inner T.jb T.sv (K.sy k)
  have ee : ∀ s t, K.e s = K.e t ↔ s = t := fun s t => ⟨K.einj s t, fun h => by rw [h]⟩
  intro s t h
  have hinj : Function.Injective T.es9 := by
    apply List.nodup_ofFn.1
    simp [es9, List.ofFn_succ, c12, c13, ca, cd1, cd2, cb, ee, T.hij, T.hik, T.hjk, T.n12_13, T.n12_a, T.n12_d1,
      T.n12_d2, T.n12_b, T.n13_a, T.n13_d1, T.n13_d2, T.n13_b, T.na_d1, T.na_d2, T.na_b, T.dd, Ne.symm T.nb_d1,
      Ne.symm T.nb_d2]
  exact hinj h

theorem pole9 (hG : InG X P) : ∀ e, K.pole e → ∃ t, e = T.es9 t := by
  rintro e (he | ⟨t, rfl⟩)
  · rcases T.inA_cases hG he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl⟩
    · exact ⟨⟨5, by decide⟩, rfl⟩
    · exact ⟨⟨6, by decide⟩, rfl⟩
    · exact ⟨⟨7, by decide⟩, rfl⟩
    · exact ⟨⟨8, by decide⟩, rfl⟩
  · rcases fin3_cases i j k t T.hij T.hik T.hjk with rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl⟩

theorem joins9 : ∀ t, X.Joins (T.es9 t) (T.vs9 (H9.ends t).1) (T.vs9 (H9.ends t).2) := by
  intro t
  fin_cases t
  · exact K.hj i
  · exact K.hj j
  · exact K.hj k
  · exact T.j12
  · exact T.j13
  · exact T.ja
  · exact T.jd1
  · exact T.jd2
  · exact T.jb

/-- **star colourings of the piece with its cut edges** from those of `H9` -/
theorem star9 (hG : InG X P) {c : Fin H9.m → Fin 6} (hc : Star 6 c) :
    ∃ φ : Fin X.m → Fin 6, StarOn K.pole 6 φ ∧ ∀ t, φ (T.es9 t) = c t :=
  starOn_of_listEmb (by decide) (by decide) T.vs9 T.es9 T.vs9_inj T.es9_inj (T.pole9 hG) T.joins9 hc

end TriPiece

end emb

end RH2F


/-
  TB5.lean — **Lemma M6B-LIFT** (fact ab4a4377238c0765) as an instance of the MC gluing across the cut of the piece
  (`mc_glue'`, 3CUT-MULTI (MC-M)). An MC colouring `c` of `X′ = K.cont` with `c(z w_i) = 6` lifts to an MC colouring
  of `X` equal to `c` outside the piece, with `e_i`, `a = y_j u`, `b = v y_k` in colour class `6`, unless the pattern
  `t_j = t_k = ζ` occurs (`Pat K i c`, the pattern excluded in (T1′)).
-/

namespace RH2F
open MGraph
open Classical

/-- the pattern `t_j = t_k = ζ` of (T1′) (the negated clause of `T1p`, fact 345a55d7429fd4b1) -/
def Pat {X : MGraph} {R : Fin X.m → Prop} (C : Cut3 R) (i : Fin 3) (c : Fin (addHub X C.w).m → Fin 6) : Prop :=
  ∃ (j k : Fin 3) (h2 h3 : Fin (addHub X C.w).m), j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
    C.cont h2 ∧ (addHub X C.w).Inc h2 (hv C.w (C.w j)) ∧ h2 ≠ hNew C.w j ∧ c h2 ≠ 5 ∧
    C.cont h3 ∧ (addHub X C.w).Inc h3 (hv C.w (C.w k)) ∧ h3 ≠ hNew C.w k ∧ c h3 ≠ 5 ∧
    c h2 = c h3 ∧ c h2 ≠ c (hNew C.w j) ∧ c h2 ≠ c (hNew C.w k) ∧
    ∀ h1, C.cont h1 → (addHub X C.w).Inc h1 (hv C.w (C.w i)) → h1 ≠ hNew C.w i → c h1 ≠ c h2

/-- the fifth colour -/
theorem fifth_colour : ∀ a b c d : Fin 6, a ≠ 5 → b ≠ 5 → c ≠ 5 → d ≠ 5 → a ≠ b → a ≠ c → a ≠ d → b ≠ c →
    b ≠ d → c ≠ d → ∃ z : Fin 6, z ≠ 5 ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d := by decide

/-- a 2-set containing `5` -/
theorem two_with5 {S : Fin 6 → Prop} (h : Two S) (h5 : S 5) : ∃ t, t ≠ 5 ∧ ∀ κ, S κ ↔ κ = 5 ∨ κ = t := by
  obtain ⟨α, β, hab, hS⟩ := h
  rcases (hS 5).1 h5 with h | h
  · refine ⟨β, fun e => hab (h.symm.trans e.symm), fun κ => ?_⟩
    rw [hS κ, ← h]
  · refine ⟨α, fun e => hab (e.trans h), fun κ => ?_⟩
    rw [hS κ, ← h]; exact Or.comm

section lift
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)
include T

/-- **the general lift**: a star colouring `φ` of the piece with its cut edges with the colours
    `e_i ↦ 6, e_j ↦ a_j, e_k ↦ a_k, t12 ↦ α, t13 ↦ β, a ↦ 6, d1 ↦ π1, d2 ↦ π2, b ↦ 6` glues with `c` under the
    stated conditions on `α`, `β` -/
theorem lift_gen (hG : InG X P) (c : Fin (addHub X K.w).m → Fin 6) (hc : MCol K.cont c)
    (hci : c (hNew K.w i) = 5) {π1 π2 tj tk α β : Fin 6}
    (hOi : ∀ κ, K.datO c i κ ↔ κ = π1 ∨ κ = π2) (hOj : ∀ κ, K.datO c j κ ↔ κ = 5 ∨ κ = tj)
    (hOk : ∀ κ, K.datO c k κ ↔ κ = 5 ∨ κ = tk)
    (hπ1j : π1 ≠ c (hNew K.w j)) (hπ2j : π2 ≠ c (hNew K.w j)) (hπ1k : π1 ≠ c (hNew K.w k))
    (hπ2k : π2 ≠ c (hNew K.w k)) (hj5 : c (hNew K.w j) ≠ 5)
    (hα5 : α ≠ 5) (hβ5 : β ≠ 5) (hαπ : α ≠ π1 ∧ α ≠ π2) (hβπ : β ≠ π1 ∧ β ≠ π2)
    (condJ : α = tj → α = c (hNew K.w k) ∧ β ≠ c (hNew K.w j))
    (condK : β = tk → β = c (hNew K.w j) ∧ α ≠ c (hNew K.w k))
    (φ : Fin X.m → Fin 6) (hφ : StarOn K.pole 6 φ)
    (vi : φ (K.e i) = 5) (vj : φ (K.e j) = c (hNew K.w j)) (vk : φ (K.e k) = c (hNew K.w k))
    (v12 : φ T.t12 = α) (v13 : φ T.t13 = β) (va : φ T.a = 5) (vd1 : φ T.d1 = π1) (vd2 : φ T.d2 = π2)
    (vb : φ T.b = 5) :
    ∃ c', MCol P c' ∧ (∀ f, K.flip.pole f → c' f = c (K.toCont f)) ∧ c' (K.e i) = 5 ∧ c' T.a = 5 ∧ c' T.b = 5 := by
  have hnb : ∀ t κ, κ = 5 ∨ κ = c (hNew K.w j) ∨ κ = c (hNew K.w k) → ¬ K.datB c t κ := by
    intro t κ hκ
    rcases hκ with rfl | rfl | rfl
    · rw [← hci]; exact K.cont_noBlk hG.1 c hc.1 t i
    · exact K.cont_noBlk hG.1 c hc.1 t j
    · exact K.cont_noBlk hG.1 c hc.1 t k
  -- the inner edges at the three ends
  have colI : ∀ κ, K.Col φ i κ → κ = α ∨ κ = β := by
    rintro κ ⟨f, hf, hfy, rfl⟩
    rcases T.at_yi hG f hf.1 hfy with rfl | rfl | rfl
    · exact absurd hf (K.not_inA_of_cut ⟨i, rfl⟩)
    · exact Or.inl v12
    · exact Or.inr v13
  have colJ : ∀ f, K.inA f → X.Inc f (K.y j) → f = T.t12 ∨ f = T.a := by
    intro f hf hfy
    rcases T.at_yj hG f hf.1 hfy with rfl | h | h
    · exact absurd hf (K.not_inA_of_cut ⟨j, rfl⟩)
    · exact Or.inl h
    · exact Or.inr h
  have colK : ∀ f, K.inA f → X.Inc f (K.y k) → f = T.t13 ∨ f = T.b := by
    intro f hf hfy
    rcases T.at_yk hG f hf.1 hfy with rfl | h | h
    · exact absurd hf (K.not_inA_of_cut ⟨k, rfl⟩)
    · exact Or.inl h
    · exact Or.inr h
  -- pole edges at `y_i`, `u`, `v`
  have atI : ∀ f, K.pole f → X.Inc f (K.y i) → f = K.e i ∨ f = T.t12 ∨ f = T.t13 :=
    fun f hf hfx => T.at_yi hG f (K.pole_P hf) hfx
  have atU : ∀ f, K.pole f → X.Inc f T.u → f = T.a ∨ f = T.d1 ∨ f = T.d2 :=
    fun f hf hfx => T.at_u hG f (K.pole_P hf) hfx
  have atV : ∀ f, K.pole f → X.Inc f T.v → f = T.d1 ∨ f = T.d2 ∨ f = T.b :=
    fun f hf hfx => T.at_v hG f (K.pole_P hf) hfx
  have hcomp : ∀ t κ, K.Col φ t κ → K.datO c t κ → (K.Blk φ t κ ∨ K.datB c t κ) → False := by
    intro t κ hcol hO hB
    rcases fin3_cases i j k t T.hij T.hik T.hjk with ht | ht | ht <;> rw [ht] at hcol hO hB
    · -- port `i`: `{α, β}` and `Π` are disjoint
      rcases colI κ hcol with rfl | rfl <;> rcases (hOi _).1 hO with h | h
      · exact hαπ.1 h
      · exact hαπ.2 h
      · exact hβπ.1 h
      · exact hβπ.2 h
    · -- port `j`
      obtain ⟨f, hf, hfy, rfl⟩ := hcol
      rcases colJ f hf hfy with rfl | rfl
      · -- `f = t12`, colour `α`
        rw [v12] at hO hB
        rcases (hOj _).1 hO with h | h
        · exact hα5 h
        · obtain ⟨hαk, hβj⟩ := condJ h
          rcases hB with ⟨f0, r, hf0, hj0, hc0, f', hf', hf'f, hf'r, hc'⟩ | hB
          · rcases colJ f0 hf0 (joins_inc_left hj0) with rfl | rfl
            · -- `r = y_i`
              have hr : r = K.y i := by
                rcases joins_unique hj0 T.j12 with ⟨h, _⟩ | ⟨_, h⟩
                · exact absurd h.symm (T.yne T.hij)
                · exact h
              subst hr
              rw [vj] at hc'
              rcases atI f' hf' hf'r with rfl | rfl | rfl
              · rw [vi] at hc'; exact hj5 hc'.symm
              · exact hf'f rfl
              · rw [v13] at hc'; exact hβj hc'
            · rw [va] at hc0; exact hα5 hc0.symm
          · exact hnb j α (Or.inr (Or.inr hαk)) hB
      · -- `f = a`, colour `6`
        rw [va] at hO hB
        rcases hB with ⟨f0, r, hf0, hj0, hc0, f', hf', hf'f, hf'r, hc'⟩ | hB
        · rcases colJ f0 hf0 (joins_inc_left hj0) with rfl | rfl
          · rw [v12] at hc0; exact hα5 hc0
          · have hr : r = T.u := by
              rcases joins_unique hj0 T.ja with ⟨_, h⟩ | ⟨h, _⟩
              · exact h
              · exact absurd h (T.uy j).symm
            subst hr
            rw [vj] at hc'
            rcases atU f' hf' hf'r with rfl | rfl | rfl
            · exact hf'f rfl
            · rw [vd1] at hc'; exact hπ1j hc'
            · rw [vd2] at hc'; exact hπ2j hc'
        · exact hnb j 5 (Or.inl rfl) hB
    · -- port `k`
      obtain ⟨f, hf, hfy, rfl⟩ := hcol
      rcases colK f hf hfy with rfl | rfl
      · -- `f = t13`, colour `β`
        rw [v13] at hO hB
        rcases (hOk _).1 hO with h | h
        · exact hβ5 h
        · obtain ⟨hβj, hαk⟩ := condK h
          rcases hB with ⟨f0, r, hf0, hj0, hc0, f', hf', hf'f, hf'r, hc'⟩ | hB
          · rcases colK f0 hf0 (joins_inc_left hj0) with rfl | rfl
            · have hr : r = K.y i := by
                rcases joins_unique hj0 T.j13 with ⟨h, _⟩ | ⟨_, h⟩
                · exact absurd h.symm (T.yne T.hik)
                · exact h
              subst hr
              rw [vk] at hc'
              rcases atI f' hf' hf'r with rfl | rfl | rfl
              · rw [vi] at hc'
                exact (T.hjk (by
                  have hk5 : c (hNew K.w k) = 5 := hc'.symm
                  exact absurd hk5 (fun e => by
                    obtain ⟨ha, _⟩ := K.dat_admissible hG.1
                      (fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩) c hc hci
                    exact T.hik (ha _ _ (hci.trans e.symm))))).elim
              · rw [v12] at hc'; exact hαk hc'
              · exact hf'f rfl
            · rw [vb] at hc0; exact hβ5 hc0.symm
          · exact hnb k β (Or.inr (Or.inl hβj)) hB
      · -- `f = b`, colour `6`
        rw [vb] at hO hB
        rcases hB with ⟨f0, r, hf0, hj0, hc0, f', hf', hf'f, hf'r, hc'⟩ | hB
        · rcases colK f0 hf0 (joins_inc_left hj0) with rfl | rfl
          · rw [v13] at hc0; exact hβ5 hc0
          · have hr : r = T.v := by
              rcases joins_unique hj0 T.jb with ⟨h, _⟩ | ⟨_, h⟩
              · exact absurd h.symm (T.vy k)
              · exact h
            subst hr
            rw [vk] at hc'
            rcases atV f' hf' hf'r with rfl | rfl | rfl
            · rw [vd1] at hc'; exact hπ1k hc'
            · rw [vd2] at hc'; exact hπ2k hc'
            · exact hf'f rfl
        · exact hnb k 5 (Or.inl rfl) hB
  have hφA : ∀ x, K.S x = true → meets P x →
      ∃ a', K.pole a' ∧ X.Inc a' x ∧ φ a' = 5 ∧ ∀ b', K.pole b' → X.Inc b' x → φ b' = 5 → b' = a' := by
    intro x hx hxm
    rcases T.side x hx hxm with rfl | rfl | rfl | rfl | rfl
    · refine ⟨K.e i, Or.inr ⟨i, rfl⟩, joins_inc_left (K.hj i), vi, fun b' hb' hbx hb5 => ?_⟩
      rcases atI b' hb' hbx with rfl | rfl | rfl
      · rfl
      · rw [v12] at hb5; exact absurd hb5 hα5
      · rw [v13] at hb5; exact absurd hb5 hβ5
    · refine ⟨T.a, Or.inl T.inA_a, joins_inc_left T.ja, va, fun b' hb' hbx hb5 => ?_⟩
      rcases T.at_yj hG b' (K.pole_P hb') hbx with rfl | rfl | rfl
      · rw [vj] at hb5; exact absurd hb5 hj5
      · rw [v12] at hb5; exact absurd hb5 hα5
      · rfl
    · refine ⟨T.b, Or.inl T.inA_b, joins_inc_right T.jb, vb, fun b' hb' hbx hb5 => ?_⟩
      rcases T.at_yk hG b' (K.pole_P hb') hbx with rfl | rfl | rfl
      · rw [vk] at hb5
        obtain ⟨ha, _⟩ := K.dat_admissible hG.1
          (fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩) c hc hci
        exact absurd (ha _ _ (hb5.trans hci.symm)) (Ne.symm T.hik)
      · rw [v13] at hb5; exact absurd hb5 hβ5
      · rfl
    · refine ⟨T.a, Or.inl T.inA_a, joins_inc_right T.ja, va, fun b' hb' hbx hb5 => ?_⟩
      rcases atU b' hb' hbx with rfl | rfl | rfl
      · rfl
      · rw [vd1] at hb5
        exact absurd hb5 (fun e => (hOi π1).2 (Or.inl rfl) |> fun h => by
          obtain ⟨_, _, _, _, hO1, _⟩ := K.dat_admissible hG.1
            (fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩) c hc hci
          exact (hO1 π1 h).1 e)
      · rw [vd2] at hb5
        exact absurd hb5 (fun e => (hOi π2).2 (Or.inr rfl) |> fun h => by
          obtain ⟨_, _, _, _, hO1, _⟩ := K.dat_admissible hG.1
            (fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩) c hc hci
          exact (hO1 π2 h).1 e)
    · refine ⟨T.b, Or.inl T.inA_b, joins_inc_left T.jb, vb, fun b' hb' hbx hb5 => ?_⟩
      rcases atV b' hb' hbx with rfl | rfl | rfl
      · rw [vd1] at hb5
        exact absurd hb5 (fun e => (hOi π1).2 (Or.inl rfl) |> fun h => by
          obtain ⟨_, _, _, _, hO1, _⟩ := K.dat_admissible hG.1
            (fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩) c hc hci
          exact (hO1 π1 h).1 e)
      · rw [vd2] at hb5
        exact absurd hb5 (fun e => (hOi π2).2 (Or.inr rfl) |> fun h => by
          obtain ⟨_, _, _, _, hO1, _⟩ := K.dat_admissible hG.1
            (fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩) c hc hci
          exact (hO1 π2 h).1 e)
      · rfl
  have hφe : ∀ t, φ (K.e t) = K.datA c t := by
    intro t
    rcases fin3_cases i j k t T.hij T.hik T.hjk with ht | ht | ht <;> rw [ht]
    · rw [vi]; exact hci.symm
    · exact vj
    · exact vk
  obtain ⟨c', hc', hcφ, hcψ⟩ := K.mc_glue' c hc φ hφ hφA hφe hcomp
  refine ⟨c', hc', hcψ, ?_, ?_, ?_⟩
  · rw [hcφ _ (Or.inr ⟨i, rfl⟩)]; exact vi
  · rw [hcφ _ (Or.inl T.inA_a)]; exact va
  · rw [hcφ _ (Or.inl T.inA_b)]; exact vb

end TriPiece

end lift

end RH2F


/-
  TB6.lean — **Lemma M6B-LIFT** (fact ab4a4377238c0765) in the form used by TRI-BRICK-EX.
-/

namespace RH2F
open MGraph
open Classical

section m6b
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)
include T

/-- **M6B-LIFT**: an MC colouring `c` of `X′ = K.cont` with `c(z w_i) = 6` and without the pattern `t_j = t_k = ζ`
    lifts to an MC colouring of `X` that agrees with `c` outside the piece and has `e_i`, `a`, `b` in colour class
    `6` -/
theorem m6b_lift (hG : InG X P) (c : Fin (addHub X K.w).m → Fin 6) (hc : MCol K.cont c)
    (hci : c (hNew K.w i) = 5) (hpat : ¬ Pat K i c) :
    ∃ c', MCol P c' ∧ (∀ f, K.flip.pole f → c' f = c (K.toCont f)) ∧ c' (K.e i) = 5 ∧ c' T.a = 5 ∧ c' T.b = 5 := by
  have hw : ∀ t, CubicAt P (K.w t) := fun t => hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩
  obtain ⟨ha_inj, _, hTwo, _, hO1, _, hO2, _⟩ := K.dat_admissible hG.1 hw c hc hci
  obtain ⟨π1, π2, hπ, hOi⟩ := hTwo i
  have hπ1 := hO1 π1 ((hOi π1).2 (Or.inl rfl))
  have hπ2 := hO1 π2 ((hOi π2).2 (Or.inr rfl))
  obtain ⟨tj, htj5, hOj⟩ := two_with5 (hTwo j) (hO2 j (Ne.symm T.hij)).1
  obtain ⟨tk, htk5, hOk⟩ := two_with5 (hTwo k) (hO2 k (Ne.symm T.hik)).1
  have haj5 : c (hNew K.w j) ≠ 5 := fun h => T.hij (ha_inj _ _ (hci.trans h.symm))
  have hak5 : c (hNew K.w k) ≠ 5 := fun h => T.hik (ha_inj _ _ (hci.trans h.symm))
  have hajk : c (hNew K.w j) ≠ c (hNew K.w k) := fun h => T.hjk (ha_inj _ _ h)
  have hπ1j : π1 ≠ c (hNew K.w j) := hπ1.2 j (Ne.symm T.hij)
  have hπ2j : π2 ≠ c (hNew K.w j) := hπ2.2 j (Ne.symm T.hij)
  have hπ1k : π1 ≠ c (hNew K.w k) := hπ1.2 k (Ne.symm T.hik)
  have hπ2k : π2 ≠ c (hNew K.w k) := hπ2.2 k (Ne.symm T.hik)
  obtain ⟨ζ, hz5, hzj, hzk, hz1, hz2⟩ := fifth_colour (c (hNew K.w j)) (c (hNew K.w k)) π1 π2 haj5 hak5 hπ1.1
    hπ2.1 hajk (Ne.symm hπ1j) (Ne.symm hπ2j) (Ne.symm hπ1k) (Ne.symm hπ2k) hπ
  -- the renaming of the normalized colours `0, 1, 2, 3, 4, 5` to `a_j, a_k, π1, π2, ζ, 6`
  let σ : Fin 6 → Fin 6 := ![c (hNew K.w j), c (hNew K.w k), π1, π2, ζ, 5]
  have hσ : ∀ a b, σ a = σ b → a = b := by
    have hinj : Function.Injective σ := by
      apply List.nodup_ofFn.1
      simp [σ, List.ofFn_succ, hajk, Ne.symm hπ1j, Ne.symm hπ2j, Ne.symm hπ1k, Ne.symm hπ2k, hπ, haj5, hak5,
        hπ1.1, hπ2.1, Ne.symm hzj, Ne.symm hzk, Ne.symm hz1, Ne.symm hz2, hz5]
    exact fun a b h => hinj h
  by_cases hka : tk = ζ
  · by_cases hjb : tj = ζ
    · -- the pattern `t_j = t_k = ζ`
      exfalso
      apply hpat
      obtain ⟨f2, hf2, hf2y, hc2⟩ := (hOj tj).2 (Or.inr rfl)
      obtain ⟨f3, hf3, hf3y, hc3⟩ := (hOk tk).2 (Or.inr rfl)
      replace hc2 : c (hOld K.w f2) = tj := by rw [← K.toCont_flip_inA hf2]; exact hc2
      replace hc3 : c (hOld K.w f3) = tk := by rw [← K.toCont_flip_inA hf3]; exact hc3
      refine ⟨j, k, hOld K.w f2, hOld K.w f3, Ne.symm T.hij, Ne.symm T.hik, T.hjk, Or.inl ⟨f2, rfl, hf2⟩,
        (hub_inc_old K.w).2 hf2y, hOld_ne_hNew _ _ _, by rw [hc2]; exact htj5, Or.inl ⟨f3, rfl, hf3⟩,
        (hub_inc_old K.w).2 hf3y, hOld_ne_hNew _ _ _, by rw [hc3]; exact htk5, by rw [hc2, hc3, hjb, hka],
        by rw [hc2, hjb]; exact hzj, by rw [hc2, hjb]; exact hzk, fun h1 h1c h1i h1n => ?_⟩
      obtain ⟨f, hfp, hfx, rfl⟩ := K.cont_at h1c h1i
      rcases hfp with hf | ⟨t, rfl⟩
      · rw [hc2, hjb]
        have hm : K.datO c i (c (K.toCont f)) := ⟨f, hf, hfx, rfl⟩
        rcases (hOi _).1 hm with h | h <;> rw [h]
        · exact Ne.symm hz1
        · exact Ne.symm hz2
      · have := K.cut_at_w hfx
        subst this
        exact absurd (K.toCont_e t) h1n
    · -- case (b): `t_j ≠ ζ`
      obtain ⟨φ, hφ, hφv⟩ := T.star9 hG (starOn_comp_inj σ hσ h9_cb)
      exact T.lift_gen hG c hc hci hOi hOj hOk hπ1j hπ2j hπ1k hπ2k haj5 (α := ζ) (β := c (hNew K.w j)) hz5 haj5
        ⟨hz1, hz2⟩ ⟨Ne.symm hπ1j, Ne.symm hπ2j⟩ (fun h => absurd h.symm hjb) (fun _ => ⟨rfl, hzk⟩) φ hφ
        (by have h := hφv ⟨0, by decide⟩; exact h) (by have h := hφv ⟨1, by decide⟩; exact h) (by have h := hφv ⟨2, by decide⟩; exact h) (by have h := hφv ⟨3, by decide⟩; exact h)
        (by have h := hφv ⟨4, by decide⟩; exact h) (by have h := hφv ⟨5, by decide⟩; exact h) (by have h := hφv ⟨6, by decide⟩; exact h) (by have h := hφv ⟨7, by decide⟩; exact h) (by have h := hφv ⟨8, by decide⟩; exact h)
  · -- case (a): `t_k ≠ ζ`
    obtain ⟨φ, hφ, hφv⟩ := T.star9 hG (starOn_comp_inj σ hσ h9_ca)
    exact T.lift_gen hG c hc hci hOi hOj hOk hπ1j hπ2j hπ1k hπ2k haj5 (α := c (hNew K.w k)) (β := ζ) hak5 hz5
      ⟨Ne.symm hπ1k, Ne.symm hπ2k⟩ ⟨hz1, hz2⟩ (fun _ => ⟨rfl, hzj⟩) (fun h => absurd h.symm hka) φ hφ
      (by have h := hφv ⟨0, by decide⟩; exact h) (by have h := hφv ⟨1, by decide⟩; exact h) (by have h := hφv ⟨2, by decide⟩; exact h) (by have h := hφv ⟨3, by decide⟩; exact h)
      (by have h := hφv ⟨4, by decide⟩; exact h) (by have h := hφv ⟨5, by decide⟩; exact h) (by have h := hφv ⟨6, by decide⟩; exact h) (by have h := hφv ⟨7, by decide⟩; exact h) (by have h := hφv ⟨8, by decide⟩; exact h)

end TriPiece

end m6b

end RH2F


/-
  TB7.lean — **Lemma TRI-BRICK-EX** (fact bd9a25a5df6fd97a) for a triangle-with-digon piece `T` on the true side of a
  3-edge-cut `K` with distinct ends of a member of 𝒢: if the pole `Q(X′, z)` of `X′ = K.cont` at its hub is dominant
  (`Dominant K.flip.hubPorts`) and (T1′) holds for `(X′, z, w_i)` (`T1p K i`), then `P` is EX1-good.
-/

namespace RH2F
open MGraph
open Classical

/-! ### the admissible datum of Step 5 (colours `6, 1, 2` of the prose are `5, 0, 1`) -/

def s5A (i j : Fin 3) : Fin 3 → Fin 6 := fun t => if t = i then 5 else if t = j then 0 else 1
def s5O (i j : Fin 3) : Fin 3 → Fin 6 → Prop :=
  fun t κ => if t = i then (κ = 2 ∨ κ = 3) else if t = j then (κ = 5 ∨ κ = 2) else (κ = 5 ∨ κ = 3)
def s5B (i j : Fin 3) : Fin 3 → Fin 6 → Prop :=
  fun t κ => if t = i then (κ = 2 ∨ κ = 3) else if t = j then κ = 2 else κ = 3

section s5
variable {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hij hik hjk

theorem s5A_i : s5A i j i = 5 := by simp [s5A]
theorem s5A_j : s5A i j j = 0 := by simp [s5A, Ne.symm hij]
theorem s5A_k : s5A i j k = 1 := by simp [s5A, Ne.symm hik, Ne.symm hjk]
theorem s5O_i (κ : Fin 6) : s5O i j i κ ↔ κ = 2 ∨ κ = 3 := by simp [s5O]
theorem s5O_j (κ : Fin 6) : s5O i j j κ ↔ κ = 5 ∨ κ = 2 := by simp [s5O, Ne.symm hij]
theorem s5O_k (κ : Fin 6) : s5O i j k κ ↔ κ = 5 ∨ κ = 3 := by simp [s5O, Ne.symm hik, Ne.symm hjk]
theorem s5B_i (κ : Fin 6) : s5B i j i κ ↔ κ = 2 ∨ κ = 3 := by simp [s5B]
theorem s5B_j (κ : Fin 6) : s5B i j j κ ↔ κ = 2 := by simp [s5B, Ne.symm hij]
theorem s5B_k (κ : Fin 6) : s5B i j k κ ↔ κ = 3 := by simp [s5B, Ne.symm hik, Ne.symm hjk]

/-- the datum of Step 5 is admissible at M-port `i` -/
theorem step5_adm : Admissible i (s5A i j) (s5O i j) (s5B i j) := by
  have cs := fun t => fin3_cases i j k t hij hik hjk
  have A := fun t => (show s5A i j t = if t = i then 5 else if t = j then 0 else 1 from rfl)
  refine ⟨fun s t h => ?_, s5A_i hij hik hjk, fun t => ?_, fun t κ hB => ?_, fun κ hO => ?_, fun κ => ?_,
    fun t ht => ?_, fun j' k' hj' hk' hjk' => ?_⟩
  · rcases cs s with rfl | rfl | rfl <;> rcases cs t with rfl | rfl | rfl <;>
      simp only [s5A_i hij hik hjk, s5A_j hij hik hjk, s5A_k hij hik hjk] at h <;>
      first | rfl | exact absurd h (by decide)
  · rcases cs t with rfl | rfl | rfl
    · exact ⟨2, 3, by decide, s5O_i hij hik hjk⟩
    · exact ⟨5, 2, by decide, s5O_j hij hik hjk⟩
    · exact ⟨5, 3, by decide, s5O_k hij hik hjk⟩
  · rcases cs t with rfl | rfl | rfl
    · exact (s5O_i hij hik hjk κ).2 ((s5B_i hij hik hjk κ).1 hB)
    · exact (s5O_j hij hik hjk κ).2 (Or.inr ((s5B_j hij hik hjk κ).1 hB))
    · exact (s5O_k hij hik hjk κ).2 (Or.inr ((s5B_k hij hik hjk κ).1 hB))
  · have h := (s5O_i hij hik hjk κ).1 hO
    refine ⟨by rcases h with rfl | rfl <;> decide, fun t ht => ?_⟩
    rcases cs t with rfl | rfl | rfl
    · exact absurd rfl ht
    · rw [s5A_j hij hik hjk]; rcases h with rfl | rfl <;> decide
    · rw [s5A_k hij hik hjk]; rcases h with rfl | rfl <;> decide
  · rw [s5B_i hij hik hjk, s5O_i hij hik hjk]
  · rcases cs t with rfl | rfl | rfl
    · exact absurd rfl ht
    · refine ⟨(s5O_j hij hik hjk 5).2 (Or.inl rfl), ?_, fun κ hB => ?_⟩
      · rw [s5O_j hij hik hjk, s5A_j hij hik hjk]; decide
      · rw [(s5B_j hij hik hjk κ).1 hB]
        refine ⟨by decide, fun s hs => ?_⟩
        rcases cs s with rfl | rfl | rfl
        · exact absurd rfl hs
        · rw [s5A_j hij hik hjk]; decide
        · rw [s5A_k hij hik hjk]; decide
    · refine ⟨(s5O_k hij hik hjk 5).2 (Or.inl rfl), ?_, fun κ hB => ?_⟩
      · rw [s5O_k hij hik hjk, s5A_k hij hik hjk]; decide
      · rw [(s5B_k hij hik hjk κ).1 hB]
        refine ⟨by decide, fun s hs => ?_⟩
        rcases cs s with rfl | rfl | rfl
        · exact absurd rfl hs
        · rw [s5A_j hij hik hjk]; decide
        · rw [s5A_k hij hik hjk]; decide
  · rintro ⟨h1, h2⟩
    rcases cs j' with rfl | rfl | rfl <;> rcases cs k' with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hj' | exact absurd rfl hk' | exact absurd rfl hjk'
      | (rw [s5A_k hij hik hjk, s5O_j hij hik hjk] at h1; revert h1; decide)
      | (rw [s5A_j hij hik hjk, s5O_k hij hik hjk] at h1; revert h1; decide)

end s5

section tbex
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)
include T

theorem inner_notCut {f : Fin X.m} (hf : K.inA f) : ¬ K.isCut f := fun h => K.not_inA_of_cut h hf

theorem toCont_es9 : ∀ t, K.flip.toCont (T.es9 t) = T.es6 t := by
  have o : ∀ f, K.inA f → K.flip.toCont f = hOld K.flip.w f := fun f hf => K.flip.toCont_old (T.inner_notCut hf)
  intro t
  fin_cases t
  · exact K.flip.toCont_e i
  · exact K.flip.toCont_e j
  · exact K.flip.toCont_e k
  · exact o _ T.inA_t12
  · exact o _ T.inA_t13
  · exact o _ T.inA_a
  · exact o _ T.inA_d1
  · exact o _ T.inA_d2
  · exact o _ T.inA_b

/-- Step 4 with Case 1.1 / 2.1: an MC colouring of `X_P` with its colour-`6` port at `s` and (D1)/(D2)-data glue -/
theorem glue_XP (hG : InG X P) (hdom : Dominant K.flip.hubPorts) (cl : List Nat)
    (hmc : MCol (fun _ : Fin H6.m => True) (colL H6.m cl)) {s : Fin 3} {ts : Fin H6.m}
    (hts : T.es6 ts = hNew K.flip.w s) (h5 : colL H6.m cl ts = 5) :
    ∃ c, MCol K.flip.cont c ∧ c (hNew K.flip.w s) = 5 ∧ ∀ t, c (T.es6 t) = colL H6.m cl t := by
  obtain ⟨c, hc, hcv⟩ := T.mcol6 hG hmc
  exact ⟨c, hc, by rw [← hts, hcv, h5], hcv⟩

/-- **Step 6**: a compatible MC pole colouring at the apex port gives a perfect matching of `X′` through `z w_i` -/
theorem step6 (hG : InG X P) {d : Fin (addHub X K.flip.flip.w).m → Fin 6} (hd : MCPole K.flip.hubPorts d)
    {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop} (hcomp : Compat K.flip.hubPorts d a O B)
    (hai : a i = 5) (hainj : ∀ s t, a s = a t → s = t) :
    ∃ N, PMOn K.cont N ∧ N (hNew K.w i) ∧ ∀ g, K.flip.inA g → (N (K.toCont g) ↔ d (K.toCont g) = 5) := by
  obtain ⟨_, hA, he, _⟩ := K.flip.pole_of_D1 hd hcomp
  let ψ : Fin X.m → Fin 6 := fun f => d (K.toCont f)
  have hψe : ∀ t, ψ (K.e t) = a t := he
  let N : Fin (addHub X K.w).m → Prop := fun e => K.cont e ∧ ∃ f, K.flip.pole f ∧ e = K.toCont f ∧ ψ f = 5
  refine ⟨N, ⟨fun e he => he.1, fun x hx => ?_⟩, ⟨Or.inr ⟨i, rfl⟩, K.e i, Or.inr ⟨i, rfl⟩, (K.toCont_e i).symm,
    by rw [hψe]; exact hai⟩, fun g hg => ⟨fun ⟨_, f, _, hfe, hf5⟩ => by rw [K.toCont_inj hfe]; exact hf5,
      fun h5 => ⟨K.toCont_mem (Or.inl hg), g, Or.inl hg, rfl, h5⟩⟩⟩
  obtain ⟨e0, he0, hx0⟩ := hx
  rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl
  · -- an old vertex, on side `B` of `K`
    have hxv : (Fin.castSucc y : Fin (addHub X K.w).n) = hv K.w y := rfl
    have hmy := (K.meets_cont_hv y).1 ⟨e0, he0, hx0⟩
    have hsy : K.flip.S y = true := by rw [Cut3.flip_S, hmy.2]; rfl
    obtain ⟨a', ha', hay, ha5, hau⟩ := hA y hsy hmy.1
    have hinc : ∀ f, K.flip.pole f → X.Inc f y → (addHub X K.w).Inc (K.toCont f) (hv K.w y) := by
      intro f hf hfy
      have hj := K.toCont_joins hf
      rw [← K.toV_B hmy.2]
      rcases hfy with h | h <;> rw [← h]
      · exact joins_inc_left hj
      · exact joins_inc_right hj
    refine ⟨K.toCont a', ⟨K.toCont_mem ha', a', ha', rfl, ha5⟩, hinc a' ha' hay, fun e he hex => ?_⟩
    obtain ⟨_, f, hf, rfl, hf5⟩ := he
    have hfy : X.Inc f y := by
      rcases Cut3.inc_of_joins' (K.toCont_joins hf) hex with h | h
      · have := K.toV_eq_hv h.symm; rw [← this.1]; exact Or.inl rfl
      · have := K.toV_eq_hv h.symm; rw [← this.1]; exact Or.inr rfl
    rw [hau f hf hfy hf5]
  · -- the hub
    refine ⟨hNew K.w i, ⟨Or.inr ⟨i, rfl⟩, K.e i, Or.inr ⟨i, rfl⟩, (K.toCont_e i).symm, by rw [hψe]; exact hai⟩,
      hub_inc_new_hub K.w i, fun e he hex => ?_⟩
    obtain ⟨_, f, hf, rfl, hf5⟩ := he
    rcases hf with hf | ⟨t, rfl⟩
    · rw [K.toCont_flip_inA hf] at hex; exact absurd hex (hub_not_inc_old _)
    · have hf5' : a t = 5 := (hψe t).symm.trans hf5
      have ht : t = i := hainj t i (hf5'.trans hai.symm)
      subst ht
      exact K.toCont_e _

/-- **Lemma TRI-BRICK-EX** -/
theorem tri_brick_ex (hG : InG X P) (hdom : Dominant K.flip.hubPorts) (hT1 : T1p K i) : EX1On P := by
  have hw : ∀ t, CubicAt P (K.flip.w t) := fun t =>
    hG.2.2.2 (K.flip.w t) ⟨K.e t, K.hP t, joins_inc_left (K.hj t)⟩
  have hwK : ∀ t, CubicAt P (K.w t) := fun t =>
    hG.2.2.2 (K.w t) ⟨K.e t, K.hP t, joins_inc_right (K.hj t)⟩
  -- the lift through (T1′) and M6B-LIFT
  have viaT1 : ∀ g0, K.cont g0 → ¬ (addHub X K.w).Inc g0 (hub K.w) → ∀ t : Bool,
      (∃ N, PMOn K.cont N ∧ N (hNew K.w i) ∧ (N g0 ↔ t = true)) →
      ∃ c1 : Fin (addHub X K.w).m → Fin 6, (c1 g0 = 5 ↔ t = true) ∧ ∃ c'', MCol P c'' ∧
        (∀ f, K.flip.pole f → c'' f = c1 (K.toCont f)) ∧ c'' (K.e i) = 5 ∧ c'' T.a = 5 ∧ c'' T.b = 5 := by
    intro g0 hg0 hgv t hN
    obtain ⟨c1, hc1, hci, hst, hpat⟩ := hT1 g0 hg0 hgv t hN
    exact ⟨c1, hst, T.m6b_lift hG c1 hc1 hci hpat⟩
  -- Case 1.2: the pairs forcing the matching `B`
  have bad : ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 := by
    obtain ⟨N0, hN0, hN0i⟩ := RH2P.pstat _ K.cont (K.cont_inG hG) (hNew K.w i) (Or.inr ⟨i, rfl⟩) true
    obtain ⟨f0, _, _, hf0, _, hf0w, _, _⟩ := K.pairB (hwK i)
    have hg0 : K.cont (hOld K.w f0) := Or.inl ⟨f0, rfl, hf0⟩
    obtain ⟨_, _, c'', hc'', _, h1, h2, h3⟩ := viaT1 (hOld K.w f0) hg0 (hub_not_inc_old _) (decide (N0 (hOld K.w f0)))
      ⟨N0, hN0, hN0i.2 rfl, by simp⟩
    exact ⟨c'', hc'', h1, h2, h3⟩
  -- gluing an MC colouring of `X_P` from the list `cl` at its colour-`6` port `s` with (D1)
  have key : ∀ (cl : List Nat), MCol (fun _ : Fin H6.m => True) (colL H6.m cl) → ∀ (s : Fin 3) (ts : Fin H6.m),
      T.es6 ts = hNew K.flip.w s → colL H6.m cl ts = 5 → ∀ (idx : Fin H6.m) (t : Bool),
      (colL H6.m cl idx = 5 ↔ t = true) → ∃ c, MCol P c ∧ (c (T.es9 idx) = 5 ↔ t = true) := by
    intro cl hmc s ts hts h5 idx t hst
    obtain ⟨c, hc, hcs, hcv⟩ := T.glue_XP hG hdom cl hmc hts h5
    obtain ⟨d, hd, hcomp⟩ := hdom.1 s _ _ _ (K.flip.dat_admissible hG.1 hw c hc hcs)
    obtain ⟨c'', hc'', _, hψ⟩ := K.flip.glue_track c hc hd hcomp
    have hp : K.flip.flip.pole (T.es9 idx) := by
      rw [Cut3.flip_flip_pole]
      fin_cases idx
      · exact Or.inr ⟨i, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
      · exact Or.inr ⟨k, rfl⟩
      · exact Or.inl T.inA_t12
      · exact Or.inl T.inA_t13
      · exact Or.inl T.inA_a
      · exact Or.inl T.inA_d1
      · exact Or.inl T.inA_d2
      · exact Or.inl T.inA_b
    refine ⟨c'', hc'', ?_⟩
    rw [hψ (T.es9 idx) hp, T.toCont_es9, hcv]
    exact hst
  have k2d := key c2d h6_c2d j ⟨1, by decide⟩ rfl rfl
  have k2d' := key c2d' h6_c2d' j ⟨1, by decide⟩ rfl rfl
  have k3d := key c3d h6_c3d k ⟨2, by decide⟩ rfl rfl
  apply ex1_of_mcol
  intro g hg t
  rcases K.flip.cases_P hg with hU | hPc | hcut
  · -- Case 2: `g` inside the far side, (D2)
    have hgc : K.flip.flip.cont (K.flip.flip.toCont g) := by
      rw [K.flip.flipToCont_inA hU]
      exact Or.inl ⟨g, rfl, by simp only [Cut3.flip_flip_inA]; exact hU⟩
    have hgv : ¬ (addHub X K.flip.flip.w).Inc (K.flip.flip.toCont g) (hub K.flip.flip.w) := by
      rw [K.flip.flipToCont_inA hU]; exact hub_not_inc_old _
    obtain ⟨s, hs⟩ := hdom.2 _ hgc hgv t
    rcases fin3_cases i j k s T.hij T.hik T.hjk with hsi | hsj | hsk
    · -- port `i`: the datum of Step 5, the matching of Step 6, then (T1′) and M6B-LIFT
      rw [hsi] at hs
      obtain ⟨d, hd, hcomp, hst⟩ := hs _ _ _ (step5_adm T.hij T.hik T.hjk)
      obtain ⟨N, hN, hNi, hNg⟩ := T.step6 hG hd hcomp (s5A_i T.hij T.hik T.hjk)
        (step5_adm T.hij T.hik T.hjk).1
      have hg0 : K.cont (K.toCont g) := K.toCont_mem (Or.inl hU)
      have hgv0 : ¬ (addHub X K.w).Inc (K.toCont g) (hub K.w) := by
        rw [K.toCont_flip_inA hU]; exact hub_not_inc_old _
      obtain ⟨c1, hst1, c'', hc'', hcψ, _, _, _⟩ := viaT1 _ hg0 hgv0 t ⟨N, hN, hNi, (hNg g hU).trans hst⟩
      exact ⟨c'', hc'', by rw [hcψ g (Or.inl hU)]; exact hst1⟩
    · rw [hsj] at hs
      obtain ⟨c, hc, hcj, _⟩ := T.glue_XP hG hdom c2d h6_c2d (s := j) (ts := ⟨1, by decide⟩) rfl rfl
      obtain ⟨d, hd, hcomp, hst⟩ := hs _ _ _ (K.flip.dat_admissible hG.1 hw c hc hcj)
      obtain ⟨c'', hc'', hφ, _⟩ := K.flip.glue_track c hc hd hcomp
      exact ⟨c'', hc'', by rw [hφ g (Or.inl hU)]; exact hst⟩
    · rw [hsk] at hs
      obtain ⟨c, hc, hck, _⟩ := T.glue_XP hG hdom c3d h6_c3d (s := k) (ts := ⟨2, by decide⟩) rfl rfl
      obtain ⟨d, hd, hcomp, hst⟩ := hs _ _ _ (K.flip.dat_admissible hG.1 hw c hc hck)
      obtain ⟨c'', hc'', hφ, _⟩ := K.flip.glue_track c hc hd hcomp
      exact ⟨c'', hc'', by rw [hφ g (Or.inl hU)]; exact hst⟩
  all_goals
    -- Case 1: `g` in the piece or a cut edge
    have hgp : K.pole g := by
      first
        | exact Or.inl ((Cut3.flip_flip_inA K).1 ‹_›)
        | exact Or.inr ‹K.flip.isCut g›
    obtain ⟨idx, rfl⟩ := T.pole9 hG g hgp
    fin_cases idx <;> cases t
    all_goals
      first
        | exact k2d _ _ (by decide)
        | exact k2d' _ _ (by decide)
        | exact k3d _ _ (by decide)
        | (obtain ⟨c, hc, h1, h2, h3⟩ := bad
           first
             | exact ⟨c, hc, fun _ => rfl, fun _ => h1⟩
             | exact ⟨c, hc, fun _ => rfl, fun _ => h2⟩
             | exact ⟨c, hc, fun _ => rfl, fun _ => h3⟩)

end TriPiece

end tbex

end RH2F


/-
  TB8.lean — the named hypothesis TRIBRICKEX of fact 30194dab4e05fdcf (layer 21) is a theorem: the Q-level
  triangle side with one inner digon gives a `TriPiece` on the true side of `Cut3.dig C`, and Lemma TRI-BRICK-EX
  applies.
-/

namespace RH2F
open MGraph
open Classical

/-- the contraction of the doubly flipped cut is the contraction of the cut -/
theorem cont_flip_flip {X : MGraph} {P : Fin X.m → Prop} (K : Cut3 P) : K.flip.flip.cont = K.cont := by
  funext e
  apply propext
  constructor
  · rintro (⟨d, h, hd⟩ | h)
    · exact Or.inl ⟨d, h, (Cut3.flip_flip_inA K.flip).1 hd⟩
    · exact Or.inr h
  · rintro (⟨d, h, hd⟩ | h)
    · exact Or.inl ⟨d, h, (Cut3.flip_flip_inA K.flip).2 hd⟩
    · exact Or.inr h

theorem dominant_cast {Y : MGraph} {Q Q' : Fin Y.m → Prop} {v : Fin Y.n} (h : Q = Q') (E : Ports Q v)
    (hd : Dominant (h ▸ E)) : Dominant E := by
  subst h; exact hd

section inst
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

/-- **TRIBRICKEX** (the named hypothesis of fact 30194dab4e05fdcf) holds -/
theorem tribrickex_holds : TRIBRICKEX := by
  intro Y Q hQ C h3 D i δ hQδ hDδ hδ1 hδ2 hδi huniq hdomAll hT1
  obtain ⟨hGd, _, _⟩ := dig_class hQ.1 hQ.2.2 D
  have hloop : Loopless Y := hQ.1.1
  -- the side `S` consists of the three ends `C.y t`
  have hmem : ∀ x, meets Q x → C.S x = true → ∃ a, x = C.y a := by
    intro x hx hsx
    exact C.flip.sideB3 (by rw [Cut3.scount_flip3]; exact h3) hx (by simp [Cut3.flip_S, hsx])
  obtain ⟨j, hj⟩ := hmem _ (ends_meets1 hQδ) hδ1
  obtain ⟨k, hk⟩ := hmem _ (ends_meets2 hQδ) hδ2
  have hij : i ≠ j := by rintro rfl; exact hδi (Or.inl hj)
  have hik : i ≠ k := by rintro rfl; exact hδi (Or.inr hk)
  have hjk : j ≠ k := by rintro rfl; exact hloop δ (by rw [hj, hk])
  -- no cut edge carries a digon
  have hcutD : ∀ t, ¬ D (C.e t) := by
    intro t hD
    have hQe := C.hP t
    have hin : C.S (Y.ends (C.e t)).1 = true ∨ C.S (Y.ends (C.e t)).2 = true := by
      rcases C.hj t with h | h <;> rw [h] <;> simp [C.sy t]
    have := huniq _ hQe hD hin
    rw [← this] at hδ1 hδ2
    rcases C.hj t with h | h <;> rw [h] at hδ1 hδ2
    · rw [C.sw t] at hδ2; exact absurd hδ2 (by decide)
    · rw [C.sw t] at hδ1; exact absurd hδ1 (by decide)
  set K := Cut3.dig (D := D) C with hK
  have hKy : ∀ t, K.y t = dO (C.y t) := by
    intro t
    show cutY (D := D) C.S (C.e t) (C.y t) = dO (C.y t)
    unfold cutY; rw [if_neg (hcutD t)]
  -- the triangle edges at `y_i`
  have hS3 : ∀ x, meets Q x → C.S x = true → x = C.y i ∨ x = C.y j ∨ x = C.y k := by
    intro x hx hsx
    obtain ⟨a, rfl⟩ := hmem x hx hsx
    rcases fin3_cases i j k a hij hik hjk with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨p, q, r, hp, hq, hr, ip, iq, ir, dpq, dpr, dqr, hall⟩ :=
    hQ.1.2.2.2 (C.y i) ⟨C.e i, C.hP i, joins_inc_left (C.hj i)⟩
  -- the two edges at `y_i` other than `e_i`
  have inner : ∀ f, Q f → Y.Inc f (C.y i) → f ≠ C.e i →
      (Y.Joins f (C.y i) (C.y j) ∨ Y.Joins f (C.y i) (C.y k)) := by
    intro f hf hfi hne
    have hnc : ¬ C.isCut f := by
      rintro ⟨t, rfl⟩
      exact hne (by rw [C.cut_at_y hfi])
    have hin := C.inA_of_notcut hf hnc hfi (C.sy i)
    have hother : ∀ z, Y.Joins f (C.y i) z → z = C.y j ∨ z = C.y k := by
      intro z hz
      have hzS : C.S z = true := by
        rcases hz with h | h
        · have := hin.2.2; rw [h] at this; exact this
        · have := hin.2.1; rw [h] at this; exact this
      rcases hS3 z ⟨f, hf, joins_inc_right hz⟩ hzS with h | h | h
      · exact absurd (h ▸ hz) (fun hz' => by
          rcases hz' with h' | h' <;> exact hloop f (by rw [h']))
      · exact Or.inl h
      · exact Or.inr h
    rcases hfi with h | h
    · rcases hother (Y.ends f).2 (Or.inl (by rw [← h])) with e | e
      · exact Or.inl (Or.inl (by rw [← h, ← e]))
      · exact Or.inr (Or.inl (by rw [← h, ← e]))
    · rcases hother (Y.ends f).1 (Or.inr (by rw [← h])) with e | e
      · exact Or.inl (Or.inr (by rw [← h, ← e]))
      · exact Or.inr (Or.inr (by rw [← h, ← e]))
  -- two distinct edges at `y_i` other than `e_i`
  obtain ⟨f1, f2, hf1, hf2, if1, if2, n1, n2, n12⟩ : ∃ f1 f2, Q f1 ∧ Q f2 ∧ Y.Inc f1 (C.y i) ∧ Y.Inc f2 (C.y i) ∧
      f1 ≠ C.e i ∧ f2 ≠ C.e i ∧ f1 ≠ f2 := by
    rcases hall (C.e i) (C.hP i) (joins_inc_left (C.hj i)) with h | h | h
    · exact ⟨q, r, hq, hr, iq, ir, fun e => dpq (e.trans h).symm, fun e => dpr (e.trans h).symm, dqr⟩
    · exact ⟨p, r, hp, hr, ip, ir, fun e => dpq (e.trans h), fun e => dqr (e.trans h).symm, dpr⟩
    · exact ⟨p, q, hp, hq, ip, iq, fun e => dpr (e.trans h), fun e => dqr (e.trans h), dpq⟩
  obtain ⟨t12, t13, h12, h13, j12, j13⟩ : ∃ t12 t13, Q t12 ∧ Q t13 ∧ Y.Joins t12 (C.y i) (C.y j) ∧
      Y.Joins t13 (C.y i) (C.y k) := by
    rcases inner f1 hf1 if1 n1 with a1 | a1 <;> rcases inner f2 hf2 if2 n2 with a2 | a2
    · exact absurd (hQ.2.1 f1 f2 _ _ hf1 hf2 a1 a2) n12
    · exact ⟨f1, f2, hf1, hf2, a1, a2⟩
    · exact ⟨f2, f1, hf2, hf1, a2, a1⟩
    · exact absurd (hQ.2.1 f1 f2 _ _ hf1 hf2 a1 a2) n12
  -- they carry no digon
  have hn12 : t12 ≠ δ := ne_of_joins j12 (Or.inl (Prod.ext hj hk : Y.ends δ = (C.y j, C.y k))) (by
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hij (C.yinj _ _ h)
    · exact hik (C.yinj _ _ h))
  have hn13 : t13 ≠ δ := ne_of_joins j13 (Or.inl (Prod.ext hj hk : Y.ends δ = (C.y j, C.y k))) (by
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hij (C.yinj _ _ h)
    · exact hik (C.yinj _ _ h))
  have hD12 : ¬ D t12 := fun hD => hn12 (huniq _ h12 hD (by rcases j12 with h | h <;> rw [h] <;> simp [C.sy i]))
  have hD13 : ¬ D t13 := fun hD => hn13 (huniq _ h13 hD (by rcases j13 with h | h <;> rw [h] <;> simp [C.sy i]))
  -- the piece
  have joinsO : ∀ {f : Fin Y.m} {x y : Fin Y.n}, ¬ D f → Y.Joins f x y →
      (digG Y D).Joins (eO f) (dO x) (dO y) := by
    intro f x y hD hjf
    rcases hjf with h | h
    · exact Or.inl (by rw [ends_eO_nD hD, h])
    · exact Or.inr (by rw [ends_eO_nD hD, h])
  have hsu : K.S (dU δ) = true := by
    show indS (D := D) C.S (dU δ) = true
    rw [indS_dU, hδ1]; rfl
  have hsv : K.S (dV δ) = true := by
    show indS (D := D) C.S (dV δ) = true
    rw [indS_dV, hδ1]; rfl
  let T : TriPiece K i j k :=
    { hij := hij, hik := hik, hjk := hjk
      u := dU δ, v := dV δ
      t12 := eO t12, t13 := eO t13, a := eO δ, d1 := eN δ 0, d2 := eN δ 1, b := eN δ 2
      p12 := (set_eO Q t12).2 h12, p13 := (set_eO Q t13).2 h13, pa := (set_eO Q δ).2 hQδ
      pd1 := (set_eN Q δ 0).2 ⟨hQδ, hDδ⟩, pd2 := (set_eN Q δ 1).2 ⟨hQδ, hDδ⟩, pb := (set_eN Q δ 2).2 ⟨hQδ, hDδ⟩
      j12 := by rw [hKy, hKy]; exact joinsO hD12 j12
      j13 := by rw [hKy, hKy]; exact joinsO hD13 j13
      ja := by rw [hKy, ← hj]; exact Or.inl (ends_eO_D hDδ)
      jd1 := Or.inl (ends_eN01 δ 0 (by decide))
      jd2 := Or.inl (ends_eN01 δ 1 (by decide))
      jb := by rw [hKy, ← hk]; exact Or.inl (ends_eN2 δ)
      dd := fun h => absurd (eN_inj h).2 (by decide)
      su := hsu, sv := hsv
      uy := fun t => by rw [hKy]; exact fun h => dO_ne_dU _ _ h.symm
      vy := fun t => by rw [hKy]; exact fun h => dO_ne_dV _ _ h.symm
      uv := dU_ne_dV _ _
      side := fun x hx hxm => by
        rcases vert_cases x with ⟨z, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
        · have hzs : C.S z = true := by
            have : indS (D := D) C.S (dO z) = true := hx
            rwa [indS_dO] at this
          have hzm : meets Q z := (meets_dig_dO hloop z).1 hxm
          rcases hS3 z hzm hzs with rfl | rfl | rfl
          · exact Or.inl (hKy i).symm
          · exact Or.inr (Or.inl (hKy j).symm)
          · exact Or.inr (Or.inr (Or.inl (hKy k).symm))
        · have hdm := (meets_dig_dU d).1 hxm
          have hdS : (C.S (Y.ends d).1 || C.S (Y.ends d).2) = true := by
            have : indS (D := D) C.S (dU d) = true := hx
            rwa [indS_dU] at this
          have hd : d = δ := huniq d hdm.1 hdm.2 (by
            cases h : C.S (Y.ends d).1
            · rw [h] at hdS; exact Or.inr (by simpa using hdS)
            · exact Or.inl rfl)
          subst hd
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · have hdm := (meets_dig_dV d).1 hxm
          have hdS : (C.S (Y.ends d).1 || C.S (Y.ends d).2) = true := by
            have : indS (D := D) C.S (dV d) = true := hx
            rwa [indS_dV] at this
          have hd : d = δ := huniq d hdm.1 hdm.2 (by
            cases h : C.S (Y.ends d).1
            · rw [h] at hdS; exact Or.inr (by simpa using hdS)
            · exact Or.inl rfl)
          subst hd
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl))) }
  have hdom : Dominant K.flip.hubPorts :=
    dominant_cast (cont_flip_flip K) K.flip.hubPorts (hdomAll _)
  exact T.tri_brick_ex hGd hdom hT1

end inst

end RH2F

namespace RH2F
open MGraph

/-- **layer 22 of the Lean formalization**: Lemma TRI-BRICK-EX (fact bd9a25a5df6fd97a) with Lemma M6B-LIFT (fact
    ab4a4377238c0765), in the instance TRIBRICKEX of layer 21 (fact 30194dab4e05fdcf); hence H-RED13 (c) and the
    closing set CS2′ from the finite facts BASE12, SIMPLE14, B14-D, SMALLHOST-D and SMALL-PD (A) alone -/
theorem layer22 :
    TRIBRICKEX ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD → HRED13c) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD →
      FEEXTD10 → FEEXISTD10 → POLE → T1TRI → IID → DMS) :=
  ⟨tribrickex_holds, fun hB12 hS14 hB14 hSH hPD => hred13c_of hB12 hS14 hB14 hSH hPD tribrickex_holds,
    fun hB12 hS14 hB14 hSH hPD => layer21.2 hB12 hS14 hB14 hSH hPD tribrickex_holds⟩

end RH2F
