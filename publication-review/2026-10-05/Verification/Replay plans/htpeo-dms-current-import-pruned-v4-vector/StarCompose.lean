/-
  StarCompose.lean — the composition lemma: a star colouring of an edge set plus a matching coloured with fresh
  colours, properly on the "conflict" relation, is a star colouring of the union with the two palettes added.

    `starOn_compose`      StarOn F k cF  +  M a matching, cM : M → Fin j with cM a ≠ cM b whenever an F-edge joins
                          an endpoint of a to an endpoint of b   ⟹   StarOn (F ∪ M) (k + j)
    `five_of_matching`    k = 3, j = 2: a 2-factor (or any star-3-colourable spanning part) plus a matching whose
                          conflict graph is bipartite gives a star 5-colouring;
    `seven_of_matching`   k = 3, j = 4: the shape of the Dvořák–Mohar–Šámal bound 7 = 3 + 4;
    `star_of_poor_matching`  a normal (Petersen-type) colouring whose poor edges form a matching is a star colouring.

  This is the only constructive tool available for five colours, and its limit is exact: the conflict graph of a
  perfect matching in a cubic graph is 4-regular, so a bipartite one needs |M| even, i.e. n ≡ 0 (mod 4); for the
  other half of the cubic graphs no star 5-colouring separates into a cycle palette and a matching palette.
  No `sorry`, standard axioms only.
-/
import StarReduce

namespace MGraph
variable {G : MGraph}

/-! ### two disjoint palettes inside `Fin (k + j)` -/

theorem castAdd_ne_natAdd {k j : Nat} (a : Fin k) (b : Fin j) : Fin.castAdd j a ≠ Fin.natAdd k b := by
  intro h
  have h' : a.val = k + b.val := congrArg Fin.val h
  have := a.isLt
  omega

theorem castAdd_inj {k j : Nat} {a b : Fin k} (h : Fin.castAdd j a = Fin.castAdd j b) : a = b := by
  have h' := congrArg Fin.val h
  exact Fin.ext h'

theorem natAdd_inj {k j : Nat} {a b : Fin j} (h : Fin.natAdd k a = Fin.natAdd k b) : a = b := by
  apply Fin.ext
  have h' : k + a.val = k + b.val := congrArg Fin.val h
  omega

/-! ### the composition lemma -/

open Classical in
/-- **Composition.**  Let `cF` be a star `k`-colouring of the edge set `F`, and let `M` be a matching (no two
    edges of `M` share a vertex) coloured by `cM` with `j` fresh colours so that two edges of `M` joined by an edge of
    `F` receive different colours.  Then `F ∪ M` is star `(k+j)`-coloured by `cF` on `F` and `k + cM` on `M`. -/
theorem starOn_compose {F M : Fin G.m → Prop} {k j : Nat} (cF : Fin G.m → Fin k) (cM : Fin G.m → Fin j)
    (hF : StarOn F k cF)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hconf : ∀ a b e, M a → M b → a ≠ b → F e → ∀ x y, G.Joins e x y → G.Inc a x → G.Inc b y →
      cM a ≠ cM b) :
    StarOn (fun f => F f ∨ M f) (k + j)
      (fun f => if M f then Fin.natAdd k (cM f) else Fin.castAdd j (cF f)) := by
  constructor
  · intro a b hab ha hb heq
    rcases hab with ⟨hne, x, hax, hbx⟩
    by_cases hma : M a <;> by_cases hmb : M b
    · exact hmatch a b hma hmb hne x hax hbx
    · simp only [if_pos hma, if_neg hmb] at heq; exact castAdd_ne_natAdd _ _ heq.symm
    · simp only [if_neg hma, if_pos hmb] at heq; exact castAdd_ne_natAdd _ _ heq
    · simp only [if_neg hma, if_neg hmb] at heq
      exact hF.1 a b ⟨hne, x, hax, hbx⟩ (ha.resolve_right hma) (hb.resolve_right hmb) (castAdd_inj heq)
  · intro w h1 h2 h3 h4 hb
    rcases hb with ⟨hb13, hb24⟩
    by_cases m1 : M w.e1 <;> by_cases m3 : M w.e3
    · -- e1, e3 ∈ M: they are joined by e2
      simp only [if_pos m1, if_pos m3] at hb13
      by_cases m2 : M w.e2
      · exact hmatch w.e1 w.e2 m1 m2 w.e1_ne_e2 w.v1 w.inc_e1_v1 w.inc_e2_v1
      · exact hconf w.e1 w.e3 w.e2 m1 m3 w.e1_ne_e3 (h2.resolve_right m2) w.v1 w.v2 w.h2 w.inc_e1_v1
          w.inc_e3_v2 (natAdd_inj hb13)
    · simp only [if_pos m1, if_neg m3] at hb13; exact castAdd_ne_natAdd _ _ hb13.symm
    · simp only [if_neg m1, if_pos m3] at hb13; exact castAdd_ne_natAdd _ _ hb13
    · -- e1, e3 ∈ F
      simp only [if_neg m1, if_neg m3] at hb13
      by_cases m2 : M w.e2 <;> by_cases m4 : M w.e4
      · -- e2, e4 ∈ M: they are joined by e3 ∈ F
        simp only [if_pos m2, if_pos m4] at hb24
        exact hconf w.e2 w.e4 w.e3 m2 m4 w.e2_ne_e4 (h3.resolve_right m3) w.v2 w.v3 w.h3 w.inc_e2_v2
          w.inc_e4_v3 (natAdd_inj hb24)
      · simp only [if_pos m2, if_neg m4] at hb24; exact castAdd_ne_natAdd _ _ hb24.symm
      · simp only [if_neg m2, if_pos m4] at hb24; exact castAdd_ne_natAdd _ _ hb24
      · simp only [if_neg m2, if_neg m4] at hb24
        exact hF.2 w (h1.resolve_right m1) (h2.resolve_right m2) (h3.resolve_right m3) (h4.resolve_right m4)
          ⟨castAdd_inj hb13, castAdd_inj hb24⟩

/-- **3 + 2 = 5.**  A star 3-colourable edge set (e.g. a 2-factor without 5-cycles) plus a matching whose
    conflict graph is bipartite: star 5-colourable. -/
theorem five_of_matching {F M : Fin G.m → Prop} (cF : Fin G.m → Fin 3) (cM : Fin G.m → Fin 2)
    (hF : StarOn F 3 cF)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hconf : ∀ a b e, M a → M b → a ≠ b → F e → ∀ x y, G.Joins e x y → G.Inc a x → G.Inc b y →
      cM a ≠ cM b) :
    Colourable (fun f => F f ∨ M f) 5 :=
  ⟨_, starOn_compose cF cM hF hmatch hconf⟩

/-- **3 + 4 = 7** — the shape of the Dvořák–Mohar–Šámal bound: a star 3-coloured 2-factor plus a perfect matching
    split into four induced matchings. -/
theorem seven_of_matching {F M : Fin G.m → Prop} (cF : Fin G.m → Fin 3) (cM : Fin G.m → Fin 4)
    (hF : StarOn F 3 cF)
    (hmatch : ∀ a b, M a → M b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False)
    (hconf : ∀ a b e, M a → M b → a ≠ b → F e → ∀ x y, G.Joins e x y → G.Inc a x → G.Inc b y →
      cM a ≠ cM b) :
    Colourable (fun f => F f ∨ M f) 7 :=
  ⟨_, starOn_compose cF cM hF hmatch hconf⟩

/-! ### normal colourings -/

/-- **Normal colourings with a poor matching are star colourings.**  `Poor` marks the poor edges; the colouring is
    normal in the sense that an edge whose two opposite neighbours share a colour is poor (it is not rich).  If no two
    poor edges share a vertex, there is no bicoloured walk: the two middle edges of one would both be poor. -/
theorem star_of_poor_matching {P : Fin G.m → Prop} {k : Nat} (c : Fin G.m → Fin k) (Poor : Fin G.m → Prop)
    (hproper : ∀ a b, G.Adj a b → P a → P b → c a ≠ c b)
    (hnormal : ∀ e a b x y, P e → P a → P b → G.Joins e x y → G.Inc a x → G.Inc b y → a ≠ e → b ≠ e → a ≠ b →
      c a = c b → Poor e)
    (hmatch : ∀ a b, Poor a → Poor b → a ≠ b → ∀ x, G.Inc a x → G.Inc b x → False) :
    StarOn P k c := by
  refine ⟨hproper, ?_⟩
  intro w h1 h2 h3 h4 hb
  rcases hb with ⟨hb13, hb24⟩
  have p2 : Poor w.e2 := hnormal w.e2 w.e1 w.e3 w.v1 w.v2 h2 h1 h3 w.h2 w.inc_e1_v1 w.inc_e3_v2
    w.e1_ne_e2 (fun h => w.e2_ne_e3 h.symm) w.e1_ne_e3 hb13
  have p3 : Poor w.e3 := hnormal w.e3 w.e2 w.e4 w.v2 w.v3 h3 h2 h4 w.h3 w.inc_e2_v2 w.inc_e4_v3
    w.e2_ne_e3 (fun h => w.e3_ne_e4 h.symm) w.e2_ne_e4 hb24
  exact hmatch w.e2 w.e3 p2 p3 w.e2_ne_e3 w.v2 w.inc_e2_v2 w.inc_e3_v2

end MGraph
