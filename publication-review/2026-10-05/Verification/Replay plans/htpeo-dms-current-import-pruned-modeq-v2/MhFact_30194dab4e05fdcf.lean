-- Lean proof of fact 30194dab4e05fdcf (RH2F.layer21); added by fact_submit, do not edit
import MhFact_f7fb58786d241d68
set_option backward.isDefEq.respectTransparency false


/-
  IV10.lean — Lemma TRI-BRICK (fact 9c887eb8c268edb0) (a): a triangle side of a 3-edge-cut with distinct ends. If
  the pole of the contraction of the triangle at its hub is dominant, the multigraph is EX1-good (the contraction of the
  other side is K₄, which is EX1-full).
-/

namespace RH2F
open MGraph
open Classical

section tri
variable {X : MGraph} {P : Fin X.m → Prop}

/-- a simple edge set is not isomorphic to a multigraph with two parallel edges -/
theorem simple_not_par_iso (hS : SimpleP P) {H : MGraph} (h : IsoFrom P H) {j j' : Fin H.m} (hjj : j ≠ j')
    (hpar : H.ends j = H.ends j') : False := by
  obtain ⟨α, β, hα, hβ, hs, hj⟩ := h
  obtain ⟨f, hf, rfl⟩ := hs j
  obtain ⟨f', hf', rfl⟩ := hs j'
  have j1 := hj f hf
  have j2 := hj f' hf'
  have j1' : H.Joins (β f') (α (X.ends f).1) (α (X.ends f).2) := by unfold Joins at j1 ⊢; rw [← hpar]; exact j1
  have m1 : ∀ g, P g → meets P (X.ends g).1 := fun g hg => ⟨g, hg, Or.inl rfl⟩
  have m2 : ∀ g, P g → meets P (X.ends g).2 := fun g hg => ⟨g, hg, Or.inr rfl⟩
  apply hjj
  congr 1
  rcases joins_unique j1' j2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have a1 := hα _ _ (m1 f hf) (m1 f' hf') e1
    have a2 := hα _ _ (m2 f hf) (m2 f' hf') e2
    exact hS f f' _ _ hf hf' (joins_ends f) (by rw [a1, a2]; exact joins_ends f')
  · have a1 := hα _ _ (m1 f hf) (m2 f' hf') e1
    have a2 := hα _ _ (m2 f hf) (m1 f' hf') e2
    exact hS f f' _ _ hf hf' (joins_ends f) (by rw [a1, a2]; exact Or.symm (joins_ends f'))

namespace Cut3
variable (C : Cut3 P)

/-- the vertices of side `B` meeting `P` are exactly the three far ends when side `B` has three vertices -/
theorem sideB3 (h3 : scount P C.S false = 3) {x : Fin X.n} (hx : meets P x) (hs : C.S x = false) :
    ∃ t, x = C.w t := by
  by_contra hno
  push_neg at hno
  have hw : ∀ t, meets P (C.w t) ∧ C.S (C.w t) = false := fun t => ⟨⟨C.e t, C.hP t, joins_inc_right (C.hj t)⟩, C.sw t⟩
  have d01 : C.w 0 ≠ C.w 1 := fun h => by have := C.winj _ _ h; simp [Fin.ext_iff] at this
  have d02 : C.w 0 ≠ C.w 2 := fun h => by have := C.winj _ _ h; simp [Fin.ext_iff] at this
  have d12 : C.w 1 ≠ C.w 2 := fun h => by have := C.winj _ _ h; simp [Fin.ext_iff] at this
  -- four distinct vertices on side `B`
  have h4 : cntF X.n (fun v => (v = C.w 0 ∨ v = C.w 1 ∨ v = C.w 2) ∨ v = x) ≤ scount P C.S false := by
    unfold scount
    apply cntF_mono
    rintro v ((rfl | rfl | rfl) | rfl)
    · exact hw 0
    · exact hw 1
    · exact hw 2
    · exact ⟨hx, hs⟩
  rw [cntF_split X.n _ (fun v => v = x)] at h4
  have e1 : cntF X.n (fun v => ((v = C.w 0 ∨ v = C.w 1 ∨ v = C.w 2) ∨ v = x) ∧ v = x) = 1 := by
    rw [← cntF_single X.n x]; apply cntF_congr; intro v
    exact ⟨fun h => h.2, fun h => ⟨Or.inr h, h⟩⟩
  have e3 : cntF X.n (fun v => ((v = C.w 0 ∨ v = C.w 1 ∨ v = C.w 2) ∨ v = x) ∧ ¬ v = x) = 3 := by
    refine Eq.trans ?_ (cntF_triple X.n d01 d02 d12); apply cntF_congr; intro v
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro rfl
      rcases h with h | h | h
      · exact hno 0 h
      · exact hno 1 h
      · exact hno 2 h
  omega

/-- with three vertices on side `B`, the contraction of side `A` is simple (it is `K₄`) -/
theorem cont_simple3 (hG : InG X P) (h3 : scount P C.S false = 3) : SimpleP C.cont := by
  have cub : ∀ t, CubicAt P (C.w t) := fun t => hG.2.2.2 _ ⟨C.e t, C.hP t, joins_inc_right (C.hj t)⟩
  -- the ends of an edge inside `B` are far ends
  have endsB : ∀ d, C.flip.inA d → (∃ t, (X.ends d).1 = C.w t) ∧ (∃ t, (X.ends d).2 = C.w t) := by
    intro d hd
    have s1 : C.S (X.ends d).1 = false := by have := hd.2.1; rw [Cut3.flip_S] at this; simpa using this
    have s2 : C.S (X.ends d).2 = false := by have := hd.2.2; rw [Cut3.flip_S] at this; simpa using this
    exact ⟨C.sideB3 h3 ⟨d, hd.1, Or.inl rfl⟩ s1, C.sideB3 h3 ⟨d, hd.1, Or.inr rfl⟩ s2⟩
  intro f g x y hf hg jf jg
  have hn : ∀ a : Fin X.n, (hv C.w a : Fin (addHub X C.w).n) ≠ hub C.w := fun a => hv_ne_hub _ _
  rcases hf with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩ <;> rcases hg with ⟨d', rfl, hd'⟩ | ⟨t', rfl⟩
  · -- two edges inside `B` joining the same two far ends
    by_contra hne
    have hdd : d ≠ d' := fun h => hne (by rw [h])
    have jd := hub_joins_old (q := C.w) (joins_ends d)
    have jd' := hub_joins_old (q := C.w) (joins_ends d')
    have par : X.Joins d' (X.ends d).1 (X.ends d).2 := by
      rcases joins_unique jf jd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jg jd' with ⟨e3, e4⟩ | ⟨e3, e4⟩
      · rw [hv_inj _ (e1.symm.trans e3), hv_inj _ (e2.symm.trans e4)]; exact joins_ends d'
      · rw [hv_inj _ (e1.symm.trans e3), hv_inj _ (e2.symm.trans e4)]; exact Or.symm (joins_ends d')
      · rw [hv_inj _ (e2.symm.trans e4), hv_inj _ (e1.symm.trans e3)]; exact Or.symm (joins_ends d')
      · rw [hv_inj _ (e2.symm.trans e4), hv_inj _ (e1.symm.trans e3)]; exact joins_ends d'
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := endsB d hd
    have hab : a ≠ b := fun h => hG.1 d (by rw [ha, hb, h])
    -- the third far end `c` has an edge inside `B`, which must go to `w a` or `w b`
    obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
      rcases a with ⟨a, ha3⟩; rcases b with ⟨b, hb3⟩
      have : a ≠ b := fun h => hab (Fin.ext h)
      exact ⟨⟨3 - a - b, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega,
        fun h => by simp [Fin.ext_iff] at h; omega⟩
    obtain ⟨f1, _, _, hf1, _, if1, _, _⟩ := C.pairB (cub c)
    obtain ⟨⟨s1, hs1⟩, ⟨s2, hs2⟩⟩ := endsB f1 hf1
    -- the edges inside `B` at `w a` are `d` and `d'`
    have atA : ∀ g, C.flip.inA g → X.Inc g (C.w a) → g = d ∨ g = d' := by
      intro g hgB hga
      obtain ⟨p, q, hpq, hp, hq, ip, iq, hall⟩ := C.pairB (cub a)
      have hdA : X.Inc d (C.w a) := Or.inl ha
      have hd'A : X.Inc d' (C.w a) := by rw [← ha]; exact joins_inc_left par
      rcases hall d hd hdA with e1 | e1 <;> rcases hall d' hd' hd'A with e2 | e2 <;>
        rcases hall g hgB hga with e3 | e3
      all_goals first
        | exact Or.inl (e3.trans e1.symm)
        | exact Or.inr (e3.trans e2.symm)
        | exact absurd (e1.trans e2.symm) hdd
    have atB : ∀ g, C.flip.inA g → X.Inc g (C.w b) → g = d ∨ g = d' := by
      intro g hgB hgb
      obtain ⟨p, q, hpq, hp, hq, ip, iq, hall⟩ := C.pairB (cub b)
      have hdB : X.Inc d (C.w b) := Or.inr hb
      have hd'B : X.Inc d' (C.w b) := by rw [← hb]; exact joins_inc_right par
      rcases hall d hd hdB with e1 | e1 <;> rcases hall d' hd' hd'B with e2 | e2 <;>
        rcases hall g hgB hgb with e3 | e3
      all_goals first
        | exact Or.inl (e3.trans e1.symm)
        | exact Or.inr (e3.trans e2.symm)
        | exact absurd (e1.trans e2.symm) hdd
    -- `f1` joins `w c` to a far end other than `w c`
    have hwc : ∀ s, (X.ends f1).1 = C.w s → (X.ends f1).2 = C.w s → False := fun s h1 h2 =>
      hG.1 f1 (h1.trans h2.symm)
    have jd_ab : X.Joins d (C.w a) (C.w b) := by rw [← ha, ← hb]; exact joins_ends d
    have jd'_ab : X.Joins d' (C.w a) (C.w b) := by rw [← ha, ← hb]; exact par
    have abj : ∀ g, (g = d ∨ g = d') → X.Inc g (C.w c) → False := by
      intro g hg hgc
      have jg : X.Joins g (C.w a) (C.w b) := by
        rcases hg with e | e <;> rw [e]
        · exact jd_ab
        · exact jd'_ab
      rcases inc_of_joins jg hgc with e | e
      · exact hca (C.winj _ _ e)
      · exact hcb (C.winj _ _ e)
    have notc : ∀ s, s ≠ c → X.Inc f1 (C.w s) → False := by
      intro s hs hinc
      have hcase : s = a ∨ s = b := by
        rcases s with ⟨s, hs3⟩; rcases a with ⟨a, ha3⟩; rcases b with ⟨b, hb3⟩; rcases c with ⟨c, hc3⟩
        simp only [Fin.ext_iff, ne_eq] at hs hca hcb hab ⊢; omega
      rcases hcase with e | e
      · rw [e] at hinc; exact abj f1 (atA f1 hf1 hinc) if1
      · rw [e] at hinc; exact abj f1 (atB f1 hf1 hinc) if1
    by_cases e1 : s1 = c <;> by_cases e2 : s2 = c
    · subst e1; subst e2; exact hwc _ hs1 hs2
    · exact notc s2 e2 (Or.inr hs2)
    · exact notc s1 e1 (Or.inl hs1)
    · exact notc s1 e1 (Or.inl hs1)
  · exfalso
    have jd := hub_joins_old (q := C.w) (joins_ends d)
    have jt : (addHub X C.w).Joins (hNew C.w t') (hub C.w) (hv C.w (C.w t')) := Or.inl (hub_ends_new C.w t')
    rcases joins_unique jf jd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jg jt with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
  · exfalso
    have jd := hub_joins_old (q := C.w) (joins_ends d')
    have jt : (addHub X C.w).Joins (hNew C.w t) (hub C.w) (hv C.w (C.w t)) := Or.inl (hub_ends_new C.w t)
    rcases joins_unique jg jd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jf jt with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
    · exact hn _ (e1.symm.trans e3)
    · exact hn _ (e2.symm.trans e4)
  · have jt : (addHub X C.w).Joins (hNew C.w t) (hub C.w) (hv C.w (C.w t)) := Or.inl (hub_ends_new C.w t)
    have jt' : (addHub X C.w).Joins (hNew C.w t') (hub C.w) (hv C.w (C.w t')) := Or.inl (hub_ends_new C.w t')
    congr 1
    apply C.winj
    rcases joins_unique jf jt with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases joins_unique jg jt' with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact hv_inj _ (e2.symm.trans e4)
    · exact absurd (e3.symm.trans e1) (hn _)
    · exact absurd (e1.symm.trans e3) (hn _)
    · exact hv_inj _ (e1.symm.trans e3)

/-- with three vertices on side `B`, the contraction of side `A` is EX1-good (it is isomorphic to `K₄` = Rep03) -/
theorem cont_ex1_3 (hG : InG X P) (h3 : scount P C.S false = 3) : EX1On C.cont := by
  have hGc := C.cont_inG hG
  have hv4 : vcount C.cont = 4 := by rw [C.vcount_cont, h3]
  obtain ⟨k, hk1, hk25, hkn, hiso⟩ := cls 4 _ C.cont hGc hv4 (by decide) (by decide)
  have hk : k = 2 ∨ k = 3 := by
    have key : ∀ k, k < 26 → 1 ≤ k → repN k = 4 → k = 2 ∨ k = 3 := by decide
    exact key k (by omega) hk1 hkn
  rcases hk with rfl | rfl
  · exfalso
    exact simple_not_par_iso (C.cont_simple3 hG h3) hiso (j := ⟨0, by decide⟩) (j' := ⟨1, by decide⟩)
      (by decide) (by decide)
  · exact ex1On_of_iso hiso (ex1Full_rep 3 (Or.inr (Or.inr (Or.inl rfl))))

/-- **Lemma TRI-BRICK (a)**: if side `B` of a 3-edge-cut with distinct ends of a member of 𝒢 has three vertices (a
    triangle) and the pole of the contraction of side `B` at its hub is dominant, then `P` is EX1-good -/
theorem tri_brick (hG : InG X P) (h3 : scount P C.S false = 3) (hdom : Dominant C.hubPorts) : EX1On P :=
  C.brick hG hdom (C.cont_ex1_3 hG h3)

end Cut3

end tri

end RH2F

/-
  IV11.lean — pole dominance is invariant under isomorphism. If the edge set `Q` of `Y` is isomorphic to the
  multigraph `H` by maps `α` (vertices), `β` (edges) with `α v = h0`, then a dominant pole of `H` at `h0` (any
  labelling `E` of its three ports) gives a dominant pole of `Q` at `v` (any labelling `D`). The ports are matched by
  the permutation induced by the isomorphism; admissible outside data are relabelled along it.
-/

namespace RH2F
open MGraph
open Classical

/-- admissibility of an outside datum is invariant under relabelling the ports by a bijection `π` with inverse `ρ` -/
theorem admissible_perm {π ρ : Fin 3 → Fin 3} (h1 : ∀ s, π (ρ s) = s) (h2 : ∀ t, ρ (π t) = t)
    {i : Fin 3} {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop} (h : Admissible i a O B) :
    Admissible (π i) (fun s => a (ρ s)) (fun s => O (ρ s)) (fun s => B (ρ s)) := by
  obtain ⟨ha, hi, hO, hBO, h1a, h1b, h2', h3⟩ := h
  have ne : ∀ t, t ≠ π i → ρ t ≠ i := fun t ht e => ht (by rw [← e, h1])
  refine ⟨fun s t e => ?_, by simp only [h2]; exact hi, fun t => hO _, fun t κ => hBO _ κ, fun κ hκ => ?_,
    fun κ => by simp only [h2]; exact h1b κ, fun t ht => ?_, fun j k hj hk hjk => ?_⟩
  · have := ha _ _ e; rw [← h1 s, ← h1 t, this]
  · simp only [h2] at hκ
    exact ⟨(h1a κ hκ).1, fun t ht => (h1a κ hκ).2 _ (ne t ht)⟩
  · obtain ⟨x1, x2, x3⟩ := h2' _ (ne t ht)
    exact ⟨x1, x2, fun κ hκ => ⟨(x3 κ hκ).1, fun s hs => (x3 κ hκ).2 _ (ne s hs)⟩⟩
  · exact h3 _ _ (ne j hj) (ne k hk) (fun e => hjk (by rw [← h1 j, ← h1 k, e]))

section domiso
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n} {H : MGraph} {h0 : Fin H.n}
  {α : Fin Y.n → Fin H.n} {β : Fin Y.m → Fin H.m}

/-- isomorphism data from the edge set `Q` of `Y` onto the multigraph `H`, sending `v` to `h0` -/
structure IsoData (Q : Fin Y.m → Prop) (v : Fin Y.n) (H : MGraph) (h0 : Fin H.n) (α : Fin Y.n → Fin H.n)
    (β : Fin Y.m → Fin H.m) : Prop where
  ia : ∀ x y, meets Q x → meets Q y → α x = α y → x = y
  ib : ∀ f g, Q f → Q g → β f = β g → f = g
  sb : ∀ j, ∃ f, Q f ∧ β f = j
  jb : ∀ f, Q f → H.Joins (β f) (α (Y.ends f).1) (α (Y.ends f).2)
  hv : α v = h0

theorem isoData_of_isoFrom (h : IsoFrom Q H) : ∃ α β, IsoData Q v H (α v) α β := by
  obtain ⟨α, β, ia, ib, sb, jb⟩ := h
  exact ⟨α, β, ia, ib, sb, jb, rfl⟩

theorem ports_meets_v (D : Ports Q v) : meets Q v := ⟨D.p 0, D.hp 0, joins_inc_left (D.hj 0)⟩
theorem ports_meets_x (D : Ports Q v) (t : Fin 3) : meets Q (D.x t) := ⟨D.p t, D.hp t, joins_inc_right (D.hj t)⟩

namespace IsoData
variable (I : IsoData Q v H h0 α β)
include I

theorem joins {f : Fin Y.m} (hf : Q f) {x y : Fin Y.n} (h : Y.Joins f x y) : H.Joins (β f) (α x) (α y) := by
  have j := I.jb f hf
  rcases h with e | e <;> rw [e] at j
  · exact j
  · exact Or.symm j

theorem inc {f : Fin Y.m} (hf : Q f) {x : Fin Y.n} (h : Y.Inc f x) : H.Inc (β f) (α x) := by
  rcases h with h | h
  · rw [← h]; exact joins_inc_left (I.jb f hf)
  · rw [← h]; exact joins_inc_right (I.jb f hf)

theorem inc_back {f : Fin Y.m} (hf : Q f) {x : Fin Y.n} (hx : meets Q x) (h : H.Inc (β f) (α x)) : Y.Inc f x := by
  rcases inc_of_joins (I.jb f hf) h with e | e
  · exact Or.inl (I.ia _ _ ⟨f, hf, Or.inl rfl⟩ hx e.symm)
  · exact Or.inr (I.ia _ _ ⟨f, hf, Or.inr rfl⟩ hx e.symm)

variable (D : Ports Q v) (E : Ports (fun _ : Fin H.m => True) h0)

theorem port_ex (t : Fin 3) : ∃ s, β (D.p t) = E.p s :=
  E.all _ trivial (by rw [← I.hv]; exact I.inc (D.hp t) (joins_inc_left (D.hj t)))

/-- the port permutation induced by the isomorphism -/
noncomputable def perm (t : Fin 3) : Fin 3 := Classical.choose (I.port_ex D E t)

theorem perm_p (t : Fin 3) : β (D.p t) = E.p (I.perm D E t) := Classical.choose_spec (I.port_ex D E t)

theorem perm_x (t : Fin 3) : α (D.x t) = E.x (I.perm D E t) := by
  have j1 : H.Joins (β (D.p t)) h0 (α (D.x t)) := by rw [← I.hv]; exact I.joins (D.hp t) (D.hj t)
  have j2 := E.hj (I.perm D E t)
  rw [← I.perm_p] at j2
  rcases joins_unique j1 j2 with ⟨_, e⟩ | ⟨e1, e2⟩
  · exact e
  · exact e2.trans e1

theorem perm_inj {s t : Fin 3} (h : I.perm D E s = I.perm D E t) : s = t := by
  have : β (D.p s) = β (D.p t) := by rw [I.perm_p, I.perm_p, h]
  exact D.pinj _ _ (I.ib _ _ (D.hp s) (D.hp t) this)

theorem perm_surj (s : Fin 3) : ∃ t, I.perm D E t = s := by
  obtain ⟨f, hf, hfs⟩ := I.sb (E.p s)
  have hv' : H.Inc (β f) (α v) := by rw [hfs, I.hv]; exact joins_inc_left (E.hj s)
  obtain ⟨t, rfl⟩ := D.all f hf (I.inc_back hf (ports_meets_v D) hv')
  exact ⟨t, E.pinj _ _ (by rw [← I.perm_p, hfs])⟩

/-- the inverse permutation -/
noncomputable def rinv (s : Fin 3) : Fin 3 := Classical.choose (I.perm_surj D E s)

theorem perm_rinv (s : Fin 3) : I.perm D E (I.rinv D E s) = s := Classical.choose_spec (I.perm_surj D E s)

theorem rinv_perm (t : Fin 3) : I.rinv D E (I.perm D E t) = t := I.perm_inj D E (I.perm_rinv D E _)

theorem not_port {f : Fin Y.m} (hf : Q f) (h : ¬ ∃ t, f = D.p t) : ¬ ∃ s, β f = E.p s := by
  rintro ⟨s, hs⟩
  apply h
  refine ⟨I.rinv D E s, I.ib _ _ hf (D.hp _) ?_⟩
  rw [hs, I.perm_p, I.perm_rinv]

/-- the vertex map of the split ambients -/
noncomputable def sig : Fin (Y.n + 3) → Fin (H.n + 3) :=
  Fin.addCases (fun x => Fin.castAdd 3 (α x)) (fun t => Fin.natAdd H.n (I.perm D E t))

theorem sig_cast (x : Fin Y.n) : I.sig D E (Fin.castAdd 3 x) = Fin.castAdd 3 (α x) := by
  simp only [sig, Fin.addCases_left]

theorem sig_nat (t : Fin 3) : I.sig D E (Fin.natAdd Y.n t) = Fin.natAdd H.n (I.perm D E t) := by
  simp only [sig, Fin.addCases_right]

/-- the edges of the split ambient are carried to edges -/
theorem split_joins {f : Fin Y.m} (hf : Q f) :
    (splitV E).Joins (β f) (I.sig D E ((splitV D).ends f).1) (I.sig D E ((splitV D).ends f).2) := by
  by_cases h : ∃ t, f = D.p t
  · obtain ⟨t, rfl⟩ := h
    left
    rw [splitV_ends_port D t, I.perm_p, splitV_ends_port E, I.sig_cast, I.sig_nat, I.perm_x]
  · unfold MGraph.Joins
    rw [splitV_ends_other D h, splitV_ends_other E (I.not_port D E hf h)]
    dsimp only
    rw [I.sig_cast, I.sig_cast]
    rcases I.jb f hf with e | e <;> rw [e]
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- the vertices of the split ambient met by edges of `Q` -/
def Rel (z : Fin (Y.n + 3)) : Prop := (∃ x, meets Q x ∧ z = Fin.castAdd 3 x) ∨ ∃ t, z = Fin.natAdd Y.n t

omit I in
theorem rel_of_inc {f : Fin Y.m} (hf : Q f) {z : Fin (Y.n + 3)} (h : (splitV D).Inc f z) : Rel (Q := Q) z := by
  by_cases hp : ∃ t, f = D.p t
  · obtain ⟨t, rfl⟩ := hp
    unfold MGraph.Inc at h
    rw [splitV_ends_port D t] at h
    rcases h with h | h
    · exact Or.inl ⟨D.x t, ports_meets_x D t, h.symm⟩
    · exact Or.inr ⟨t, h.symm⟩
  · unfold MGraph.Inc at h
    rw [splitV_ends_other D hp] at h
    rcases h with h | h
    · exact Or.inl ⟨_, ⟨f, hf, Or.inl rfl⟩, h.symm⟩
    · exact Or.inl ⟨_, ⟨f, hf, Or.inr rfl⟩, h.symm⟩

theorem sig_inj {z z' : Fin (Y.n + 3)} (hz : Rel (Q := Q) z) (hz' : Rel (Q := Q) z')
    (h : I.sig D E z = I.sig D E z') : z = z' := by
  rcases hz with ⟨x, hx, rfl⟩ | ⟨t, rfl⟩ <;> rcases hz' with ⟨y, hy, rfl⟩ | ⟨s, rfl⟩
  · rw [I.sig_cast, I.sig_cast] at h
    have : α x = α y := Fin.castAdd_inj.mp h
    rw [I.ia _ _ hx hy this]
  · rw [I.sig_cast, I.sig_nat] at h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    have := (α x).isLt
    omega
  · rw [I.sig_cast, I.sig_nat] at h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    have := (α y).isLt
    omega
  · rw [I.sig_nat, I.sig_nat] at h
    have : I.perm D E t = I.perm D E s := (Fin.natAdd_inj _).mp h
    rw [I.perm_inj D E this]

theorem split_inc {f : Fin Y.m} (hf : Q f) {z : Fin (Y.n + 3)} (h : (splitV D).Inc f z) :
    (splitV E).Inc (β f) (I.sig D E z) := by
  rcases h with h | h
  · rw [← h]; exact joins_inc_left (I.split_joins D E hf)
  · rw [← h]; exact joins_inc_right (I.split_joins D E hf)

theorem split_inc_back {f : Fin Y.m} (hf : Q f) {z : Fin (Y.n + 3)} (hz : Rel (Q := Q) z)
    (h : (splitV E).Inc (β f) (I.sig D E z)) : (splitV D).Inc f z := by
  rcases inc_of_joins (I.split_joins D E hf) h with e | e
  · exact Or.inl (I.sig_inj D E (rel_of_inc D hf (Or.inl rfl)) hz e.symm)
  · exact Or.inr (I.sig_inj D E (rel_of_inc D hf (Or.inr rfl)) hz e.symm)

omit I in
theorem vPole_Q {f : Fin Y.m} (h : vPole D f) : Q f := by
  rcases h with h | ⟨t, rfl⟩
  · exact h.1
  · exact D.hp t

theorem vPole_map {f : Fin Y.m} (h : vPole D f) : vPole E (β f) := by
  rcases h with ⟨hf, hfv⟩ | ⟨t, rfl⟩
  · exact Or.inl ⟨trivial, fun h => hfv (I.inc_back hf (ports_meets_v D) (by rw [I.hv]; exact h))⟩
  · exact Or.inr ⟨I.perm D E t, I.perm_p D E t⟩

theorem vPole_back {f : Fin Y.m} (hf : Q f) (h : vPole E (β f)) : vPole D f := by
  by_cases hp : ∃ t, f = D.p t
  · exact Or.inr hp
  · rcases h with ⟨_, hv'⟩ | hs
    · exact Or.inl ⟨hf, fun h => hv' (by rw [← I.hv]; exact I.inc hf h)⟩
    · exact absurd hs (I.not_port D E hf hp)

theorem mcPole_map {d : Fin H.m → Fin 6} (h : MCPole E d) : MCPole D (fun f => d (β f)) := by
  refine ⟨?_, fun x hxv hx => ?_⟩
  · refine starOn_embed (G := splitV D) (H := splitV E) (φ := I.sig D E) (ψ := β) ?_ ?_ (fun a ha => I.vPole_map D E ha)
      (fun a ha => I.split_joins D E (vPole_Q D ha)) h.1
    · intro x y a b ha hb hax hby e
      exact I.sig_inj D E (rel_of_inc D (vPole_Q D ha) hax) (rel_of_inc D (vPole_Q D hb) hby) e
    · intro a b ha hb e
      exact I.ib _ _ (vPole_Q D ha) (vPole_Q D hb) e
  · have hαx : α x ≠ h0 := fun e => hxv (I.ia _ _ hx (ports_meets_v D) (e.trans I.hv.symm))
    obtain ⟨f, hf, hfx⟩ := hx
    obtain ⟨a', ha', hax', ha5', huniq'⟩ := h.2 (α x) hαx ⟨β f, trivial, I.inc hf hfx⟩
    obtain ⟨a, haQ, rfl⟩ := I.sb a'
    have hrel : Rel (Q := Q) (Fin.castAdd 3 x) := Or.inl ⟨x, ⟨f, hf, hfx⟩, rfl⟩
    refine ⟨a, I.vPole_back D E haQ ha', I.split_inc_back D E haQ hrel (by rw [I.sig_cast]; exact hax'), ha5',
      fun b hb hbx hb5 => ?_⟩
    have := huniq' (β b) (I.vPole_map D E hb) (by rw [← I.sig_cast D E]; exact I.split_inc D E (vPole_Q D hb) hbx) hb5
    exact I.ib _ _ (vPole_Q D hb) haQ this

theorem vCol_map {d : Fin H.m → Fin 6} {t : Fin 3} {κ : Fin 6} (h : vCol D (fun f => d (β f)) t κ) :
    vCol E d (I.perm D E t) κ := by
  obtain ⟨f, hf, hne, hfx, rfl⟩ := h
  refine ⟨β f, I.vPole_map D E hf, fun e => hne ?_, ?_, rfl⟩
  · rw [← I.perm_p] at e
    exact I.ib _ _ (vPole_Q D hf) (D.hp t) e
  · rw [← I.perm_x, ← I.sig_cast D E]
    exact I.split_inc D E (vPole_Q D hf) hfx

theorem vBlk_map {d : Fin H.m → Fin 6} {t : Fin 3} {κ : Fin 6} (h : vBlk D (fun f => d (β f)) t κ) :
    vBlk E d (I.perm D E t) κ := by
  obtain ⟨f, r, hf, hne, hfr, rfl, f', hf', hne', hf'r, hcol⟩ := h
  have hfQ := vPole_Q D hf
  refine ⟨β f, I.sig D E r, I.vPole_map D E hf, fun e => hne ?_, ?_, rfl, β f', I.vPole_map D E hf',
    fun e => hne' (I.ib _ _ (vPole_Q D hf') hfQ e), I.split_inc D E (vPole_Q D hf') hf'r, ?_⟩
  · rw [← I.perm_p] at e
    exact I.ib _ _ hfQ (D.hp t) e
  · have j := I.split_joins D E hfQ
    rw [← I.perm_x, ← I.sig_cast D E]
    rcases hfr with e | e <;> rw [e] at j
    · exact j
    · exact Or.symm j
  · simp only at hcol
    rw [hcol, I.perm_p]

theorem compat_map {d : Fin H.m → Fin 6} {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop}
    (h : Compat E d (fun s => a (I.rinv D E s)) (fun s => O (I.rinv D E s)) (fun s => B (I.rinv D E s))) :
    Compat D (fun f => d (β f)) a O B := by
  refine ⟨fun t => ?_, fun t κ hc hO hb => ?_⟩
  · show d (β (D.p t)) = a t
    rw [I.perm_p, h.1]
    show a (I.rinv D E (I.perm D E t)) = a t
    rw [I.rinv_perm]
  · refine h.2 (I.perm D E t) κ (I.vCol_map D E hc) (by show O _ κ; rw [I.rinv_perm]; exact hO) ?_
    rcases hb with hb | hb
    · exact Or.inl (I.vBlk_map D E hb)
    · exact Or.inr (by show B _ κ; rw [I.rinv_perm]; exact hb)

theorem adm_map {i : Fin 3} {a : Fin 3 → Fin 6} {O B : Fin 3 → Fin 6 → Prop} (h : Admissible i a O B) :
    Admissible (I.perm D E i) (fun s => a (I.rinv D E s)) (fun s => O (I.rinv D E s)) (fun s => B (I.rinv D E s)) :=
  admissible_perm (I.perm_rinv D E) (I.rinv_perm D E) h

theorem d1_map {i : Fin 3} (h : D1 E (I.perm D E i)) : D1 D i := by
  intro a O B hadm
  obtain ⟨d, hd, hc⟩ := h _ _ _ (I.adm_map D E hadm)
  exact ⟨fun f => d (β f), I.mcPole_map D E hd, I.compat_map D E hc⟩

theorem d2_map (h : D2 E) : D2 D := by
  intro g hg hgv s
  have hgv' : ¬ H.Inc (β g) h0 := fun e => hgv (I.inc_back hg (ports_meets_v D) (by rw [I.hv]; exact e))
  obtain ⟨i', hi'⟩ := h (β g) trivial hgv' s
  refine ⟨I.rinv D E i', fun a O B hadm => ?_⟩
  have hadm' := I.adm_map D E hadm
  rw [I.perm_rinv] at hadm'
  obtain ⟨d, hd, hc, h5⟩ := hi' _ _ _ hadm'
  exact ⟨fun f => d (β f), I.mcPole_map D E hd, I.compat_map D E hc, h5⟩

/-- **dominance transfer**: a dominant pole of `H` at `h0` gives a dominant pole of `Q` at `v` -/
theorem dominant_map (h : Dominant E) : Dominant D :=
  ⟨fun i => I.d1_map D E (h.1 _), I.d2_map D E h.2⟩

end IsoData

/-- the identity is isomorphism data of `H` onto itself -/
theorem isoData_id (H : MGraph) (h0 : Fin H.n) : IsoData (fun _ : Fin H.m => True) h0 H h0 id id :=
  ⟨fun _ _ _ _ e => e, fun _ _ _ _ e => e, fun j => ⟨j, trivial, rfl⟩, fun f _ => Or.inl rfl, rfl⟩

/-- dominance of a pole of `H` at `h0` does not depend on the labelling of the ports -/
theorem dominant_relabel {H : MGraph} {h0 : Fin H.n} (E E' : Ports (fun _ : Fin H.m => True) h0)
    (h : Dominant E) : Dominant E' :=
  (isoData_id H h0).dominant_map E' E h

end domiso

end RH2F


/-
  PR1.lean — the named finite facts of the pole route (SMALL-PD (A), SMALLHOST-D, TRI-BRICK-EX in the instance used),
  and the small side of a 3-edge-cut with distinct ends: if its true side has at most 7 vertices and the multigraph at
  least 16, then either the multigraph is EX1-good, or the closure of the small side is `Rep_6` (K₄ with a digon on one
  edge) with its hub at an apex vertex (`2` or `3`), i.e. the small side is a triangle carrying a digon on the edge
  opposite the port of the hub edge.
-/

namespace RH2F
open MGraph
open Classical

/-! ### the named finite facts -/

/-- SMALL-PD (A) (fact 86f2b7c4166011f6), for the four poles that occur: the prism (`Rep_7`), K₃,₃ (`Rep_8`) and V₈
    (`Rep_25`) at every vertex, and K₄ with a digon inserted into the edge `0 1` (`Rep_6`) at the ends `0`, `1` of that
    edge. Every labelling of the ports is dominant. -/
def SMALLPD : Prop :=
  ∀ (k : Nat) (h0 : Fin (repG k).n), (k = 7 ∨ k = 8 ∨ k = 25 ∨ (k = 6 ∧ (h0.val = 0 ∨ h0.val = 1))) →
    ∀ E : Ports (fun _ : Fin (repG k).m => True) h0, Dominant E

/-- Lemma SMALLHOST-D (fact d2f6b988c49c84f6): digon insertions with at least 16 vertices of the c4c simple cubic
    graphs on at most 8 vertices are EX1-good -/
def SMALLHOSTD : Prop :=
  ∀ (Y : MGraph) (Q D : Fin Y.m → Prop), C4C Y Q → SimpleP Q → vcount Q ≤ 8 →
    16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) → EX1On (digSet Q D)

/-- Lemma TRI-BRICK-EX (fact bd9a25a5df6fd97a), in the instance used: `Q ∈ 𝒮`, a 3-edge-cut `C` of `Q` with distinct
    ends whose side `S` has three vertices (a triangle), exactly one edge `δ` of `D` incident with `S`, lying inside `S`
    and missing `y_i`. If every labelling of the pole of `X_T = (Q^D)/V_S` at its hub is dominant and (T1′) holds for
    `(X_T, z_S, w_i)`, then `Q^D` is EX1-good. -/
def TRIBRICKEX : Prop :=
  ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → ∀ (C : Cut3 Q), scount Q C.S true = 3 →
    ∀ (D : Fin Y.m → Prop) (i : Fin 3) (δ : Fin Y.m), Q δ → D δ → C.S (Y.ends δ).1 = true →
      C.S (Y.ends δ).2 = true → ¬ Y.Inc δ (C.y i) →
      (∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = δ) →
      (∀ E : Ports (Cut3.dig (D := D) C).cont (hub (Cut3.dig (D := D) C).w), Dominant E) →
      T1p (Cut3.dig (D := D) C) i → EX1On (digSet Q D)

/-! ### transporting ports along isomorphism data -/

section pmap
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n} {H : MGraph} {h0 : Fin H.n}
  {α : Fin Y.n → Fin H.n} {β : Fin Y.m → Fin H.m}

/-- the ports of `H` at `h0` given by the images of the ports of `Q` at `v` -/
def IsoData.pmap (I : IsoData Q v H h0 α β) (D : Ports Q v) : Ports (fun _ : Fin H.m => True) h0 where
  p := fun t => β (D.p t)
  x := fun t => α (D.x t)
  hp := fun _ => trivial
  hj := fun t => by rw [← I.hv]; exact I.joins (D.hp t) (D.hj t)
  xinj := fun s t h => D.xinj _ _ (I.ia _ _ (ports_meets_x D s) (ports_meets_x D t) h)
  pinj := fun s t h => D.pinj _ _ (I.ib _ _ (D.hp s) (D.hp t) h)
  all := fun j _ hj => by
    obtain ⟨f, hf, rfl⟩ := I.sb j
    rw [← I.hv] at hj
    obtain ⟨t, rfl⟩ := D.all f hf (I.inc_back hf (ports_meets_v D) hj)
    exact ⟨t, rfl⟩

end pmap

/-! ### vertices without three distinct neighbours -/

/-- the other end of `e` at `v` -/
def othE (G : MGraph) (e : Fin G.m) (v : Fin G.n) : Fin G.n :=
  if (G.ends e).1 = v then (G.ends e).2 else (G.ends e).1

theorem othE_of_joins {G : MGraph} {e : Fin G.m} {v x : Fin G.n} (h : G.Joins e v x) : othE G e v = x := by
  unfold othE
  rcases h with h | h <;> rw [h]
  · simp
  · by_cases hx : x = v
    · subst hx; simp
    · simp [hx]

/-- the Bool check: at `v`, among any three distinct incident edges two have the same other end -/
def noThree (G : MGraph) (v : Fin G.n) : Bool :=
  (List.finRange G.m).all fun a => (List.finRange G.m).all fun b => (List.finRange G.m).all fun c =>
    !(a != b && a != c && b != c &&
      ((G.ends a).1 == v || (G.ends a).2 == v) && ((G.ends b).1 == v || (G.ends b).2 == v) &&
      ((G.ends c).1 == v || (G.ends c).2 == v)) ||
    othE G a v == othE G b v || othE G a v == othE G c v || othE G b v == othE G c v

theorem noPorts_of_noThree {G : MGraph} {v : Fin G.n} (h : noThree G v = true)
    (E : Ports (fun _ : Fin G.m => True) v) : False := by
  have key := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h (E.p 0) (mem_finRange' _)) (E.p 1)
    (mem_finRange' _)) (E.p 2) (mem_finRange' _)
  have n01 : E.p 0 ≠ E.p 1 := fun e => absurd (E.pinj _ _ e) (by decide)
  have n02 : E.p 0 ≠ E.p 2 := fun e => absurd (E.pinj _ _ e) (by decide)
  have n12 : E.p 1 ≠ E.p 2 := fun e => absurd (E.pinj _ _ e) (by decide)
  have inc : ∀ t, ((G.ends (E.p t)).1 == v || (G.ends (E.p t)).2 == v) = true := by
    intro t
    rcases E.hj t with h | h <;> rw [h] <;> simp
  have o := fun t => othE_of_joins (E.hj t)
  have b01 : (E.p 0 != E.p 1) = true := bne_iff_ne.2 n01
  have b02 : (E.p 0 != E.p 2) = true := bne_iff_ne.2 n02
  have b12 : (E.p 1 != E.p 2) = true := bne_iff_ne.2 n12
  rw [b01, b02, b12, inc 0, inc 1, inc 2] at key
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, o] at key
  rcases key with (h | h) | h
  · exact absurd (E.xinj _ _ h) (by decide)
  · exact absurd (E.xinj _ _ h) (by decide)
  · exact absurd (E.xinj _ _ h) (by decide)

theorem rep4_noThree : ∀ v : Fin (repG 4).n, noThree (repG 4) v = true := by decide

theorem rep6_noThree4 : noThree (repG 6) ⟨4, by decide⟩ = true := by decide
theorem rep6_noThree5 : noThree (repG 6) ⟨5, by decide⟩ = true := by decide

/-! ### the small side -/

section small
variable {X : MGraph} {P : Fin X.m → Prop}

/-- the closure of the true side of `K` is `Rep_6` with its hub at an apex vertex -/
def ApexIso (K : Cut3 P) : Prop :=
  ∃ (α : Fin (addHub X K.flip.w).n → Fin (repG 6).n) (β : Fin (addHub X K.flip.w).m → Fin (repG 6).m),
    vcount K.flip.cont = 6 ∧ IsoData K.flip.cont (hub K.flip.w) (repG 6) (α (hub K.flip.w)) α β ∧
      ((α (hub K.flip.w)).val = 2 ∨ (α (hub K.flip.w)).val = 3)

theorem vcount_flip_cont (K : Cut3 P) : vcount K.flip.cont = scount P K.S true + 1 := by
  rw [Cut3.vcount_cont, Cut3.scount_flip3]; rfl

theorem vcount_flipflip_cont (K : Cut3 P) : vcount K.flip.flip.cont = scount P K.S false + 1 := by
  rw [Cut3.vcount_cont, Cut3.scount_flip3, Cut3.scount_flip3]; rfl

/-- the T5 representatives are EX1-full -/
theorem ex1Full_T5 {k : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ (9 ≤ k ∧ k ≤ 24)) : EX1FullH (repG k) := by
  obtain ⟨cs, h⟩ := layer7.2.1 k hk
  exact ex1Full_of_cert h

/-- **the small side**: a 3-edge-cut with distinct ends of a 2-cut-reduced member of 𝒢 with at least 16 vertices,
    whose true side has at most 7 vertices. Under (POLE), SMALL-PD and EX1-goodness of all smaller 2-cut-reduced
    members of 𝒢 with at least 10 vertices, the multigraph is EX1-good, unless the closure of the small side is `Rep_6`
    with the hub at an apex vertex. -/
theorem small_side3 (hpole : POLE) (hPD : SMALLPD)
    (ih : ∀ (X' : MGraph) (P' : Fin X'.m → Prop), InG X' P' → 10 ≤ vcount P' → TwoCutReducedOn P' →
      vcount P' < vcount P → EX1On P')
    (hG : InG X P) (h2 : TwoCutReducedOn P) (h16 : 16 ≤ vcount P) (K : Cut3 P) (h7 : scount P K.S true ≤ 7) :
    EX1On P ∨ ApexIso K := by
  have hsplit := vcount_split P K.S
  have h3 := K.three_le_A
  have hZv := vcount_flip_cont K
  -- the big side
  have hbig : EX1On K.flip.cont → EX1On P := by
    intro hZ
    have hdom : Dominant K.flip.hubPorts :=
      hpole _ K.flip.flip.cont (K.flip.flip.cont_inG hG) (by rw [vcount_flipflip_cont]; omega)
        (K.flip.flip.cont_2cr h2) _ K.flip.hubPorts
    exact K.flip.brick hG hdom hZ
  -- the small side is dominant
  have hsmall : Dominant K.hubPorts → EX1On P := by
    intro hdom
    have hW : EX1On K.cont := ih _ K.cont (K.cont_inG hG) (by rw [Cut3.vcount_cont]; omega) (K.cont_2cr h2)
      (by rw [Cut3.vcount_cont]; omega)
    exact K.brick hG hdom hW
  obtain ⟨k, hk1, hk25, hkn, hiso⟩ := cls _ _ K.flip.cont (K.flip.cont_inG hG) rfl (by omega) (by omega)
  obtain ⟨α, β, I⟩ := isoData_of_isoFrom (v := hub K.flip.w) hiso
  have hcase : (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ (9 ≤ k ∧ k ≤ 24)) ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 25 := by
    omega
  rcases hcase with hT5 | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (hbig (ex1On_of_iso hiso (ex1Full_T5 hT5)))
  · exact absurd (noPorts_of_noThree (rep4_noThree _) (I.pmap K.hubPorts)) id
  · have hv6 : (α (hub K.flip.w)).val < 6 := (α (hub K.flip.w)).isLt
    have : (α (hub K.flip.w)).val = 0 ∨ (α (hub K.flip.w)).val = 1 ∨ (α (hub K.flip.w)).val = 2 ∨
        (α (hub K.flip.w)).val = 3 ∨ (α (hub K.flip.w)).val = 4 ∨ (α (hub K.flip.w)).val = 5 := by omega
    rcases this with h | h | h | h | h | h
    · exact Or.inl (hsmall (I.dominant_map K.hubPorts (I.pmap K.hubPorts) (hPD 6 _ (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl h⟩))) (I.pmap K.hubPorts))))
    · exact Or.inl (hsmall (I.dominant_map K.hubPorts (I.pmap K.hubPorts) (hPD 6 _ (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr h⟩))) (I.pmap K.hubPorts))))
    · exact Or.inr ⟨α, β, hkn.symm, I, Or.inl h⟩
    · exact Or.inr ⟨α, β, hkn.symm, I, Or.inr h⟩
    · have e : α (hub K.flip.w) = ⟨4, by decide⟩ := Fin.ext h
      exact absurd (noPorts_of_noThree (e ▸ rep6_noThree4) (e ▸ I.pmap K.hubPorts)) id
    · have e : α (hub K.flip.w) = ⟨5, by decide⟩ := Fin.ext h
      exact absurd (noPorts_of_noThree (e ▸ rep6_noThree5) (e ▸ I.pmap K.hubPorts)) id
  · exact Or.inl (hsmall (I.dominant_map K.hubPorts (I.pmap K.hubPorts) (hPD 7 _ (Or.inl rfl) (I.pmap K.hubPorts))))
  · exact Or.inl (hsmall (I.dominant_map K.hubPorts (I.pmap K.hubPorts) (hPD 8 _ (Or.inr (Or.inl rfl)) (I.pmap K.hubPorts))))
  · exact Or.inl (hsmall (I.dominant_map K.hubPorts (I.pmap K.hubPorts) (hPD 25 _ (Or.inr (Or.inr (Or.inl rfl))) (I.pmap K.hubPorts))))

end small

end RH2F


/-
  PR2.lean — reading the triangle-with-digon piece back to the host. For `Q ∈ 𝒮`, `D` and a 3-edge-cut `C` of `Q` with
  distinct ends: the sides of the induced cut `Cut3.dig C` of `Q^D` have `|S| + 2·#(edges of D meeting S)` and
  `|T| + 2·#(edges of D inside T)` vertices; two parallel edges of `Q^D` are the two edges of an inserted digon; and if
  the closure of a side of `Cut3.dig C` is `Rep_6` with its hub at an apex vertex, then that side of `C` is a
  triangle carrying exactly one edge of `D`, which lies inside it.
-/

namespace RH2F
open MGraph
open Classical

section digcount
variable {Y : MGraph} {D : Fin Y.m → Prop}

/-- **side counts of the induced cut** -/
theorem scount_indS (hloop : Loopless Y) {Q : Fin Y.m → Prop} (S : Fin Y.n → Bool) (b : Bool) :
    scount (digSet Q D) (indS (D := D) S) b =
      scount Q S b + 2 * cntF Y.m (fun d => Q d ∧ D d ∧ (S (Y.ends d).1 || S (Y.ends d).2) = b) := by
  unfold scount
  let A : Finset (Fin Y.m) := Finset.univ.filter (fun d => Q d ∧ D d ∧ (S (Y.ends d).1 || S (Y.ends d).2) = b)
  have hA : cntF Y.m (fun d => Q d ∧ D d ∧ (S (Y.ends d).1 || S (Y.ends d).2) = b) = A.card := by
    rw [cntF_eq_card]; convert rfl
  rw [cntF_eq_card, cntF_eq_card, hA]
  have hset : Finset.univ.filter (fun w => meets (digSet Q D) w ∧ indS (D := D) S w = b) =
      (Finset.univ.filter (fun x => meets Q x ∧ S x = b)).image dO ∪ (A.image dU ∪ A.image dV) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, A]
    rcases vert_cases w with ⟨x, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩
    · rw [meets_dig_dO hloop, indS_dO]
      constructor
      · intro h; exact Or.inl ⟨x, h, rfl⟩
      · rintro (⟨y, hy, h⟩ | ⟨y, _, h⟩ | ⟨y, _, h⟩)
        · rw [dO_inj h] at hy; exact hy
        · exact absurd h.symm (dO_ne_dU _ _)
        · exact absurd h.symm (dO_ne_dV _ _)
    · rw [meets_dig_dU, indS_dU]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨d, ⟨h.1.1, h.1.2, h.2⟩, rfl⟩)
      · rintro (⟨y, _, h⟩ | ⟨y, hy, h⟩ | ⟨y, _, h⟩)
        · exact absurd h (dO_ne_dU _ _)
        · rw [← dU_inj h]; exact ⟨⟨hy.1, hy.2.1⟩, hy.2.2⟩
        · exact absurd h (dU_ne_dV _ _).symm
    · rw [meets_dig_dV, indS_dV]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨d, ⟨h.1.1, h.1.2, h.2⟩, rfl⟩)
      · rintro (⟨y, _, h⟩ | ⟨y, _, h⟩ | ⟨y, hy, h⟩)
        · exact absurd h (dO_ne_dV _ _)
        · exact absurd h (dU_ne_dV _ _)
        · rw [← dV_inj h]; exact ⟨⟨hy.1, hy.2.1⟩, hy.2.2⟩
  have e1 := congrArg Finset.card hset
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (fun a b h => dO_inj h), Finset.card_image_of_injective _ (fun a b h => dU_inj h),
    Finset.card_image_of_injective _ (fun a b h => dV_inj h)] at e1
  · rw [two_mul]; convert e1 using 3; ext; simp
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

/-- **parallel edges of `Q^D`** (Q simple): two distinct edges of `Q^D` joining the same two vertices join the two new
    vertices of an edge of `D` -/
theorem dig_par {Q : Fin Y.m → Prop} (hS : SimpleP Q) {e e' : Fin (digG Y D).m} (he : digSet Q D e)
    (he' : digSet Q D e') (hne : e ≠ e')
    (hj : (digG Y D).Joins e' ((digG Y D).ends e).1 ((digG Y D).ends e).2) :
    ∃ d, Q d ∧ D d ∧ (digG Y D).ends e = (dU d, dV d) := by
  rcases dig_cases e with ⟨d, rfl⟩ | ⟨d, k, rfl⟩ <;> rcases dig_cases e' with ⟨d', rfl⟩ | ⟨d', k', rfl⟩
  · -- two old edges
    have hd := (set_eO Q d).1 he
    have hd' := (set_eO Q d').1 he'
    by_cases hD : D d <;> by_cases hD' : D d' <;> simp only [MGraph.Joins] at hj
    · rw [ends_eO_D hD, ends_eO_D hD'] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact absurd (congrArg eO (dU_inj hj.2)).symm hne
      · exact absurd hj.1 (dO_ne_dU _ _)
    · rw [ends_eO_D hD, ends_eO_nD hD'] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact absurd hj.2 (dO_ne_dU _ _)
      · exact absurd hj.1 (dO_ne_dU _ _)
    · rw [ends_eO_nD hD, ends_eO_D hD'] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact absurd hj.2.symm (dO_ne_dU _ _)
      · exact absurd hj.2.symm (dO_ne_dU _ _)
    · rw [ends_eO_nD hD, ends_eO_nD hD'] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact absurd (congrArg eO (hS d' d _ _ hd' hd (Or.inl (Prod.ext (dO_inj hj.1) (dO_inj hj.2)))
          (joins_ends d))) hne.symm
      · exact absurd (congrArg eO (hS d' d _ _ hd' hd (Or.inr (Prod.ext (dO_inj hj.1) (dO_inj hj.2)))
          (joins_ends d))) hne.symm
  · -- old, new
    exfalso
    simp only [MGraph.Joins] at hj
    by_cases hD : D d
    · rw [ends_eO_D hD] at hj
      rcases k_cases k' with rfl | hk
      · rw [ends_eN2] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dV _ _ hj.1.symm
        · exact dU_ne_dV _ _ hj.1.symm
      · rw [ends_eN01 d' k' hk] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dU _ _ hj.1.symm
        · exact dO_ne_dV _ _ hj.2.symm
    · rw [ends_eO_nD hD] at hj
      rcases k_cases k' with rfl | hk
      · rw [ends_eN2] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dV _ _ hj.1.symm
        · exact dO_ne_dV _ _ hj.1.symm
      · rw [ends_eN01 d' k' hk] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dU _ _ hj.1.symm
        · exact dO_ne_dV _ _ hj.2.symm
  · -- new, old
    exfalso
    simp only [MGraph.Joins] at hj
    by_cases hD : D d'
    · rw [ends_eO_D hD] at hj
      rcases k_cases k with rfl | hk
      · rw [ends_eN2] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dV _ _ hj.1
        · exact dU_ne_dV _ _ hj.2
      · rw [ends_eN01 d k hk] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dU _ _ hj.1
        · exact dO_ne_dV _ _ hj.1
    · rw [ends_eO_nD hD] at hj
      rcases k_cases k with rfl | hk
      · rw [ends_eN2] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dV _ _ hj.1
        · exact dO_ne_dV _ _ hj.2
      · rw [ends_eN01 d k hk] at hj
        rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
        · exact dO_ne_dU _ _ hj.1
        · exact dO_ne_dV _ _ hj.1
  · -- two new edges
    obtain ⟨hd, hD⟩ := (set_eN Q d k).1 he
    simp only [MGraph.Joins] at hj
    rcases k_cases k with rfl | hk <;> rcases k_cases k' with rfl | hk'
    · exfalso
      rw [ends_eN2, ends_eN2] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact hne (by rw [dV_inj hj.1])
      · exact dO_ne_dV _ _ hj.2
    · exfalso
      rw [ends_eN2, ends_eN01 d' k' hk'] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact dO_ne_dV _ _ hj.2.symm
      · exact dO_ne_dU _ _ hj.1.symm
    · exfalso
      rw [ends_eN01 d k hk, ends_eN2] at hj
      rcases hj with hj | hj <;> simp only [Prod.mk.injEq] at hj
      · exact dU_ne_dV _ _ hj.1.symm
      · exact dO_ne_dU _ _ hj.2
    · exact ⟨d, hd, hD, ends_eN01 d k hk⟩

end digcount

/-! ### facts about `Rep_6` -/

theorem rep6_e6 : (repG 6).ends ⟨6, by decide⟩ = (⟨4, by decide⟩, ⟨5, by decide⟩) := by decide
theorem rep6_e7 : (repG 6).ends ⟨7, by decide⟩ = (⟨4, by decide⟩, ⟨5, by decide⟩) := by decide

/-- no edge of `Rep_6` joins an apex vertex (`2`, `3`) to a digon vertex (`4`, `5`) -/
theorem rep6_noapex : ∀ j : Fin (repG 6).m,
    ((((repG 6).ends j).1.val = 2 ∨ ((repG 6).ends j).1.val = 3) → ((repG 6).ends j).2.val ≠ 4 ∧ ((repG 6).ends j).2.val ≠ 5) ∧
    ((((repG 6).ends j).2.val = 2 ∨ ((repG 6).ends j).2.val = 3) → ((repG 6).ends j).1.val ≠ 4 ∧ ((repG 6).ends j).1.val ≠ 5) := by
  decide

/-! ### the apex configuration -/

section apex
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

/-- **the digon of an apex closure**: if the closure of the true side of a 3-edge-cut `K` of `Q^D` (Q simple) is
    `Rep_6` with its hub at an apex vertex, then the true side has 5 vertices and contains both new vertices of an edge
    `d0 ∈ Q ∩ D`, none of which is an end `K.y i` of a cut edge -/
theorem apex_digon (hS : SimpleP Q) (K : Cut3 (digSet Q D)) (hA : ApexIso K) :
    scount (digSet Q D) K.S true = 5 ∧ ∃ d0, Q d0 ∧ D d0 ∧ K.S (dU d0) = true ∧ K.S (dV d0) = true ∧
      ∀ i, K.y i ≠ dU d0 ∧ K.y i ≠ dV d0 := by
  obtain ⟨α, β, hv6, I, hap⟩ := hA
  have h5 : scount (digSet Q D) K.S true = 5 := by rw [vcount_flip_cont] at hv6; omega
  refine ⟨h5, ?_⟩
  have hapx : ∀ x : Fin (repG 6).n, x = α (hub K.flip.w) → x.val ≠ 4 ∧ x.val ≠ 5 := by
    intro x hx; rw [hx]; rcases hap with h | h <;> rw [h] <;> decide
  -- the preimages of the two parallel edges 6 and 7 are old edges
  have old : ∀ j : Fin (repG 6).m, (repG 6).ends j = (⟨4, by decide⟩, ⟨5, by decide⟩) →
      ∃ f d, K.flip.cont f ∧ β f = j ∧ f = hOld K.flip.w d ∧ K.flip.flip.inA d ∧
        ((α (hv K.flip.w ((digG Y D).ends d).1)).val = 4 ∧ (α (hv K.flip.w ((digG Y D).ends d).2)).val = 5 ∨
         (α (hv K.flip.w ((digG Y D).ends d).1)).val = 5 ∧ (α (hv K.flip.w ((digG Y D).ends d).2)).val = 4) := by
    intro j hjends
    obtain ⟨f, hf, rfl⟩ := I.sb j
    have hjf := I.jb f hf
    rcases hf with ⟨d, rfl, hd⟩ | ⟨t, rfl⟩
    · refine ⟨_, d, Or.inl ⟨d, rfl, hd⟩, rfl, rfl, hd, ?_⟩
      rw [hub_ends_old] at hjf
      rcases hjf with h | h <;> rw [hjends] at h <;> simp only [Prod.mk.injEq] at h
      · exact Or.inl ⟨by rw [← h.1], by rw [← h.2]⟩
      · exact Or.inr ⟨by rw [← h.2], by rw [← h.1]⟩
    · exfalso
      rw [hub_ends_new] at hjf
      rcases hjf with h | h <;> rw [hjends] at h <;> simp only [Prod.mk.injEq] at h
      · exact (hapx _ h.1).1 rfl
      · exact (hapx _ h.2).2 rfl
  obtain ⟨f6, d6, hf6, hb6, rfl, hin6, h6⟩ := old ⟨6, by decide⟩ rep6_e6
  obtain ⟨f7, d7, hf7, hb7, rfl, hin7, h7⟩ := old ⟨7, by decide⟩ rep6_e7
  have hne : d6 ≠ d7 := by
    rintro rfl; rw [hb6] at hb7; exact absurd (congrArg Fin.val hb7) (by decide)
  have hd6 : digSet Q D d6 := hin6.1
  have hd7 : digSet Q D d7 := hin7.1
  have m6 : ∀ b : Bool, meets K.flip.cont (hv K.flip.w (if b then ((digG Y D).ends d6).1 else ((digG Y D).ends d6).2)) := by
    intro b; cases b
    · exact ⟨hOld K.flip.w d6, hf6, Or.inr (by rw [hub_ends_old]; rfl)⟩
    · exact ⟨hOld K.flip.w d6, hf6, Or.inl (by rw [hub_ends_old]; rfl)⟩
  have m7 : ∀ b : Bool, meets K.flip.cont (hv K.flip.w (if b then ((digG Y D).ends d7).1 else ((digG Y D).ends d7).2)) := by
    intro b; cases b
    · exact ⟨hOld K.flip.w d7, hf7, Or.inr (by rw [hub_ends_old]; rfl)⟩
    · exact ⟨hOld K.flip.w d7, hf7, Or.inl (by rw [hub_ends_old]; rfl)⟩
  have eqv : ∀ b b' : Bool, α (hv K.flip.w (if b then ((digG Y D).ends d6).1 else ((digG Y D).ends d6).2)) =
      α (hv K.flip.w (if b' then ((digG Y D).ends d7).1 else ((digG Y D).ends d7).2)) →
      (if b then ((digG Y D).ends d6).1 else ((digG Y D).ends d6).2) =
        (if b' then ((digG Y D).ends d7).1 else ((digG Y D).ends d7).2) :=
    fun b b' h => hv_inj _ (I.ia _ _ (m6 b) (m7 b') h)
  have hj : (digG Y D).Joins d7 ((digG Y D).ends d6).1 ((digG Y D).ends d6).2 := by
    rcases h6 with ⟨a6, b6⟩ | ⟨a6, b6⟩ <;> rcases h7 with ⟨a7, b7⟩ | ⟨a7, b7⟩
    · left
      have e1 := eqv true true (Fin.ext (by simp only [if_true]; rw [a6, a7]))
      have e2 := eqv false false (Fin.ext (by simp only [Bool.false_eq_true, if_false]; rw [b6, b7]))
      simp only [if_true, Bool.false_eq_true, if_false] at e1 e2
      rw [e1, e2]
    · right
      have e1 := eqv true false (Fin.ext (by simp only [if_true, Bool.false_eq_true, if_false]; rw [a6, b7]))
      have e2 := eqv false true (Fin.ext (by simp only [if_true, Bool.false_eq_true, if_false]; rw [b6, a7]))
      simp only [if_true, Bool.false_eq_true, if_false] at e1 e2
      rw [e1, e2]
    · right
      have e1 := eqv true false (Fin.ext (by simp only [if_true, Bool.false_eq_true, if_false]; rw [a6, b7]))
      have e2 := eqv false true (Fin.ext (by simp only [if_true, Bool.false_eq_true, if_false]; rw [b6, a7]))
      simp only [if_true, Bool.false_eq_true, if_false] at e1 e2
      rw [e1, e2]
    · left
      have e1 := eqv true true (Fin.ext (by simp only [if_true]; rw [a6, a7]))
      have e2 := eqv false false (Fin.ext (by simp only [Bool.false_eq_true, if_false]; rw [b6, b7]))
      simp only [if_true, Bool.false_eq_true, if_false] at e1 e2
      rw [e1, e2]
  obtain ⟨d0, hQ0, hD0, hends⟩ := dig_par hS hd6 hd7 hne hj
  have hinA : K.inA d6 := (Cut3.flip_flip_inA K).1 hin6
  refine ⟨d0, hQ0, hD0, ?_, ?_, fun i => ?_⟩
  · have := hinA.2.1; rw [hends] at this; exact this
  · have := hinA.2.2; rw [hends] at this; exact this
  · -- the hub is not adjacent to a digon vertex
    have hjn := I.jb (hNew K.flip.w i) (Or.inr ⟨i, rfl⟩)
    rw [hub_ends_new] at hjn
    have hqi : K.flip.w i = K.y i := rfl
    have key : ∀ b : Bool, K.y i = (if b then ((digG Y D).ends d6).1 else ((digG Y D).ends d6).2) → False := by
      intro b hb
      have hval : (α (hv K.flip.w (K.y i))).val = 4 ∨ (α (hv K.flip.w (K.y i))).val = 5 := by
        rw [hb]; cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;> omega
      have hr := rep6_noapex (β (hNew K.flip.w i))
      rcases hjn with h | h <;> rw [h] at hr <;> simp only at hr <;> rw [hqi] at hr
      · rcases hap with ha | ha <;> rcases hval with hv | hv
        · exact (hr.1 (Or.inl ha)).1 hv
        · exact (hr.1 (Or.inl ha)).2 hv
        · exact (hr.1 (Or.inr ha)).1 hv
        · exact (hr.1 (Or.inr ha)).2 hv
      · rcases hap with ha | ha <;> rcases hval with hv | hv
        · exact (hr.2 (Or.inl ha)).1 hv
        · exact (hr.2 (Or.inl ha)).2 hv
        · exact (hr.2 (Or.inr ha)).1 hv
        · exact (hr.2 (Or.inr ha)).2 hv
    refine ⟨fun h => key true ?_, fun h => key false ?_⟩
    · simp only [if_true]; rw [hends]; exact h
    · simp only [Bool.false_eq_true, if_false]; rw [hends]; exact h

end apex

end RH2F


/-
  PR3.lean — the two apex configurations read back to the host `Q`, the shifted cut (the digon of one cut edge moved
  to the other side), and small combinatorial facts (a `Cut3` is a 3-edge-cut; cyclic sides are symmetric; the apex of
  a triangle side).
-/

namespace RH2F
open MGraph
open Classical

section misc
variable {X : MGraph} {P : Fin X.m → Prop}

/-- a `Cut3` is a 3-edge-cut -/
theorem cut3_threeCut (K : Cut3 P) : ThreeCut P K.S := by
  have hc : ∀ i, RH2F.Crosses P K.S (K.e i) := by
    intro i
    refine ⟨K.hP i, ?_⟩
    rcases K.hj i with h | h <;> rw [h] <;> simp [K.sy i, K.sw i]
  have d : ∀ i j : Fin 3, i ≠ j → K.e i ≠ K.e j := fun i j hij h => hij (K.einj _ _ h)
  refine ⟨K.e 0, K.e 1, K.e 2, d _ _ (by decide), d _ _ (by decide), d _ _ (by decide), hc 0, hc 1, hc 2,
    fun f hf => ?_⟩
  obtain ⟨i, rfl⟩ := K.cut f hf.1 hf.2
  have : i = 0 ∨ i = 1 ∨ i = 2 := by rcases i with ⟨i, hi⟩; simp only [Fin.ext_iff]; omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- the sides of a `Cut3` of a loopless cubic edge set have odd size -/
theorem cut3_odd (hG : InG X P) (K : Cut3 P) (b : Bool) : scount P K.S b % 2 = 1 :=
  three_side_odd hG.1 hG.2.2.2 (cut3_threeCut K) b

/-- cyclic 3-edge-cut sides are symmetric -/
theorem cycSide_flip {S : Fin X.n → Bool} (h : CycSide P S) : CycSide P (fun v => !S v) := by
  obtain ⟨⟨e1, e2, e3, d12, d13, d23, c1, c2, c3, hall⟩, hT, hF⟩ := h
  have cr : ∀ f, RH2F.Crosses P (fun v => !S v) f ↔ RH2F.Crosses P S f := by
    intro f; unfold RH2F.Crosses; constructor
    · rintro ⟨hf, hne⟩; exact ⟨hf, fun e => hne (by simp only [e])⟩
    · rintro ⟨hf, hne⟩; exact ⟨hf, fun e => hne (by simpa using e)⟩
  refine ⟨⟨e1, e2, e3, d12, d13, d23, (cr _).2 c1, (cr _).2 c2, (cr _).2 c3, fun d hd => hall d ((cr d).1 hd)⟩,
    hasCycle_mono (fun f hf => ⟨hf.1, by simp [hf.2.1], by simp [hf.2.2]⟩) hF,
    hasCycle_mono (fun f hf => ⟨hf.1, by simp [hf.2.1], by simp [hf.2.2]⟩) hT⟩

/-- the apex: an edge with both ends among three distinct vertices `y 0, y 1, y 2` misses one of them -/
theorem exists_apex (hloop : Loopless X) (y : Fin 3 → Fin X.n) (hy : ∀ s t, y s = y t → s = t) {δ : Fin X.m}
    (h1 : ∃ a, (X.ends δ).1 = y a) (h2 : ∃ b, (X.ends δ).2 = y b) : ∃ i, ¬ X.Inc δ (y i) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hab : a ≠ b := by
    rintro rfl; exact hloop δ (by rw [ha, hb])
  have hex : ∀ a b : Fin 3, a ≠ b → ∃ i, i ≠ a ∧ i ≠ b := by decide
  obtain ⟨i, hia, hib⟩ := hex a b hab
  refine ⟨i, fun h => ?_⟩
  rcases h with h | h
  · exact hia (hy _ _ (h.symm.trans ha))
  · exact hib (hy _ _ (h.symm.trans hb))

end misc

section apexQ
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

theorem cntF_one_uniq {n : Nat} {W : Fin n → Prop} (h : cntF n W ≤ 1) {a b : Fin n} (ha : W a) (hb : W b) : a = b := by
  by_contra hne
  have h2 : cntF n (fun k => k = a ∨ k = b) ≤ cntF n W :=
    cntF_mono _ _ _ (fun k hk => by rcases hk with rfl | rfl <;> assumption)
  rw [cntF_pair n hne] at h2
  omega

/-- **the apex configuration on side `S`**: if the closure of `V_S` (the true side of `Cut3.dig C`) is `Rep_6` with
    its hub at an apex vertex, then `S` has three vertices and exactly one edge of `D` meets `S`; it lies inside `S` -/
theorem apexS (hQ : InS Y Q) (C : Cut3 Q) (hA : ApexIso (Cut3.dig (D := D) C)) :
    scount Q C.S true = 3 ∧ ∃ δ, Q δ ∧ D δ ∧ C.S (Y.ends δ).1 = true ∧ C.S (Y.ends δ).2 = true ∧
      ∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = δ := by
  obtain ⟨h5, d0, hQ0, hD0, hU, _, hy⟩ := apex_digon hQ.2.1 _ hA
  have hU' : (C.S (Y.ends d0).1 || C.S (Y.ends d0).2) = true := by
    have e : (Cut3.dig (D := D) C).S (dU d0) = indS (D := D) C.S (dU d0) := rfl
    rw [e, indS_dU] at hU; exact hU
  have hc := scount_indS (D := D) hQ.1.1 (Q := Q) C.S true
  have h5' : scount (digSet Q D) (indS (D := D) C.S) true = 5 := h5
  rw [h5'] at hc
  have h3 := C.three_le_A
  have hmem : 1 ≤ cntF Y.m (fun d => Q d ∧ D d ∧ (C.S (Y.ends d).1 || C.S (Y.ends d).2) = true) :=
    cntF_le_of_mem _ _ ⟨hQ0, hD0, hU'⟩
  have hs3 : scount Q C.S true = 3 := by omega
  have hc1 : cntF Y.m (fun d => Q d ∧ D d ∧ (C.S (Y.ends d).1 || C.S (Y.ends d).2) = true) ≤ 1 := by omega
  have huniq : ∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = d0 := by
    intro d hd hDd hSd
    exact cntF_one_uniq hc1 ⟨hd, hDd, by rcases hSd with h | h <;> simp [h]⟩ ⟨hQ0, hD0, hU'⟩
  -- `d0` is not a cut edge
  have hboth : C.S (Y.ends d0).1 = true ∧ C.S (Y.ends d0).2 = true := by
    by_contra hno
    have hne : C.S (Y.ends d0).1 ≠ C.S (Y.ends d0).2 := by
      intro e
      apply hno
      rw [← e] at hU' ⊢
      simp only [Bool.or_self] at hU'
      exact ⟨hU', hU'⟩
    obtain ⟨i, hi⟩ := C.cut d0 hQ0 hne
    have hyi : (Cut3.dig (D := D) C).y i = cutY (D := D) C.S (C.e i) (C.y i) := rfl
    rw [← hi] at hyi
    unfold cutY at hyi
    rw [if_pos hD0] at hyi
    split_ifs at hyi
    · exact (hy i).2 hyi
    · exact (hy i).1 hyi
  exact ⟨hs3, d0, hQ0, hD0, hboth.1, hboth.2, huniq⟩

/-- **the apex configuration on side `T`**: if the closure of `V_T` (the false side of `Cut3.dig C`) is `Rep_6` with
    its hub at an apex vertex, then `T` has three vertices and exactly one edge of `D` lies inside `T` -/
theorem apexT (hQ : InS Y Q) (C : Cut3 Q) (hA : ApexIso (Cut3.dig (D := D) C).flip) :
    scount Q C.S false = 3 ∧ ∃ δ, Q δ ∧ D δ ∧ C.S (Y.ends δ).1 = false ∧ C.S (Y.ends δ).2 = false ∧
      ∀ d, Q d → D d → C.S (Y.ends d).1 = false → C.S (Y.ends d).2 = false → d = δ := by
  obtain ⟨h5, d0, hQ0, hD0, hU, _, _⟩ := apex_digon hQ.2.1 _ hA
  have hU' : (C.S (Y.ends d0).1 || C.S (Y.ends d0).2) = false := by
    have e : (Cut3.dig (D := D) C).flip.S (dU d0) = !indS (D := D) C.S (dU d0) := rfl
    rw [e, indS_dU] at hU; simpa using hU
  have hc := scount_indS (D := D) hQ.1.1 (Q := Q) C.S false
  have h5' : scount (digSet Q D) (indS (D := D) C.S) false = 5 := by
    rw [Cut3.scount_flip3] at h5; exact h5
  rw [h5'] at hc
  have h3 : 3 ≤ scount Q C.S false := by have := C.flip.three_le_A; rw [Cut3.scount_flip3] at this; exact this
  have hmem : 1 ≤ cntF Y.m (fun d => Q d ∧ D d ∧ (C.S (Y.ends d).1 || C.S (Y.ends d).2) = false) :=
    cntF_le_of_mem _ _ ⟨hQ0, hD0, hU'⟩
  have hs3 : scount Q C.S false = 3 := by omega
  have hc1 : cntF Y.m (fun d => Q d ∧ D d ∧ (C.S (Y.ends d).1 || C.S (Y.ends d).2) = false) ≤ 1 := by omega
  have hb : C.S (Y.ends d0).1 = false ∧ C.S (Y.ends d0).2 = false := by
    simpa [Bool.or_eq_false_iff] using hU'
  refine ⟨hs3, d0, hQ0, hD0, hb.1, hb.2, fun d hd hDd h1 h2 => ?_⟩
  exact cntF_one_uniq hc1 ⟨hd, hDd, by simp [h1, h2]⟩ ⟨hQ0, hD0, hU'⟩

end apexQ

section shift
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

/-- the side function of the shifted cut: the two new vertices of `f` are moved to side `false` -/
noncomputable def shS (C : Cut3 Q) (f : Fin Y.m) (w : Fin (digG Y D).n) : Bool :=
  if w = dU f ∨ w = dV f then false else indS (D := D) C.S w

theorem shS_dO (C : Cut3 Q) (f : Fin Y.m) (x : Fin Y.n) : shS (D := D) C f (dO x) = C.S x := by
  unfold shS
  rw [if_neg (by rintro (h | h); exact dO_ne_dU _ _ h; exact dO_ne_dV _ _ h), indS_dO]

theorem shS_U (C : Cut3 Q) (f : Fin Y.m) {w : Fin (digG Y D).n} (h : w = dU f ∨ w = dV f) :
    shS (D := D) C f w = false := by
  unfold shS; rw [if_pos h]

/-- **the shifted cut**: for a cut edge `f = C.e j` carrying a digon, moving its two new vertices from side `V_S` to
    side `V_T` gives a 3-edge-cut with distinct ends of `Q^D` whose false side has two more vertices -/
theorem exists_shift (hQ : InS Y Q) (C : Cut3 Q) (j : Fin 3) (hD : D (C.e j)) :
    ∃ K3 : Cut3 (digSet Q D),
      scount (digSet Q D) K3.S false = scount (digSet Q D) (indS (D := D) C.S) false + 2 := by
  set f := C.e j with hfdef
  have hf : Q f := C.hP j
  have hjf : Y.Joins f (C.y j) (C.w j) := C.hj j
  have hcr : C.S (Y.ends f).1 ≠ C.S (Y.ends f).2 := by
    rcases hjf with h | h <;> rw [h] <;> simp [C.sy j, C.sw j]
  -- the path edge at the `S`-end and the new vertex next to it
  let shE : Fin (digG Y D).m := if C.S (Y.ends f).1 = true then eO f else eN f 2
  let shW : Fin (digG Y D).n := if C.S (Y.ends f).1 = true then dU f else dV f
  have hshW : shW = dU f ∨ shW = dV f := by
    simp only [shW]; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hshE_set : digSet Q D shE := by
    simp only [shE]; split_ifs
    · exact (set_eO Q f).2 hf
    · exact (set_eN Q f 2).2 ⟨hf, hD⟩
  have hshE_j : (digG Y D).Joins shE (dO (C.y j)) shW := by
    simp only [shE, shW]
    rcases hjf with h | h
    · have h1 : C.S (Y.ends f).1 = true := by rw [h]; exact C.sy j
      rw [if_pos h1, if_pos h1]
      exact Or.inl (by rw [ends_eO_D hD, h])
    · have h1 : C.S (Y.ends f).1 = false := by rw [h]; exact C.sw j
      rw [if_neg (by rw [h1]; decide), if_neg (by rw [h1]; decide)]
      exact Or.inr (by rw [ends_eN2, h])
  have hdOU : ∀ x : Fin Y.n, ¬ ((dO x : Fin (digG Y D).n) = dU f ∨ (dO x : Fin (digG Y D).n) = dV f) := by
    rintro x (h | h)
    · exact dO_ne_dU _ _ h
    · exact dO_ne_dV _ _ h
  have hne_j : ∀ i, i ≠ j → C.e i ≠ f := fun i hi h => hi (C.einj _ _ h)
  have hcutY : ∀ i, i ≠ j → ¬ (cutY (D := D) C.S (C.e i) (C.y i) = dU f ∨ cutY (D := D) C.S (C.e i) (C.y i) = dV f) := by
    intro i hi
    unfold cutY
    split_ifs
    · rintro (h | h)
      · exact dU_ne_dV _ _ h.symm
      · exact hne_j i hi (dV_inj h)
    · rintro (h | h)
      · exact hne_j i hi (dU_inj h)
      · exact dU_ne_dV _ _ h
    · exact hdOU _
  have hcutE : ∀ i, i ≠ j → cutE (D := D) C.S (C.e i) ≠ shE := by
    intro i hi h
    simp only [shE] at h
    unfold cutE at h
    split_ifs at h <;> first
      | exact hne_j i hi (eN_inj h).1
      | exact hne_j i hi (eO_inj h)
      | exact eO_ne_eN _ _ _ h
      | exact eO_ne_eN _ _ _ h.symm
  refine ⟨{ S := shS C f
            e := fun i => if i = j then shE else cutE C.S (C.e i)
            y := fun i => if i = j then dO (C.y j) else cutY C.S (C.e i) (C.y i)
            w := fun i => if i = j then shW else dO (C.w i)
            hP := fun i => by
              by_cases hi : i = j
              · rw [if_pos hi]; exact hshE_set
              · rw [if_neg hi]; exact cutE_set C.S (C.hP i)
            hj := fun i => by
              by_cases hi : i = j
              · simp only [if_pos hi]; exact hshE_j
              · simp only [if_neg hi]; exact cutE_joins C.S (C.hj i) (C.sy i) (C.sw i)
            sy := fun i => by
              by_cases hi : i = j
              · simp only [if_pos hi]; rw [shS_dO]; exact C.sy j
              · simp only [if_neg hi]
                unfold shS; rw [if_neg (hcutY i hi)]; exact cutY_side C.S (C.hj i) (C.sy i)
            sw := fun i => by
              by_cases hi : i = j
              · simp only [if_pos hi]; exact shS_U C f hshW
              · simp only [if_neg hi]; rw [shS_dO]; exact C.sw i
            einj := fun i i' h => by
              by_cases hi : i = j <;> by_cases hi' : i' = j <;> simp only [hi, hi', if_true, if_false] at h
              · rw [hi, hi']
              · exact absurd h.symm (hcutE i' hi')
              · exact absurd h (hcutE i hi)
              · exact (Cut3.dig (D := D) C).einj i i' h
            yinj := fun i i' h => by
              by_cases hi : i = j <;> by_cases hi' : i' = j <;> simp only [hi, hi', if_true, if_false] at h
              · rw [hi, hi']
              · exfalso
                unfold cutY at h
                split_ifs at h
                · exact dO_ne_dV _ _ h
                · exact dO_ne_dU _ _ h
                · exact hi' (C.yinj _ _ (dO_inj h)).symm
              · exfalso
                unfold cutY at h
                split_ifs at h
                · exact dO_ne_dV _ _ h.symm
                · exact dO_ne_dU _ _ h.symm
                · exact hi (C.yinj _ _ (dO_inj h))
              · exact (Cut3.dig (D := D) C).yinj i i' h
            winj := fun i i' h => by
              by_cases hi : i = j <;> by_cases hi' : i' = j <;> simp only [hi, hi', if_true, if_false] at h
              · rw [hi, hi']
              · exact absurd (h ▸ hshW) (hdOU _)
              · exact absurd (h.symm ▸ hshW) (hdOU _)
              · exact C.winj _ _ (dO_inj h)
            cut := fun e he hc => by
              by_cases hU : (digG Y D).Inc e (dU f) ∨ (digG Y D).Inc e (dV f)
              · rcases dig_cases e with ⟨d, rfl⟩ | ⟨d, k, rfl⟩
                · have hd : d = f := by
                    rcases hU with h | h
                    · exact (inc_eO_dU.1 h).2
                    · exact absurd h not_inc_eO_dV
                  subst hd
                  rw [ends_eO_D hD, shS_dO, shS_U C _ (Or.inl rfl)] at hc
                  have h1 : C.S (Y.ends (C.e j)).1 = true := by simpa using hc
                  refine ⟨j, ?_⟩
                  simp only [if_true, shE]; rw [if_pos h1]
                · have hd : d = f := by
                    rcases hU with h | h
                    · exact (inc_eN_dU.1 h).2
                    · exact inc_eN_dV.1 h
                  subst hd
                  rcases k_cases k with rfl | hk
                  · rw [ends_eN2, shS_dO, shS_U C _ (Or.inr rfl)] at hc
                    have h2 : C.S (Y.ends (C.e j)).2 = true := by simpa using hc
                    have h1 : C.S (Y.ends (C.e j)).1 = false := by
                      by_contra h; apply hcr; simp only [Bool.not_eq_false] at h; rw [h, h2]
                    refine ⟨j, ?_⟩
                    simp only [if_true, shE]; rw [if_neg (by rw [h1]; decide)]
                  · rw [ends_eN01 _ k hk, shS_U C _ (Or.inl rfl), shS_U C _ (Or.inr rfl)] at hc
                    exact absurd rfl hc
              · have h1 : ¬ (((digG Y D).ends e).1 = dU f ∨ ((digG Y D).ends e).1 = dV f) := by
                  rintro (h | h)
                  · exact hU (Or.inl (Or.inl h))
                  · exact hU (Or.inr (Or.inl h))
                have h2 : ¬ (((digG Y D).ends e).2 = dU f ∨ ((digG Y D).ends e).2 = dV f) := by
                  rintro (h | h)
                  · exact hU (Or.inl (Or.inr h))
                  · exact hU (Or.inr (Or.inr h))
                have hc' : indS (D := D) C.S ((digG Y D).ends e).1 ≠ indS (D := D) C.S ((digG Y D).ends e).2 := by
                  unfold shS at hc; rw [if_neg h1, if_neg h2] at hc; exact hc
                obtain ⟨f', hf', hfc, rfl⟩ := indS_cross C.S he hc'
                obtain ⟨i, rfl⟩ := C.cut f' hf' hfc
                by_cases hi : i = j
                · exfalso
                  subst hi
                  apply hU
                  unfold cutE
                  rw [if_pos hD]
                  split_ifs
                  · exact Or.inr (inc_eN_dV.2 rfl)
                  · exact Or.inl (inc_eO_dU.2 ⟨hD, rfl⟩)
                · exact ⟨i, by simp only [if_neg hi]⟩ }, ?_⟩
  -- the count
  show scount (digSet Q D) (shS C f) false = _
  have hin : (C.S (Y.ends f).1 || C.S (Y.ends f).2) = true := by
    cases h1 : C.S (Y.ends f).1 <;> cases h2 : C.S (Y.ends f).2 <;> simp_all
  unfold scount
  rw [cntF_congr _ _ (fun w => (meets (digSet Q D) w ∧ indS (D := D) C.S w = false) ∨ (w = dU f ∨ w = dV f)) (by
    intro w
    by_cases hw : w = dU f ∨ w = dV f
    · rw [shS_U C f hw]
      refine ⟨fun _ => Or.inr hw, fun _ => ⟨?_, rfl⟩⟩
      rcases hw with rfl | rfl
      · exact (meets_dig_dU f).2 ⟨hf, hD⟩
      · exact (meets_dig_dV f).2 ⟨hf, hD⟩
    · unfold shS; rw [if_neg hw]
      exact ⟨fun h => Or.inl h, fun h => h.resolve_right hw⟩)]
  rw [cntF_split (digG Y D).n _ (fun w => w = dU f ∨ w = dV f)]
  have e1 : cntF (digG Y D).n (fun w => ((meets (digSet Q D) w ∧ indS (D := D) C.S w = false) ∨
      (w = dU f ∨ w = dV f)) ∧ (w = dU f ∨ w = dV f)) = 2 := by
    rw [← cntF_pair _ (dU_ne_dV f f)]
    exact cntF_congr _ _ _ (fun w => ⟨fun h => h.2, fun h => ⟨Or.inr h, h⟩⟩)
  have e2 : cntF (digG Y D).n (fun w => ((meets (digSet Q D) w ∧ indS (D := D) C.S w = false) ∨
      (w = dU f ∨ w = dV f)) ∧ ¬ (w = dU f ∨ w = dV f)) =
      cntF (digG Y D).n (fun w => meets (digSet Q D) w ∧ indS (D := D) C.S w = false) := by
    apply cntF_congr
    intro w
    constructor
    · rintro ⟨h | h, hn⟩
      · exact h
      · exact absurd h hn
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (rfl | rfl)
      · rw [indS_dU, hin] at h; exact absurd h.2 (by decide)
      · rw [indS_dV, hin] at h; exact absurd h.2 (by decide)
  rw [e1, e2]; omega

end shift

end RH2F


/-
  PR4.lean — **H-RED13 (c)** (fact da66a84c773b73b3) in Lean: (KD≥16)₁₀ ∧ (POLE) ∧ (T1′-TRI) ⇒ (H), from the finite
  facts BASE12, SIMPLE14, B14-D, SMALLHOST-D, SMALL-PD (A) (the four poles used) and Lemma TRI-BRICK-EX (the instance
  used) as named hypotheses. The proof uses the full (POLE) at both sides of a cyclic 3-edge-cut of the host, so it
  needs no minimal side and no case analysis on the side sizes beyond ≤ 7 / ≥ 9.
-/

namespace RH2F
open MGraph
open Classical

section main
variable {Y : MGraph} {Q D : Fin Y.m → Prop}

/-- **the induction step**: `Q ∈ 𝒮`, `Q^D` with at least 16 vertices, all smaller 2-cut-reduced members of 𝒢 with at
    least 10 vertices EX1-good -/
theorem hred13_step (hKD : KD16_10) (hpole : POLE) (hT1 : T1TRI) (hSH : SMALLHOSTD) (hPD : SMALLPD)
    (hTB : TRIBRICKEX) (hQ : InS Y Q) (h16 : 16 ≤ vcount (digSet Q D))
    (ih : ∀ (X' : MGraph) (P' : Fin X'.m → Prop), InG X' P' → 10 ≤ vcount P' → TwoCutReducedOn P' →
      vcount P' < vcount (digSet Q D) → EX1On P') : EX1On (digSet Q D) := by
  obtain ⟨hGd, h2d, hvd⟩ := dig_class hQ.1 hQ.2.2 D
  have hn16 : 16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) := by rw [← hvd]; exact h16
  by_cases hc4 : C4C Y Q
  · by_cases hQ10 : 10 ≤ vcount Q
    · exact hKD Y Q D ⟨hc4, hQ.2.1, hQ10, hn16⟩
    · have hevQ := vcount_even' hQ.1
      exact hSH Y Q D hc4 hQ.2.1 (by omega) hn16
  obtain ⟨S, hS⟩ : ∃ S, CycSide Q S := by
    rcases Classical.em (∃ S, CycSide Q S) with hex | hex
    · exact hex
    · exact absurd ((c4c_iff_noCyc hQ.1 hQ.2.2).2 hex) hc4
  obtain ⟨C, hCS⟩ := cycCut hQ.1 hQ.2.2 hS
  subst hCS
  -- T1 and TRI-BRICK-EX at a triangle side `S'` of a cut `C'` carrying exactly one digon, inside `S'`
  have tri : ∀ (C' : Cut3 Q), CycSide Q C'.S → scount Q C'.S true = 3 → ∀ δ, Q δ → D δ →
      C'.S (Y.ends δ).1 = true → C'.S (Y.ends δ).2 = true →
      (∀ d, Q d → D d → (C'.S (Y.ends d).1 = true ∨ C'.S (Y.ends d).2 = true) → d = δ) →
      EX1On (digSet Q D) := by
    intro C' hcyc h3 δ hQδ hDδ h1 h2 huniq
    -- the side `V_S'` has 5 vertices
    have hc := scount_indS (D := D) hQ.1.1 (Q := Q) C'.S true
    have hcnt : cntF Y.m (fun d => Q d ∧ D d ∧ (C'.S (Y.ends d).1 || C'.S (Y.ends d).2) = true) = 1 := by
      apply le_antisymm
      · rw [← cntF_single Y.m δ]
        apply cntF_mono
        intro d ⟨hd, hDd, hSd⟩
        apply huniq d hd hDd
        cases h : C'.S (Y.ends d).1
        · rw [h] at hSd; exact Or.inr (by simpa using hSd)
        · exact Or.inl rfl
      · exact cntF_le_of_mem _ _ ⟨hQδ, hDδ, by simp [h1]⟩
    rw [h3, hcnt] at hc
    have hsp := vcount_split (digSet Q D) (Cut3.dig (D := D) C').S
    have hv5 : scount (digSet Q D) (Cut3.dig (D := D) C').S true = 5 := hc
    have hdom : ∀ E : Ports (Cut3.dig (D := D) C').cont (hub (Cut3.dig (D := D) C').w), Dominant E :=
      fun E => hpole _ _ ((Cut3.dig (D := D) C').cont_inG hGd) (by rw [Cut3.vcount_cont]; omega)
        ((Cut3.dig (D := D) C').cont_2cr h2d) _ E
    -- the apex `y_i`
    have hmem : ∀ x, meets Q x → C'.S x = true → ∃ a, x = C'.y a := by
      intro x hx hsx
      exact C'.flip.sideB3 (by rw [Cut3.scount_flip3]; exact h3) hx (by simp [Cut3.flip_S, hsx])
    obtain ⟨i, hi⟩ := exists_apex hQ.1.1 C'.y C'.yinj
      (let ⟨a, ha⟩ := hmem _ (ends_meets1 hQδ) h1; ⟨a, ha⟩) (let ⟨a, ha⟩ := hmem _ (ends_meets2 hQδ) h2; ⟨a, ha⟩)
    have hT := hT1 Y Q hQ hc4 C' hcyc h3 D hn16 i δ hQδ hDδ h1 h2 hi huniq
    exact hTB Y Q hQ C' h3 D i δ hQδ hDδ h1 h2 hi huniq hdom hT
  set K := Cut3.dig (D := D) C with hK
  have hsplit := vcount_split (digSet Q D) K.S
  have hodd := cut3_odd hGd K
  by_cases ha : 9 ≤ scount (digSet Q D) K.S true
  · by_cases hb : 9 ≤ scount (digSet Q D) K.S false
    · -- both sides have at least 9 vertices: (POLE) on `V_S`, induction on `V_T`
      have hdom : Dominant K.hubPorts :=
        hpole _ K.flip.cont (K.flip.cont_inG hGd) (by rw [vcount_flip_cont]; omega) (K.flip.cont_2cr h2d) _ K.hubPorts
      have hW : EX1On K.cont := ih _ K.cont (K.cont_inG hGd) (by rw [Cut3.vcount_cont]; omega) (K.cont_2cr h2d)
        (by rw [Cut3.vcount_cont]; omega)
      exact K.brick hGd hdom hW
    · -- the side `V_T` is small
      have hb7 : scount (digSet Q D) K.S false ≤ 7 := by have := hodd false; omega
      rcases small_side3 hpole hPD ih hGd h2d h16 K.flip (by rw [Cut3.scount_flip3]; exact hb7) with h | hA
      · exact h
      · obtain ⟨hT3, δ, hQδ, hDδ, hδ1, hδ2, huniq⟩ := apexT hQ C hA
        have h5 : scount (digSet Q D) K.S false = 5 := by
          have := (apex_digon hQ.2.1 _ hA).1; rw [Cut3.scount_flip3] at this; exact this
        by_cases hk : ∃ j, D (C.e j)
        · -- a cut edge carries a digon: shift it to the side `V_T`
          obtain ⟨j, hj⟩ := hk
          obtain ⟨K3, hK3⟩ := exists_shift hQ C j hj
          have h7 : scount (digSet Q D) K3.flip.S true = 7 := by
            rw [Cut3.scount_flip3]; show scount (digSet Q D) K3.S false = 7
            rw [hK3]; show scount (digSet Q D) K.S false + 2 = 7; omega
          rcases small_side3 hpole hPD ih hGd h2d h16 K3.flip (by omega) with h | hA3
          · exact h
          · exfalso; have := (apex_digon hQ.2.1 _ hA3).1; omega
        · -- no cut edge carries a digon: the triangle `T` with its digon, seen from `C.flip`
          apply tri C.flip (cycSide_flip hS) (by rw [Cut3.scount_flip3]; exact hT3) δ hQδ hDδ
            (by simp [Cut3.flip_S, hδ1]) (by simp [Cut3.flip_S, hδ2])
          intro d hd hDd hSd
          simp only [Cut3.flip_S, Bool.not_eq_true'] at hSd
          by_cases hb1 : C.S (Y.ends d).1 = false
          · by_cases hb2 : C.S (Y.ends d).2 = false
            · exact huniq d hd hDd hb1 hb2
            · exfalso
              obtain ⟨j, rfl⟩ := C.cut d hd (by rw [hb1]; simpa using hb2)
              exact hk ⟨j, hDd⟩
          · have hb2 : C.S (Y.ends d).2 = false := hSd.resolve_left hb1
            exfalso
            obtain ⟨j, rfl⟩ := C.cut d hd (by rw [hb2]; simpa using hb1)
            exact hk ⟨j, hDd⟩
  · -- the side `V_S` is small
    have ha7 : scount (digSet Q D) K.S true ≤ 7 := by have := hodd true; omega
    rcases small_side3 hpole hPD ih hGd h2d h16 K ha7 with h | hA
    · exact h
    · obtain ⟨hS3, δ, hQδ, hDδ, hδ1, hδ2, huniq⟩ := apexS hQ C hA
      exact tri C hS hS3 δ hQδ hDδ hδ1 hδ2 huniq

end main

/-- **H-RED13 (c)** (fact da66a84c773b73b3) from the finite facts and Lemma TRI-BRICK-EX -/
theorem hred13c_of (hB12 : BASE12) (hS14 : SIMPLE14) (hB14 : B14D) (hSH : SMALLHOSTD) (hPD : SMALLPD)
    (hTB : TRIBRICKEX) : HRED13c := by
  intro hKD hpole hT1 X P
  generalize hn : vcount P = n
  induction n using Nat.strong_induction_on generalizing X P with
  | _ n ih =>
    intro hG h10 h2
    have hev := vcount_even' hG
    by_cases h14 : n ≤ 14
    · rcases (by omega : n = 10 ∨ n = 12 ∨ n = 14) with h | h | h
      · exact hB12 X P hG h2 (Or.inl (hn.trans h))
      · exact hB12 X P hG h2 (Or.inr (hn.trans h))
      · by_cases hs : SimpleP P
        · exact hS14 X P (inS_of_simple hG h2 hs) (hn.trans h)
        · exact hB14 X P hG h2 (hn.trans h) hs
    · obtain ⟨Y, Q, D, hQ, _, hvP, _, htr⟩ := hasm_converse hG h2 (by rw [hn]; exact h10)
      apply htr
      have hvd := vcount_dig hQ.1.1 (P := Q) (D := D)
      exact hred13_step hKD hpole hT1 hSH hPD hTB hQ (by omega)
        (fun X' P' hG' h10' h2' hlt => ih _ (by omega) X' P' rfl hG' h10' h2')

end RH2F

namespace RH2F
open MGraph

/-- **layer 21 of the Lean formalization**: H-RED13 (c) (fact da66a84c773b73b3) from the finite facts BASE12, SIMPLE14,
    B14-D, SMALLHOST-D, SMALL-PD (A) and Lemma TRI-BRICK-EX; hence the closing set CS2′ of the root (fact
    82aca6f992b64c00) with these facts in place of H-RED13 (c) -/
theorem layer21 :
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD → TRIBRICKEX → HRED13c) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD → TRIBRICKEX →
      FEEXTD10 → FEEXISTD10 → POLE → T1TRI → IID → DMS) :=
  ⟨hred13c_of, fun hB12 hS14 hB14 hSH hPD hTB hext hex hpole ht1 hD =>
    cs2p (hred13c_of hB12 hS14 hB14 hSH hPD hTB) hext hex hpole ht1 hD⟩

end RH2F
