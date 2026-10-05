-- Lean proof of fact 046773df0a672922 (RH2P.layerP); added by fact_submit, do not edit
import Mathlib.Combinatorics.SimpleGraph.Tutte
import MhFact_341b6e5e1be16205
/-
  Part (P) of fact f6e8c173bef4cfa1 in Lean 4.20 with Mathlib (SimpleGraph.tutte): every edge of a connected
  bridgeless loopless cubic multigraph lies in some perfect matching and outside some perfect matching
  (Schönberger 1934), and Theorem RH2 with this hypothesis discharged.
-/

namespace RH2P
open MGraph RH2F Finset
open Classical

section count
variable {X : MGraph}

/-- the number of `P`-edges at `x` -/
noncomputable def deg (P : Fin X.m → Prop) (x : Fin X.n) : Nat := (univ.filter (fun f => P f ∧ X.Inc f x)).card

/-- the number of `P`-edges with both ends in `K` -/
noncomputable def inside (P : Fin X.m → Prop) (K : Fin X.n → Prop) : Nat :=
  (univ.filter (fun f => P f ∧ K (X.ends f).1 ∧ K (X.ends f).2)).card

/-- the number of `P`-edges with exactly one end in `K` -/
noncomputable def cross (P : Fin X.m → Prop) (K : Fin X.n → Prop) : Nat :=
  (univ.filter (fun f => P f ∧ ¬ (K (X.ends f).1 ↔ K (X.ends f).2))).card

theorem deg_cubic {P : Fin X.m → Prop} (hc : CubicOn P) {x : Fin X.n} (hx : ∃ f, P f ∧ X.Inc f x) :
    deg P x = 3 := by
  obtain ⟨a, b, c, ha, hb, hc', hax, hbx, hcx, hab, hac, hbc, hall⟩ := hc x hx
  have : univ.filter (fun f => P f ∧ X.Inc f x) = {a, b, c} := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hf, hfx⟩; exact hall f hf hfx
    · rintro (rfl | rfl | rfl)
      · exact ⟨ha, hax⟩
      · exact ⟨hb, hbx⟩
      · exact ⟨hc', hcx⟩
  rw [deg, this, card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
    card_singleton]

/-- the number of ends of `f` in `K` -/
theorem ends_in (hloop : Loopless X) (K : Fin X.n → Prop) (f : Fin X.m) :
    (univ.filter (fun x => K x ∧ X.Inc f x)).card =
      (if K (X.ends f).1 then 1 else 0) + (if K (X.ends f).2 then 1 else 0) := by
  have hne := hloop f
  by_cases h1 : K (X.ends f).1 <;> by_cases h2 : K (X.ends f).2
  · have : univ.filter (fun x => K x ∧ X.Inc f x) = {(X.ends f).1, (X.ends f).2} := by
      ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]; simp only [MGraph.Inc]
      constructor
      · rintro ⟨_, h | h⟩ <;> simp [h]
      · rintro (rfl | rfl) <;> simp_all
    rw [this, card_insert_of_notMem (by simpa using hne)]; simp [h1, h2]
  · have : univ.filter (fun x => K x ∧ X.Inc f x) = {(X.ends f).1} := by
      ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]; simp only [MGraph.Inc]
      constructor
      · rintro ⟨hk, h | h⟩
        · exact h.symm
        · subst h; exact absurd hk h2
      · rintro rfl; exact ⟨h1, Or.inl rfl⟩
    rw [this]; simp [h1, h2]
  · have : univ.filter (fun x => K x ∧ X.Inc f x) = {(X.ends f).2} := by
      ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]; simp only [MGraph.Inc]
      constructor
      · rintro ⟨hk, h | h⟩
        · subst h; exact absurd hk h1
        · exact h.symm
      · rintro rfl; exact ⟨h2, Or.inr rfl⟩
    rw [this]; simp [h1, h2]
  · have : univ.filter (fun x => K x ∧ X.Inc f x) = ∅ := by
      ext x; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]; simp only [MGraph.Inc]
      rintro ⟨hk, h | h⟩
      · subst h; exact h1 hk
      · subst h; exact h2 hk
    rw [this]; simp [h1, h2]

/-- the degree sum over a vertex set `K` -/
theorem deg_sum (hloop : Loopless X) (P : Fin X.m → Prop) (K : Fin X.n → Prop) :
    ∑ x ∈ univ.filter K, deg P x = 2 * inside P K + cross P K := by
  have step1 : ∑ x ∈ univ.filter K, deg P x =
      ∑ f : Fin X.m, if P f then (univ.filter (fun x => K x ∧ X.Inc f x)).card else 0 := by
    unfold deg
    simp only [card_filter]
    rw [Finset.sum_comm' (t' := univ) (s' := fun _ => univ.filter K)]
    · apply Finset.sum_congr rfl
      intro f _
      by_cases hf : P f
      · simp only [hf, true_and, if_true]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        simp only [ite_and]
      · simp [hf]
    · intro x f; simp
  rw [step1]
  simp_rw [ends_in hloop K]
  unfold inside cross
  simp only [card_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : P f <;> by_cases h1 : K (X.ends f).1 <;> by_cases h2 : K (X.ends f).2 <;> simp [hf, h1, h2]

end count

section schoen
variable {X : MGraph} {P : Fin X.m → Prop}

/-- `v` meets `P` -/
def mt (P : Fin X.m → Prop) (v : Fin X.n) : Prop := ∃ f, P f ∧ X.Inc f v

/-- the vertices of `P` other than `u` and `w` -/
abbrev VT (P : Fin X.m → Prop) (u w : Fin X.n) := {v : Fin X.n // mt P v ∧ v ≠ u ∧ v ≠ w}

/-- the underlying simple graph of `P` on the vertices other than `u`, `w` -/
def GT (P : Fin X.m → Prop) (u w : Fin X.n) : SimpleGraph (VT P u w) where
  Adj a b := a ≠ b ∧ ∃ f, P f ∧ X.Joins f a.1 b.1
  symm := ⟨fun _ _ ⟨h1, f, hf, hj⟩ => ⟨h1.symm, f, hf, Or.symm hj⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {u w : Fin X.n} {U : Set (VT P u w)}

/-- the graph `GT − U` of Tutte's condition -/
abbrev HG (P : Fin X.m → Prop) (u w : Fin X.n) (U : Set (VT P u w)) :=
  ((⊤ : (GT P u w).Subgraph).deleteVerts U).coe

theorem memW (b : VT P u w) : b ∈ ((⊤ : (GT P u w).Subgraph).deleteVerts U).verts ↔ b ∉ U := by
  simp [SimpleGraph.Subgraph.deleteVerts_verts]

theorem adjH (a b : ((⊤ : (GT P u w).Subgraph).deleteVerts U).verts) :
    (HG P u w U).Adj a b ↔ (GT P u w).Adj a.1 b.1 := by
  have ha := (memW a.1).1 a.2
  have hb := (memW b.1).1 b.2
  simp [SimpleGraph.Subgraph.deleteVerts_adj, ha, hb]

/-- the vertices of `X` in the component `c` -/
def KX (c : (HG P u w U).ConnectedComponent) (x : Fin X.n) : Prop :=
  ∃ a, (HG P u w U).connectedComponentMk a = c ∧ a.1.1 = x

theorem kx_props {c : (HG P u w U).ConnectedComponent} {x : Fin X.n} (h : KX c x) :
    mt P x ∧ x ≠ u ∧ x ≠ w ∧ ∀ b : VT P u w, b.1 = x → b ∉ U := by
  obtain ⟨a, _, rfl⟩ := h
  refine ⟨a.1.2.1, a.1.2.2.1, a.1.2.2.2, fun b hb => ?_⟩
  have : b = a.1 := Subtype.ext hb
  rw [this]; exact (memW a.1).1 a.2

theorem kx_unique {c c' : (HG P u w U).ConnectedComponent} {x : Fin X.n} (h : KX c x) (h' : KX c' x) :
    c = c' := by
  obtain ⟨a, rfl, hx⟩ := h
  obtain ⟨a', rfl, hx'⟩ := h'
  have : a = a' := Subtype.ext (Subtype.ext (hx.trans hx'.symm))
  rw [this]

theorem kx_close (hloop : Loopless X) {c : (HG P u w U).ConnectedComponent} {x y : Fin X.n} {f : Fin X.m}
    (h : KX c x) (hf : P f) (hj : X.Joins f x y) :
    y = u ∨ y = w ∨ (∃ b : VT P u w, b.1 = y ∧ b ∈ U) ∨ KX c y := by
  by_cases hyu : y = u
  · exact Or.inl hyu
  by_cases hyw : y = w
  · exact Or.inr (Or.inl hyw)
  let b : VT P u w := ⟨y, ⟨f, hf, joins_inc_right hj⟩, hyu, hyw⟩
  by_cases hbU : b ∈ U
  · exact Or.inr (Or.inr (Or.inl ⟨b, rfl, hbU⟩))
  refine Or.inr (Or.inr (Or.inr ?_))
  obtain ⟨a, hac, rfl⟩ := h
  let b' : ((⊤ : (GT P u w).Subgraph).deleteVerts U).verts := ⟨b, (memW b).2 hbU⟩
  have hadj : (HG P u w U).Adj a b' := by
    rw [adjH]
    refine ⟨fun hab => ?_, f, hf, hj⟩
    have : a.1.1 = y := congrArg Subtype.val hab
    exact ne_of_joins hloop hj this
  refine ⟨b', ?_, rfl⟩
  rw [← hac]
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm


/-- the set `S′ = U ∪ {u, w}` as vertices of `X` -/
def SP (U : Set (VT P u w)) (u w : Fin X.n) (x : Fin X.n) : Prop := x = u ∨ x = w ∨ ∃ b ∈ U, b.1 = x

/-- the end of a crossing edge in the component is outside `S′`, the other end inside -/
theorem cross_ends (hloop : Loopless X) {c : (HG P u w U).ConnectedComponent} {f : Fin X.m} (hf : P f)
    {a b : Fin X.n} (hj : X.Joins f a b) (ha : KX c a) (hb : ¬ KX c b) : ¬ SP U u w a ∧ SP U u w b := by
  have hp := kx_props ha
  refine ⟨?_, ?_⟩
  · rintro (h | h | ⟨b', hb', h⟩)
    · exact hp.2.1 h
    · exact hp.2.2.1 h
    · exact hp.2.2.2 b' h hb'
  · rcases kx_close hloop ha hf hj with h | h | ⟨b', h1, h2⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨b', h2, h1⟩)
    · exact absurd h hb

theorem cross_sub (hloop : Loopless X) (c : (HG P u w U).ConnectedComponent) (f : Fin X.m)
    (h : P f ∧ ¬ (KX c (X.ends f).1 ↔ KX c (X.ends f).2)) :
    P f ∧ ¬ (SP U u w (X.ends f).1 ↔ SP U u w (X.ends f).2) := by
  refine ⟨h.1, ?_⟩
  by_cases h1 : KX c (X.ends f).1
  · have h2 : ¬ KX c (X.ends f).2 := fun h2 => h.2 ⟨fun _ => h2, fun _ => h1⟩
    have := cross_ends hloop h.1 (joins_ends f) h1 h2
    exact fun hi => this.1 (hi.2 this.2)
  · have h2 : KX c (X.ends f).2 := by
      by_contra h2; exact h.2 ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
    have := cross_ends hloop h.1 (Or.symm (joins_ends f)) h2 h1
    exact fun hi => this.1 (hi.1 this.2)

theorem cross_disj (hloop : Loopless X) {c c' : (HG P u w U).ConnectedComponent} {f : Fin X.m}
    (h : P f ∧ ¬ (KX c (X.ends f).1 ↔ KX c (X.ends f).2))
    (h' : P f ∧ ¬ (KX c' (X.ends f).1 ↔ KX c' (X.ends f).2)) : c = c' := by
  -- the end of `f` outside `S′` lies in both components
  have key : ∀ (d : (HG P u w U).ConnectedComponent), (P f ∧ ¬ (KX d (X.ends f).1 ↔ KX d (X.ends f).2)) →
      (KX d (X.ends f).1 ∧ ¬ SP U u w (X.ends f).1 ∧ SP U u w (X.ends f).2) ∨
      (KX d (X.ends f).2 ∧ ¬ SP U u w (X.ends f).2 ∧ SP U u w (X.ends f).1) := by
    intro d hd
    by_cases h1 : KX d (X.ends f).1
    · have h2 : ¬ KX d (X.ends f).2 := fun h2 => hd.2 ⟨fun _ => h2, fun _ => h1⟩
      exact Or.inl ⟨h1, cross_ends hloop hd.1 (joins_ends f) h1 h2⟩
    · have h2 : KX d (X.ends f).2 := by
        by_contra h2; exact hd.2 ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
      exact Or.inr ⟨h2, cross_ends hloop hd.1 (Or.symm (joins_ends f)) h2 h1⟩
  rcases key c h with ⟨k1, s1, s2⟩ | ⟨k1, s1, s2⟩ <;> rcases key c' h' with ⟨k1', s1', s2'⟩ | ⟨k1', s1', s2'⟩
  · exact kx_unique k1 k1'
  · exact absurd s2 s1'
  · exact absurd s2 s1'
  · exact kx_unique k1 k1'

/-- the vertices of a component, counted in `X` -/
theorem kx_card (c : (HG P u w U).ConnectedComponent) :
    (univ.filter (KX c)).card = c.supp.ncard := by
  rw [Set.ncard_eq_toFinset_card']
  let emb : ((⊤ : (GT P u w).Subgraph).deleteVerts U).verts ↪ Fin X.n :=
    ⟨fun a => a.1.1, fun a a' h => Subtype.ext (Subtype.ext h)⟩
  have : univ.filter (KX c) = c.supp.toFinset.map emb := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_map, Set.mem_toFinset,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  rw [this, card_map]


/-- a component of `GT − U` sends an odd number of edges out when it has an odd number of vertices -/
theorem cross_odd (hG : InG X P) (c : (HG P u w U).ConnectedComponent) (hodd : Odd c.supp.ncard) :
    Odd (cross P (KX c)) := by
  have hs := deg_sum hG.1 P (KX c)
  have h3 : ∑ x ∈ univ.filter (KX c), deg P x = 3 * c.supp.ncard := by
    rw [← kx_card c, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mem_filter] at hx
    rw [deg_cubic hG.2.2.2 (kx_props hx.2).1]
    rfl
  rw [h3] at hs
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at hs
  refine ⟨3 * k + 1 - inside P (KX c), ?_⟩
  omega

/-- no component of `GT − U` sends exactly one edge out (bridgeless) -/
theorem cross_ne_one (hG : InG X P) (c : (HG P u w U).ConnectedComponent) : cross P (KX c) ≠ 1 := by
  intro h1
  obtain ⟨f, hf⟩ := Finset.card_eq_one.1 h1
  have hfm : f ∈ univ.filter (fun f => P f ∧ ¬ (KX c (X.ends f).1 ↔ KX c (X.ends f).2)) := by
    rw [hf]; exact mem_singleton_self f
  rw [mem_filter] at hfm
  have hPf := hfm.2.1
  have only : ∀ g, P g → g ≠ f → (KX c (X.ends g).1 ↔ KX c (X.ends g).2) := by
    intro g hg hne
    by_contra hc
    have : g ∈ univ.filter (fun f => P f ∧ ¬ (KX c (X.ends f).1 ↔ KX c (X.ends f).2)) := by
      rw [mem_filter]; exact ⟨mem_univ g, hg, hc⟩
    rw [hf, mem_singleton] at this
    exact hne this
  by_cases h1 : KX c (X.ends f).1
  · have h2 : ¬ KX c (X.ends f).2 := fun h2 => hfm.2.2 ⟨fun _ => h2, fun _ => h1⟩
    refine hG.2.2.1 f hPf ⟨fun x => decide (KX c x), by simp [h1], by simp [h2], fun g hg hne => ?_⟩
    exact decide_eq_decide.2 (only g hg hne)
  · have h2 : KX c (X.ends f).2 := by
      by_contra h2'; exact hfm.2.2 ⟨fun h' => absurd h' h1, fun h' => absurd h' h2'⟩
    refine hG.2.2.1 f hPf ⟨fun x => !decide (KX c x), by simp [h1], by simp [h2], fun g hg hne => ?_⟩
    show (!decide (KX c (X.ends g).1)) = (!decide (KX c (X.ends g).2))
    rw [decide_eq_decide.2 (only g hg hne)]

/-- every component of `GT − U` sends some edge out (connected, and `h = uw` lies outside) -/
theorem cross_ne_zero (hG : InG X P) {h : Fin X.m} (hh : P h) (hu : (X.ends h).1 = u)
    (c : (HG P u w U).ConnectedComponent) : cross P (KX c) ≠ 0 := by
  intro h0
  have none : ∀ g, P g → (KX c (X.ends g).1 ↔ KX c (X.ends g).2) := by
    intro g hg
    by_contra hc
    have : g ∈ univ.filter (fun f => P f ∧ ¬ (KX c (X.ends f).1 ↔ KX c (X.ends f).2)) := by
      rw [mem_filter]; exact ⟨mem_univ g, hg, hc⟩
    rw [cross, Finset.card_eq_zero] at h0
    rw [h0] at this
    exact Finset.notMem_empty g this
  obtain ⟨a, ha⟩ := c.exists_rep
  have hxa : KX c a.1.1 := ⟨a, ha, rfl⟩
  obtain ⟨f1, hf1, hinc⟩ := a.1.2.1
  have hcon := hG.2.1 (fun x => decide (KX c x)) (fun g hg => decide_eq_decide.2 (none g hg)) f1 h hf1 hh
  have hu' : ¬ KX c (X.ends h).1 := fun hk => (kx_props hk).2.1 hu
  have hf1' : KX c (X.ends f1).1 := by
    rcases hinc with h1 | h1
    · rw [h1]; exact hxa
    · exact (none f1 hf1).2 (h1 ▸ hxa)
  simp [hf1', hu'] at hcon

theorem three_le_cross (hG : InG X P) {h : Fin X.m} (hh : P h) (hu : (X.ends h).1 = u)
    (c : (HG P u w U).ConnectedComponent) (hodd : Odd c.supp.ncard) : 3 ≤ cross P (KX c) := by
  have h1 := cross_odd hG c hodd
  have h2 := cross_ne_one hG c
  have h3 := cross_ne_zero hG hh hu c
  obtain ⟨k, hk⟩ := h1
  omega


theorem sp_card (huw : u ≠ w) : (univ.filter (SP U u w)).card = U.ncard + 2 := by
  let emb : VT P u w ↪ Fin X.n := ⟨Subtype.val, Subtype.val_injective⟩
  have hU : u ∉ U.toFinset.map emb := by
    simp only [mem_map, Set.mem_toFinset, not_exists, not_and]
    intro b _ hb; exact b.2.2.1 hb
  have hW : w ∉ U.toFinset.map emb := by
    simp only [mem_map, Set.mem_toFinset, not_exists, not_and]
    intro b _ hb; exact b.2.2.2 hb
  have : univ.filter (SP U u w) = insert u (insert w (U.toFinset.map emb)) := by
    ext x
    simp only [SP, mem_filter, mem_univ, true_and, mem_insert, mem_map, Set.mem_toFinset]
    constructor
    · rintro (h | h | ⟨b, hb, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨b, hb, h⟩)
    · rintro (h | h | ⟨b, hb, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨b, hb, h⟩)
  rw [this, card_insert_of_notMem (by simp only [mem_insert, not_or]; exact ⟨huw, hU⟩),
    card_insert_of_notMem hW, card_map, Set.ncard_eq_toFinset_card']

theorem cross_sp (hG : InG X P) {h : Fin X.m} (hh : P h) (hu : (X.ends h).1 = u) (hw : (X.ends h).2 = w) :
    cross P (SP U u w) + 2 ≤ 3 * (U.ncard + 2) := by
  have huw : u ≠ w := by rw [← hu, ← hw]; exact hG.1 h
  have hs := deg_sum hG.1 P (SP U u w)
  have h3 : ∑ x ∈ univ.filter (SP U u w), deg P x = 3 * (U.ncard + 2) := by
    rw [← sp_card huw, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mem_filter] at hx
    have hm : ∃ f, P f ∧ X.Inc f x := by
      rcases hx.2 with h1 | h1 | ⟨b, _, h1⟩
      · exact ⟨h, hh, Or.inl (hu.trans h1.symm)⟩
      · exact ⟨h, hh, Or.inr (hw.trans h1.symm)⟩
      · exact h1 ▸ b.2.1
    rw [deg_cubic hG.2.2.2 hm]
    rfl
  have hin : 1 ≤ inside P (SP U u w) := by
    apply Finset.card_pos.2
    exact ⟨h, mem_filter.2 ⟨mem_univ h, hh, Or.inl hu, Or.inr (Or.inl hw)⟩⟩
  omega

/-- the vertices of `P` are even in number -/
theorem mt_even (hG : InG X P) : (univ.filter (mt P)).card % 2 = 0 := by
  have hs := deg_sum hG.1 P (mt P)
  have h3 : ∑ x ∈ univ.filter (mt P), deg P x = 3 * (univ.filter (mt P)).card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mem_filter] at hx
    rw [deg_cubic hG.2.2.2 hx.2]
    rfl
  have h0 : cross P (mt P) = 0 := by
    rw [cross, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f _ hf
    exact hf.2 ⟨fun _ => ⟨f, hf.1, Or.inr rfl⟩, fun _ => ⟨f, hf.1, Or.inl rfl⟩⟩
  omega

theorem vt_card (hG : InG X P) {h : Fin X.m} (hh : P h) (hu : (X.ends h).1 = u) (hw : (X.ends h).2 = w) :
    Nat.card (VT P u w) + 2 = (univ.filter (mt P)).card := by
  have huw : u ≠ w := by rw [← hu, ← hw]; exact hG.1 h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmu : mt P u := ⟨h, hh, Or.inl hu⟩
  have hmw : mt P w := ⟨h, hh, Or.inr hw⟩
  have : univ.filter (mt P) = insert u (insert w (univ.filter (fun v => mt P v ∧ v ≠ u ∧ v ≠ w))) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hx
      by_cases h1 : x = u
      · exact Or.inl h1
      by_cases h2 : x = w
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr ⟨hx, h1, h2⟩)
    · rintro (rfl | rfl | ⟨hx, _, _⟩)
      · exact hmu
      · exact hmw
      · exact hx
  rw [this, card_insert_of_notMem (by simp [huw]), card_insert_of_notMem (by simp)]

/-- **Tutte's condition** for `GT P u w`, where `u w` is an edge of the bridgeless cubic `P` -/
theorem not_violator (hG : InG X P) {h : Fin X.m} (hh : P h) (hu : (X.ends h).1 = u) (hw : (X.ends h).2 = w)
    (U : Set (VT P u w)) : ¬ (GT P u w).IsTutteViolator U := by
  unfold SimpleGraph.IsTutteViolator
  rw [not_lt]
  change (HG P u w U).oddComponents.ncard ≤ U.ncard
  -- the counting bound
  have hsum : ∑ c ∈ (HG P u w U).oddComponents.toFinset, cross P (KX c) ≤ cross P (SP U u w) := by
    unfold cross
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      intro f hf
      rw [Finset.mem_biUnion] at hf
      obtain ⟨c, _, hfc⟩ := hf
      rw [mem_filter] at hfc ⊢
      exact ⟨mem_univ f, cross_sub hG.1 c f hfc.2⟩
    · intro c _ c' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro f hf hf'
      rw [mem_filter] at hf hf'
      exact hne (cross_disj hG.1 hf.2 hf'.2)
  have h3 : 3 * (HG P u w U).oddComponents.ncard ≤
      ∑ c ∈ (HG P u w U).oddComponents.toFinset, cross P (KX c) := by
    rw [Set.ncard_eq_toFinset_card', Nat.mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro c hc
    rw [Set.mem_toFinset] at hc
    exact three_le_cross hG hh hu c hc
  have hsp := cross_sp (U := U) hG hh hu hw
  -- parity
  have hpar := (HG P u w U).odd_ncard_oddComponents
  have hW : Nat.card ((⊤ : (GT P u w).Subgraph).deleteVerts U).verts + U.ncard = Nat.card (VT P u w) := by
    rw [Nat.card_coe_set_eq, SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.ncard_diff_add_ncard_of_subset (Set.subset_univ U), Set.ncard_univ]
  have hV := vt_card hG hh hu hw
  have hE := mt_even hG
  rcases Nat.even_or_odd (HG P u w U).oddComponents.ncard with ⟨k, hk⟩ | ho
  · -- even: then `Nat.card` of the vertex set is even, so `|U|` is even
    have hne : ¬ Odd (Nat.card ((⊤ : (GT P u w).Subgraph).deleteVerts U).verts) := by
      rw [← hpar]; rintro ⟨j, hj⟩; omega
    rw [Nat.not_odd_iff_even] at hne
    obtain ⟨j, hj⟩ := hne
    omega
  · have ho' := hpar.1 ho
    obtain ⟨j, hj⟩ := ho'
    obtain ⟨k, hk⟩ := ho
    omega


/-- the `P`-edges joining `a` and `b` -/
noncomputable def jn (P : Fin X.m → Prop) (a b : Fin X.n) : Finset (Fin X.m) :=
  univ.filter (fun f => P f ∧ X.Joins f a b)

theorem jn_symm (a b : Fin X.n) : jn P a b = jn P b a := by
  ext f; simp only [jn, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, Or.symm h2⟩, fun ⟨h1, h2⟩ => ⟨h1, Or.symm h2⟩⟩

theorem min'_eq_of {s t : Finset (Fin X.m)} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst hst; rfl

/-- **Schönberger's theorem**: every edge of a connected bridgeless loopless cubic multigraph lies in a perfect
    matching. -/
theorem schoenberger (hG : InG X P) {h : Fin X.m} (hh : P h) : ∃ N, PMOn P N ∧ N h := by
  obtain ⟨M, hM⟩ := (SimpleGraph.tutte (G := GT P (X.ends h).1 (X.ends h).2)).2
    (fun U => not_violator hG hh rfl rfl U)
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  have huw : (X.ends h).1 ≠ (X.ends h).2 := hG.1 h
  -- the matching `N`: `h`, and for each matched pair the `P`-edge of least index joining it
  let N : Fin X.m → Prop := fun f => f = h ∨
    ∃ a b : VT P (X.ends h).1 (X.ends h).2, M.Adj a b ∧ ∃ hne : (jn P a.1 b.1).Nonempty,
      f = (jn P a.1 b.1).min' hne
  refine ⟨N, ⟨?_, ?_⟩, Or.inl rfl⟩
  · rintro f (rfl | ⟨a, b, _, hne, rfl⟩)
    · exact hh
    · have := Finset.min'_mem _ hne
      exact (mem_filter.1 this).2.1
  · intro x hx
    by_cases hxu : x = (X.ends h).1 ∨ x = (X.ends h).2
    · refine ⟨h, Or.inl rfl, ?_, ?_⟩
      · rcases hxu with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro d (rfl | ⟨a, b, _, hne, rfl⟩) hdx
        · rfl
        · exfalso
          have hj := (mem_filter.1 (Finset.min'_mem _ hne)).2.2
          rcases inc_of_joins hj hdx with h1 | h1
          · rcases hxu with h2 | h2
            · exact a.2.2.1 (h1 ▸ h2)
            · exact a.2.2.2 (h1 ▸ h2)
          · rcases hxu with h2 | h2
            · exact b.2.2.1 (h1 ▸ h2)
            · exact b.2.2.2 (h1 ▸ h2)
    · push_neg at hxu
      let a : VT P (X.ends h).1 (X.ends h).2 := ⟨x, hx, hxu.1, hxu.2⟩
      obtain ⟨b, hab, huniq⟩ := hM a
      have hG' : (GT P (X.ends h).1 (X.ends h).2).Adj a b := M.adj_sub hab
      obtain ⟨_, f0, hf0, hj0⟩ := hG'
      have hne : (jn P a.1 b.1).Nonempty := ⟨f0, mem_filter.2 ⟨mem_univ _, hf0, hj0⟩⟩
      refine ⟨(jn P a.1 b.1).min' hne, Or.inr ⟨a, b, hab, hne, rfl⟩, ?_, ?_⟩
      · exact joins_inc_left (mem_filter.1 (Finset.min'_mem _ hne)).2.2
      · rintro d (rfl | ⟨a', b', hab', hne', rfl⟩) hdx
        · exfalso
          rcases hdx with h1 | h1
          · exact hxu.1 h1.symm
          · exact hxu.2 h1.symm
        · have hj := (mem_filter.1 (Finset.min'_mem _ hne')).2.2
          rcases inc_of_joins hj hdx with h1 | h1
          · -- `x = a'`
            have ha' : a' = a := Subtype.ext h1.symm
            have hb' : b' = b := huniq b' (ha' ▸ hab')
            exact min'_eq_of (by rw [ha', hb']) _ _
          · -- `x = b'`
            have hb' : b' = a := Subtype.ext h1.symm
            have ha' : a' = b := huniq a' (hb' ▸ hab'.symm)
            exact min'_eq_of (by rw [ha', hb', jn_symm]) _ _


end schoen

/-- **Part (P) of fact f6e8c173bef4cfa1** (Petersen–Schönberger): in a connected bridgeless loopless cubic multigraph
    every edge lies in some perfect matching and outside some perfect matching. -/
theorem pstat : PStat := by
  intro X P hG h hh t
  cases t
  · obtain ⟨a, b, _, ha, hb, _, hax, hbx, _, hab, _, _, _⟩ := hG.2.2.2 (X.ends h).1 ⟨h, hh, Or.inl rfl⟩
    have : ∃ h', P h' ∧ X.Inc h' (X.ends h).1 ∧ h' ≠ h := by
      by_cases hah : a = h
      · exact ⟨b, hb, hbx, fun e => hab (hah.trans e.symm)⟩
      · exact ⟨a, ha, hax, hah⟩
    obtain ⟨h', hh', hinc, hne⟩ := this
    obtain ⟨N, hN, hN'⟩ := schoenberger hG hh'
    refine ⟨N, hN, ?_⟩
    simp only [Bool.false_eq_true, iff_false]
    intro hNh
    obtain ⟨e, _, _, huniq⟩ := hN.2 (X.ends h).1 ⟨h, hh, Or.inl rfl⟩
    exact hne ((huniq h' hN' hinc).trans (huniq h hNh (Or.inl rfl)).symm)
  · obtain ⟨N, hN, hNh⟩ := schoenberger hG hh
    exact ⟨N, hN, by simp [hNh]⟩

/-- **Theorem RH2** (fact 6bfcd4d52c94468a) with part (P) discharged: (H) and (II) imply DMS, given the small-side
    facts of EX1-RED and Theorem B8. -/
theorem rh2_P : RH2F.SmallFacts → RH2F.B8S → RH2F.Hyp → RH2F.II → RH2F.DMS := RH2F.rh2 pstat

/-- the fact: part (P) and RH2 without it -/
theorem layerP : RH2F.PStat ∧ (RH2F.SmallFacts → RH2F.B8S → RH2F.Hyp → RH2F.II → RH2F.DMS) :=
  ⟨pstat, rh2_P⟩

end RH2P
