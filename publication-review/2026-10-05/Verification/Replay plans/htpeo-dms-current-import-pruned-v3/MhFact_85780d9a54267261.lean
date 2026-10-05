-- Lean proof of fact 85780d9a54267261 (RH2F.layer25); added by fact_submit, do not edit
import MhFact_83263f8970f3987b
set_option backward.isDefEq.respectTransparency false


/-
  TE1.lean — gluing two pole colourings across a 3-edge-cut (3CUT-MULTI (A-M) with the MC condition), and the
  translation of `Col`/`Blk` of the pole side `A` of a cut to the hub pole.
-/

namespace RH2F
open MGraph
open Classical

section gluep
variable {X : MGraph} {P : Fin X.m → Prop}

/-- **gluing two pole colourings**: star colourings of the two poles of a 3-edge-cut, equal on the cut edges,
    with empty triple intersections, each with exactly one colour-`6` edge at every vertex of its side, give an MC
    colouring -/
theorem glue_poles (C : Cut3 P) (φ ψ : Fin X.m → Fin 6) (hφ : StarOn C.pole 6 φ) (hψ : StarOn C.flip.pole 6 ψ)
    (hcut : ∀ t, φ (C.e t) = ψ (C.e t))
    (htri : ∀ i κ, C.Col φ i κ → C.flip.Col ψ i κ → (C.Blk φ i κ ∨ C.flip.Blk ψ i κ) → False)
    (hφA : ∀ x, C.S x = true → meets P x →
      ∃ a, C.pole a ∧ X.Inc a x ∧ φ a = 5 ∧ ∀ b, C.pole b → X.Inc b x → φ b = 5 → b = a)
    (hψB : ∀ x, C.S x = false → meets P x →
      ∃ a, C.flip.pole a ∧ X.Inc a x ∧ ψ a = 5 ∧ ∀ b, C.flip.pole b → X.Inc b x → ψ b = 5 → b = a) :
    ∃ c, MCol P c ∧ (∀ f, C.pole f → c f = φ f) ∧ (∀ f, C.flip.pole f → c f = ψ f) := by
  let c : Fin X.m → Fin 6 := fun f => if C.inA f then φ f else ψ f
  have hcφ : ∀ f, C.pole f → c f = φ f := by
    intro f hf
    by_cases h : C.inA f
    · simp only [c, if_pos h]
    · simp only [c, if_neg h]
      obtain ⟨t, rfl⟩ := hf.resolve_left h
      exact (hcut t).symm
  have hcψ : ∀ f, C.flip.pole f → c f = ψ f := by
    intro f hf
    have : ¬ C.inA f := by
      rcases hf with h | ⟨t, ht⟩
      · exact fun h' => C.not_flip_of_inA h' h
      · exact C.not_inA_of_cut ⟨t, ht⟩
    simp only [c, if_neg this]
  refine ⟨c, ⟨C.glue3 φ ψ c hφ hψ hcφ hcψ htri, fun x hx => ?_⟩, hcφ, hcψ⟩
  obtain ⟨f0, hf0, hf0x⟩ := hx
  cases hs : C.S x
  · have hs' : C.flip.S x = true := by rw [Cut3.flip_S, hs]; rfl
    obtain ⟨a, ha, hax, ha5, hau⟩ := hψB x hs ⟨f0, hf0, hf0x⟩
    refine ⟨a, C.flip.pole_P ha, hax, by rw [hcψ a ha]; exact ha5, fun b hb hbx hb5 => ?_⟩
    have hbp := C.flip.pole_of_inc hb hbx hs'
    exact hau b hbp hbx (by rw [← hcψ b hbp]; exact hb5)
  · obtain ⟨a, ha, hax, ha5, hau⟩ := hφA x hs ⟨f0, hf0, hf0x⟩
    refine ⟨a, C.pole_P ha, hax, by rw [hcφ a ha]; exact ha5, fun b hb hbx hb5 => ?_⟩
    have hbp := C.pole_of_inc hb hbx hs
    exact hau b hbp hbx (by rw [← hcφ b hbp]; exact hb5)

namespace Cut3
variable (C : Cut3 P)

/-- `Col` of the pole side `A` is `Col` of the hub pole -/
theorem col_hub {d : Fin (addHub X C.flip.w).m → Fin 6} {t : Fin 3} {κ : Fin 6}
    (h : C.Col (fun f => d (C.flip.toCont f)) t κ) : vCol C.hubPorts d t κ := by
  have incA : ∀ {f : Fin X.m} {x : Fin X.n}, C.pole f → X.Inc f x → C.S x = true →
      (splitV C.hubPorts).Inc (C.flip.toCont f) (Fin.castAdd 3 (hv C.flip.w x)) := by
    intro f x hf hfx hx
    have hj := C.pole_joins hf
    rw [← C.toPV_A hx]
    rcases hfx with h | h <;> rw [← h]
    · exact joins_inc_left hj
    · exact joins_inc_right hj
  obtain ⟨f, hf, hfy, hfc⟩ := h
  refine ⟨C.flip.toCont f, C.pole_mem (Or.inl hf), ?_, ?_, hfc⟩
  · rw [C.flipToCont_inA hf, C.hubPorts_p]; exact hOld_ne_hNew _ _ _
  · rw [C.hubPorts_x]; exact incA (Or.inl hf) hfy (C.sy t)

/-- `Blk` of the pole side `A` is `Blk` of the hub pole -/
theorem blk_hub {d : Fin (addHub X C.flip.w).m → Fin 6} {t : Fin 3} {κ : Fin 6}
    (h : C.Blk (fun f => d (C.flip.toCont f)) t κ) : vBlk C.hubPorts d t κ := by
  have inj : ∀ f g, C.flip.toCont f = C.flip.toCont g → f = g := fun f g h => C.flip.toCont_inj h
  have incA : ∀ {f : Fin X.m} {x : Fin X.n}, C.pole f → X.Inc f x → C.S x = true →
      (splitV C.hubPorts).Inc (C.flip.toCont f) (Fin.castAdd 3 (hv C.flip.w x)) := by
    intro f x hf hfx hx
    have hj := C.pole_joins hf
    rw [← C.toPV_A hx]
    rcases hfx with h | h <;> rw [← h]
    · exact joins_inc_left hj
    · exact joins_inc_right hj
  obtain ⟨f, r, hf, hjr, hfc, f', hf'p, hf'f, hf'r, hf'c⟩ := h
  have hrA : C.S r = true := C.side_of_inA hf (joins_inc_right hjr)
  have hjf := C.pole_joins (Or.inl hf)
  refine ⟨C.flip.toCont f, C.toPV r, C.pole_mem (Or.inl hf), ?_, ?_, hfc, C.flip.toCont f',
    C.pole_mem hf'p, fun h => hf'f (inj _ _ h), ?_, ?_⟩
  · rw [C.flipToCont_inA hf, C.hubPorts_p]; exact hOld_ne_hNew _ _ _
  · rcases joins_unique hjr (joins_ends f) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [C.hubPorts_x, ← C.toPV_A (C.sy t), h1, h2]; exact hjf
    · rw [C.hubPorts_x, ← C.toPV_A (C.sy t), h1, h2]; exact Or.symm hjf
  · rw [C.toPV_A hrA]; exact incA hf'p hf'r hrA
  · rw [C.hubPorts_p]; show d (C.flip.toCont f') = d (hNew C.flip.w t)
    rw [← C.flipToCont_e]; exact hf'c

/-- the pole colouring read on side `A`: star, MC on side `A`, port colours (the datum-free part of `pole_of_D1`) -/
theorem pole_side {d : Fin (addHub X C.flip.w).m → Fin 6} (hd : MCPole C.hubPorts d) :
    StarOn C.pole 6 (fun f => d (C.flip.toCont f)) ∧
    (∀ x, C.S x = true → meets P x →
      ∃ a', C.pole a' ∧ X.Inc a' x ∧ d (C.flip.toCont a') = 5 ∧
        ∀ b, C.pole b → X.Inc b x → d (C.flip.toCont b) = 5 → b = a') ∧
    (∀ t, d (C.flip.toCont (C.e t)) = d (C.hubPorts.p t)) := by
  obtain ⟨h1, h2, h3, _⟩ := C.pole_of_D1 hd (a := fun t => d (C.hubPorts.p t)) (O := fun _ _ => False)
    (B := fun _ _ => False) ⟨fun _ => rfl, fun _ _ _ h _ => h⟩
  exact ⟨h1, h2, h3⟩

end Cut3

end gluep

end RH2F


/-
  TE2.lean — **Lemma TD-EXT** (fact b35d04291c8ef257) for a triangle-with-digon piece `T` on the true side of a
  3-edge-cut `K`: an MC pole colouring `d` of `Q(X′, z)` (`K.flip.hubPorts`) with `d(p_i) = 6`, `d(p_j)`, `d(p_k)`
  distinct colours other than `6`, of L-shape at the apex port (condition (ii) or (iii)), extends over the piece to an
  MC colouring of `X` with `e_i`, `y_j u`, `v y_k` in colour class `6` that agrees with `d` on the far side.
  (b) W-colourings of shape (S1) at the apex port are of L-shape.
-/

namespace RH2F
open MGraph
open Classical

def c9ii : List Nat := [5, 0, 1, 1, 2, 5, 3, 4, 5]
def c9iii : List Nat := [5, 0, 1, 2, 0, 5, 3, 4, 5]
theorem h9_cii : Star 6 (colL H9.m c9ii) := H9.star_of_check _ (by decide)
theorem h9_ciii : Star 6 (colL H9.m c9iii) := H9.star_of_check _ (by decide)

theorem two_rest : ∀ x y z : Fin 6, x ≠ 5 → y ≠ 5 → z ≠ 5 → x ≠ y → x ≠ z → y ≠ z →
    ∃ e e' : Fin 6, e ≠ e' ∧ e ≠ 5 ∧ e ≠ x ∧ e ≠ y ∧ e ≠ z ∧ e' ≠ 5 ∧ e' ≠ x ∧ e' ≠ y ∧ e' ≠ z := by decide

section tdext
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n}

/-- condition (ii) of fact b35d04291c8ef257 at the apex port `i` (with `a2 = d(p_j)`, `a3 = d(p_k)`), in the
    `Col`/`Blk` form: `a3 ∉ Π`, a colour `β ∉ {6, a2, a3} ∪ Π ∪ {t_3}`, and not (`t_2 = a3` and `f_2` blocked) -/
def CondII (D : Ports Q v) (i j k : Fin 3) (d : Fin Y.m → Fin 6) : Prop :=
  ¬ vCol D d i (d (D.p k)) ∧
  (∃ β, β ≠ 5 ∧ β ≠ d (D.p j) ∧ β ≠ d (D.p k) ∧ ¬ vCol D d i β ∧ ¬ vCol D d k β) ∧
  ¬ (vCol D d j (d (D.p k)) ∧ vBlk D d j (d (D.p k)))

/-- condition (iii) (the mirror image of (ii)) -/
def CondIII (D : Ports Q v) (i j k : Fin 3) (d : Fin Y.m → Fin 6) : Prop :=
  ¬ vCol D d i (d (D.p j)) ∧
  (∃ α, α ≠ 5 ∧ α ≠ d (D.p j) ∧ α ≠ d (D.p k) ∧ ¬ vCol D d i α ∧ ¬ vCol D d j α) ∧
  ¬ (vCol D d k (d (D.p j)) ∧ vBlk D d k (d (D.p j)))

/-- an MC pole colouring of **L-shape at the apex port** `i` -/
def LShape (D : Ports Q v) (i j k : Fin 3) (d : Fin Y.m → Fin 6) : Prop :=
  MCPole D d ∧ d (D.p i) = 5 ∧ d (D.p j) ≠ 5 ∧ d (D.p k) ≠ 5 ∧ d (D.p j) ≠ d (D.p k) ∧
  (CondII D i j k d ∨ CondIII D i j k d)

end tdext

section ext
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)
include T

/-- **the general extension**: a star colouring `φ` of the piece with its cut edges with colours
    `e_i ↦ 6, e_j ↦ a2, e_k ↦ a3, t12 ↦ α, t13 ↦ β, a ↦ 6, d1 ↦ ε, d2 ↦ ε′, b ↦ 6` glues with the pole colouring
    `d` under the stated conditions -/
theorem ext_gen (hG : InG X P) {d : Fin (addHub X K.flip.flip.w).m → Fin 6} (hd : MCPole K.flip.hubPorts d)
    (hi : d (K.flip.hubPorts.p i) = 5) (hj5 : d (K.flip.hubPorts.p j) ≠ 5) (hk5 : d (K.flip.hubPorts.p k) ≠ 5)
    (hjk : d (K.flip.hubPorts.p j) ≠ d (K.flip.hubPorts.p k)) {α β ε ε' : Fin 6}
    (hα5 : α ≠ 5) (hβ5 : β ≠ 5) (hεj : ε ≠ d (K.flip.hubPorts.p j)) (hε'j : ε' ≠ d (K.flip.hubPorts.p j))
    (hεk : ε ≠ d (K.flip.hubPorts.p k)) (hε'k : ε' ≠ d (K.flip.hubPorts.p k)) (hε5 : ε ≠ 5) (hε'5 : ε' ≠ 5)
    (pI : ¬ vCol K.flip.hubPorts d i α ∧ ¬ vCol K.flip.hubPorts d i β)
    (pJ : vCol K.flip.hubPorts d j α → α = d (K.flip.hubPorts.p k) ∧ β ≠ d (K.flip.hubPorts.p j) ∧
      ¬ vBlk K.flip.hubPorts d j α)
    (pK : vCol K.flip.hubPorts d k β → β = d (K.flip.hubPorts.p j) ∧ α ≠ d (K.flip.hubPorts.p k) ∧
      ¬ vBlk K.flip.hubPorts d k β)
    (φ : Fin X.m → Fin 6) (hφ : StarOn K.pole 6 φ)
    (vi : φ (K.e i) = 5) (vj : φ (K.e j) = d (K.flip.hubPorts.p j)) (vk : φ (K.e k) = d (K.flip.hubPorts.p k))
    (v12 : φ T.t12 = α) (v13 : φ T.t13 = β) (va : φ T.a = 5) (vd1 : φ T.d1 = ε) (vd2 : φ T.d2 = ε')
    (vb : φ T.b = 5) :
    ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 ∧ ∀ f, K.flip.inA f → c f = d (K.toCont f) := by
  obtain ⟨hψ, hψA, hψe⟩ := K.flip.pole_side hd
  set ψ : Fin X.m → Fin 6 := fun f => d (K.flip.flip.toCont f) with hψdef
  have hports : ∀ s u, d (K.flip.hubPorts.p s) = d (K.flip.hubPorts.p u) → s = u := by
    have hv : ∀ s, s = i ∨ s = j ∨ s = k := fun s => fin3_cases i j k s T.hij T.hik T.hjk
    intro s u h
    rcases hv s with rfl | rfl | rfl <;> rcases hv u with rfl | rfl | rfl
    all_goals first
      | rfl
      | (exfalso; first
          | exact hj5 (h.symm.trans hi) | exact hj5 (h.trans hi) | exact hk5 (h.symm.trans hi)
          | exact hk5 (h.trans hi) | exact hjk h | exact hjk h.symm)
  have nb5 : ∀ t, d (K.flip.hubPorts.p t) ≠ 5 → ¬ vBlk K.flip.hubPorts d t 5 :=
    fun t ht => noBlk5 (K.flip.flip.cont_inG hG).1 hd hports ht
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
  have atI : ∀ f, K.pole f → X.Inc f (K.y i) → f = K.e i ∨ f = T.t12 ∨ f = T.t13 :=
    fun f hf hfx => T.at_yi hG f (K.pole_P hf) hfx
  have atU : ∀ f, K.pole f → X.Inc f T.u → f = T.a ∨ f = T.d1 ∨ f = T.d2 :=
    fun f hf hfx => T.at_u hG f (K.pole_P hf) hfx
  have atV : ∀ f, K.pole f → X.Inc f T.v → f = T.d1 ∨ f = T.d2 ∨ f = T.b :=
    fun f hf hfx => T.at_v hG f (K.pole_P hf) hfx
  have hcut : ∀ t, φ (K.e t) = ψ (K.e t) := by
    intro t
    have e := hψe t
    rcases fin3_cases i j k t T.hij T.hik T.hjk with rfl | rfl | rfl
    · rw [vi]; exact (e.trans hi).symm
    · rw [vj]; exact e.symm
    · rw [vk]; exact e.symm
  have htri : ∀ t κ, K.Col φ t κ → K.flip.Col ψ t κ → (K.Blk φ t κ ∨ K.flip.Blk ψ t κ) → False := by
    intro t κ hc hc' hB
    have hv := K.flip.col_hub hc'
    rcases fin3_cases i j k t T.hij T.hik T.hjk with ht | ht | ht <;> rw [ht] at hc hc' hB hv
    · -- apex port: the triangle colours `α`, `β` avoid `Π`
      obtain ⟨f, hf, hfy, rfl⟩ := hc
      rcases atI f (Or.inl hf) hfy with rfl | rfl | rfl
      · exact K.not_inA_of_cut ⟨i, rfl⟩ hf
      · rw [v12] at hv; exact pI.1 hv
      · rw [v13] at hv; exact pI.2 hv
    · obtain ⟨f, hf, hfy, rfl⟩ := hc
      rcases colJ f hf hfy with rfl | rfl
      · rw [v12] at hv hB
        obtain ⟨hαk, hβj, hnb⟩ := pJ hv
        rcases hB with ⟨f0, r, hf0, hj0, hc0, f', hf', hf'f, hf'r, hc'⟩ | hB
        · rcases colJ f0 hf0 (joins_inc_left hj0) with rfl | rfl
          · have hr : r = K.y i := by
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
        · exact hnb (K.flip.blk_hub hB)
      · rw [va] at hv hB
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
            · rw [vd1] at hc'; exact hεj hc'
            · rw [vd2] at hc'; exact hε'j hc'
        · exact nb5 j hj5 (K.flip.blk_hub hB)
    · obtain ⟨f, hf, hfy, rfl⟩ := hc
      rcases colK f hf hfy with rfl | rfl
      · rw [v13] at hv hB
        obtain ⟨hβj, hαk, hnb⟩ := pK hv
        rcases hB with ⟨f0, r, hf0, hj0, hc0, f', hf', hf'f, hf'r, hc'⟩ | hB
        · rcases colK f0 hf0 (joins_inc_left hj0) with rfl | rfl
          · have hr : r = K.y i := by
              rcases joins_unique hj0 T.j13 with ⟨h, _⟩ | ⟨_, h⟩
              · exact absurd h.symm (T.yne T.hik)
              · exact h
            subst hr
            rw [vk] at hc'
            rcases atI f' hf' hf'r with rfl | rfl | rfl
            · rw [vi] at hc'; exact hk5 hc'.symm
            · rw [v12] at hc'; exact hαk hc'
            · exact hf'f rfl
          · rw [vb] at hc0; exact hβ5 hc0.symm
        · exact hnb (K.flip.blk_hub hB)
      · rw [vb] at hv hB
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
            · rw [vd1] at hc'; exact hεk hc'
            · rw [vd2] at hc'; exact hε'k hc'
            · exact hf'f rfl
        · exact nb5 k hk5 (K.flip.blk_hub hB)
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
      · rw [vk] at hb5; exact absurd hb5 hk5
      · rw [v13] at hb5; exact absurd hb5 hβ5
      · rfl
    · refine ⟨T.a, Or.inl T.inA_a, joins_inc_right T.ja, va, fun b' hb' hbx hb5 => ?_⟩
      rcases atU b' hb' hbx with rfl | rfl | rfl
      · rfl
      · rw [vd1] at hb5; exact absurd hb5 hε5
      · rw [vd2] at hb5; exact absurd hb5 hε'5
    · refine ⟨T.b, Or.inl T.inA_b, joins_inc_left T.jb, vb, fun b' hb' hbx hb5 => ?_⟩
      rcases atV b' hb' hbx with rfl | rfl | rfl
      · rw [vd1] at hb5; exact absurd hb5 hε5
      · rw [vd2] at hb5; exact absurd hb5 hε'5
      · rfl
  have hψB : ∀ x, K.S x = false → meets P x →
      ∃ a', K.flip.pole a' ∧ X.Inc a' x ∧ ψ a' = 5 ∧ ∀ b', K.flip.pole b' → X.Inc b' x → ψ b' = 5 → b' = a' := by
    intro x hx hxm
    exact hψA x (by rw [Cut3.flip_S, hx]; rfl) hxm
  obtain ⟨c, hc, hcφ, hcψ⟩ := glue_poles K φ ψ hφ hψ hcut htri hφA hψB
  refine ⟨c, hc, by rw [hcφ _ (Or.inr ⟨i, rfl⟩)]; exact vi, by rw [hcφ _ (Or.inl T.inA_a)]; exact va,
    by rw [hcφ _ (Or.inl T.inA_b)]; exact vb, fun f hf => hcψ f (Or.inl hf)⟩

end TriPiece

end ext

end RH2F


/-
  TE3.lean — Lemma TD-EXT (a) and (b) (fact b35d04291c8ef257), the L-shape form (TD-L) of the restricted EX1 property
  and Corollary TDL-RED (fact ec1a55061cb47e8f): (TD-L) implies (TD), (TD-L-TRI) implies (TD-TRI), and Theorem ROOT-CS4
  with (W-EXT) in place of (POLE) and (TD-L-TRI) in place of (TD-TRI).
-/

namespace RH2F
open MGraph
open Classical

theorem sixth_colour : ∀ a b c d e : Fin 6, ∃ z : Fin 6, z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d ∧ z ≠ e := by decide

section tdext2
variable {X : MGraph} {P : Fin X.m → Prop} {K : Cut3 P} {i j k : Fin 3}

namespace TriPiece
variable (T : TriPiece K i j k)
include T

/-- **Lemma TD-EXT (a)**: an MC pole colouring of L-shape at the apex port extends over the piece -/
theorem td_ext (hG : InG X P) {d : Fin (addHub X K.flip.flip.w).m → Fin 6} (hL : LShape K.flip.hubPorts i j k d) :
    ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 ∧ ∀ f, K.flip.inA f → c f = d (K.toCont f) := by
  obtain ⟨hd, hi, hj5, hk5, hjk, hII | hIII⟩ := hL
  · obtain ⟨ha3i, ⟨β, hβ5, hβj, hβk, hβi, hβkc⟩, hnot⟩ := hII
    obtain ⟨e, e', hee, he5, hej, hek, heb, he'5, he'j, he'k, he'b⟩ :=
      two_rest (d (K.flip.hubPorts.p j)) (d (K.flip.hubPorts.p k)) β hj5 hk5 hβ5 hjk (Ne.symm hβj) (Ne.symm hβk)
    let σ : Fin 6 → Fin 6 := ![d (K.flip.hubPorts.p j), d (K.flip.hubPorts.p k), β, e, e', 5]
    have hσ : ∀ a b, σ a = σ b → a = b := by
      have hinj : Function.Injective σ := by
        apply List.nodup_ofFn.1
        simp [σ, List.ofFn_succ, hjk, Ne.symm hβj, Ne.symm hβk, Ne.symm hej, Ne.symm hek, Ne.symm heb,
          Ne.symm he'j, Ne.symm he'k, Ne.symm he'b, hee, hj5, hk5, hβ5, he5, he'5]
      exact fun a b h => hinj h
    obtain ⟨φ, hφ, hφv⟩ := T.star9 hG (starOn_comp_inj σ hσ h9_cii)
    exact T.ext_gen hG hd hi hj5 hk5 hjk (α := d (K.flip.hubPorts.p k)) (β := β) (ε := e) (ε' := e') hk5 hβ5
      hej he'j hek he'k he5 he'5 ⟨ha3i, hβi⟩ (fun hv => ⟨rfl, hβj, fun hb => hnot ⟨hv, hb⟩⟩)
      (fun hv => absurd hv hβkc) φ hφ
      (by have h := hφv ⟨0, by decide⟩; exact h) (by have h := hφv ⟨1, by decide⟩; exact h)
      (by have h := hφv ⟨2, by decide⟩; exact h) (by have h := hφv ⟨3, by decide⟩; exact h)
      (by have h := hφv ⟨4, by decide⟩; exact h) (by have h := hφv ⟨5, by decide⟩; exact h)
      (by have h := hφv ⟨6, by decide⟩; exact h) (by have h := hφv ⟨7, by decide⟩; exact h)
      (by have h := hφv ⟨8, by decide⟩; exact h)
  · obtain ⟨ha2i, ⟨α, hα5, hαj, hαk, hαi, hαjc⟩, hnot⟩ := hIII
    obtain ⟨e, e', hee, he5, hej, hek, hea, he'5, he'j, he'k, he'a⟩ :=
      two_rest (d (K.flip.hubPorts.p j)) (d (K.flip.hubPorts.p k)) α hj5 hk5 hα5 hjk (Ne.symm hαj) (Ne.symm hαk)
    let σ : Fin 6 → Fin 6 := ![d (K.flip.hubPorts.p j), d (K.flip.hubPorts.p k), α, e, e', 5]
    have hσ : ∀ a b, σ a = σ b → a = b := by
      have hinj : Function.Injective σ := by
        apply List.nodup_ofFn.1
        simp [σ, List.ofFn_succ, hjk, Ne.symm hαj, Ne.symm hαk, Ne.symm hej, Ne.symm hek, Ne.symm hea,
          Ne.symm he'j, Ne.symm he'k, Ne.symm he'a, hee, hj5, hk5, hα5, he5, he'5]
      exact fun a b h => hinj h
    obtain ⟨φ, hφ, hφv⟩ := T.star9 hG (starOn_comp_inj σ hσ h9_ciii)
    exact T.ext_gen hG hd hi hj5 hk5 hjk (α := α) (β := d (K.flip.hubPorts.p j)) (ε := e) (ε' := e') hα5 hj5
      hej he'j hek he'k he5 he'5 ⟨hαi, ha2i⟩ (fun hv => absurd hv hαjc)
      (fun hv => ⟨rfl, hαk, fun hb => hnot ⟨hv, hb⟩⟩) φ hφ
      (by have h := hφv ⟨0, by decide⟩; exact h) (by have h := hφv ⟨1, by decide⟩; exact h)
      (by have h := hφv ⟨2, by decide⟩; exact h) (by have h := hφv ⟨3, by decide⟩; exact h)
      (by have h := hφv ⟨4, by decide⟩; exact h) (by have h := hφv ⟨5, by decide⟩; exact h)
      (by have h := hφv ⟨6, by decide⟩; exact h) (by have h := hφv ⟨7, by decide⟩; exact h)
      (by have h := hφv ⟨8, by decide⟩; exact h)

/-- the property (TD-L) of fact ec1a55061cb47e8f: for every edge `g` inside the far side and every status `t`
    realized by a perfect matching through `e_i`, `a`, `b`, an MC pole colouring of `Q(X′, z)` of L-shape at the apex
    port with `[d(g) = 6] = t` -/
def TDL : Prop :=
  ∀ g, K.flip.inA g → ∀ t : Bool,
    (∃ N, PMOn P N ∧ N (K.e i) ∧ N T.a ∧ N T.b ∧ (N g ↔ t = true)) →
    ∃ d, LShape K.flip.hubPorts i j k d ∧ (d (K.toCont g) = 5 ↔ t = true)

/-- **Corollary TDL-RED**, the local part: (TD-L) implies (TD) -/
theorem td_of_tdl (hG : InG X P) (h : T.TDL) : T.TD := by
  intro g hg t hN
  obtain ⟨d, hL, hst⟩ := h g hg t hN
  obtain ⟨c, hc, h1, h2, h3, hcd⟩ := T.td_ext hG hL
  exact ⟨c, hc, h1, h2, h3, by rw [hcd g hg]; exact hst⟩

end TriPiece

end tdext2

section tdb
variable {Y : MGraph} {Q : Fin Y.m → Prop} {v : Fin Y.n}

/-- **Lemma TD-EXT (b)**: a W-colouring of shape (S1) at the apex port is of L-shape -/
theorem lshape_of_wcol_s1 (hG : InG Y Q) {D : Ports Q v} {i j k : Fin 3} {d : Fin Y.m → Fin 6}
    (hW : WCol D i j k d)
    (hS1 : ∃ c, c ≠ 5 ∧ c ≠ d (D.p j) ∧ c ≠ d (D.p k) ∧
      ((∀ κ, vCol D d i κ ↔ κ = d (D.p j) ∨ κ = c) ∨ (∀ κ, vCol D d i κ ↔ κ = d (D.p k) ∨ κ = c)) ∧
      ¬ vCol D d j c ∧ ¬ vCol D d k c) :
    LShape D i j k d := by
  obtain ⟨hd, hdi, hA5, hB5, hAB, hW0j, hW0k, _⟩ := hW
  obtain ⟨c, hc5, hcA, hcB, hci, hcj, hck⟩ := hS1
  obtain ⟨γj, hγj5, _, hCj⟩ := col_two hG hd hA5
  obtain ⟨γk, hγk5, _, hCk⟩ := col_two hG hd hB5
  refine ⟨hd, hdi, hA5, hB5, hAB, ?_⟩
  rcases hci with h | h
  · -- `Col_i(d) = {A, c}`: condition (ii)
    left
    obtain ⟨β, hβ5, hβA, hβB, hβc, hβk⟩ := sixth_colour 5 (d (D.p j)) (d (D.p k)) c γk
    refine ⟨fun hv => ?_, ⟨β, hβ5, hβA, hβB, fun hv => ?_, fun hv => ?_⟩, fun hb => hW0j hb.2⟩
    · rcases (h _).1 hv with e | e
      · exact hAB e.symm
      · exact hcB e.symm
    · rcases (h _).1 hv with e | e
      · exact hβA e
      · exact hβc e
    · rcases (hCk _).1 hv with e | e
      · exact hβ5 e
      · exact hβk e
  · -- `Col_i(d) = {B, c}`: condition (iii)
    right
    obtain ⟨α, hα5, hαA, hαB, hαc, hαj⟩ := sixth_colour 5 (d (D.p j)) (d (D.p k)) c γj
    refine ⟨fun hv => ?_, ⟨α, hα5, hαA, hαB, fun hv => ?_, fun hv => ?_⟩, fun hb => hW0k hb.2⟩
    · rcases (h _).1 hv with e | e
      · exact hAB e
      · exact hcA e.symm
    · rcases (h _).1 hv with e | e
      · exact hαB e
      · exact hαc e
    · rcases (hCj _).1 hv with e | e
      · exact hα5 e
      · exact hαj e

end tdb

/-- (TD-L-TRI) (fact ec1a55061cb47e8f): (TD-TRI) with (TD-L) in place of (TD). The ports `j`, `k` face the ends of
    `δ`: `C.y j` is the end of `δ` next to `u = dU δ` (the edge `eO δ`) and `C.y k` the end next to `v = dV δ` -/
def TDLTRI : Prop :=
  ∀ (Y : MGraph) (Q : Fin Y.m → Prop), InS Y Q → ¬ C4C Y Q → ∀ (C : Cut3 Q), CycSide Q C.S → scount Q C.S true = 3 →
    ∀ (D : Fin Y.m → Prop), 16 ≤ vcount Q + 2 * cntF Y.m (fun d => Q d ∧ D d) →
    ∀ (i j k : Fin 3) (δ : Fin Y.m), Q δ → D δ → (Y.ends δ).1 = C.y j → (Y.ends δ).2 = C.y k → i ≠ j → i ≠ k →
      (∀ d, Q d → D d → (C.S (Y.ends d).1 = true ∨ C.S (Y.ends d).2 = true) → d = δ) →
      ∀ g, (Cut3.dig (D := D) C).flip.inA g → ∀ t : Bool,
        (∃ N, PMOn (digSet Q D) N ∧ N ((Cut3.dig (D := D) C).e i) ∧ N (eO δ) ∧ N (eN δ 2) ∧ (N g ↔ t = true)) →
        ∃ d, LShape (Cut3.dig (D := D) C).flip.hubPorts i j k d ∧
          (d ((Cut3.dig (D := D) C).toCont g) = 5 ↔ t = true)

/-- **Corollary TDL-RED**: (TD-L-TRI) implies (TD-TRI) -/
theorem tdtri_of_tdltri (hL : TDLTRI) : TDTRI := by
  intro Y Q hQ hc4 C hcyc h3 D hn16 i δ hQδ hDδ hδ1 hδ2 hδi huniq
  obtain ⟨hGd, _, _⟩ := dig_class hQ.1 hQ.2.2 D
  obtain ⟨j, k, T, hTa, hTb⟩ := triPiece_of hQ C h3 D i δ hQδ hDδ hδ1 hδ2 hδi huniq
  -- the ports of the TriPiece face the ends of `δ`
  have hj : (Y.ends δ).1 = C.y j := by
    have h := T.ja
    rw [hTa] at h
    have hy : (Cut3.dig (D := D) C).y j = dO (C.y j) := by
      show cutY (D := D) C.S (C.e j) (C.y j) = dO (C.y j)
      unfold cutY
      rw [if_neg]
      intro hD
      have hin : C.S (Y.ends (C.e j)).1 = true ∨ C.S (Y.ends (C.e j)).2 = true := by
        rcases C.hj j with h' | h' <;> rw [h'] <;> simp [C.sy j]
      have e := huniq _ (C.hP j) hD hin
      rw [← e] at hδ1 hδ2
      rcases C.hj j with h' | h' <;> rw [h'] at hδ1 hδ2
      · rw [C.sw j] at hδ2; exact absurd hδ2 (by decide)
      · rw [C.sw j] at hδ1; exact absurd hδ1 (by decide)
    rw [hy] at h
    rcases joins_unique h (Or.inl (ends_eO_D hDδ)) with ⟨e1, _⟩ | ⟨e1, _⟩
    · exact (dO_inj e1).symm
    · exact absurd e1 (dO_ne_dU _ _)
  have hk : (Y.ends δ).2 = C.y k := by
    have h := T.jb
    rw [hTb] at h
    have hy : (Cut3.dig (D := D) C).y k = dO (C.y k) := by
      show cutY (D := D) C.S (C.e k) (C.y k) = dO (C.y k)
      unfold cutY
      rw [if_neg]
      intro hD
      have hin : C.S (Y.ends (C.e k)).1 = true ∨ C.S (Y.ends (C.e k)).2 = true := by
        rcases C.hj k with h' | h' <;> rw [h'] <;> simp [C.sy k]
      have e := huniq _ (C.hP k) hD hin
      rw [← e] at hδ1 hδ2
      rcases C.hj k with h' | h' <;> rw [h'] at hδ1 hδ2
      · rw [C.sw k] at hδ2; exact absurd hδ2 (by decide)
      · rw [C.sw k] at hδ1; exact absurd hδ1 (by decide)
    rw [hy] at h
    rcases joins_unique h (Or.inl (ends_eN2 δ)) with ⟨_, e2⟩ | ⟨_, e2⟩
    · exact (dO_inj e2).symm
    · exact absurd e2 (dO_ne_dV _ _)
  have hTDL : T.TDL := by
    unfold TriPiece.TDL; rw [hTa, hTb]
    exact hL Y Q hQ hc4 C hcyc h3 D hn16 i j k δ hQδ hDδ hj hk T.hij T.hik huniq
  have h := T.td_of_tdl hGd hTDL
  unfold TriPiece.TD at h; rw [hTa, hTb] at h
  exact h

end RH2F

namespace RH2F
open MGraph

/-- **layer 25 of the Lean formalization**: Lemma TD-EXT (fact b35d04291c8ef257) (a) and (b) and Corollary TDL-RED
    (fact ec1a55061cb47e8f); hence Theorem ROOT-CS4 (fact 6010cb59aaf31d7a) with (W-EXT) in place of (POLE) and
    (TD-L-TRI) in place of (TD-TRI) -/
theorem layer25 :
    (∀ (X : MGraph) (P : Fin X.m → Prop) (K : Cut3 P) (i j k : Fin 3) (T : TriPiece K i j k)
      (d : Fin (addHub X K.flip.flip.w).m → Fin 6), InG X P → LShape K.flip.hubPorts i j k d →
      ∃ c, MCol P c ∧ c (K.e i) = 5 ∧ c T.a = 5 ∧ c T.b = 5 ∧ ∀ f, K.flip.inA f → c f = d (K.toCont f)) ∧
    (∀ (Y : MGraph) (Q : Fin Y.m → Prop) (v : Fin Y.n) (D : Ports Q v) (i j k : Fin 3) (d : Fin Y.m → Fin 6),
      InG Y Q → WCol D i j k d →
      (∃ c, c ≠ 5 ∧ c ≠ d (D.p j) ∧ c ≠ d (D.p k) ∧
        ((∀ κ, vCol D d i κ ↔ κ = d (D.p j) ∨ κ = c) ∨ (∀ κ, vCol D d i κ ↔ κ = d (D.p k) ∨ κ = c)) ∧
        ¬ vCol D d j c ∧ ¬ vCol D d k c) → LShape D i j k d) ∧
    (∀ (X : MGraph) (P : Fin X.m → Prop) (K : Cut3 P) (i j k : Fin 3) (T : TriPiece K i j k), InG X P →
      T.TDL → T.TD) ∧
    (TDLTRI → TDTRI) ∧
    (BASE12 → SIMPLE14 → B14D → SMALLHOSTD → SMALLPD →
      FEEXTD10 → FEEXISTD10 → WEXT → TDLTRI → IID → DMS) :=
  ⟨fun _ _ _ _ _ _ T _ hG hL => T.td_ext hG hL, fun _ _ _ _ _ _ _ _ hG hW hS1 => lshape_of_wcol_s1 hG hW hS1,
   fun _ _ _ _ _ _ T hG h => T.td_of_tdl hG h, tdtri_of_tdltri,
   fun hB12 hS14 hB14 hSH hPD hext hex hW htdl hD =>
     layer24.2.2 hB12 hS14 hB14 hSH hPD hext hex hW (tdtri_of_tdltri htdl) hD⟩

end RH2F
