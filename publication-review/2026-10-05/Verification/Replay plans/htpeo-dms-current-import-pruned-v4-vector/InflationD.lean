import InflationC

namespace Inflation

variable (H : MGraph) (slot : Fin H.m → Bool → Fin 3)

theorem base_inc_side (e : Fin H.m) (X : Fin H.n) (h : H.Inc e X) :
    ∃ b : Bool, endOf H e b = X := by
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem adj_sides {e f : Fin H.m} (h : H.Adj e f) :
    ∃ p : Bool × Bool, endOf H e p.1 = endOf H f p.2 := by
  obtain ⟨_, X, he, hf⟩ := h
  obtain ⟨b, hb⟩ := base_inc_side H e X he
  obtain ⟨b', hb'⟩ := base_inc_side H f X hf
  exact ⟨(b, b'), hb.trans hb'.symm⟩

def neighbors (e : Fin H.m) : Finset (Fin H.m) :=
  Finset.univ.filter (H.Adj e)

noncomputable def neighborSides (e f : Fin H.m) : Bool × Bool :=
  if h : H.Adj e f then Classical.choose (adj_sides H h) else (false, false)

theorem neighborSides_spec (e f : Fin H.m) (h : H.Adj e f) :
    endOf H e (neighborSides H e f).1 = endOf H f (neighborSides H e f).2 := by
  simp only [neighborSides, dif_pos h]
  exact Classical.choose_spec (adj_sides H h)

noncomputable def neighborPort (e f : Fin H.m) : Bool × Fin 3 :=
  ((neighborSides H e f).1, slot f (neighborSides H e f).2)

def freePorts (e : Fin H.m) : Finset (Bool × Fin 3) :=
  Finset.univ.filter (fun p => p.2 ≠ slot e p.1)

theorem freePorts_card (e : Fin H.m) : (freePorts H slot e).card = 4 := by
  have h : ∀ a b : Fin 3,
      (Finset.univ.filter (fun p : Bool × Fin 3 => p.2 ≠ (if p.1 then b else a))).card = 4 := by decide
  exact h (slot e false) (slot e true)

theorem neighborPort_mem (hinj : PortsInj H slot) (e f : Fin H.m)
    (h : f ∈ neighbors H e) : neighborPort H slot e f ∈ freePorts H slot e := by
  have hadj : H.Adj e f := (Finset.mem_filter.mp h).2
  have hs := neighborSides_spec H e f hadj
  have hne := hadj.1
  simp only [neighborPort, freePorts, Finset.mem_filter, Finset.mem_univ, true_and]
  intro heq
  exact hne ((hinj e (neighborSides H e f).1 f (neighborSides H e f).2
    hs heq.symm).1)

theorem neighborPort_inj (hinj : PortsInj H slot) (e : Fin H.m) :
    Set.InjOn (neighborPort H slot e) (neighbors H e) := by
  intro f hf g hg heq
  have hfd : H.Adj e f := (Finset.mem_filter.mp hf).2
  have hgd : H.Adj e g := (Finset.mem_filter.mp hg).2
  have hsF := neighborSides_spec H e f hfd
  have hsG := neighborSides_spec H e g hgd
  have hb : (neighborSides H e f).1 = (neighborSides H e g).1 :=
    by simpa only [neighborPort] using congrArg Prod.fst heq
  have hp : slot f (neighborSides H e f).2 = slot g (neighborSides H e g).2 :=
    by simpa only [neighborPort] using congrArg Prod.snd heq
  apply (hinj f (neighborSides H e f).2 g (neighborSides H e g).2 ?_ hp).1
  rw [← hsF, hb, hsG]

theorem neighbors_card_le_four (hinj : PortsInj H slot) (e : Fin H.m) :
    (neighbors H e).card ≤ 4 := by
  have h := Finset.card_le_card_of_injOn (neighborPort H slot e)
    (fun f hf => neighborPort_mem H slot hinj e f hf)
    (neighborPort_inj H slot hinj e)
  rw [freePorts_card H slot e] at h
  exact h

theorem base_adj_symm {e f : Fin H.m} (h : H.Adj e f) : H.Adj f e :=
  ⟨fun heq => h.1 heq.symm, h.2.imp fun _ p => ⟨p.2, p.1⟩⟩

def goodBase (k : Nat) (c : Fin H.m → Fin 5) : Prop :=
  ∀ e f, H.Adj e f → e.val < k → f.val < k → c e ≠ c f

theorem base_coloring_exists (hinj : PortsInj H slot) :
    ∃ c : Fin H.m → Fin 5, ∀ e f, H.Adj e f → c e ≠ c f := by
  have step : ∀ k : Nat, k ≤ H.m → ∃ c : Fin H.m → Fin 5, goodBase H k c := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨fun _ => 0, ?_⟩
        intro e f _ he _
        omega
    | succ k ih =>
        intro hk
        obtain ⟨c, hc⟩ := ih (by omega)
        let e : Fin H.m := ⟨k, by omega⟩
        let F := (neighbors H e).filter (fun f => f.val < k)
        let B := F.image c
        have hcardF : F.card ≤ 4 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans
            (neighbors_card_le_four H slot hinj e)
        have hcardB : B.card ≤ 4 := (Finset.card_image_le).trans hcardF
        have hfree : ∃ z : Fin 5, z ∉ B := by
          by_contra hn
          push_neg at hn
          have hsub : (Finset.univ : Finset (Fin 5)) ⊆ B := by
            intro z _
            exact hn z
          have hfive : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
          have := Finset.card_le_card hsub
          omega
        obtain ⟨z, hz⟩ := hfree
        let c' : Fin H.m → Fin 5 := fun f => if f = e then z else c f
        refine ⟨c', ?_⟩
        intro a b hab ha hb
        by_cases hae : a = e
        · subst a
          have hbe : b ≠ e := fun h => hab.1 h.symm
          have hblt : b.val < k := by
            have hneq : b.val ≠ k := by
              intro h
              exact hbe (Fin.ext h)
            omega
          have hbf : b ∈ F := Finset.mem_filter.mpr ⟨by simp [neighbors, hab], hblt⟩
          have hcb : c b ∈ B := Finset.mem_image.mpr ⟨b, hbf, rfl⟩
          change (if e = e then z else c e) ≠ (if b = e then z else c b)
          simp only [ite_true, if_neg hbe]
          intro heq
          exact hz (by rw [heq]; exact hcb)
        by_cases hbe : b = e
        · subst b
          have ha' : a.val < k := by
            have hneq : a.val ≠ k := by
              intro h
              exact hae (Fin.ext h)
            omega
          have haf : a ∈ F := Finset.mem_filter.mpr
            ⟨by simp [neighbors, base_adj_symm H hab], ha'⟩
          have hca : c a ∈ B := Finset.mem_image.mpr ⟨a, haf, rfl⟩
          change (if a = e then z else c a) ≠ (if e = e then z else c e)
          simp only [ite_true, if_neg hae]
          intro heq
          exact hz (by rw [← heq]; exact hca)
        have ha' : a.val < k := by
          have hneq : a.val ≠ k := by
            intro h
            exact hae (Fin.ext h)
          omega
        have hb' : b.val < k := by
          have hneq : b.val ≠ k := by
            intro h
            exact hbe (Fin.ext h)
          omega
        change (if a = e then z else c a) ≠ (if b = e then z else c b)
        simpa only [if_neg hae, if_neg hbe] using hc a b hab ha' hb'
  obtain ⟨c, hc⟩ := step H.m (le_refl _)
  exact ⟨c, fun e f h => hc e f h e.isLt f.isLt⟩

end Inflation
