import IndependentTransversals.GeneralHaxell
import Mathlib.Data.Finset.Lattice.Union

/-! A known weaker Haxell matching criterion, proved by a literal conflict graph.
The constant is 2ℓ for internal edge size at most ℓ, not the sharper 2ℓ−1.
This is foundational mathematics and does not prove the BM router. -/
noncomputable section
open IndependentTransversals
namespace OpenMathReview.WeakHypergraph
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

abbrev EdgeVertex (F : A → Finset (Finset B)) := Σ a : A, {e : Finset B // e ∈ F a}

def block (F : A → Finset (Finset B)) (a : A) : Set (EdgeVertex F) := {v | v.1 = a}

def conflict (F : A → Finset (Finset B)) : SimpleGraph (EdgeVertex F) where
  Adj v w := v ≠ w ∧ ¬Disjoint v.2.1 w.2.1
  symm := by
    constructor
    intro v w h
    exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem block_injective (F : A → Finset (Finset B))
    (hF : ∀ a, (F a).Nonempty) : Function.Injective (block F) := by
  intro a b hab
  obtain ⟨e, he⟩ := hF a
  have hm : (⟨a, ⟨e, he⟩⟩ : EdgeVertex F) ∈ block F b := hab ▸ rfl
  exact hm

def partitioned (F : A → Finset (Finset B)) (hF : ∀ a, (F a).Nonempty) :
    PartitionedGraph (EdgeVertex F) where
  graph := conflict F
  blocks := Set.range (block F)
  isPartition := by
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨e, he⟩ := hF a
      have hm : (⟨a, ⟨e, he⟩⟩ : EdgeVertex F) ∈ block F a := rfl
      rw [ha] at hm
      exact hm
    · intro v
      refine ⟨block F v.1, ⟨⟨v.1, rfl⟩, rfl⟩, ?_⟩
      rintro U ⟨⟨a, rfl⟩, hv⟩
      change v.1 = a at hv
      exact congrArg (block F) hv.symm

/-- Each nonempty subfamily has an edge avoiding every proposed small cover.
The conclusion chooses one genuine internal edge for every index, disjointly. -/
theorem disjoint_representatives (F : A → Finset (Finset B)) (ℓ : ℕ)
    (hsize : ∀ a e, e ∈ F a → e.card ≤ ℓ)
    (hcover : ∀ I : Finset A, I.Nonempty → ∀ U : Finset B,
      U.card ≤ 2 * ℓ * (I.card - 1) →
        ∃ a ∈ I, ∃ e ∈ F a, Disjoint e U) :
    ∃ f : A → Finset B, (∀ a, f a ∈ F a) ∧
      Pairwise (fun a b => Disjoint (f a) (f b)) := by
  classical
  have hF : ∀ a, (F a).Nonempty := by
    intro a
    obtain ⟨b, hb, e, he, _⟩ := hcover {a} (by simp) ∅ (by simp)
    have hba : b = a := by simpa using hb
    exact ⟨e, hba ▸ he⟩
  letI : Fintype (EdgeVertex F) := Fintype.ofFinite _
  let G := partitioned F hF
  have hn : G.NoSmallTotalDomination := by
    intro C hC hCn D hD
    let I : Finset A := Finset.univ.filter (fun a => block F a ∈ C)
    have hI : ∀ a, a ∈ I ↔ block F a ∈ C := by intro a; simp [I]
    have himage : block F '' (I : Set A) = C := by
      ext U
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hI a).mp ha
      · intro hU
        obtain ⟨a, rfl⟩ := hC hU
        exact ⟨a, (hI a).mpr hU, rfl⟩
    have hcard : I.card = C.ncard := by
      rw [← himage, Set.ncard_image_of_injective _ (block_injective F hF)]
      simp
    have hIn : I.Nonempty := by
      obtain ⟨U, hU⟩ := hCn
      obtain ⟨a, rfl⟩ := hC hU
      exact ⟨a, (hI a).mpr hU⟩
    let DF := (Set.toFinite D).toFinset
    let U : Finset B := DF.biUnion (fun v => v.2.1)
    have hDFcard : DF.card = D.ncard := by
      exact (Set.ncard_eq_toFinset_card D (Set.toFinite D)).symm
    have hUbound : U.card ≤ 2 * ℓ * (I.card - 1) := by
      calc
        U.card ≤ ∑ v ∈ DF, v.2.1.card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ DF, ℓ := Finset.sum_le_sum (fun v _ => hsize v.1 v.2.1 v.2.2)
        _ = ℓ * D.ncard := by simp [hDFcard, Nat.mul_comm]
        _ ≤ ℓ * (2 * (C.ncard - 1)) := Nat.mul_le_mul_left ℓ hD
        _ = 2 * ℓ * (I.card - 1) := by rw [hcard]; ring
    obtain ⟨a, ha, e, he, hd⟩ := hcover I hIn U hUbound
    let v : EdgeVertex F := ⟨a, ⟨e, he⟩⟩
    refine ⟨v, ?_, ?_⟩
    · change v ∈ ⋃₀ (C ∩ G.blocks)
      exact ⟨block F a, ⟨(hI a).mp ha, ⟨a, rfl⟩⟩, rfl⟩
    · apply Set.disjoint_left.mpr
      intro w hwN hwD
      have hsub : w.2.1 ⊆ U := by
        intro b hb
        exact Finset.mem_biUnion.mpr ⟨w, (Set.Finite.mem_toFinset (Set.toFinite D)).mpr hwD, hb⟩
      exact hwN.2 (hd.mono_right hsub)
  obtain ⟨T, hT, hblocks⟩ := G.haxell_no_small_total_domination hn
  have choose : ∀ a, ∃ v : EdgeVertex F, v ∈ T ∧ v.1 = a := by
    intro a
    obtain ⟨v, hv, _⟩ := hblocks (block F a) ⟨a, rfl⟩
    exact ⟨v, hv.1, hv.2⟩
  choose v hvT hvA using choose
  refine ⟨fun a => (v a).2.1, ?_, ?_⟩
  · intro a
    simpa only [hvA a] using (v a).2.2
  · intro a b hab
    have hneq : v a ≠ v b := by
      intro heq
      exact hab ((hvA a).symm.trans ((congrArg Sigma.fst heq).trans (hvA b)))
    by_contra hd
    exact hT (hvT a) (hvT b) hneq ⟨hneq, hd⟩

#print axioms disjoint_representatives
#check @disjoint_representatives
end OpenMathReview.WeakHypergraph
