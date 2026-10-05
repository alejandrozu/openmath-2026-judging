import Lea.RamseyLifting.Lifting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

set_option maxHeartbeats 1000000

/-!
# From the blow-up bound to `c₄ ≤ P`

This file completes the final paragraph of `LIFTING.md`, on top of the verified
module `Lea.RamseyLifting.Lifting` (imported, never edited).
-/

namespace Lea.RamseyC4

open Finset

/-! ## 1. Monochromatic four-sets over an arbitrary finite vertex type -/

/-- A finset of vertices all of whose pairs of DISTINCT elements get the same colour. -/
def Mono {V : Type*} (χ : V → V → Bool) (S : Finset V) : Prop :=
  ∃ c : Bool, ∀ u ∈ S, ∀ x ∈ S, u ≠ x → χ u x = c

instance decMono {V : Type*} [DecidableEq V] (χ : V → V → Bool) :
    DecidablePred (Mono χ) := fun _ => by unfold Mono; infer_instance

/-- `M₄` for an arbitrary finite vertex type: the number of monochromatic four-sets. -/
def m4 {V : Type*} [Fintype V] [DecidableEq V] (χ : V → V → Bool) : ℕ :=
  (((univ : Finset V).powersetCard 4).filter (Mono χ)).card

lemma m4_le {V : Type*} [Fintype V] [DecidableEq V] (χ : V → V → Bool) :
    m4 χ ≤ (Fintype.card V).choose 4 := by
  unfold m4
  calc (((univ : Finset V).powersetCard 4).filter (Mono χ)).card
      ≤ ((univ : Finset V).powersetCard 4).card := Finset.card_filter_le _ _
    _ = (Fintype.card V).choose 4 := by rw [Finset.card_powersetCard, Finset.card_univ]

/-- Only the colours of DISTINCT pairs matter. -/
lemma m4_congr {V : Type*} [Fintype V] [DecidableEq V] {χ ψ : V → V → Bool}
    (h : ∀ x y, x ≠ y → χ x y = ψ x y) : m4 χ = m4 ψ := by
  unfold m4
  congr 1
  refine Finset.filter_congr ?_
  intro S _
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun u hu x hx hux => by rw [← h u x hux]; exact hc u hu x hx hux⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun u hu x hx hux => by rw [h u x hux]; exact hc u hu x hx hux⟩

/-- Pulling a colouring back along an embedding. -/
lemma mono_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (χ : W → W → Bool) (S : Finset V) :
    Mono (fun x y : V => χ (f x) (f y)) S ↔ Mono χ (S.map f) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro u hu x hx hux
    obtain ⟨u', hu', rfl⟩ := Finset.mem_map.1 hu
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    exact hc u' hu' x' hx' (fun hh => hux (by rw [hh]))
  · rintro ⟨c, hc⟩
    exact ⟨c, fun u hu x hx hux =>
      hc (f u) (Finset.mem_map_of_mem f hu) (f x) (Finset.mem_map_of_mem f hx)
        (fun hh => hux (f.injective hh))⟩

/-- **Transport along a bijection of vertex types.** -/
lemma m4_equiv {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (χ : V → V → Bool) :
    m4 (fun x y : W => χ (e.symm x) (e.symm y)) = m4 χ := by
  unfold m4
  refine Finset.card_nbij' (i := fun S : Finset W => S.map e.symm.toEmbedding)
    (j := fun S : Finset V => S.map e.toEmbedding) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard_univ] at hS ⊢
    refine ⟨by rw [Finset.card_map]; exact hS.1, ?_⟩
    exact (mono_map e.symm.toEmbedding χ S).1 hS.2
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard_univ] at hS ⊢
    refine ⟨by rw [Finset.card_map]; exact hS.1, ?_⟩
    refine (mono_map e.toEmbedding (fun x y : W => χ (e.symm x) (e.symm y)) S).1 ?_
    simpa using hS.2
  · intro S _
    ext x
    simp [Finset.mem_map_equiv]
  · intro S _
    ext x
    simp [Finset.mem_map_equiv]

/-! ## 2. Two-colourings of `K n`, their density, and the minimum `a n` -/

/-- A labelled two-colouring of the complete graph on `Fin n`: a symmetric Boolean matrix
with a fixed dummy diagonal (the diagonal is not an edge colour). -/
def IsCol {n : ℕ} (G : Fin n → Fin n → Bool) : Prop :=
  (∀ x y, G x y = G y x) ∧ ∀ x, G x x = false

instance decIsCol {n : ℕ} : DecidablePred (IsCol (n := n)) :=
  fun G => by unfold IsCol; infer_instance

/-- All two-colourings of `K n`, as a finite set. -/
def cols (n : ℕ) : Finset (Fin n → Fin n → Bool) := univ.filter IsCol

lemma blue_mem (n : ℕ) : (fun _ _ : Fin n => false) ∈ cols n := by
  simp [cols, IsCol]

lemma cols_nonempty (n : ℕ) : (cols n).Nonempty := ⟨_, blue_mem n⟩

/-- Monochromatic `K₄` density of an `n`-vertex two-colouring.  For `n < 4` the denominator
is `0`, so this is a deliberate zero-extension. -/
def density {n : ℕ} (G : Fin n → Fin n → Bool) : ℚ :=
  (m4 G : ℚ) / (n.choose 4 : ℚ)

/-- The finite set of densities realised at order `n`. -/
def densities (n : ℕ) : Finset ℚ := (cols n).image density

lemma densities_nonempty (n : ℕ) : (densities n).Nonempty :=
  (cols_nonempty n).image _

/-- **`a n`**: the minimum monochromatic-`K₄` density over all `n`-vertex two-colourings. -/
def a (n : ℕ) : ℚ := (densities n).min' (densities_nonempty n)

lemma a_le_density {n : ℕ} {G : Fin n → Fin n → Bool} (hG : G ∈ cols n) :
    a n ≤ density G :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hG)

lemma exists_density_eq_a (n : ℕ) : ∃ G ∈ cols n, density G = a n := by
  have h : a n ∈ densities n := Finset.min'_mem (densities n) (densities_nonempty n)
  unfold densities at h
  rw [Finset.mem_image] at h
  obtain ⟨G, hG, hGd⟩ := h
  exact ⟨G, hG, hGd⟩

lemma density_nonneg {n : ℕ} (G : Fin n → Fin n → Bool) : 0 ≤ density G := by
  unfold density
  positivity

lemma density_le_one {n : ℕ} (G : Fin n → Fin n → Bool) : density G ≤ 1 := by
  unfold density
  rcases Nat.lt_or_ge n 4 with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp
  · have hpos : 0 < n.choose 4 := Nat.choose_pos h
    have hq : (0 : ℚ) < (n.choose 4 : ℚ) := by exact_mod_cast hpos
    rw [div_le_one hq]
    have := m4_le (V := Fin n) G
    rw [Fintype.card_fin] at this
    exact_mod_cast this

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  obtain ⟨G, _, hG⟩ := exists_density_eq_a n
  rw [← hG]
  exact density_nonneg G

lemma a_le_one (n : ℕ) : a n ≤ 1 := by
  obtain ⟨G, _, hG⟩ := exists_density_eq_a n
  rw [← hG]
  exact density_le_one G

lemma a_of_lt_four {n : ℕ} (h : n < 4) : a n = 0 := by
  refine le_antisymm ?_ (a_nonneg n)
  refine le_trans (a_le_density (blue_mem n)) ?_
  unfold density
  rw [Nat.choose_eq_zero_of_lt h]
  simp

/-! ## 3. Vertex deletion and the averaging step -/

/-- Delete vertex `i`: pull the colouring back along `i.succAbove`. -/
def del {n : ℕ} (i : Fin (n + 1)) (G : Fin (n + 1) → Fin (n + 1) → Bool) :
    Fin n → Fin n → Bool := fun x y => G (i.succAbove x) (i.succAbove y)

lemma del_mem_cols {n : ℕ} {G : Fin (n + 1) → Fin (n + 1) → Bool} (hG : G ∈ cols (n + 1))
    (i : Fin (n + 1)) : del i G ∈ cols n := by
  simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and, IsCol] at hG ⊢
  exact ⟨fun x y => hG.1 _ _, fun x => hG.2 _⟩

/-- The four-sets avoiding `i`, transported to four-sets of the deleted graph. -/
lemma map_filter_succAbove {n : ℕ} {i : Fin (n + 1)} {T : Finset (Fin (n + 1))} (hiT : i ∉ T) :
    ((univ : Finset (Fin n)).filter (fun x => i.succAbove x ∈ T)).map (Fin.succAboveEmb i) = T := by
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.coe_succAboveEmb]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    have hyi : y ≠ i := fun h => hiT (h ▸ hy)
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hyi
    exact ⟨z, by rw [hz]; exact hy, hz⟩

/-- **`M₄` of a deletion** counts the monochromatic four-sets of `G` that avoid `i`. -/
lemma m4_del {n : ℕ} (G : Fin (n + 1) → Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    m4 (del i G) =
      ((((univ : Finset (Fin (n + 1))).powersetCard 4).filter (Mono G)).filter
        (fun S => i ∉ S)).card := by
  unfold m4
  refine Finset.card_nbij' (i := fun S : Finset (Fin n) => S.map (Fin.succAboveEmb i))
    (j := fun T : Finset (Fin (n + 1)) =>
      (univ : Finset (Fin n)).filter (fun x => i.succAbove x ∈ T)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_powersetCard_univ] at hS ⊢
    refine ⟨⟨by rw [Finset.card_map]; exact hS.1, ?_⟩, ?_⟩
    · exact (mono_map (Fin.succAboveEmb i) G S).1 hS.2
    · simp only [Finset.mem_map, Fin.coe_succAboveEmb, not_exists]
      rintro x ⟨-, hx⟩
      exact Fin.succAbove_ne i x hx
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_powersetCard_univ] at hT ⊢
    obtain ⟨⟨hcard, hmono⟩, hiT⟩ := hT
    have hmap := map_filter_succAbove (i := i) hiT
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_map (Fin.succAboveEmb i), hmap, hcard]
    · have hpull :
          Mono (fun x y : Fin n => G ((Fin.succAboveEmb i) x) ((Fin.succAboveEmb i) y))
            ((univ : Finset (Fin n)).filter (fun x => i.succAbove x ∈ T)) := by
        apply (mono_map (Fin.succAboveEmb i) G _).2
        rwa [hmap]
      change Mono (fun x y : Fin n => G (i.succAbove x) (i.succAbove y)) _
      simpa only [Fin.coe_succAboveEmb] using hpull
  · intro S _
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.coe_succAboveEmb]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rwa [Fin.succAbove_right_injective hxy] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hT
    exact map_filter_succAbove hT.2

/-- Generic incidence count: a four-set of an `(c+4)`-element vertex type avoids exactly
`c` vertices. -/
lemma sum_card_avoid {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ}
    (hV : Fintype.card V = c + 4) (F : Finset (Finset V)) (hF : ∀ S ∈ F, S.card = 4) :
    ∑ _i : V, (F.filter (fun S => _i ∉ S)).card = c * F.card := by
  have h1 : ∀ i : V, (F.filter (fun S => i ∉ S)).card = ∑ S ∈ F, if i ∉ S then 1 else 0 :=
    fun i => Finset.card_filter _ _
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ S ∈ F, (∑ _i : V, if _i ∉ S then 1 else 0) = c := by
    intro S hS
    rw [← Finset.card_filter]
    have h3 : ((univ : Finset V).filter (fun x => x ∉ S)) = Sᶜ := by
      ext x
      simp
    rw [h3, Finset.card_compl, hF S hS, hV]
    omega
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]

/-- **The numerator double count.** -/
lemma sum_m4_del {k : ℕ} (G : Fin (k + 5) → Fin (k + 5) → Bool) :
    ∑ i : Fin (k + 5), m4 (del i G) = (k + 1) * m4 G := by
  have h : ∀ i : Fin (k + 5), m4 (del i G) =
      ((((univ : Finset (Fin (k + 5))).powersetCard 4).filter (Mono G)).filter
        (fun S => i ∉ S)).card := fun i => m4_del G i
  simp_rw [h]
  have hcard : Fintype.card (Fin (k + 5)) = (k + 1) + 4 := by
    rw [Fintype.card_fin]
  refine sum_card_avoid hcard _ ?_
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powersetCard_univ] at hS
  exact hS.1

/-- Every four-set is monochromatic in the all-blue colouring. -/
lemma m4_false {V : Type*} [Fintype V] [DecidableEq V] :
    m4 (fun _ _ : V => false) = (Fintype.card V).choose 4 := by
  unfold m4
  rw [Finset.filter_true_of_mem (fun S _ => ⟨false, fun _ _ _ _ _ => rfl⟩),
    Finset.card_powersetCard, Finset.card_univ]

/-- **The denominator identity**, obtained from the double count applied to the all-blue
colouring: `(n+1)·C(n,4) = (n-3)·C(n+1,4)`. -/
lemma choose_step (k : ℕ) : (k + 5) * (k + 4).choose 4 = (k + 1) * (k + 5).choose 4 := by
  have h := sum_m4_del (fun _ _ : Fin (k + 5) => false)
  have hdel : ∀ i : Fin (k + 5),
      del i (fun _ _ : Fin (k + 5) => false) = fun _ _ : Fin (k + 4) => false := fun _ => rfl
  simp_rw [hdel, m4_false, Fintype.card_fin] at h
  simpa using h

lemma choose_four_pos (k : ℕ) : 0 < (k + 4).choose 4 := Nat.choose_pos (by omega)

/-- **The averaging identity**: the deletions of an `(n+1)`-vertex graph have average
density equal to the graph's own density. -/
lemma sum_density_del {k : ℕ} (G : Fin (k + 5) → Fin (k + 5) → Bool) :
    ∑ i : Fin (k + 5), density (del i G) = ((k : ℚ) + 5) * density G := by
  have hBpos : (0 : ℚ) < (((k + 4).choose 4 : ℕ) : ℚ) := by
    exact_mod_cast choose_four_pos k
  have hCpos : (0 : ℚ) < (((k + 5).choose 4 : ℕ) : ℚ) := by
    have : 0 < (k + 5).choose 4 := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hnum : (∑ i : Fin (k + 5), (m4 (del i G) : ℚ)) = ((k : ℚ) + 1) * (m4 G : ℚ) := by
    have h : ((∑ i : Fin (k + 5), m4 (del i G) : ℕ) : ℚ) = (((k + 1) * m4 G : ℕ) : ℚ) := by
      rw [sum_m4_del]
    push_cast at h
    exact h
  have hstep : ((k : ℚ) + 5) * (((k + 4).choose 4 : ℕ) : ℚ)
      = ((k : ℚ) + 1) * (((k + 5).choose 4 : ℕ) : ℚ) := by
    have h : (((k + 5) * (k + 4).choose 4 : ℕ) : ℚ) = (((k + 1) * (k + 5).choose 4 : ℕ) : ℚ) := by
      rw [choose_step]
    push_cast at h
    linarith [h]
  unfold density
  rw [← Finset.sum_div, hnum]
  field_simp [ne_of_gt hBpos, ne_of_gt hCpos]
  have hm := congrArg (fun x : ℚ => x * (m4 G : ℚ)) hstep
  nlinarith [hm]

/-- Some deletion is no denser than the graph itself. -/
lemma exists_del_le {k : ℕ} (G : Fin (k + 5) → Fin (k + 5) → Bool) :
    ∃ i : Fin (k + 5), density (del i G) ≤ density G := by
  by_contra hcon
  push Not at hcon
  have hne : (univ : Finset (Fin (k + 5))).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hlt : ∑ _i : Fin (k + 5), density G < ∑ i : Fin (k + 5), density (del i G) :=
    Finset.sum_lt_sum_of_nonempty hne (fun i _ => hcon i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_density_del] at hlt
  push_cast at hlt
  exact lt_irrefl _ hlt

/-! ## 4. `a` is nondecreasing -/

/-- **Result 1.** The minimum density is nondecreasing from `n = 4` on. -/
theorem a_step_mono {n : ℕ} (hn : 4 ≤ n) : a n ≤ a (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  obtain ⟨G, hG, hGa⟩ := exists_density_eq_a (k + 5)
  obtain ⟨i, hi⟩ := exists_del_le G
  calc a (k + 4) ≤ density (del i G) := a_le_density (del_mem_cols hG i)
    _ ≤ density G := hi
    _ = a (k + 5) := hGa

/-- The zero-extension below `4` keeps `a` monotone everywhere. -/
theorem a_monotone : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases Nat.lt_or_ge n 4 with h | h
  · rw [a_of_lt_four h]
    exact a_nonneg _
  · exact a_step_mono h

/-! ## 5. The limit `c₄` — the only `ℝ` in the development -/

/-- **`c₄`**, the limit of the nondecreasing bounded sequence `a`. -/
noncomputable def c4 : ℝ := ⨆ n : ℕ, ((a n : ℚ) : ℝ)

lemma monotone_aR : Monotone (fun n : ℕ => ((a n : ℚ) : ℝ)) := by
  intro p q h
  exact (Rat.cast_le (K := ℝ)).2 (a_monotone h)

lemma bddAbove_aR : BddAbove (Set.range fun n : ℕ => ((a n : ℚ) : ℝ)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  simpa using ((Rat.cast_le (K := ℝ)).2 (a_le_one n))

/-- **Result 2.** `a n` converges, and its limit is `c₄`. -/
theorem tendsto_a_c4 :
    Filter.Tendsto (fun n : ℕ => ((a n : ℚ) : ℝ)) Filter.atTop (nhds c4) :=
  tendsto_atTop_ciSup monotone_aR bddAbove_aR

theorem c4_exists :
    ∃ c : ℝ, Filter.Tendsto (fun n : ℕ => ((a n : ℚ) : ℝ)) Filter.atTop (nhds c) :=
  ⟨c4, tendsto_a_c4⟩

/-! ## 6. A hand-checkable small value -/

/-- A `K₄` colouring with exactly one red edge. -/
def oneRed4 (i j : Fin 4) : Bool :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then true else false

/-- Its unique four-set has both colours, hence is not monochromatic. -/
lemma oneRed4_m4 : m4 oneRed4 = 0 := by decide

lemma a_le_zero_of_m4_eq_zero {n : ℕ} {G : Fin n → Fin n → Bool} (hG : G ∈ cols n)
    (hM : m4 G = 0) : a n ≤ 0 := by
  calc a n ≤ density G := a_le_density hG
    _ = 0 := by simp [density, hM]

/-- Membership in `cols n` is exactly the structural colouring predicate `IsCol`.

**Why the `IsCol`-facing lemmas exist.**  When the elaborator checks an argument against
an expected type `_ ∈ cols k` with `k` a *closed numeral*, it puts that proposition in
weak-head normal form, and the descent `SetLike.instMembership → Set.instMembership →
Finset.instSetLike → Multiset.instMembership → Quot.liftOn` is forced.  Iota-reducing
`Quot.lift` needs its multiset in constructor form, so whnf evaluates `(cols k).val`,
hence `Finset.univ.val`, hence `Multiset.pi` over all `2 ^ (k * k)` functions
`Fin k → Fin k → Bool`.  Measured: fine for `k ≤ 2`, dead at `k = 3` (512) and `k = 4`
(65536).  The work is bounded, so a larger `maxHeartbeats` is the wrong remedy.

This bridge is safe because it is stated *and applied* only at a variable `n`, where
`cols n` is stuck and whnf gives up at once; `IsCol` carries no `Finset`, so the lemmas
below can be instantiated at a numeral for free. -/
lemma mem_cols_iff {n : ℕ} {G : Fin n → Fin n → Bool} : G ∈ cols n ↔ IsCol G := by
  simp [cols]

/-- `IsCol`-flavoured `a_le_zero_of_m4_eq_zero`: no `Finset` in the hypothesis. -/
lemma a_le_zero_of_isCol {n : ℕ} {G : Fin n → Fin n → Bool} (hG : IsCol G)
    (hM : m4 G = 0) : a n ≤ 0 :=
  a_le_zero_of_m4_eq_zero (mem_cols_iff.2 hG) hM

/-- `oneRed4` really is a colouring: 16 symmetry checks and 4 diagonal checks, so this
`decide` is 20 boolean tests, not an enumeration of `cols 4`. -/
lemma oneRed4_iscol : IsCol oneRed4 := by decide

/-- **`a 4 = 0`.**  The one-red-edge colouring of `K₄` has no monochromatic four-set,
so the minimum monochromatic-`K₄` density at order `4` is `0`.  This pins `a` to a value
checkable by hand: `K₄` has a single four-set, and one differently-coloured edge kills it. -/
theorem a_four : a 4 = 0 :=
  le_antisymm (a_le_zero_of_isCol oneRed4_iscol oneRed4_m4) (a_nonneg 4)

/-- All-blue `K₄`: its unique four-set is monochromatic, so `M₄ = 1`. -/
lemma m4_blue_four : m4 (fun _ _ : Fin 4 => false) = 1 :=
  (m4_false (V := Fin 4)).trans (by decide)

/-- All-blue `K₅`: all `C(5,4) = 5` four-sets are monochromatic.  This is the same number
the imported file checks for a one-block red clique of size five. -/
lemma m4_blue_five : m4 (fun _ _ : Fin 5 => false) = 5 :=
  (m4_false (V := Fin 5)).trans (by decide)

/-- The all-blue graph has density exactly `1`, pinning the denominator convention. -/
lemma density_blue_five : density (fun _ _ : Fin 5 => false) = 1 := by
  unfold density
  rw [m4_blue_five, show Nat.choose 5 4 = 5 from by decide]
  norm_num

/-! ## 7. Transporting `M₄` from the blow-up type to `Fin (Qw v)`

The imported `M4` is stated over `Blow v = Σ i, Fin (v i)`, while `a` ranges over
colourings of `Fin n`.  `Fintype.equivFinOfCardEq (card_blow v)` is the cardinality
bijection, and `m4_equiv` transports the count along it. -/

open Lea.RamseyLifting in
lemma m4_blow {m : ℕ} (A : Fin m → Fin m → Bool) (v : Fin m → ℕ) :
    m4 (fun u x : Blow v => A u.1 x.1) = M4 A v := by
  unfold m4 M4
  congr 1
  exact Finset.filter_congr (fun S _ => Iff.rfl)

open Lea.RamseyLifting in
/-- The blow-up as a labelled colouring of `K (Qw v)`.  Only genuine self-pairs are
patched to `false`; two DISTINCT vertices of one block keep the diagonal colour `A i i`. -/
noncomputable def blowCol {m : ℕ} (A : Fin m → Fin m → Bool) (v : Fin m → ℕ) :
    Fin (Qw v) → Fin (Qw v) → Bool :=
  fun x y => if x = y then false else
    A ((Fintype.equivFinOfCardEq (card_blow v)).symm x).1
      ((Fintype.equivFinOfCardEq (card_blow v)).symm y).1

open Lea.RamseyLifting in
lemma blowCol_mem_cols {m : ℕ} {A : Fin m → Fin m → Bool} (hA : ∀ i j, A i j = A j i)
    (v : Fin m → ℕ) : blowCol A v ∈ cols (Qw v) := by
  simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and, IsCol]
  constructor
  · intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · simp [blowCol, hxy, Ne.symm hxy, hA]
  · intro x
    simp [blowCol]

open Lea.RamseyLifting in
/-- **The transport identity.**  The blow-up's finite-graph `M₄` is exactly the imported
`M4 A v`. -/
lemma m4_blowCol {m : ℕ} {A : Fin m → Fin m → Bool} (v : Fin m → ℕ) :
    m4 (blowCol A v) = M4 A v := by
  let e : Blow v ≃ Fin (Qw v) := Fintype.equivFinOfCardEq (card_blow v)
  calc
    m4 (blowCol A v) =
        m4 (fun x y : Fin (Qw v) => A (e.symm x).1 (e.symm y).1) := by
      apply m4_congr
      intro x y hxy
      simp [blowCol, e, hxy]
    _ = m4 (fun u x : Blow v => A u.1 x.1) :=
      m4_equiv e (fun u x : Blow v => A u.1 x.1)
    _ = M4 A v := m4_blow A v

open Lea.RamseyLifting in
/-- `a` at the blow-up's order is at most the blow-up's own density. -/
theorem a_le_blow {m : ℕ} {A : Fin m → Fin m → Bool} (hA : ∀ i j, A i j = A j i)
    (v : Fin m → ℕ) :
    a (Qw v) ≤ (M4 A v : ℚ) / (((Qw v).choose 4 : ℕ) : ℚ) := by
  simpa only [density, m4_blowCol] using (a_le_density (blowCol_mem_cols hA v))

/-! ## 8. `c₄ ≤ P` -/

open Lea.RamseyLifting in
/-- **Every `a n` is already at most `P`**, still entirely in `ℚ`: push `n` up the
nondecreasing sequence to a blow-up order `tQ`, where the imported estimate applies. -/
theorem a_le_Pval {m : ℕ} {A : Fin m → Fin m → Bool} (hA : ∀ i j, A i j = A j i)
    (w : Fin m → ℕ) (hQ : 0 < Qw w) (n : ℕ) : a n ≤ Pval A w := by
  by_contra hcon
  push Not at hcon
  set ε : ℚ := a n - Pval A w with hεdef
  have hεpos : 0 < ε := sub_pos.2 hcon
  obtain ⟨T0, hT0⟩ := exists_nat_gt (6 / ε)
  set t : ℕ := max (max n 4) (T0 + 1) with htdef
  have htpos : 0 < t := by omega
  have htQ : t ≤ t * Qw w := Nat.le_mul_of_pos_right t hQ
  have hN : 4 ≤ t * Qw w := le_trans (by omega) htQ
  have hnle : n ≤ t * Qw w := le_trans (by omega) htQ
  -- monotonicity pushes `n` up to the blow-up order
  have h1 : a n ≤ a (t * Qw w) := a_monotone hnle
  -- the blow-up realises a colouring of that order
  have h2 : a (t * Qw w)
      ≤ (M4 A (fun i => t * w i) : ℚ) / (((t * Qw w).choose 4 : ℕ) : ℚ) := by
    have h := a_le_blow hA (fun i => t * w i)
    rwa [Qw_smul] at h
  -- the imported lifting bound
  have h3 := lifting_bound hA w t htpos hQ hN
  have h4 : (M4 A (fun i => t * w i) : ℚ) / (((t * Qw w).choose 4 : ℕ) : ℚ)
      ≤ Pval A w + 6 / ((t * Qw w : ℕ) : ℚ) := by
    have := (abs_le.1 h3).2
    linarith
  -- the error term is smaller than the gap
  have hNq : (0 : ℚ) < ((t * Qw w : ℕ) : ℚ) := by
    have : 0 < t * Qw w := by omega
    exact_mod_cast this
  have hTt : (6 : ℚ) / ε < ((t * Qw w : ℕ) : ℚ) := by
    have hT0t : (T0 : ℚ) ≤ ((t * Qw w : ℕ) : ℚ) := by
      have : T0 ≤ t * Qw w := le_trans (by omega) htQ
      exact_mod_cast this
    linarith
  have h5 : 6 / ((t * Qw w : ℕ) : ℚ) < ε := by
    rw [div_lt_iff₀ hNq]
    rw [div_lt_iff₀ hεpos] at hTt
    linarith
  linarith

/-- **Result 3 — the conclusion of `LIFTING.md`.**  For every symmetric template with
positive total weight, `c₄ ≤ P(A,w)`. -/
theorem c4_le_Pval {m : ℕ} {A : Fin m → Fin m → Bool} (hA : ∀ i j, A i j = A j i)
    (w : Fin m → ℕ) (hQ : 0 < Lea.RamseyLifting.Qw w) :
    c4 ≤ ((Lea.RamseyLifting.Pval A w : ℚ) : ℝ) := by
  unfold c4
  refine ciSup_le (fun n => ?_)
  exact (Rat.cast_le (K := ℝ)).2 (a_le_Pval hA w hQ n)

end Lea.RamseyC4

/-! ## 9. Axiom audit -/

#print axioms Lea.RamseyC4.a_step_mono
#print axioms Lea.RamseyC4.a_monotone
#print axioms Lea.RamseyC4.tendsto_a_c4
#print axioms Lea.RamseyC4.c4_exists
#print axioms Lea.RamseyC4.a_le_Pval
#print axioms Lea.RamseyC4.c4_le_Pval
#print axioms Lea.RamseyC4.m4_blowCol
#print axioms Lea.RamseyC4.a_four
#print axioms Lea.RamseyC4.m4_blue_five
