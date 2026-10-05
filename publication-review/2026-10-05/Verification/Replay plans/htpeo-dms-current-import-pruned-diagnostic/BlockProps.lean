/-
  BlockProps.lean — the cyclic block graphs of `BlockStar` in the vocabulary of the DMS chain:
  `MGraph.Loopless`, `MGraph.Subcubic`, `MGraph.Colourable`, and the statement `RH2F.DMS`.

  * `BG_ends`           — read-back of the edge list: edge `(J, s)` joins `(J, src s)` and `((J + jmp s) mod n, dst s)`;
  * `BG_loopless`       — no loops, if jumps are smaller than `n` and edges inside a block join different types;
  * `BG_subcubic`       — at most three edges at every vertex, by a Boolean degree check on windows of `D + 1` blocks;
  * `colourable_of_star`— a star colouring with `k ≤ k'` colours gives `Colourable P k'` for every edge set `P`;
  * `dms_iff`           — `RH2F.DMS` is literally `∀ G, DMSfor G`; the family theorems prove `DMSfor G` for their graphs
                          (together with the hypotheses `Subcubic`, `Loopless`).
-/
import BlockStar
import StarReduce
import MhFact_5c1eb3f583cf643f
import MhFact_341b6e5e1be16205

namespace BlockStar

variable {W C : Type} {r q : Nat}

/-- the instance of the Dvořák–Mohar–Šámal conjecture for one multigraph `G`
    (the body of `RH2F.DMS`, which quantifies over all `G`) -/
def DMSfor (G : MGraph) : Prop := G.Subcubic → G.Loopless → ∀ P : Fin G.m → Prop, MGraph.Colourable P 6

theorem dms_iff : RH2F.DMS ↔ ∀ G : MGraph, DMSfor G := Iff.rfl

theorem colourable_of_star {G : MGraph} {k k' : Nat} {c : Fin G.m → Fin k} (h : G.Star k c) (hk : k ≤ k') :
    ∀ P : Fin G.m → Prop, MGraph.Colourable P k' := by
  intro P
  refine ⟨fun f => Fin.castLE hk (c f), ?_⟩
  have h' : MGraph.StarOn P k c :=
    ⟨fun a b hab _ _ => h.1 a b hab trivial trivial, fun w _ _ _ _ => h.2 w trivial trivial trivial trivial⟩
  exact MGraph.starOn_map (Fin.castLE hk) (fun x y hxy => Fin.castLE_injective hk hxy) h'

theorem dmsfor_of_star {G : MGraph} {k : Nat} {c : Fin G.m → Fin k} (h : G.Star k c) (hk : k ≤ 6) : DMSfor G :=
  fun _ _ => colourable_of_star h hk

theorem sq_lt {n q : Nat} (e : Fin (n * q)) : e.val % q < q := by
  have he : e.val < n * q := e.isLt
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by
    have h2 : n * q = 0 := by simp [h]
    omega))

/-- read-back of the edge list of the cyclic block graph -/
theorem BG_ends (Wr : Wir W r q) (n : Nat) (ω : Nat → W) (J s : Nat) (hJ : J < n) (hs : s < q) :
    ∃ h : J * q + s < n * q,
      ((BG Wr n ω).ends ⟨J * q + s, h⟩).1.val = J * r + Wr.src (ω J) s ∧
      ((BG Wr n ω).ends ⟨J * q + s, h⟩).2.val = ((J + Wr.jmp (ω J) s) % n) * r + Wr.dst (ω J) s := by
  have d := dm (J := J) hs
  refine ⟨vtx_lt hJ hs, ?_, ?_⟩
  · show (J * q + s) / q * r + Wr.src (ω ((J * q + s) / q)) ((J * q + s) % q) = _
    rw [d.1, d.2]
  · show (((J * q + s) / q + Wr.jmp (ω ((J * q + s) / q)) ((J * q + s) % q)) % n) * r +
      Wr.dst (ω ((J * q + s) / q)) ((J * q + s) % q) = _
    rw [d.1, d.2]

theorem modc' {n j p : Nat} (hj : j < n) (hp : p ≤ n) :
    (j + p) % n = if j + p < n then j + p else j + p - n := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

theorem BG_loopless (Wr : Wir W r q) (n : Nat) (ω : Nat → W) (hn : Wr.D < n)
    (h : ∀ w s, s < q → Wr.jmp w s = 0 → Wr.src w s ≠ Wr.dst w s) : (BG Wr n ω).Loopless := by
  intro e heq
  have hv : ((BG Wr n ω).ends e).1.val = ((BG Wr n ω).ends e).2.val := by rw [heq]
  have ht : ((BG Wr n ω).ends e).1.val = (e.val / q) * r + Wr.src (ω (e.val / q)) (e.val % q) := rfl
  have hh : ((BG Wr n ω).ends e).2.val =
      ((e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n) * r + Wr.dst (ω (e.val / q)) (e.val % q) := rfl
  have dt := dm (J := e.val / q) (Wr.hsrc (ω (e.val / q)) (e.val % q))
  have dh := dm (J := (e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n)
    (Wr.hdst (ω (e.val / q)) (e.val % q))
  rw [ht, hh] at hv
  have h1 : e.val / q = (e.val / q + Wr.jmp (ω (e.val / q)) (e.val % q)) % n := by
    have := congrArg (fun x => x / r) hv
    simp only [dt.1, dh.1] at this
    exact this
  have h2 : Wr.src (ω (e.val / q)) (e.val % q) = Wr.dst (ω (e.val / q)) (e.val % q) := by
    have := congrArg (fun x => x % r) hv
    simp only [dt.2, dh.2] at this
    exact this
  have hjm := Wr.hjmp (ω (e.val / q)) (e.val % q)
  by_cases hz : Wr.jmp (ω (e.val / q)) (e.val % q) = 0
  · exact h _ _ (sq_lt e) hz h2
  · rw [modc' (blk_lt e) (by omega)] at h1
    split_ifs at h1 <;> omega

section Deg
variable (Wr : Wir W r q) (wk : Nat → W)

/-- in a window of `D + 1` blocks: the edges `(o, s)` incident with the vertex `(D, t)` -/
def cands (t : Nat) : List (Nat × Nat) :=
  (List.range (Wr.D + 1)).flatMap fun o =>
    ((List.range q).filter fun s => atB Wr wk o s false Wr.D t || atB Wr wk o s true Wr.D t).map fun s => (o, s)

/-- every vertex of the last block of the window has at most three incident edges -/
def degOK : Bool := allB r fun t => decide ((cands Wr wk t).length ≤ 3)

end Deg

theorem BG_subcubic (Wr : Wir W r q) (n : Nat) (ω : Nat → W)
    (H : ∀ j, j < n → ∃ wk : Nat → W, (∀ p, p ≤ Wr.D → wk p = ω ((j + p) % n)) ∧ degOK Wr wk = true) :
    (BG Wr n ω).Subcubic := by
  intro x a b c d ha hb hc hd hab hac had hbc hbd hcd
  have hx : x.val < n * r := x.isLt
  have hJ : x.val / r < n := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hx (Nat.mul_comm n r))
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hJ
  have hr : 0 < r := Nat.pos_of_ne_zero (fun h => by
    have h2 : n * r = 0 := by simp [h]
    omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨wk, hag, hok⟩ := H ((x.val / r + m * Wr.D) % (m + 1)) (Nat.mod_lt _ hn)
  have hb' : ∀ p, ((x.val / r + m * Wr.D) % (m + 1) + p) % (m + 1) < m + 1 := fun p => Nat.mod_lt _ hn
  have hs : ∀ p d', (((x.val / r + m * Wr.D) % (m + 1) + p) % (m + 1) + d') % (m + 1) =
      ((x.val / r + m * Wr.D) % (m + 1) + (p + d')) % (m + 1) := by
    intro p d'
    rw [Nat.mod_add_mod, Nat.add_assoc]
  have hxb : x.val / r = ((x.val / r + m * Wr.D) % (m + 1) + Wr.D) % (m + 1) := by
    rw [Nat.mod_add_mod, Nat.add_assoc, ← Nat.succ_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJ]
  have mem : ∀ e : Fin (BG Wr (m + 1) ω).m, (BG Wr (m + 1) ω).Inc e x →
      ∃ o, e.val / q = ((x.val / r + m * Wr.D) % (m + 1) + o) % (m + 1) ∧
        (o, e.val % q) ∈ cands Wr wk (x.val % r) := by
    intro e he
    obtain ⟨o, hd', hm, hat, hq⟩ := liftI Wr (m + 1) ω
      (fun p => ((x.val / r + m * Wr.D) % (m + 1) + p) % (m + 1)) wk hb' hs e x he Wr.D (Nat.le_refl _) hag hxb
    have ho : o ≤ Wr.D := by rcases hm with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    refine ⟨o, hq, ?_⟩
    have hpred : (atB Wr wk o (e.val % q) false Wr.D (x.val % r) ||
        atB Wr wk o (e.val % q) true Wr.D (x.val % r)) = true := by
      rcases hm with ⟨rfl, _⟩ | ⟨rfl, _, _⟩
      · simp only [hat, Bool.true_or]
      · simp only [hat, Bool.or_true]
    simp only [cands, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
    exact ⟨o, by omega, e.val % q, ⟨sq_lt e, hpred⟩, rfl⟩
  obtain ⟨oa, qa, ma⟩ := mem a ha
  obtain ⟨ob, qb, mb⟩ := mem b hb
  obtain ⟨oc, qc, mc⟩ := mem c hc
  obtain ⟨od, qd, md⟩ := mem d hd
  have ne : ∀ (e e' : Fin (BG Wr (m + 1) ω).m) (o o' : Nat), e ≠ e' →
      e.val / q = ((x.val / r + m * Wr.D) % (m + 1) + o) % (m + 1) →
      e'.val / q = ((x.val / r + m * Wr.D) % (m + 1) + o') % (m + 1) →
      (o, e.val % q) ≠ (o', e'.val % q) := by
    intro e e' o o' hne h1 h2 heq
    exact hne (edge_ext (q := q) (by rw [h1, h2, (Prod.mk.inj heq).1]) (Prod.mk.inj heq).2)
  have k1 : (cands Wr wk (x.val % r)).length ≤ 3 :=
    of_decide_eq_true (allB_spec hok (x.val % r) (Nat.mod_lt _ hr))
  have hnd : [(oa, a.val % q), (ob, b.val % q), (oc, c.val % q), (od, d.val % q)].Nodup := by
    simp [ne a b oa ob hab qa qb, ne a c oa oc hac qa qc, ne a d oa od had qa qd,
      ne b c ob oc hbc qb qc, ne b d ob od hbd qb qd, ne c d oc od hcd qc qd]
  have hsub : [(oa, a.val % q), (ob, b.val % q), (oc, c.val % q), (od, d.val % q)] ⊆
      cands Wr wk (x.val % r) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hlen := (List.subperm_of_subset hnd hsub).length_le
  simp only [List.length_cons, List.length_nil] at hlen
  omega

end BlockStar
