import InflationB

namespace Inflation

variable (H : MGraph) (slot : Fin H.m → Bool → Fin 3)
variable (φ : Fin H.m → Fin 5) (ρ : Fin H.n → Fin 5 → Fin 5)

def inflCol (f : Fin (inflate H slot).m) : Fin 5 :=
  if h : f.val < H.n * 12 then
    ρ ⟨f.val / 12, by omega⟩ (kappa ⟨f.val % 12, by omega⟩)
  else φ ⟨f.val - H.n * 12, by have hf : f.val < H.n * 12 + H.m := f.isLt; omega⟩

def inflSeen (x : Fin (inflate H slot).n) : Finset (Fin 5) :=
  (seen ⟨x.val % 9, by omega⟩).image (ρ ⟨x.val / 9, by have hx : x.val < H.n * 9 := x.isLt; omega⟩)

theorem color_piece (X : Fin H.n) (s : Fin 12) :
    inflCol H slot φ ρ (mkPE H slot X s) = ρ X (kappa s) := by
  have hs := s.isLt
  have hX := X.isLt
  have h : X.val * 12 + s.val < H.n * 12 := by omega
  have hd : (X.val * 12 + s.val) / 12 = X.val := by omega
  have hm : (X.val * 12 + s.val) % 12 = s.val := by omega
  simp [inflCol, mkPE, h, hd, hm]

theorem color_inter (e : Fin H.m) :
    inflCol H slot φ ρ (mkIE H slot e) = φ e := by
  have h : ¬ H.n * 12 + e.val < H.n * 12 := by omega
  simp [inflCol, mkIE, h]

theorem seen_mkIV (X : Fin H.n) (a : Fin 9) :
    inflSeen H slot ρ (mkIV H slot X a) = (seen a).image (ρ X) := by
  have ha := a.isLt
  have hd : (X.val * 9 + a.val) / 9 = X.val := by omega
  have hm : (X.val * 9 + a.val) % 9 = a.val := by omega
  simp [inflSeen, mkIV, mkV, hd, hm]

theorem piece_inc_iff (X : Fin H.n) (s : Fin 12)
    (x : Fin (inflate H slot).n) :
    (inflate H slot).Inc (mkPE H slot X s) x ↔
      x = mkIV H slot X (pe1 s.val) ∨ x = mkIV H slot X (pe2 s.val) := by
  simp [MGraph.Inc, piece_ends, eq_comm]

theorem inter_inc_iff (e : Fin H.m) (x : Fin (inflate H slot).n) :
    (inflate H slot).Inc (mkIE H slot e) x ↔
      x = mkIV H slot (endOf H e false) (portv (slot e false)) ∨
      x = mkIV H slot (endOf H e true) (portv (slot e true)) := by
  simp [MGraph.Inc, inter_ends, eq_comm]

theorem inter_unique_sides (hinj : PortsInj H slot)
    (e f : Fin H.m) (b b' : Bool)
    (h : mkIV H slot (endOf H e b) (portv (slot e b)) =
         mkIV H slot (endOf H f b') (portv (slot f b'))) : e = f := by
  obtain ⟨hX, hp⟩ := mkIV_inj H slot h
  exact (hinj e b f b' hX (table_port_inj hp)).1

theorem inter_unique (hinj : PortsInj H slot)
    (e f : Fin H.m) (x : Fin (inflate H slot).n)
    (he : (inflate H slot).Inc (mkIE H slot e) x)
    (hf : (inflate H slot).Inc (mkIE H slot f) x) : e = f := by
  rcases (inter_inc_iff H slot e x).mp he with he | he <;>
    rcases (inter_inc_iff H slot f x).mp hf with hf | hf
  · exact inter_unique_sides H slot hinj e f false false (he.symm.trans hf)
  · exact inter_unique_sides H slot hinj e f false true (he.symm.trans hf)
  · exact inter_unique_sides H slot hinj e f true false (he.symm.trans hf)
  · exact inter_unique_sides H slot hinj e f true true (he.symm.trans hf)

theorem piece_color_mem (X : Fin H.n) (s : Fin 12)
    (x : Fin (inflate H slot).n)
    (hi : (inflate H slot).Inc (mkPE H slot X s) x) :
    inflCol H slot φ ρ (mkPE H slot X s) ∈ inflSeen H slot ρ x := by
  rcases (piece_inc_iff H slot X s x).mp hi with rfl | rfl
  · rw [color_piece, seen_mkIV]
    exact Finset.mem_image.mpr ⟨kappa s, (table_piece_mem s).1, rfl⟩
  · rw [color_piece, seen_mkIV]
    exact Finset.mem_image.mpr ⟨kappa s, (table_piece_mem s).2, rfl⟩

theorem inter_color_mem
    (hmatch : ∀ e b, ρ (endOf H e b) (pi (slot e b)) = φ e)
    (e : Fin H.m) (x : Fin (inflate H slot).n)
    (hi : (inflate H slot).Inc (mkIE H slot e) x) :
    inflCol H slot φ ρ (mkIE H slot e) ∈ inflSeen H slot ρ x := by
  rcases (inter_inc_iff H slot e x).mp hi with rfl | rfl
  · rw [color_inter, seen_mkIV, ← hmatch e false]
    exact Finset.mem_image.mpr ⟨pi (slot e false), table_port_mem _, rfl⟩
  · rw [color_inter, seen_mkIV, ← hmatch e true]
    exact Finset.mem_image.mpr ⟨pi (slot e true), table_port_mem _, rfl⟩

theorem all_color_mem
    (hmatch : ∀ e b, ρ (endOf H e b) (pi (slot e b)) = φ e) :
    ∀ f x, (inflate H slot).Inc f x →
      inflCol H slot φ ρ f ∈ inflSeen H slot ρ x := by
  intro f x hi
  rcases edge_cases H slot f with ⟨X, s, rfl⟩ | ⟨e, rfl⟩
  · exact piece_color_mem H slot φ ρ X s x hi
  · exact inter_color_mem H slot φ ρ hmatch e x hi

theorem piece_inc_mkIV (X Y : Fin H.n) (s : Fin 12) (a : Fin 9)
    (hi : (inflate H slot).Inc (mkPE H slot X s) (mkIV H slot Y a)) :
    X = Y ∧ (pe1 s.val = a ∨ pe2 s.val = a) := by
  rcases (piece_inc_iff H slot X s _).mp hi with h | h
  · obtain ⟨hX, ha⟩ := mkIV_inj H slot h.symm
    exact ⟨hX, Or.inl ha⟩
  · obtain ⟨hX, ha⟩ := mkIV_inj H slot h.symm
    exact ⟨hX, Or.inr ha⟩

theorem inter_inc_mkIV (e : Fin H.m) (X : Fin H.n) (a : Fin 9)
    (hi : (inflate H slot).Inc (mkIE H slot e) (mkIV H slot X a)) :
    ∃ b : Bool, endOf H e b = X ∧ portv (slot e b) = a := by
  rcases (inter_inc_iff H slot e _).mp hi with h | h
  · obtain ⟨hX, ha⟩ := mkIV_inj H slot h.symm
    exact ⟨false, hX, ha⟩
  · obtain ⟨hX, ha⟩ := mkIV_inj H slot h.symm
    exact ⟨true, hX, ha⟩

theorem piece_rich_local (hρ : ∀ X, Function.Injective (ρ X))
    (X : Fin H.n) (s : Fin 12) (z : Fin 5)
    (ha : z ∈ inflSeen H slot ρ (mkIV H slot X (pe1 s.val)))
    (hb : z ∈ inflSeen H slot ρ (mkIV H slot X (pe2 s.val))) :
    z = inflCol H slot φ ρ (mkPE H slot X s) := by
  rw [seen_mkIV] at ha hb
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hb
  have huv : u = v := hρ X heq.symm
  subst v
  rw [color_piece]
  exact congrArg (ρ X) (table_piece_rich s u hu hv)

theorem piece_rich (hρ : ∀ X, Function.Injective (ρ X))
    (X : Fin H.n) (s : Fin 12) (x y : Fin (inflate H slot).n)
    (hj : (inflate H slot).Joins (mkPE H slot X s) x y)
    (z : Fin 5) (hx : z ∈ inflSeen H slot ρ x)
    (hy : z ∈ inflSeen H slot ρ y) :
    z = inflCol H slot φ ρ (mkPE H slot X s) := by
  rcases hj with h | h
  · rw [piece_ends] at h
    have h1 : mkIV H slot X (pe1 s.val) = x := (Prod.mk.inj h).1
    have h2 : mkIV H slot X (pe2 s.val) = y := (Prod.mk.inj h).2
    subst x
    subst y
    exact piece_rich_local H slot φ ρ hρ X s z hx hy
  · rw [piece_ends] at h
    have h1 : mkIV H slot X (pe1 s.val) = y := (Prod.mk.inj h).1
    have h2 : mkIV H slot X (pe2 s.val) = x := (Prod.mk.inj h).2
    subst x
    subst y
    exact piece_rich_local H slot φ ρ hρ X s z hy hx

theorem piece_piece_color_ne (hρ : ∀ X, Function.Injective (ρ X))
    (X Y : Fin H.n) (s t : Fin 12) (x : Fin (inflate H slot).n)
    (hne : mkPE H slot X s ≠ mkPE H slot Y t)
    (hx : (inflate H slot).Inc (mkPE H slot X s) x)
    (hy : (inflate H slot).Inc (mkPE H slot Y t) x) :
    inflCol H slot φ ρ (mkPE H slot X s) ≠
      inflCol H slot φ ρ (mkPE H slot Y t) := by
  obtain ⟨Z, a, rfl⟩ := vertex_cases H slot x
  obtain ⟨hXZ, hs⟩ := piece_inc_mkIV H slot X Z s a hx
  obtain ⟨hYZ, ht⟩ := piece_inc_mkIV H slot Y Z t a hy
  subst X
  subst Y
  have hst : s ≠ t := by
    intro h
    subst t
    exact hne rfl
  rw [color_piece, color_piece]
  exact fun heq => table_piece_proper s t a hst hs ht (hρ Z heq)

theorem piece_inter_color_ne
    (hρ : ∀ X, Function.Injective (ρ X))
    (hmatch : ∀ e b, ρ (endOf H e b) (pi (slot e b)) = φ e)
    (X : Fin H.n) (s : Fin 12) (e : Fin H.m) (x : Fin (inflate H slot).n)
    (hx : (inflate H slot).Inc (mkPE H slot X s) x)
    (he : (inflate H slot).Inc (mkIE H slot e) x) :
    inflCol H slot φ ρ (mkPE H slot X s) ≠
      inflCol H slot φ ρ (mkIE H slot e) := by
  obtain ⟨Z, a, rfl⟩ := vertex_cases H slot x
  obtain ⟨hXZ, hs⟩ := piece_inc_mkIV H slot X Z s a hx
  obtain ⟨b, hbZ, hp⟩ := inter_inc_mkIV H slot e Z a he
  subst X
  rw [color_piece, color_inter, ← hmatch e b, hbZ]
  intro heq
  have hk := hρ Z heq
  exact table_port_proper (slot e b) s (by simpa only [hp] using hs) hk

theorem all_color_proper
    (hinj : PortsInj H slot)
    (hρ : ∀ X, Function.Injective (ρ X))
    (hmatch : ∀ e b, ρ (endOf H e b) (pi (slot e b)) = φ e) :
    ∀ a b, (inflate H slot).Adj a b →
      inflCol H slot φ ρ a ≠ inflCol H slot φ ρ b := by
  intro a b ⟨hne, x, hax, hbx⟩
  rcases edge_cases H slot a with ⟨X, s, rfl⟩ | ⟨e, rfl⟩ <;>
    rcases edge_cases H slot b with ⟨Y, t, rfl⟩ | ⟨f, rfl⟩
  · exact piece_piece_color_ne H slot φ ρ hρ X Y s t x hne hax hbx
  · exact piece_inter_color_ne H slot φ ρ hρ hmatch X s f x hax hbx
  · exact Ne.symm (piece_inter_color_ne H slot φ ρ hρ hmatch Y t e x hbx hax)
  · exact False.elim (hne (congrArg (mkIE H slot) (inter_unique H slot hinj e f x hax hbx)))

/-- A matched injective recolouring at each base vertex produces a star colouring. -/
theorem inflate_star5_of_matching
    (hinj : PortsInj H slot)
    (hρ : ∀ X, Function.Injective (ρ X))
    (hmatch : ∀ e b, ρ (endOf H e b) (pi (slot e b)) = φ e) :
    (inflate H slot).Star 5 (inflCol H slot φ ρ) := by
  apply MGraph.star_of_seen (inflate H slot) (inflCol H slot φ ρ)
    (inflSeen H slot ρ) (fun f => f.val < H.n * 12)
  · exact all_color_mem H slot φ ρ hmatch
  · exact all_color_proper H slot φ ρ hinj hρ hmatch
  · intro f x y hf hj z hx hy
    rcases edge_cases H slot f with ⟨X, s, rfl⟩ | ⟨e, rfl⟩
    · exact piece_rich H slot φ ρ hρ X s x y hj z hx hy
    · have : ¬ (mkIE H slot e).val < H.n * 12 := by
        dsimp [mkIE]
        omega
      exact False.elim (this hf)
  · intro a b x ha hb hax hbx
    rcases edge_cases H slot a with ⟨X, s, rfl⟩ | ⟨e, rfl⟩
    · have : (mkPE H slot X s).val < H.n * 12 := by
        dsimp [mkPE]
        have := X.isLt
        have := s.isLt
        omega
      exact False.elim (ha this)
    · rcases edge_cases H slot b with ⟨Y, t, rfl⟩ | ⟨f, rfl⟩
      · have : (mkPE H slot Y t).val < H.n * 12 := by
          dsimp [mkPE]
          have := Y.isLt
          have := t.isLt
          omega
        exact False.elim (hb this)
      · exact congrArg (mkIE H slot) (inter_unique H slot hinj e f x hax hbx)

end Inflation
