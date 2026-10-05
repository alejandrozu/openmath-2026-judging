import InflationA

namespace Inflation

variable (H : MGraph) (slot : Fin H.m → Bool → Fin 3)

def mkPE (X : Fin H.n) (s : Fin 12) : Fin (inflate H slot).m :=
  ⟨X.val * 12 + s.val, by
    change X.val * 12 + s.val < H.n * 12 + H.m
    have := X.isLt
    have := s.isLt
    omega⟩

def mkIE (e : Fin H.m) : Fin (inflate H slot).m :=
  ⟨H.n * 12 + e.val, by
    change H.n * 12 + e.val < H.n * 12 + H.m
    have := e.isLt
    omega⟩

def mkIV (X : Fin H.n) (a : Fin 9) : Fin (inflate H slot).n :=
  mkV X.val X.isLt a

theorem piece_ends (X : Fin H.n) (s : Fin 12) :
    (inflate H slot).ends (mkPE H slot X s) =
    (mkIV H slot X (pe1 s.val), mkIV H slot X (pe2 s.val)) := by
  have h : X.val * 12 + s.val < H.n * 12 := by
    have := X.isLt
    have := s.isLt
    omega
  have hd : (X.val * 12 + s.val) / 12 = X.val := by have := s.isLt; omega
  have hm : (X.val * 12 + s.val) % 12 = s.val := by have := s.isLt; omega
  simp [inflate, mkPE, mkIV, h, hd, hm]

theorem inter_ends (e : Fin H.m) :
    (inflate H slot).ends (mkIE H slot e) =
    (mkIV H slot (endOf H e false) (portv (slot e false)),
     mkIV H slot (endOf H e true) (portv (slot e true))) := by
  have h : ¬ (H.n * 12 + e.val < H.n * 12) := by omega
  simp [inflate, mkIE, mkIV, h]

theorem edge_cases (f : Fin (inflate H slot).m) :
    (∃ X : Fin H.n, ∃ s : Fin 12, f = mkPE H slot X s) ∨
    (∃ e : Fin H.m, f = mkIE H slot e) := by
  by_cases h : f.val < H.n * 12
  · left
    refine ⟨⟨f.val / 12, by omega⟩, ⟨f.val % 12, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [mkPE]
    omega
  · right
    refine ⟨⟨f.val - H.n * 12, by
      have hf : f.val < H.n * 12 + H.m := f.isLt
      omega⟩, ?_⟩
    apply Fin.ext
    dsimp [mkIE]
    omega

theorem vertex_cases (x : Fin (inflate H slot).n) :
    ∃ X : Fin H.n, ∃ a : Fin 9, x = mkIV H slot X a := by
  refine ⟨⟨x.val / 9, by have hx : x.val < H.n * 9 := x.isLt; omega⟩,
    ⟨x.val % 9, by omega⟩, ?_⟩
  apply Fin.ext
  dsimp [mkIV, mkV]
  omega

theorem mkIV_inj {X Y : Fin H.n} {a b : Fin 9}
    (h : mkIV H slot X a = mkIV H slot Y b) : X = Y ∧ a = b := by
  have hval : X.val * 9 + a.val = Y.val * 9 + b.val := congrArg Fin.val h
  constructor <;> apply Fin.ext <;> omega

theorem mkPE_inj {X Y : Fin H.n} {s t : Fin 12}
    (h : mkPE H slot X s = mkPE H slot Y t) : X = Y ∧ s = t := by
  have hval : X.val * 12 + s.val = Y.val * 12 + t.val := congrArg Fin.val h
  constructor <;> apply Fin.ext <;> omega

theorem mkIE_inj {e f : Fin H.m} (h : mkIE H slot e = mkIE H slot f) : e = f := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [mkIE] at hv
  omega

theorem mkPE_ne_mkIE (X : Fin H.n) (s : Fin 12) (e : Fin H.m) :
    mkPE H slot X s ≠ mkIE H slot e := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [mkPE, mkIE] at hv
  have := X.isLt
  have := s.isLt
  omega

end Inflation
