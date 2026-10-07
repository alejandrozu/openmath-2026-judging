import ComponentClosure

/-!
# Hamilton decomposition of every exact-four-colour Haar component

The ambient elementary abelian group may be infinite. Both graph symmetries
are proved for the actual arbitrary-palette Haar graph. No global connected
host or component-support assumption is used.
-/

noncomputable section

namespace RobertPublishable.HaarComponent

open SimpleGraph Erdos585

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

def translationIso (S : Finset V) (a : V) : Haar.graph S ≃g Haar.graph S where
  toEquiv :=
    { toFun := fun v => (v.1 + a, v.2)
      invFun := fun v => (v.1 - a, v.2)
      left_inv := by rintro ⟨x, b⟩; simp
      right_inv := by rintro ⟨x, b⟩; simp }
  map_rel_iff' := by
    rintro ⟨x, b⟩ ⟨y, c⟩
    simp [Haar.graph]

def reflectionIso (S : Finset V) : Haar.graph S ≃g Haar.graph S where
  toEquiv :=
    { toFun := fun v => (-v.1, !v.2)
      invFun := fun v => (-v.1, !v.2)
      left_inv := by rintro ⟨x, b⟩; simp
      right_inv := by rintro ⟨x, b⟩; simp }
  map_rel_iff' := by
    rintro ⟨x, b⟩ ⟨y, c⟩
    cases b <;> cases c <;> simp [Haar.graph, sub_eq_add_neg, add_comm]

def moveIso (S : Finset V) (u x : V × Bool) : Haar.graph S ≃g Haar.graph S :=
  if u.2 = x.2 then translationIso S (x.1 - u.1)
  else (reflectionIso S).trans (translationIso S (x.1 + u.1))

theorem moveIso_apply (S : Finset V) (u x : V × Bool) : moveIso S u x u = x := by
  rcases u with ⟨a, b⟩
  rcases x with ⟨c, d⟩
  cases b <;> cases d <;> simp [moveIso, translationIso, reflectionIso, RelIso.trans_apply]

/-- Every vertex's actual component, not merely some induced subgraph,
is decomposed by two genuine Hamilton cycles. -/
theorem every_vertex_component {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]
    (S : Finset V) (h4 : S.card = 4) (x : V × Bool) :
    HamiltonDecomposesComponent (Haar.graph S) ((Haar.graph S).connectedComponentMk x) := by
  obtain ⟨u, v, P, Q, hP, hQ, hS, hE⟩ :=
    HaarClassification.hasPair_of_four (p := p) S (by omega)
  let e : Haar.graph S ≃g Haar.graph S := moveIso S u x
  have he : e u = x := moveIso_apply S u x
  obtain ⟨hP', hQ', hS', hE'⟩ := (pair_map_iff e.toHom e.injective P Q).mpr ⟨hP, hQ, hS, hE⟩
  have hf := OpenMathReview.HaarInfinite.neighbor_finite S
  have hd : ∀ y, ((Haar.graph S).neighborSet y).ncard = 4 := by
    intro y
    rw [OpenMathReview.HaarInfinite.neighbor_ncard, h4]
  have hc := pair_support_eq_component hP' hQ' hS' hE' hf hd
  have hcover := pair_edges_exhaust_component hP' hQ' hS' hE' hf hd
  have hcomp : ((Haar.graph S).connectedComponentMk (e u)).supp =
      ((Haar.graph S).connectedComponentMk x).supp :=
    congrArg (fun y => ((Haar.graph S).connectedComponentMk y).supp) he
  refine ⟨e u, e v, P.map e.toHom, Q.map e.toHom, hP', hQ', hc.trans hcomp, ?_, hE', ?_⟩
  · exact (congrArg (fun T : Finset (V × Bool) => (T : Set (V × Bool))) hS').symm.trans
      (hc.trans hcomp)
  · intro a b ha hab
    exact hcover (hcomp.symm ▸ ha) hab

theorem every_connected_component {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]
    (S : Finset V) (h4 : S.card = 4) (C : (Haar.graph S).ConnectedComponent) :
    HamiltonDecomposesComponent (Haar.graph S) C := by
  obtain ⟨x, hx⟩ := C.nonempty_supp
  have h := every_vertex_component (p := p) S h4 x
  change (Haar.graph S).connectedComponentMk x = C at hx
  rwa [hx] at h

theorem every_component_finite {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]
    (S : Finset V) (h4 : S.card = 4) (C : (Haar.graph S).ConnectedComponent) :
    C.supp.Finite := by
  obtain ⟨u, v, P, Q, _, _, hc, _⟩ := every_connected_component (p := p) S h4 C
  rw [← hc]
  exact P.support.toFinset.finite_toSet

#print axioms translationIso
#print axioms reflectionIso
#print axioms moveIso_apply
#print axioms every_vertex_component
#print axioms every_connected_component
#print axioms every_component_finite
#check @every_connected_component
#check @every_component_finite

end RobertPublishable.HaarComponent
