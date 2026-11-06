/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Weil.Attr

/-!
# Connecting homomorphisms of a short exact sequence of complexes

Let `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` be a short exact sequence of homological complexes in an abelian
category, with maps `u : X ⟶ Y` and `v : Y ⟶ Z`, and let `i j` be indices with `c.Rel i j`
(for cochain complexes indexed by `ℤ`: `j = i + 1`). A morphism `δ : H^i(Z) ⟶ H^j(X)` is a
*connecting homomorphism* if `δ [z] = [x]` whenever `z ∈ Z^i`, `y ∈ Y^i`, `x ∈ X^j` satisfy
`dz = 0`, `dx = 0`, `v y = z` and `u x = d y`.

Elements are generalized elements `A ⟶ Z^i` etc. We show that the connecting homomorphism
`ShortComplex.ShortExact.δ` of Mathlib is a connecting homomorphism in this sense, and that it is
the only one.

## Main definitions

* `CategoryTheory.ShortComplex.IsConnectingHomomorphism`: the predicate on morphisms
  `S.X₃.homology i ⟶ S.X₁.homology j` described above.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.isConnectingHomomorphism_δ`: `hS.δ i j hij` is a
  connecting homomorphism.
* `CategoryTheory.ShortComplex.ShortExact.isConnectingHomomorphism_iff`: a morphism is a
  connecting homomorphism if and only if it equals `hS.δ i j hij`.

## Implementation notes

The source quantifies over elements of the terms of the complexes; here they are morphisms
from an arbitrary object `A`. Uniqueness uses that in an abelian category epimorphisms are
surjective up to refinements (`CategoryTheory.surjective_up_to_refinements_of_epi`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Appendix A II, p. 296.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

namespace ShortComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

/-- A morphism `δ : H^i(X₃) ⟶ H^j(X₁)` is a connecting homomorphism of the short complex
`S = (X₁ ⟶ X₂ ⟶ X₃)` of complexes if for all (generalized) elements `x₃` of `X₃^i`, `x₂` of
`X₂^i` and `x₁` of `X₁^j` with `d x₃ = 0`, `d x₁ = 0`, `g x₂ = x₃` and `f x₁ = d x₂`, the class
of `x₃` is sent by `δ` to the class of `x₁`. -/
@[weil "def_fka2_ses_connecting_homomorphism"]
def IsConnectingHomomorphism (S : ShortComplex (HomologicalComplex C c)) (i j : ι)
    (hij : c.Rel i j) (δ : S.X₃.homology i ⟶ S.X₁.homology j) : Prop :=
  ∀ ⦃A : C⦄ (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0) (x₂ : A ⟶ S.X₂.X i)
    (_ : x₂ ≫ S.g.f i = x₃) (x₁ : A ⟶ S.X₁.X j) (hx₁ : x₁ ≫ S.X₁.d j (c.next j) = 0)
    (_ : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j),
    S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i ≫ δ =
      S.X₁.liftCycles x₁ (c.next j) rfl hx₁ ≫ S.X₁.homologyπ j

namespace ShortExact

variable {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i j : ι)
  (hij : c.Rel i j)

include hS in
/-- The connecting homomorphism `hS.δ i j hij` is a connecting homomorphism. -/
lemma isConnectingHomomorphism_δ : S.IsConnectingHomomorphism i j hij (hS.δ i j hij) := by
  intro A x₃ hx₃ x₂ hx₂ x₁ hx₁ h
  exact hS.δ_eq i j hij x₃ hx₃ x₂ hx₂ x₁ h (c.next j) rfl

include hS in
/-- Two connecting homomorphisms of a short exact sequence of complexes are equal. -/
lemma _root_.CategoryTheory.ShortComplex.IsConnectingHomomorphism.eq
    {δ δ' : S.X₃.homology i ⟶ S.X₁.homology j}
    (h : S.IsConnectingHomomorphism i j hij δ) (h' : S.IsConnectingHomomorphism i j hij δ') :
    δ = δ' := by
  rw [← cancel_epi (S.X₃.homologyπ i)]
  have hgi : Epi (S.g.f i) := (hS.map_of_exact (HomologicalComplex.eval C c i)).epi_g
  have hexj := (hS.map_of_exact (HomologicalComplex.eval C c j)).exact
  obtain ⟨A₁, π₁, hπ₁, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi (S.g.f i) (S.X₃.iCycles i)
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := hexj.exact_up_to_refinements (x₂ ≫ S.X₂.d i j) (by
    dsimp
    rw [assoc, ← S.g.comm, ← reassoc_of% hx₂, S.X₃.iCycles_d, comp_zero])
  dsimp at hx₁
  have hdx₁ : x₁ ≫ S.X₁.d j (c.next j) = 0 := by
    have : Mono (S.f.f (c.next j)) :=
      (hS.map_of_exact (HomologicalComplex.eval C c (c.next j))).mono_f
    rw [← cancel_mono (S.f.f (c.next j)), assoc, ← S.f.comm, ← reassoc_of% hx₁]
    simp
  have key : S.X₃.liftCycles ((π₂ ≫ π₁) ≫ S.X₃.iCycles i) j (c.next_eq' hij)
      (by simp) = π₂ ≫ π₁ := by
    rw [← cancel_mono (S.X₃.iCycles i), HomologicalComplex.liftCycles_i]
  have e := h ((π₂ ≫ π₁) ≫ S.X₃.iCycles i) (by simp) (π₂ ≫ x₂)
    (by rw [assoc, assoc, hx₂]) x₁ hdx₁ (by rw [← hx₁, assoc])
  have e' := h' ((π₂ ≫ π₁) ≫ S.X₃.iCycles i) (by simp) (π₂ ≫ x₂)
    (by rw [assoc, assoc, hx₂]) x₁ hdx₁ (by rw [← hx₁, assoc])
  rw [key] at e e'
  rw [← cancel_epi (π₂ ≫ π₁)]
  simpa only [assoc] using e.trans e'.symm

include hS in
/-- A morphism `H^i(X₃) ⟶ H^j(X₁)` is a connecting homomorphism if and only if it is
`hS.δ i j hij`. -/
lemma isConnectingHomomorphism_iff (δ : S.X₃.homology i ⟶ S.X₁.homology j) :
    S.IsConnectingHomomorphism i j hij δ ↔ δ = hS.δ i j hij :=
  ⟨fun h ↦ h.eq hS i j hij (hS.isConnectingHomomorphism_δ i j hij),
    fun h ↦ h ▸ hS.isConnectingHomomorphism_δ i j hij⟩

end ShortExact

end ShortComplex

end CategoryTheory
