module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Weil.Attr

/-!
# Connecting morphisms in the derived category

Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes in an abelian
category `C`, and let `φ : Cone(X₁ ⟶ X₂) ⟶ X₃` be the cone-to-quotient map
(`CochainComplex.mappingCone.descShortComplex`), which is a quasi-isomorphism. A morphism
`w : Q(X₃) ⟶ Q(X₁)⟦1⟧` in the derived category is a *connecting morphism* of `S` if
`w ∘ Q(φ)` is the image under `Q` of the third arrow of the standard cone triangle of
`X₁ ⟶ X₂`. Since `Q(φ)` is an isomorphism, there is exactly one such morphism, namely
Mathlib's `DerivedCategory.triangleOfSESδ`.

## Main definitions

* `DerivedCategory.IsConnectingMorphism S w`: `w` is a connecting morphism of `S` in the
  derived category.

## Main results

* `DerivedCategory.isConnectingMorphism_triangleOfSESδ`: `triangleOfSESδ hS` is a connecting
  morphism.
* `DerivedCategory.isConnectingMorphism_iff_eq_triangleOfSESδ`: it is the only one.
* `DerivedCategory.existsUnique_isConnectingMorphism`: a short exact sequence has exactly one
  connecting morphism in the derived category.
* `DerivedCategory.isConnectingMorphism_iff_fst`: the same condition with the projection
  `Cone(X₁ ⟶ X₂) ⟶ X₁⟦1⟧`, `(x, y) ↦ x`, in place of the triangle's third arrow.

## Implementation notes

The condition is stated with Mathlib's sign conventions: the third arrow of
`CochainComplex.mappingCone.triangle` is induced by `-fst`, the negative of the projection
`(x, y) ↦ x` from `Cone(f)ⁿ = X₁ⁿ⁺¹ ⊞ X₂ⁿ`. With this convention the triangle
`Q(X₁) ⟶ Q(X₂) ⟶ Q(X₃) ⟶ Q(X₁)⟦1⟧` built from a connecting morphism is distinguished in
Mathlib's triangulated structure (`DerivedCategory.triangleOfSES_distinguished`).
`DerivedCategory.isConnectingMorphism_iff_fst` records the condition in the form using the
projection itself: `w` is a connecting morphism if and only if `-w ∘ Q(φ) = Q(fst)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Appendix A II, p. 296.
-/

/- FK's printed condition `w ∘ Q(φ) = Q(π_u)` uses FK's projection `π_u(x, y) = x`; Mathlib's cone
triangle uses `-π_u`. The definition follows Mathlib's sign convention, so that FK's admissible
triangle `(Q u, Q v, w)` is Mathlib's distinguished triangle; FK's literal condition is
`isConnectingMorphism_iff_fst` applied to `-w`. -/

@[expose] public section

open CategoryTheory Limits Pretriangulated CochainComplex HomComplex

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A morphism `w : Q(X₃) ⟶ Q(X₁)⟦1⟧` in the derived category is a *connecting morphism* of the
short complex `S` of cochain complexes if its composition with the image of the cone-to-quotient
map `Cone(X₁ ⟶ X₂) ⟶ X₃` is the image of the third arrow of the standard cone triangle. -/
@[weil "def_fka2_ses_connecting_morphism_derived"]
def IsConnectingMorphism (S : ShortComplex (CochainComplex C ℤ))
    (w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧) : Prop :=
  Q.map (mappingCone.descShortComplex S) ≫ w =
    Q.map (mappingCone.triangle S.f).mor₃ ≫ (Q.commShiftIso (1 : ℤ)).hom.app S.X₁

variable {S : ShortComplex (CochainComplex C ℤ)}

lemma isConnectingMorphism_triangleOfSESδ (hS : S.ShortExact) :
    IsConnectingMorphism S (triangleOfSESδ hS) :=
  descShortComplex_triangleOfSESδ hS

lemma isIso_Q_map_descShortComplex (hS : S.ShortExact) :
    IsIso (Q.map (mappingCone.descShortComplex S)) := by
  have := mappingCone.quasiIso_descShortComplex hS
  infer_instance

lemma IsConnectingMorphism.eq_triangleOfSESδ (hS : S.ShortExact)
    {w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧} (hw : IsConnectingMorphism S w) :
    w = triangleOfSESδ hS := by
  have := isIso_Q_map_descShortComplex hS
  rw [← cancel_epi (Q.map (mappingCone.descShortComplex S))]
  exact hw.trans (isConnectingMorphism_triangleOfSESδ hS).symm

lemma isConnectingMorphism_iff_eq_triangleOfSESδ (hS : S.ShortExact)
    (w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧) :
    IsConnectingMorphism S w ↔ w = triangleOfSESδ hS :=
  ⟨fun hw => hw.eq_triangleOfSESδ hS, fun h => h ▸ isConnectingMorphism_triangleOfSESδ hS⟩

/-- A short exact sequence of cochain complexes has exactly one connecting morphism in the
derived category. -/
lemma existsUnique_isConnectingMorphism (hS : S.ShortExact) :
    ∃! w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧, IsConnectingMorphism S w :=
  ⟨triangleOfSESδ hS, isConnectingMorphism_triangleOfSESδ hS,
    fun _ hw => hw.eq_triangleOfSESδ hS⟩

/-- The connecting-morphism condition with the projection `Cone(X₁ ⟶ X₂) ⟶ X₁⟦1⟧`,
`(x, y) ↦ x`, in place of the third arrow of the cone triangle (which is its negative). -/
lemma isConnectingMorphism_iff_fst (w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧) :
    IsConnectingMorphism S w ↔
      Q.map (mappingCone.descShortComplex S) ≫ (-w) =
        Q.map (Cocycle.homOf ((mappingCone.fst S.f).rightShift 1 0 (zero_add 1))) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  have h : (mappingCone.triangle S.f).mor₃ =
      -Cocycle.homOf ((mappingCone.fst S.f).rightShift 1 0 (zero_add 1)) := by
    ext n
    simp [mappingCone.triangle, Cochain.rightShift_neg]
  have h' : Q.map (mappingCone.triangle S.f).mor₃ =
      -Q.map (Cocycle.homOf ((mappingCone.fst S.f).rightShift 1 0 (zero_add 1))) := by
    rw [← Functor.map_neg]
    exact congrArg Q.map h
  simp only [IsConnectingMorphism, h', Preadditive.comp_neg]
  rw [neg_eq_iff_eq_neg, ← Preadditive.neg_comp]
  exact Iff.rfl

end DerivedCategory

end
