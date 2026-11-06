module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionBaseChange

/-!
# Restriction to an open subscheme commutes with derived direct image

Let `f : X ⟶ Y` be a morphism of schemes, `j : U ⟶ Y` an open immersion, and
```
X₁ --i₂--> X
|f₁        |f
v          v
U  --j---> Y
```
a cartesian square, so that `X₁ = f⁻¹(U) = X ×_Y U`. For every bounded below complex `𝒢` of
étale sheaves of `Λ`-modules on `X` there is an isomorphism
`j⁻¹ Rf_* 𝒢 ≅ Rf₁_* (i₂⁻¹ 𝒢)` in `D⁺(U_étale, Λ)`, natural in `𝒢`.

The isomorphism is the base change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of the square, which is an
isomorphism at every object when `g` is an open immersion
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageInverseImageIsoOfIsOpenImmersion`:
  the natural isomorphism `j⁻¹ ∘ Rf_* ≅ Rf₁_* ∘ i₂⁻¹` of functors
  `D⁺(X_étale, Λ) ⥤ D⁺(U_étale, Λ)`.

## Implementation notes

The source states the result for abelian sheaves; here the coefficients are any ring `Λ`
(`Λ = ℤ` gives abelian sheaves), and the square is any cartesian square rather than the
chosen fibre product `X ×_Y U`. The sheaves live on Mathlib's small étale site
`X.smallEtaleTopology`, the site of `Stacks.EtaleCohomology.EtaleModules` and of the derived
functors `Stacks.EtaleCohomology.etaleModuleDerivedDirectImage`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FK]
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

attribute [-instance] Stacks.EtaleCohomology.etaleAbelianDirectImage_additive

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type w) [Ring Λ]

/-- **Restriction to an open subscheme commutes with derived direct image.** For a cartesian
square `i₂ ≫ f = f₁ ≫ j` of schemes with `j : U ⟶ Y` an open immersion, the natural
isomorphism `j⁻¹ Rf_* 𝒢 ≅ Rf₁_* (i₂⁻¹ 𝒢)` of functors on `D⁺(X_étale, Λ)`; its components are
the base change maps of the square. -/
@[weil "lem_fk108_open_restriction_commutes_derived_direct_image"]
def etaleModuleDerivedDirectImageInverseImageIsoOfIsOpenImmersion {X X₁ Y U : Scheme.{u}}
    (f : X ⟶ Y) {j : U ⟶ Y} {i₂ : X₁ ⟶ X} {f₁ : X₁ ⟶ U} (sq : IsPullback i₂ f₁ f j)
    [IsOpenImmersion j] :
    etaleModuleDerivedDirectImage.{u, w} Λ f ⋙ etaleModuleDerivedInverseImagePlus.{u, w} Λ j ≅
      etaleModuleDerivedInverseImagePlus.{u, w} Λ i₂ ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ f₁ :=
  haveI : ∀ K, IsIso ((etaleModuleDerivedBaseChange.{u, w} Λ f f₁ j i₂ sq.w.symm).app K) :=
    fun K => isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion.{u, w} Λ f sq K
  haveI := NatIso.isIso_of_isIso_app (etaleModuleDerivedBaseChange.{u, w} Λ f f₁ j i₂ sq.w.symm)
  asIso (etaleModuleDerivedBaseChange.{u, w} Λ f f₁ j i₂ sq.w.symm)

/-- The isomorphism `j⁻¹ Rf_* ≅ Rf₁_* i₂⁻¹` is the base change map of the square. -/
@[simp]
lemma etaleModuleDerivedDirectImageInverseImageIsoOfIsOpenImmersion_hom
    {X X₁ Y U : Scheme.{u}} (f : X ⟶ Y) {j : U ⟶ Y} {i₂ : X₁ ⟶ X} {f₁ : X₁ ⟶ U}
    (sq : IsPullback i₂ f₁ f j) [IsOpenImmersion j] :
    (etaleModuleDerivedDirectImageInverseImageIsoOfIsOpenImmersion.{u, w} Λ f sq).hom =
      etaleModuleDerivedBaseChange.{u, w} Λ f f₁ j i₂ sq.w.symm :=
  rfl

end Stacks.EtaleCohomology

end
