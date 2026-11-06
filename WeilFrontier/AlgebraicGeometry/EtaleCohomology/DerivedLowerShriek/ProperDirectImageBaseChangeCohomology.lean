module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import Weil.Attr

/-!
# Base change for higher direct images with proper support

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes and `j` a compactification of `f`. For every bounded below
complex `K` of sheaves of `Λ`-modules on the small étale site of `X` with torsion cohomology
sheaves and every `v : ℤ` there is an isomorphism `g⁻¹ R^v f_!(K) ≅ R^v f'_!(g'⁻¹ K)`, natural in
`K`, where `R^v f'_!` is computed with the base change of `j`. It is the image under the
cohomology sheaf functor `H^v` of the base change isomorphism `g⁻¹ Rf_! ≅ Rf'_! g'⁻¹`
([Stacks, Tag 0F7L]), using that the inverse image `g⁻¹` is exact and hence commutes with `H^v`.

## Main results

* `AlgebraicGeometry.higherDirectImageProperSupportBaseChangeIso`: the natural isomorphism
  `g⁻¹ ∘ R^v f_! ≅ R^v f'_! ∘ g'⁻¹` of functors on `D⁺_tors(X)`.

## Implementation notes

The sheaves live on Mathlib's small étale site `X.smallEtaleTopology`, the site of
`AlgebraicGeometry.higherDirectImageProperSupport`. The coefficients are any ring `Λ` in `Type`,
the source's case being `Λ = ℤ`. The base-changed compactification is
`AlgebraicGeometry.CompactificationOf.baseChange`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

universe u

namespace AlgebraicGeometry

variable (Λ : Type) [Ring Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- The inverse image `a⁻¹` commutes with the cohomology sheaf functors of bounded below derived
categories of étale sheaves of `Λ`-modules: `a⁻¹ ∘ H^v ≅ H^v ∘ a⁻¹`, natural in the complex, the
inverse image being exact. -/
def etaleModuleDerivedInverseImagePlusHomologyNatIso {Z W : Scheme.{u}} (a : W ⟶ Z) (v : ℤ) :
    etaleModuleDerivedInverseImagePlus.{u, 0} Λ a ⋙
        DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ W) v ≅
      DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Z) v ⋙
        etaleModuleInverseImage.{u, 0} Λ a :=
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (etaleModuleInverseImage.{u, 0} Λ a))
      (DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ W) v) ≪≫
    Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (etaleModuleInverseImage.{u, 0} Λ a) v

/-- **Base change for higher direct images with proper support.** For a cartesian square
`g' ≫ f = f' ≫ g` of schemes, a compactification `j` of `f` and `v : ℤ`, the isomorphism
`g⁻¹ R^v f_!(K) ≅ R^v f'_!(g'⁻¹ K)`, natural in `K ∈ D⁺_tors(X)`, where `R^v f'_!` is computed
with the base change `j.baseChange sq` of `j`. -/
@[weil "lem_fk108_proper_direct_image_base_change_cohomology"]
def higherDirectImageProperSupportBaseChangeIso (v : ℤ) :
    higherDirectImageProperSupportTorsion f j Λ v ⋙ etaleModuleInverseImage.{u, 0} Λ g ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, 0} Λ g' ⋙
        higherDirectImageProperSupport f' (j.baseChange sq) Λ v :=
  Functor.isoWhiskerLeft ((isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j Λ)
      (etaleModuleDerivedInverseImagePlusHomologyNatIso Λ g v).symm ≪≫
    Functor.isoWhiskerRight (derivedLowerShriekBaseChangeIso Λ sq j)
      (DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Y') v)

end AlgebraicGeometry
