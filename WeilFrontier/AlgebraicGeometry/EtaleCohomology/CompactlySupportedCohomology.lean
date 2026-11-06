module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyRestrictScalars
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import Weil.Attr

/-!
# Higher direct images with proper support of a sheaf in degree zero

Let `f : X ⟶ S` be a morphism of schemes with a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ S`,
and `Λ` a ring. For a sheaf `F` of `Λ`-modules on the small étale site of `X`, placed in
degree `0`, the higher direct images with proper support `R^v f_!(F) = H^v(R f̄_*(j_! F))`
vanish for `v < 0`, and `R^0 f_!(F) ≅ f̄_*(j_! F)`, naturally in `F`.

Both follow from the shape of `Rf_! = R f̄_* ∘ Rj_!`: each of the two right derived functors
keeps a complex in degrees `≥ a` in degrees `≥ a`, which gives the vanishing (more generally, for
every bounded below complex with no cohomology in negative degrees). Extension by zero is exact,
so `Rj_!(F[0]) ≅ (j_! F)[0]`; and the degree zero cohomology of the right derived functor of the
left exact functor `f̄_*` at a sheaf placed in degree zero is `f̄_*` itself.

## Main results

* `AlgebraicGeometry.higherDirectImageProperSupportZeroIso`: `R^0 f_!(F) ≅ f̄_*(j_! F)`,
  naturally in the sheaf `F`.
* `AlgebraicGeometry.isZero_higherDirectImageProperSupport_obj`: `R^v f_!(K) = 0` for `v < 0`
  and a bounded below complex `K` with `H^i(K) = 0` for `i < 0`.
* `AlgebraicGeometry.isZero_higherDirectImageProperSupport_singleFunctor_obj`: `R^v f_!(F) = 0`
  for `v < 0` and a sheaf `F` placed in degree `0`.

## Implementation notes

The source states the result for torsion abelian sheaves; neither the torsion hypothesis nor
`Λ = ℤ` is used, and the statements here are for sheaves of modules over an arbitrary ring `Λ`.
The sheaves live on Mathlib's small étale site, as for
`AlgebraicGeometry.higherDirectImageProperSupport`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

universe u r

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (j : CompactificationOf (Over.mk f)) (Λ : Type r)
  [Ring Λ]

/-- `R^0 f_!(F) ≅ f̄_*(j_! F)`, naturally in the sheaf `F` placed in degree `0`: extension by
zero is exact, so `Rj_!(F[0]) ≅ (j_! F)[0]`, and `R^0 f̄_* = f̄_*`, the direct image being left
exact. -/
@[weil "lem_fk108_higher_direct_image_proper_support_zero"]
def higherDirectImageProperSupportZeroIso :
    DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0 ⋙
        higherDirectImageProperSupport f j Λ 0 ≅
      etaleModuleExtensionByZero.{u, r} Λ j.immersion ⋙
        etaleModuleDirectImage.{u, r} Λ j.toBase :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          (etaleModuleExtensionByZero.{u, r} Λ
            j.immersion).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus ≪≫
        Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (etaleModuleExtensionByZero.{u, r} Λ j.immersion) 0)
      (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase ⋙
        DerivedCategory.Plus.homologyFunctor _ 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleModuleExtensionByZero.{u, r} Λ j.immersion)
      ((Stacks.DerivedIndexing.rightDerivedIso
          (etaleModuleDirectImage.{u, r} Λ j.toBase) 0).symm ≪≫
        (etaleModuleDirectImage.{u, r} Λ j.toBase).rightDerivedZeroIsoSelf)

/-- `R^v f_!(K) = 0` for `v < 0` when the bounded below complex `K` has no cohomology in negative
degrees: `Rj_!` and `R f̄_*` both keep `K` in degrees `≥ 0`. -/
theorem isZero_higherDirectImageProperSupport_obj
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) [K.IsGE 0] {v : ℤ} (hv : v < 0) :
    IsZero ((higherDirectImageProperSupport f j Λ v).obj K) := by
  have h₁ := Functor.isGE_rightDerivedFunctorPlus_obj
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion) K 0
  have h₂ := @Functor.isGE_rightDerivedFunctorPlus_obj _ _ _ _ _ _ _ _
    (etaleModuleDirectImage.{u, r} Λ j.toBase) _ _ _ 0 h₁
  exact @DerivedCategory.Plus.isZero_homology_of_isGE' _ _ _ _ _ 0 v hv h₂

/-- `R^v f_!(F) = 0` for `v < 0` and a sheaf `F` placed in degree `0`. -/
@[weil "lem_fk108_higher_direct_image_proper_support_zero"]
theorem isZero_higherDirectImageProperSupport_singleFunctor_obj (F : EtaleModules.{u, r} Λ X)
    {v : ℤ} (hv : v < 0) :
    IsZero ((higherDirectImageProperSupport f j Λ v).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  isZero_higherDirectImageProperSupport_obj f j Λ _ hv

end AlgebraicGeometry
