module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage

/-!
# Constructibility of higher direct images with proper support

Let `f : X ⟶ S` be a compactifiable morphism of schemes with `S` Noetherian, and `F` a
constructible abelian sheaf on the small étale site of `X` which is torsion prime to the residue
characteristics of `S`. Then every higher direct image with proper support `R^v f_! F` is a
constructible abelian sheaf on the small étale site of `S`. In fact the torsion condition on the
orders is not needed: it suffices that `F` be a torsion sheaf.

The higher direct image `R^v f_!` (`AlgebraicGeometry.higherDirectImageProperSupport`) is
computed through a compactification `j` of `f` on sheaves of `ℤ`-modules on Mathlib's small étale
site. An abelian sheaf `F` on the small étale site `AlgebraicGeometry.SmallEtale` is carried there
by the equivalence `AddCommGrpCat ≌ ModuleCat ℤ` followed by the comparison of sites
`AlgebraicGeometry.SmallEtale.sheafEquiv`, and `R^v f_! F` is carried back the same way.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_higherDirectImageProperSupport_of_torsion`:
  `R^v f_! F` is constructible for a constructible torsion abelian sheaf `F`.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_higherDirectImageProperSupport`: `R^v f_! F` is
  constructible for a constructible abelian sheaf `F` which is torsion prime to the residue
  characteristics of `S`.

## Implementation notes

A compactifiable morphism is given here by a compactification `j : X ⟶ X̄`, `X̄ ⟶ S` of `f`,
through which `R^v f_!` is computed; such a morphism is separated and locally of finite type. The
morphism `f` is also asked to be quasi-compact, which holds when `X` is Noetherian. The statement
holds for every `v : ℤ`, not only for `v ≥ 0`.

The proof is Stacks, Tag 0GL0 for the ring `ℤ`
(`Stacks.EtaleCohomology.lowerShriekConstructibilityInput`): for a constructible torsion sheaf of
`ℤ`-modules, the cohomology sheaves of `Rf_!` are constructible as sheaves of `ℤ`-modules, and they
are torsion (`Stacks.EtaleCohomology.isTorsionPlus_derivedLowerShriek_obj`). A constructible
abelian sheaf is a constructible sheaf of `ℤ`-modules, and a torsion sheaf of `ℤ`-modules which is
constructible has finite local values, so it is a constructible abelian sheaf.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.10
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X S : B.Scheme}

/-- **Constructibility of `R^v f_!` for torsion coefficients** (Stacks, Tag 0GL0, for sheaves).
Let `f : X ⟶ S` be a quasi-compact morphism with a compactification `j`, `S` Noetherian, and `F`
a constructible abelian sheaf on the small étale site of `X` which is a torsion sheaf. Then for
every `v`, the higher direct image with proper support `R^v f_! F`, computed through `j`, is a
constructible abelian sheaf on the small étale site of `S`. -/
theorem isConstructibleAbelianSheaf_higherDirectImageProperSupport_of_torsion
    [IsNoetherian S.obj] (f : X.obj ⟶ S.obj) [QuasiCompact f]
    (j : CompactificationOf (Over.mk f))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F)
    (hFt : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F)
    (v : ℤ) :
    IsConstructibleAbelianSheaf B S
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B S.obj S.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).inverse.obj
        ((SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{u + 1} ℤ)).inverse.obj
          ((higherDirectImageProperSupport f j ℤ v).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} ℤ)).functor.obj
                ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
                  AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F)))))) := by
  have : IsSeparated f := by rw [← j.immersion_toBase_general]; infer_instance
  have : LocallyOfFiniteType f := by rw [← j.immersion_toBase_general]; infer_instance
  set Fm := (Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
    AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F
  set EX := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} ℤ)
  set G := EX.functor.obj Fm
  have hGc : IsBigSiteConstructibleEtaleModule B X ℤ G := by
    have h1 := isConstructibleModuleSheaf_moduleCatIntEquivalence B X F hF
    have := (SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} B X
      ℤ).toIsClosedUnderIsomorphisms
    exact ObjectProperty.prop_of_iso (fun F : Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{u + 1} ℤ) => IsConstructibleModuleSheaf B X ℤ F) (EX.unitIso.app Fm) h1
  have hGt : IsTorsionEtaleModule ℤ X.obj G := by
    refine torsionSheafProperty_of_pushforward (SmallEtale.topology B X.obj X.property)
      X.obj.smallEtaleTopology (SmallEtale.toEtaleSite B X.obj X.property)
      ((etaleModuleForgetAb.{u, 0} ℤ X.obj).obj G) ?_
    exact (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).unitIso.app F ≪≫
        (Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
          AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).inverse.mapIso (EX.unitIso.app Fm)) hFt
  set H := (higherDirectImageProperSupport f j ℤ v).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have hHc : IsBigSiteConstructibleEtaleModule B S ℤ H :=
    lowerShriekConstructibilityInput B f j ℤ G hGc hGt v
  have hHt : IsTorsionEtaleModule ℤ S.obj H :=
    isTorsionPlus_derivedLowerShriek_obj ℤ f j _
      (fun q => isTorsionEtaleModule_homology_singleFunctor hGt q) v
  set ES := SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{u + 1} ℤ)
  set cS := Sheaf.coefficientEquivalence (SmallEtale.topology B S.obj S.property)
    AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  refine isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int_general B S _ ?_ ?_
  · have := (SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} B S
      ℤ).toIsClosedUnderIsomorphisms
    exact ObjectProperty.prop_of_iso (fun F : Sheaf (SmallEtale.topology B S.obj S.property)
        (ModuleCat.{u + 1} ℤ) => IsConstructibleModuleSheaf B S ℤ F)
      (cS.counitIso.app (ES.inverse.obj H)).symm hHc
  · exact SmallEtale.torsionSheafProperty_sheafEquiv_inverse_obj B S
      ((etaleModuleForgetAb.{u, 0} ℤ S.obj).obj H) hHt

/-- **Constructibility of `R^v f_!`** (Freitag--Kiehl I.8.10). Let `f : X ⟶ S` be a
quasi-compact morphism with a compactification `j`, `S` Noetherian, and `F` a constructible
abelian sheaf on the small étale site of `X` which is torsion prime to the residue
characteristics of `S`. Then for every `v`, the higher direct image with proper support
`R^v f_! F`, computed through `j`, is a constructible abelian sheaf on the small étale site of
`S`. -/
@[weil "thm_fk108_proper_direct_image_constructible"]
theorem isConstructibleAbelianSheaf_higherDirectImageProperSupport
    [IsNoetherian S.obj] (f : X.obj ⟶ S.obj) [QuasiCompact f]
    (j : CompactificationOf (Over.mk f))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F)
    (hFt : SmallEtale.IsTorsionPrimeToResidueCharacteristics B X.obj X.property S.obj F)
    (v : ℤ) :
    IsConstructibleAbelianSheaf B S
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B S.obj S.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).inverse.obj
        ((SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{u + 1} ℤ)).inverse.obj
          ((higherDirectImageProperSupport f j ℤ v).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} ℤ)).functor.obj
                ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
                  AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F)))))) :=
  isConstructibleAbelianSheaf_higherDirectImageProperSupport_of_torsion B f j F hF
    hFt.isTorsionSheaf v

end AlgebraicGeometry
