module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage

/-!
# Constructibility of higher direct images with proper support

Let `f : X ⟶ S` be a separated morphism of finite presentation with a compactification, `S`
quasi-compact and quasi-separated, and `F` a constructible abelian sheaf on the small étale site
of `X`. Then every higher direct image with proper support `R^v f_! F` is a constructible abelian
sheaf on the small étale site of `S`.

## Main definitions

* `AlgebraicGeometry.smallEtaleHigherDirectImageProperSupport`: `R^v f_!` on abelian sheaves on
  the small étale sites `SmallEtale`, transported from
  `AlgebraicGeometry.higherDirectImageProperSupport` on Mathlib's small étale sites.

## Main results

* `AlgebraicGeometry.isConstructibleEtaleModule_higherDirectImageProperSupport`: the statement
  for sheaves of `ℤ`-modules on Mathlib's small étale site; `R^v f_! F` is moreover torsion.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_smallEtaleHigherDirectImageProperSupport`: the
  statement for constructible abelian sheaves on the small étale sites `SmallEtale`.

## Implementation notes

The source states the result for `f` smooth with all nonempty geometric fibres of pure
dimension `1`, and `F` torsion prime to the residue characteristics of `S`. None of these
hypotheses is needed: the result is Stacks, Tag 0GL0 (`Stacks.EtaleCohomology.`
`isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible`), which holds
for every separated morphism of finite presentation and every constructible torsion
sheaf, and a constructible abelian sheaf is torsion. The hypotheses of the source (Noetherian
schemes, `f` smooth and compactifiable) imply the ones made here, so the source's case is
contained in the statement.

The higher direct images with proper support are constructed on Mathlib's small étale site, for
sheaves of `Λ`-modules; for abelian sheaves on `SmallEtale` they are obtained through
`AlgebraicGeometry.SmallEtale.sheafEquiv` and the equivalence between abelian groups and
`ℤ`-modules.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8,
  Lemma 8.11.
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj)
  (j : CompactificationOf (Over.mk f))

/-- An abelian sheaf on the small étale site `SmallEtale` of `X`, as a sheaf of `ℤ`-modules on
Mathlib's small étale site of `X`. -/
abbrev smallEtaleAbelianToEtaleModules (X : B.Scheme) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      EtaleModules.{u, 0} ℤ X.obj :=
  (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor ⋙
    (Sheaf.coefficientEquivalence X.obj.smallEtaleTopology
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor

/-- A sheaf of `ℤ`-modules on Mathlib's small étale site of `X`, as an abelian sheaf on the small
étale site `SmallEtale` of `X`. -/
abbrev etaleModulesToSmallEtaleAbelian (X : B.Scheme) :
    EtaleModules.{u, 0} ℤ X.obj ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  (Sheaf.coefficientEquivalence X.obj.smallEtaleTopology
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).inverse ⋙
    (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse

/-- The `v`-th **higher direct image with proper support** `R^v f_! F` of an abelian sheaf `F` on
the small étale site `SmallEtale` of `X`, computed through the compactification `j` of `f`: the
transport of `AlgebraicGeometry.higherDirectImageProperSupport` (with `Λ = ℤ`, on `F` placed in
degree `0`). -/
abbrev smallEtaleHigherDirectImageProperSupport (v : ℤ) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} :=
  smallEtaleAbelianToEtaleModules B X ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    higherDirectImageProperSupport f j ℤ v ⋙ etaleModulesToSmallEtaleAbelian B S

variable [CompactSpace S.obj] [QuasiSeparatedSpace S.obj] [IsSeparated f]
  [LocallyOfFinitePresentation f] [QuasiCompact f]

/-- **Constructibility of `R^v f_!` for sheaves of `ℤ`-modules.** For `f : X ⟶ S` separated of
finite presentation with a compactification `j`, `S` quasi-compact and quasi-separated, and `F` a
constructible torsion sheaf of `ℤ`-modules on the small étale site of `X`, every higher direct
image with proper support `R^v f_! F` is constructible and torsion. -/
theorem isConstructibleEtaleModule_higherDirectImageProperSupport
    (F : EtaleModules.{u, 0} ℤ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X ℤ F)
    (ht : IsTorsionEtaleModule ℤ X.obj F) (v : ℤ) :
    IsBigSiteConstructibleEtaleModule B S ℤ ((higherDirectImageProperSupport f j ℤ v).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ∧
      IsTorsionEtaleModule ℤ S.obj ((higherDirectImageProperSupport f j ℤ v).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  ⟨(isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible B f j ℤ).1 _
      (fun q => ⟨isConstructibleEtaleModule_homology_singleFunctor hF q,
        isTorsionEtaleModule_homology_singleFunctor ht q⟩) v,
    isTorsionPlus_derivedLowerShriek_obj ℤ f j _
      (fun q => isTorsionEtaleModule_homology_singleFunctor ht q) v⟩

/-- **Constructibility of higher direct images with proper support.** Let `f : X ⟶ S` be a
separated morphism of finite presentation with a compactification `j`, with `S` quasi-compact and
quasi-separated, and `F` a constructible abelian sheaf on the small étale site of `X`. Then
`R^v f_! F` is a constructible abelian sheaf on the small étale site of `S` for every `v`.

This contains the case of a smooth compactifiable `f` of relative dimension `1` and `F` torsion
prime to the residue characteristics of `S`. -/
@[weil "lem_fk108_proper_direct_image_constructible_smooth_curve"]
theorem isConstructibleAbelianSheaf_smallEtaleHigherDirectImageProperSupport
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) (v : ℤ) :
    IsConstructibleAbelianSheaf B S
      ((smallEtaleHigherDirectImageProperSupport B f j v).obj F) := by
  let EX := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  let CX := Sheaf.coefficientEquivalence X.obj.smallEtaleTopology
    AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let CS := Sheaf.coefficientEquivalence S.obj.smallEtaleTopology
    AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let G := (smallEtaleAbelianToEtaleModules B X).obj F
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} (B := B)
    (X := X) (Λ := ℤ)
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} (B := B)
    (X := S) (Λ := ℤ)
  have hG : IsBigSiteConstructibleEtaleModule B X ℤ G :=
    ObjectProperty.prop_of_iso (fun K : Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{u + 1} ℤ) => IsConstructibleModuleSheaf B X ℤ K)
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.mapIso (EX.unitIso.app F) :
          _ ≅ (etaleModulesToSmallEtale.{u, 0} B X ℤ).obj G)
      (isConstructibleModuleSheaf_moduleCatIntEquivalence B X F hF)
  have htG : IsTorsionEtaleModule ℤ X.obj G :=
    (Stacks.Torsion.torsionSheafProperty _).prop_of_iso (CX.unitIso.app (EX.functor.obj F))
      (SmallEtale.torsionSheafProperty_sheafEquiv_functor_obj B X F
        (torsionSheafProperty_of_isConstructibleAbelianSheaf B X F hF))
  obtain ⟨hH, htH⟩ := isConstructibleEtaleModule_higherDirectImageProperSupport B f j G hG htG v
  set H := (higherDirectImageProperSupport f j ℤ v).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  refine isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int B S _ ?_
    (SmallEtale.torsionSheafProperty_sheafEquiv_inverse_obj B S _ htH)
  exact ObjectProperty.prop_of_iso (fun K : Sheaf (SmallEtale.topology B S.obj S.property)
        (ModuleCat.{u + 1} ℤ) => IsConstructibleModuleSheaf B S ℤ K)
    ((etaleModulesToSmallEtale.{u, 0} B S ℤ).mapIso (CS.counitIso.app H)).symm hH

end AlgebraicGeometry
