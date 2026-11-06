module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import Weil.Attr

/-!
# The complex of cohomology with compact support on the small étale site

Let `k` be a field, `f : X ⟶ Spec k` a separated morphism of finite type with a
compactification `j`, an open immersion of `X` into a scheme proper over `k`, and `Λ` a ring. For
a bounded below complex `K` of sheaves of `Λ`-modules on the small étale site of `X`, the complex
of cohomology with compact support is `RΓ_c(X, K) = RΓ(Spec k, Rf_! K)`, where
`Rf_! = R(f̄)_* ∘ j_!` is the derived direct image with proper support.

This file states it for sheaves on the small étale site `AlgebraicGeometry.SmallEtale` of `X`
inside a big étale site, through the equivalence of sheaf categories
`AlgebraicGeometry.SmallEtale.sheafEquiv` with Mathlib's small étale site
`X.smallEtaleTopology`, where `Stacks.EtaleCohomology.compactlySupportedCohomology` is
constructed. An equivalence of abelian categories is exact in both directions, so it induces an
equivalence of bounded below derived categories.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleDerivedPlusEquiv`: the equivalence of bounded below derived
  categories of sheaves of `Λ`-modules on `SmallEtale` and on Mathlib's small étale site.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomology`: `K ↦ RΓ_c(X, K)` on the bounded
  below derived category of sheaves of `Λ`-modules on the small étale site of `X`.
* `AlgebraicGeometry.SmallEtale.isTorsionPlus`, and
  `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyTorsion`: the restriction of
  `RΓ_c(X, -)` to the full subcategory `D⁺_tors(X)` of complexes with torsion cohomology sheaves.

## Main results

* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyIso`: on complexes coming from
  Mathlib's small étale site, the functor is `Stacks.EtaleCohomology.compactlySupportedCohomology`.

## Implementation notes

The source takes the base field separably closed; the formula uses no hypothesis on the field, so
the definition is given over any field. The compactification is an explicit argument, as in
`Stacks.EtaleCohomology.compactlySupportedCohomology`; the source suppresses it from the notation.
The source's domain is `D⁺_tors(X)`; since the formula uses no torsion hypothesis, the functor is
defined on the whole bounded below derived category, and its restriction to torsion complexes is
`compactlySupportedCohomologyTorsion`. The torsion condition is the one of
`Stacks.EtaleCohomology.isTorsionPlus`, read through `moduleDerivedPlusEquiv`. The derived
categories are those of the standard model `HasDerivedCategory.standard`. The coefficients are
`Λ`-modules in the universe `max (u + 1) r`, the one in which
`Stacks.EtaleCohomology.compactlySupportedCohomology` is constructed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

universe u r

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (Λ : Type r) [Ring Λ]

/-- Presheaves of `Λ`-modules on the small étale site of `X` can be sheafified, the site being
essentially small. -/
instance hasSheafify_moduleCat_max :
    HasSheafify (topology B X hX) (ModuleCat.{max (u + 1) r} Λ) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) r} _ _

/-- The equivalence between sheaves of `Λ`-modules on the small étale site `SmallEtale` of `X`
and on Mathlib's small étale site of `X`. -/
abbrev moduleSheafEquiv :
    Sheaf (topology B X hX) (ModuleCat.{max (u + 1) r} Λ) ≌
      Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X :=
  sheafEquiv B X hX (ModuleCat.{max (u + 1) r} Λ)

instance additive_moduleSheafEquiv_functor : (moduleSheafEquiv B X hX Λ).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance additive_moduleSheafEquiv_inverse : (moduleSheafEquiv B X hX Λ).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The equivalence of bounded below derived categories** of sheaves of `Λ`-modules on the small
étale site `SmallEtale` of `X` and on Mathlib's small étale site of `X`, induced degreewise by the
equivalence of sheaf categories `moduleSheafEquiv`. -/
def moduleDerivedPlusEquiv :
    DerivedCategory.Plus (Sheaf (topology B X hX) (ModuleCat.{max (u + 1) r} Λ)) ≌
      DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X) :=
  CategoryTheory.Equivalence.mk (moduleSheafEquiv B X hX Λ).functor.mapDerivedCategoryPlus
    (moduleSheafEquiv B X hX Λ).inverse.mapDerivedCategoryPlus
    (Functor.mapDerivedCategoryPlusIdIso.symm ≪≫
      (Functor.mapDerivedCategoryPlusCompIsoh (moduleSheafEquiv B X hX Λ).unitIso.symm).symm)
    (Functor.mapDerivedCategoryPlusCompIsoh (moduleSheafEquiv B X hX Λ).counitIso ≪≫
      Functor.mapDerivedCategoryPlusIdIso)

@[simp]
theorem moduleDerivedPlusEquiv_functor :
    (moduleDerivedPlusEquiv B X hX Λ).functor =
      (moduleSheafEquiv B X hX Λ).functor.mapDerivedCategoryPlus :=
  rfl

@[simp]
theorem moduleDerivedPlusEquiv_inverse :
    (moduleDerivedPlusEquiv B X hX Λ).inverse =
      (moduleSheafEquiv B X hX Λ).inverse.mapDerivedCategoryPlus :=
  rfl

variable (k : Type u) [Field k] {X} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

/-- **Cohomology with compact support**, `RΓ_c(X, K) = RΓ(Spec k, Rf_! K)`, of a bounded below
complex `K` of sheaves of `Λ`-modules on the small étale site of a separated finite type
`k`-scheme `X`, computed through the compactification `j` of `f : X ⟶ Spec k`; the value is an
object of the bounded below derived category of `Λ`-modules. -/
@[weil "def_fk108_compact_support_cohomology_derived"]
abbrev compactlySupportedCohomology (j : CompactificationOf (Over.mk f)) :
    DerivedCategory.Plus (Sheaf (topology B X hX) (ModuleCat.{max (u + 1) r} Λ)) ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (moduleDerivedPlusEquiv B X hX Λ).functor ⋙
    Stacks.EtaleCohomology.compactlySupportedCohomology.{u, r} k f j Λ

/-- `RΓ_c(X, -)` on `SmallEtale` is `Stacks.EtaleCohomology.compactlySupportedCohomology` on
Mathlib's small étale site, transported along `moduleDerivedPlusEquiv`. -/
def compactlySupportedCohomologyIso (j : CompactificationOf (Over.mk f)) :
    (moduleDerivedPlusEquiv B X hX Λ).inverse ⋙ compactlySupportedCohomology B hX Λ k f j ≅
      Stacks.EtaleCohomology.compactlySupportedCohomology.{u, r} k f j Λ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedPlusEquiv B X hX Λ).counitIso _ ≪≫
    Functor.leftUnitor _

variable (X) in
/-- The objects of the bounded below derived category of sheaves of `Λ`-modules on the small
étale site of `X` all of whose cohomology sheaves are torsion: the subcategory `D⁺_tors(X)`. -/
def isTorsionPlus :
    ObjectProperty (DerivedCategory.Plus (Sheaf (topology B X hX) (ModuleCat.{max (u + 1) r} Λ))) :=
  (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X).inverseImage
    (moduleDerivedPlusEquiv B X hX Λ).functor

/-- **Cohomology with compact support** `RΓ_c(X, K)` on the subcategory `D⁺_tors(X)` of bounded
below complexes with torsion cohomology sheaves, which is the domain the source states the
definition on. -/
@[weil "def_fk108_compact_support_cohomology_derived"]
abbrev compactlySupportedCohomologyTorsion (j : CompactificationOf (Over.mk f)) :
    (isTorsionPlus B X hX Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (isTorsionPlus B X hX Λ).ι ⋙ compactlySupportedCohomology B hX Λ k f j

end AlgebraicGeometry.SmallEtale

end
