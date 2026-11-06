module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import Weil.Defs.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import Weil.Attr

/-!
# The derived direct image with proper support

Let `f : X ⟶ S` be a morphism of schemes and `c = (X̄, j, f̄)` a compactification of `f`: an open
immersion `j : X ⟶ X̄` followed by a proper morphism `f̄ : X̄ ⟶ S` with `j ≫ f̄ = f`. The derived
direct image with proper support of a bounded below complex `K` of étale sheaves on `X` is
`Rf_! K = R f̄_* (j_! K)`, an object of the bounded below derived category of étale sheaves on
`S`: extend `K` by zero to `X̄` and take the total right derived direct image along `f̄`,
computed by applying `f̄_*` to an injective resolution of `j_! K`.
The compactification is part of the data.

On the small étale sites of Mathlib this is `Stacks.EtaleCohomology.derivedLowerShriek`. This file
gives the same functor on the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of a
big étale site `B`, by transport along the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the two categories of sheaves.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleSheafEquivEtaleModules`: the equivalence between sheaves of
  `Λ`-modules on the small étale site `SmallEtale B X` and on Mathlib's small étale site of `X`.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriek`: the functor
  `Rf_! = R f̄_* ∘ j_! : D⁺(X, Λ) ⥤ D⁺(S, Λ)` attached to a compactification of `f`, on the small
  étale sites of `B`.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedLowerShriek_obj`: `Rf_! K` is the derived direct image
  `R f̄_* (j_! K)` of Mathlib's small étale sites, read back on `SmallEtale B S`.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekCompIso`: the comparison
  `Rf_! ⋙ E_S ≅ E_X ⋙ Rf_!` with the derived lower shriek of Mathlib's small étale sites, for `E`
  the equivalences of sheaf categories.
* `AlgebraicGeometry.SmallEtale.sheafEquivInverseCompDerivedLowerShriekIso`: the comparison
  `E_X⁻¹ ⋙ Rf_! ≅ Rf_! ⋙ E_S⁻¹`.

## Implementation notes

The source defines `Rf_!` on the bounded below complexes with torsion cohomology sheaves and for
abelian sheaves. The formula uses neither restriction, so the functor here is defined on the whole
bounded below derived category of sheaves of `Λ`-modules for an arbitrary ring `Λ`; the source's
functor is its restriction to the torsion complexes and to `Λ = ℤ`. The derived categories are the
ones of `HasDerivedCategory.standard`, as for `Stacks.EtaleCohomology.derivedLowerShriek`, and the
sheaf categories are `AlgebraicGeometry.SmallEtale.ModuleSheaf`, with coefficients in the
universe `max (u + 1) r` in which that functor is defined.

The schemes `X` and `S` are objects of `B`, so that their small étale sites are defined; the
compactification `X̄` need not be, since the derived direct image along `f̄` is taken on
Mathlib's small étale sites.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 86][FreitagKiehl]
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- Sheaves of `Λ`-modules on the small étale site `SmallEtale B X` of an object `X` of a big
étale site are sheaves of `Λ`-modules on Mathlib's small étale site of `X`: the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`, with the limits it needs supplied in the coefficient
universe. -/
abbrev moduleSheafEquivEtaleModules (X : B.Scheme) :
    ModuleSheaf.{u, r, r} B X Λ ≌ Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X.obj :=
  @sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ) _
    (ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) r, r})

instance (X : B.Scheme) : (moduleSheafEquivEtaleModules B Λ X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance (X : B.Scheme) : (moduleSheafEquivEtaleModules B Λ X).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

variable {B} {X S : B.Scheme} (f : X.obj ⟶ S.obj) (c : f.Compactification)

/-- **The derived direct image with proper support** `Rf_! = R f̄_* ∘ j_!` attached to a
compactification `c = (X̄, j, f̄)` of `f : X ⟶ S`, on the bounded below derived categories of
sheaves of `Λ`-modules on the small étale sites of `X` and `S`: `Rf_! K = R f̄_* (j_! K)`. -/
@[weil "def_fk108_proper_direct_image_derived"]
def derivedLowerShriek :
    DerivedCategory.Plus (ModuleSheaf.{u, r, r} B X Λ) ⥤
      DerivedCategory.Plus (ModuleSheaf.{u, r, r} B S Λ) :=
  (moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙
    Stacks.EtaleCohomology.derivedLowerShriek f c Λ ⋙
    (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus

/-- `Rf_! K = R f̄_* (j_! K)`: the value of `Rf_!` is the derived direct image along `f̄` of the
extension by zero along `j`, on Mathlib's small étale sites, read back on `SmallEtale B S`. -/
@[weil "def_fk108_proper_direct_image_derived"]
theorem derivedLowerShriek_obj (K : DerivedCategory.Plus (ModuleSheaf.{u, r, r} B X Λ)) :
    (derivedLowerShriek Λ f c).obj K =
      (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus.obj
        ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImage.{u, r} Λ c.toBase).obj
          ((Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZero.{u, r} Λ c.immersion).obj
            ((moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus.obj K))) :=
  rfl

/-- The functor induced on bounded below derived categories by an equivalence `E`, followed by
the one induced by its inverse, is the identity: `E⁻¹ ⋙ E ≅ 𝟭` on `D⁺`. -/
def mapDerivedCategoryPlusInverseCompFunctorIso (Y : B.Scheme) :
    (moduleSheafEquivEtaleModules B Λ Y).inverse.mapDerivedCategoryPlus ⋙
        (moduleSheafEquivEtaleModules B Λ Y).functor.mapDerivedCategoryPlus ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryPlusCompIsoh (moduleSheafEquivEtaleModules B Λ Y).counitIso ≪≫
    Functor.mapDerivedCategoryPlusIdIso

/-- The functor induced on bounded below derived categories by the inverse of an equivalence `E`,
followed by the one induced by `E`, is the identity: `E ⋙ E⁻¹ ≅ 𝟭` on `D⁺`. -/
def mapDerivedCategoryPlusFunctorCompInverseIso (Y : B.Scheme) :
    (moduleSheafEquivEtaleModules B Λ Y).functor.mapDerivedCategoryPlus ⋙
        (moduleSheafEquivEtaleModules B Λ Y).inverse.mapDerivedCategoryPlus ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryPlusCompIsoh (moduleSheafEquivEtaleModules B Λ Y).unitIso.symm ≪≫
    Functor.mapDerivedCategoryPlusIdIso

/-- `Rf_!` on the small étale sites of `B` is the derived lower shriek
`Stacks.EtaleCohomology.derivedLowerShriek` of Mathlib's small étale sites, across the
equivalences `E` of the sheaf categories: `Rf_! ⋙ E_S ≅ E_X ⋙ Rf_!`. -/
@[weil "def_fk108_proper_direct_image_derived"]
def derivedLowerShriekCompIso :
    derivedLowerShriek Λ f c ⋙
        (moduleSheafEquivEtaleModules B Λ S).functor.mapDerivedCategoryPlus ≅
      (moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙
        Stacks.EtaleCohomology.derivedLowerShriek f c Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (mapDerivedCategoryPlusInverseCompFunctorIso Λ S) ≪≫
      Functor.rightUnitor _)

/-- `E_X⁻¹ ⋙ Rf_! ≅ Rf_! ⋙ E_S⁻¹`, for `Rf_!` on the small étale sites of `B` on the left and on
Mathlib's small étale sites on the right. -/
def sheafEquivInverseCompDerivedLowerShriekIso :
    (moduleSheafEquivEtaleModules B Λ X).inverse.mapDerivedCategoryPlus ⋙
        derivedLowerShriek Λ f c ≅
      Stacks.EtaleCohomology.derivedLowerShriek f c Λ ⋙
        (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryPlusInverseCompFunctorIso Λ X) _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.SmallEtale
