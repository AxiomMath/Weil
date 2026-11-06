module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import Weil.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Attr

/-!
# Higher direct images with proper support

Let `f : X ⟶ S` be a morphism of schemes with a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ S`
over `S` (an open immersion into a scheme proper over `S`), and `Λ` a ring. The derived direct
image with proper support is `Rf_! = Rf̄_* ∘ j_!` (`Stacks.EtaleCohomology.derivedLowerShriek`).
For a bounded below complex `K` of sheaves of `Λ`-modules on the small étale site of `X` and
`v : ℤ`, the `v`-th higher direct image with proper support is the sheaf
`R^v f_!(K) = H^v(Rf_!(K)) = R^v f̄_*(j_! K)` on the small étale site of `S`.

## Main definitions

* `AlgebraicGeometry.higherDirectImageProperSupport`: `K ↦ R^v f_!(K) = H^v(Rf_!(K))`, on the
  bounded below derived category.
* `AlgebraicGeometry.higherDirectImageProperSupportTorsion`: its restriction to the full
  subcategory `D⁺_tors(X)` of complexes with torsion cohomology sheaves.

## Main results

* `AlgebraicGeometry.higherDirectImageProperSupport_eq_rightDerivedFunctorPlusHomology`:
  `R^v f_!(K) = R^v f̄_*(j_! K)`, the classical derived functor of `f̄_*` applied to `j_! K`.
* `AlgebraicGeometry.lowerShriekHomology_eq_higherDirectImageProperSupport`: on a sheaf placed
  in degree `0`, `R^v f_!` is `Stacks.EtaleCohomology.lowerShriekHomology`.

## Implementation notes

The compactification is an explicit argument, as in `Stacks.EtaleCohomology.derivedLowerShriek`;
the source suppresses it from the notation. The functor is defined on the whole bounded below
derived category, since its formula uses no torsion hypothesis; the source's domain `D⁺_tors(X)`
is the restriction `higherDirectImageProperSupportTorsion`. The source takes `Λ = ℤ` (torsion
abelian sheaves); here `Λ` is any ring. The sheaves live on Mathlib's small étale site
`X.smallEtaleTopology`, where `Rf_!` is constructed. The derived categories are those of the
standard model `HasDerivedCategory.standard`, in which `Rf_!` is defined. In
`higherDirectImageProperSupport_eq_rightDerivedFunctorPlusHomology` the instance of enough
injectives on sheaves of modules on `X̄` is given explicitly: instance search leaves a universe
parameter of `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` unassigned there.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]

/-- The `v`-th **higher direct image with proper support** `R^v f_!(K) = H^v(Rf_!(K))` of a
bounded below complex `K` of sheaves of `Λ`-modules on the small étale site of `X`, computed
through the compactification `j` of `f`. -/
@[weil "def_fk108_higher_direct_image_proper_support"]
abbrev higherDirectImageProperSupport (v : ℤ) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤ EtaleModules.{u, r} Λ S :=
  derivedLowerShriek.{u, r} f j Λ ⋙
    DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, r} Λ S) v

/-- `R^v f_!` on the full subcategory `D⁺_tors(X)` of bounded below complexes with torsion
cohomology sheaves, the domain on which the source states the definition. -/
@[weil "def_fk108_higher_direct_image_proper_support"]
abbrev higherDirectImageProperSupportTorsion (v : ℤ) :
    (isTorsionPlus.{u, r} Λ X).FullSubcategory ⥤ EtaleModules.{u, r} Λ S :=
  (isTorsionPlus.{u, r} Λ X).ι ⋙ higherDirectImageProperSupport f j Λ v

/-- `R^v f_!(K) = R^v f̄_*(j_! K)`: the higher direct image with proper support is the `v`-th
classical derived functor of the direct image along `f̄ : X̄ ⟶ S`, applied to `j_! K`. -/
@[weil "def_fk108_higher_direct_image_proper_support"]
theorem higherDirectImageProperSupport_eq_rightDerivedFunctorPlusHomology (v : ℤ) :
    higherDirectImageProperSupport f j Λ v =
      etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⋙
        @Functor.rightDerivedFunctorPlusHomology _ _ _ _ _ _ _ _
          (etaleModuleDirectImage.{u, r} Λ j.toBase) _
          (Scheme.etaleSheaves_enoughInjectives.{u, 0, r} j.space Λ) v :=
  rfl

/-- For a sheaf `G` placed in degree `0`, `R^v f_!(G)` is
`Stacks.EtaleCohomology.lowerShriekHomology`. -/
theorem lowerShriekHomology_eq_higherDirectImageProperSupport (f : X ⟶ S)
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ] (v : ℤ) :
    lowerShriekHomology Λ f j v =
      singlePlus (EtaleModules.{u, 0} Λ X) ⋙ DerivedCategory.Plus.Q ⋙
        higherDirectImageProperSupport f j Λ v :=
  rfl

end AlgebraicGeometry
