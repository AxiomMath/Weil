module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# The derived category of abelian étale sheaves

For a scheme `S` contained in a big étale site `B`, the derived category `D(S) = D(S, ℤ)` is the
unbounded derived category of the abelian category of sheaves of abelian groups on the small
étale site of `S`.

An equivalence of abelian categories is exact, so it induces an equivalence of unbounded derived
categories (`StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence`). Applied to the
equivalence between sheaves on the bounded small étale site `AlgebraicGeometry.SmallEtale B S hS`
and sheaves on Mathlib's small étale site `S.Etale`, this identifies the derived category of
abelian sheaves on the bounded site with `Stacks.EtaleCohomology.smallEtaleDerivedCategory S`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.AbelianDerivedCategory B S hS`: the derived category `D(S)` of
  sheaves of abelian groups on the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.derivedCategoryEquiv`: the equivalence between the derived
  category of abelian sheaves on the bounded small étale site and
  `Stacks.EtaleCohomology.smallEtaleDerivedCategory S`, with coefficients in the universe of the
  objects of the site.

## Implementation notes

As in `Stacks.EtaleCohomology.smallEtaleDerivedCategory`, derived categories are formed with the
standard localization `HasDerivedCategory.standard`, enabled as a local instance; a consumer
enables it the same way.

`AlgebraicGeometry.SmallEtale.AbelianDerivedCategory` takes coefficients in the universe `u` of
morphisms of the site, where the category of abelian sheaves is abelian and Grothendieck abelian
by `AlgebraicGeometry.SmallEtale.abelian_sheaf` and
`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf`. The comparison with
`Stacks.EtaleCohomology.smallEtaleDerivedCategory S`, whose coefficients are in the universe
`u + 1`, is stated with coefficients in `u + 1` on both sides; there the category of abelian
sheaves on the bounded site is abelian by `CategoryTheory.sheafIsAbelian`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], Appendix A II
* [Stacks Project, Tag 05QI](https://stacks.math.columbia.edu/tag/05QI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The derived category `D(S) = D(S, ℤ)` of a scheme `S`: the unbounded derived category of
the abelian category of sheaves of abelian groups on the small étale site of `S`. -/
@[weil "not_fka2_derived_category_abelian_sheaves"]
abbrev AbelianDerivedCategory : Type (u + 1) :=
  DerivedCategory (Sheaf (topology B S hS) AddCommGrpCat.{u})

section CoefficientsSuccUniverse

/-- The functor of the equivalence between abelian sheaves on the bounded small étale site and
on Mathlib's small étale site is additive. -/
instance sheafEquiv_functor_additive :
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of the equivalence between abelian sheaves on the bounded small étale site and
on Mathlib's small étale site, which is restriction, is additive. -/
instance sheafEquiv_inverse_additive :
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] sheafIsAbelian

/-- The derived category of abelian sheaves on the bounded small étale site of `S`, with
coefficients in the universe of the objects of the site, is equivalent to
`Stacks.EtaleCohomology.smallEtaleDerivedCategory S`, the derived category of abelian sheaves on
Mathlib's small étale site: it is induced by the equivalence of the categories of sheaves. -/
noncomputable def derivedCategoryEquiv :
    DerivedCategory (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) ≌
      Stacks.EtaleCohomology.smallEtaleDerivedCategory S :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).unitIso
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).counitIso

@[simp]
theorem derivedCategoryEquiv_functor :
    (derivedCategoryEquiv B S hS).functor =
      (sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor.mapDerivedCategory :=
  rfl

@[simp]
theorem derivedCategoryEquiv_inverse :
    (derivedCategoryEquiv B S hS).inverse =
      (sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory :=
  rfl

end CoefficientsSuccUniverse

end AlgebraicGeometry.SmallEtale
