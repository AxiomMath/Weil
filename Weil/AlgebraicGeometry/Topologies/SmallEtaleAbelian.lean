module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian

/-!
# Sheaves of modules on the small étale site have enough injectives

Let `R` be a ring and `X` a scheme. The abelian category of sheaves of `R`-modules on the small
étale site of `X` is a Grothendieck abelian category: filtered colimits are exact and the
category has a generator. Hence it has enough injectives: every sheaf of `R`-modules embeds into
an injective one.

## Main results

* `ModuleCat.preservesFilteredColimitsOfSize_forget_of_small`: the forgetful functor of
  `ModuleCat.{u} R` preserves `u`-filtered colimits, for a `u`-small ring `R` in any universe.
* `AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat_of_small`: presheaves of `R`-modules on
  `SmallEtale B S hS` can be sheafified, for a `u`-small ring `R` in any universe.
* `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_moduleCat`: sheaves of `R`-modules on
  `SmallEtale B S hS` form a Grothendieck abelian category.
* `AlgebraicGeometry.SmallEtale.enoughInjectives_sheaf_moduleCat`: they have enough injectives.
* `AlgebraicGeometry.Scheme.enoughInjectives_etaleModules`: the same statement on Mathlib's small
  étale site `X.smallEtaleTopology`, for `Stacks.EtaleCohomology.EtaleModules`.

## Implementation notes

The ring is allowed to be noncommutative, and on `SmallEtale B S hS` the coefficients are
`ModuleCat.{u} R` for any ring `R` that is `u`-small. Both results are instances of the general
fact that a Grothendieck abelian category has enough injectives
(`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`); that sheaves on an essentially small
site with values in a Grothendieck abelian category form a Grothendieck abelian category is
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`. The generators of the source's
proof (free sheaves on representables) are subsumed by that result.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4]
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
-/

@[expose] public section

open CategoryTheory

universe u r

namespace ModuleCat

variable (R : Type r) [Ring R]

/-- The forgetful functor from `R`-modules in universe `u` to types preserves `u`-filtered
colimits, for a ring `R` in any universe: they are computed on underlying abelian groups. -/
theorem preservesFilteredColimitsOfSize_forget_of_small [Small.{u} R] :
    Limits.PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u} R)) :=
  let : Limits.PreservesColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u, r, u, u} R
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
    (forget AddCommGrpCat)

end ModuleCat

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (R : Type r) [Ring R]

/-- Presheaves of `R`-modules on the small étale site of `S` can be sheafified, for a `u`-small
ring `R` in any universe. StacksFrontier's `AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat` is
the same in the module universe `max (u + 1) r w`, stated as a theorem. -/
instance hasSheafify_moduleCat_of_small [Small.{u} R] :
    HasSheafify (topology B S hS) (ModuleCat.{u} R) :=
  have := ModuleCat.preservesFilteredColimitsOfSize_forget_of_small.{u, r} R
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Sheaves of `R`-modules on the small étale site of `S` form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_sheaf_moduleCat [Small.{u} R] :
    IsGrothendieckAbelian.{u} (Sheaf (topology B S hS) (ModuleCat.{u} R)) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Sheaves of `R`-modules on the small étale site of `S` have enough injectives. -/
@[weil "lem_fk104_r_module_sheaves_enough_injectives"]
instance enoughInjectives_sheaf_moduleCat [Small.{u} R] :
    EnoughInjectives (Sheaf (topology B S hS) (ModuleCat.{u} R)) :=
  IsGrothendieckAbelian.enoughInjectives

end SmallEtale

/-- Sheaves of `R`-modules on Mathlib's small étale site of `X` have enough injectives. -/
@[weil "lem_fk104_r_module_sheaves_enough_injectives"]
theorem Scheme.enoughInjectives_etaleModules (R : Type r) [Ring R] (X : Scheme.{u}) :
    EnoughInjectives (Stacks.EtaleCohomology.EtaleModules.{u, r} R X) :=
  inferInstance

end AlgebraicGeometry

end
