/-
Copyright (c) 2026 Weil project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UniversalHomeomorphismInvariance
public import Weil.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Weil.Attr

/-!
# Étale cohomology is invariant under purely inseparable morphisms

Let `f : X ⟶ Y` be a purely inseparable morphism of schemes (finite, universally injective and
surjective) and `G` an abelian sheaf on the small étale site of `Y`. Then for every `ν ≥ 0` the
restriction map `H^ν(Y, G) ⟶ H^ν(X, f^* G)` is an isomorphism.

The inverse image `f^*` is an equivalence of the categories of abelian sheaves
(`AlgebraicGeometry.SmallEtale.smallEtaleInverseImageEquivOfIsPurelyInseparable`). An exact,
fully faithful functor preserving injective objects induces bijections on all `Ext`-groups, and
`f^*` carries the constant sheaf `ℤ_Y` to the constant sheaf `ℤ_X`; since cohomology is `Ext`
out of the constant sheaf `ℤ`, the restriction map is bijective.

## Main results

* `SmallEtale.bijective_smallEtaleCohomologyRestrictionMap_of_isPurelyInseparable`:
  for a purely inseparable `f`, the restriction map `H^ν(Y, G) →+ H^ν(X, f^* G)` is bijective.
* `AlgebraicGeometry.SmallEtale.cohomologyAddEquivOfIsPurelyInseparable`: the resulting
  isomorphism `H^ν(Y, G) ≃+ H^ν(X, f^* G)`.

## Implementation notes

The source argues with an injective resolution `G → I^•` on `Y`, whose image `f^* G → f^* I^•`
is an injective resolution on `X` with the same complex of global sections. Here cohomology is
`CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ`, and the same
observation (an equivalence preserves injective objects) is used in the form of
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`. The isomorphism obtained
is the canonical restriction map `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`, which
is more than the existence of an isomorphism asserted by the source. Coefficients are abelian
groups in the universe `u + 1`, where the inverse image is defined.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian

universe w u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} (f : T ⟶ S)
  [HasExt.{w} (Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (topology B T.obj T.property) AddCommGrpCat.{u + 1})]

/-- **Étale cohomology is invariant under purely inseparable morphisms.** For a purely
inseparable morphism `f : T ⟶ S` and an abelian sheaf `G` on the small étale site of `S`, the
restriction map `H^ν(S, G) →+ H^ν(T, f^* G)` is bijective for every `ν`. -/
@[weil "lem_fk103_purely_inseparable_cohomology_iso"]
theorem bijective_smallEtaleCohomologyRestrictionMap_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (G : Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap B f G ν) := by
  let E := smallEtaleInverseImage B f AddCommGrpCat.{u + 1}
  have : E.IsEquivalence :=
    (smallEtaleInverseImageEquivOfIsPurelyInseparable f AddCommGrpCat.{u + 1}
      hf).isEquivalence_functor
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact (Stacks.EtaleCohomology.ext_precomp_iso_bijective
      (smallEtaleInverseImageConstantSheafIso B f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift ℤ))) ν).comp
    (Functor.mapExt_bijective_of_preservesInjectiveObjects E _ G ν)

/-- **The isomorphism `H^ν(S, G) ≃+ H^ν(T, f^* G)`** for a purely inseparable morphism
`f : T ⟶ S` and an abelian sheaf `G` on the small étale site of `S`: the restriction map, which
is bijective. -/
@[weil "lem_fk103_purely_inseparable_cohomology_iso"]
def cohomologyAddEquivOfIsPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (G : Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    G.H ν ≃+ ((smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj G).H ν :=
  AddEquiv.ofBijective (smallEtaleCohomologyRestrictionMap B f G ν)
    (bijective_smallEtaleCohomologyRestrictionMap_of_isPurelyInseparable f hf G ν)

@[simp]
lemma cohomologyAddEquivOfIsPurelyInseparable_apply
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (G : Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}) (ν : ℕ) (x : G.H ν) :
    cohomologyAddEquivOfIsPurelyInseparable f hf G ν x =
      smallEtaleCohomologyRestrictionMap B f G ν x :=
  rfl

end AlgebraicGeometry.SmallEtale

end
