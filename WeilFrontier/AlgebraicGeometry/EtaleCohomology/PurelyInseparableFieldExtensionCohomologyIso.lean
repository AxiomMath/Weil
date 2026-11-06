/-
Copyright (c) 2026 Weil project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UniversalHomeomorphismInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.Attr

/-!
# Étale cohomology is invariant under purely inseparable extension of the base field

Let `k` be a field, `X` a scheme over `k`, `L / k` a purely inseparable field extension, possibly
infinite, and `G` an abelian sheaf on the small étale site of `X`. Then for every `ν ≥ 0` the
restriction map `H^ν(X, G) → H^ν(X ⊗_k L, h^* G)` along the projection `h : X ⊗_k L ⟶ X` is an
isomorphism.

The morphism `Spec L ⟶ Spec k` is a universal homeomorphism, hence so is its base change `h`.
For a universal homeomorphism `f` the inverse image `f^*` on abelian sheaves of the small étale
sites is an equivalence; an equivalence induces bijections on all `Ext`-groups and `f^*` carries
the constant sheaf `ℤ` to the constant sheaf `ℤ`, so the restriction map on cohomology is
bijective.

## Main results

* `SmallEtale.bijective_smallEtaleCohomologyRestrictionMap_of_universalHomeomorphism`:
  for a universal homeomorphism `f`, the restriction map `H^ν(S, G) →+ H^ν(T, f^* G)` is bijective.
* `AlgebraicGeometry.SmallEtale.bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec`:
  for the base change `h : X ⊗_k L ⟶ X` along a purely inseparable field extension `L / k`, the
  restriction map `H^ν(X, G) →+ H^ν(X ⊗_k L, h^* G)` is bijective.
* `AlgebraicGeometry.SmallEtale.cohomologyAddEquivOfIsPullbackSpec`: the resulting isomorphism.

## Implementation notes

The source passes to the limit over the finite subextensions of `L / k`, using the invariance
of cohomology under finite purely inseparable morphisms at each finite level and the
commutation of cohomology with limits of schemes with affine transition maps. Here the
projection `X ⊗_k L ⟶ X` is shown directly to be a universal homeomorphism, being a base
change of `Spec L ⟶ Spec k`, and the invariance of étale cohomology under universal
homeomorphisms (Stacks 03SI) is applied to it; no limit argument is needed. The hypotheses that
`X` is of finite type and separated over `k` are not used.

The scheme `X ⊗_k L` is an object of the big étale site `B`, which is size-bounded, so it is
given as an object `XL` of `B` together with a pullback square exhibiting
`XL = X ×_{Spec k} Spec L`. The restriction map is
`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`, the inverse image on `Ext`-groups out of
the constant sheaf `ℤ` precomposed with the constant-sheaf comparison.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian

universe w u

namespace AlgebraicGeometry.SmallEtale

section UniversalHomeomorphism

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} (f : T ⟶ S)
  [HasExt.{w} (Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (topology B T.obj T.property) AddCommGrpCat.{u + 1})]

/-- **Étale cohomology is invariant under universal homeomorphisms.** For a universal
homeomorphism `f : T ⟶ S` and an abelian sheaf `G` on the small étale site of `S`, the
restriction map `H^ν(S, G) →+ H^ν(T, f^* G)` is bijective for every `ν`. -/
theorem bijective_smallEtaleCohomologyRestrictionMap_of_universalHomeomorphism
    [UniversalHomeomorphism (B.inclusion.map f)]
    (G : Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap B f G ν) := by
  let E := smallEtaleInverseImage B f AddCommGrpCat.{u + 1}
  have := isEquivalence_smallPushforward_of_universalHomeomorphism f AddCommGrpCat.{u + 1}
  have : E.IsEquivalence :=
    (smallEtaleInverseImageAdjunction B f
      AddCommGrpCat.{u + 1}).isEquivalence_left_of_isEquivalence_right
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact (Stacks.EtaleCohomology.ext_precomp_iso_bijective
      (smallEtaleInverseImageConstantSheafIso B f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift ℤ))) ν).comp
    (Functor.mapExt_bijective_of_preservesInjectiveObjects E _ G ν)

end UniversalHomeomorphism

section FieldExtension

variable {B : BigEtaleSite.{u}} (k L : Type u) [Field k] [Field L] [Algebra k L]
  [IsPurelyInseparable k L] {X XL : B.Scheme} (s : B.inclusion.obj X ⟶ Spec (.of k))
  (h : XL ⟶ X) (p : B.inclusion.obj XL ⟶ Spec (.of L))

/-- The projection `X ×_{Spec k} Spec L ⟶ X` along a purely inseparable field extension `L / k`
is a universal homeomorphism. -/
theorem universalHomeomorphism_of_isPullback_spec
    (sq : IsPullback (B.inclusion.map h) p s (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    UniversalHomeomorphism (B.inclusion.map h) :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip
    (Stacks.EtaleCohomology.specMap_universalHomeomorphism_of_isPurelyInseparable
      k L).universally_isHomeomorph⟩

variable
  [HasExt.{w} (Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (topology B XL.obj XL.property) AddCommGrpCat.{u + 1})]

/-- **Étale cohomology is invariant under purely inseparable extension of the base field.**
Let `X` be a scheme over a field `k` (structure morphism `s`), `L / k` a purely inseparable field
extension, possibly infinite, and `h : X ⊗_k L ⟶ X` the projection, where `X ⊗_k L` is given with
a pullback square over `Spec L ⟶ Spec k`. For every abelian sheaf `G` on the small étale site of
`X` and every `ν`, the restriction map `H^ν(X, G) →+ H^ν(X ⊗_k L, h^* G)` is bijective. -/
@[weil "thm_fk103_purely_inseparable_field_extension_cohomology_iso"]
theorem bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec
    (sq : IsPullback (B.inclusion.map h) p s (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (G : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap B h G ν) := by
  have := universalHomeomorphism_of_isPullback_spec k L s h p sq
  exact bijective_smallEtaleCohomologyRestrictionMap_of_universalHomeomorphism h G ν

/-- **The isomorphism `H^ν(X, G) ≃+ H^ν(X ⊗_k L, h^* G)`** for the projection
`h : X ⊗_k L ⟶ X` along a purely inseparable field extension `L / k`: the restriction map, which
is bijective. -/
def cohomologyAddEquivOfIsPullbackSpec
    (sq : IsPullback (B.inclusion.map h) p s (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (G : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    G.H ν ≃+ ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj G).H ν :=
  AddEquiv.ofBijective (smallEtaleCohomologyRestrictionMap B h G ν)
    (bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec k L s h p sq G ν)

@[simp]
lemma cohomologyAddEquivOfIsPullbackSpec_apply
    (sq : IsPullback (B.inclusion.map h) p s (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (G : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1}) (ν : ℕ) (x : G.H ν) :
    cohomologyAddEquivOfIsPullbackSpec k L s h p sq G ν x =
      smallEtaleCohomologyRestrictionMap B h G ν x :=
  rfl

end FieldExtension

end AlgebraicGeometry.SmallEtale

end
