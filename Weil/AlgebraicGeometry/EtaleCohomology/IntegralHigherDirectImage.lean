module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Attr

/-!
# Higher direct images along finite morphisms vanish

Let `B` be a big étale site and `f : X ⟶ Y` a morphism of it whose underlying morphism of
schemes is integral, for instance finite. Direct image `f_*` of sheaves on the small étale sites
then carries epimorphisms to epimorphisms; being a right adjoint it is left exact, so it is an
exact functor of abelian sheaves. Applied to an injective resolution of an abelian sheaf `G` it
gives a resolution of `f_* G`, so the higher direct images `R^ν f_* G` vanish for `ν > 0`.

## Main results

In the namespace `AlgebraicGeometry.BigEtaleSite`:

* `smallPushforward_type_preservesEpimorphisms_of_isIntegralHom`,
  `smallPushforward_addCommGrpCat_preservesEpimorphisms_of_isIntegralHom`: direct image along an
  integral morphism preserves epimorphisms of sheaves of sets and of abelian sheaves on the small
  étale sites.
* `isZero_higherDirectImage_obj_of_isIntegralHom`: `R^ν f_* G = 0` for `ν > 0` and `f` integral.
* `isZero_higherDirectImage_obj_of_isFinite`: the same for `f` finite.

## Implementation notes

On Mathlib's small étale sites, preservation of epimorphisms of sheaves of sets along an integral
morphism is `Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom`.
It is carried to the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of `B` through
the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` and the comparison of direct images
`AlgebraicGeometry.SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso`. For abelian sheaves an
epimorphism is a locally surjective morphism, a property of the underlying sheaves of sets, and
direct image commutes with taking underlying sheaves of sets.

The result is stated for integral morphisms, which contain the finite ones.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.3
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- Direct image of sheaves of sets on the small étale sites along an integral morphism preserves
epimorphisms. -/
theorem smallPushforward_type_preservesEpimorphisms_of_isIntegralHom
    [UnivLE.{u, w}] [IsIntegralHom (B.inclusion.map f)] :
    (B.smallPushforward f (Type w)).PreservesEpimorphisms := by
  constructor
  intro F G φ hφ
  let EX := SmallEtale.sheafEquiv B X.1 X.property (Type w)
  let EY := SmallEtale.sheafEquiv B Y.1 Y.property (Type w)
  have h1 : Epi (EX.functor.map φ) := EX.functor.map_epi φ
  have h2 : Epi (((Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous (Type w) Y.obj.smallEtaleTopology
        X.obj.smallEtaleTopology).map (EX.functor.map φ)) :=
    (Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom
      (B.inclusion.map f)).preserves _
  have h3 : Epi ((B.smallPushforward f (Type w) ⋙ EY.functor).map φ) := by
    let e := SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f (Type w)
    exact ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso e φ)).2 h2
  constructor
  intro Z g h hgh
  apply EY.functor.map_injective
  rw [← cancel_epi ((B.smallPushforward f (Type w) ⋙ EY.functor).map φ), Functor.comp_map,
    ← EY.functor.map_comp, ← EY.functor.map_comp, hgh]

/-- Direct image of abelian sheaves on the small étale sites along an integral morphism preserves
epimorphisms. -/
theorem smallPushforward_addCommGrpCat_preservesEpimorphisms_of_isIntegralHom
    [UnivLE.{u, w}] [IsIntegralHom (B.inclusion.map f)]
    [HasSheafify (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w}]
    [HasSheafify (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{w}]
    [HasSheafify (SmallEtale.topology B Y.1 Y.property) (Type w)]
    [(SmallEtale.topology B X.1 X.property).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (B.smallPushforward f AddCommGrpCat.{w}).PreservesEpimorphisms := by
  have hset := smallPushforward_type_preservesEpimorphisms_of_isIntegralHom.{w} B f
  constructor
  intro F G φ hφ
  have hloc : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} φ).2 hφ
  have : Epi ((sheafCompose (SmallEtale.topology B X.1 X.property)
      (forget AddCommGrpCat.{w})).map φ) := Sheaf.epi_of_isLocallySurjective _
  have hset' : Epi ((B.smallPushforward f (Type w)).map
      ((sheafCompose (SmallEtale.topology B X.1 X.property) (forget AddCommGrpCat.{w})).map φ)) :=
    hset.preserves _
  have hforget : Epi ((sheafCompose (SmallEtale.topology B Y.1 Y.property)
      (forget AddCommGrpCat.{w})).map ((B.smallPushforward f AddCommGrpCat.{w}).map φ)) := hset'
  have hlocforget : Sheaf.IsLocallySurjective
      ((sheafCompose (SmallEtale.topology B Y.1 Y.property) (forget AddCommGrpCat.{w})).map
        ((B.smallPushforward f AddCommGrpCat.{w}).map φ)) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hforget
  have : Sheaf.IsLocallySurjective ((B.smallPushforward f AddCommGrpCat.{w}).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget _ _).2 hlocforget
  exact Sheaf.epi_of_isLocallySurjective _

/-- **Higher direct images along an integral morphism vanish**: for an abelian sheaf `G` on the
small étale site of `X`, `R^ν f_* G = 0` for every `ν > 0`. -/
theorem isZero_higherDirectImage_obj_of_isIntegralHom
    [UnivLE.{u, w}] [IsIntegralHom (B.inclusion.map f)]
    [HasSheafify (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w}]
    [HasSheafify (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{w}]
    [HasSheafify (SmallEtale.topology B Y.1 Y.property) (Type w)]
    [(SmallEtale.topology B X.1 X.property).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w})]
    (G : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w}) {ν : ℕ} (hν : 0 < ν) :
    IsZero ((higherDirectImage B f ν).obj G) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hν.ne'
  have := smallPushforward_addCommGrpCat_preservesEpimorphisms_of_isIntegralHom.{w} B f
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (B.smallPushforward f AddCommGrpCat.{w})
  exact Stacks.RightDerivedTransport.isZero_rightDerived_succ_of_preservesHomology _ n G

/-- **Higher direct images along a finite morphism vanish**: for a finite morphism `f : X ⟶ Y`
and an abelian sheaf `G` on the small étale site of `X`, `R^ν f_* G = 0` for every `ν > 0`. -/
@[weil "lem_fk103_finite_higher_direct_images_vanish"]
theorem isZero_higherDirectImage_obj_of_isFinite
    [UnivLE.{u, w}] [IsFinite (B.inclusion.map f)]
    [HasSheafify (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w}]
    [HasSheafify (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{w}]
    [HasSheafify (SmallEtale.topology B Y.1 Y.property) (Type w)]
    [(SmallEtale.topology B X.1 X.property).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w})]
    (G : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{w}) {ν : ℕ} (hν : 0 < ν) :
    IsZero ((higherDirectImage B f ν).obj G) :=
  isZero_higherDirectImage_obj_of_isIntegralHom B f G hν

end AlgebraicGeometry.BigEtaleSite
