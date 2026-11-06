module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import Weil.Attr

/-!
# Direct image along a finite morphism is exact

Let `B` be a big étale site and `f : X ⟶ Y` a morphism of `B` whose underlying morphism of
schemes is integral, for instance finite. Then the direct image
`f_* : Ab(X_étale) ⥤ Ab(Y_étale)` of abelian sheaves on the small étale sites is an exact
functor: it preserves finite limits and finite colimits.

## Main results

* `AlgebraicGeometry.BigEtaleSite.smallPushforward_exact_of_isIntegralHom`: the direct image
  of abelian sheaves along an integral morphism is exact.
* `AlgebraicGeometry.BigEtaleSite.smallPushforward_exact_of_isFinite`: the direct image of
  abelian sheaves along a finite morphism is exact.

## Implementation notes

The integral case is transported from the corresponding statement on the small étale sites of
the underlying schemes, `Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom`,
along the comparison `AlgebraicGeometry.SmallEtale.smallPushforwardIsoSheafEquiv` of the two
direct images. The finite case is a special case, since a finite morphism is integral.

The proof by stalks, through the description of the stalk of `f_* F` at a geometric point as
the product of the stalks of `F` at the finitely many points of the geometric fibre, is not
needed: exactness follows from the fact that integral morphisms have property (B) of
[Stacks, Tag 04DR], so that direct image preserves surjections.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3]
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)

/-- The direct image `f_* : Ab(X_étale) ⥤ Ab(Y_étale)` along a morphism of a big étale site
whose underlying morphism of schemes is integral is an exact functor. -/
theorem smallPushforward_exact_of_isIntegralHom [IsIntegralHom (B.inclusion.map f)] :
    exactFunctor _ _ (B.smallPushforward f AddCommGrpCat.{u + 1}) := by
  have h := (exactFunctor_iff _).mp
    (Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom (B.inclusion.map f))
  have : PreservesFiniteLimits
      (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} (B.inclusion.map f)) := h.1
  have h2 : PreservesFiniteColimits
      (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} (B.inclusion.map f)) := h.2
  exact (exactFunctor _ _).prop_of_iso (SmallEtale.smallPushforwardIsoSheafEquiv f).symm
    ((exactFunctor_iff _).mpr ⟨inferInstance,
      @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ inferInstance
        (@comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h2 inferInstance)⟩)

/-- **Freitag–Kiehl, I.3.** The direct image `f_* : Ab(X_étale) ⥤ Ab(Y_étale)` along a
finite morphism `f` is an exact functor. -/
@[weil "lem_fk103_finite_direct_image_exact"]
theorem smallPushforward_exact_of_isFinite [IsFinite (B.inclusion.map f)] :
    exactFunctor _ _ (B.smallPushforward f AddCommGrpCat.{u + 1}) :=
  smallPushforward_exact_of_isIntegralHom f

end AlgebraicGeometry.BigEtaleSite

end
