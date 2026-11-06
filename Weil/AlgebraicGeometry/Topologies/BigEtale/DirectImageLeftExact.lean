module

public import Weil.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Limits
public import Weil.Attr

/-!
# The direct image of étale sheaves is additive and left exact

Let `B` be a big étale site and `f : X ⟶ Y` a morphism of it. The direct image
`f_* : Sh(X_et, A) ⥤ Sh(Y_et, A)`, `(f_* F)(U) = F(U ×_Y X)`, preserves every limit that exists
in `A`: limits of sheaves are computed objectwise, and on presheaves `f_*` is precomposition with
base change, which commutes with objectwise limits. In particular `f_*` is left exact. When `A` is
preadditive, `f_*` is additive, since the sum of two morphisms of sheaves is computed objectwise.
For `A` the category of abelian groups this is the statement that
`f_* : Sh(X_et, Ab) ⥤ Sh(Y_et, Ab)` is additive and left exact.

## Main results

* `AlgebraicGeometry.BigEtaleSite.preservesLimitsOfShape_smallPushforward`: `f_*` preserves
  limits of any shape that `A` has.
* `AlgebraicGeometry.BigEtaleSite.preservesFiniteLimits_smallPushforward`: `f_*` is left exact.
* `AlgebraicGeometry.BigEtaleSite.additive_smallPushforward`: `f_*` is additive.

## Implementation notes

The statements are made for sheaves with values in an arbitrary category `A` (with the limits,
resp. the preadditive structure, needed), abelian groups being the case of the source. Left
exactness is stated as preservation of finite limits, which for an additive functor between
abelian categories is preservation of kernels.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2]
* [Stacks Project, Tag 03PY](https://stacks.math.columbia.edu/tag/03PY)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w' w v u

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) (A : Type w) [Category.{v} A]

/-- **The direct image of étale sheaves preserves limits**: if `A` has limits of shape `K`, then
`f_* : Sh(X_et, A) ⥤ Sh(Y_et, A)` preserves limits of shape `K`. -/
instance preservesLimitsOfShape_smallPushforward (K : Type w') [Category K]
    [HasLimitsOfShape K A] : PreservesLimitsOfShape K (B.smallPushforward f A) := by
  have : PreservesLimitsOfShape K
      (B.smallPushforward f A ⋙ sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) A) :=
    preservesLimitsOfShape_of_natIso
      ((smallEtaleBaseChange B f).sheafPushforwardContinuousCompSheafToPresheafIso A
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) A)

/-- **The direct image of étale sheaves is left exact**: if `A` has finite limits, then
`f_* : Sh(X_et, A) ⥤ Sh(Y_et, A)` preserves finite limits (for abelian groups: kernels). -/
@[weil "lem_fk102_direct_image_left_exact"]
instance preservesFiniteLimits_smallPushforward [HasFiniteLimits A] :
    PreservesFiniteLimits (B.smallPushforward f A) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- **The direct image of étale sheaves is additive**: for a preadditive category `A`,
`f_* : Sh(X_et, A) ⥤ Sh(Y_et, A)` sends a sum of morphisms of sheaves to the sum of their
direct images. -/
@[weil "lem_fk102_direct_image_left_exact"]
instance additive_smallPushforward [Preadditive A] : (B.smallPushforward f A).Additive where
  map_add := rfl

/-- The direct image `f_* : Sh(X_et, Ab) ⥤ Sh(Y_et, Ab)` of étale sheaves of abelian groups is
additive and left exact. -/
example : (B.smallPushforward f AddCommGrpCat.{v}).Additive ∧
    PreservesFiniteLimits (B.smallPushforward f AddCommGrpCat.{v}) :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.BigEtaleSite
