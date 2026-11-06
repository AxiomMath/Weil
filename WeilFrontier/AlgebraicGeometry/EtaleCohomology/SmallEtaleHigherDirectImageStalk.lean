module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleHigherDirectImageStalk
public import Weil.Attr

/-!
# The values of the cohomology presheaves of a direct image

Let `f : X ⟶ Y` be a morphism of schemes, `F` an abelian sheaf on the small étale site of `X`
and `F → J^•` an injective resolution, and let `P^i_J` be the presheaf `U ↦ H^i((f_* J^•)(U))`
on the small étale site of `Y`. For an étale `U → Y` write `V = X ×_Y U`, an étale `X`-scheme,
and `F_U` for the restriction of `F` to the site localized at `V`. Then

`P^i_J(U) ≅ H^i(V, F_U)`,

the `i`-th cohomology of the localized site, i.e. the `i`-th right derived functor of the
sections over its terminal object `V → V` applied to `F_U`.

The proof follows the source: `(f_* J^•)(U)` is the complex of sections `J^•(V)`; restriction
to the localization at `V` is exact and preserves injective sheaves, so its value on `J^•` is an
injective resolution of `F_U`, whose global sections are again `J^•(V)`.

## Main results

* `Stacks.EtaleCohomology.directImageCohomologyPresheafObjIso`:
  `P^i_J(U) ≅ H^i(X ×_Y U, F|_{X ×_Y U})`.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale` with
`AlgebraicGeometry.Scheme.smallEtaleTopology`, the site on which the presheaf
`Stacks.EtaleCohomology.directImageCohomologyPresheaf` is defined, and `X ×_Y U` is the object
`(Stacks.EtaleCohomology.smallEtaleBaseChange f).obj U` of `X.Etale`. The restriction of `F` to
`X ×_Y U` is the restriction `CategoryTheory.GrothendieckTopology.overPullback` to the localized
site `X_ét / (X ×_Y U)`, as in the source, where the sites `Et(X)/V` and `Et(V)` are identified.

The isomorphism is the composite of the comparison of `P^i_J` with the derived functor of the
direct image (`Stacks.EtaleCohomology.directImageCohomologyPresheafIso`), of the exactness of
evaluation at `U` (`Stacks.DerivedFunctor.rightDerivedEvaluationIso`), and of the cohomology of a
localized site (`Stacks.Cohomology.LocalizedSite.overPullbackRightDerivedSectionsIso`, which
packages the exactness of restriction and the preservation of injectives).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitagkiehl1988], I.2
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **The value of the cohomology presheaf of a direct image.** For a morphism of schemes
`f : X ⟶ Y`, an injective resolution `F → J^•` of an abelian sheaf on the small étale site of
`X`, `i : ℕ` and an étale `U → Y`, the value at `U` of `P^i_J : U ↦ H^i((f_* J^•)(U))` is the
cohomology `H^i(X ×_Y U, F_U)` of the restriction `F_U` of `F` to the site localized at the
étale `X`-scheme `X ×_Y U`: the `i`-th right derived functor of sections over the terminal
object `X ×_Y U → X ×_Y U` of the localized site, applied to `F_U`. -/
@[weil "lem_fk102_direct_image_cohomology_presheaf_value"]
def directImageCohomologyPresheafObjIso (J : InjectiveResolution F) (i : ℕ) (U : Y.Etale) :
    (directImageCohomologyPresheaf f J i).obj (op U) ≅
      ((sheafToPresheaf ((smallEtaleTopology X).over ((smallEtaleBaseChange f).obj U))
          AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
          (op (Over.mk (𝟙 ((smallEtaleBaseChange f).obj U))))).rightDerived i).obj
        (((smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1}
          ((smallEtaleBaseChange f).obj U)).obj F) :=
  letI := smallEtalePushforward_additive.{u, u + 1} f
  (directImageCohomologyPresheafIso f J i).app (op U) ≪≫
    DerivedFunctor.rightDerivedEvaluationIso
      (etaleAbelianDirectImage.{u, u + 1} f ⋙
        sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)) F i ≪≫
    ((Cohomology.LocalizedSite.overPullbackRightDerivedSectionsIso.{u, u + 1, u + 1}
      (smallEtaleTopology X) ((smallEtaleBaseChange f).obj U) i
        (Over.mk (𝟙 ((smallEtaleBaseChange f).obj U)))).app F).symm

end Stacks.EtaleCohomology
