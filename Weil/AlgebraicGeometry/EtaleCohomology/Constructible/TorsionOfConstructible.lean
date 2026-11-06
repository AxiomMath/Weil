module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible

/-!
# Constructible abelian étale sheaves are torsion sheaves

Every constructible sheaf of abelian groups on the small étale site of a scheme `X` is a torsion
sheaf. The stalk of a constructible sheaf at a geometric point is the stalk of its finite locally
constant restriction to a stratum through the image of that point, hence a finite, so torsion,
abelian group; and torsion of an abelian étale sheaf is detected on the stalks at geometric
points.

## Main results

* `AlgebraicGeometry.isTorsionSheaf_of_isConstructibleAbelianSheaf`: a constructible abelian
  sheaf on the small étale site is a torsion sheaf.

## Implementation notes

No hypothesis on `X` is needed. Constructibility is `AlgebraicGeometry.IsConstructibleAbelianSheaf`
(Stacks, Tag 03RW), which on a scheme with noetherian underlying space is the definition of [FK]
(`AlgebraicGeometry.isConstructibleAbelianSheaf_iff_exists_immersion_cover`); torsion is the
local notion `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`, which for a locally noetherian `X`
is the sectionwise notion of [FK]
(`AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 0GJX](https://stacks.math.columbia.edu/tag/0GJX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **A constructible sheaf of abelian groups is a torsion sheaf.** Every constructible abelian
sheaf on the small étale site of `X` is a torsion sheaf. -/
@[weil "lem_fk104_constructible_abelian_is_torsion"]
theorem isTorsionSheaf_of_isConstructibleAbelianSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    SmallEtale.IsTorsionSheaf B X.obj X.property F :=
  torsionSheafProperty_of_isConstructibleAbelianSheaf B X F hF

end AlgebraicGeometry

end
