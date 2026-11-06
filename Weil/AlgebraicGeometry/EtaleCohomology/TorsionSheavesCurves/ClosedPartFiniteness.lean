module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedPartFiniteness

/-!
# Constructible sheaves have finite stalks

Let `F` be a constructible sheaf of sets on the small étale site of a scheme `X`. Then the stalk
`F_x` is finite for every geometric point `x` of `X`: the point lies over a point of one of the
strata `Yⱼ` on which `F` is finite locally constant, the stalk of `F` at `x` is the stalk of
`F|_{Yⱼ}` at a geometric point of `Yⱼ` above the same point, and the stalks of a finite locally
constant sheaf are finite. In particular the underlying sheaf of sets of a constructible sheaf of
abelian groups has finite stalks.

## Main results

* `AlgebraicGeometry.finite_etaleStalk_of_isConstructibleSetSheaf'`: the stalks of a
  constructible sheaf of sets at geometric points are finite.
* `AlgebraicGeometry.finite_etaleStalk_underlying_of_isConstructibleAbelianSheaf`: the stalks of
  the underlying sheaf of sets of a constructible sheaf of abelian groups are finite.

## Implementation notes

Geometric points are `AlgebraicGeometry.GeometricPoint X.obj` (algebraically closed fields) and
the stalk is `AlgebraicGeometry.etaleStalk`, the colimit over étale neighbourhoods. The sheaf of
sets case is `AlgebraicGeometry.finite_etaleStalk_of_isConstructibleSetSheaf`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **The stalks of a constructible sheaf of sets are finite.** For a constructible sheaf of sets
`F` on the small étale site of `X`, the stalk `F_x` is finite at every geometric point `x`. -/
@[weil "lem_fk104_constructible_abelian_stalks_finite"]
theorem finite_etaleStalk_of_isConstructibleSetSheaf'
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) (x : GeometricPoint X.obj) :
    Finite (etaleStalk B X.obj X.property x F.obj) :=
  finite_etaleStalk_of_isConstructibleSetSheaf B X F hF x

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **The underlying sheaf of sets of a constructible abelian sheaf has finite stalks.** For a
constructible sheaf of abelian groups `F` on the small étale site of `X`, the stalk of its
underlying sheaf of sets at every geometric point is finite. -/
@[weil "lem_fk104_constructible_abelian_stalks_finite"]
theorem finite_etaleStalk_underlying_of_isConstructibleAbelianSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) (x : GeometricPoint X.obj) :
    Finite (etaleStalk B X.obj X.property x ((smallEtaleUnderlyingSetSheaf B X).obj F).obj) :=
  finite_etaleStalk_of_isConstructibleSetSheaf B X _
    ((isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf B X F).mp hF) x

end AlgebraicGeometry
