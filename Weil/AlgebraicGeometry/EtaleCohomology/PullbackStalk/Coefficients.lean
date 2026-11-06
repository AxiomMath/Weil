module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients

/-!
# Restriction of an étale sheaf with finite stalks

Let `F` be a sheaf of sets on the small étale site of a scheme `X` and let `q : T ⟶ X` be an
object of that site. The restriction `F|_T` of `F` to the small étale site of `T` sends an étale
`T`-scheme `V ⟶ T` to `F(V ⟶ T ⟶ X)`. For a geometric point `t̄` of `T`, the stalk of `F|_T` at
`t̄` is the stalk of `F` at the geometric point `q ∘ t̄` of `X`. Consequently, if `F` has finite
stalks, so does `F|_T`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.restrictSheafFiberIso`: the stalk of `F|_T` at `t̄` is the stalk
  of `F` at `q ∘ t̄`.

## Main results

* `AlgebraicGeometry.SmallEtale.HasFiniteStalks.restrict`: the restriction of a sheaf with finite
  stalks to an object of the small étale site has finite stalks.

## Implementation notes

The restriction to `T` is the restriction along the functor
`AlgebraicGeometry.smallEtalePostcompose`, which composes the structure morphism of an étale
`T`-scheme with `q`; on sheaves it is `CategoryTheory.Functor.sheafPushforwardContinuous` along
that functor. This restriction is the inverse image along `q`
(`AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose`), and the inverse image commutes with
stalks (`AlgebraicGeometry.smallEtalePullbackSheafFiberIso`, Stacks 03Q1); the comparison of
stalks is the composite of the two.

The statement is made on the whole small étale site of `X`, which contains the category of
noetherian separated étale `X`-schemes of the source.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- Restriction along base change by the structure morphism of an object `T` of the small étale
site has a left adjoint, the restriction along composition with that structure morphism. -/
theorem isRightAdjoint_sheafPushforwardContinuous_smallEtaleBaseChange (T : SmallEtale B X hX) :
    ((smallEtaleBaseChange B T.obj.hom).sheafPushforwardContinuous (Type v)
      (SmallEtale.topology B X hX)
      (SmallEtale.topology B T.obj.left.1 T.obj.left.property)).IsRightAdjoint :=
  ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX T).sheafPushforwardAdjunction
    (Type v)).isRightAdjoint

/-- **The stalk of a restriction.** For a sheaf of sets `F` on the small étale site of `X`, an
object `q : T ⟶ X` of that site and a geometric point `t̄` of `T`, the stalk at `t̄` of the
restriction of `F` to the small étale site of `T` is the stalk of `F` at `q ∘ t̄`. -/
def restrictSheafFiberIso (F : Sheaf (SmallEtale.topology B X hX) (Type v)) [UnivLE.{u, v}]
    (T : SmallEtale B X hX) (t : GeometricPoint ((SmallEtale.toScheme B X hX).obj T)) :
    (geometricPointSitePoint B T.obj.left.1 T.obj.left.property t).sheafFiber.obj
        (((smallEtalePostcompose B X hX T).sheafPushforwardContinuous (Type v)
          (SmallEtale.topology B T.obj.left.1 T.obj.left.property)
          (SmallEtale.topology B X hX)).obj F) ≅
      (geometricPointSitePoint B X hX (toBaseGeometricPoint T t)).sheafFiber.obj F :=
  haveI := isRightAdjoint_sheafPushforwardContinuous_smallEtaleBaseChange.{v} T
  (geometricPointSitePoint B T.obj.left.1 T.obj.left.property t).sheafFiber.mapIso
      ((smallEtaleSheafPullbackIsoPostcompose B X hX T (Type v)).app F).symm ≪≫
    (smallEtalePullbackSheafFiberIso B T.obj.hom t (Type v)).app F

/-- **Restriction preserves finite stalks.** If a sheaf of sets `F` on the small étale site of
`X` has finite stalks, then for every object `T` of that site the restriction of `F` to the small
étale site of `T` has finite stalks. -/
@[weil "lem_fk103_restriction_finite_stalks"]
theorem HasFiniteStalks.restrict {F : Sheaf (SmallEtale.topology B X hX) (Type v)}
    {hv : UnivLE.{u, v}} (hF : HasFiniteStalks F) (T : SmallEtale B X hX) :
    HasFiniteStalks
      (((smallEtalePostcompose B X hX T).sheafPushforwardContinuous (Type v)
        (SmallEtale.topology B T.obj.left.1 T.obj.left.property)
        (SmallEtale.topology B X hX)).obj F) := fun t ↦
  have := hF (toBaseGeometricPoint T t)
  Finite.of_equiv _ (restrictSheafFiberIso F T t).symm.toEquiv

end AlgebraicGeometry.SmallEtale

end
