module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import Weil.AlgebraicGeometry.Sites.EtaleNeighborhoodsDependOnPoint
public import Weil.AlgebraicGeometry.Sites.StalkUnchangedAlgebraicClosure
public import Weil.Attr

/-!
# Stalks at geometric points with the same image

Let `X` be a scheme and `s : Spec K ⟶ X`, `t : Spec L ⟶ X` morphisms from spectra of separably
closed fields with the same underlying point `x₀ ∈ X`. The stalk of an étale sheaf at `s` depends
only on the separable closure `k'` of `κ(x₀)` in `K`: the factorization `Spec K ⟶ Spec k' ⟶ X`
induces an isomorphism of points of the small étale site. Two separable closures of `κ(x₀)` are
isomorphic over `κ(x₀)`, so the points of the small étale site defined by `s` and by `t` are
isomorphic, and hence so are the stalk functors at `s` and at `t`, naturally in the sheaf.

Since the stalk functors are exact, the isomorphism passes to the stalk functors on unbounded
derived categories, and to their cohomology functors.

## Main definitions

* `AlgebraicGeometry.Scheme.pointSmallEtaleIsoResidueSeparableClosure`: the isomorphism of
  points `pointSmallEtale s ≅ pointSmallEtale s'`, with `s'` the point of the separable closure
  of the residue field.
* `AlgebraicGeometry.Scheme.pointSmallEtaleIsoOfEq`: for `s`, `t` with the same underlying point,
  an isomorphism `pointSmallEtale s ≅ pointSmallEtale t`.
* `AlgebraicGeometry.Scheme.sheafFiberIsoOfEq`: the induced isomorphism of stalk functors on
  sheaves with values in any category with `u`-small colimits.
* `AlgebraicGeometry.Scheme.smallEtaleStalkAbIsoOfEq`,
  `AlgebraicGeometry.Scheme.smallEtaleDerivedStalkAbIsoOfEq`,
  `AlgebraicGeometry.Scheme.smallEtaleDerivedStalkAbHomologyIsoOfEq`: the isomorphisms of the
  abelian stalk functors, of the derived stalk functors and of their cohomology functors.
* `AlgebraicGeometry.GeometricPoint.smallEtaleStalkAbIsoOfLiesOver`,
  `AlgebraicGeometry.GeometricPoint.smallEtaleDerivedStalkAbIsoOfLiesOver`,
  `AlgebraicGeometry.GeometricPoint.smallEtaleDerivedStalkAbHomologyIsoOfLiesOver`: the same for
  geometric points `s`, `t` with `t` lying over the image of `s`.

## Implementation notes

The statements are made on Mathlib's small étale site `X.Etale` with the points
`AlgebraicGeometry.Scheme.pointSmallEtale`, which are defined for separably closed fields, and
are specialized to geometric points (algebraically closed fields) at the end. The derived stalk
functors are the descents `Functor.mapDerivedCategory` of the exact stalk functors, in the model
`HasDerivedCategory.standard` of the derived categories in which they are defined.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

universe u u' v'

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

variable {X : Scheme.{u}} {K L : Type u} [Field K] [Field L] [IsSepClosed K] [IsSepClosed L]

/-- The point of the small étale site defined by `s : Spec K ⟶ X` is isomorphic to the one
defined by `s' : Spec k' ⟶ X`, where `k'` is the separable closure in `K` of the residue field of
the underlying point: every lift of `s` to an étale `X`-scheme descends uniquely to `s'`. -/
def pointSmallEtaleIsoResidueSeparableClosure (s : Spec (.of K) ⟶ X) :
    pointSmallEtale s ≅ pointSmallEtale (residueSeparableClosurePoint s) :=
  haveI := isIso_pointSmallEtaleHomOfFac s (residueSeparableClosurePoint s)
    (toResidueSeparableClosure s) (toResidueSeparableClosure_comp_residueSeparableClosurePoint s)
  asIso (pointSmallEtaleHomOfFac s (residueSeparableClosurePoint s)
    (toResidueSeparableClosure s) (toResidueSeparableClosure_comp_residueSeparableClosurePoint s))

/-- An isomorphism over `X` between morphisms from spectra of separably closed fields induces an
isomorphism of the points of the small étale site they define. -/
def pointSmallEtaleIsoOfOverIso (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (e : Over.mk t ≅ Over.mk s) :
    pointSmallEtale t ≅ pointSmallEtale s :=
  haveI := isIso_pointSmallEtaleHomOfFac t s e.hom.left (Over.w e.hom)
  asIso (pointSmallEtaleHomOfFac t s e.hom.left (Over.w e.hom))

/-- **Points of the small étale site depend only on the underlying point.** For morphisms
`s : Spec K ⟶ X` and `t : Spec L ⟶ X` from spectra of separably closed fields with the same
underlying point, the points of the small étale site they define are isomorphic. -/
def pointSmallEtaleIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    pointSmallEtale s ≅ pointSmallEtale t :=
  pointSmallEtaleIsoResidueSeparableClosure s ≪≫
    (pointSmallEtaleIsoOfOverIso _ _ (residueSeparableClosurePointIsoOfEq s t h)).symm ≪≫
    (pointSmallEtaleIsoResidueSeparableClosure t).symm

section SheafFiber

variable (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- **Stalks depend only on the underlying point.** For morphisms `s : Spec K ⟶ X` and
`t : Spec L ⟶ X` from spectra of separably closed fields with the same underlying point, the
stalk functors at `s` and at `t` on sheaves on the small étale site are isomorphic. -/
def sheafFiberIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    (pointSmallEtale s).sheafFiber (A := A) ≅ (pointSmallEtale t).sheafFiber :=
  (GrothendieckTopology.Point.sheafFiberIsoOfIso (A := A) (pointSmallEtaleIsoOfEq t s h.symm))

end SheafFiber

section Abelian

/-- The isomorphism of abelian stalk functors `F_s ≅ F_t` for morphisms `s`, `t` from spectra of
separably closed fields with the same underlying point. -/
def smallEtaleStalkAbIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    smallEtaleStalkAb s ≅ smallEtaleStalkAb t :=
  sheafFiberIsoOfEq Ab.{u + 1} s t h

/-- The isomorphism of the derived stalk functors `K_s ≅ K_t` on the unbounded derived category
of abelian sheaves on the small étale site, for morphisms `s`, `t` from spectra of separably
closed fields with the same underlying point. -/
def smallEtaleDerivedStalkAbIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    smallEtaleDerivedStalkAb s ≅ smallEtaleDerivedStalkAb t :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
    (smallEtaleStalkAbIsoOfEq s t h)

/-- The isomorphism of the cohomology functors `K ↦ H^n(K_s)` and `K ↦ H^n(K_t)` of the derived
stalks, for morphisms `s`, `t` from spectra of separably closed fields with the same underlying
point. -/
def smallEtaleDerivedStalkAbHomologyIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) (n : ℤ) :
    smallEtaleDerivedStalkAb s ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n ≅
      smallEtaleDerivedStalkAb t ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n :=
  Functor.isoWhiskerRight (smallEtaleDerivedStalkAbIsoOfEq s t h) _

end Abelian

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.GeometricPoint

open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- **Stalks at geometric points over the same point are isomorphic.** For geometric points `s`
and `t` of `X` such that `t` lies over the image of `s`, the stalk functors at `s` and at `t` on
abelian sheaves on the small étale site are isomorphic. -/
def smallEtaleStalkAbIsoOfLiesOver (s t : GeometricPoint X) (h : t.LiesOver (s.hom default)) :
    smallEtaleStalkAb s.hom ≅ smallEtaleStalkAb t.hom :=
  smallEtaleStalkAbIsoOfEq s.hom t.hom h.symm

/-- The isomorphism of derived stalk functors at geometric points `s`, `t` of `X` with `t` lying
over the image of `s`. -/
def smallEtaleDerivedStalkAbIsoOfLiesOver (s t : GeometricPoint X)
    (h : t.LiesOver (s.hom default)) :
    smallEtaleDerivedStalkAb s.hom ≅ smallEtaleDerivedStalkAb t.hom :=
  smallEtaleDerivedStalkAbIsoOfEq s.hom t.hom h.symm

/-- The isomorphism of the cohomology functors of the derived stalks at geometric points `s`,
`t` of `X` with `t` lying over the image of `s`. -/
def smallEtaleDerivedStalkAbHomologyIsoOfLiesOver (s t : GeometricPoint X)
    (h : t.LiesOver (s.hom default)) (n : ℤ) :
    smallEtaleDerivedStalkAb s.hom ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n ≅
      smallEtaleDerivedStalkAb t.hom ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n :=
  smallEtaleDerivedStalkAbHomologyIsoOfEq s.hom t.hom h.symm n

end AlgebraicGeometry.GeometricPoint
