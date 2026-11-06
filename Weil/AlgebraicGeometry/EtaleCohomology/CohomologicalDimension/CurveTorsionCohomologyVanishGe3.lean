module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeTwiceDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Étale cohomology of curves over a separably closed field vanishes in degrees at least three

Let `k` be a separably closed field and `X` a scheme of finite type over `k` with `dim X ≤ 1`.
Then `H^q(X, 𝓕) = 0` for every torsion abelian sheaf `𝓕` on the small étale site of `X` and every
`q ≥ 3`.

This is the bound `cd(X) ≤ 2 dim(X) + cd(k)` for schemes of finite type over a field (Stacks
0F0W, SGA 4 X 4.3), together with `cd(k) = 0` for a separably closed field.

## Main results

* `AlgebraicGeometry.Scheme.subsingleton_H_of_topologicalKrullDim_le_one`: the statement on
  Mathlib's small étale site `X.smallEtaleTopology`.
* `AlgebraicGeometry.SmallEtale.subsingleton_H_of_topologicalKrullDim_le_one`: the statement on
  the bounded small étale site `AlgebraicGeometry.SmallEtale.topology`, for the torsion sheaves
  `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`.

## Implementation notes

The source deduces the statement for torsion sheaves from the case of constructible sheaves by
writing a torsion sheaf as the filtered union of its constructible subsheaves and passing to the
limit in cohomology. The general bound used here is already proved for all torsion sheaves, so no
passage to the limit is needed. The source's hypothesis that the orders of the sections be prime
to the characteristic of `k` is not needed either, and is omitted. "Of finite type" is expressed
as `X` quasi-compact and locally of finite type over `k`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Proposition I.5
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- **Étale cohomology of a curve over a separably closed field vanishes in degrees `≥ 3`.** Let
`k` be a separably closed field and `X` a quasi-compact scheme locally of finite type over `k`
with `dim X ≤ 1`. Then `H^q(X, 𝓕) = 0` for every torsion abelian sheaf `𝓕` on the small étale site
of `X` and every `q ≥ 3`. -/
@[weil "prop_fk105_curve_torsion_cohomology_vanish_ge_3"]
theorem subsingleton_H_of_topologicalKrullDim_le_one (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [CompactSpace X] [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  refine subsingleton_H_of_topologicalKrullDim_le k 1 X f (by exact_mod_cast hX) F hF q ?_
  have h0 := etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k
  rw [nonpos_iff_eq_zero.1 h0, add_zero]
  exact_mod_cast (by omega : 2 * 1 < q)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SmallEtale

/-- **Étale cohomology of a curve over a separably closed field vanishes in degrees `≥ 3`**, on
the bounded small étale site. Let `k` be a separably closed field and `X` a quasi-compact scheme
locally of finite type over `k` with `dim X ≤ 1`. Then `H^q(X, 𝓕) = 0` for every torsion abelian
sheaf `𝓕` on the small étale site of `X` and every `q ≥ 3`. -/
@[weil "prop_fk105_curve_torsion_cohomology_vanish_ge_3"]
theorem subsingleton_H_of_topologicalKrullDim_le_one (B : BigEtaleSite.{u}) (k : Type u)
    [Field k] [IsSepClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [CompactSpace X]
    [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) (hS : B.Contains X)
    [HasExt.{u + 1} (Sheaf (topology B X hS) AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology B X hS) AddCommGrpCat.{u + 1})
    (hF : IsTorsionSheaf B X hS F) (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  let E := sheafEquiv B X hS AddCommGrpCat.{u + 1}
  let G := E.functor.obj F
  have hG : Stacks.Torsion.torsionSheafProperty _ G :=
    (torsionSheafProperty_toEtaleSite_iff B X hS G).1
      ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso (E.unitIso.app F) hF)
  have := Scheme.subsingleton_H_of_topologicalKrullDim_le_one k X f hX G hG q hq
  let e₁ := Stacks.Cohomology.DenseSubsite.hAddEquiv (topology B X hS)
    X.smallEtaleTopology (toEtaleSite B X hS) G q
  let e₂ := ((Sheaf.functorH.{u + 1, u + 1} (topology B X hS) q).mapIso
    (E.unitIso.app F)).addCommGroupIsoToAddEquiv
  exact (e₂.trans e₁.symm).toEquiv.subsingleton

end AlgebraicGeometry.SmallEtale
