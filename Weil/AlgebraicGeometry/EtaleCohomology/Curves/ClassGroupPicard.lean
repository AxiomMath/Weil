/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicard
public import Weil.Attr

/-!
# The degree of a line bundle on a smooth proper curve

Let `X` be a smooth proper curve over an algebraically closed field `k`. A divisor on `X` is a
finitely supported function `D : closedPoints X →₀ ℤ`, its degree is `Finsupp.degree D = ∑ D(x)`,
and the line bundle `𝒪_X(D)` is read through its class in `Pic(X)`, the image of `D` under the
isomorphism `Cl(X) ≃+ Pic(X)` (`Stacks.EtaleCohomology.closedPointClassGroupAddEquivSchemePicard`).

An integer `d` is *a degree* of an invertible `𝒪_X`-module `L` when some divisor `D` with
`𝒪_X(D) ≅ L` has degree `d`. We show that this happens exactly when `d` is the value on the
class of `L` of the degree homomorphism `AlgebraicGeometry.picardDegree : Pic(X) →+ ℤ`. Hence
every invertible module has exactly one degree, and isomorphic invertible modules have the same
degree.

## Main results

* `AlgebraicGeometry.isLineBundleDegree_iff_picardDegree_eq`: `d` is a degree of `L` if and only if
  `deg [L] = d`.
* `AlgebraicGeometry.existsUnique_isLineBundleDegree`: every invertible module has exactly one
  degree.
* `AlgebraicGeometry.isLineBundleDegree_iff_of_iso`: the degrees of isomorphic invertible modules
  agree.

## Implementation notes

There is no explicit sheaf `𝒪_X(D)` for a non-effective divisor in the library, so the condition
`𝒪_X(D) ≅ L` is stated as the equality of `D`'s image under `Cl(X) ≃+ Pic(X)` with the class of
`L` in `Pic(X)`; by `Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff` this is the same as an
isomorphism with any invertible module representing that image. A smooth connected curve is
integral, and the curve hypothesis `AlgebraicGeometry.IsCurve` includes integrality.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FK]
* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))

/-- An integer `d` is *a degree* of the invertible module `L` on the curve `X` when there is a
divisor `D` on `X` with `𝒪_X(D) ≅ L` and `deg D = d`; the condition `𝒪_X(D) ≅ L` is the equality
of the image of `D` in `Pic(X)` under `Cl(X) ≃+ Pic(X)` with the class of `L`. -/
def IsLineBundleDegree [IsCurve k g] [Smooth g] (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) (d : ℤ) :
    Prop :=
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  ∃ D : closedPoints X →₀ ℤ,
    Stacks.EtaleCohomology.closedPointClassGroupAddEquivSchemePicard g
        (QuotientAddGroup.mk D : Stacks.EtaleCohomology.closedPointClassGroup X) =
      schemePicardClassOf X L hL ∧ D.degree = d

variable [IsAlgClosed k] [IsCurve k g] [Smooth g] [IsProper g]

/-- **The degree of a line bundle in the divisor sense is its Picard degree**: `d` is a degree of
`L` if and only if `deg [L] = d`. -/
theorem isLineBundleDegree_iff_picardDegree_eq (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) (d : ℤ) :
    IsLineBundleDegree g L hL d ↔
      picardDegree k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le
        (schemePicardClassOf X L hL) = d := by
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le
  constructor
  · rintro ⟨D, hD, rfl⟩
    rw [← hD, Stacks.EtaleCohomology.picardDegree_closedPointClassGroupAddEquivSchemePicard_mk g
      hdim, Finsupp.degree_apply, Finsupp.sum]
  · rintro rfl
    obtain ⟨c, hc⟩ :=
      (Stacks.EtaleCohomology.closedPointClassGroupAddEquivSchemePicard g).surjective
        (schemePicardClassOf X L hL)
    induction c using QuotientAddGroup.induction_on with
    | H D =>
      refine ⟨D, hc, ?_⟩
      rw [← hc, Stacks.EtaleCohomology.picardDegree_closedPointClassGroupAddEquivSchemePicard_mk g
        hdim, Finsupp.degree_apply, Finsupp.sum]

/-- **Every line bundle on a smooth proper curve over an algebraically closed field has exactly
one degree** in the divisor sense. -/
@[weil "lem_fk105_degree_line_bundle_exists_unique"]
theorem existsUnique_isLineBundleDegree (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    ∃! d : ℤ, IsLineBundleDegree g L hL d :=
  ⟨_, (isLineBundleDegree_iff_picardDegree_eq g L hL _).2 rfl,
    fun _ hd => ((isLineBundleDegree_iff_picardDegree_eq g L hL _).1 hd).symm⟩

/-- **Isomorphic line bundles have the same degrees.** -/
@[weil "lem_fk105_degree_line_bundle_exists_unique"]
theorem isLineBundleDegree_iff_of_iso {L L' : X.Modules}
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L)
    (hL' : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L')
    (e : L ≅ L') (d : ℤ) :
    IsLineBundleDegree g L hL d ↔ IsLineBundleDegree g L' hL' d := by
  have h : schemePicardClassOf X L hL = schemePicardClassOf X L' hL' :=
    (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.presheaf (zariskiStructureIsSheaf X)
      L L' hL hL').2 ⟨e⟩
  rw [isLineBundleDegree_iff_picardDegree_eq, isLineBundleDegree_iff_picardDegree_eq, h]

end AlgebraicGeometry

end
