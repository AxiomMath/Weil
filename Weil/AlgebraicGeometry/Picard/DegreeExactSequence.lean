/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import StacksFrontier.AlgebraicGeometry.Picard.ClosedPointDegreeOne
public import Weil.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicard
public import Weil.Attr

/-!
# The degree exact sequence of a smooth proper curve

Let `X` be a smooth proper curve over an algebraically closed field `k`. The degree of line
bundles is a homomorphism `deg : Pic(X) →+ ℤ` (`AlgebraicGeometry.picardDegree`), whose value on
the class of an invertible module `L` is the degree of `L` in the divisor sense
(`AlgebraicGeometry.isLineBundleDegree_iff_picardDegree_eq`). We show that it is surjective with
kernel `Pic⁰(X)`, i.e. that `0 → Pic⁰(X) → Pic(X) → ℤ → 0` is exact, where `Pic⁰(X)` is the
subgroup of classes of invertible modules whose degree is `0`.

## Main results

* `AlgebraicGeometry.mem_picardDegreeZero_iff_isLineBundleDegree_zero`: the class of `L` lies in
  `Pic⁰(X)` if and only if `0` is the degree of `L`.
* `AlgebraicGeometry.picardDegree_shortExact`: the sequence `0 → Pic⁰(X) → Pic(X) → ℤ → 0` is
  exact.

## Implementation notes

`Pic⁰(X)` is `AlgebraicGeometry.picardDegreeZero`, defined as the kernel of
`AlgebraicGeometry.picardDegree`; its identification with the classes of degree `0` in the
divisor sense is `AlgebraicGeometry.mem_picardDegreeZero_iff_isLineBundleDegree_zero`.
Surjectivity is `AlgebraicGeometry.surjective_picardDegree_of_isAlgClosed`: the class of a closed
point has degree one.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FK]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g]

/-- **`Pic⁰(X)` consists of the classes of degree `0`**: the class of an invertible module `L`
lies in `Pic⁰(X)` if and only if `0` is the degree of `L` in the divisor sense. -/
@[weil "lem_fk105_degree_exact_sequence"]
theorem mem_picardDegreeZero_iff_isLineBundleDegree_zero (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    schemePicardClassOf X L hL ∈
        picardDegreeZero k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le ↔
      IsLineBundleDegree g L hL 0 :=
  (isLineBundleDegree_iff_picardDegree_eq g L hL 0).symm

/-- **The degree exact sequence** `0 → Pic⁰(X) → Pic(X) → ℤ → 0` of a smooth proper curve over
an algebraically closed field: the inclusion of `Pic⁰(X)` is injective, its image is the kernel
of the degree, and the degree is surjective. -/
@[weil "lem_fk105_degree_exact_sequence"]
theorem picardDegree_shortExact :
    Function.Injective
        (picardDegreeZero k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le).subtype ∧
      Function.Exact
        (picardDegreeZero k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le).subtype
        (picardDegree k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le) ∧
      Function.Surjective
        (picardDegree k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le) := by
  refine ⟨Subtype.val_injective, fun x => ?_, surjective_picardDegree_of_isAlgClosed k g _⟩
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

end AlgebraicGeometry

end
