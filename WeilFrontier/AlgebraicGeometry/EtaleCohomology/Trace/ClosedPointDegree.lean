module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import Mathlib.FieldTheory.Finiteness
public import Weil.Attr

/-!
# Closed points of a scheme of finite type over a finite field

Let `X₀` be a scheme locally of finite type over a field `k`, and `α` a closed point of `X₀`.
Then the residue field `κ(α)` is a finite extension of `k`, so the degree
`d(α) = [κ(α) : k]` is a positive integer. When `k` is finite with `q` elements, `κ(α)` is a
finite field with `q ^ d(α)` elements.

## Main results

* `AlgebraicGeometry.Scheme.pointDegree_pos` — `0 < d(α)` for a closed point `α`.
* `AlgebraicGeometry.Scheme.finite_residueField_of_isClosed_of_finite` — over a finite field,
  the residue field at a closed point is finite.
* `AlgebraicGeometry.Scheme.natCard_residueField_eq_pow_pointDegree` — over a finite field with
  `q` elements, `#κ(α) = q ^ d(α)`.

## Implementation notes

The result is stated for schemes locally of finite type over `k`, which contains the case of a
scheme of finite type. The finiteness of `κ(α)` over `k` is Zariski's lemma applied to the
finite-type `k`-algebra `κ(α)` (`Stacks.EtaleCohomology.finiteType_fieldToResidue`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.4][FreitagKiehl]
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- At a closed point `x` of a scheme locally of finite type over a field `k`, the residue field
`κ(x)` is a finite extension of `k`. -/
theorem module_finite_residueField_of_isClosed (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := residueFieldAlgebra f x
    Module.Finite k (X.residueField x) := by
  let := residueFieldAlgebra f x
  have : Algebra.FiniteType k (X.residueField x) :=
    Stacks.EtaleCohomology.finiteType_fieldToResidue f x hx
  exact finite_of_finite_type_of_isJacobsonRing k (X.residueField x)

/-- The degree of a closed point of a scheme locally of finite type over a field is positive. -/
@[weil "lem_fk204_degree_closed_point_finite"]
theorem pointDegree_pos (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) : 0 < pointDegree f x :=
  Stacks.EtaleCohomology.residueDegree_pos f x hx

/-- Over a finite field, the residue field at a closed point of a scheme locally of finite type
is finite. -/
@[weil "lem_fk204_degree_closed_point_finite"]
theorem finite_residueField_of_isClosed_of_finite [Finite k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  let := residueFieldAlgebra f x
  have := module_finite_residueField_of_isClosed f x hx
  exact Module.finite_of_finite k

/-- Over a finite field with `q` elements, the residue field at a closed point `x` of a scheme
locally of finite type has `q ^ d(x)` elements. -/
@[weil "lem_fk204_degree_closed_point_finite"]
theorem natCard_residueField_eq_pow_pointDegree [Finite k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nat.card (X.residueField x) = Nat.card k ^ pointDegree f x := by
  let := residueFieldAlgebra f x
  have := module_finite_residueField_of_isClosed f x hx
  exact Module.natCard_eq_pow_finrank

end AlgebraicGeometry.Scheme
