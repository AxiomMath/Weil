module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import Weil.Attr

/-!
# The degree of a point of a scheme over a field

Let `X₀` be a scheme over a field `κ`, with structure morphism `f : X₀ ⟶ Spec κ`. The degree of a
point `α` of `X₀` is `d(α) = [κ(α) : κ]`, the degree of the residue field `κ(α)` over `κ`, with
the convention `d(α) = 0` when this extension is infinite.

## Main definitions

* `AlgebraicGeometry.Scheme.pointDegree` — the degree `d(α) = [κ(α) : κ]` of a point, `0` when
  the extension is infinite. It is `Stacks.EtaleCohomology.residueDegree`.

## Main results

* `AlgebraicGeometry.Scheme.pointDegree_eq_finrank` — `d(α)` is the `κ`-dimension of `κ(α)`.
* `AlgebraicGeometry.Scheme.pointDegree_eq_zero_of_not_finite` — the convention `d(α) = 0` for an
  infinite extension.

## Implementation notes

The `κ`-algebra structure on `κ(α)` is the one given by the composite `κ → 𝒪_{X₀,α} → κ(α)` of
the structure morphism with the residue map (`AlgebraicGeometry.fieldToResidue`). The degree is
`Stacks.EtaleCohomology.residueDegree`, whose API (positivity at closed points of a scheme
locally of finite type, finiteness of the closed points of bounded degree over a finite field)
applies to `pointDegree` unchanged.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The degree of a point.** For a scheme `X` over a field `k`, with structure morphism `f`, the
degree of a point `x` is `[κ(x) : k]`, and `0` when `κ(x)` is infinite-dimensional over `k`. -/
@[weil "def_fk204_degree_closed_point"]
abbrev pointDegree (f : X ⟶ Spec (.of k)) (x : X) : ℕ :=
  Stacks.EtaleCohomology.residueDegree f x

/-- The `k`-algebra structure on the residue field `κ(x)` of a scheme over `k`. -/
abbrev residueFieldAlgebra (f : X ⟶ Spec (.of k)) (x : X) : Algebra k (X.residueField x) :=
  (fieldToResidue f x).hom.toAlgebra

theorem pointDegree_eq_finrank (f : X ⟶ Spec (.of k)) (x : X) :
    pointDegree f x =
      letI := residueFieldAlgebra f x
      Module.finrank k (X.residueField x) :=
  rfl

theorem pointDegree_eq_zero_of_not_finite (f : X ⟶ Spec (.of k)) (x : X)
    (h : letI := residueFieldAlgebra f x; ¬ Module.Finite k (X.residueField x)) :
    pointDegree f x = 0 := by
  let := residueFieldAlgebra f x
  exact Module.finrank_of_not_finite h

end AlgebraicGeometry.Scheme
