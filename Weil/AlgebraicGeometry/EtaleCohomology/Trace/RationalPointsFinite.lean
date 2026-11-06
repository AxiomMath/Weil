module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentTraceFormulaConclusion

/-!
# A scheme of finite type over a finite field has finitely many points over each extension

Let `k` be a finite field and `X` a scheme of finite type over `k`, with structure morphism
`f : X ⟶ Spec k`. For every `n ≥ 1` the set `X(k_n)` of `k_n`-valued points of `X` over `k`, where
`k_n` is an extension of `k` of degree `n`, is finite. More generally `X(K)` is finite for every
finite field `K` containing `k`.

## Main results

* `AlgebraicGeometry.finite_fieldValuedPoints_of_finite`: `X(K)` is finite for every finite
  extension field `K` of `k`.
* `AlgebraicGeometry.finite_fieldValuedPoints_extension`: `X(k_n)` is finite for the extension
  `k_n` of degree `n` used in `AlgebraicGeometry.pointCountOfDegree`.
* `AlgebraicGeometry.pointCount_pos_iff`: since `X(K)` is finite, the point count `#X(K)` is
  positive exactly when `X` has a `K`-valued point.

## Implementation notes

"Finite type" is expressed as `LocallyOfFiniteType f` together with `QuasiCompact f`. The
finiteness itself is `Stacks.EtaleCohomology.finite_fieldValuedPoints`, proved by bounding the
closed points of residue degree dividing `[K : k]` and the residue-field embeddings at each of
them, rather than by the source's count of algebra homomorphisms on an affine cover.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public section

open CategoryTheory Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]

/-- A scheme of finite type over a finite field `k` has finitely many `K`-valued points over `k`
for every finite field extension `K` of `k`. -/
theorem finite_fieldValuedPoints_of_finite (K : Type u) [Field K] [Algebra k K] [Finite K] :
    Finite (fieldValuedPoints f K) :=
  finite_fieldValuedPoints f K

/-- A scheme `X` of finite type over a finite field `k` has finitely many points with values in
the extension `k_n` of degree `n ≥ 1` of `k` used to define the point count `#X(k_n)`. -/
@[weil "lem_fk0_rational_points_finite"]
theorem finite_fieldValuedPoints_extension (n : ℕ) [NeZero n] :
    haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
    Finite (fieldValuedPoints f (ULift.{u} (FiniteField.Extension k (ringChar k) n))) := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have : Fintype k := Fintype.ofFinite k
  have : Finite (FiniteField.Extension k (ringChar k) n) :=
    Module.finite_of_finite k
  exact finite_fieldValuedPoints f _

/-- For a finite extension field `K` of `k`, `#X(K)` is positive exactly when `X` has a
`K`-valued point. -/
theorem pointCount_pos_iff (K : Type u) [Field K] [Algebra k K] [Finite K] :
    0 < pointCount f K ↔ Nonempty (fieldValuedPoints f K) := by
  have := finite_fieldValuedPoints f K
  exact Nat.card_pos_iff.trans (and_iff_left inferInstance)

end AlgebraicGeometry
