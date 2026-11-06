module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount

/-!
# The point count of a scheme over a finite field as a sum over closed points

Let `k` be a finite field and `X` a scheme of finite type over `k`, with structure morphism
`f : X ⟶ Spec k`. For `n ≥ 1` the `n`-th point count `A_n = #X(k_n)` is

`A_n = ∑_{x closed, d(x) ∣ n} d(x)`,

where `d(x) = [κ(x) : k]` is the degree of the closed point `x`. Indeed a `k_n`-valued point is a
point `x` together with a `k`-embedding `κ(x) → k_n`; such an embedding exists only when `x` is
closed and `d(x) ∣ n`, and then there are exactly `d(x)` of them. The sum is finite, since a
quasi-compact scheme locally of finite type over a finite field has only finitely many closed
points of bounded degree.

## Main results

* `AlgebraicGeometry.finite_setOf_isClosed_pointDegree_dvd`: for `n ≥ 1` there are only finitely
  many closed points `x` with `d(x) ∣ n`.
* `AlgebraicGeometry.pointCount_eq_sum_pointDegree`: `#X(K) = ∑_{x closed, d(x) ∣ [K : k]} d(x)`
  for every finite extension `K` of `k`.
* `AlgebraicGeometry.pointCountOfDegree_eq_sum_pointDegree`: `A_n = ∑_{x closed, d(x) ∣ n} d(x)`.

## Implementation notes

The count is `Stacks.EtaleCohomology.natCard_fieldValuedPoints`, which sums over a finset of
closed points (as elements of `closedPoints X`) of degree at most `n`; here the sum is rewritten as
a sum over the finite set of points `x` of `X` with `{x}` closed and `d(x) ∣ n`, the index set of
the source.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]

/-- For `n ≠ 0`, a scheme of finite type over a finite field has only finitely many closed points
whose degree divides `n`. -/
@[weil "lem_fk0_point_count_closed_point_degrees"]
theorem finite_setOf_isClosed_pointDegree_dvd (n : ℕ) [NeZero n] :
    {x : X | IsClosed ({x} : Set X) ∧ Scheme.pointDegree f x ∣ n}.Finite := by
  have h := (finite_setOf_closedPoints_residueDegree_le f n).image Subtype.val
  refine h.subset ?_
  rintro x ⟨hc, hd⟩
  exact ⟨⟨x, hc⟩, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hd, rfl⟩

/-- **The point count over a finite extension as a sum of degrees.** If `K` is a finite extension
of the finite field `k`, then `#X(K) = ∑ d(x)`, the sum over the closed points `x` of `X` whose
degree `d(x)` divides `[K : k]`. -/
theorem pointCount_eq_sum_pointDegree (K : Type u) [Field K] [Algebra k K] [Finite K] (n : ℕ)
    [NeZero n] (hK : Module.finrank k K = n) :
    pointCount f K =
      ∑ x ∈ (finite_setOf_isClosed_pointDegree_dvd f n).toFinset, Scheme.pointDegree f x := by
  subst hK
  rw [pointCount, natCard_fieldValuedPoints]
  refine Finset.sum_bij (fun y _ => y.1) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, closedPointsDegreeLE, Set.Finite.mem_toFinset] at hy
    simp only [Set.Finite.mem_toFinset]
    exact ⟨y.2, hy.2⟩
  · intro y₁ _ y₂ _ h
    exact Subtype.ext h
  · intro x hx
    simp only [Set.Finite.mem_toFinset] at hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, closedPointsDegreeLE, Set.Finite.mem_toFinset]
    exact ⟨Nat.le_of_dvd Module.finrank_pos hx.2, hx.2⟩
  · intro y _
    rfl

/-- **The point count as a sum of degrees of closed points.** For a scheme `X` of finite type over
the finite field `k` and `n ≥ 1`, the `n`-th point count is `A_n = ∑ d(x)`, the sum over the
closed points `x` of `X` whose degree `d(x) = [κ(x) : k]` divides `n`. -/
@[weil "lem_fk0_point_count_closed_point_degrees"]
theorem pointCountOfDegree_eq_sum_pointDegree (n : ℕ) [NeZero n] :
    pointCountOfDegree f n =
      ∑ x ∈ (finite_setOf_isClosed_pointDegree_dvd f n).toFinset, Scheme.pointDegree f x := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  let K := ULift.{u} (FiniteField.Extension k (ringChar k) n)
  have hK : Module.finrank k K = n := by
    rw [(ULift.algEquiv (R := k)
      (A := FiniteField.Extension k (ringChar k) n)).toLinearEquiv.finrank_eq]
    exact FiniteField.finrank_extension k (ringChar k) n
  have : Finite K := Module.finite_of_finite k
  rw [pointCountOfDegree_eq_pointCount f K hK, pointCount_eq_sum_pointDegree f K n hK]

end AlgebraicGeometry
