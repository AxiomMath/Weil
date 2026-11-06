module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Trace.ZetaSeries

/-!
# Zeta series of a scheme whose point counts are a sum

Let `X` and `Y_i` (`i` in a finite index set) be schemes over a finite field `k` with point
counts `A_n(X) = ∑_i A_n(Y_i)` for every `n ≥ 1`. Then their zeta series satisfy
`f_X = ∏_i f_{Y_i}` in `ℚ⟦t⟧`: both sides have constant coefficient `1`, and the logarithmic
derivative of a product of series with constant coefficient `1` is the sum of the logarithmic
derivatives, so both sides have logarithmic derivative `∑_{n ≥ 1} A_n(X) t ^ n`.

## Main results

* `AlgebraicGeometry.pointCountSeries_eq_sum`: `∑_n A_n(X) t ^ n = ∑_i ∑_n A_n(Y_i) t ^ n`.
* `AlgebraicGeometry.zetaSeries_eq_prod_of_pointCountOfDegree_eq_sum`: `f_X = ∏_i f_{Y_i}`.

## Implementation notes

The source assumes the schemes of finite type over `k`; the argument does not use it, and the
statement is made for arbitrary schemes over `k` (point counts are `0` when infinite).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {ι : Type*} (s : Finset ι) {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ Spec (.of k))

/-- If `A_n(X) = ∑_{i ∈ s} A_n(Y_i)` for every `n ≥ 1`, then the point-count series
`∑_{n ≥ 1} A_n t ^ n` of `X` is the sum of those of the `Y_i`. -/
theorem pointCountSeries_eq_sum
    (h : ∀ (n : ℕ) [NeZero n], pointCountOfDegree f n = ∑ i ∈ s, pointCountOfDegree (g i) n) :
    pointCountSeries f = ∑ i ∈ s, pointCountSeries (g i) := by
  ext n
  rw [map_sum]
  rcases n with _ | n
  · simp [pointCountSeries]
  · rw [coeff_pointCountSeries f (n + 1), h (n + 1)]
    push_cast
    exact Finset.sum_congr rfl fun i _ => (coeff_pointCountSeries (g i) (n + 1)).symm

/-- If `A_n(X) = ∑_{i ∈ s} A_n(Y_i)` for every `n ≥ 1`, then the zeta series of `X` is the
product of the zeta series of the `Y_i`. -/
@[weil "lem_fk0_zeta_series_product_of_point_count_sum"]
theorem zetaSeries_eq_prod_of_pointCountOfDegree_eq_sum
    (h : ∀ (n : ℕ) [NeZero n], pointCountOfDegree f n = ∑ i ∈ s, pointCountOfDegree (g i) n) :
    zetaSeries f = ∏ i ∈ s, zetaSeries (g i) := by
  refine ((eq_zetaSeries_iff f _).mpr ⟨?_, ?_⟩).symm
  · simp [map_prod]
  · rw [PowerSeries.logDerivative_finsetProd s _ fun i _ => constantCoeff_zetaSeries (g i),
      pointCountSeries_eq_sum f s g h]
    exact Finset.sum_congr rfl fun i _ => logDerivative_zetaSeries (g i)

end AlgebraicGeometry
