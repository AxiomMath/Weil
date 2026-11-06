module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.ZetaSeries
public import Weil.RingTheory.PowerSeries.LogDerivative

/-!
# The zeta series is characterized by its derivative

Let `X` be a scheme over a finite field `k`, with point counts `A_n` and zeta series
`f = exp (∑_{n ≥ 1} (A_n / n) t ^ n) ∈ ℚ⟦t⟧`. Then `f` is the unique series `g ∈ ℚ⟦t⟧` with
`g(0) = 1` and `g' = (∑_{n ≥ 1} A_n t ^ {n-1}) g`.

## Main results

* `AlgebraicGeometry.derivative_zetaSeries`: `f' = (∑_{n ≥ 1} A_n t ^ {n-1}) f`.
* `AlgebraicGeometry.eq_zetaSeries_iff_derivative`: `g = f` if and only if `g(0) = 1` and
  `g' = (∑_{n ≥ 1} A_n t ^ {n-1}) g`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open PowerSeries

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The formal derivative of `u = ∑_{n ≥ 1} (A_n / n) t ^ n` is `∑_{n ≥ 1} A_n t ^ {n-1}`. -/
theorem derivative_pointCountLogSeries :
    d⁄dX ℚ (pointCountLogSeries f) =
      PowerSeries.mk fun n => (pointCountOfDegree f (n + 1) : ℚ) := by
  ext n
  rw [coeff_derivative, coeff_pointCountLogSeries f (n + 1), coeff_mk]
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The zeta series satisfies `f' = (∑_{n ≥ 1} A_n t ^ {n-1}) f`. -/
theorem derivative_zetaSeries :
    d⁄dX ℚ (zetaSeries f) =
      (PowerSeries.mk fun n => (pointCountOfDegree f (n + 1) : ℚ)) * zetaSeries f := by
  rw [zetaSeries, derivative_subst (hasSubst_pointCountLogSeries f), derivative_exp,
    derivative_pointCountLogSeries, mul_comm]

/-- A series `g ∈ ℚ⟦t⟧` is the zeta series `f` of `X` if and only if `g(0) = 1` and
`g' = (∑_{n ≥ 1} A_n t ^ {n-1}) g`. -/
@[weil "lem_fk0_zeta_series_characterized_by_log_derivative"]
theorem eq_zetaSeries_iff_derivative (g : ℚ⟦X⟧) :
    g = zetaSeries f ↔
      constantCoeff g = 1 ∧
        d⁄dX ℚ g = (PowerSeries.mk fun n => (pointCountOfDegree f (n + 1) : ℚ)) * g := by
  constructor
  · rintro rfl
    exact ⟨constantCoeff_zetaSeries f, derivative_zetaSeries f⟩
  · rintro ⟨h1, h2⟩
    refine eq_of_derivative_mul_eq_mul_derivative h1 (constantCoeff_zetaSeries f) ?_
    rw [h2, derivative_zetaSeries]
    ring

end AlgebraicGeometry
