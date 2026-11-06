module

public import Weil.Attr
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative

/-!
# The logarithmic derivative `u' · u⁻¹` of a formal power series

For a power series `u` with constant coefficient `1` over a commutative ring `R`, the series
`u` is a unit and its logarithmic derivative is `D(u) = u' · u⁻¹`, where `u'` is the formal
derivative; one writes also `u' / u` or `d/dt log u`. It is the operator `d/dt log`, defined
without any logarithm having to exist.

This is the operator `T d/dT log` divided by `T`: `T · D(u)` is
`PowerSeries.logDerivative u`. All the rules of the logarithmic derivative are transported
from that operator along this identity: additivity on products, inverses going to negatives,
injectivity on series with constant coefficient `1` over a ring with torsion-free additive
group, and the dependence of the coefficient of `T ^ m` on `u` modulo `T ^ (m + 2)` only.

## Main definitions

* `PowerSeries.logDeriv`: the series `u' · u⁻¹`, the inverse taken as `invOfUnit u 1`.

## Main results

* `PowerSeries.logDeriv_eq_derivative_mul_inv`: over a field, `D(u) = u' · u⁻¹` with the field
  inverse of power series.
* `PowerSeries.X_mul_logDeriv`: `T · D(u) = T u' u⁻¹`.
* `PowerSeries.coeff_succ_logDerivative`: the coefficients of the two conventions differ by a
  shift of one.
* `PowerSeries.logDeriv_mul`, `PowerSeries.logDeriv_finsetProd`, `PowerSeries.logDeriv_invOfUnit`,
  `PowerSeries.eq_of_logDeriv_eq`, `PowerSeries.coeff_logDeriv_congr`.

## Implementation notes

The definition uses `invOfUnit u 1`, which is the inverse of `u` exactly when the constant
coefficient of `u` is `1`; away from that case it carries no meaning, as in the source, which
defines `D(u)` only for such `u`. Working over an arbitrary commutative ring rather than `ℚ_ℓ`
costs nothing; over a field the inverse agrees with the field inverse of power series.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. II, §4.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The logarithmic derivative `u' · u⁻¹` of a formal power series `u` with constant
coefficient `1`, the inverse being `invOfUnit u 1`. -/
@[weil "not_fk204_logarithmic_derivative"]
noncomputable def logDeriv (u : R⟦X⟧) : R⟦X⟧ := d⁄dX R u * invOfUnit u 1

theorem logDeriv_def (u : R⟦X⟧) : logDeriv u = d⁄dX R u * invOfUnit u 1 := rfl

/-- Over a field, the logarithmic derivative of a series with constant coefficient `1` is
`u' · u⁻¹` with the field inverse of power series. -/
@[weil "not_fk204_logarithmic_derivative"]
theorem logDeriv_eq_derivative_mul_inv {k : Type*} [Field k] {u : k⟦X⟧}
    (hu : constantCoeff u = 1) : logDeriv u = d⁄dX k u * u⁻¹ := by
  rw [logDeriv, invOfUnit_eq' u 1 hu]

/-- `u · D(u) = u'` for a series with constant coefficient `1`. -/
theorem mul_logDeriv {u : R⟦X⟧} (hu : constantCoeff u = 1) : u * logDeriv u = d⁄dX R u := by
  have h := mul_invOfUnit_one hu
  rw [logDeriv]
  linear_combination d⁄dX R u * h

/-- `T · D(u)` is the operator `T d/dT log` applied to `u`. -/
theorem X_mul_logDeriv (u : R⟦X⟧) : X * logDeriv u = logDerivative u := by
  rw [logDeriv, logDerivative, mul_assoc]

/-- The coefficient of `T ^ (n + 1)` of `T u' u⁻¹` is the coefficient of `T ^ n` of `u' u⁻¹`. -/
theorem coeff_succ_logDerivative (u : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (logDerivative u) = coeff n (logDeriv u) := by
  rw [← X_mul_logDeriv, coeff_succ_X_mul]

/-- The logarithmic derivative of `1` vanishes. -/
@[simp]
theorem logDeriv_one : logDeriv (1 : R⟦X⟧) = 0 := by simp [logDeriv]

/-- The logarithmic derivative is additive on series with constant coefficient `1`. -/
theorem logDeriv_mul {u v : R⟦X⟧} (hu : constantCoeff u = 1) (hv : constantCoeff v = 1) :
    logDeriv (u * v) = logDeriv u + logDeriv v := by
  refine X_mul_cancel ?_
  rw [mul_add, X_mul_logDeriv, X_mul_logDeriv, X_mul_logDeriv, logDerivative_mul hu hv]

/-- The logarithmic derivative of a finite product of series with constant coefficient `1`. -/
theorem logDeriv_finsetProd {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    logDeriv (∏ i ∈ s, f i) = ∑ i ∈ s, logDeriv (f i) := by
  refine X_mul_cancel ?_
  rw [X_mul_logDeriv, logDerivative_finsetProd s f hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (X_mul_logDeriv (f i)).symm

/-- The logarithmic derivative of the inverse of a series with constant coefficient `1`. -/
theorem logDeriv_invOfUnit {u : R⟦X⟧} (hu : constantCoeff u = 1) :
    logDeriv (invOfUnit u 1) = -logDeriv u := by
  refine X_mul_cancel ?_
  rw [X_mul_logDeriv, mul_neg, X_mul_logDeriv, logDerivative_invOfUnit hu]

/-- Two power series with constant coefficient `1` and the same logarithmic derivative agree,
provided the additive group of the coefficient ring is torsion free. -/
theorem eq_of_logDeriv_eq [IsAddTorsionFree R] {u v : R⟦X⟧}
    (hu : constantCoeff u = 1) (hv : constantCoeff v = 1) (h : logDeriv u = logDeriv v) :
    u = v :=
  eq_of_logDerivative_eq hu hv (by rw [← X_mul_logDeriv, ← X_mul_logDeriv, h])

/-- The coefficient of `T ^ m` of the logarithmic derivative depends only on the series modulo
`T ^ (m + 2)`. -/
theorem coeff_logDeriv_congr {u v : R⟦X⟧} {m : ℕ} (hu : constantCoeff u = 1)
    (hv : constantCoeff v = 1) (h : (X : R⟦X⟧) ^ (m + 2) ∣ u - v) :
    coeff m (logDeriv u) = coeff m (logDeriv v) := by
  rw [← coeff_succ_logDerivative, ← coeff_succ_logDerivative]
  exact coeff_logDerivative_congr hu hv h

end PowerSeries

end
