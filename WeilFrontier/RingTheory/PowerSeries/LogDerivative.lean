module

public import StacksFrontier.RingTheory.PowerSeries.LogDerivative
public import Weil.Attr

/-!
# A power series with constant coefficient one is determined by its logarithmic derivative

Let `R` be a commutative ring whose additive group is torsion free (for instance a field of
characteristic zero), and let `g, h ∈ R⟦X⟧` have constant coefficient `1`. If `g' h = g h'`,
then `g = h`: the quotient `g h⁻¹` has vanishing derivative, hence is constant, equal to `1`.

## Main results

* `PowerSeries.eq_of_derivative_mul_eq_mul_derivative`: if `g' h = g h'` and both constant
  coefficients are `1`, then `g = h`.

## Implementation notes

The source states the result over a field of characteristic zero; it holds over any
commutative ring with torsion-free additive group, which is the generality used here. The
proof reduces to `PowerSeries.eq_of_logDerivative_eq`, the same statement for the logarithmic
derivative `X · u' · u⁻¹`.

## References

* [FK88] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Introduction.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Two power series with constant coefficient `1` satisfying `g' h = g h'` are equal, over a
commutative ring whose additive group is torsion free. -/
@[weil "lem_fk0_power_series_determined_by_log_derivative"]
theorem eq_of_derivative_mul_eq_mul_derivative [IsAddTorsionFree R] {g h : R⟦X⟧}
    (hg : constantCoeff g = 1) (hh : constantCoeff h = 1)
    (hd : d⁄dX R g * h = g * d⁄dX R h) : g = h := by
  refine eq_of_logDerivative_eq hg hh ?_
  have hg' := mul_invOfUnit_one hg
  have hh' := mul_invOfUnit_one hh
  rw [logDerivative, logDerivative]
  linear_combination (X * invOfUnit g 1 * invOfUnit h 1) * hd -
    (X * d⁄dX R g * invOfUnit g 1) * hh' + (X * d⁄dX R h * invOfUnit h 1) * hg'

end PowerSeries
