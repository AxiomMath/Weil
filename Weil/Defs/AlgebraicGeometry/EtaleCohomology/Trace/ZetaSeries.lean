module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import Weil.Definitions
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The zeta series of a scheme over a finite field

Let `X` be a scheme over a finite field `k`, with point counts `A_n = #X(k_n)` for `n ≥ 1`
(`AlgebraicGeometry.pointCountOfDegree`). Put `u = ∑_{n ≥ 1} (A_n / n) t ^ n ∈ t ℚ⟦t⟧`. The zeta
series of `X` is
`f_X(t) = exp u = ∑_{m ≥ 0} u ^ m / m! ∈ ℚ⟦t⟧`,
the sum converging `t`-adically since `u ^ m ∈ t ^ m ℚ⟦t⟧`: the coefficient of `t ^ N` is the
finite sum over `m ≤ N`.

Its constant coefficient is `1`, and its logarithmic derivative `t f' / f` is
`∑_{n ≥ 1} A_n t ^ n`; since a series with constant coefficient `1` over `ℚ` is determined by its
logarithmic derivative (`PowerSeries.eq_of_logDerivative_eq`), this characterizes `f_X`.

## Main definitions

`pointCountLogSeries` and `zetaSeries` are defined in `Weil.Definitions`.

* `AlgebraicGeometry.pointCountLogSeries f`: the series `u = ∑_{n ≥ 1} (A_n / n) t ^ n`.
* `AlgebraicGeometry.pointCountSeries f`: the series `∑_{n ≥ 1} A_n t ^ n`.
* `AlgebraicGeometry.zetaSeries f`: the zeta series `exp u`, the substitution of `u` into
  `PowerSeries.exp ℚ`.

## Main results

* `AlgebraicGeometry.coeff_zetaSeries`: the coefficient of `t ^ N` of `f_X` is
  `∑_{m ≤ N} [t ^ N] u ^ m / m!`.
* `AlgebraicGeometry.constantCoeff_zetaSeries`: the constant coefficient of `f_X` is `1`.
* `AlgebraicGeometry.logDerivative_zetaSeries`: `t f_X' / f_X = ∑_{n ≥ 1} A_n t ^ n`.
* `PowerSeries.logDerivative_subst_exp`: `t (exp g)' / exp g = t g'` for `g` without constant
  term.

## Implementation notes

The infinite sum `∑_m u ^ m / m!` is Mathlib's substitution `PowerSeries.subst u (exp ℚ)`, which
is defined since `u` has no constant term; `coeff_zetaSeries` recovers the source's finite
coefficient formula.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The exponential of a series without constant term has constant coefficient `1`. -/
theorem constantCoeff_subst_exp {g : R⟦X⟧} (hg : constantCoeff g = 0) :
    constantCoeff ((exp R).subst g) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (HasSubst.of_constantCoeff_zero' hg),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hg, zero_pow hd, smul_zero]

/-- The logarithmic derivative of `exp g`, for `g` without constant term, is `t g'`. -/
theorem logDerivative_subst_exp {g : R⟦X⟧} (hg : constantCoeff g = 0) :
    logDerivative ((exp R).subst g) = X * d⁄dX R g := by
  have hs := HasSubst.of_constantCoeff_zero' hg
  rw [logDerivative, derivative_subst hs, derivative_exp]
  have h := mul_invOfUnit_one (constantCoeff_subst_exp hg)
  linear_combination (X * d⁄dX R g) * h

end PowerSeries

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The series `∑_{n ≥ 1} A_n t ^ n` of the point counts `A_n = pointCountOfDegree f n`. -/
def pointCountSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    (pointCountOfDegree f n : ℚ)

theorem coeff_pointCountLogSeries (n : ℕ) [NeZero n] :
    PowerSeries.coeff n (pointCountLogSeries f) = (pointCountOfDegree f n : ℚ) / n := by
  simp [pointCountLogSeries, NeZero.ne n]

theorem coeff_pointCountSeries (n : ℕ) [NeZero n] :
    PowerSeries.coeff n (pointCountSeries f) = (pointCountOfDegree f n : ℚ) := by
  simp [pointCountSeries, NeZero.ne n]

@[simp]
theorem constantCoeff_pointCountLogSeries :
    PowerSeries.constantCoeff (pointCountLogSeries f) = 0 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, pointCountLogSeries]

@[simp]
theorem constantCoeff_pointCountSeries :
    PowerSeries.constantCoeff (pointCountSeries f) = 0 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, pointCountSeries]

theorem hasSubst_pointCountLogSeries : PowerSeries.HasSubst (pointCountLogSeries f) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_pointCountLogSeries f)

/-- `u ^ m` is divisible by `t ^ m`, so its coefficients below `t ^ m` vanish. -/
theorem coeff_pointCountLogSeries_pow_of_lt {N m : ℕ} (h : N < m) :
    PowerSeries.coeff N (pointCountLogSeries f ^ m) = 0 := by
  obtain ⟨v, hv⟩ := PowerSeries.X_dvd_iff.mpr (constantCoeff_pointCountLogSeries f)
  rw [hv, mul_pow, PowerSeries.coeff_X_pow_mul']
  split_ifs with h'
  · omega
  · rfl

/-- The coefficient of `t ^ N` of the zeta series is the finite sum
`∑_{m ≤ N} [t ^ N] u ^ m / m!`. -/
theorem coeff_zetaSeries (N : ℕ) :
    PowerSeries.coeff N (zetaSeries f) =
      ∑ m ∈ Finset.range (N + 1),
        PowerSeries.coeff N (pointCountLogSeries f ^ m) / (m.factorial : ℚ) := by
  rw [zetaSeries, PowerSeries.coeff_subst' (hasSubst_pointCountLogSeries f),
    finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp [PowerSeries.coeff_exp, div_eq_inv_mul]
  · intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hm (by rw [coeff_pointCountLogSeries_pow_of_lt f (by omega), smul_zero])

@[simp]
theorem constantCoeff_zetaSeries : PowerSeries.constantCoeff (zetaSeries f) = 1 :=
  PowerSeries.constantCoeff_subst_exp (constantCoeff_pointCountLogSeries f)

/-- The logarithmic derivative `t f_X' / f_X` of the zeta series is `∑_{n ≥ 1} A_n t ^ n`. -/
theorem logDerivative_zetaSeries :
    PowerSeries.logDerivative (zetaSeries f) = pointCountSeries f := by
  rw [zetaSeries, PowerSeries.logDerivative_subst_exp (constantCoeff_pointCountLogSeries f)]
  ext n
  rcases n with _ | n
  · simp [pointCountSeries]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      coeff_pointCountLogSeries f (n + 1), coeff_pointCountSeries f (n + 1)]
    have : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp

/-- The zeta series is the unique series with constant coefficient `1` whose logarithmic
derivative is `∑_{n ≥ 1} A_n t ^ n`. -/
theorem eq_zetaSeries_iff (g : PowerSeries ℚ) :
    g = zetaSeries f ↔
      PowerSeries.constantCoeff g = 1 ∧ PowerSeries.logDerivative g = pointCountSeries f := by
  constructor
  · rintro rfl
    exact ⟨constantCoeff_zetaSeries f, logDerivative_zetaSeries f⟩
  · rintro ⟨h1, h2⟩
    exact PowerSeries.eq_of_logDerivative_eq h1 (constantCoeff_zetaSeries f)
      (h2.trans (logDerivative_zetaSeries f).symm)

end AlgebraicGeometry
