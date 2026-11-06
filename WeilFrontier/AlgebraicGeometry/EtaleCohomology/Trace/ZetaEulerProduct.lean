module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointCountClosedPointDegrees
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Trace.ZetaSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve

/-!
# The Euler product of the zeta series

Let `X` be a scheme of finite type over a finite field `k`, with zeta series
`f_X = exp (∑_{n ≥ 1} A_n t ^ n / n) ∈ ℚ⟦t⟧` (`AlgebraicGeometry.zetaSeries`). Then

`f_X(t) = ∏_{x ∈ |X|} (1 - t ^ {d(x)})⁻¹`,

the product over the closed points `x` of `X`, with `d(x) = [κ(x) : k]`. The product converges
`t`-adically: only finitely many closed points have degree at most `N`, and every factor is
`1` modulo `t ^ {d(x)}`, so the coefficient of `t ^ N` is that of any finite subproduct over a
set of closed points containing all those of degree at most `N`.

The Euler product is `Stacks.EtaleCohomology.constantLFunction f ℚ`, the L-function of the
constant sheaf (Stacks, Tag 03UV), whose local factor at `x` is `(1 - t ^ {d(x)})⁻¹`.

The proof compares logarithmic derivatives. A series with constant coefficient `1` is determined
by its logarithmic derivative `t g' / g`, and that of `f_X` is `∑_{n ≥ 1} A_n t ^ n`
(`AlgebraicGeometry.eq_zetaSeries_iff`). The logarithmic derivative of `(1 - t ^ d)⁻¹` is
`d ∑_{j ≥ 1} t ^ {j d}`, so the coefficient of `t ^ N` in that of the finite product over the
closed points of degree at most `N` is `∑_{d(x) ∣ N} d(x) = A_N`
(`AlgebraicGeometry.pointCountOfDegree_eq_sum_pointDegree`); and the coefficient of `t ^ N` of a
logarithmic derivative only depends on the series modulo `t ^ {N + 1}`.

## Main results

* `AlgebraicGeometry.zetaSeries_eq_constantLFunction`: `f_X = ∏_{x ∈ |X|} (1 - t ^ {d(x)})⁻¹`,
  the right side being `Stacks.EtaleCohomology.constantLFunction f ℚ`.
* `AlgebraicGeometry.coeff_zetaSeries_eq_coeff_prod`: the coefficient of `t ^ N` of `f_X` is that
  of `∏_{x ∈ s} (1 - t ^ {d(x)})⁻¹` for every finite set `s` of closed points containing those of
  degree at most `N`.
* `AlgebraicGeometry.logDerivative_constantLFunction`: the logarithmic derivative of the Euler
  product is `∑_{n ≥ 1} A_n t ^ n`.
* `PowerSeries.coeff_logDerivative_invOfUnit_one_sub_X_pow`: the coefficient of `t ^ m` of the
  logarithmic derivative of `(1 - t ^ e)⁻¹` is `e` if `e ∣ m` and `m ≠ 0`, and `0` otherwise.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe u

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The series `∑_j t ^ {j e}` times `1 - t ^ e` is `1`. -/
theorem mk_ite_dvd_mul_one_sub_X_pow {e : ℕ} (he : 0 < e) :
    PowerSeries.mk (fun d => if e ∣ d then (1 : R) else 0) * (1 - X ^ e) = 1 := by
  ext d
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
  by_cases hd : e ≤ d
  · have h : e ∣ d ↔ e ∣ d - e := by
      conv_lhs => rw [← Nat.sub_add_cancel hd]
      exact Nat.dvd_add_left (dvd_refl e)
    rw [ite_eq_left hd, coeff_mk, ite_eq_right (show d ≠ 0 by omega)]
    by_cases h' : e ∣ d
    · rw [ite_eq_left h', ite_eq_left (h.1 h'), sub_self]
    · rw [ite_eq_right h', ite_eq_right fun x => h' (h.2 x), sub_self]
  · rw [ite_eq_right hd, sub_zero]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp
    · rw [ite_eq_right (fun h => hd (Nat.le_of_dvd hd0 h)), ite_eq_right hd0.ne']

/-- The inverse of `1 - t ^ e`, for `e > 0`, is `∑_j t ^ {j e}`. -/
theorem invOfUnit_one_sub_X_pow {e : ℕ} (he : 0 < e) :
    invOfUnit (1 - X ^ e : R⟦X⟧) 1 = PowerSeries.mk (fun d => if e ∣ d then (1 : R) else 0) := by
  have hu : constantCoeff (1 - X ^ e : R⟦X⟧) = 1 := by simp [he.ne']
  calc invOfUnit (1 - X ^ e : R⟦X⟧) 1
      = invOfUnit (1 - X ^ e : R⟦X⟧) 1 *
          (PowerSeries.mk (fun d => if e ∣ d then (1 : R) else 0) * (1 - X ^ e)) := by
        rw [mk_ite_dvd_mul_one_sub_X_pow he, mul_one]
    _ = ((1 - X ^ e) * invOfUnit (1 - X ^ e : R⟦X⟧) 1) *
          PowerSeries.mk (fun d => if e ∣ d then (1 : R) else 0) := by ring
    _ = _ := by rw [mul_invOfUnit_one hu, one_mul]

/-- The logarithmic derivative of `(1 - t ^ e)⁻¹`, for `e > 0`, is `e ∑_{j ≥ 1} t ^ {j e}`: its
coefficient of `t ^ m` is `e` if `e ∣ m` and `m ≠ 0`, and `0` otherwise. -/
theorem coeff_logDerivative_invOfUnit_one_sub_X_pow {e : ℕ} (he : 0 < e) (m : ℕ) :
    coeff m (logDerivative (invOfUnit (1 - X ^ e : R⟦X⟧) 1)) =
      if e ∣ m ∧ m ≠ 0 then (e : R) else 0 := by
  have hu : constantCoeff (1 - X ^ e : R⟦X⟧) = 1 := by simp [he.ne']
  set g := PowerSeries.mk (fun d => if e ∣ d then (1 : R) else 0)
  have hlog : logDerivative (invOfUnit (1 - X ^ e : R⟦X⟧) 1) = (e : R⟦X⟧) * X ^ e * g := by
    rw [logDerivative_invOfUnit hu, logDerivative, invOfUnit_one_sub_X_pow he, map_sub,
      derivative_one, derivative_pow, derivative_X]
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    simp only [Nat.add_sub_cancel, zero_sub]
    push_cast
    ring
  rw [hlog, ← map_natCast (C (R := R)), mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hm : e ≤ m
  · have h : e ∣ m ↔ e ∣ m - e := by
      conv_lhs => rw [← Nat.sub_add_cancel hm]
      exact Nat.dvd_add_left (dvd_refl e)
    rw [ite_eq_left hm, coeff_mk]
    by_cases h' : e ∣ m
    · rw [ite_eq_left (h.1 h'), ite_eq_left ⟨h', by omega⟩, mul_one]
    · rw [ite_eq_right fun x => h' (h.2 x), ite_eq_right fun x => h' x.1, mul_zero]
  · rw [ite_eq_right hm, mul_zero, ite_eq_right]
    rintro ⟨h', hm0⟩
    exact hm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h')

end PowerSeries

namespace Stacks.EtaleCohomology

variable {R : Type*} [CommRing R]

/-- The local Euler factor of the rank-one identity matrix at a point of degree `d` is
`(1 - t ^ d)⁻¹`. -/
theorem localEulerFactor_one_fin_one (d : ℕ) :
    localEulerFactor (1 : Matrix (Fin 1) (Fin 1) R) d =
      PowerSeries.invOfUnit (1 - PowerSeries.X ^ d) 1 := by
  rw [localEulerFactor, localCharSeries_one_fin_one]

/-- Over a field, the local Euler factor of the rank-one identity matrix at a point of nonzero
degree `d` is the inverse `(1 - t ^ d)⁻¹` in `K⟦t⟧`. -/
theorem localEulerFactor_one_fin_one_eq_inv {K : Type*} [Field K] {d : ℕ} (hd : d ≠ 0) :
    localEulerFactor (1 : Matrix (Fin 1) (Fin 1) K) d = (1 - PowerSeries.X ^ d)⁻¹ := by
  have hu : PowerSeries.constantCoeff (1 - PowerSeries.X ^ d : PowerSeries K) = 1 := by
    simp [hd]
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [hu]; exact one_ne_zero),
    localEulerFactor_one_fin_one, mul_comm, PowerSeries.mul_invOfUnit_one hu]

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]

/-- The Euler product agrees modulo `t ^ {m + 1}` with its finite subproduct over the closed
points of degree at most `m`. -/
theorem X_pow_dvd_constantLFunction_sub_partialProduct (m : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (m + 1) ∣
      constantLFunction f ℚ - (constantFrobeniusMatrices f ℚ).eulerSystem.partialProduct m := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  rw [map_sub, sub_eq_zero, constantLFunction,
    FrobeniusMatrices.coeff_lFunction_eq _
      ((constantFrobeniusMatrices f ℚ).eulerSystem.support_subset (show j ≤ m by omega))]
  rfl

/-- **The logarithmic derivative of the Euler product.** The logarithmic derivative of
`∏_{x ∈ |X|} (1 - t ^ {d(x)})⁻¹` is `∑_{n ≥ 1} A_n t ^ n`. -/
theorem logDerivative_constantLFunction :
    PowerSeries.logDerivative (constantLFunction f ℚ) = pointCountSeries f := by
  have hfac : ∀ x, PowerSeries.constantCoeff
      ((constantFrobeniusMatrices f ℚ).eulerSystem.factor x) = 1 := fun x =>
    constantCoeff_localEulerFactor _ _
  ext m
  rw [PowerSeries.coeff_logDerivative_congr (u := constantLFunction f ℚ)
    (FrobeniusMatrices.constantCoeff_lFunction (constantFrobeniusMatrices f ℚ))
    (by rw [EulerSystem.partialProduct, map_prod]; exact Finset.prod_eq_one fun x _ => hfac x)
    (X_pow_dvd_constantLFunction_sub_partialProduct f m)]
  rw [EulerSystem.partialProduct, PowerSeries.logDerivative_finsetProd _ _ fun x _ => hfac x,
    map_sum]
  have hterm : ∀ x : closedPoints X, PowerSeries.coeff m
      (PowerSeries.logDerivative ((constantFrobeniusMatrices f ℚ).eulerSystem.factor x)) =
        if residueDegree f x.1 ∣ m ∧ m ≠ 0 then (residueDegree f x.1 : ℚ) else 0 := by
    intro x
    change PowerSeries.coeff m (PowerSeries.logDerivative
      (localEulerFactor (1 : Matrix (Fin 1) (Fin 1) ℚ) (residueDegree f x.1))) = _
    rw [localEulerFactor_one_fin_one,
      PowerSeries.coeff_logDerivative_invOfUnit_one_sub_X_pow (residueDegree_pos f x.1 x.2)]
  simp_rw [hterm]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pointCountSeries]
  · have : NeZero m := ⟨hm.ne'⟩
    rw [coeff_pointCountSeries f m, pointCountOfDegree_eq_sum_pointDegree f m, Nat.cast_sum,
      ← Finset.sum_filter]
    refine Finset.sum_bij (fun y _ => y.1) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter] at hy
      simp only [Set.Finite.mem_toFinset]
      exact ⟨y.2, hy.2.1⟩
    · intro y₁ _ y₂ _ h
      exact Subtype.ext h
    · intro x hx
      simp only [Set.Finite.mem_toFinset] at hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, EulerSystem.mem_support]
      exact ⟨Nat.le_of_dvd hm hx.2, hx.2, hm.ne'⟩
    · intro y _
      rfl

/-- **The Euler product of the zeta series.** For a scheme `X` of finite type over a finite field
`k`, the zeta series is the Euler product over the closed points,
`f_X(t) = ∏_{x ∈ |X|} (1 - t ^ {d(x)})⁻¹` with `d(x) = [κ(x) : k]`, the product being the
`t`-adically convergent `Stacks.EtaleCohomology.constantLFunction f ℚ`. -/
@[weil "lem_fk0_zeta_euler_product"]
theorem zetaSeries_eq_constantLFunction : zetaSeries f = constantLFunction f ℚ :=
  ((eq_zetaSeries_iff f _).2
    ⟨FrobeniusMatrices.constantCoeff_lFunction _, logDerivative_constantLFunction f⟩).symm

/-- **The Euler product of the zeta series, coefficientwise.** For a scheme `X` of finite type
over a finite field `k` and `N : ℕ`, the coefficient of `t ^ N` of the zeta series is that of the
finite product `∏_{x ∈ s} (1 - t ^ {d(x)})⁻¹` over any finite set `s` of closed points containing
every closed point of degree `d(x) ≤ N`. -/
@[weil "lem_fk0_zeta_euler_product"]
theorem coeff_zetaSeries_eq_coeff_prod (N : ℕ) (s : Finset (closedPoints X))
    (hs : ∀ x : closedPoints X, Scheme.pointDegree f x.1 ≤ N → x ∈ s) :
    PowerSeries.coeff N (zetaSeries f) =
      PowerSeries.coeff N (∏ x ∈ s, (1 - PowerSeries.X ^ Scheme.pointDegree f x.1)⁻¹) := by
  rw [zetaSeries_eq_constantLFunction, constantLFunction,
    FrobeniusMatrices.coeff_lFunction_eq _ (fun x hx => hs x (EulerSystem.mem_support _ |>.1 hx))]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  exact localEulerFactor_one_fin_one_eq_inv (residueDegree_pos f x.1 x.2).ne'

end AlgebraicGeometry
