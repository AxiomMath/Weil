module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSystemLocalFactor
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ZetaEulerProduct
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ZetaSeriesProductOfPointCountSum
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import WeilFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.FiniteExistence
public import WeilFrontier.AlgebraicGeometry.NagataCompactification.AffineFiniteTypeCompactifiable
public import WeilFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification
public import WeilFrontier.RingTheory.PowerSeries.Inverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification

/-!
# Rationality of the zeta series of a scheme of finite type over a finite field

Let `k` be a finite field and `X` a scheme of finite type over `k`. The zeta series
`f_X = exp (∑_{n ≥ 1} A_n tⁿ / n) ∈ ℚ⟦t⟧`, `A_n` the number of points of `X` with values in the
degree-`n` extension of `k`, is the expansion of a rational function (Dwork, Grothendieck):
there are `P, Q ∈ ℚ[t]` with `Q(0) = 1` and `Q f_X = P`.

The proof is that of [FK, Introduction (1)] together with [FK, II.4]: the zeta function
`Z_X ∈ ℚ_ℓ⟦t⟧` of `X` (the `L`-function of the constant `ℓ`-adic sheaf) is the Euler product
`∏_{x ∈ |X|} (1 - t^{deg x})⁻¹`, which is also the zeta series `f_X`; for `X` compactifiable,
the trace formula (Stacks, Tag 03V0) makes `Z_X` rational over `ℚ_ℓ`, and rationality descends
to `ℚ`; an arbitrary `X` is cut into finitely many affine locally closed pieces, each of which is
compactifiable, and `f_X` is the product of their zeta series.

## Main results

* `Weil.zetaFunction_eq_constantLFunction`: `Z_X = ∏_{x ∈ |X|} (1 - t^{deg x})⁻¹` in `ℚ_ℓ⟦t⟧`.
* `Weil.map_zetaSeries_eq_zetaFunction`: the image of `f_X` in `ℚ_ℓ⟦t⟧` is `Z_X`.
* `Weil.zetaFunction_eq_map_constantLFunction_int`, `Weil.exists_zetaFunction_eq_map_int`:
  `Z_X ∈ 1 + t ℤ⟦t⟧`.
* `Weil.exists_zetaFunction_eq_map_int_of_two_primes`: `Z_X` formed with `ℚ_ℓ` and with `ℚ_ℓ'` is
  the same element of `ℤ⟦t⟧`.
* `AlgebraicGeometry.exists_mul_zetaSeries_eq_of_hasCompactification`: rationality for a
  compactifiable `X`.
* `AlgebraicGeometry.exists_mul_zetaSeries_eq`: **rationality of the zeta series** of every
  scheme of finite type over `k`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Introduction (1), II.4,
  IV.1.
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology PowerSeries

universe u

namespace Weil

section ZetaFunction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]

/-- **The Euler product of the zeta function** (FK IV.1). For a scheme `X` of finite type over a
finite field, `Z_X(t) = ∏_{x ∈ |X|} (1 - t^{deg x})⁻¹` in `ℚ_ℓ⟦t⟧`, the `t`-adically convergent
product being `Stacks.EtaleCohomology.constantLFunction f ℚ_ℓ`. -/
@[weil "lem_fk401_zeta_euler_product"]
theorem zetaFunction_eq_constantLFunction :
    zetaFunction B X ℓ f = constantLFunction f ℚ_[ℓ] := by
  have := isNoetherian_of_finiteType f
  have : IsLocallyNoetherian X.1 := LocallyOfFiniteType.isLocallyNoetherian f
  have : QuasiSeparatedSpace X.1 := IsLocallyNoetherian.quasiSeparatedSpace
  rw [zetaFunction_def]
  exact rationalLFunction_constantSystem B X ℓ f

/-- **The zeta series is the `L`-series of the constant sheaf** (FK, Introduction). The image of
the zeta series `f_X ∈ ℚ⟦t⟧` under the coefficientwise inclusion `ℚ ⊆ ℚ_ℓ` is the zeta function
`Z_X(t) ∈ ℚ_ℓ⟦t⟧`. -/
@[weil "lem_fk0_zeta_series_eq_l_series"]
theorem map_zetaSeries_eq_zetaFunction :
    PowerSeries.map (algebraMap ℚ ℚ_[ℓ]) (zetaSeries f) = zetaFunction B X ℓ f := by
  rw [zetaFunction_eq_constantLFunction, zetaSeries_eq_constantLFunction, map_constantLFunction]

/-- The zeta function is the image of the Euler product `∏_{x ∈ |X|} (1 - t^{deg x})⁻¹` formed
in `ℤ⟦t⟧`. -/
theorem zetaFunction_eq_map_constantLFunction_int :
    zetaFunction B X ℓ f = PowerSeries.map (Int.castRingHom ℚ_[ℓ]) (constantLFunction f ℤ) := by
  rw [zetaFunction_eq_constantLFunction, map_constantLFunction]

/-- **The zeta function has integer coefficients** (FK IV.1): `Z_X(t) ∈ 1 + t ℤ⟦t⟧ ⊆ ℚ_ℓ⟦t⟧`. -/
@[weil "lem_fk401_zeta_integer_coefficients"]
theorem exists_zetaFunction_eq_map_int :
    ∃ g : ℤ⟦X⟧, constantCoeff g = 1 ∧
      zetaFunction B X ℓ f = PowerSeries.map (Int.castRingHom ℚ_[ℓ]) g := by
  refine ⟨constantLFunction f ℤ, ?_, zetaFunction_eq_map_constantLFunction_int B X ℓ f⟩
  exact FrobeniusMatrices.constantCoeff_lFunction _

/-- **The zeta function does not depend on `ℓ`** (FK IV.1). For primes `ℓ, ℓ'`, the zeta function
formed with `ℚ_ℓ` and the one formed with `ℚ_ℓ'` are the images of the same series `g ∈ ℤ⟦t⟧`. -/
@[weil "lem_fk401_zeta_independent_of_l"]
theorem exists_zetaFunction_eq_map_int_of_two_primes (ℓ' : ℕ) [Fact ℓ'.Prime] :
    ∃ g : ℤ⟦X⟧, constantCoeff g = 1 ∧
      zetaFunction B X ℓ f = PowerSeries.map (Int.castRingHom ℚ_[ℓ]) g ∧
      zetaFunction B X ℓ' f = PowerSeries.map (Int.castRingHom ℚ_[ℓ']) g :=
  ⟨constantLFunction f ℤ, FrobeniusMatrices.constantCoeff_lFunction _,
    zetaFunction_eq_map_constantLFunction_int B X ℓ f,
    zetaFunction_eq_map_constantLFunction_int B X ℓ' f⟩

end ZetaFunction

end Weil

namespace AlgebraicGeometry

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

variable {k : Type u} [Field k] [Finite k]

/-- A compactifiable morphism is separated: it is an open immersion followed by a proper
morphism. -/
theorem isSeparated_of_compactificationOf {X : Scheme.{u}} {S : Scheme.{u}} {f : X ⟶ S}
    (j : CompactificationOf (Over.mk f)) : IsSeparated f := by
  have hj : IsOpenImmersion j.immersion := j.property.1
  have hp : IsProper j.toBase := j.property.2
  have hw : j.immersion ≫ j.toBase = f := by
    exact Over.w j.obj.hom
  rw [← hw]
  infer_instance

/-- There is a prime number different from a given natural number. -/
private theorem exists_prime_ne (p : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
  obtain ⟨ℓ, hℓ, hp⟩ := Nat.exists_infinite_primes (p + 1)
  exact ⟨ℓ, hp, by omega⟩

/-- **Rationality of the zeta series of a compactifiable scheme** (FK II.4). Let `X` be a scheme
of finite type over the finite field `k` whose structure morphism is compactifiable. Then there
are polynomials `P, Q ∈ ℚ[t]` with `Q(0) = 1` and `Q f_X = P` in `ℚ⟦t⟧`. -/
@[weil "lem_fk0_zeta_series_rational_compactifiable"]
theorem exists_mul_zetaSeries_eq_of_hasCompactification {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (hf : HasCompactification f) :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧ (Q : ℚ⟦X⟧) * zetaSeries f = P := by
  obtain ⟨j, -⟩ := hf
  have := isSeparated_of_compactificationOf j
  obtain ⟨ℓ, hℓ, hℓp⟩ := exists_prime_ne (ringChar k)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let B := BigEtaleSite.containing X
  let X' : B.Scheme := ⟨X, BigEtaleSite.contains_containing X⟩
  let f' : X'.1 ⟶ Spec (.of k) := f
  have : LocallyOfFiniteType f' := ‹_›
  have : QuasiCompact f' := ‹_›
  have : IsSeparated f' := ‹_›
  have := Weil.isNoetherian_of_finiteType f'
  have : QuasiSeparatedSpace X'.1 := quasiSeparatedSpace_of_quasiSeparated f'
  obtain ⟨P, Q, hQ, hPQ⟩ := Weil.exists_rationalLFunction_mul_eq_polynomial B X' ℓ f' j hℓp
    (LAdicSheaf.constantSystem B X' ℓ)
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQ
  refine PowerSeries.exists_mul_eq_of_map_algebraMap_mul_eq (zetaSeries f) (P := P) hQ0 ?_
  rw [mul_comm, ← hPQ]
  congr 1
  rw [← Weil.zetaFunction_def]
  exact Weil.map_zetaSeries_eq_zetaFunction B X' ℓ f'

/-- **Rationality of the zeta series** (Dwork; FK, Introduction (1)). Let `X` be a scheme of
finite type over a finite field `k` and `f_X ∈ ℚ⟦t⟧` its zeta series. Then there are polynomials
`P, Q ∈ ℚ[t]` with `Q(0) = 1` and `Q f_X = P` in `ℚ⟦t⟧`: `f_X` is the expansion at `t = 0` of
the rational function `P / Q`. -/
@[weil "thm_fk0_weil_rationality"]
theorem exists_mul_zetaSeries_eq {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧ (Q : ℚ⟦X⟧) * zetaSeries f = P := by
  obtain ⟨r, Y, hY, hdisj, hcover, hYi⟩ := exists_affine_locallyClosed_partition_of_finiteType f
  let g : ∀ i, reducedInducedScheme (Y i) (hY i) ⟶ X := fun i =>
    reducedInducedInclusion (Y i) (hY i)
  have hrange : ∀ i, Set.range (g i) = Y i := fun i => range_reducedInducedInclusion (Y i) (hY i)
  have hrat : ∀ i, ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      (Q : ℚ⟦X⟧) * zetaSeries (g i ≫ f) = P := by
    intro i
    obtain ⟨hA, hL, hC⟩ := hYi i
    exact exists_mul_zetaSeries_eq_of_hasCompactification (g i ≫ f)
      (hasCompactification_of_isAffine_of_field (g i ≫ f))
  choose P Q hQ hPQ using hrat
  have hcount : ∀ (n : ℕ) [NeZero n],
      pointCountOfDegree f n = ∑ i ∈ Finset.univ, pointCountOfDegree (g i ≫ f) n := by
    intro n _
    have : ∀ i, LocallyOfFiniteType (g i ≫ f) := fun i => (hYi i).2.1
    have : ∀ i, QuasiCompact (g i ≫ f) := fun i => (hYi i).2.2
    refine pointCountOfDegree_eq_sum_of_isPreimmersion f g ?_ ?_ n
    · intro i j hij
      rw [hrange, hrange]
      exact hdisj hij
    · intro x
      have : x ∈ ⋃ i, Y i := hcover ▸ Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
      exact ⟨i, (hrange i).symm ▸ hi⟩
  refine ⟨∏ i, P i, ∏ i, Q i, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_prod]
    simp [hQ]
  · have hc : ∀ s : Fin r → Polynomial ℚ,
        ((∏ i, s i : Polynomial ℚ) : ℚ⟦X⟧) = ∏ i, (s i : ℚ⟦X⟧) := fun s =>
      map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) s Finset.univ
    rw [zetaSeries_eq_prod_of_pointCountOfDegree_eq_sum f Finset.univ (fun i => g i ≫ f) hcount,
      hc, hc, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hPQ i

end AlgebraicGeometry
