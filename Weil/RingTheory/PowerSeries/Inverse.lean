module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Weil.Attr

/-!
# Rationality of a power series descends to a subfield

Let `K → L` be a field extension and `g ∈ K⟦X⟧`. If `g`, viewed in `L⟦X⟧`, is rational, i.e.
`Q * g = P` for polynomials `P, Q ∈ L[X]` with `Q ≠ 0`, then `g` is already rational over `K`:
there are `P₁, Q₁ ∈ K[X]` with `Q₁(0) = 1` and `Q₁ * g = P₁`.

The proof applies a `K`-linear functional `φ : L → K` coefficientwise. Since the coefficients of
`g` lie in `K`, the coefficients of `Q * g` are `K`-linear combinations of the coefficients of
`Q`, so `φ` carries the relation `Q * g = P` to a relation `φ(Q) * g = φ(P)` over `K`; choosing
`φ` nonzero on some coefficient of `Q` makes `φ(Q) ≠ 0`. Finally a relation `Q * g = P` with
`Q ≠ 0` can be normalised to `Q(0) = 1` by cancelling powers of `X`.

## Main results

* `PowerSeries.exists_coeff_zero_eq_one_mul_eq_of_mul_eq`: over a field, a relation
  `Q * g = P` with `Q ≠ 0` gives one with `Q₁(0) = 1`.
* `PowerSeries.exists_mul_eq_of_map_algebraMap_mul_eq`: rationality of `g ∈ K⟦X⟧` over an
  extension field `L` implies rationality over `K`, with denominator of constant term `1`.

## Implementation notes

The source argues with the rank of a finite system of linear equations, which is invariant under
extension of the base field. We instead apply a `K`-linear functional `L → K` to the coefficients,
which avoids choosing a finite subsystem.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Introduction.
-/

@[expose] public section

open Polynomial

namespace PowerSeries

/-- Over a field, a relation `Q * g = P` between a power series `g` and polynomials `P, Q` with
`Q ≠ 0` can be normalised to one whose denominator has constant term `1`. -/
theorem exists_coeff_zero_eq_one_mul_eq_of_mul_eq {F : Type*} [Field F] {g : F⟦X⟧}
    {P Q : F[X]} (hQ : Q ≠ 0) (h : (Q : F⟦X⟧) * g = P) :
    ∃ P₁ Q₁ : F[X], Q₁.coeff 0 = 1 ∧ (Q₁ : F⟦X⟧) * g = P₁ := by
  induction hn : Q.natDegree using Nat.strong_induction_on generalizing P Q with
  | _ n ih =>
    by_cases h0 : Q.coeff 0 = 0
    · -- `X` divides `Q`, hence `P`; cancel it.
      have hP0 : P.coeff 0 = 0 := by
        have := congrArg (coeff 0) h
        simpa [Polynomial.coeff_coe, coeff_zero_eq_constantCoeff_apply, h0] using this.symm
      have hQX : Q = Polynomial.X * Q.divX := by simpa [h0] using (X_mul_divX_add Q).symm
      have hPX : P = Polynomial.X * P.divX := by simpa [hP0] using (X_mul_divX_add P).symm
      have hdiv : Q.divX ≠ 0 := by
        intro hd
        exact hQ (by rw [hQX, hd, mul_zero])
      have hdeg : Q.divX.natDegree < n := by
        rw [← hn, natDegree_divX_eq_natDegree_tsub_one]
        have : Q.natDegree ≠ 0 := by
          intro hz
          apply hQ
          rw [eq_C_of_natDegree_eq_zero hz, h0, map_zero]
        omega
      refine ih _ hdeg hdiv (P := P.divX) ?_ rfl
      have hX : (PowerSeries.X : F⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
      apply mul_left_cancel₀ hX
      rw [← mul_assoc]
      have e1 : (PowerSeries.X : F⟦X⟧) * (Q.divX : F⟦X⟧) = (Q : F⟦X⟧) := by
        conv_rhs => rw [hQX]
        rw [Polynomial.coe_mul, Polynomial.coe_X]
      have e2 : (PowerSeries.X : F⟦X⟧) * (P.divX : F⟦X⟧) = (P : F⟦X⟧) := by
        conv_rhs => rw [hPX]
        rw [Polynomial.coe_mul, Polynomial.coe_X]
      rw [e1, e2, h]
    · refine ⟨Polynomial.C (Q.coeff 0)⁻¹ * P, Polynomial.C (Q.coeff 0)⁻¹ * Q, ?_, ?_⟩
      · simp [h0]
      · rw [Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc, h]

/-- **Rationality descends to a subfield.** Let `K → L` be a field extension and `g ∈ K⟦X⟧`.
If `Q * g = P` in `L⟦X⟧` for polynomials `P, Q ∈ L[X]` with `Q ≠ 0`, then there are
`P₁, Q₁ ∈ K[X]` with `Q₁(0) = 1` and `Q₁ * g = P₁` in `K⟦X⟧`. -/
@[weil "lem_fk0_rational_series_descends_to_subfield"]
theorem exists_mul_eq_of_map_algebraMap_mul_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (g : K⟦X⟧) {P Q : L[X]} (hQ : Q ≠ 0)
    (h : (Q : L⟦X⟧) * g.map (algebraMap K L) = P) :
    ∃ P₁ Q₁ : K[X], Q₁.coeff 0 = 1 ∧ (Q₁ : K⟦X⟧) * g = P₁ := by
  obtain ⟨j, hj⟩ : ∃ j, Q.coeff j ≠ 0 := by
    by_contra! hc
    exact hQ (Polynomial.ext fun n => by simp [hc n])
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hj
  -- apply `φ` to every coefficient of a polynomial
  let ψ : L[X] → K[X] := fun p =>
    ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i))
  have hψ : ∀ p n, (ψ p).coeff n = φ (p.coeff n) := fun p n => by
    simp only [ψ, finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hn
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have key : ∀ n, coeff n ((ψ Q : K⟦X⟧) * g) =
      φ (coeff n ((Q : L⟦X⟧) * g.map (algebraMap K L))) := by
    intro n
    simp only [coeff_mul, Polynomial.coeff_coe, hψ, coeff_map, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_comm (Q.coeff x.1), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  refine exists_coeff_zero_eq_one_mul_eq_of_mul_eq (P := ψ P) (Q := ψ Q) ?_ ?_
  · intro h0
    apply hφ
    rw [← hψ, h0, Polynomial.coeff_zero]
  · ext n
    rw [key, h, Polynomial.coeff_coe, Polynomial.coeff_coe, hψ]

end PowerSeries

end
