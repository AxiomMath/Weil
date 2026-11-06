module

public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusIso
public import Weil.Attr

/-!
# The degree of `P_ν` is the `ν`-th ℓ-adic Betti number

Let `X` be a scheme proper over a finite field `k`, `ℓ ≠ char k` a prime, and
`P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))`. Then `deg P_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)`.

Indeed `P_ν` is the reverse of the characteristic polynomial `χ` of `F_ν`, which has degree
`dim H^ν(X_k̄, ℚ_ℓ)`; reversing a polynomial lowers its degree by its trailing degree, which is
`0` here because the constant coefficient of `χ` is `± det F_ν`, a unit since `F_ν` is invertible.

## Main results

* `LinearMap.natDegree_charpoly_reverse_of_isUnit`: for an invertible endomorphism of a finite free
  module over a nontrivial commutative ring, the reverse of the characteristic polynomial has
  degree the rank.
* `Weil.natDegree_rationalFrobeniusCharpolyReverse`: `deg P_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)`.
* `Weil.degree_rationalFrobeniusCharpolyReverse`: the same for `Polynomial.degree`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Polynomial

universe u

namespace LinearMap

variable {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- The constant coefficient of the characteristic polynomial of an invertible endomorphism is
nonzero. -/
theorem charpoly_coeff_zero_ne_zero_of_isUnit {F : Module.End R M} (h : IsUnit F) :
    F.charpoly.coeff 0 ≠ 0 := by
  intro h0
  have hdet : IsUnit (LinearMap.det F) := h.map _
  rw [LinearMap.det_eq_sign_charpoly_coeff, h0, mul_zero] at hdet
  exact not_isUnit_zero hdet

/-- The reverse of the characteristic polynomial of an invertible endomorphism has degree the
rank of the module. -/
theorem natDegree_charpoly_reverse_of_isUnit {F : Module.End R M} (h : IsUnit F) :
    F.charpoly.reverse.natDegree = Module.finrank R M := by
  rw [Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.2 (Or.inr (charpoly_coeff_zero_ne_zero_of_isUnit h)),
    Nat.sub_zero, LinearMap.charpoly_natDegree]

end LinearMap

namespace Weil

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- **`deg P_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)`** for `X` proper over the finite field `k` and
`ℓ ≠ char k`. -/
@[weil "lem_fk401_char_poly_degree_eq_dimension"]
theorem natDegree_rationalFrobeniusCharpolyReverse (ν : ℕ) :
    (rationalFrobeniusCharpolyReverse B X f ℓ ν).natDegree =
      Module.finrank ℚ_[ℓ] (rationalCohomology B X f ℓ ν) :=
  LinearMap.natDegree_charpoly_reverse_of_isUnit (isUnit_rationalFrobenius B X f ℓ ν)

/-- `deg P_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)`, for `Polynomial.degree`. -/
theorem degree_rationalFrobeniusCharpolyReverse (ν : ℕ) :
    (rationalFrobeniusCharpolyReverse B X f ℓ ν).degree =
      Module.finrank ℚ_[ℓ] (rationalCohomology B X f ℓ ν) := by
  rw [← natDegree_rationalFrobeniusCharpolyReverse]
  exact Polynomial.degree_eq_natDegree
    (mt Polynomial.reverse_eq_zero.1 (rationalFrobenius B X f ℓ ν).charpoly_monic.ne_zero)

end Weil
