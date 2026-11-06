module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius
public import Weil.Attr
public import WeilFrontier.Definitions

/-!
# The sign in the functional equation of the zeta function

Let `k` be a finite field with `q` elements, `ℓ ≠ char k` a prime and `X` a scheme proper over
`k` of dimension `n`. The *sign of the functional equation* is

`ε = 1` if `n` is odd, and `ε = (-1) ^ N` if `n` is even,

where `N` is the (algebraic) multiplicity of `q ^ (n / 2) ∈ ℤ ⊆ ℚ_ℓ` as an eigenvalue of the
Frobenius endomorphism `F_n` of `H^n(X_k̄, ℚ_ℓ)`, that is, its multiplicity as a root of the
characteristic polynomial of `F_n`.

## Main definitions

Defined in `WeilFrontier.Definitions`:

* `Weil.functionalEquationSign`: the sign `ε`.

## Main results

* `Weil.functionalEquationSign_of_odd`, `Weil.functionalEquationSign_of_even`: the two cases.
* `Weil.functionalEquationSign_mul_self`: `ε * ε = 1`.
* `Weil.functionalEquationSign_eq_one_or_eq_neg_one`: `ε = 1` or `ε = -1`.

## Implementation notes

The degree `n` is an explicit argument rather than the dimension of `X` read off from `X`: the
functional equation is stated for `X` of pure dimension `n`, and it is that `n` which enters.
The sign is an integer; the multiplicity is `Polynomial.rootMultiplicity` of `q ^ (n / 2)` in
`LinearMap.charpoly` of `Weil.rationalFrobenius`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

theorem functionalEquationSign_of_odd {n : ℕ} (hn : Odd n) :
    functionalEquationSign B X f ℓ n = 1 := by
  simp [functionalEquationSign, hn]

theorem functionalEquationSign_of_even {n : ℕ} (hn : Even n) :
    functionalEquationSign B X f ℓ n =
      (-1) ^ Polynomial.rootMultiplicity ((Fintype.card k : ℚ_[ℓ]) ^ (n / 2))
        (rationalFrobenius B X f ℓ n).charpoly := by
  simp [functionalEquationSign, Nat.not_odd_iff_even.mpr hn]

theorem functionalEquationSign_mul_self (n : ℕ) :
    functionalEquationSign B X f ℓ n * functionalEquationSign B X f ℓ n = 1 := by
  unfold functionalEquationSign
  split_ifs
  · rfl
  · rw [← mul_pow]; simp

theorem functionalEquationSign_eq_one_or_eq_neg_one (n : ℕ) :
    functionalEquationSign B X f ℓ n = 1 ∨ functionalEquationSign B X f ℓ n = -1 := by
  unfold functionalEquationSign
  split_ifs
  · exact Or.inl rfl
  · exact neg_one_pow_eq_or ℤ _

theorem isUnit_functionalEquationSign (n : ℕ) : IsUnit (functionalEquationSign B X f ℓ n) :=
  IsUnit.of_mul_eq_one _ (functionalEquationSign_mul_self B X f ℓ n)

end Weil
