module

public import Weil.Attr
public import Weil.Defs.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Openness of the unramified locus

Let `B` be an algebra essentially of finite type over a ring `A`. The set of primes `P` of `B`
such that `A_{P ∩ A} → B_P` is an unramified local homomorphism is open in `Spec B`. Indeed, this
set is Mathlib's unramified locus `Algebra.unramifiedLocus A B`, the complement of the support of
the finitely generated module `Ω[B⁄A]`.

## Main results

- `Algebra.setOf_isUnramifiedLocal_eq_unramifiedLocus`: the set of primes `P` with
  `A_{P ∩ A} → B_P` unramified is the unramified locus.
- `Algebra.isOpen_setOf_isUnramifiedLocal`: this set is open.

## Implementation notes

The source assumes `A` noetherian and `B` of finite type over `A`; only essential finite type
of `B` over `A` is used. The algebra structure of `B_P` over `A_{P ∩ A}` is
`Localization.AtPrime.algebraOfLiesOver`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

public section

namespace Algebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- The set of primes `P` of `B` such that `A_{P ∩ A} → B_P` is an unramified local
homomorphism is the unramified locus of `B` over `A`. -/
lemma setOf_isUnramifiedLocal_eq_unramifiedLocus [EssFiniteType A B] :
    {P : PrimeSpectrum B |
      letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under A) P.asIdeal
      IsUnramifiedLocal (Localization.AtPrime (P.asIdeal.under A))
        (Localization.AtPrime P.asIdeal)} = unramifiedLocus A B := by
  ext P
  let := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under A) P.asIdeal
  exact (isUnramifiedAt_iff_isUnramifiedLocal A (P.asIdeal.under A) P.asIdeal).symm

/-- For `B` essentially of finite type over `A` (e.g. `A` noetherian and `B` a finitely
generated `A`-algebra), the set of primes `P` of `B` such that `A_{P ∩ A} → B_P` is an
unramified local homomorphism is open in `Spec B`. -/
@[weil "lem_fk101_unramified_locus_open"]
theorem isOpen_setOf_isUnramifiedLocal [EssFiniteType A B] :
    IsOpen {P : PrimeSpectrum B |
      letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under A) P.asIdeal
      IsUnramifiedLocal (Localization.AtPrime (P.asIdeal.under A))
        (Localization.AtPrime P.asIdeal)} := by
  rw [setOf_isUnramifiedLocal_eq_unramifiedLocus]
  exact isOpen_unramifiedLocus

end Algebra

end
