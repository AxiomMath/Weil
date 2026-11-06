module

public import Weil.Attr
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height

/-!
# Divisorial ideals

An ideal `𝔞` of a commutative ring `R` is *divisorial* if every associated prime of the
`R`-module `R ⧸ 𝔞` has height `1`. The unit ideal is divisorial, since `R ⧸ ⊤` is the zero
module and has no associated primes. For a noetherian normal domain the divisorial ideals are
those whose primary decomposition involves only primes of height one; for instance a nonzero
principal ideal of a noetherian normal domain is divisorial.

An ideal `𝔟` *divides* `𝔞` when `𝔞 ≤ 𝔟`; this is the order on `Ideal R` and needs no definition.

## Main definitions

* `Ideal.IsDivisorial`: every associated prime of `R ⧸ 𝔞` has height `1`.

## Main results

* `Ideal.isDivisorial_top`: the unit ideal is divisorial.
* `Ideal.IsDivisorial.height_eq_one`: an associated prime of `R ⧸ 𝔞` has height `1`.
* `Ideal.IsPrime.isDivisorial_of_height_eq_one`: over a noetherian ring, a prime of height `1`
  is divisorial.

## Implementation notes

The source defines the notion for a noetherian integral domain; the definition is stated for
any commutative ring, since none of these hypotheses is needed to state it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- An ideal `a` is divisorial if every associated prime of `R ⧸ a` has height `1`. -/
@[weil "def_fk107_divisorial_ideal"]
def IsDivisorial (a : Ideal R) : Prop :=
  ∀ P ∈ associatedPrimes R (R ⧸ a), P.height = 1

theorem isDivisorial_iff {a : Ideal R} :
    a.IsDivisorial ↔ ∀ P ∈ associatedPrimes R (R ⧸ a), P.height = 1 :=
  Iff.rfl

theorem IsDivisorial.height_eq_one {a P : Ideal R} (ha : a.IsDivisorial)
    (hP : P ∈ associatedPrimes R (R ⧸ a)) : P.height = 1 :=
  ha P hP

/-- The unit ideal is divisorial: `R ⧸ ⊤` has no associated primes. -/
theorem isDivisorial_top : (⊤ : Ideal R).IsDivisorial := by
  intro P hP
  rw [associatedPrimes.eq_empty_of_subsingleton] at hP
  exact absurd hP (Set.notMem_empty P)

/-- Over a noetherian ring, a prime ideal of height `1` is divisorial. -/
theorem IsPrime.isDivisorial_of_height_eq_one [IsNoetherianRing R] {P : Ideal R}
    (hP : P.IsPrime) (h : P.height = 1) : P.IsDivisorial := by
  intro Q hQ
  rw [associatedPrimes.eq_singleton_of_isPrimary hP.isPrimary] at hQ
  rw [Set.mem_singleton_iff.mp hQ, hP.radical, h]

end Ideal

end
