module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import Weil.RingTheory.Henselian.Henselization.HenselianLineDomain
public import Weil.RingTheory.Henselian.Henselization.HenselianLineModPrime
public import StacksFrontier.RingTheory.Henselian.Quotient

/-!
# Extending a prime ideal of the base to the henselian polynomial ring

Let `A` be a henselian noetherian local ring, `𝔭 ⊂ A` a prime ideal and `T = (T_i)_{i ∈ σ}` a
finite family of indeterminates. Write `A{T}` for the Henselization of `A[T]` at the origin
(`MvPolynomial.IsHenselianPolynomialRing`). Then `𝔭 A{T}` is a prime ideal of `A{T}`.

Indeed `A ⧸ 𝔭` is a henselian noetherian local domain, so `(A ⧸ 𝔭){T}` is a domain, and
`A{T} ⧸ 𝔭 A{T} ≅ (A ⧸ 𝔭){T}`.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.isPrime_map`: `𝔭 A{T}` is a prime ideal of `A{T}`.

## Implementation notes

The source treats one indeterminate `t` (the case `σ = Fin 1`); any finite family is allowed
here. That `A ⧸ 𝔭` is henselian is taken from the fact that a quotient of a henselian local ring
by a proper ideal is henselian, `A ⧸ 𝔭` being a local ring finite over `A`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open IsLocalRing

universe u v w

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] {σ : Type v}
  [Finite σ]

/-- **The extension of a prime ideal of the base to `A{T}` is prime.** Let `A` be a henselian
noetherian local ring, `𝔭` a prime ideal of `A`, `T` a finite family of indeterminates and
`B = A{T}` the Henselization of `A[T]` at the origin. Then `𝔭 B` is a prime ideal of `B`. -/
@[weil "lem_fk107_henselian_line_extended_prime_is_prime"]
theorem isPrime_map (𝔭 : Ideal A) [𝔭.IsPrime]
    {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
    [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]
    (hB : IsHenselianPolynomialRing A σ B) :
    (𝔭.map (algebraMap A B)).IsPrime := by
  have : IsLocalRing (A ⧸ 𝔭) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : HenselianLocalRing (A ⧸ 𝔭) :=
    Stacks.Henselian.henselianLocalRing_quotient (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨B', _, _, _, hB'⟩ := exists_isHenselianPolynomialRing (A ⧸ 𝔭) σ
  have : IsDomain B' := isDomain hB'
  obtain ⟨e, -⟩ := exists_ringEquiv_quotient_of_isHenselianPolynomialRing 𝔭 hB hB'
  have : IsDomain (B ⧸ 𝔭.map (algebraMap A B)) := e.toMulEquiv.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

end MvPolynomial.IsHenselianPolynomialRing
