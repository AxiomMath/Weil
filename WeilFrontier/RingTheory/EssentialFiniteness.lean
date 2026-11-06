module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilFrontier.Defs.RingTheory.EssentialFiniteness
public import Weil.Attr

/-!
# Localizations of finitely generated algebras at primes

Let `C` be a finitely generated `A`-algebra, `𝔓` a prime ideal of `C` and `𝔮 = 𝔓 ∩ A`. Then
the induced homomorphism `A_𝔮 → C_𝔓` is a finitely generated local homomorphism: it is local,
and `C_𝔓` is essentially of finite type over `A_𝔮`.

## Main results

* `Algebra.isFinitelyGeneratedLocal_localization_atPrime`: for `𝔓` lying over `𝔮`, the
  homomorphism `A_𝔮 → C_𝔓` is a finitely generated local homomorphism.

## Implementation notes

Freitag–Kiehl assume `A` noetherian; the statement holds for every commutative ring `A`. The
algebra structure of `C_𝔓` over `A_𝔮` is any one compatible with `Localization.localRingHom`
(the class `Localization.AtPrime.IsLiesOverAlgebra`), for instance
`Localization.AtPrime.algebraOfLiesOver`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

universe u v

namespace Algebra

variable {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]

/-- If `C` is a finitely generated `A`-algebra and `𝔓` is a prime of `C` lying over the prime
`𝔮` of `A`, then `A_𝔮 → C_𝔓` is a finitely generated local homomorphism. -/
@[weil "lem_fk101_localization_is_finitely_generated_local"]
theorem isFinitelyGeneratedLocal_localization_atPrime [FiniteType A C]
    (q : Ideal A) [q.IsPrime] (P : Ideal C) [P.IsPrime] [P.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra q P] :
    IsFinitelyGeneratedLocal (Localization.AtPrime q) (Localization.AtPrime P) := by
  refine ⟨?_, ?_⟩
  · rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  · have : EssFiniteType C (Localization.AtPrime P) :=
      EssFiniteType.of_isLocalization (Localization.AtPrime P) P.primeCompl
    have : EssFiniteType A (Localization.AtPrime P) :=
      EssFiniteType.comp A C (Localization.AtPrime P)
    exact EssFiniteType.of_comp A (Localization.AtPrime q) (Localization.AtPrime P)

/-- The Freitag–Kiehl form: for a prime `𝔓` of a finitely generated `A`-algebra `C`, the
homomorphism `A_{𝔓 ∩ A} → C_𝔓` (with its canonical algebra structure) is a finitely generated
local homomorphism. -/
@[weil "lem_fk101_localization_is_finitely_generated_local"]
theorem isFinitelyGeneratedLocal_localization_comap_atPrime [FiniteType A C]
    (P : Ideal C) [P.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (P.comap (algebraMap A C)) P
    IsFinitelyGeneratedLocal (Localization.AtPrime (P.comap (algebraMap A C)))
      (Localization.AtPrime P) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.comap (algebraMap A C)) P
  exact isFinitelyGeneratedLocal_localization_atPrime _ P

end Algebra

end
