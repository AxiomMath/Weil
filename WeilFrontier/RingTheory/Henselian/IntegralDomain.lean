module

public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Nagata.Shrink
public import Weil.Attr

/-!
# Integral closure of an excellent henselian local domain in a finite extension

Let `A` be an excellent henselian local domain with field of fractions `K`, and let `L` be a
finite field extension of `K`. The integral closure `A_L` of `A` in `L` is a finite `A`-module,
because an excellent ring is quasi-excellent, hence Nagata, so the domain `A` is Japanese
(N-2). Consequently `A_L` is Noetherian. Being a domain integral over the henselian local
ring `A`, it is itself a henselian local ring, and `A → A_L` is a local homomorphism.

## Main results

* `IsExcellent.module_finite_integralClosure`: for an excellent domain `A` with fraction field
  `K` and a finite extension `L / K`, the integral closure of `A` in `L` is a finite `A`-module.
* `IsExcellent.henselianLocalRing_integralClosure`: if moreover `A` is a henselian local ring,
  then the integral closure of `A` in `L` is a henselian local Noetherian ring, finite over `A`,
  and `A → A_L` is a local homomorphism.

## Implementation notes

The integral closure is `integralClosure A L`, an `A`-subalgebra of `L`; it is a domain as a
subring of a field. The field `L` and the fraction field `K` may live in arbitrary universes.

The henselian and locality assertions are Stacks Tag 092X
(`RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain`), which holds for any domain
integral over a henselian local ring; finiteness is not needed for them, only for Noetherianity.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7]
* [Stacks Project, Tag 07QV](https://stacks.math.columbia.edu/tag/07QV)
* [Stacks Project, Tag 092X](https://stacks.math.columbia.edu/tag/092X)
-/

@[expose] public section

universe u v w

namespace IsExcellent

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The integral closure of an excellent domain in a finite extension of its field of fractions
is a finite module. -/
theorem module_finite_integralClosure (hA : IsExcellent A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    Module.Finite A (integralClosure A L) :=
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  module_finite_integralClosure_of_isJapaneseRing
    (IsJapaneseRing.of_ringEquiv (RingEquiv.quotientBot A)
      ((isNagataRing_of_isQuasiExcellent hA.1).isJapaneseRing_quotient ⊥)) K L

/-- **Integral closure of an excellent henselian local domain.** Let `A` be an excellent
henselian local domain with field of fractions `K` and `L / K` a finite field extension. Then the
integral closure `A_L` of `A` in `L` is a henselian local Noetherian domain, finite over `A`,
and `A → A_L` is a local homomorphism. -/
@[weil "lem_fk107_integral_closure_local_henselian"]
theorem henselianLocalRing_integralClosure [HenselianLocalRing A] (hA : IsExcellent A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    HenselianLocalRing (integralClosure A L) ∧ IsNoetherianRing (integralClosure A L) ∧
      Module.Finite A (integralClosure A L) ∧
      IsLocalHom (algebraMap A (integralClosure A L)) := by
  have hfin := module_finite_integralClosure hA K L
  have : IsNoetherianRing A := hA.1.1
  obtain ⟨hB, hloc, -⟩ := RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
    (algebraMap A (integralClosure A L))
    (Algebra.IsIntegral.isIntegral (R := A) (A := integralClosure A L))
  refine ⟨hB, ?_, hfin, hloc⟩
  exact isNoetherian_of_tower A (isNoetherian_of_isNoetherianRing_of_finite A _)

end IsExcellent

end
