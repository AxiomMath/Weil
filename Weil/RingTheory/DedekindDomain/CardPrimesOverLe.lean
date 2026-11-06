module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The number of primes over a prime is at most the degree

Let `R` be an integral domain and `S` a finite flat `R`-algebra. For a prime `p` of `R`, the
fundamental identity `∑_{q ∣ p} e(q | p) f(q | p) = rank_R S` and the positivity of the
ramification indices and inertia degrees give that at most `rank_R S` primes of `S` lie over `p`.

For an extension of Dedekind domains `S / R` with fraction fields `L / K`, this says that a
nonzero maximal ideal of `R` has at most `[L : K]` prime factors in `S`. We specialise to the
case used for curves: `K` a finite separable extension of the rational function field `k(X)`,
`S` the integral closure of `k[X]` in `K`, and the prime `(X - b)` of `k[X]`.

## Main results

* `Ideal.ncard_primesOver_le_finrank`: `#{q ∣ p} ≤ rank_R S` for `S` finite flat over a domain.
* `IsDedekindDomain.card_primesOverFinset_le_finrank`: the Dedekind form, `≤ [L : K]`.
* `Polynomial.ncard_primesOver_X_sub_C_le_finrank`: at most `[K : k(X)]` primes of the
  integral closure of `k[X]` in `K` lie over `(X - b)`.
* `Polynomial.card_primesOverFinset_X_sub_C_le_finrank`: the same for
  `integralClosure k[X] K`, phrased with `IsDedekindDomain.primesOverFinset`; the instances
  `Polynomial.faithfulSMul_of_ratFunc` and `Polynomial.isDedekindDomain_integralClosure` make
  that statement elaborate.

## Implementation notes

The bound is derived from `Ideal.sum_ramification_inertia_eq_finrank`, the fundamental identity
for finite flat extensions of domains, together with `Ideal.ramificationIdx_pos` and
`Ideal.inertiaDeg_pos`.
-/

public section

open Module Polynomial

namespace Ideal

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]

/-- If `S` is a finite flat algebra over a domain `R`, at most `rank_R S` primes of `S` lie
over a given prime `p` of `R`. -/
theorem ncard_primesOver_le_finrank (p : Ideal R) [p.IsPrime] :
    (p.primesOver S).ncard ≤ finrank R S := by
  have hfin : (p.primesOver S).Finite := Algebra.QuasiFinite.finite_primesOver p
  let := hfin.fintype
  rw [← sum_ramification_inertia_eq_finrank p S, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have : q.1.IsPrime := q.2.1
  exact Right.one_le_mul (ramificationIdx_pos q.1 R) (inertiaDeg_pos q.1 R)

end Ideal

namespace IsDedekindDomain

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Flat R S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]

/-- Let `S / R` be a finite flat extension of domains, `S` Dedekind, with fraction fields
`L / K`. A nonzero maximal ideal `p` of `R` has at most `[L : K]` prime factors in `S`. When `R`
is a Dedekind domain, flatness follows from torsion-freeness. -/
theorem card_primesOverFinset_le_finrank {p : Ideal R} [p.IsMaximal] (hp : p ≠ ⊥) :
    (primesOverFinset p S).card ≤ finrank K L := by
  rw [← Set.ncard_coe_finset, coe_primesOverFinset hp, IsFractionRing.finrank_eq R K S L]
  exact Ideal.ncard_primesOver_le_finrank p

end IsDedekindDomain

namespace Polynomial

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra (RatFunc k) K]
  [FiniteDimensional (RatFunc k) K] [Algebra.IsSeparable (RatFunc k) K] [Algebra k[X] K]
  [IsScalarTower k[X] (RatFunc k) K]

theorem isMaximal_span_X_sub_C (b : k) : (Ideal.span {X - C b} : Ideal k[X]).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)

theorem span_X_sub_C_ne_bot (b : k) : (Ideal.span {X - C b} : Ideal k[X]) ≠ ⊥ := by
  simpa [Ideal.span_singleton_eq_bot] using X_sub_C_ne_zero b

/-- An extension field `K` of `k(X)` is a faithful `k[X]`-module. -/
instance faithfulSMul_of_ratFunc : FaithfulSMul k[X] K := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq k[X] (RatFunc k) K]
  exact (algebraMap (RatFunc k) K).injective.comp (IsFractionRing.injective k[X] (RatFunc k))

/-- Let `K` be a finite separable extension of `k(X)` and `S` the integral closure of `k[X]`
in `K`. For every `b : k`, at most `[K : k(X)]` primes of `S` lie over `(X - b)`. -/
theorem ncard_primesOver_X_sub_C_le_finrank (S : Type*) [CommRing S] [IsDomain S] [Algebra S K]
    [Algebra k[X] S] [IsScalarTower k[X] S K] [IsIntegralClosure S k[X] K] (b : k) :
    ((Ideal.span {X - C b} : Ideal k[X]).primesOver S).ncard ≤ finrank (RatFunc k) K := by
  have : Module.Finite k[X] S := IsIntegralClosure.finite k[X] (RatFunc k) K S
  have : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K S
  have : IsFractionRing S K :=
    IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) K S
  have : FaithfulSMul k[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    refine Function.Injective.of_comp (f := algebraMap S K) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective k[X] K
  have := isMaximal_span_X_sub_C b
  rw [← IsDedekindDomain.coe_primesOverFinset (span_X_sub_C_ne_bot b), Set.ncard_coe_finset]
  exact IsDedekindDomain.card_primesOverFinset_le_finrank (RatFunc k) K (span_X_sub_C_ne_bot b)

/-- The integral closure of `k[X]` in a finite separable extension of `k(X)` is a Dedekind
domain. -/
instance isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure k[X] K) :=
  integralClosure.isDedekindDomain k[X] (RatFunc k) K

/-- Let `K` be a finite separable extension of `k(X)`. For every `b : k`, at most `[K : k(X)]`
prime factors of `(X - b)` occur in the integral closure of `k[X]` in `K`. -/
theorem card_primesOverFinset_X_sub_C_le_finrank (b : k) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {X - C b} : Ideal k[X])
      (integralClosure k[X] K)).card ≤ finrank (RatFunc k) K := by
  have := isMaximal_span_X_sub_C b
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset (span_X_sub_C_ne_bot b)]
  exact ncard_primesOver_X_sub_C_le_finrank K (integralClosure k[X] K) b

end Polynomial
