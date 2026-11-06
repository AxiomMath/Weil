module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import StacksFrontier.RingTheory.Henselian.NormalDomainOfHenselization
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The Henselization of a polynomial ring over a normal domain is normal

Let `A` be a local domain, integrally closed in its field of fractions, and `T = (T_i)_{i ∈ σ}` a
finite family of indeterminates. The polynomial ring `A[T]` is an integrally closed domain, hence
so is its localization `A[T]_{𝔭₀}` at the origin `𝔭₀ = (𝔪, T)`, a normal local domain. Being a
normal domain is invariant under henselization (Stacks 06DI), so the Henselization `A{T}` of
`A[T]_{𝔭₀}` is again an integrally closed domain.

## Main results

* `MvPolynomial.isIntegrallyClosed_of_finite`: a polynomial ring in finitely many variables over
  an integrally closed domain is integrally closed.
* `MvPolynomial.IsHenselianPolynomialRing.isDomain_and_isIntegrallyClosed`: `A{T}` is an
  integrally closed domain when `A` is a normal local domain and `σ` is finite.

## Implementation notes

The source assumes `A` henselian and noetherian and treats one indeterminate; neither hypothesis
is used, and any finite family of indeterminates is allowed. The source argues through the
completion, or through the filtered colimit of local-étale algebras; here the permanence of
normality under henselization, Stacks 06DI, is applied to the normal local domain
`A[T]_{𝔭₀}` directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace MvPolynomial

/-- A polynomial ring in finitely many variables over an integrally closed domain is integrally
closed. -/
theorem isIntegrallyClosed_of_finite (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (σ : Type v) [Finite σ] : IsIntegrallyClosed (MvPolynomial σ R) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  suffices IsIntegrallyClosed (MvPolynomial (Fin n) R) from
    IsIntegrallyClosed.of_equiv (renameEquiv R e).symm.toRingEquiv
  clear e
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih =>
    have := ih
    have : IsDomain (MvPolynomial (Fin n) R) := NoZeroDivisors.to_isDomain _
    exact IsIntegrallyClosed.of_equiv (finSuccEquiv R n).symm.toRingEquiv

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type v}

/-- The localization `A[T]_{𝔭₀}` of a polynomial ring in finitely many variables over a normal
local domain is integrally closed. -/
theorem isIntegrallyClosed_localizationAtOrigin [IsDomain A] [IsIntegrallyClosed A] [Finite σ] :
    IsIntegrallyClosed (LocalizationAtOrigin A σ) := by
  have := isIntegrallyClosed_of_finite A σ
  exact isIntegrallyClosed_of_isLocalization _ (originIdeal A σ).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

/-- **The Henselization of a polynomial ring over a normal local domain is normal.** Let `A` be a
local domain, integrally closed in its field of fractions, and `T` a finite family of
indeterminates. Then the Henselization `A{T}` of `A[T]` at the origin is an integral domain
integrally closed in its field of fractions. -/
@[weil "lem_fk107_henselian_line_normal"]
theorem IsHenselianPolynomialRing.isDomain_and_isIntegrallyClosed [IsDomain A]
    [IsIntegrallyClosed A] [Finite σ] {B : Type w} [CommRing B] [IsLocalRing B]
    [Algebra (LocalizationAtOrigin A σ) B] (h : IsHenselianPolynomialRing A σ B) :
    IsDomain B ∧ IsIntegrallyClosed B := by
  have := isIntegrallyClosed_localizationAtOrigin (A := A) (σ := σ)
  have : IsHenselization (LocalizationAtOrigin A σ)
    (ResidueField (LocalizationAtOrigin A σ)) B := h
  exact StacksDraft.isDomain_and_isIntegrallyClosed_of_isHenselization
    (R := LocalizationAtOrigin A σ)

end MvPolynomial
