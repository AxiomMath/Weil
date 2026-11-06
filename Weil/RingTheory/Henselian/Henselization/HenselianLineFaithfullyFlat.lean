module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import Weil.RingTheory.Henselian.Henselization.HenselizationFaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization

/-!
# The Henselization of a polynomial ring at the origin is faithfully flat

Let `A` be a local ring, `T = (T_i)_{i ∈ σ}` a family of indeterminates and `A{T}` the
Henselization of `A[T]_{𝔭₀}`, `𝔭₀ = (𝔪(A), T)`. Then `A → A{T}` is faithfully flat: `A[T]` is free
over `A`, `A[T]_{𝔭₀}` is a localization of `A[T]`, and `A[T]_{𝔭₀} → A{T}` is faithfully flat, so
`A → A{T}` is flat; the map `A → A[T]_{𝔭₀}` is a local homomorphism of local rings, hence
faithfully flat, and so is the composite.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.faithfullyFlat`: `A{T}` is a faithfully flat
  `A`-module.
* `MvPolynomial.IsHenselianPolynomialRing.faithfullyFlat_algebraMap`: the ring map `A → A{T}` is
  faithfully flat.

## Implementation notes

The source takes `A` noetherian and a single indeterminate `t`; neither is needed, and the
statement allows any local ring and any index type `σ` (`σ = Fin 1` for `A{t}`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open IsLocalRing

universe u v w

namespace MvPolynomial

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type v}

/-- The map `A → A[T]_{𝔭₀}` is a local homomorphism. -/
instance isLocalHom_algebraMap_localizationAtOrigin :
    IsLocalHom (algebraMap A (LocalizationAtOrigin A σ)) := by
  refine ⟨fun a ha => ?_⟩
  rw [IsScalarTower.algebraMap_apply A (MvPolynomial σ A) (LocalizationAtOrigin A σ),
    IsLocalization.AtPrime.isUnit_to_map_iff (LocalizationAtOrigin A σ) (originIdeal A σ)] at ha
  by_contra hu
  refine ha (show algebraMap A (MvPolynomial σ A) a ∈ originIdeal A σ from ?_)
  rw [mem_originIdeal, algebraMap_eq, constantCoeff_C]
  exact (mem_maximalIdeal a).2 hu

/-- `A[T]_{𝔭₀}` is a faithfully flat `A`-module. -/
instance faithfullyFlat_localizationAtOrigin :
    Module.FaithfullyFlat A (LocalizationAtOrigin A σ) := by
  have : Module.Flat A (LocalizationAtOrigin A σ) :=
    Module.Flat.trans A (MvPolynomial σ A) (LocalizationAtOrigin A σ)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

namespace IsHenselianPolynomialRing

variable {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
  [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]

/-- `A{T}` is a faithfully flat `A`-module. -/
theorem faithfullyFlat (h : IsHenselianPolynomialRing A σ B) : Module.FaithfullyFlat A B := by
  obtain ⟨ψ, hψ⟩ := isHenselianPolynomialRing_iff_exists_isHenselizationAlong.1 h
  have : Module.FaithfullyFlat (LocalizationAtOrigin A σ) B :=
    RingHom.faithfullyFlat_algebraMap_iff.1 hψ.faithfullyFlat_algebraMap
  exact Module.FaithfullyFlat.trans A (LocalizationAtOrigin A σ) B

/-- **`A → A{T}` is faithfully flat.** For a local ring `A` and the Henselization `A{T}` of the
polynomial ring `A[T]` at the origin, the ring map `A → A{T}` is faithfully flat. -/
@[weil "lem_fk107_henselian_line_faithfully_flat"]
theorem faithfullyFlat_algebraMap (h : IsHenselianPolynomialRing A σ B) :
    (algebraMap A B).FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.2 h.faithfullyFlat

end IsHenselianPolynomialRing

end MvPolynomial
