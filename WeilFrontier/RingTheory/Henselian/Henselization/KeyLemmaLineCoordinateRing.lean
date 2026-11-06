module

public import Weil.Attr
public import WeilFrontier.RingTheory.Henselian.Henselization.HenselianLineBaseChangeFinite
public import WeilFrontier.RingTheory.Henselian.Henselization.HenselianLineDomain
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.RingTheory.Nagata.Shrink
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The generic fibre of the henselian line over a finite extension

Let `A` be an excellent henselian local domain with field of fractions `K`, let `L ⊇ K` be a
finite field extension and let `A_L` be the integral closure of `A` in `L`. Write `A{T}` for the
henselization of the polynomial ring `A[T]` at the origin `(𝔪, T)`
(`MvPolynomial.IsHenselianPolynomialRing`). Then
`A{T} ⊗_A L ≅ A_L{T} ⊗_{A_L} L` as `L[T]`-algebras, and this ring is the localization of the
integral domain `A_L{T}` at the nonzero elements of `A`.

Since `A` is excellent, it is a Nagata ring, so `A_L` is finite over `A`; being a domain integral
over the henselian local ring `A`, it is a henselian local ring, and it is noetherian. Every
element of `L` is the quotient of an element of `A_L` by a nonzero element of `A`, so
`L = (A ∖ 0)⁻¹ A_L`. The finite base change of the henselian polynomial ring gives
`A{T} ⊗_A A_L ≅ A_L{T}`, whence
`A{T} ⊗_A L ≅ (A{T} ⊗_A A_L) ⊗_{A_L} L ≅ A_L{T} ⊗_{A_L} L = (A ∖ 0)⁻¹ A_L{T}`, and `A_L{T}` is a
domain as the henselization of a polynomial ring over a henselian noetherian local domain.

## Main results

* `IsIntegralClosure.module_finite_of_isExcellent`: the integral closure of an excellent domain in
  a finite extension of its field of fractions is finite over it.
* `IsIntegralClosure.henselianLocalRing`: the integral closure of a henselian local domain in a
  field is a henselian local ring.
* `MvPolynomial.exists_ringEquiv_tensorProduct_of_isIntegralClosure`:
  `A{T} ⊗_A L ≅ A_L{T} ⊗_{A_L} L` as `L[T]`-algebras, this ring is the localization of
  `A_L{T}` at the image of `A ∖ 0`, and `A_L{T}` is a domain.

## Implementation notes

The source takes `A` noetherian (implied by excellence) and one indeterminate `t`; the statement
holds for any finite family of indeterminates (`σ = Fin 1` is the source's case). The integral
closure `A_L` is any `IsIntegralClosure C A L`; its local ring structure, needed to speak of
`C[T]_{(𝔪_C, T)}`, is an instance argument, supplied by `IsIntegralClosure.henselianLocalRing`.
The `L[T]`-algebra structures on both tensor products are the maps sending `l ∈ L` to `1 ⊗ l` and
`T_i` to `T_i ⊗ 1`; that the isomorphism is one of `L[T]`-algebras is its compatibility with these
maps.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
-/

public section

open IsLocalRing
open scoped TensorProduct nonZeroDivisors

universe u u' v w w' z

namespace IsIntegralClosure

variable {A : Type u} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K] {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  {C : Type*} [CommRing C] [Algebra A C] [Algebra C L] [IsScalarTower A C L]
  [IsIntegralClosure C A L]

include K in
/-- The integral closure of an excellent domain `A` in a finite extension `L` of its field of
fractions is a finite `A`-module. -/
theorem module_finite_of_isExcellent [FiniteDimensional K L] (hA : IsExcellent A) :
    Module.Finite A C := by
  have hJ : IsJapaneseRing A :=
    MonogenicN1.isJapaneseRing_of_isNagataRing (isNagataRing_of_isQuasiExcellent hA.1)
  have : Module.Finite A (integralClosure A L) :=
    module_finite_integralClosure_of_isJapaneseRing hJ K L
  exact Module.Finite.equiv (IsIntegralClosure.equiv A (integralClosure A L) L C).toLinearEquiv

omit [IsDomain A] in
variable (A L C) in
include A L in
/-- The integral closure of a domain in a field is a domain. -/
theorem isDomain : IsDomain C :=
  (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)

omit [IsDomain A] in
variable (A L C) in
include L in
/-- The integral closure of a henselian local domain `A` in a field `L` is a henselian local
ring. -/
theorem henselianLocalRing [HenselianLocalRing A] : HenselianLocalRing C := by
  have : IsDomain C := isDomain A L C
  exact (RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain (algebraMap A C)
    (IsIntegralClosure.isIntegral_algebra A L (A := C)).isIntegral).1

end IsIntegralClosure

namespace MvPolynomial

variable {A : Type u} [CommRing A] [IsDomain A] [HenselianLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type z} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  {C : Type u'} [CommRing C] [IsLocalRing C] [Algebra A C] [Algebra C L] [IsScalarTower A C L]
  [IsIntegralClosure C A L] {σ : Type v} [Finite σ]

include K in
/-- **The generic fibre of the henselian line over a finite extension.** Let `A` be an excellent
henselian local domain with field of fractions `K`, `L` a finite extension of `K`, `C = A_L` the
integral closure of `A` in `L`, and `B = A{T}`, `B' = A_L{T}` the henselizations of the polynomial
rings at the origin. Then there is a ring isomorphism `e : B ⊗_A L ≃ B' ⊗_{A_L} L` of
`L[T]`-algebras (it carries the image of `p ∈ L[T]` under `l ↦ 1 ⊗ l`, `T_i ↦ T_i ⊗ 1` to the image
of `p`); the ring `B' ⊗_{A_L} L` is the localization of `B'` at the image of the nonzero elements
of `A`; and `B'` is an integral domain. -/
@[weil "lem_fk107_key_lemma_line_coordinate_ring"]
theorem exists_ringEquiv_tensorProduct_of_isIntegralClosure (hA : IsExcellent A)
    {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
    [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]
    (hB : IsHenselianPolynomialRing A σ B)
    {B' : Type w'} [CommRing B'] [IsLocalRing B'] [Algebra (LocalizationAtOrigin C σ) B']
    [Algebra C B'] [IsScalarTower C (LocalizationAtOrigin C σ) B']
    (hB' : IsHenselianPolynomialRing C σ B') :
    (∃ e : B ⊗[A] L ≃+* B' ⊗[C] L, ∀ p : MvPolynomial σ L,
      e (eval₂Hom (Algebra.TensorProduct.includeRight : L →ₐ[A] B ⊗[A] L).toRingHom
        (fun i => algebraMap (LocalizationAtOrigin A σ) B
          (algebraMap _ _ (X i : MvPolynomial σ A)) ⊗ₜ 1) p) =
        eval₂Hom (Algebra.TensorProduct.includeRight : L →ₐ[C] B' ⊗[C] L).toRingHom
          (fun i => algebraMap (LocalizationAtOrigin C σ) B'
            (algebraMap _ _ (X i : MvPolynomial σ C)) ⊗ₜ 1) p) ∧
    IsLocalization (Algebra.algebraMapSubmonoid B' (Algebra.algebraMapSubmonoid C A⁰))
      (B' ⊗[C] L) ∧
    IsDomain B' := by
  classical
  have : Module.Finite A C := IsIntegralClosure.module_finite_of_isExcellent (K := K) (L := L) hA
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorProduct_of_isHenselianPolynomialRing hB hB'
  -- `e` as an isomorphism of `C`-algebras `C ⊗_A B ≃ B'`
  let e₁ : C ⊗[A] B ≃+* B' := (Algebra.TensorProduct.comm A C B).toRingEquiv.trans e
  have he₁ (c : C) : e₁ (algebraMap C (C ⊗[A] B) c) = algebraMap C B' c := by
    have := he (MvPolynomial.C c)
    rw [eval₂Hom_C] at this
    change e (1 ⊗ₜ c) = _
    refine this.trans ?_
    rw [IsScalarTower.algebraMap_apply C (LocalizationAtOrigin C σ) B',
      IsScalarTower.algebraMap_apply C (MvPolynomial σ C) (LocalizationAtOrigin C σ),
      MvPolynomial.algebraMap_eq]
  let e' : C ⊗[A] B ≃ₐ[C] B' := AlgEquiv.ofRingEquiv (f := e₁) he₁
  let Φ : B ⊗[A] L ≃+* B' ⊗[C] L :=
    (Algebra.TensorProduct.comm A B L).toRingEquiv.trans <|
      (Algebra.TensorProduct.cancelBaseChange A C C L B).symm.toRingEquiv.trans <|
        (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[C] L) e').toRingEquiv.trans
          (Algebra.TensorProduct.comm C L B').toRingEquiv
  refine ⟨⟨Φ, fun p => ?_⟩, ?_, ?_⟩
  · induction p using MvPolynomial.induction_on with
    | C l => simp [Φ, ← Algebra.TensorProduct.one_def]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      have hX := he (X i)
      rw [eval₂Hom_X'] at hX
      simp only [map_mul, hp, eval₂Hom_X']
      congr 1
      simp [Φ, e', e₁, hX]
  · have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
      IsIntegralClosure.isLocalization A K L C
    infer_instance
  · have : IsDomain C := IsIntegralClosure.isDomain A L C
    have : HenselianLocalRing C := IsIntegralClosure.henselianLocalRing A L C
    have : IsNoetherianRing A := hA.1.1
    have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
    exact hB'.isDomain

end MvPolynomial
