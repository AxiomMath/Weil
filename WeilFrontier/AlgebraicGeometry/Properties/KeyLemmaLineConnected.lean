module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Scheme
public import WeilFrontier.RingTheory.Henselian.Henselization.HenselianLineFaithfullyFlat
public import WeilFrontier.RingTheory.Henselian.Henselization.KeyLemmaLineCoordinateRing
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The henselian line over a finite extension is connected and noetherian

Let `A` be an excellent henselian local domain with field of fractions `K`, let `L ⊇ K` be a
finite field extension and let `A{T}` be the henselization of the polynomial ring `A[T]` at the
origin. Then the ring `A{T} ⊗_A L` of global sections of `X_L = Spec (A{T} ⊗_A L)` is a
noetherian integral domain, so `X_L` is a nonempty, connected, noetherian (indeed integral)
scheme.

Write `A_L` for the integral closure of `A` in `L`. By
`MvPolynomial.exists_ringEquiv_tensorProduct_of_isIntegralClosure`,
`A{T} ⊗_A L ≅ A_L{T} ⊗_{A_L} L`, the localization of the noetherian domain `A_L{T}` at the image
of `A ∖ 0`. The maps `A → A_L` and `A_L → A_L{T}` are injective (the second is faithfully
flat), so this image does not contain `0` and the localization is a nonzero noetherian domain.

## Main results

* `isDomain_and_isNoetherianRing_tensorProduct_of_isExcellent` (in the namespace
  `MvPolynomial.IsHenselianPolynomialRing`): `A{T} ⊗_A L` is a noetherian domain.
* `AlgebraicGeometry.isIntegral_henselianLineGeneric`,
  `AlgebraicGeometry.isNoetherian_henselianLineGeneric`: `X_L` is an integral noetherian scheme.
* `AlgebraicGeometry.henselianLineGeneric_nonempty_connectedSpace_isNoetherian`: `X_L` is a
  nonempty connected noetherian scheme.

## Implementation notes

The source takes `A` noetherian (implied by excellence) and one indeterminate `t`; the results
hold for any finite family of indeterminates `σ` (`σ = Fin 1` is the source's case).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open IsLocalRing
open scoped TensorProduct nonZeroDivisors

universe u v w z

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [IsDomain A] [HenselianLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type z} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  {σ : Type v} [Finite σ]
  {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
  [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]

include K in
/-- Auxiliary form of `isDomain_and_isNoetherianRing_tensorProduct_of_isExcellent`, for a given
integral closure `C` of `A` in `L`. -/
private theorem isDomain_and_isNoetherianRing_tensorProduct_aux (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A σ B)
    (C : Type z) [CommRing C] [IsLocalRing C] [Algebra A C] [Algebra C L] [IsScalarTower A C L]
    [IsIntegralClosure C A L] :
    IsDomain (B ⊗[A] L) ∧ IsNoetherianRing (B ⊗[A] L) := by
  classical
  have : IsDomain C := IsIntegralClosure.isDomain A L C
  have : IsNoetherianRing A := hA.1.1
  have : Module.Finite A C := IsIntegralClosure.module_finite_of_isExcellent (K := K) (L := L) hA
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  obtain ⟨B', _, _, _, hB'⟩ := exists_isHenselianPolynomialRing C σ
  let : Algebra C B' :=
    ((algebraMap (LocalizationAtOrigin C σ) B').comp
      (algebraMap C (LocalizationAtOrigin C σ))).toAlgebra
  have : IsScalarTower C (LocalizationAtOrigin C σ) B' :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨⟨e, -⟩, hloc, hdom⟩ :=
    exists_ringEquiv_tensorProduct_of_isIntegralClosure (K := K) (L := L) (C := C) hA hB hB'
  -- the submonoid `A ∖ 0` of `A_L{T}` does not contain `0`
  have hAC : Function.Injective (algebraMap A C) := by
    intro x y hxy
    have h := congrArg (algebraMap C L) hxy
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h
    exact IsFractionRing.injective A K ((algebraMap K L).injective h)
  have hCB' : Function.Injective (algebraMap C B') := hB'.faithfullyFlat_algebraMap.injective
  set M := Algebra.algebraMapSubmonoid B' (Algebra.algebraMapSubmonoid C A⁰)
  have hM : M ≤ B'⁰ := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply nonZeroDivisors.ne_zero ha
    apply hAC
    apply hCB'
    simpa using h0
  have : IsLocalization M (B' ⊗[C] L) := hloc
  have : IsDomain (B' ⊗[C] L) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (B' ⊗[C] L) hM
  have : IsNoetherianRing (LocalizationAtOrigin C σ) :=
    IsLocalization.isNoetherianRing (originIdeal C σ).primeCompl _ inferInstance
  have : IsNoetherianRing B' :=
    isNoetherianRing_of_isHenselization (A := LocalizationAtOrigin C σ)
      (ResidueField (LocalizationAtOrigin C σ))
  have : IsNoetherianRing (B' ⊗[C] L) := IsLocalization.isNoetherianRing M _ inferInstance
  exact ⟨e.toMulEquiv.isDomain _, isNoetherianRing_of_ringEquiv _ e.symm⟩

include K in
/-- `A{T} ⊗_A L` is a noetherian integral domain, for `A` an excellent henselian local domain
with field of fractions `K` and `L` a finite extension of `K`. -/
theorem isDomain_and_isNoetherianRing_tensorProduct_of_isExcellent (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A σ B) :
    IsDomain (B ⊗[A] L) ∧ IsNoetherianRing (B ⊗[A] L) := by
  have : HenselianLocalRing (integralClosure A L) :=
    IsIntegralClosure.henselianLocalRing A L (integralClosure A L)
  exact isDomain_and_isNoetherianRing_tensorProduct_aux (K := K) hA hB (integralClosure A L)

end MvPolynomial.IsHenselianPolynomialRing

namespace AlgebraicGeometry

open MvPolynomial

variable {A : Type u} [CommRing A] [IsDomain A] [HenselianLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type z} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  {σ : Type v} [Finite σ]
  {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
  [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]

include K in
/-- For `A` an excellent henselian local domain with field of fractions `K`, `L` a finite
extension of `K` and `B = A{T}`, the scheme `X_L = Spec (A{T} ⊗_A L)` is integral. -/
theorem isIntegral_henselianLineGeneric (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A σ B) : IsIntegral (henselianLineGeneric A B L) := by
  have := (hB.isDomain_and_isNoetherianRing_tensorProduct_of_isExcellent (K := K) (L := L) hA).1
  infer_instance

include K in
/-- For `A` an excellent henselian local domain with field of fractions `K`, `L` a finite
extension of `K` and `B = A{T}`, the scheme `X_L = Spec (A{T} ⊗_A L)` is noetherian. -/
theorem isNoetherian_henselianLineGeneric (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A σ B) : IsNoetherian (henselianLineGeneric A B L) := by
  have := (hB.isDomain_and_isNoetherianRing_tensorProduct_of_isExcellent (K := K) (L := L) hA).2
  infer_instance

include K in
/-- **The henselian line over a finite extension is connected.** Let `A` be an excellent
henselian noetherian local domain with field of fractions `K`, let `L ⊇ K` be a finite field
extension and let `B = A{t}` be the henselization of `A[t]` at the origin. Then
`X_L = Spec (A{t} ⊗_A L)` is a nonempty connected noetherian scheme. -/
@[weil "lem_fk107_key_lemma_line_connected"]
theorem henselianLineGeneric_nonempty_connectedSpace_isNoetherian (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A σ B) :
    Nonempty (henselianLineGeneric A B L) ∧ ConnectedSpace (henselianLineGeneric A B L) ∧
      IsNoetherian (henselianLineGeneric A B L) := by
  have := isIntegral_henselianLineGeneric (K := K) (L := L) hA hB
  have := isNoetherian_henselianLineGeneric (K := K) (L := L) hA hB
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
