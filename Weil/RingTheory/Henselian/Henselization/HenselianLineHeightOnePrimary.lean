module

public import Weil.Attr
public import Weil.RingTheory.Henselian.Henselization.HenselianLineDomain
public import Weil.RingTheory.Henselian.Henselization.HenselianLinePrimaryExtension
public import StacksFrontier.RingTheory.UniqueFactorizationDomain.HeightOneOrders
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Primary ideals of `A{T}` over a height-one prime

Let `A` be a normal henselian noetherian local domain, `𝔭 ⊂ A` a prime ideal of height one,
`T = (T_i)_{i ∈ σ}` a finite family of indeterminates and `B = A{T}` the Henselization of `A[T]`
at the origin (`MvPolynomial.IsHenselianPolynomialRing`). Every `𝔭 B`-primary ideal `I` of `B` is
of the form `𝔮 B` for a `𝔭`-primary ideal `𝔮` of `A`.

The ideal `P = 𝔭 B` is prime and lies over `𝔭`, `A → B` being faithfully flat. The localization
`A_𝔭` is a discrete valuation ring, so its maximal ideal is principal, and hence so is the maximal
ideal `𝔭 B_P` of the noetherian local domain `B_P`. Thus `I B_P = (P B_P)^m` for some `m ≥ 1`.
The contraction `𝔮` of `(𝔭 A_𝔭)^m` to `A` is `𝔭`-primary, `𝔮 B` is `P`-primary, and
`𝔮 B_P = (𝔭 A_𝔭)^m B_P = I B_P`. A `P`-primary ideal is the contraction of its extension to
`B_P`, so `I = 𝔮 B`.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.exists_isPrimary_eq_map_of_isPrimary`: a primary ideal
  of `A{T}` with radical `𝔭 A{T}`, `𝔭` of height one, is `𝔮 A{T}` for a `𝔭`-primary `𝔮`.

## Implementation notes

The source treats one indeterminate `t` (the case `σ = Fin 1`); any finite family is allowed
here. "`I` is `𝔭 A{T}`-primary" is the conjunction of `I.IsPrimary` and
`I.radical = 𝔭 A{T}`, and likewise for `𝔮`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open IsLocalRing

universe u v w

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] {σ : Type v}
  [Finite σ] {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
  [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]

/-- **Primary ideals of `A{T}` over a height-one prime.** Let `A` be a normal henselian
noetherian local domain, `𝔭 ⊂ A` a prime ideal of height one and `B = A{T}` the Henselization of
`A[T]` at the origin, `T` a finite family of indeterminates. Every `𝔭 B`-primary ideal `I` of `B`
equals `𝔮 B` for some `𝔭`-primary ideal `𝔮` of `A`. -/
@[weil "lem_fk107_henselian_line_height_one_primary"]
theorem exists_isPrimary_eq_map_of_isPrimary [IsDomain A] [IsIntegrallyClosed A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1) (hB : IsHenselianPolynomialRing A σ B)
    {I : Ideal B} (hI : I.IsPrimary) (hIr : I.radical = 𝔭.map (algebraMap A B)) :
    ∃ 𝔮 : Ideal A, 𝔮.IsPrimary ∧ 𝔮.radical = 𝔭 ∧ I = 𝔮.map (algebraMap A B) := by
  set P := 𝔭.map (algebraMap A B)
  have hP : P.IsPrime := isPrime_map 𝔭 hB
  have : IsDomain B := isDomain hB
  have : IsHenselization (LocalizationAtOrigin A σ)
    (ResidueField (LocalizationAtOrigin A σ)) B := hB
  have : IsNoetherianRing B :=
    isNoetherianRing_of_isHenselization (A := LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ))
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  have hcomap : P.comap (algebraMap A B) = 𝔭 := Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
  -- `𝔭 ≠ ⊥`, hence `P ≠ ⊥`
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at h𝔭
    exact zero_ne_one h𝔭
  have hPne : P ≠ ⊥ := fun h => h𝔭ne
    ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).1 h)
  -- the localizations `A_𝔭` and `B_P`
  let Ap := Localization.AtPrime 𝔭
  let BP := Localization.AtPrime P
  have : IsDiscreteValuationRing Ap :=
    Stacks.RingTheory.HeightOneOrders.isDiscreteValuationRing_of_height_eq_one 𝔭 h𝔭 Ap
  let φ : Ap →+* BP := Localization.localRingHom 𝔭 P (algebraMap A B) hcomap.symm
  have hφ : φ.comp (algebraMap A Ap) = (algebraMap B BP).comp (algebraMap A B) :=
    RingHom.ext fun a => Localization.localRingHom_to_map _ _ _ hcomap.symm a
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Ap)).principal
  have hmaxBP : maximalIdeal BP = (maximalIdeal Ap).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 Ap, Ideal.map_map, hφ, ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hprinc : (maximalIdeal BP).IsPrincipal := by
    rw [hmaxBP, hπ, Ideal.map_span, Set.image_singleton]
    exact ⟨⟨_, rfl⟩⟩
  have hBPinj : Function.Injective (algebraMap B BP) :=
    IsLocalization.injective BP P.primeCompl_le_nonZeroDivisors
  have hmaxne : maximalIdeal BP ≠ ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P BP]
    exact fun h => hPne ((Ideal.map_eq_bot_iff_of_injective hBPinj).1 h)
  have hBPnf : ¬IsField BP := fun h => hmaxne (isField_iff_maximalIdeal_eq.1 h)
  -- `I B_P` is a power of the maximal ideal
  have hIle : I ≤ P := hIr ▸ Ideal.le_radical
  have hIne : I.map (algebraMap B BP) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hBPinj]
    rintro rfl
    apply hPne
    rw [← hIr, Ideal.radical_bot_of_isReduced]
  have hpow : ∀ J : Ideal BP, J ≠ ⊥ → ∃ n : ℕ, J = maximalIdeal BP ^ n :=
    ((IsDiscreteValuationRing.TFAE BP hBPnf).out 5 7).1 hprinc
  obtain ⟨m, hm⟩ := hpow _ hIne
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top] at hm
    have : I.map (algebraMap B BP) ≤ maximalIdeal BP := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P BP]
      exact Ideal.map_mono hIle
    exact (maximalIdeal.isMaximal BP).ne_top (top_le_iff.1 (hm ▸ this))
  -- the `𝔭`-primary ideal `𝔮`
  set 𝔮 := (maximalIdeal Ap ^ m).comap (algebraMap A Ap)
  have hrad : (maximalIdeal Ap ^ m).radical = maximalIdeal Ap := by
    rw [Ideal.radical_pow _ hm0, (maximalIdeal.isMaximal Ap).isPrime.radical]
  have hJ : (maximalIdeal Ap ^ m).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact maximalIdeal.isMaximal Ap)
  have h𝔮 : 𝔮.IsPrimary := hJ.comap _
  have h𝔮r : 𝔮.radical = 𝔭 := by
    rw [← Ideal.comap_radical, hrad]
    exact IsLocalization.AtPrime.under_maximalIdeal Ap 𝔭
  have h𝔮map : 𝔮.map (algebraMap A Ap) = maximalIdeal Ap ^ m :=
    IsLocalization.map_under 𝔭.primeCompl Ap _
  have hqB : (𝔮.map (algebraMap A B)).IsPrimary := isPrimary_map h𝔮 hB
  have hqBr : (𝔮.map (algebraMap A B)).radical = P := by
    rw [radical_map_eq_of_isPrimary h𝔮 hB, h𝔮r]
  have key : (𝔮.map (algebraMap A B)).map (algebraMap B BP) = I.map (algebraMap B BP) := by
    rw [Ideal.map_map, ← hφ, ← Ideal.map_map, h𝔮map, Ideal.map_pow, ← hmaxBP, hm]
  -- a `P`-primary ideal is saturated with respect to `B → B_P`
  have hdisj : ∀ {J : Ideal B}, J.radical = P → Disjoint (P.primeCompl : Set B) J :=
    fun {J} hJr => Set.disjoint_left.2 fun x hx hxJ => hx (hJr ▸ Ideal.le_radical hxJ)
  refine ⟨𝔮, h𝔮, h𝔮r, ?_⟩
  rw [← IsLocalization.under_map_of_isPrimary_disjoint P.primeCompl BP hI (hdisj hIr),
    ← IsLocalization.under_map_of_isPrimary_disjoint P.primeCompl BP hqB (hdisj hqBr), key]

end MvPolynomial.IsHenselianPolynomialRing
