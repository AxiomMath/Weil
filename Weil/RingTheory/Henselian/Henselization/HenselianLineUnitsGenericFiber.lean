module

public import Weil.Attr
public import Weil.RingTheory.Henselian.Henselization.HenselianLineExtendedPrimeIsPrime
public import Weil.RingTheory.Henselian.Henselization.HenselianLineFaithfullyFlat
public import Weil.RingTheory.Henselian.Henselization.HenselianLineDomain
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.AffineDescent
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Units on the generic fibre of the henselian polynomial ring

Let `A` be a normal henselian noetherian local domain with fraction field `κ`, `T` a finite
family of indeterminates and `A{T}` the Henselization of `A[T]` at the origin
(`MvPolynomial.IsHenselianPolynomialRing`). Every unit of the generic fibre
`A{T} ⊗_A κ` is the product of a unit of `A{T}` and a nonzero element of `κ`.

The generic fibre is the localization of `A{T}` at the nonzero elements of `A`. A unit `s` of it
is a fraction `x / r` with `x ∈ A{T}`, `0 ≠ r ∈ A`, whose inverse is a fraction `x' / r'` of the
same shape, so that `x x' = r r'`. The extension `A → A{T}` is faithfully flat, `A{T}` is a
noetherian domain, and the extension `𝔭 A{T}` of every prime `𝔭` of `A` is prime. In this
situation the intersection of symbolic powers of the minimal primes of `A` over `r r'` with
exponents the valuations of `x` along their extensions is an invertible, hence principal, ideal
`(g)` of the local ring `A`, and `x = ε g` with `ε` a unit of `A{T}` (the affine step of Stacks
0BD7). Then `s = ε · (g / r)`.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.exists_eq_algebraMap_units_mul_algebraMap_units`: for
  any localization `L` of `A{T}` at the nonzero elements of `A` and any fraction field `K` of `A`
  mapping compatibly to `L`, every unit of `L` is `ε c` with `ε ∈ A{T}ˣ` and `c ∈ Kˣ`.
* `MvPolynomial.IsHenselianPolynomialRing.exists_eq_tmul_of_units_tensorProduct`: the same for
  `L = A{T} ⊗_A K`, where it reads `u = ε ⊗ c`.

## Implementation notes

The source works with one indeterminate `t`; any finite family is allowed here. The source's
proof descends the divisorial ideal `f A{T}` to a divisorial ideal of `A` and shows it is
principal by faithfully flat descent of a free module of rank one; here the descended ideal is
the intersection of symbolic powers above, and its principality comes from its invertibility
over the local ring `A`. The henselian polynomial ring is taken in the universe of `A`, as the
descent lemma requires both rings in one universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [StacksProject 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

public section

open IsLocalRing TensorProduct

universe u v

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [HenselianLocalRing A] {σ : Type v} [Finite σ] {B : Type u} [CommRing B] [IsLocalRing B]
  [Algebra (LocalizationAtOrigin A σ) B] [Algebra A B]
  [IsScalarTower A (LocalizationAtOrigin A σ) B]

/-- A unit `s` of the localization `L` of a domain `B` at the nonzero elements of a subdomain `A`
is a fraction `x / r`, its inverse is a fraction `x' / r'`, and `x x' = r r'`. -/
private theorem exists_mul_eq_algebraMap_of_isUnit {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    {L : Type*} [CommRing L] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L] (s : Lˣ) :
    ∃ (x x' : B) (r r' : A), r ≠ 0 ∧ r' ≠ 0 ∧ x * x' = algebraMap A B (r * r') ∧
      algebraMap B L x = algebraMap A L r * s := by
  obtain ⟨⟨x, m, hm⟩, h1⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (s : L)
  obtain ⟨⟨x', m', hm'⟩, h2⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (↑s⁻¹ : L)
  obtain ⟨r, hr, rfl⟩ := hm
  obtain ⟨r', hr', rfl⟩ := hm'
  refine ⟨x, x', r, r', nonZeroDivisors.ne_zero hr, nonZeroDivisors.ne_zero hr', ?_, ?_⟩
  · have hle : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
      rintro y ⟨t, ht, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero fun hc => (nonZeroDivisors.ne_zero ht)
        (FaithfulSMul.algebraMap_injective A B (by simpa using hc))
    refine IsLocalization.injective L hle ?_
    have hprod : ((s : L) * ↑s⁻¹) * (algebraMap B L (algebraMap A B r) *
        algebraMap B L (algebraMap A B r')) = algebraMap B L x * algebraMap B L x' := by
      rw [← h1, ← h2]; ring
    rw [Units.mul_inv, one_mul] at hprod
    simp only [map_mul]
    exact hprod.symm
  · rw [← h1, ← IsScalarTower.algebraMap_apply]
    ring

/-- The key factorization: if `x x' = r r'` in `A{T}` with `x x' ≠ 0`, then `x = ε g` with `ε` a
unit of `A{T}` and `g ∈ A`. -/
private theorem exists_isUnit_mul_algebraMap_of_mul_eq (hB : IsHenselianPolynomialRing A σ B)
    {x x' : B} {f : A} (hf : f ≠ 0) (hxx' : x * x' = algebraMap A B f) :
    ∃ (g : A) (ε : B), IsUnit ε ∧ x = ε * algebraMap A B g := by
  have : IsDomain B := isDomain hB
  have : IsHenselization (LocalizationAtOrigin A σ)
    (ResidueField (LocalizationAtOrigin A σ)) B := hB
  have : IsNoetherianRing B :=
    isNoetherianRing_of_isHenselization (A := LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ))
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  have hfB : algebraMap A B f ≠ 0 := fun h =>
    hf (FaithfulSMul.algebraMap_injective A B (by simpa using h))
  have hx : x ≠ 0 := by rintro rfl; exact hfB (by simpa using hxx'.symm)
  have hx' : x' ≠ 0 := by rintro rfl; exact hfB (by simpa using hxx'.symm)
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {f})
  let ι := {q : Ideal A // q ∈ (Ideal.span {f}).minimalPrimes}
  have : Fintype ι := hfin.fintype
  let p : ι → Ideal A := fun i => i.1
  have hprime : ∀ i, (p i).IsPrime := fun i => i.2.1.1
  have hprime' : ∀ i, ((p i).map (algebraMap A B)).IsPrime := fun i =>
    have := hprime i
    isPrime_map (p i) hB
  obtain ⟨-, g, ε, hε, -, hxg⟩ := Ideal.exists_isUnit_mul_of_mul_eq_algebraMap (A := B)
    (Finset.univ : Finset ι) p hf hx hx' (fun i _ => i.2)
    (fun q hq => ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩) hxx'
  exact ⟨g, ε, hε, hxg⟩

/-- **Units on the generic fibre of the henselian line.** Let `A` be a normal henselian noetherian
local domain with fraction field `K`, `T` a finite family of indeterminates and `B = A{T}` the
Henselization of `A[T]` at the origin. Let `L` be the localization of `B` at the nonzero elements
of `A` (the generic fibre `B ⊗_A K`), with compatible maps `B → L` and `K → L`. Then every unit
of `L` is the product of (the image of) a unit of `B` and (the image of) a nonzero element
of `K`. -/
@[weil "lem_fk107_henselian_line_units_generic_fiber"]
theorem exists_eq_algebraMap_units_mul_algebraMap_units (hB : IsHenselianPolynomialRing A σ B)
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [CommRing L] [Algebra B L] [Algebra A L] [IsScalarTower A B L] [Algebra K L]
    [IsScalarTower A K L] [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    (s : Lˣ) :
    ∃ (ε : Bˣ) (c : Kˣ), (s : L) = algebraMap B L ε * algebraMap K L c := by
  have : IsDomain B := isDomain hB
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  obtain ⟨x, x', r, r', hr, hr', hxx', hxs⟩ :=
    exists_mul_eq_algebraMap_of_isUnit (A := A) (B := B) (L := L) s
  obtain ⟨g, ε, hε, hxg⟩ :=
    exists_isUnit_mul_algebraMap_of_mul_eq hB (mul_ne_zero hr hr') hxx'
  have hfB : algebraMap A B (r * r') ≠ 0 := fun h =>
    mul_ne_zero hr hr' (FaithfulSMul.algebraMap_injective A B (by simpa using h))
  have hg : g ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hxg
    rw [hxg, zero_mul] at hxx'
    exact hfB hxx'.symm
  have hgK : algebraMap A K g ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hg
  have hrK : algebraMap A K r ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hr
  refine ⟨hε.unit, Units.mk0 (algebraMap A K g / algebraMap A K r) (div_ne_zero hgK hrK), ?_⟩
  -- `r` is a unit of `L`
  have hrL : IsUnit (algebraMap A L r) := by
    rw [IsScalarTower.algebraMap_apply A B L]
    exact IsLocalization.map_units L
      (⟨algebraMap A B r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩ :
        Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
  have hc : algebraMap K L (algebraMap A K g / algebraMap A K r) * algebraMap A L r =
      algebraMap A L g := by
    rw [IsScalarTower.algebraMap_apply A K L r, ← map_mul, div_mul_cancel₀ _ hrK,
      ← IsScalarTower.algebraMap_apply]
  refine hrL.mul_left_cancel ?_
  simp only [IsUnit.unit_spec, Units.val_mk0]
  calc algebraMap A L r * s = algebraMap B L x := hxs.symm
    _ = algebraMap B L ε * algebraMap A L g := by
        rw [hxg, map_mul, ← IsScalarTower.algebraMap_apply]
    _ = _ := by rw [← hc]; ring

/-- **Units on the generic fibre of the henselian line, tensor form.** Let `A` be a normal
henselian noetherian local domain with fraction field `K`, `T` a finite family of indeterminates
and `B = A{T}` the Henselization of `A[T]` at the origin. Every unit of `B ⊗_A K` is `ε ⊗ c` with
`ε` a unit of `B` and `c` a nonzero element of `K`. -/
@[weil "lem_fk107_henselian_line_units_generic_fiber"]
theorem exists_eq_tmul_of_units_tensorProduct (hB : IsHenselianPolynomialRing A σ B)
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (s : (B ⊗[A] K)ˣ) :
    ∃ (ε : Bˣ) (c : Kˣ), (s : B ⊗[A] K) = (ε : B) ⊗ₜ[A] (c : K) := by
  let : Algebra K (B ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A K (B ⊗[A] K) := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A B a ⊗ₜ[A] (1 : K) = (1 : B) ⊗ₜ[A] algebraMap A K a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (B ⊗[A] K) :=
    IsLocalization.tensor K (nonZeroDivisors A)
  obtain ⟨ε, c, h⟩ := exists_eq_algebraMap_units_mul_algebraMap_units hB K (L := B ⊗[A] K) s
  refine ⟨ε, c, h.trans ?_⟩
  change ((ε : B) ⊗ₜ[A] (1 : K)) * ((1 : B) ⊗ₜ[A] (c : K)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end MvPolynomial.IsHenselianPolynomialRing
