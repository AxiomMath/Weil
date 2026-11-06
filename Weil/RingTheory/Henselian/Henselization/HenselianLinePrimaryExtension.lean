module

public import Weil.Attr
public import Weil.RingTheory.Henselian.Henselization.HenselianLineExtendedPrimeIsPrime
public import Weil.RingTheory.Henselian.Henselization.HenselianLineFaithfullyFlat
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Extending a primary ideal of the base to the henselian polynomial ring

Let `A` be a henselian noetherian local ring, `T = (T_i)_{i ∈ σ}` a finite family of
indeterminates and `A{T}` the Henselization of `A[T]` at the origin
(`MvPolynomial.IsHenselianPolynomialRing`). If `𝔮 ⊂ A` is a `𝔭`-primary ideal, then `𝔮 A{T}` is
a `𝔭 A{T}`-primary ideal of `A{T}`.

The radical is computed from `𝔭ⁿ ⊆ 𝔮 ⊆ 𝔭` and the primality of `𝔭 A{T}`. For primality, an
element `y ∉ 𝔭 A{T}` that is a zero divisor on `A{T} ⧸ 𝔮 A{T} ≅ A{T} ⊗_A (A ⧸ 𝔮)` lies in an
associated prime of this module, `A{T}` being noetherian. Since `A → A{T}` is flat, the
associated primes of `A{T} ⊗_A (A ⧸ 𝔮)` are those of `A{T} ⧸ 𝔭 A{T}`, the only associated prime
of `A ⧸ 𝔮` being `𝔭` (Stacks 0312), and `A{T} ⧸ 𝔭 A{T}` is a domain whose only associated prime
is `𝔭 A{T}`, which does not contain `y`.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.radical_map_eq_of_isPrimary`:
  `√(𝔮 A{T}) = (√𝔮) A{T}` for a primary ideal `𝔮` of `A`.
* `MvPolynomial.IsHenselianPolynomialRing.isPrimary_map`: `𝔮 A{T}` is primary.

## Implementation notes

The source treats one indeterminate `t` (the case `σ = Fin 1`); any finite family is allowed
here. The prime `𝔭` of the source is `√𝔮`, so "`𝔮 A{T}` is `𝔭 A{T}`-primary" is the conjunction
of the two main results.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [StacksProject 0312](https://stacks.math.columbia.edu/tag/0312)
-/

public section

open IsLocalRing TensorProduct

universe u v w

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] {σ : Type v}
  [Finite σ] {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
  [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]

/-- **Radical of an extended primary ideal.** Let `A` be a henselian noetherian local ring,
`𝔮 ⊂ A` a primary ideal and `B = A{T}` the Henselization of `A[T]` at the origin, `T` a finite
family of indeterminates. Then the radical of `𝔮 B` is `(√𝔮) B`. -/
@[weil "lem_fk107_henselian_line_primary_extension"]
theorem radical_map_eq_of_isPrimary {𝔮 : Ideal A} (h𝔮 : 𝔮.IsPrimary)
    (hB : IsHenselianPolynomialRing A σ B) :
    (𝔮.map (algebraMap A B)).radical = 𝔮.radical.map (algebraMap A B) := by
  have : 𝔮.radical.IsPrime := Ideal.isPrime_radical h𝔮
  have hP : (𝔮.radical.map (algebraMap A B)).IsPrime := isPrime_map 𝔮.radical hB
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_refl 𝔮.radical)
    (IsNoetherian.noetherian _)
  refine le_antisymm ?_ fun x hx => ?_
  · rw [← hP.radical]
    exact Ideal.radical_mono (Ideal.map_mono Ideal.le_radical)
  · refine ⟨n, ?_⟩
    have : x ^ n ∈ (𝔮.radical.map (algebraMap A B)) ^ n := Ideal.pow_mem_pow hx n
    rw [← Ideal.map_pow] at this
    exact Ideal.map_mono hn this

/-- **The extension of a primary ideal to `A{T}` is primary.** Let `A` be a henselian noetherian
local ring, `𝔮 ⊂ A` a primary ideal and `B = A{T}` the Henselization of `A[T]` at the origin, `T`
a finite family of indeterminates. Then `𝔮 B` is a primary ideal of `B`; its radical is `(√𝔮) B`
by `radical_map_eq_of_isPrimary`. -/
@[weil "lem_fk107_henselian_line_primary_extension"]
theorem isPrimary_map {𝔮 : Ideal A} (h𝔮 : 𝔮.IsPrimary)
    (hB : IsHenselianPolynomialRing A σ B) :
    (𝔮.map (algebraMap A B)).IsPrimary := by
  set f := algebraMap A B
  set P := 𝔮.radical.map f
  have : 𝔮.radical.IsPrime := Ideal.isPrime_radical h𝔮
  have hP : P.IsPrime := isPrime_map 𝔮.radical hB
  have : IsHenselization (LocalizationAtOrigin A σ)
    (ResidueField (LocalizationAtOrigin A σ)) B := hB
  have : IsNoetherianRing B :=
    isNoetherianRing_of_isHenselization (A := LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ))
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  rw [Ideal.isPrimary_iff]
  refine ⟨ne_top_of_le_ne_top hP.ne_top (Ideal.map_mono Ideal.le_radical), fun {x y} hxy => ?_⟩
  rw [radical_map_eq_of_isPrimary h𝔮 hB]
  by_contra hcon
  obtain ⟨hx, hy⟩ := not_or.1 hcon
  -- the `B`-module `B ⊗_A (A ⧸ 𝔮) ≅ B ⧸ 𝔮 B`
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔮
  set w : B ⊗[A] (A ⧸ 𝔮) := e (Ideal.Quotient.mk _ x)
  have hw : w ≠ 0 := by
    simpa [w, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hyw : y • w = 0 := by
    have : y • w = e (Ideal.Quotient.mk _ (x * y)) := by
      rw [← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm]
    rw [this, (Ideal.Quotient.eq_zero_iff_mem).2 hxy, map_zero]
  obtain ⟨Q, hQ, hwQ⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B w hw
  have hyQ : y ∈ Q := hwQ (Submodule.mem_colon_singleton.2 (by simpa using hyw))
  obtain ⟨hQp, z, hz⟩ := isAssociatedPrime_iff.1 hQ
  have hmem := ((associatedPrimes.tensorProduct_of_flat (R := A) (S := B) (M := A ⧸ 𝔮)
    (N := B)).2 inferInstance).le ⟨hQp, z, hz.symm⟩
  rw [associatedPrimes.eq_singleton_of_isPrimary h𝔮] at hmem
  simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left, Set.mem_ofPred_eq] at hmem
  obtain ⟨-, w', hw'⟩ := hmem
  rw [← hw'] at hyQ
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ w'
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map] at hyQ
  have hyQ' : y * b ∈ P := by simpa using hyQ
  have hb : b ∈ P := (hP.mem_or_mem hyQ').resolve_left hy
  have hb' : b ∈ P • (⊤ : Submodule B B) := by simpa using hb
  exact hQp.ne_top (by
    rw [← hw', (Submodule.Quotient.mk_eq_zero _).2 hb', Submodule.colon_singleton_zero])

end MvPolynomial.IsHenselianPolynomialRing
