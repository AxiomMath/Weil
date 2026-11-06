module

public import Weil.Attr
public import Weil.RingTheory.Henselian.Henselization.HenselianLineBaseChangeFinite
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The henselian polynomial ring modulo an ideal of the base

Let `A` be a local ring, `I ⊂ A` an ideal with `A ⧸ I` local (for instance a prime ideal `𝔭`),
and `T = (T_i)_{i ∈ σ}` a family of indeterminates. Write `A{T}` for the henselization of `A[T]`
at the origin (`MvPolynomial.IsHenselianPolynomialRing`). Then
`A{T} ⧸ I A{T} ≅ (A ⧸ I){T}` as `A[T]`-algebras.

Indeed `A ⧸ I` is a local `A`-algebra, finite as an `A`-module, and
`A{T} ⧸ I A{T} ≅ A{T} ⊗_A A ⧸ I`, so this is the finite base change
`MvPolynomial.exists_ringEquiv_tensorProduct_of_isHenselianPolynomialRing`.

## Main results

* `MvPolynomial.exists_ringEquiv_quotient_of_isHenselianPolynomialRing`:
  `A{T} ⧸ I A{T} ≅ (A ⧸ I){T}`, compatibly with the maps from `A[T]`.

## Implementation notes

The source assumes `A` henselian and noetherian, `I = 𝔭` prime, and one indeterminate `t`; none
of this is used. Only the locality of `A ⧸ I` is needed (it holds for every proper ideal, by
`IsLocalRing.of_surjective'`), and any family of indeterminates is allowed (`σ = Fin 1` is the
source's case). The `A[T]`-algebra structures are the maps
`A[T] → A[T]_{(𝔪, T)} → A{T} → A{T} ⧸ I A{T}` and
`A[T] → (A ⧸ I)[T] → (A ⧸ I)[T]_{(𝔪, T)} → (A ⧸ I){T}`; that the isomorphism is one of
`A[T]`-algebras is its compatibility with them.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open IsLocalRing
open scoped TensorProduct

universe u v w w'

namespace MvPolynomial

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type v}

/-- **The henselian polynomial ring modulo an ideal of the base.** Let `A` be a local ring, `I` an
ideal of `A` with `A ⧸ I` local (e.g. a prime ideal), `B = A{T}` and `B' = (A ⧸ I){T}` the
henselizations of the polynomial rings at the origin. Then `B ⧸ I B ≅ B'` as `A[T]`-algebras:
there is a ring isomorphism `e : B ⧸ I B ≃ B'` carrying the image of every `q ∈ A[T]` in
`B ⧸ I B` to the image in `B'` of its reduction `q mod I ∈ (A ⧸ I)[T]`. -/
@[weil "lem_fk107_henselian_line_mod_prime"]
theorem exists_ringEquiv_quotient_of_isHenselianPolynomialRing (I : Ideal A)
    [IsLocalRing (A ⧸ I)]
    {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
    [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]
    (hB : IsHenselianPolynomialRing A σ B)
    {B' : Type w'} [CommRing B'] [IsLocalRing B'] [Algebra (LocalizationAtOrigin (A ⧸ I) σ) B']
    (hB' : IsHenselianPolynomialRing (A ⧸ I) σ B') :
    ∃ e : B ⧸ I.map (algebraMap A B) ≃+* B', ∀ q : MvPolynomial σ A,
      e (Ideal.Quotient.mk _ (algebraMap (LocalizationAtOrigin A σ) B (algebraMap _ _ q))) =
        algebraMap (LocalizationAtOrigin (A ⧸ I) σ) B'
          (algebraMap _ _ (map (Ideal.Quotient.mk I) q)) := by
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorProduct_of_isHenselianPolynomialRing hB hB'
  refine ⟨(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv.trans e,
    fun q => ?_⟩
  rw [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, ← he]
  congr 1
  -- both sides are ring homomorphisms `A[T] → B ⊗_A A ⧸ I` evaluated at `q`
  let φ : MvPolynomial σ A →+* B ⊗[A] (A ⧸ I) :=
    (eval₂Hom (Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[A] B ⊗[A] (A ⧸ I)).toRingHom
      (fun i => algebraMap (LocalizationAtOrigin A σ) B
        (algebraMap _ _ (X i : MvPolynomial σ A)) ⊗ₜ 1)).comp (map (Ideal.Quotient.mk I))
  let ψ : MvPolynomial σ A →+* B ⊗[A] (A ⧸ I) :=
    Algebra.TensorProduct.includeLeftRingHom.comp
      ((algebraMap (LocalizationAtOrigin A σ) B).comp (algebraMap _ _))
  have : ψ = φ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change algebraMap (LocalizationAtOrigin A σ) B (algebraMap _ _ (C a)) ⊗ₜ 1 =
        eval₂Hom _ _ (map (Ideal.Quotient.mk I) (C a))
      rw [map_C, eval₂Hom_C, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (MvPolynomial σ A),
        ← IsScalarTower.algebraMap_apply A (LocalizationAtOrigin A σ) B]
      change algebraMap A B a ⊗ₜ 1 = 1 ⊗ₜ algebraMap A (A ⧸ I) a
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · change _ = eval₂Hom _ _ (map (Ideal.Quotient.mk I) (X i))
      rw [map_X, eval₂Hom_X']
      rfl
  exact RingHom.congr_fun this q

end MvPolynomial
