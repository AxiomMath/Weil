module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteAlgebras
public import WeilFrontier.Defs.RingTheory.Henselian.StrictHenselization.StrictHenselizationComparisonMap
public import WeilFrontier.Defs.RingTheory.TensorProduct.Quotient
public import WeilFrontier.RingTheory.Henselian.Henselization.Defs
public import WeilFrontier.RingTheory.Henselian.Henselization.StrictHenselizationTensorLocalFactorIso
public import WeilFrontier.RingTheory.Henselian.Henselization.TensorProduct

/-!
# A finite algebra base changed to a strict Henselization

Let `A` be a local ring, `A → B` a finite ring homomorphism, `k` a separably closed field with a
local homomorphism `φ : A → k`, large enough for `A → B`, and `(Ã, φ̃)` the Henselization of `A`
with respect to `φ`. Then every comparison map
`Θ : Ã ⊗[A] B → ∏_{ψ ∈ Hom_A(B, k)} B̃_ψ` is a ring isomorphism, and `Hom_A(B, k)` is finite.

The proof: `T = Ã ⊗[A] B` is finite over the henselian local ring `Ã`, so it has finitely many
maximal ideals and `T → ∏_M T_M` is bijective. The maximal ideals of `T` are the kernels `M_ψ`
of `a ⊗ b ↦ φ̃(a) ψ(b)`, each for exactly one `ψ`, and each component `Θ_ψ` factors as an
isomorphism `T_{M_ψ} ≃ B̃_ψ` after the localization map.

## Main results

* `IsLocalRing.IsHenselizationAlong.finite_homOver`: `Hom_A(B, k)` is finite.
* `IsLocalRing.IsStrictHenselizationComparison.bijective`: a comparison map is bijective.
* `IsLocalRing.IsStrictHenselizationComparison.ringEquiv`: the comparison map as a ring
  isomorphism.

## Implementation notes

The source assumes `A` noetherian; the proof does not use it. The hypothesis on `k` is the
one of `IsLargeEnoughFor` (every residue field of `k ⊗[A] B ⧸ 𝔫` at a maximal ideal is `k`),
not the weaker one that every `B ⧸ 𝔫` embeds into `k` over `A`, under which the statement fails.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w x

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Module.Finite A B] {k : Type w} [Field k] [IsSepClosed k] [Algebra A k]
  [IsLocalHom (algebraMap A k)] {Ã : Type x} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã]
  {φ' : Ã →+* k}

/-- An element of `Hom_A(B, k)` as an `A`-algebra homomorphism. -/
def HomOver.toAlgHom (ψ : HomOver (algebraMap A k) B) : B →ₐ[A] k :=
  { (ψ : B →+* k) with commutes' := fun a => RingHom.congr_fun ψ.2 a }

/-- `Hom_A(B, k)` is the set of `A`-algebra homomorphisms `B →ₐ[A] k`. -/
def HomOver.equivAlgHom : HomOver (algebraMap A k) B ≃ (B →ₐ[A] k) where
  toFun := HomOver.toAlgHom
  invFun σ := ⟨σ.toRingHom, RingHom.ext fun a => σ.commutes a⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace IsHenselizationAlong

variable (hA : IsHenselizationAlong (algebraMap A k) Ã φ')
include hA

/-- The maximal ideal `M_ψ` of `Ã ⊗[A] B`, the kernel of `a ⊗ b ↦ φ̃(a) ψ(b)`. -/
def maximalIdealOfHomOver (ψ : HomOver (algebraMap A k) B) : MaximalSpectrum (Ã ⊗[A] B) :=
  ⟨RingHom.ker (Algebra.TensorProduct.productMap hA.toAlgHom ψ.toAlgHom),
    hA.isMaximal_ker_productMap ψ.toAlgHom⟩

/-- `ψ ↦ M_ψ` is a bijection from `Hom_A(B, k)` onto the maximal ideals of `Ã ⊗[A] B`. -/
theorem bijective_maximalIdealOfHomOver (hk : IsLargeEnoughFor A B k) :
    Function.Bijective (hA.maximalIdealOfHomOver (B := B)) :=
  (hA.bijective_ker_productMap hk).comp HomOver.equivAlgHom.bijective

/-- **`Hom_A(B, k)` is finite**, when `k` is large enough for the finite `A → B`. -/
@[weil "lem_fk103_strict_henselization_tensor_finite"]
theorem finite_homOver (hk : IsLargeEnoughFor A B k) : Finite (HomOver (algebraMap A k) B) := by
  have := hA.henselian
  have := finite_maximalSpectrum_of_henselianLocalRing Ã (Ã ⊗[A] B)
  exact Finite.of_injective _ (hA.bijective_maximalIdealOfHomOver hk).1

end IsHenselizationAlong

namespace IsStrictHenselizationComparison

variable {Θ : Ã ⊗[A] B →+* strictHenselizationProduct (algebraMap A k) B}

/-- **Comparison maps are isomorphisms.** Let `A` be a local ring, `A → B` finite, `k` a
separably closed field with a local homomorphism `A → k`, large enough for `A → B`, and
`(Ã, φ̃)` the Henselization of `A` with respect to `A → k`. Then every comparison map
`Θ : Ã ⊗[A] B → ∏_{ψ ∈ Hom_A(B, k)} B̃_ψ` is bijective. -/
@[weil "lem_fk103_strict_henselization_tensor_finite"]
theorem bijective (hA : IsHenselizationAlong (algebraMap A k) Ã φ')
    (hk : IsLargeEnoughFor A B k) (hΘ : IsStrictHenselizationComparison φ' Θ) :
    Function.Bijective Θ := by
  classical
  set T := Ã ⊗[A] B
  have := hA.henselian
  have hT := bijective_toPiLocalization_of_henselianLocalRing Ã T
  -- the local factors `β_ψ : T_{M_ψ} ≃ B̃_ψ`
  have hβ : ∀ ψ : HomOver (algebraMap A k) B,
      ∃ β : Localization.AtPrime (hA.maximalIdealOfHomOver ψ).asIdeal ≃+*
          (ψ : B →+* k).strictHenselizationAt,
        ∀ t, β (algebraMap _ _ t) = Θ t ψ := fun ψ =>
    hA.exists_ringEquiv_localization_tensorProduct
      (RingHom.isStrictHenselizationAt_strictHenselizationAt (ψ : B →+* k))
      (Algebra.TensorProduct.productMap hA.toAlgHom ψ.toAlgHom).toRingHom
      (fun a b => by simp [HomOver.toAlgHom])
      ((Pi.evalRingHom _ ψ).comp Θ) (fun b => hΘ.apply_one_tmul ψ b)
      (fun a => hΘ.hom_apply_tmul_one ψ a)
  choose β hβ using hβ
  let E := Equiv.ofBijective _ (hA.bijective_maximalIdealOfHomOver (B := B) hk)
  refine ⟨fun t₁ t₂ he => hT.1 ?_, fun y => ?_⟩
  · funext I
    obtain ⟨ψ, rfl⟩ := E.surjective I
    apply (β ψ).injective
    simp only [MaximalSpectrum.toPiLocalization_apply_apply]
    change β ψ (algebraMap T _ t₁) = β ψ (algebraMap T _ t₂)
    rw [hβ, hβ, he]
  · let w : ∀ ψ, Localization.AtPrime (E ψ).asIdeal := fun ψ => (β ψ).symm (y ψ)
    obtain ⟨t, ht⟩ := hT.2 (Equiv.piCongrLeft (fun I : MaximalSpectrum T =>
      Localization.AtPrime I.asIdeal) E w)
    refine ⟨t, funext fun ψ => ?_⟩
    have := congrFun ht (E ψ)
    rw [Equiv.piCongrLeft_apply_apply, MaximalSpectrum.toPiLocalization_apply_apply] at this
    rw [← hβ ψ t]
    change β ψ (algebraMap T (Localization.AtPrime (E ψ).asIdeal) t) = y ψ
    rw [this]
    exact (β ψ).apply_symm_apply (y ψ)

/-- A comparison map `Θ : Ã ⊗[A] B → ∏_{ψ ∈ Hom_A(B, k)} B̃_ψ` as a ring isomorphism. -/
noncomputable def ringEquiv (hA : IsHenselizationAlong (algebraMap A k) Ã φ')
    (hk : IsLargeEnoughFor A B k) (hΘ : IsStrictHenselizationComparison φ' Θ) :
    Ã ⊗[A] B ≃+* strictHenselizationProduct (algebraMap A k) B :=
  RingEquiv.ofBijective Θ (hΘ.bijective hA hk)

@[simp]
theorem ringEquiv_apply (hA : IsHenselizationAlong (algebraMap A k) Ã φ')
    (hk : IsLargeEnoughFor A B k) (hΘ : IsStrictHenselizationComparison φ' Θ)
    (t : Ã ⊗[A] B) : hΘ.ringEquiv hA hk t = Θ t :=
  rfl

end IsStrictHenselizationComparison

end IsLocalRing
