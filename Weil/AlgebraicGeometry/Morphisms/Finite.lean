/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Weil.RingTheory.TotallySplit
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Generic factorization of finite surjective morphisms through purely inseparable ones

Let `f : X ⟶ Y` be a finite surjective morphism of integral schemes. We show that, after an
étale base change `U ⟶ Y` with `U` nonempty, the morphism `X ×[Y] U ⟶ U` factors as a purely
inseparable morphism `X ×[Y] U ⟶ U ⊔ ⋯ ⊔ U` (`m ≥ 1` copies) followed by the fold map.

The proof is the classical one. Let `K` and `L` be the function fields of `Y` and `X`, let `Lₛ` be
the separable closure of `K` in `L` and `m = [Lₛ : K]`. There is a finite separable extension
`K'/K` with `K' ⊗[K] Lₛ ≅ K'ᵐ`; since `L/Lₛ` is purely inseparable, every element of
`K' ⊗[K] L` has a `pⁿ`-th power in the image of `K'ᵐ` (`p` the exponential characteristic). Over
an affine open `Spec B ⊆ Y` with preimage `Spec A`, write `K' = K(β)` with `β` a root of a monic
`Q ∈ B[X]` whose image in `K[X]` is the minimal polynomial of `β`, and let `B'` be the standard
étale `B`-algebra `B[X, 1/c]/(Q)` for a suitable nonzero `c ∈ B` clearing all the denominators
involved. Flatness of `B'` over `B` embeds `A ⊗[B] B'` into `K' ⊗[K] L`, and the decomposition
of the generic fibre descends to a finite `p`-radical ring map `B'ᵐ → A ⊗[B] B'`, whose spectrum
is the required purely inseparable morphism.

## Main results

* `AlgebraicGeometry.IsFinite.exists_etale_isPurelyInseparable_comp_sigmaDesc_eq_snd`: the
  generic factorization of a finite surjective morphism of integral schemes.
* `Algebra.exists_etale_finite_isPRadical_pi`: its algebraic form, for a finite injective
  extension of domains `B → A`.
* `AlgebraicGeometry.isPurelyInseparable_SpecMap_of_isPRadical`: the spectrum of a finite
  `p`-radical ring map is purely inseparable.

## Implementation notes

The source assumes the schemes noetherian and separated; neither hypothesis is needed. The
étale scheme `U` is affine, the spectrum of a standard étale algebra over an affine open of `Y`.
The disjoint union of `m` copies of `U` is the coproduct `∐ fun _ : Fin m ↦ U` and the fold map
is `Sigma.desc fun _ ↦ 𝟙 U`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

open CategoryTheory Limits

universe u

open Polynomial IntermediateField TensorProduct

namespace Algebra.GenericFactorization

/-- The elements of `S` some `p ^ n`-th power of which lies in the range of `φ : R →+* S`. -/
def powRange {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ) [ExpChar S p] :
    Subring S where
  carrier := {x | ∃ (n : ℕ) (y : R), φ y = x ^ p ^ n}
  mul_mem' := by
    rintro x z ⟨n, y, hy⟩ ⟨k, w, hw⟩
    refine ⟨n + k, y ^ p ^ k * w ^ p ^ n, ?_⟩
    rw [map_mul, map_pow, map_pow, hy, hw, mul_pow, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      add_comm k n]
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro x z ⟨n, y, hy⟩ ⟨k, w, hw⟩
    refine ⟨n + k, y ^ p ^ k + w ^ p ^ n, ?_⟩
    rw [map_add, map_pow, map_pow, hy, hw, add_pow_expChar_pow, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm k n]
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro x ⟨n, y, hy⟩
    refine ⟨n, -y, ?_⟩
    rw [map_neg, hy, neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

/-- Membership in `powRange`. -/
theorem mem_powRange {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ) [ExpChar S p]
    (x : S) : x ∈ powRange φ p ↔ ∃ (n : ℕ) (y : R), φ y = x ^ p ^ n := Iff.rfl

/-- Finitely many elements of a module over a domain, each of which lies in a submodule `N` after
multiplication by a nonzero scalar, have a common such nonzero scalar. -/
theorem exists_common_denom {B M : Type*} [CommRing B] [IsDomain B] [AddCommGroup M] [Module B M]
    (N : Submodule B M) {ι : Type*} [Finite ι] (x : ι → M)
    (h : ∀ i, ∃ b : B, b ≠ 0 ∧ b • x i ∈ N) : ∃ b : B, b ≠ 0 ∧ ∀ i, b • x i ∈ N := by
  classical
  cases nonempty_fintype ι
  choose b hb hbx using h
  refine ⟨∏ i, b i, Finset.prod_ne_zero_iff.mpr fun i _ ↦ hb i, fun i ↦ ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
  exact N.smul_mem _ (hbx i)

/-- In a domain `A` integral over a domain `B`, every element of the fraction field of `A` becomes
an element of `A` after multiplication by a nonzero element of `B`. -/
theorem exists_mul_eq_algebraMap {B A F : Type*} [CommRing B] [IsDomain B] [CommRing A]
    [IsDomain A] [Algebra B A] [Algebra.IsIntegral B A] [Field F] [Algebra A F] [Algebra B F]
    [IsScalarTower B A F] [IsFractionRing A F] (f : F) :
    ∃ b : B, b ≠ 0 ∧ ∃ a : A, algebraMap A F a = algebraMap B F b * f := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) f
  have hs : (s : A) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have := Ideal.comap_ne_bot_of_integral_mem (R := B) hs (Ideal.mem_span_singleton_self (s : A))
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨b, hb0, t * a, ?_⟩
  rw [IsScalarTower.algebraMap_apply B A F, ← ht, map_mul, map_mul, mul_assoc,
    IsLocalization.mk'_spec']

/-- If `A` is a domain finite over a domain `B`, the fraction field of `A` is finite over the
fraction field of `B`. -/
theorem finite_of_isFractionRing {B A K F : Type*} [CommRing B] [IsDomain B] [CommRing A]
    [IsDomain A] [Algebra B A] [Module.Finite B A] [Field K] [Algebra B K] [IsFractionRing B K]
    [Field F] [Algebra A F] [Algebra B F] [Algebra K F] [IsScalarTower B A F]
    [IsScalarTower B K F] [IsFractionRing A F] : Module.Finite K F := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := A)
  refine ⟨⟨s.image (algebraMap A F), Submodule.eq_top_iff'.mpr fun f ↦ ?_⟩⟩
  obtain ⟨b, hb, a, ha⟩ := exists_mul_eq_algebraMap (B := B) (A := A) f
  have ha' : algebraMap A F a ∈
      Submodule.span K ((s.image (algebraMap A F) : Finset F) : Set F) := by
    have : a ∈ Submodule.span B (s : Set A) := hs ▸ Submodule.mem_top
    have := Submodule.apply_mem_span_image_of_mem_span
      (IsScalarTower.toAlgHom B A F).toLinearMap this
    rw [Finset.coe_image]
    exact Submodule.span_le_restrictScalars B K _ this
  have hbK : algebraMap B K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hb
  have : f = (algebraMap B K b)⁻¹ • algebraMap A F a := by
    rw [ha, Algebra.smul_def, IsScalarTower.algebraMap_apply B K F, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hbK, map_one, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ ha'



/-- If `β` generates `K'` as a `K`-algebra, `K` the fraction field of `B`, every element of `K'`
becomes a polynomial in `β` with coefficients in `B` after multiplication by a nonzero element of
`B`. -/
theorem exists_aeval_eq_mul {B K K' : Type*} [CommRing B] [IsDomain B] [Field K] [Algebra B K]
    [IsFractionRing B K] [Field K'] [Algebra K K'] [Algebra B K'] [IsScalarTower B K K'] {β : K'}
    (hβ : Algebra.adjoin K {β} = ⊤) (k : K') :
    ∃ b : B, b ≠ 0 ∧ ∃ q : B[X], aeval β q = algebraMap B K' b * k := by
  have hk : k ∈ Algebra.adjoin K {β} := hβ ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hk
  obtain ⟨q, rfl⟩ := hk
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (R := B) (nonZeroDivisors B) q
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors B) q, ?_⟩
  rw [← aeval_map_algebraMap K, hq, Algebra.smul_def, Polynomial.algebraMap_apply, map_mul,
    aeval_C, ← IsScalarTower.algebraMap_apply]
  rfl

/-- **Generic splitting.** For a finite field extension `F/K` there are a finite separable
extension `K'/K`, an integer `m ≥ 1` and an injective `K'`-algebra map `K'ᵐ → K' ⊗[K] F` such
that every element of `K' ⊗[K] F` has a `pⁿ`-th power in its image, `p` the exponential
characteristic of `K`. Here `m` is the separable degree of `F/K`. -/
theorem exists_pi_tensorProduct (K F : Type u) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K'), FiniteDimensional K K' ∧
      Algebra.IsSeparable K K' ∧ ∃ m : ℕ, 1 ≤ m ∧ ∃ χ : (Fin m → K') →ₐ[K'] K' ⊗[K] F,
        Function.Injective χ ∧ ∀ t, ∃ (n : ℕ) (y : Fin m → K'), χ y = t ^ ringExpChar K ^ n := by
  let Ls := separableClosure K F
  have : Algebra.Etale K Ls :=
    ⟨Algebra.FormallyEtale.of_isSeparable K Ls, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  obtain ⟨K', _, _, hfin, hsep, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finiteDimensional_isSeparable_tensorProduct_algEquiv_pi K Ls
  set m := Module.finrank K Ls
  have hm : 1 ≤ m := Module.finrank_pos
  let ι : Ls →ₐ[K] F := IsScalarTower.toAlgHom K Ls F
  let χ : (Fin m → K') →ₐ[K'] K' ⊗[K] F :=
    (Algebra.TensorProduct.map (AlgHom.id K' K') ι).comp e.symm.toAlgHom
  have hχ : Function.Injective χ := by
    refine Function.Injective.comp (f := e.symm) ?_ e.symm.injective
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K') ι.toLinearMap ι.injective
  refine ⟨K', inferInstance, inferInstance, hfin, hsep, m, hm, χ, hχ, ?_⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nontrivial (K' ⊗[K] F) := hχ.nontrivial
  set p := ringExpChar K
  have : ExpChar (K' ⊗[K] F) p :=
    expChar_of_injective_algebraMap (algebraMap K (K' ⊗[K] F)).injective p
  have : ExpChar Ls p := expChar_of_injective_algebraMap (algebraMap K Ls).injective p
  have hpi : IsPurelyInseparable Ls F := separableClosure.isPurelyInseparable K F
  suffices ∀ t, t ∈ powRange χ.toRingHom p from this
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k f =>
    rw [← mul_one k, ← one_mul f, ← Algebra.TensorProduct.tmul_mul_tmul]
    refine mul_mem ⟨0, algebraMap K' _ k, ?_⟩ ?_
    · simp [Algebra.TensorProduct.algebraMap_apply]
    · obtain ⟨n, l, hl⟩ := IsPurelyInseparable.pow_mem Ls p f
      refine ⟨n, e (1 ⊗ₜ l), ?_⟩
      simp [χ, ι, Algebra.TensorProduct.tmul_pow, hl]
  | add x y hx hy => exact add_mem hx hy


section


variable {B K K' : Type*} [CommRing B] [IsDomain B] [Field K] [Algebra B K] [IsFractionRing B K]
  [Field K'] [Algebra K K'] [Algebra B K'] [IsScalarTower B K K']

/-- A finite separable extension `K'` of the fraction field `K` of a domain `B` has a primitive
element `β` whose minimal polynomial is the image of a monic `Q ∈ B[X]`, and `Q'` is invertible
modulo `Q` after inverting a nonzero `c ∈ B`. -/
theorem exists_primitive_monic_lift [FiniteDimensional K K'] [Algebra.IsSeparable K K'] :
    ∃ (β : K') (Q : B[X]), Q.Monic ∧ Q.map (algebraMap B K) = minpoly K β ∧
      Algebra.adjoin K {β} = ⊤ ∧ ∃ (pu pv : B[X]) (c : B), c ≠ 0 ∧
        derivative Q * pu + Q * pv = C c := by
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element K K'
  have hγi : IsIntegral K γ := Algebra.IsIntegral.isIntegral γ
  set P := minpoly K γ
  have hPm : P.Monic := minpoly.monic hγi
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := lifts_and_natDegree_eq_and_monic
    (IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors B) P
      (by rw [hPm.leadingCoeff]; exact one_mem _))
    ((monic_scaleRoots_iff _).mpr hPm)
  set d : B := (IsLocalization.commonDenom (nonZeroDivisors B) P.support P.coeff : B)
  have hd : d ≠ 0 := nonZeroDivisors.coe_ne_zero _
  set β : K' := algebraMap B K' d * γ
  have hβ : aeval β (Q.map (algebraMap B K)) = 0 := by
    rw [hQ, aeval_def]
    have := scaleRoots_eval₂_eq_zero (algebraMap K K') (s := algebraMap B K d) (minpoly.aeval K γ)
    rwa [← IsScalarTower.algebraMap_apply] at this
  have hdK : algebraMap B K' d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply B K K']
    exact (_root_.map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hd)
  have hKβ : K⟮β⟯ = ⊤ := by
    rw [_root_.eq_top_iff, ← hγ, adjoin_simple_le_iff]
    have : γ = (algebraMap B K' d)⁻¹ * β := by
      rw [← mul_assoc, inv_mul_cancel₀ hdK, one_mul]
    rw [this, IsScalarTower.algebraMap_apply B K K', ← map_inv₀]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have hβi : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hadj : Algebra.adjoin K {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβi.isAlgebraic, hKβ]
    rfl
  have hmin : Q.map (algebraMap B K) = minpoly K β := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβi) (hQm.map _)
      (minpoly.dvd K β hβ) ?_)
    rw [hQm.natDegree_map, hQdeg, natDegree_scaleRoots, ← IntermediateField.adjoin.finrank hγi,
      ← IntermediateField.adjoin.finrank hβi, hγ, hKβ]
  refine ⟨β, Q, hQm, hmin, hadj, ?_⟩
  have hsep : (minpoly K β).Separable := Algebra.IsSeparable.isSeparable K β
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨bu, hbu, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors B) u
  obtain ⟨bv, hbv, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors B) v
  set U := IsLocalization.integerNormalization (nonZeroDivisors B) u
  set V := IsLocalization.integerNormalization (nonZeroDivisors B) v
  refine ⟨C bu * V, C bv * U, bu * bv, mul_ne_zero (nonZeroDivisors.ne_zero hbu)
    (nonZeroDivisors.ne_zero hbv), ?_⟩
  apply map_injective (algebraMap B K) (IsFractionRing.injective B K)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map, hmin,
    hu, hv]
  rw [← hmin] at huv ⊢
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
  linear_combination (C (algebraMap B K bu) * C (algebraMap B K bv)) * huv


end

/-- **Spreading out the generic splitting.** Let `B → A` be a finite injective extension of
domains with fraction fields `K → F`, and let `χ : K'ᵐ → K' ⊗[K] F` be a generic splitting as in
`exists_pi_tensorProduct`. Then there are an étale `B`-algebra `B' ≠ 0` and a finite `p`-radical
`B'`-algebra map `B'ᵐ → A ⊗[B] B'`. -/
theorem exists_etale_of_pi_tensorProduct (B A K F K' : Type u) [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [Algebra B A] [FaithfulSMul B A] [Module.Finite B A]
    [Field K] [Algebra B K] [IsFractionRing B K] [Field F] [Algebra A F] [Algebra B F]
    [Algebra K F] [IsScalarTower B A F] [IsScalarTower B K F] [IsFractionRing A F]
    [Field K'] [Algebra K K'] [Algebra B K'] [IsScalarTower B K K'] [FiniteDimensional K K']
    [Algebra.IsSeparable K K'] (m : ℕ) (hm : 1 ≤ m) (χ : (Fin m → K') →ₐ[K'] K' ⊗[K] F)
    (hχ : Function.Injective χ)
    (hrad : ∀ t, ∃ (n : ℕ) (y : Fin m → K'), χ y = t ^ ringExpChar K ^ n) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B'), Algebra.Etale B B' ∧ Nontrivial B' ∧
      ∃ p : ℕ, ExpChar (A ⊗[B] B') p ∧ ∃ φ : (Fin m → B') →+* A ⊗[B] B',
        φ.Finite ∧ IsPRadical φ p ∧
        φ.comp (algebraMap B' (Fin m → B')) = Algebra.TensorProduct.includeRight.toRingHom := by
  classical
  set p := ringExpChar K
  obtain ⟨β, Q, hQm, hQmin, hadj, pu, pv, c₀, hc₀, hcond⟩ :=
    exists_primitive_monic_lift (B := B) (K := K) (K' := K')
  have hQβ : aeval β Q = 0 := by
    rw [← aeval_map_algebraMap K, hQmin, minpoly.aeval]
  -- the subalgebra `Λ` of `T = K' ⊗[K] F` generated by `A` and `β`
  let jA : A →ₐ[B] K' ⊗[K] F :=
    ((Algebra.TensorProduct.includeRight : F →ₐ[K] K' ⊗[K] F).restrictScalars B).comp
      (IsScalarTower.toAlgHom B A F)
  let Λ : Subalgebra B (K' ⊗[K] F) := Algebra.adjoin B (Set.range jA ∪ {β ⊗ₜ 1})
  have hβΛ : β ⊗ₜ[K] (1 : F) ∈ Λ := Algebra.subset_adjoin (Or.inr rfl)
  have hjΛ (a : A) : jA a ∈ Λ := Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
  have hdenT (t : K' ⊗[K] F) : ∃ b : B, b ≠ 0 ∧ b • t ∈ Λ.toSubmodule := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | tmul k f =>
      obtain ⟨b₁, hb₁, q, hq⟩ := exists_aeval_eq_mul (B := B) hadj k
      obtain ⟨b₂, hb₂, a, ha⟩ := exists_mul_eq_algebraMap (B := B) (A := A) f
      refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
      have : (b₁ * b₂) • (k ⊗ₜ[K] f) = (aeval β q ⊗ₜ[K] (1 : F)) * jA a := by
        simp only [jA, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hq, ha]
        rw [← Algebra.smul_def, ← Algebra.smul_def, ← algebraMap_smul K b₂ f,
          ← TensorProduct.smul_tmul, smul_comm, algebraMap_smul, TensorProduct.smul_tmul',
          smul_smul, mul_comm]
      rw [this]
      refine Λ.mul_mem ?_ (hjΛ a)
      have : aeval β q ⊗ₜ[K] (1 : F) = aeval (β ⊗ₜ[K] (1 : F)) q := by
        rw [← Algebra.TensorProduct.includeLeft_apply (S := B), ← aeval_algHom_apply]
        rfl
      rw [this]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hβΛ)
        (aeval_mem_adjoin_singleton B _)
    | add x y hx hy =>
      obtain ⟨b, hb, hbx⟩ := hx
      obtain ⟨b', hb', hby⟩ := hy
      refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
      exact add_mem (Submodule.smul_mem _ _ hbx) (Submodule.smul_mem _ _ hby)
  have hdenK (k : K') : ∃ b : B, b ≠ 0 ∧ b • k ∈ (aeval (R := B) β).range.toSubmodule := by
    obtain ⟨b, hb, q, hq⟩ := exists_aeval_eq_mul (B := B) hadj k
    exact ⟨b, hb, q, by rw [Algebra.smul_def, ← hq]; rfl⟩
  let e : Fin m → K' ⊗[K] F := fun i ↦ χ (Pi.single i 1)
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := B) (A := A)
  choose n v hv using fun a : G ↦ hrad (jA a)
  obtain ⟨b₁, hb₁, hb₁e⟩ := exists_common_denom Λ.toSubmodule e (fun i ↦ hdenT (e i))
  obtain ⟨b₂, hb₂, hb₂v⟩ := exists_common_denom (aeval (R := B) β).range.toSubmodule
    (fun ai : G × Fin m ↦ v ai.1 ai.2) (fun ai ↦ hdenK _)
  set b := b₁ * b₂ with hb_def
  have hb : b ≠ 0 := mul_ne_zero hb₁ hb₂
  have hbe (i : Fin m) : b • e i ∈ Λ := by
    rw [hb_def, mul_comm, mul_smul]; exact Λ.smul_mem (hb₁e i) _
  have hbv (a : G) (i : Fin m) : b • v a i ∈ (aeval (R := B) β).range := by
    rw [hb_def, mul_smul]; exact Subalgebra.smul_mem _ (hb₂v (a, i)) _
  set c := c₀ * b
  have hc : c ≠ 0 := mul_ne_zero hc₀ hb
  let P : StandardEtalePair B := ⟨Q, hQm, C c, ⟨pu * C b, pv * C b, 1, by
    rw [pow_one, show (C c : B[X]) = C c₀ * C b from C_mul]
    linear_combination (C b) * hcond⟩⟩
  have hBK' : Function.Injective (algebraMap B K') := by
    rw [IsScalarTower.algebraMap_eq B K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective B K)
  have hPβ : P.HasMap β := ⟨hQβ, by
    change IsUnit (aeval β (C c))
    rw [aeval_C]
    exact Ne.isUnit ((map_ne_zero_iff _ hBK').mpr hc)⟩
  let lam : P.Ring →ₐ[B] K' := P.lift β hPβ
  have hlamX : lam P.X = β := P.lift_X β hPβ
  have hcu : IsUnit (algebraMap B P.Ring c) := by
    have := P.hasMap_X.2
    rwa [show P.g = C c from rfl, aeval_C] at this
  have hbu : IsUnit (algebraMap B P.Ring b) :=
    isUnit_of_mul_isUnit_right (x := algebraMap B P.Ring c₀) (by rw [← map_mul]; exact hcu)
  have hy : aeval ((1 : F) ⊗ₜ[B] P.X) (minpoly K β) = 0 := by
    rw [← hQmin, aeval_map_algebraMap, ← Algebra.TensorProduct.includeRight_apply,
      aeval_algHom_apply]
    rw [show aeval P.X Q = 0 from P.hasMap_X.1, map_zero]
  let pb : PowerBasis K K' := PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral β) hadj
  have hpb : pb.gen = β := PowerBasis.ofAdjoinEqTop'_gen _ _
  let κ : K' →ₐ[K] F ⊗[B] P.Ring := pb.lift ((1 : F) ⊗ₜ P.X) (by rw [hpb]; exact hy)
  have hκ : κ β = (1 : F) ⊗ₜ P.X := by
    have : κ pb.gen = (1 : F) ⊗ₜ P.X := pb.lift_gen _ _
    rwa [hpb] at this
  let μ : K' ⊗[K] F →ₐ[K] F ⊗[B] P.Ring :=
    Algebra.TensorProduct.lift κ (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[B] P.Ring)
      (fun _ _ ↦ Commute.all _ _)
  let ν : F ⊗[B] P.Ring →ₐ[B] K' ⊗[K] F :=
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeRight : F →ₐ[K] K' ⊗[K] F).restrictScalars B)
      ((Algebra.TensorProduct.includeLeft : K' →ₐ[B] K' ⊗[K] F).comp lam)
      (fun _ _ ↦ Commute.all _ _)
  have hκlam : (κ.restrictScalars B).comp lam = Algebra.TensorProduct.includeRight :=
    P.hom_ext (by simp [hlamX, hκ])
  have hμν : (μ.restrictScalars B).comp ν = AlgHom.id B _ :=
    Algebra.TensorProduct.ext (AlgHom.ext fun f ↦ by simp [μ, ν])
      (AlgHom.ext fun r ↦ by
        simpa [μ, ν, ← Algebra.TensorProduct.one_def] using DFunLike.congr_fun hκlam r)
  have hν : Function.Injective ν :=
    Function.LeftInverse.injective (g := μ) (fun x ↦ DFunLike.congr_fun hμν x)
  let ιS : A ⊗[B] P.Ring →ₐ[B] K' ⊗[K] F :=
    ν.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom B A F) (AlgHom.id B P.Ring))
  have hιS : Function.Injective ιS :=
    hν.comp (Module.Flat.rTensor_preserves_injective_linearMap (M := P.Ring)
      (IsScalarTower.toAlgHom B A F).toLinearMap (IsFractionRing.injective A F))
  have hι1 (r : P.Ring) : ιS (1 ⊗ₜ r) = algebraMap K' _ (lam r) := by
    simp [ιS, ν, Algebra.TensorProduct.algebraMap_apply]
  have hι2 (a : A) : ιS (a ⊗ₜ 1) = jA a := by
    simp [ιS, ν, jA]
  obtain ⟨ub, hub⟩ := hbu.exists_left_inv
  have hlamb : lam ub * algebraMap B K' b = 1 := by
    rw [← lam.commutes, ← map_mul, hub, map_one]
  have hΛ : Λ ≤ ιS.range := by
    refine Algebra.adjoin_le ?_
    rintro _ (⟨a, rfl⟩ | rfl)
    · exact ⟨a ⊗ₜ 1, hι2 a⟩
    · exact ⟨1 ⊗ₜ P.X, by
        change ιS _ = _
        rw [hι1, hlamX]; simp [Algebra.TensorProduct.algebraMap_apply]⟩
  have hrange_e (i : Fin m) : e i ∈ ιS.range := by
    obtain ⟨x, hx⟩ := hΛ (hbe i)
    refine ⟨(1 ⊗ₜ ub) * x, ?_⟩
    change ιS _ = _
    change ιS x = _ at hx
    rw [map_mul, hx, hι1, Algebra.smul_def, IsScalarTower.algebraMap_apply B K' (K' ⊗[K] F),
      ← mul_assoc, ← map_mul, hlamb, map_one, one_mul]
  have hrange_v (a : G) (i : Fin m) : v a i ∈ lam.range := by
    obtain ⟨q, hq⟩ := hbv a i
    refine ⟨ub * aeval P.X q, ?_⟩
    change lam _ = _
    rw [map_mul, ← aeval_algHom_apply, hlamX]
    change aeval β q = _ at hq
    rw [hq, Algebra.smul_def, ← mul_assoc, hlamb, one_mul]
  choose w hw using hrange_v
  have hincl : Function.Injective (fun r : P.Ring ↦ (1 : A) ⊗ₜ[B] r) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := P.Ring)
      (Algebra.linearMap B A) (FaithfulSMul.algebraMap_injective B A)
    have h2 := (TensorProduct.lid B P.Ring).symm.injective
    convert h1.comp h2 using 1
    ext r
    simp
  have hlam : Function.Injective lam := fun r r' h ↦ hincl (hιS (by
    simp only [hι1, h]))
  let Φ₀ : (Fin m → P.Ring) →+* K' ⊗[K] F :=
    χ.toRingHom.comp (RingHom.pi fun i ↦ lam.toRingHom.comp (Pi.evalRingHom _ i))
  have hΦ₀ (x : Fin m → P.Ring) : Φ₀ x = χ (fun i ↦ lam (x i)) := rfl
  have hΦrange (x : Fin m → P.Ring) : Φ₀ x ∈ ιS.range := by
    have : (fun i ↦ lam (x i)) = ∑ i, lam (x i) • (Pi.single i 1 : Fin m → K') := by
      ext j
      simp [Pi.single_apply]
    rw [hΦ₀, this, map_sum]
    refine Subalgebra.sum_mem _ fun i _ ↦ ?_
    rw [map_smul, Algebra.smul_def, ← hι1]
    exact mul_mem ⟨_, rfl⟩ (hrange_e i)
  let φ : (Fin m → P.Ring) →+* A ⊗[B] P.Ring :=
    (AlgEquiv.ofInjective ιS hιS).symm.toRingHom.comp (Φ₀.codRestrict ιS.range hΦrange)
  have hφ (x : Fin m → P.Ring) : ιS (φ x) = Φ₀ x := by
    change ιS ((AlgEquiv.ofInjective ιS hιS).symm _) = _
    rw [← AlgEquiv.ofInjective_apply ιS hιS, AlgEquiv.apply_symm_apply]
    rfl
  have hφinj : Function.Injective φ := by
    intro x x' h
    have := congrArg ιS h
    rw [hφ, hφ, hΦ₀, hΦ₀] at this
    funext i
    exact hlam (congrFun (hχ this) i)
  have hφe : φ.comp (algebraMap P.Ring (Fin m → P.Ring)) =
      Algebra.TensorProduct.includeRight.toRingHom := by
    refine RingHom.ext fun r ↦ hιS ?_
    rw [RingHom.comp_apply, hφ, hΦ₀]
    change χ (algebraMap K' _ (lam r)) = _
    rw [AlgHom.commutes]
    exact (hι1 r).symm
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nontrivial (K' ⊗[K] F) := hχ.nontrivial
  have : ExpChar (K' ⊗[K] F) p :=
    expChar_of_injective_algebraMap (algebraMap K (K' ⊗[K] F)).injective p
  have hexp : ExpChar (A ⊗[B] P.Ring) p := RingHom.expChar ιS.toRingHom hιS p
  have hfin_incl :
      (Algebra.TensorProduct.includeRight : P.Ring →ₐ[B] A ⊗[B] P.Ring).toRingHom.Finite := by
    have : (Algebra.TensorProduct.includeRight.toRingHom : P.Ring →+* A ⊗[B] P.Ring) =
        (Algebra.TensorProduct.comm B P.Ring A).toRingHom.comp
          (algebraMap P.Ring (P.Ring ⊗[B] A)) := by
      ext r
      simp
    rw [this]
    exact (RingHom.Finite.of_surjective _ (Algebra.TensorProduct.comm B _ _).surjective).comp
      (RingHom.finite_algebraMap.mpr inferInstance)
  have hφfin : φ.Finite := RingHom.Finite.of_comp_finite (f := algebraMap P.Ring (Fin m → _))
    (by rw [hφe]; exact hfin_incl)
  have hr1 (r : P.Ring) : (1 : A) ⊗ₜ[B] r ∈ powRange φ p :=
    ⟨0, algebraMap _ _ r, by rw [pow_zero, pow_one, ← RingHom.comp_apply, hφe]; rfl⟩
  have hA (a : A) : a ⊗ₜ[B] (1 : P.Ring) ∈ powRange φ p := by
    have : a ∈ Algebra.adjoin B (G : Set A) := hG ▸ Algebra.mem_top
    induction this using Algebra.adjoin_induction with
    | mem a ha =>
      refine ⟨n ⟨a, ha⟩, w ⟨a, ha⟩, hιS ?_⟩
      rw [hφ, map_pow, hι2, hΦ₀, ← hv ⟨a, ha⟩]
      congr 1
      funext i
      exact hw _ i
    | algebraMap b' =>
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      exact hr1 _
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul]; exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← mul_one (1 : P.Ring), ← Algebra.TensorProduct.tmul_mul_tmul]
      exact mul_mem hx hy
  have hpow (x : A ⊗[B] P.Ring) : x ∈ powRange φ p := by
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a r =>
      rw [← mul_one a, ← one_mul r, ← Algebra.TensorProduct.tmul_mul_tmul]
      exact mul_mem (hA a) (hr1 r)
    | add x y hx hy => exact add_mem hx hy
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, lam.toRingHom.domain_nontrivial, p,
    hexp, φ, hφfin, ⟨hpow, ?_⟩, hφe⟩
  rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφinj]
  exact bot_le


end Algebra.GenericFactorization

namespace AlgebraicGeometry

/-- If `φ : R →+* S` is `p`-radical and `S` has exponential characteristic `p`, two ring maps from
`S` to a field agreeing on `R` are equal. -/
theorem _root_.IsPRadical.injective_comp_field {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : ℕ) [ExpChar S p] [IsPRadical φ p] (K : Type*) [Field K] :
    Function.Injective fun f : S →+* K ↦ f.comp φ := by
  intro f g hfg
  simp only at hfg
  obtain _ | @⟨_, hp, hchar⟩ := ‹ExpChar S p›
  · ext x
    obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem φ 1 x
    simp only [one_pow, pow_one] at hy
    rw [← hy, ← RingHom.comp_apply, hfg, RingHom.comp_apply]
  · have hK : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [← map_natCast f, CharP.cast_eq_zero, map_zero])
    have : ExpChar K p := ExpChar.prime hp
    ext x
    obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem φ p x
    apply iterateFrobenius_inj K p n
    rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow, ← map_pow, ← hy,
      ← RingHom.comp_apply, hfg, RingHom.comp_apply]

/-- If `φ : R →+* S` is finite and `p`-radical, then `Spec S ⟶ Spec R` is purely inseparable. -/
theorem isPurelyInseparable_SpecMap_of_isPRadical {R S : CommRingCat.{u}} (φ : R ⟶ S) (p : ℕ)
    [ExpChar S p] (hfin : φ.hom.Finite) [IsPRadical φ.hom p] :
    (Spec.map φ).IsPurelyInseparable := by
  refine ⟨(IsFinite.SpecMap_iff φ).mpr hfin, ?_, ?_⟩
  · refine ((tfae_universallyInjective (Spec.map φ)).out 1 2).mpr ?_
    intro K _ g₁ g₂ h
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at h ⊢
    simp only [← Spec.map_comp, Spec.map_inj] at h
    congr 1
    ext1
    exact IsPRadical.injective_comp_field φ.hom p K (congrArg CommRingCat.Hom.hom h)
  · have hp : 0 < p := expChar_pos S p
    have := PrimeSpectrum.isHomeomorph_comap φ.hom (fun x ↦ by
        obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem φ.hom p x
        exact ⟨p ^ n, pow_pos hp n, y, hy⟩)
      ((IsPRadical.ker_le φ.hom p).trans pNilradical_le_nilradical)
    exact ⟨this.surjective⟩

namespace Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-- A composite of purely inseparable morphisms is purely inseparable. -/
theorem IsPurelyInseparable.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : f.IsPurelyInseparable)
    (hg : g.IsPurelyInseparable) : (f ≫ g).IsPurelyInseparable := by
  have := hf.1; have := hf.2.2; have := hg.1; have := hg.2.2
  exact ⟨inferInstance, MorphismProperty.comp_mem @UniversallyInjective f g hf.2.1 hg.2.1,
    inferInstance⟩

/-- An isomorphism is purely inseparable. -/
theorem IsPurelyInseparable.of_isIso (f : X ⟶ Y) [IsIso f] : f.IsPurelyInseparable :=
  isPurelyInseparable_of_instances

end Scheme.Hom

/-- **Generic factorization, algebraic form.** Let `B → A` be a finite injective extension of
domains. There are a nonzero étale `B`-algebra `B'`, an integer `m ≥ 1` and a finite `p`-radical
ring map `φ : B'ᵐ → A ⊗[B] B'` of `B'`-algebras, `p` the exponential characteristic of
`A ⊗[B] B'`. -/
theorem _root_.Algebra.exists_etale_finite_isPRadical_pi (B A : Type u) [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [Algebra B A] [FaithfulSMul B A] [Module.Finite B A] :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B'), Algebra.Etale B B' ∧ Nontrivial B' ∧
      ∃ (m p : ℕ), 1 ≤ m ∧ ExpChar (A ⊗[B] B') p ∧ ∃ φ : (Fin m → B') →+* A ⊗[B] B',
        φ.Finite ∧ IsPRadical φ p ∧
        φ.comp (algebraMap B' (Fin m → B')) = Algebra.TensorProduct.includeRight.toRingHom := by
  classical
  let : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B (FractionRing A)
  have : IsScalarTower B (FractionRing B) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra B _
  have : Module.Finite (FractionRing B) (FractionRing A) :=
    Algebra.GenericFactorization.finite_of_isFractionRing (B := B) (A := A)
  obtain ⟨K', _, _, hfin, hsep, m, hm, χ, hχ, hrad⟩ :=
    Algebra.GenericFactorization.exists_pi_tensorProduct (FractionRing B) (FractionRing A)
  let : Algebra B K' :=
    ((algebraMap (FractionRing B) K').comp (algebraMap B (FractionRing B))).toAlgebra
  have : IsScalarTower B (FractionRing B) K' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨B', _, _, h1, h2, p, h3, φ, h4, h5, h6⟩ :=
    Algebra.GenericFactorization.exists_etale_of_pi_tensorProduct B A (FractionRing B)
      (FractionRing A) K' m hm χ hχ hrad
  exact ⟨B', _, _, h1, h2, m, p, hm, h3, φ, h4, h5, h6⟩

/-- Transport of the generic factorization along a pullback square whose bottom arrow is étale. -/
theorem exists_etale_isPurelyInseparable_of_isPullback {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    {i : X₁ ⟶ X₂} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {j : Y₁ ⟶ Y₂} (h : IsPullback i f₁ f₂ j)
    [Etale j]
    (H : ∃ (U : Scheme.{u}) (e : U ⟶ Y₁), Etale e ∧ Nonempty U ∧ ∃ m : ℕ, 1 ≤ m ∧
      ∃ g : pullback f₁ e ⟶ ∐ fun _ : Fin m ↦ U, g.IsPurelyInseparable ∧
        g ≫ Sigma.desc (fun _ ↦ 𝟙 U) = pullback.snd f₁ e) :
    ∃ (U : Scheme.{u}) (e : U ⟶ Y₂), Etale e ∧ Nonempty U ∧ ∃ m : ℕ, 1 ≤ m ∧
      ∃ g : pullback f₂ e ⟶ ∐ fun _ : Fin m ↦ U, g.IsPurelyInseparable ∧
        g ≫ Sigma.desc (fun _ ↦ 𝟙 U) = pullback.snd f₂ e := by
  obtain ⟨U, e, he, hU, m, hm, g, hg, hge⟩ := H
  have h' : IsPullback (pullback.fst f₁ e ≫ i) (pullback.snd f₁ e) f₂ (e ≫ j) :=
    ((IsPullback.of_hasPullback f₁ e).flip.paste_vert h.flip).flip
  refine ⟨U, e ≫ j, inferInstance, hU, m, hm, h'.isoPullback.inv ≫ g,
    (Scheme.Hom.IsPurelyInseparable.of_isIso _).comp hg, ?_⟩
  rw [Category.assoc, hge, IsPullback.isoPullback_inv_snd]

/-- The generic factorization for `Spec A ⟶ Spec B`, `B → A` a finite injective extension of
domains. -/
theorem exists_etale_isPurelyInseparable_SpecMap (B A : Type u) [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [Algebra B A] [FaithfulSMul B A] [Module.Finite B A] :
    ∃ (U : Scheme.{u}) (e : U ⟶ Spec (.of B)), Etale e ∧ Nonempty U ∧ ∃ m : ℕ, 1 ≤ m ∧
      ∃ g : pullback (Spec.map (CommRingCat.ofHom (algebraMap B A))) e ⟶ ∐ fun _ : Fin m ↦ U,
        g.IsPurelyInseparable ∧ g ≫ Sigma.desc (fun _ ↦ 𝟙 U) =
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B A))) e := by
  obtain ⟨B', _, _, hB', _, m, p, hm, _, φ, hφ, _, hφe⟩ :=
    Algebra.exists_etale_finite_isPRadical_pi B A
  let ι := ULift.{u} (Fin m)
  let ε : Fin m ≃ ι := Equiv.ulift.symm
  let σ := sigmaSpec (fun _ : ι ↦ CommRingCat.of B')
  let ψ : CommRingCat.of (ι → B') ⟶ CommRingCat.of (Fin m → B') :=
    CommRingCat.ofHom (RingEquiv.piCongrLeft (fun _ ↦ B') ε).symm.toRingHom
  have : IsIso ψ := (RingEquiv.piCongrLeft (fun _ ↦ B') ε).symm.toCommRingCatIso.isIso_hom
  have hσ : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap B' (ι → B'))) =
      Sigma.desc (fun _ ↦ 𝟙 (Spec (.of B'))) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [ι_sigmaSpec_assoc, Sigma.ι_desc, ← Spec.map_comp, ← Spec.map_id]
    rfl
  have hε : (Sigma.reindex ε (fun _ : ι ↦ Spec (.of B'))).inv ≫
      Sigma.desc (fun _ : Fin m ↦ 𝟙 (Spec (.of B'))) = Sigma.desc (fun _ ↦ 𝟙 (Spec (.of B'))) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨j, rfl⟩ := ε.surjective i
    erw [Sigma.ι_reindex_inv_assoc, Sigma.ι_desc, Sigma.ι_desc]
  have hPI : (Spec.map (CommRingCat.ofHom φ)).IsPurelyInseparable :=
    isPurelyInseparable_SpecMap_of_isPRadical (R := .of (Fin m → B')) (S := .of (A ⊗[B] B'))
      (CommRingCat.ofHom φ) p hφ
  refine ⟨Spec (.of B'), Spec.map (CommRingCat.ofHom (algebraMap B B')), ?_, ?_, m, hm,
    (pullbackSpecIso B A B').hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ Spec.map ψ ≫ inv σ ≫
      (Sigma.reindex ε (fun _ : ι ↦ Spec (.of B'))).inv, ?_, ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap).mpr hB')
  · exact inferInstanceAs (Nonempty (PrimeSpectrum B'))
  · exact (Scheme.Hom.IsPurelyInseparable.of_isIso _).comp
      (hPI.comp (Scheme.Hom.IsPurelyInseparable.of_isIso _))
  · simp only [Category.assoc]
    erw [hε]
    rw [← hσ, IsIso.inv_hom_id_assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← pullbackSpecIso_hom_snd]
    congr 2
    ext1
    exact hφe

/-- **Generic factorization of a finite surjective morphism.** Let `f : X ⟶ Y` be a finite
surjective morphism of integral schemes. There are a nonempty scheme `U` with an étale morphism
`e : U ⟶ Y`, an integer `m ≥ 1` and a purely inseparable morphism `g : X ×[Y] U ⟶ ∐ᵢ₌₁ᵐ U`
whose composite with the fold map `∐ᵢ₌₁ᵐ U ⟶ U` is the projection `X ×[Y] U ⟶ U`. -/
@[weil "lem_fk104_finite_morphism_generic_factorization_purely_inseparable"]
theorem IsFinite.exists_etale_isPurelyInseparable_comp_sigmaDesc_eq_snd {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Surjective f] [IsIntegral X] [IsIntegral Y] :
    ∃ (U : Scheme.{u}) (e : U ⟶ Y), Etale e ∧ Nonempty U ∧ ∃ m : ℕ, 1 ≤ m ∧
      ∃ g : pullback f e ⟶ ∐ fun _ : Fin m ↦ U, g.IsPurelyInseparable ∧
        g ≫ Sigma.desc (fun _ ↦ 𝟙 U) = pullback.snd f e := by
  obtain ⟨y⟩ := ‹IsIntegral Y›.nonempty
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  have hV' : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  obtain ⟨x, hx⟩ := f.surjective y
  have : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, by simpa [hx] using hyV⟩⟩
  have : IsAffine V := hV
  have : IsAffine (f ⁻¹ᵁ V) := hV'
  refine exists_etale_isPurelyInseparable_of_isPullback
    (isPullback_morphismRestrict f V).flip ?_
  let φ := (f ∣_ V).appTop
  have hsq : IsPullback (f ⁻¹ᵁ V).toScheme.isoSpec.inv (Spec.map φ) (f ∣_ V)
      V.toScheme.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality _).symm⟩
  refine exists_etale_isPurelyInseparable_of_isPullback hsq ?_
  algebraize [φ.hom]
  have : Module.Finite Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := (f ∣_ V).finite_appTop
  have : FaithfulSMul Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := by
    have e : Spec.map φ = (f ⁻¹ᵁ V).toScheme.isoSpec.inv ≫ f ∣_ V ≫ V.toScheme.isoSpec.hom := by
      rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    have : Surjective (f ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : Surjective (Spec.map φ) := e ▸ inferInstance
    obtain ⟨q, hq⟩ := (Spec.map φ).surjective (⊥ : PrimeSpectrum Γ(V, ⊤))
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ((injective_iff_map_eq_zero _).mpr ?_)
    intro b hb
    have : b ∈ (PrimeSpectrum.comap φ.hom q).asIdeal := by
      change φ.hom b ∈ q.asIdeal
      exact hb ▸ q.asIdeal.zero_mem
    rw [show PrimeSpectrum.comap φ.hom q = ⊥ from hq] at this
    exact this
  exact exists_etale_isPurelyInseparable_SpecMap Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤)

end AlgebraicGeometry
