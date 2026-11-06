module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import WeilFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.TensorProduct

/-!
# Finite base change of the henselian polynomial ring

Let `A` be a local ring, `A'` a local `A`-algebra which is finite as an `A`-module, and let
`T = (T_i)_{i ∈ σ}` be a family of indeterminates. Write `A{T}` for the henselization of
`A[T]` at the origin `(𝔪, T)` (`MvPolynomial.IsHenselianPolynomialRing`). Then
`A{T} ⊗_A A' ≅ A'{T}` as `A'[T]`-algebras.

The proof uses only the universal property of the henselization. Since `A'` is finite over `A`,
the ring `A{T} ⊗_A A'` is finite over the henselian local ring `A{T}`. Its maximal ideals lie over
the maximal ideal of `A{T}`, whose residue field is that of `A`, and over the maximal ideal of
`A'`; such a prime is unique, so `A{T} ⊗_A A'` is local, and it is henselian, being a finite local
algebra over a henselian local ring. The map `A'[T] → A{T} ⊗_A A'` is then local at the origin, so
it extends to a local map `A'{T} → A{T} ⊗_A A'`; in the other direction, the local map
`A{T} → A'{T}` and `A' → A'{T}` induce `A{T} ⊗_A A' → A'{T}`. Both composites are local and
compatible with the structure maps out of `A'[T]_{(𝔪', T)}`, resp. `A{T}` and `A'`, so they are
the identity by the uniqueness in the universal property.

## Main results

* `MvPolynomial.exists_ringEquiv_tensorProduct_of_isHenselianPolynomialRing`:
  `A{T} ⊗_A A' ≅ A'{T}`, compatibly with the maps from `A'[T]`.

## Implementation notes

The source assumes `A` henselian and noetherian and takes one indeterminate `t`; neither
hypothesis is used, and the statement holds for any family of indeterminates (`σ = Fin 1` is the
source's case). The `A'[T]`-algebra structure of `A{T} ⊗_A A'` is the map
`A'[T] → A{T} ⊗_A A'` sending `a'` to `1 ⊗ a'` and `T_i` to `T_i ⊗ 1`; that the isomorphism is
one of `A'[T]`-algebras is the compatibility of the isomorphism with this map and the structure
map `A'[T] → A'[T]_{(𝔪', T)} → A'{T}`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
-/

public section

open IsLocalRing
open scoped TensorProduct

universe u u' v w w'

namespace MvPolynomial

/-- The universal property of a henselization `Rh` of `R`, in ring-homomorphism form: every local
homomorphism `φ : R → C` to a henselian local ring extends uniquely to a local `Rh → C`. -/
private theorem exists_unique_lift_of_isHenselization {R : Type*} [CommRing R] [IsLocalRing R]
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh] {C : Type*} [CommRing C] [HenselianLocalRing C]
    (φ : R →+* C) [IsLocalHom φ] :
    ∃ f : Rh →+* C, IsLocalHom f ∧ f.comp (algebraMap R Rh) = φ ∧
      ∀ g : Rh →+* C, IsLocalHom g → g.comp (algebraMap R Rh) = φ → g = f := by
  let := φ.toAlgebra
  have : IsLocalHom (algebraMap R C) := ‹IsLocalHom φ›
  have : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  obtain ⟨f, hf, hu⟩ := StacksDraft.existsUnique_isLocalHom_of_indEtale (C := C)
    (StacksDraft.indEtale_of_isHenselization (ResidueField R) (Rh := Rh))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := Rh)).2
  refine ⟨f.toRingHom, ⟨hf.map_nonunit⟩, RingHom.ext f.commutes, fun g hg hgc => ?_⟩
  have := hu { g with commutes' := RingHom.congr_fun hgc } ⟨hg.map_nonunit⟩
  exact RingHom.ext fun x => AlgHom.congr_fun this x

/-- A finite algebra between local rings has a local structure map. -/
private theorem isLocalHom_algebraMap_of_finite {A A' : Type*} [CommRing A] [IsLocalRing A]
    [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Finite A A'] :
    IsLocalHom (algebraMap A A') := by
  have : ((maximalIdeal A').comap (algebraMap A A')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  exact ((local_hom_TFAE (algebraMap A A')).out 1 5).mpr (eq_maximalIdeal this)

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type v}

/-- The structure map `A → A[T]_{(𝔪, T)}` is local. -/
private theorem isLocalHom_algebraMap_localizationAtOrigin :
    IsLocalHom (algebraMap A (LocalizationAtOrigin A σ)) := by
  have h : (originResidue A σ).comp (algebraMap A (LocalizationAtOrigin A σ)) = residue A := by
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A (MvPolynomial σ A),
      MvPolynomial.algebraMap_eq, originResidue_algebraMap, constantCoeff_C]
  have : IsLocalHom ((originResidue A σ).comp (algebraMap A (LocalizationAtOrigin A σ))) := by
    rw [h]; infer_instance
  exact isLocalHom_of_comp _ (originResidue A σ)

/-- The residue field of `A{T}` is reached from `A`. -/
private theorem exists_residue_eq_of_isHenselianPolynomialRing {B : Type w} [CommRing B]
    [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B] [Algebra A B]
    [IsScalarTower A (LocalizationAtOrigin A σ) B] (hB : IsHenselianPolynomialRing A σ B)
    (b : B) : ∃ a : A, residue B b = residue B (algebraMap A B a) := by
  have : IsLocalHom (algebraMap (LocalizationAtOrigin A σ) B) :=
    IsHenselization.isLocalHom (L := ResidueField (LocalizationAtOrigin A σ))
  obtain ⟨y, hy⟩ := (IsHenselization.residueField_map_bijective
    (R := LocalizationAtOrigin A σ) (Rh := B)).2 (residue B b)
  obtain ⟨p, rfl⟩ := residue_surjective y
  obtain ⟨a, ha⟩ := residue_surjective (originResidue A σ p)
  have hc : originResidue A σ (algebraMap A (LocalizationAtOrigin A σ) a) = residue A a := by
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial σ A),
      MvPolynomial.algebraMap_eq, originResidue_algebraMap, constantCoeff_C]
  have h0 : originResidue A σ (p - algebraMap A (LocalizationAtOrigin A σ) a) = 0 := by
    rw [map_sub, hc, ← ha, sub_self]
  have hm : p - algebraMap A (LocalizationAtOrigin A σ) a ∈
      maximalIdeal (LocalizationAtOrigin A σ) :=
    (mem_maximalIdeal _).2 fun hu => not_isUnit_zero (h0 ▸ hu.map (originResidue A σ))
  have hr : residue _ p = residue _ (algebraMap A (LocalizationAtOrigin A σ) a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hm
  refine ⟨a, ?_⟩
  rw [← hy, hr, ResidueField.map_residue, ← IsScalarTower.algebraMap_apply]

variable {A' : Type u'} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Finite A A']

/-- **Finite base change of the henselian polynomial ring.** Let `A` be a local ring, `A'` a local
`A`-algebra finite as an `A`-module, `B = A{T}` and `B' = A'{T}` the henselizations of the
polynomial rings at the origin. Then `B ⊗_A A' ≅ B'` as `A'[T]`-algebras: there is a ring
isomorphism `e : B ⊗_A A' ≃ B'` which carries the image of `p ∈ A'[T]` in `B ⊗_A A'` (under
`a' ↦ 1 ⊗ a'`, `T_i ↦ T_i ⊗ 1`) to the image of `p` in `B'`. -/
@[weil "lem_fk107_henselian_line_base_change_finite"]
theorem exists_ringEquiv_tensorProduct_of_isHenselianPolynomialRing
    {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
    [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A σ) B]
    (hB : IsHenselianPolynomialRing A σ B)
    {B' : Type w'} [CommRing B'] [IsLocalRing B'] [Algebra (LocalizationAtOrigin A' σ) B']
    (hB' : IsHenselianPolynomialRing A' σ B') :
    ∃ e : B ⊗[A] A' ≃+* B', ∀ p : MvPolynomial σ A',
      e (eval₂Hom (Algebra.TensorProduct.includeRight : A' →ₐ[A] B ⊗[A] A').toRingHom
        (fun i => algebraMap (LocalizationAtOrigin A σ) B
          (algebraMap _ _ (X i : MvPolynomial σ A)) ⊗ₜ 1) p) =
        algebraMap (LocalizationAtOrigin A' σ) B' (algebraMap _ _ p) := by
  classical
  have := hB
  have := hB'
  set P := LocalizationAtOrigin A σ
  set P' := LocalizationAtOrigin A' σ
  set T := B ⊗[A] A'
  have hPB : IsLocalHom (algebraMap P B) := IsHenselization.isLocalHom (L := ResidueField P)
  have hPB' : IsLocalHom (algebraMap P' B') := IsHenselization.isLocalHom (L := ResidueField P')
  have : HenselianLocalRing B := IsHenselization.henselian (R := P) (L := ResidueField P)
  have : HenselianLocalRing B' := IsHenselization.henselian (R := P') (L := ResidueField P')
  have hAA' : IsLocalHom (algebraMap A A') := isLocalHom_algebraMap_of_finite
  have hAP : IsLocalHom (algebraMap A P) := isLocalHom_algebraMap_localizationAtOrigin
  have hAB : IsLocalHom (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A P B]; infer_instance
  -- the map `A[T]_{(𝔪, T)} → A'[T]_{(𝔪', T)}`
  have hAA'm : (maximalIdeal A').comap (algebraMap A A') = maximalIdeal A :=
    ((local_hom_TFAE (algebraMap A A')).out 1 5).mp hAA'
  have hcomap : originIdeal A σ = (originIdeal A' σ).comap (map (algebraMap A A')) := by
    ext f
    change constantCoeff f ∈ maximalIdeal A ↔
      constantCoeff (map (algebraMap A A') f) ∈ maximalIdeal A'
    rw [constantCoeff_map, ← hAA'm, Ideal.mem_comap]
  let ι : P →+* P' := Localization.localRingHom _ _ (map (algebraMap A A')) hcomap
  have hι (f : MvPolynomial σ A) :
      ι (algebraMap _ P f) = algebraMap _ P' (map (algebraMap A A') f) :=
    Localization.localRingHom_to_map _ _ _ hcomap f
  -- the map `A' → A'{T}` and the local map `A{T} → A'{T}`
  let ψ' : A' →+* B' := (algebraMap P' B').comp ((algebraMap (MvPolynomial σ A') P').comp C)
  obtain ⟨f, hf, hfc, -⟩ := exists_unique_lift_of_isHenselization (Rh := B) (C := B')
    ((algebraMap P' B').comp ι)
  let := (ψ'.comp (algebraMap A A')).toAlgebra
  let fA : B →ₐ[A] B' :=
    { f with
      commutes' := fun a => by
        change f (algebraMap A B a) = ψ' (algebraMap A A' a)
        rw [IsScalarTower.algebraMap_apply A P B, ← RingHom.comp_apply, hfc,
          IsScalarTower.algebraMap_apply A (MvPolynomial σ A) P, MvPolynomial.algebraMap_eq,
          RingHom.comp_apply, hι, map_C]
        rfl }
  let gA : A' →ₐ[A] B' := { ψ' with commutes' := fun _ => rfl }
  let Φ : T →+* B' := (Algebra.TensorProduct.lift fA gA fun _ _ => .all _ _).toRingHom
  have hΦ (b : B) (a' : A') : Φ (b ⊗ₜ a') = f b * ψ' a' := Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have : Nontrivial T := Φ.domain_nontrivial
  -- the maximal ideals of `T` lie over `𝔪_B` and `𝔪_{A'}`
  have hBm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    ((local_hom_TFAE (algebraMap A B)).out 1 5).mp hAB
  have hMB (M : Ideal T) [M.IsMaximal] : M.comap (algebraMap B T) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hRA : (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom.comp (algebraMap A A') =
      (algebraMap B T).comp (algebraMap A B) := by
    rw [← IsScalarTower.algebraMap_eq]
    exact (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).comp_algebraMap
  have hMA' (M : Ideal T) [M.IsMaximal] :
      M.comap (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom = maximalIdeal A' := by
    have hc : (M.comap (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom).comap
        (algebraMap A A') = maximalIdeal A := by
      rw [Ideal.comap_comap, hRA, ← Ideal.comap_comap, hMB, hBm]
    have : (M.comap (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hc]; infer_instance)
    exact eq_maximalIdeal this
  have hsurj : (algebraMap A (ResidueField B)).SurjectiveOnStalks := by
    refine RingHom.surjectiveOnStalks_of_surjective fun x => ?_
    obtain ⟨b, rfl⟩ := residue_surjective x
    obtain ⟨a, ha⟩ := exists_residue_eq_of_isHenselianPolynomialRing hB b
    exact ⟨a, by rw [ha, IsScalarTower.algebraMap_apply A B (ResidueField B),
      ResidueField.algebraMap_eq]⟩
  have : IsLocalRing T := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal T
    refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => ?_⟩
    exact StacksDraft.tensorProduct_prime_eq_of_residue hsurj N M (hMB N) (hMB M)
      ((hMA' N).trans (hMA' M).symm)
  have hBT : IsLocalHom (algebraMap B T) :=
    ((local_hom_TFAE (algebraMap B T)).out 1 5).mpr (hMB _)
  have : IsLocalization.AtPrime T (maximalIdeal T) :=
    IsLocalization.self fun x hx => (mem_nonunits_iff.not_left).1 hx
  have : HenselianLocalRing T :=
    HenselianLocalRing.of_isLocalization_atPrime_of_finite (R := B) (S := T) (maximalIdeal T) T
  -- the map `A'[T] → B ⊗_A A'` and its extension `A'[T]_{(𝔪', T)} → B ⊗_A A'`
  let x : σ → T := fun i => algebraMap P B (algebraMap _ _ (X i : MvPolynomial σ A)) ⊗ₜ 1
  let θ : MvPolynomial σ A' →+* T :=
    eval₂Hom (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom x
  have hx (i : σ) : x i ∈ maximalIdeal T := by
    have h1 : algebraMap _ P (X i : MvPolynomial σ A) ∈ maximalIdeal P := by
      refine (IsLocalization.AtPrime.to_map_mem_maximal_iff P (originIdeal A σ) _).2 ?_
      rw [mem_originIdeal, constantCoeff_X]
      exact zero_mem _
    have h2 : algebraMap P B (algebraMap _ P (X i : MvPolynomial σ A)) ∈ maximalIdeal B :=
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h1
        (isUnit_of_map_unit (algebraMap P B) _ hu)
    rw [← hMB (maximalIdeal T)] at h2
    exact h2
  have hθ : (maximalIdeal T).comap θ = originIdeal A' σ := by
    refine ((Ideal.IsMaximal.eq_of_le (originIdeal_isMaximal A' σ)
      (Ideal.comap_ne_top θ (maximalIdeal.isMaximal T).ne_top)) ?_).symm
    rw [originIdeal_eq]
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      have : θ.comp C = (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom :=
        eval₂Hom_comp_C _ _
      rw [this, hMA']
    · rw [idealOfVars, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change θ (X i) ∈ maximalIdeal T
      rw [eval₂Hom_X']
      exact hx i
  have hu : ∀ y : (originIdeal A' σ).primeCompl, IsUnit (θ y) := fun y =>
    notMem_maximalIdeal.mp fun hy => y.2 (by
      have : (y : MvPolynomial σ A') ∈ (maximalIdeal T).comap θ := hy
      rwa [hθ] at this)
  let Ψ : P' →+* T := IsLocalization.lift hu
  have hΨ (p : MvPolynomial σ A') : Ψ (algebraMap _ P' p) = θ p := IsLocalization.lift_eq hu p
  have hΨl : IsLocalHom Ψ := by
    apply ((local_hom_TFAE Ψ).out 1 4).mpr
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (originIdeal A' σ) P',
      Ideal.map_le_iff_le_comap, Ideal.comap_comap, IsLocalization.lift_comp hu, hθ]
  -- `Φ` is local
  have hΦB : Φ.comp (algebraMap B T) = f := by
    ext b
    change Φ (b ⊗ₜ 1) = f b
    rw [hΦ, map_one, mul_one]
  have hΦl : IsLocalHom Φ := by
    apply ((local_hom_TFAE Φ).out 1 5).mpr
    have hc : ((maximalIdeal B').comap Φ).comap (algebraMap B T) = maximalIdeal B := by
      rw [Ideal.comap_comap, hΦB]
      exact ((local_hom_TFAE f).out 1 5).mp hf
    have : ((maximalIdeal B').comap Φ).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hc]; infer_instance)
    exact eq_maximalIdeal this
  -- the local map `A'{T} → B ⊗_A A'`
  obtain ⟨F, hF, hFc, -⟩ := exists_unique_lift_of_isHenselization (Rh := B') (C := T) Ψ
  obtain ⟨g₁, -, -, huB'⟩ := exists_unique_lift_of_isHenselization (Rh := B') (C := B')
    (algebraMap P' B')
  obtain ⟨g₂, -, -, huB⟩ := exists_unique_lift_of_isHenselization (Rh := B) (C := T)
    (Ψ.comp ι)
  have hΦθ : Φ.comp θ = (algebraMap P' B').comp (algebraMap _ P') := by
    refine MvPolynomial.ringHom_ext (fun a' => ?_) (fun i => ?_)
    · change Φ (θ (C a')) = _
      rw [eval₂Hom_C]
      change Φ (1 ⊗ₜ a') = _
      rw [hΦ, map_one, one_mul]
      rfl
    · change Φ (θ (X i)) = _
      rw [eval₂Hom_X', hΦ, map_one, mul_one, ← RingHom.comp_apply f, hfc, RingHom.comp_apply,
        hι, map_X]
      rfl
  have hΦΨ : Φ.comp Ψ = algebraMap P' B' := by
    refine IsLocalization.ringHom_ext (originIdeal A' σ).primeCompl ?_
    rw [RingHom.comp_assoc, IsLocalization.lift_comp hu, hΦθ]
  have h1 : Φ.comp F = RingHom.id B' := by
    have := huB' (Φ.comp F) inferInstance (by rw [RingHom.comp_assoc, hFc, hΦΨ])
    rw [this, ← huB' (RingHom.id B') inferInstance (RingHom.id_comp _)]
  have hιc : ι.comp (algebraMap _ P) = (algebraMap _ P').comp (map (algebraMap A A')) :=
    RingHom.ext hι
  have hΨι : Ψ.comp ι = (algebraMap B T).comp (algebraMap P B) := by
    refine IsLocalization.ringHom_ext (originIdeal A σ).primeCompl ?_
    rw [RingHom.comp_assoc, hιc, ← RingHom.comp_assoc, IsLocalization.lift_comp hu]
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change θ (map _ (C a)) = algebraMap B T (algebraMap P B (algebraMap _ P (C a)))
      rw [map_C, eval₂Hom_C, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (MvPolynomial σ A) P,
        ← IsScalarTower.algebraMap_apply A P B]
      change 1 ⊗ₜ algebraMap A A' a = algebraMap A B a ⊗ₜ 1
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · change θ (map _ (X i)) = algebraMap B T (algebraMap P B (algebraMap _ P (X i)))
      rw [map_X, eval₂Hom_X']
      rfl
  have hFf : F.comp f = algebraMap B T := by
    rw [huB (F.comp f) inferInstance (by rw [RingHom.comp_assoc, hfc, ← RingHom.comp_assoc, hFc]),
      ← huB (algebraMap B T) hBT hΨι.symm]
  have h2 : F.comp Φ = RingHom.id T := by
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, RingHom.id_apply] at hs ht ⊢; rw [hs, ht]
    | tmul b a' =>
      rw [RingHom.comp_apply, hΦ, map_mul, ← RingHom.comp_apply F f, hFf, RingHom.id_apply]
      rw [show ψ' a' = algebraMap P' B' (algebraMap _ P' (C a' : MvPolynomial σ A')) from rfl,
        ← RingHom.comp_apply F, hFc, hΨ, eval₂Hom_C]
      change b ⊗ₜ 1 * 1 ⊗ₜ a' = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨RingEquiv.ofRingHom Φ F h1 h2, fun p => ?_⟩
  change Φ (θ p) = _
  rw [← hΨ, ← RingHom.comp_apply, hΦΨ]

end MvPolynomial
