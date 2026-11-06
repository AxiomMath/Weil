module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.Defs
public import WeilFrontier.Defs.RingTheory.TensorProduct.Quotient
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Maximal ideals of a finite algebra base changed to a strict Henselization

Let `A` be a local ring, `A → B` a finite ring homomorphism, `k` a separably closed field with a
local homomorphism `φ : A → k`, and `(Ã, ψ)` the Henselization of `A` with respect to `φ`, so that
`Ã` is a strict Henselization of `A`. Put `T = Ã ⊗[A] B`. Every `A`-algebra homomorphism
`σ : B → k` gives a ring homomorphism `χ_σ : T → k`, `a ⊗ b ↦ ψ a * σ b`. When `k` is large
enough for `A → B`, the map `σ ↦ ker χ_σ` is a bijection from `B →ₐ[A] k` onto the maximal
ideals of `T`.

## Main results

* `IsLocalRing.IsHenselizationAlong.isMaximal_ker_productMap`: the kernel of `χ_σ` is a maximal
  ideal.
* `IsLocalRing.IsHenselizationAlong.bijective_ker_productMap`: `σ ↦ ker χ_σ` is a bijection onto
  the maximal spectrum of `Ã ⊗[A] B`.

## Implementation notes

The proof differs from the source's. Homomorphisms `B → k` over `A` are the same as
homomorphisms `T → k` over `Ã`. Injectivity: two such homomorphisms with the same kernel `M`
factor through the field `T ⧸ M`, which is algebraic over the separably closed residue field
of `Ã`, hence purely inseparable over it, and so has at most one embedding into `k` over it.
Surjectivity: for a maximal ideal `M` the field `T ⧸ M` and `k` embed compatibly into a residue
field `Ω` of `k ⊗[Ã] (T ⧸ M)`; the image of `B` in `Ω` is the image of `k ⊗[A] B ⧸ 𝔫` (with `𝔫`
the contraction of `M` to `B`), which is `k` because `k` is large enough for `A → B`. This
gives `σ : B → k` with `χ_σ` inducing `T ⧸ M → Ω`, whose kernel is `M`.

The source assumes `A` noetherian; the proof does not use it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w u₁ v₁

namespace IsLocalRing.IsHenselizationAlong

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type w} [Field k] [Algebra A k]
  [IsLocalHom (algebraMap A k)] {Ã : Type u₁} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã]
  {ψ : Ã →+* k}

/-- The map `ψ : Ã → k` of a Henselization with respect to `φ = algebraMap A k`, as an
`A`-algebra homomorphism. -/
def toAlgHom (h : IsHenselizationAlong (algebraMap A k) Ã ψ) : Ã →ₐ[A] k :=
  { ψ with commutes' := h.ψ_algebraMap }

@[simp]
theorem toAlgHom_apply (h : IsHenselizationAlong (algebraMap A k) Ã ψ) (a : Ã) :
    h.toAlgHom a = ψ a :=
  rfl

/-- A ring homomorphism to `k` from an integral `Ã`-algebra, extending `ψ`, has maximal kernel. -/
theorem isMaximal_ker_of_comp_eq (h : IsHenselizationAlong (algebraMap A k) Ã ψ)
    {T : Type v₁} [CommRing T] [Algebra Ã T] [Algebra.IsIntegral Ã T] (χ : T →+* k)
    (hχ : χ.comp (algebraMap Ã T) = ψ) : (RingHom.ker χ).IsMaximal := by
  have := RingHom.ker_isPrime χ
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Ã) _ ?_
  rw [RingHom.comap_ker, hχ, h.ker_ψ]
  exact maximalIdeal.isMaximal Ã

/-- The contraction to `Ã` of the kernel of a ring homomorphism extending `ψ` is the maximal
ideal of `Ã`. -/
theorem comap_ker_of_comp_eq (h : IsHenselizationAlong (algebraMap A k) Ã ψ)
    {T : Type v₁} [CommRing T] [Algebra Ã T] (χ : T →+* k)
    (hχ : χ.comp (algebraMap Ã T) = ψ) :
    (RingHom.ker χ).comap (algebraMap Ã T) = maximalIdeal Ã := by
  rw [RingHom.comap_ker, hχ, h.ker_ψ]

/-- Two ring homomorphisms to `k` from an integral `Ã`-algebra, extending `ψ` and with the same
kernel, are equal: the residue field at the common kernel is purely inseparable over the
separably closed residue field of `Ã`. -/
theorem eq_of_ker_eq [IsSepClosed k] (h : IsHenselizationAlong (algebraMap A k) Ã ψ)
    {T : Type v₁} [CommRing T] [Algebra Ã T] [Algebra.IsIntegral Ã T] {χ₁ χ₂ : T →+* k}
    (h₁ : χ₁.comp (algebraMap Ã T) = ψ) (h₂ : χ₂.comp (algebraMap Ã T) = ψ)
    (hker : RingHom.ker χ₁ = RingHom.ker χ₂) : χ₁ = χ₂ := by
  set M := RingHom.ker χ₁ with hM
  have := h.isMaximal_ker_of_comp_eq χ₁ h₁
  have hle : maximalIdeal Ã ≤ M.comap (algebraMap Ã T) := (h.comap_ker_of_comp_eq χ₁ h₁).ge
  have := h.isLocalHom_ψ
  have := h.isSepClosed_residueField
  let : Field (T ⧸ M) := Ideal.Quotient.field M
  let : Algebra (ResidueField Ã) (T ⧸ M) := Ideal.Quotient.algebraQuotientOfLEComap hle
  let : Algebra (ResidueField Ã) k := (ResidueField.lift ψ).toAlgebra
  have : IsScalarTower Ã (ResidueField Ã) (T ⧸ M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral (ResidueField Ã) (T ⧸ M) := Algebra.IsIntegral.tower_top Ã
  let f : ((T ⧸ M) →ₐ[ResidueField Ã] k) → T →+* k := fun g =>
    g.toRingHom.comp (Ideal.Quotient.mk M)
  have hf : ∀ (χ : T →+* k) (hχ : χ.comp (algebraMap Ã T) = ψ) (hχM : M ≤ RingHom.ker χ),
      ∃ g : (T ⧸ M) →ₐ[ResidueField Ã] k, f g = χ := fun χ hχ hχM =>
    ⟨{ Ideal.Quotient.lift M χ hχM with
        commutes' := fun x => by
          obtain ⟨a, rfl⟩ := residue_surjective x
          change χ (algebraMap Ã T a) = ResidueField.lift ψ (residue Ã a)
          rw [ResidueField.lift_residue_apply, ← hχ, RingHom.comp_apply] },
      RingHom.ext fun _ => rfl⟩
  obtain ⟨g₁, hg₁⟩ := hf χ₁ h₁ le_rfl
  obtain ⟨g₂, hg₂⟩ := hf χ₂ h₂ hker.le
  rw [← hg₁, ← hg₂, Subsingleton.elim g₁ g₂]

section TensorProduct

variable {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- The kernel of `χ_σ : Ã ⊗[A] B → k`, `a ⊗ b ↦ ψ a * σ b`, is a maximal ideal. -/
@[weil "lem_fk103_strict_henselization_tensor_maximal_ideals_bijection"]
theorem isMaximal_ker_productMap (h : IsHenselizationAlong (algebraMap A k) Ã ψ)
    (σ : B →ₐ[A] k) :
    (RingHom.ker (Algebra.TensorProduct.productMap h.toAlgHom σ)).IsMaximal :=
  h.isMaximal_ker_of_comp_eq (T := Ã ⊗[A] B)
    (Algebra.TensorProduct.productMap h.toAlgHom σ).toRingHom
    (RingHom.ext fun a => by simp)

/-- Every maximal ideal of `Ã ⊗[A] B` is the kernel of `χ_σ` for some `σ : B →ₐ[A] k`, when `k`
is large enough for `A → B`. -/
theorem exists_ker_productMap_eq (h : IsHenselizationAlong (algebraMap A k) Ã ψ)
    (hk : IsLargeEnoughFor A B k) (M : Ideal (Ã ⊗[A] B)) [M.IsMaximal] :
    ∃ σ : B →ₐ[A] k, RingHom.ker (Algebra.TensorProduct.productMap h.toAlgHom σ) = M := by
  have hle : maximalIdeal Ã ≤ M.comap (algebraMap Ã (Ã ⊗[A] B)) :=
    maximalIdeal_le_comap_of_isMaximal (A := Ã) M
  have hcomap : M.comap (algebraMap Ã (Ã ⊗[A] B)) = maximalIdeal Ã :=
    (le_maximalIdeal (Ideal.IsMaximal.under Ã M).ne_top).antisymm hle
  have := h.isLocalHom_ψ
  have := h.isLocalHom_algebraMap
  let : Field (Ã ⊗[A] B ⧸ M) := Ideal.Quotient.field M
  let : Algebra (ResidueField Ã) (Ã ⊗[A] B ⧸ M) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have : IsScalarTower Ã (ResidueField Ã) (Ã ⊗[A] B ⧸ M) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra Ã k := ψ.toAlgebra
  let : Algebra (ResidueField Ã) k := (ResidueField.lift ψ).toAlgebra
  have : IsScalarTower Ã (ResidueField Ã) k :=
    IsScalarTower.of_algebraMap_eq fun a => (ResidueField.lift_residue_apply ψ a).symm
  -- a field `Ω` into which both `k` and `T ⧸ M` embed over `Ã`
  have : Nontrivial (k ⊗[Ã] (Ã ⊗[A] B ⧸ M)) := by
    have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      (ResidueField Ã) k (Ã ⊗[A] B ⧸ M) (algebraMap (ResidueField Ã) k).injective
      (algebraMap (ResidueField Ã) (Ã ⊗[A] B ⧸ M)).injective
    exact (tensorEquivTensorResidueField (A := Ã) k (Ã ⊗[A] B ⧸ M)).toEquiv.nontrivial
  obtain ⟨𝔐', h𝔐'⟩ := Ideal.exists_maximal (k ⊗[Ã] (Ã ⊗[A] B ⧸ M))
  let : Field (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐') := Ideal.Quotient.field 𝔐'
  let ρ : Ã ⊗[A] B →+* k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐' :=
    (Ideal.Quotient.mk 𝔐').comp
      (((Algebra.TensorProduct.includeRight :
        (Ã ⊗[A] B ⧸ M) →ₐ[Ã] k ⊗[Ã] (Ã ⊗[A] B ⧸ M)) : _ →+* _).comp (Ideal.Quotient.mk M))
  have hρM : M ≤ RingHom.ker ρ := fun x hx => by
    simp [ρ, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have hρker : RingHom.ker ρ = M :=
    (Ideal.IsMaximal.eq_of_le ‹M.IsMaximal› (RingHom.ker_ne_top ρ) hρM).symm
  have hρÃ : ∀ a : Ã, ρ (algebraMap Ã _ a) =
      algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐') (ψ a) := fun a => by
    change Ideal.Quotient.mk 𝔐' ((1 : k) ⊗ₜ (algebraMap Ã (Ã ⊗[A] B ⧸ M) a)) =
      Ideal.Quotient.mk 𝔐' (ψ a ⊗ₜ 1)
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  -- the contraction `𝔫` of `M` to `B`
  let ιB : B →+* Ã ⊗[A] B := (Algebra.TensorProduct.includeRight : B →ₐ[A] Ã ⊗[A] B)
  have hιB : ∀ a : A, ιB (algebraMap A B a) = algebraMap Ã _ (algebraMap A Ã a) := fun a => by
    simp [ιB, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
      TensorProduct.smul_tmul']
  let 𝔫 := M.comap ιB
  have : 𝔫.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) 𝔫 ?_
    have e1 : 𝔫.comap (algebraMap A B) =
        (M.comap (algebraMap Ã (Ã ⊗[A] B))).comap (algebraMap A Ã) := by
      rw [Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      exact RingHom.ext hιB
    rw [e1, hcomap, maximalIdeal_comap]
    exact maximalIdeal.isMaximal A
  -- the map `B ⧸ 𝔫 → Ω`
  let ρB : B →+* k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐' := ρ.comp ιB
  let ρF : B ⧸ 𝔫 →+* k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐' :=
    Ideal.Quotient.lift 𝔫 ρB fun b hb => hρM hb
  have hρBA : ∀ a : A, ρB (algebraMap A B a) =
      algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐') (algebraMap A k a) := fun a => by
    rw [RingHom.comp_apply, hιB, hρÃ, h.ψ_algebraMap]
  let ρFA : B ⧸ 𝔫 →ₐ[A] k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐' :=
    { ρF with
      commutes' := fun a => (hρBA a).trans (IsScalarTower.algebraMap_apply A k _ a).symm }
  let g : k ⊗[A] (B ⧸ 𝔫) →ₐ[k] k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐' :=
    Algebra.TensorProduct.lift (Algebra.ofId k _) ρFA fun _ _ => Commute.all _ _
  have : (RingHom.ker g).IsMaximal := by
    have := RingHom.ker_isPrime g
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := k) _ ?_
    have e2 : (RingHom.ker g).comap (algebraMap k (k ⊗[A] (B ⧸ 𝔫))) = ⊥ := by
      change (RingHom.ker g.toRingHom).comap _ = ⊥
      rw [RingHom.comap_ker]
      refine (RingHom.injective_iff_ker_eq_bot _).1 fun x y hxy =>
        (algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐')).injective ?_
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes] using hxy
    rw [e2]
    exact Ideal.bot_isMaximal
  have hbij := hk.bijective 𝔫 (RingHom.ker g)
  have hrange : ∀ y, g y ∈ (algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐')).range := fun y => by
    obtain ⟨c, hc⟩ := hbij.2 (Ideal.Quotient.mk _ y)
    refine ⟨c, ?_⟩
    have : g (algebraMap k _ c) = g y := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]
      exact Ideal.Quotient.eq.1 hc
    rw [← this, AlgHom.commutes]
  have hρBrange : ρB.range ≤ (algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐')).range := by
    rintro _ ⟨b, rfl⟩
    have := hrange (1 ⊗ₜ Ideal.Quotient.mk 𝔫 b)
    rwa [Algebra.TensorProduct.lift_tmul, map_one, one_mul] at this
  -- `σ₀ : B → k` with `ρB = algebraMap k Ω ∘ σ₀`
  let e := RingEquiv.ofBijective (algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐')).rangeRestrict
    ⟨fun x y hxy => (algebraMap k _).injective (congrArg Subtype.val hxy),
      RingHom.rangeRestrict_surjective _⟩
  let σ₀ : B →+* k := (e.symm : _ →+* k).comp (ρB.codRestrict _ fun b => hρBrange ⟨b, rfl⟩)
  have hσ₀ : ∀ b, algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐') (σ₀ b) = ρB b := fun b =>
    congrArg Subtype.val (e.apply_symm_apply ⟨ρB b, hρBrange ⟨b, rfl⟩⟩)
  let σ : B →ₐ[A] k :=
    { σ₀ with
      commutes' := fun a => (algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐')).injective (by
        change algebraMap k _ (σ₀ (algebraMap A B a)) = _
        rw [hσ₀, hρBA]) }
  refine ⟨σ, ?_⟩
  have hχ : (algebraMap k (k ⊗[Ã] (Ã ⊗[A] B ⧸ M) ⧸ 𝔐')).comp
      (Algebra.TensorProduct.productMap h.toAlgHom σ : _ →+* k) = ρ := by
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hab : a ⊗ₜ[A] b = algebraMap Ã _ a * ιB b := by
        simp [ιB, Algebra.TensorProduct.algebraMap_apply]
      rw [RingHom.comp_apply, AlgHom.coe_toRingHom, Algebra.TensorProduct.productMap_apply_tmul,
        map_mul, toAlgHom_apply, hab, map_mul, hρÃ]
      exact congrArg _ (hσ₀ b)
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← hρker, ← hχ, RingHom.ker_comp_of_injective _ (algebraMap k _).injective]
  rfl

/-- **Maximal ideals of `Ã ⊗[A] B`.** Let `A` be a local ring, `A → B` finite, `k` a separably
closed field with a local homomorphism `A → k`, large enough for `A → B`, and `(Ã, ψ)` the
Henselization of `A` with respect to `A → k`. For `σ : B →ₐ[A] k` let `χ_σ : Ã ⊗[A] B → k` be
`a ⊗ b ↦ ψ a * σ b`. Then `σ ↦ ker χ_σ` is a bijection from `B →ₐ[A] k` onto the maximal
ideals of `Ã ⊗[A] B`. -/
@[weil "lem_fk103_strict_henselization_tensor_maximal_ideals_bijection"]
theorem bijective_ker_productMap [IsSepClosed k] (h : IsHenselizationAlong (algebraMap A k) Ã ψ)
    (hk : IsLargeEnoughFor A B k) :
    Function.Bijective fun σ : B →ₐ[A] k =>
      (⟨RingHom.ker (Algebra.TensorProduct.productMap h.toAlgHom σ),
        h.isMaximal_ker_productMap σ⟩ : MaximalSpectrum (Ã ⊗[A] B)) := by
  refine ⟨fun σ₁ σ₂ he => ?_, fun M => ?_⟩
  · have hcomp : ∀ σ : B →ₐ[A] k, (Algebra.TensorProduct.productMap h.toAlgHom σ :
        _ →+* k).comp (algebraMap Ã (Ã ⊗[A] B)) = ψ := fun σ => RingHom.ext fun a => by simp
    have := h.eq_of_ker_eq (hcomp σ₁) (hcomp σ₂) (congrArg MaximalSpectrum.asIdeal he)
    ext b
    simpa using RingHom.congr_fun this (1 ⊗ₜ b)
  · obtain ⟨σ, hσ⟩ := h.exists_ker_productMap_eq hk M.asIdeal
    exact ⟨σ, MaximalSpectrum.ext hσ⟩

end TensorProduct

end IsLocalRing.IsHenselizationAlong

