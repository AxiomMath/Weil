module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.StrictHenselization.StrictHenselizationComparisonMap
public import StacksFrontier.RingTheory.Henselian.StrictHenselization

/-!
# Existence of comparison maps to strict Henselizations

Let `A` be a local ring, `B` an `A`-algebra, `k` a separably closed field, `φ : A → k` a local
homomorphism and `(Ã, φ̃)` a Henselization of `A` with respect to `φ`. For every `A`-algebra
homomorphism `ψ : B → k` there is an `A`-algebra homomorphism `γ_ψ : Ã → B̃_ψ` to the strict
Henselization of `B` at `ψ` with `ψ̃ ∘ γ_ψ = φ̃`. Combining `γ_ψ` with the structure map
`ι_ψ : B → B̃_ψ` gives `Θ_ψ : Ã ⊗_A B → B̃_ψ`, and the product of the `Θ_ψ` is a comparison map
`Θ : Ã ⊗_A B → ∏_ψ B̃_ψ`.

The map `γ_ψ` comes from the universal property of the ind-étale local `A`-algebra `Ã` mapping to
the henselian local ring `B̃_ψ` (Stacks 04GU), applied to the embedding of residue fields
`κ(Ã) ≅ κ_φ ⊆ κ_{ψ_𝔫} ≅ κ(B̃_ψ)` inside `k`: an element of `k` separable over the residue field of
`A` is separable over the residue field of `B_𝔫`, `𝔫 = ker ψ`.

## Main results

* `IsLocalRing.IsHenselizationAlong.exists_algHom_strictHenselizationAt`: the map `γ_ψ`.
* `IsLocalRing.IsHenselizationAlong.exists_isStrictHenselizationComparison`: a comparison map
  exists.

## Implementation notes

The source assumes `A` noetherian and `A → B` finite. Neither is used: the map `A → B_𝔫` is
local because `ψ ∘ (A → B) = φ` is local, and `γ_ψ` is given by the universal property of the
henselization. The `A`-algebra structure on `B̃_ψ` is the composite `A → B → B̃_ψ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3.2
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
-/

public section

open IsLocalRing TensorProduct

universe u v w x

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type v} [Field k] [IsSepClosed k]
  {φ : A →+* k} [IsLocalHom φ] {B : Type w} [CommRing B] [Algebra A B]

omit [IsLocalRing A] [IsSepClosed k] in
/-- For `ψ ∘ (A → B) = φ` with `φ` local, the composite `A → B → B_𝔫`, `𝔫 = ker ψ`, is local. -/
theorem isLocalHom_algebraMap_comp_of_comp_eq (ψ : B →+* k) (hψ : ψ.comp (algebraMap A B) = φ) :
    IsLocalHom ((algebraMap B (Localization.AtPrime (RingHom.ker ψ))).comp (algebraMap A B)) := by
  have hcomp : ψ.liftLocalizationAtKer.comp
      ((algebraMap B (Localization.AtPrime (RingHom.ker ψ))).comp (algebraMap A B)) = φ := by
    rw [← RingHom.comp_assoc, RingHom.liftLocalizationAtKer_comp_algebraMap, hψ]
  have : IsLocalHom (ψ.liftLocalizationAtKer.comp
      ((algebraMap B (Localization.AtPrime (RingHom.ker ψ))).comp (algebraMap A B))) := by
    rw [hcomp]; infer_instance
  exact isLocalHom_of_comp _ ψ.liftLocalizationAtKer

omit [IsSepClosed k] in
/-- The separable closure `κ_φ` of the residue field of `A` in `k` is contained in the separable
closure `κ_{ψ_𝔫}` of the residue field of `B_𝔫`, for `ψ ∘ (A → B) = φ`. -/
theorem residueSeparableClosure_le_of_comp_eq (ψ : B →+* k)
    (hψ : ψ.comp (algebraMap A B) = φ) :
    residueSeparableClosure φ ≤ residueSeparableClosure ψ.liftLocalizationAtKer := by
  intro y hy
  let g := (algebraMap B (Localization.AtPrime (RingHom.ker ψ))).comp (algebraMap A B)
  have := isLocalHom_algebraMap_comp_of_comp_eq ψ hψ
  rw [mem_residueSeparableClosure] at hy ⊢
  let : Algebra (ResidueField A) k := (ResidueField.lift φ).toAlgebra
  let : Algebra (ResidueField (Localization.AtPrime (RingHom.ker ψ))) k :=
    (ResidueField.lift ψ.liftLocalizationAtKer).toAlgebra
  let : Algebra (ResidueField A) (ResidueField (Localization.AtPrime (RingHom.ker ψ))) :=
    (ResidueField.map g).toAlgebra
  have : IsScalarTower (ResidueField A) (ResidueField (Localization.AtPrime (RingHom.ker ψ))) k :=
    IsScalarTower.of_algebraMap_eq fun z => by
      obtain ⟨a, rfl⟩ := residue_surjective z
      change ResidueField.lift φ (residue A a) =
        ResidueField.lift ψ.liftLocalizationAtKer (ResidueField.map g (residue A a))
      rw [ResidueField.map_residue, ResidueField.lift_residue_apply,
        ResidueField.lift_residue_apply]
      change φ a = ψ.liftLocalizationAtKer (algebraMap B _ (algebraMap A B a))
      rw [RingHom.liftLocalizationAtKer_algebraMap, ← hψ, RingHom.comp_apply]
  exact hy.tower_top _

/-- **The map `γ_ψ : Ã → B̃_ψ`.** For a Henselization `(Ã, φ̃)` of `A` with respect to `φ` and an
`A`-algebra homomorphism `ψ : B → k`, there is an `A`-algebra homomorphism `γ : Ã → B̃_ψ` with
`ψ̃ ∘ γ = φ̃`, where `B̃_ψ` is an `A`-algebra through `A → B → B̃_ψ`. -/
theorem IsHenselizationAlong.exists_algHom_strictHenselizationAt {Ã : Type x} [CommRing Ã]
    [IsLocalRing Ã] [Algebra A Ã] {φ' : Ã →+* k} (h : IsHenselizationAlong φ Ã φ')
    (ψ : B →+* k) (hψ : ψ.comp (algebraMap A B) = φ)
    [Algebra A ψ.strictHenselizationAt] [IsScalarTower A B ψ.strictHenselizationAt] :
    ∃ γ : Ã →ₐ[A] ψ.strictHenselizationAt, ψ.strictHenselizationAtHom.comp γ.toRingHom = φ' := by
  have hH := h.isHenselization
  have := h.isLocalHom_ψ
  have : HenselianLocalRing ψ.strictHenselizationAt :=
    (RingHom.isStrictHenselizationAt_strictHenselizationAt ψ).henselian
  set ψ' := ψ.strictHenselizationAtHom
  have hψ' := RingHom.isStrictHenselizationAt_strictHenselizationAt ψ
  -- `κ(B̃_ψ) ≅ range (lift ψ̃) ⊆ k`
  let e : ResidueField ψ.strictHenselizationAt ≃+* (ResidueField.lift ψ').range :=
    RingEquiv.ofBijective (ResidueField.lift ψ').rangeRestrict
      ⟨fun a b hab => (ResidueField.lift ψ').injective (congrArg Subtype.val hab),
        (ResidueField.lift ψ').rangeRestrict_surjective⟩
  have hmem : ∀ z : ResidueField Ã, ResidueField.lift φ' z ∈ (ResidueField.lift ψ').range := by
    intro z
    obtain ⟨a, rfl⟩ := residue_surjective z
    rw [ResidueField.lift_residue_apply]
    have h1 : φ' a ∈ residueSeparableClosure ψ.liftLocalizationAtKer := by
      apply residueSeparableClosure_le_of_comp_eq ψ hψ
      have : φ' a ∈ φ'.range := ⟨a, rfl⟩
      rw [h.range_ψ] at this
      exact this
    have h2 : φ' a ∈ ψ'.range := by rw [hψ'.range_ψ]; exact h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨residue _ b, by rw [ResidueField.lift_residue_apply, hb]⟩
  let r : ResidueField Ã →+* ResidueField ψ.strictHenselizationAt :=
    e.symm.toRingHom.comp ((ResidueField.lift φ').codRestrict _ hmem)
  have hr : ∀ z, ResidueField.lift ψ' (r z) = ResidueField.lift φ' z := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨_, hmem z⟩)
    exact this
  have hr' : r.comp ((residue Ã).comp (algebraMap A Ã))
      = (residue ψ.strictHenselizationAt).comp (algebraMap A ψ.strictHenselizationAt) := by
    ext a
    apply (ResidueField.lift ψ').injective
    simp only [RingHom.comp_apply]
    rw [hr, ResidueField.lift_residue_apply, ResidueField.lift_residue_apply, h.ψ_algebraMap,
      IsScalarTower.algebraMap_apply A B ψ.strictHenselizationAt,
      RingHom.strictHenselizationAtHom_algebraMap, ← hψ, RingHom.comp_apply]
  let γ := HenselianLocalRing.indEtaleAlgHomOfResidue hH.ind_etale r hr'
  refine ⟨γ, RingHom.ext fun a => ?_⟩
  have hγr : residue _ (γ a) = r (residue Ã a) := RingHom.congr_fun
    (HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hH.ind_etale r hr') a
  change ψ' (γ a) = φ' a
  rw [← ResidueField.lift_residue_apply ψ' (γ a), hγr, hr, ResidueField.lift_residue_apply]

/-- **Comparison maps exist.** Let `A` be a local ring, `B` an `A`-algebra, `k` a separably
closed field, `φ : A → k` a local homomorphism and `(Ã, φ̃)` a Henselization of `A` with respect
to `φ`. Then there is a comparison map `Θ : Ã ⊗_A B → ∏_{ψ ∈ Hom_A(B, k)} B̃_ψ`: a ring
homomorphism with `Θ_ψ (1 ⊗ b) = ι_ψ b` and `ψ̃ (Θ_ψ (a ⊗ 1)) = φ̃ a`. -/
@[weil "lem_fk103_strict_henselization_comparison_map_exists"]
theorem IsHenselizationAlong.exists_isStrictHenselizationComparison {Ã : Type x} [CommRing Ã]
    [IsLocalRing Ã] [Algebra A Ã] {φ' : Ã →+* k} (h : IsHenselizationAlong φ Ã φ') :
    ∃ Θ : Ã ⊗[A] B →+* strictHenselizationProduct φ B, IsStrictHenselizationComparison φ' Θ := by
  have key : ∀ ψ : HomOver φ B, ∃ Θψ : Ã ⊗[A] B →+* (ψ : B →+* k).strictHenselizationAt,
      (∀ b : B, Θψ (1 ⊗ₜ b) = algebraMap B _ b) ∧
        ∀ a : Ã, (ψ : B →+* k).strictHenselizationAtHom (Θψ (a ⊗ₜ 1)) = φ' a := by
    intro ψ
    let : Algebra A (ψ : B →+* k).strictHenselizationAt :=
      ((algebraMap B _).comp (algebraMap A B)).toAlgebra
    have : IsScalarTower A B (ψ : B →+* k).strictHenselizationAt :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨γ, hγ⟩ := h.exists_algHom_strictHenselizationAt (ψ : B →+* k) ψ.2
    let Θψ : Ã ⊗[A] B →ₐ[A] (ψ : B →+* k).strictHenselizationAt :=
      Algebra.TensorProduct.lift γ (IsScalarTower.toAlgHom A B _) fun _ _ => Commute.all _ _
    refine ⟨Θψ.toRingHom, fun b => ?_, fun a => ?_⟩
    · change Θψ (1 ⊗ₜ b) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    · rw [← hγ]
      change (ψ : B →+* k).strictHenselizationAtHom (Θψ (a ⊗ₜ 1)) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
  choose Θ hΘ₁ hΘ₂ using key
  exact ⟨RingHom.pi Θ, ⟨fun ψ b => hΘ₁ ψ b, fun ψ a => hΘ₂ ψ a⟩⟩

end IsLocalRing
