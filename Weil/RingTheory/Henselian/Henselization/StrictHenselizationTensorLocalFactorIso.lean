module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.StrictHenselization.AtPrime
public import Weil.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.StrictHenselization

/-!
# Local factors of a finite algebra base changed to a strict Henselization

Let `A` be a local ring, `B` a finite `A`-algebra, `k` a separably closed field, `φ : A → k` a
local homomorphism and `(Ã, φ̃)` the Henselization of `A` with respect to `φ`. Put
`T = Ã ⊗[A] B`. A homomorphism `ψ : B → k` gives the homomorphism `χ : T → k`,
`a ⊗ b ↦ φ̃(a) ψ(b)`, whose kernel `M_ψ` is a maximal ideal of `T`, and the strict Henselization
`(B̃_ψ, ψ̃)` of `B` at `ψ`. Given a ring homomorphism `θ : T → B̃_ψ` with `θ(1 ⊗ b) = ι_ψ(b)` and
`ψ̃(θ(a ⊗ 1)) = φ̃(a)`, the map `θ` induces an isomorphism `T_{M_ψ} ≅ B̃_ψ`.

The proof: `ψ̃ ∘ θ = χ`, so `θ` inverts `T ∖ M_ψ` and induces `β : T_{M_ψ} → B̃_ψ`. The ring
`T_{M_ψ}` is strictly henselian, and the residue field of `B̃_ψ`, the separable closure of
`κ(ker ψ)` in `k`, lies in the separably closed image of the residue field of `T_{M_ψ}` in `k`.
The universal property of the strict Henselization (Stacks 04GU) gives a local
`B_{ker ψ}`-algebra map `α : B̃_ψ → T_{M_ψ}` compatible with the maps to `k`, and the uniqueness
in that universal property, applied to `B̃_ψ` over `B_{ker ψ}` and to `Ã` over `A`, shows that
`α` and `β` are mutually inverse.

## Main results

* `IsLocalRing.IsHenselizationAlong.exists_ringEquiv_localization_tensorProduct`: the
  isomorphism `β : T_{M_ψ} ≃ B̃_ψ` with `β(t / 1) = θ(t)`.

## Implementation notes

The source assumes `A` noetherian and `ψ` an `A`-algebra homomorphism; neither is needed. The
second is implied by the existence of `χ`, which is taken as an argument together with its
values `χ(a ⊗ b) = φ̃(a) ψ(b)`; these determine it. The Henselization and the strict
Henselization are any pairs satisfying `IsLocalRing.IsHenselizationAlong` and
`RingHom.IsStrictHenselizationAt`, not only the chosen ones.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [StacksProject 05WR](https://stacks.math.columbia.edu/tag/05WR)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w x y

namespace IsLocalRing.IsHenselizationAlong

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Module.Finite A B] {k : Type w} [Field k] [IsSepClosed k] {φ : A →+* k} [IsLocalHom φ]
  {Ã : Type x} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {φ' : Ã →+* k}

/-- **The local factor of a finite algebra base changed to a strict Henselization.** Let
`(Ã, φ̃)` be the Henselization of a local ring `A` with respect to a local homomorphism `φ` to a
separably closed field `k`, let `B` be a finite `A`-algebra, `ψ : B → k` a homomorphism and
`(B̃_ψ, ψ̃)` a strict Henselization of `B` at `ψ`. Let `χ : Ã ⊗[A] B → k` be the homomorphism
`a ⊗ b ↦ φ̃(a) ψ(b)` and `θ : Ã ⊗[A] B → B̃_ψ` a ring homomorphism with `θ(1 ⊗ b) = ι_ψ(b)` and
`ψ̃(θ(a ⊗ 1)) = φ̃(a)`. Then `θ` induces a ring isomorphism `β` from the localization of
`Ã ⊗[A] B` at `ker χ` onto `B̃_ψ`, with `β(t / 1) = θ(t)`. -/
@[weil "lem_fk103_strict_henselization_tensor_local_factor_iso"]
theorem exists_ringEquiv_localization_tensorProduct (hA : IsHenselizationAlong φ Ã φ')
    {ψ : B →+* k} {B' : Type y} [CommRing B'] [IsLocalRing B']
    [Algebra (Localization.AtPrime (RingHom.ker ψ)) B'] [Algebra B B']
    [IsScalarTower B (Localization.AtPrime (RingHom.ker ψ)) B'] {ψ' : B' →+* k}
    (hB : ψ.IsStrictHenselizationAt B' ψ')
    (χ : Ã ⊗[A] B →+* k) (hχ : ∀ a b, χ (a ⊗ₜ b) = φ' a * ψ b)
    (θ : Ã ⊗[A] B →+* B') (hθB : ∀ b, θ (1 ⊗ₜ b) = algebraMap B B' b)
    (hθA : ∀ a, ψ' (θ (a ⊗ₜ 1)) = φ' a) :
    ∃ β : Localization.AtPrime (RingHom.ker χ) ≃+* B',
      ∀ t, β (algebraMap _ _ t) = θ t := by
  classical
  -- notation
  set T := Ã ⊗[A] B
  set M : Ideal T := RingHom.ker χ
  set F := Localization.AtPrime M
  set Bn := Localization.AtPrime (RingHom.ker ψ)
  have hBn := hB.isHenselization
  have hAh := hA.isHenselization
  have : IsLocalHom ψ' := hB.isLocalHom_ψ
  have : IsLocalHom φ' := hA.isLocalHom_ψ
  have : HenselianLocalRing B' := hB.henselian
  -- `ψ̃ ∘ θ = χ`
  have hψθ : ∀ t, ψ' (θ t) = χ t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        have : a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : B)) * ((1 : Ã) ⊗ₜ[A] b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this, map_mul, map_mul, map_mul, hθA, hθB, hB.apply_algebraMap, hχ, hχ, map_one,
          map_one, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  -- `θ` inverts the complement of `M`, so it induces `β₀ : F → B̃`
  have hunit : ∀ s : M.primeCompl, IsUnit (θ s) := fun s => by
    by_contra hnu
    have hm : θ s ∈ maximalIdeal B' := hnu
    rw [← hB.ker_ψ, RingHom.mem_ker, hψθ] at hm
    exact s.2 hm
  let β₀ : F →+* B' := IsLocalization.lift hunit
  have hβ₀ : ∀ t, β₀ (algebraMap T F t) = θ t := IsLocalization.lift_eq hunit
  let χ' : F →+* k := ψ'.comp β₀
  have hχ' : ∀ t, χ' (algebraMap T F t) = χ t := fun t => by
    simp only [χ', RingHom.comp_apply, hβ₀, hψθ]
  have : IsLocalHom χ' := ⟨fun x hx => by
    obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective M.primeCompl x
    have hs : IsUnit (χ s) := isUnit_iff_ne_zero.2 s.2
    have hspec : χ' (IsLocalization.mk' F t s) * χ s = χ t := by
      rw [← hχ' s, ← map_mul, IsLocalization.mk'_spec, hχ']
    have ht : t ∈ M.primeCompl := fun h =>
      (hx.mul hs).ne_zero (hspec.trans (RingHom.mem_ker.1 h))
    exact (IsLocalization.AtPrime.isUnit_mk'_iff _ _ t s).2 ht⟩
  -- `M` is maximal, so `F` is strictly henselian
  have hcomapA : M.comap (algebraMap Ã T) = maximalIdeal Ã := by
    ext a
    change χ (a ⊗ₜ[A] (1 : B)) = 0 ↔ _
    rw [hχ, map_one, mul_one, ← RingHom.mem_ker, hA.ker_ψ]
  have hMmax : M.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Ã)
    rw [hcomapA]
    infer_instance
  have hFsh : StrictlyHenselianLocalRing F :=
    hA.strictlyHenselianLocalRing_localization_tensorProduct (B := B) M
  have : HenselianLocalRing F := hFsh.toHenselianLocalRing
  have hFsep : IsSepClosed (ResidueField F) := hFsh.toIsSepClosed
  -- the local homomorphism `g : B_𝔫 → F`
  let iR : B →+* T := (Algebra.TensorProduct.includeRight : B →ₐ[A] T).toRingHom
  have hiR : ∀ b, iR b = (1 : Ã) ⊗ₜ[A] b := fun _ => rfl
  have hcomapB : RingHom.ker ψ = M.comap iR := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hiR, hχ, map_one, one_mul]
  let g : Bn →+* F := Localization.localRingHom (RingHom.ker ψ) M iR hcomapB
  have hg : ∀ b, g (algebraMap B Bn b) = algebraMap T F ((1 : Ã) ⊗ₜ[A] b) := fun b =>
    Localization.localRingHom_to_map _ _ _ hcomapB b
  let _ : Algebra Bn F := g.toAlgebra
  have hgalg : ∀ z, algebraMap Bn F z = g z := fun _ => rfl
  have hχ'g : ∀ z, χ' (g z) = ψ.liftLocalizationAtKer z := by
    intro z
    have := IsLocalization.ringHom_ext (RingHom.ker ψ).primeCompl (S := Bn)
      (j := χ'.comp g) (k := ψ.liftLocalizationAtKer) (RingHom.ext fun b => by
        simp only [RingHom.comp_apply, hg, hχ', hχ, map_one, one_mul]
        exact (RingHom.liftLocalizationAtKer_algebraMap ψ b).symm)
    exact RingHom.congr_fun this z
  have hβ₀g : ∀ z, β₀ (g z) = algebraMap Bn B' z := by
    intro z
    have := IsLocalization.ringHom_ext (RingHom.ker ψ).primeCompl (S := Bn)
      (j := β₀.comp g) (k := algebraMap Bn B') (RingHom.ext fun b => by
        simp only [RingHom.comp_apply, hg, hβ₀, hθB]
        exact IsScalarTower.algebraMap_apply B Bn B' b)
    exact RingHom.congr_fun this z
  -- the residue field of `B̃` lands in the image of the residue field of `F` in `k`
  set K : Subfield k := (ResidueField.lift χ').fieldRange
  have hKsep : IsSepClosed K :=
    Stacks.StrictHenselization.EtaleColimit.isSepClosed_of_ringEquiv
      (ResidueField.lift χ').rangeRestrictFieldEquiv
  have hliftg : ∀ z, ResidueField.lift ψ.liftLocalizationAtKer z =
      ResidueField.lift χ' (ResidueField.map g z) := by
    intro z
    obtain ⟨z, rfl⟩ := residue_surjective z
    rw [ResidueField.lift_residue_apply, ResidueField.map_residue, ResidueField.lift_residue_apply,
      hχ'g]
  have hsub : ∀ x : B', ψ' x ∈ K := by
    intro x
    have hx : ψ' x ∈ residueSeparableClosure ψ.liftLocalizationAtKer := by
      rw [← Subfield.mem_toSubring, ← hB.range_ψ]
      exact ⟨x, rfl⟩
    rw [mem_residueSeparableClosure] at hx
    let _ : Algebra (ResidueField Bn) k := (ResidueField.lift ψ.liftLocalizationAtKer).toAlgebra
    let _ : Algebra (ResidueField Bn) K :=
      ((ResidueField.lift χ').rangeRestrictField.comp (ResidueField.map g)).toAlgebra
    have : IsScalarTower (ResidueField Bn) K k :=
      IsScalarTower.of_algebraMap_eq fun z => hliftg z
    have hxK : IsSeparable K (ψ' x) := hx.tower_top K
    have hbot := IntermediateField.eq_bot_of_isSepClosed_of_isSeparable (separableClosure K k)
    have hmem : ψ' x ∈ separableClosure K k := mem_separableClosure_iff.2 hxK
    rw [hbot, IntermediateField.mem_bot] at hmem
    obtain ⟨y, hy⟩ := hmem
    rw [← hy]
    exact y.2
  -- the residue map `κ(B̃) → κ(F)` over `k`
  have hsubR : ∀ y, ResidueField.lift ψ' y ∈ K := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    rw [ResidueField.lift_residue_apply]
    exact hsub x
  let res : ResidueField B' →+* ResidueField F :=
    (ResidueField.lift χ').rangeRestrictFieldEquiv.symm.toRingHom.comp
      ((ResidueField.lift ψ').codRestrict K hsubR)
  have hres : ∀ y, ResidueField.lift χ' (res y) = ResidueField.lift ψ' y := fun y =>
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _
  have hlinj : Function.Injective (ResidueField.lift χ') := (ResidueField.lift χ').injective
  -- the map `α : B̃ → F` of the universal property
  have hindB := IsHenselization.ind_etale (R := Bn)
    (L := residueSeparableClosure ψ.liftLocalizationAtKer) (Rh := B')
  have hresB : res.comp ((residue B').comp (algebraMap Bn B')) =
      (residue F).comp (algebraMap Bn F) := by
    ext z
    apply hlinj
    simp only [RingHom.comp_apply, hres, ResidueField.lift_residue_apply, hgalg, hχ'g]
    exact hB.ψ_algebraMap z
  let α : B' →ₐ[Bn] F := HenselianLocalRing.indEtaleAlgHomOfResidue hindB res hresB
  have hαres := HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hindB res hresB
  have hχ'α : ∀ x, χ' (α x) = ψ' x := by
    intro x
    rw [← ResidueField.lift_residue_apply χ' (α x)]
    change ResidueField.lift χ' (((residue F).comp (α : B' →+* F)) x) = _
    rw [hαres, RingHom.comp_apply, hres, ResidueField.lift_residue_apply]
  -- `β₀ ∘ α = id`
  have hβα : β₀.comp (α : B' →+* F) = RingHom.id B' := by
    let β₁ : F →ₐ[Bn] B' := { β₀ with commutes' := hβ₀g }
    have hloc : IsLocalHom (β₁.comp α) := by
      have : IsLocalHom (ψ'.comp (β₁.comp α : B' →+* B')) := by
        have : ψ'.comp (β₁.comp α : B' →+* B') = ψ' := RingHom.ext fun x => hχ'α x
        rw [this]; infer_instance
      exact ⟨fun x hx => (isLocalHom_of_comp (β₁.comp α : B' →+* B') ψ').map_nonunit x hx⟩
    have hres1 : (residue B').comp ((β₁.comp α : B' →ₐ[Bn] B') : B' →+* B') =
        (RingHom.id _).comp (residue B') := by
      ext x
      apply (ResidueField.lift ψ').injective
      simp only [RingHom.comp_apply, RingHom.id_apply, ResidueField.lift_residue_apply]
      exact hχ'α x
    have hid : (residue B').comp ((AlgHom.id Bn B' : B' →ₐ[Bn] B') : B' →+* B') =
        (RingHom.id _).comp (residue B') := rfl
    have hφid : (RingHom.id (ResidueField B')).comp ((residue B').comp (algebraMap Bn B')) =
        (residue B').comp (algebraMap Bn B') := rfl
    have e1 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hindB _ hφid _ hloc hres1
    have e2 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hindB _ hφid
      (AlgHom.id Bn B') ⟨fun _ hx => hx⟩ hid
    have := congrArg (fun f : B' →ₐ[Bn] B' => (f : B' →+* B')) (e1.trans e2.symm)
    exact this
  -- `α ∘ θ` is the localization map on `1 ⊗ b`
  have hαθB : ∀ b, α (θ ((1 : Ã) ⊗ₜ[A] b)) = algebraMap T F ((1 : Ã) ⊗ₜ[A] b) := by
    intro b
    rw [hθB, IsScalarTower.algebraMap_apply B Bn B', AlgHom.commutes, hgalg, hg]
  -- `α ∘ θ` is the localization map on `a ⊗ 1`, by uniqueness over `A`
  have hαθA : ∀ a, α (θ (a ⊗ₜ[A] (1 : B))) = algebraMap T F (a ⊗ₜ[A] (1 : B)) := by
    have htmul : ∀ a₀ : A, algebraMap A Ã a₀ ⊗ₜ[A] (1 : B) = (1 : Ã) ⊗ₜ[A] algebraMap A B a₀ :=
      fun a₀ => by rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have hAF : ∀ a₀ : A, algebraMap A F a₀ =
        algebraMap T F ((1 : Ã) ⊗ₜ[A] algebraMap A B a₀) := fun a₀ => by
      rw [IsScalarTower.algebraMap_apply A T F, Algebra.TensorProduct.algebraMap_apply,
        htmul]
    let h₁ : Ã →ₐ[A] F :=
      { ((α : B' →+* F).comp θ).comp
          (Algebra.TensorProduct.includeLeft : Ã →ₐ[A] T).toRingHom with
        commutes' := fun a₀ => by
          change α (θ (algebraMap A Ã a₀ ⊗ₜ[A] (1 : B))) = _
          rw [htmul, hαθB, hAF] }
    let h₂ : Ã →ₐ[A] F :=
      { (algebraMap T F).comp (Algebra.TensorProduct.includeLeft : Ã →ₐ[A] T).toRingHom with
        commutes' := fun a₀ => by
          change algebraMap T F (algebraMap A Ã a₀ ⊗ₜ[A] (1 : B)) = _
          rw [htmul, hAF] }
    have hh₁ : ∀ a, h₁ a = α (θ (a ⊗ₜ[A] (1 : B))) := fun _ => rfl
    have hh₂ : ∀ a, h₂ a = algebraMap T F (a ⊗ₜ[A] (1 : B)) := fun _ => rfl
    have hχ'h₁ : ∀ a, χ' (h₁ a) = φ' a := fun a => by rw [hh₁, hχ'α, hθA]
    have hχ'h₂ : ∀ a, χ' (h₂ a) = φ' a := fun a => by
      rw [hh₂, hχ', hχ, map_one, mul_one]
    have hloc₁ : IsLocalHom h₁ := by
      have : χ'.comp (h₁ : Ã →+* F) = φ' := RingHom.ext hχ'h₁
      have : IsLocalHom (χ'.comp (h₁ : Ã →+* F)) := by rw [this]; infer_instance
      exact ⟨fun x hx => (isLocalHom_of_comp (h₁ : Ã →+* F) χ').map_nonunit x hx⟩
    have hloc₂ : IsLocalHom (h₂ : Ã →+* F) := by
      have : χ'.comp (h₂ : Ã →+* F) = φ' := RingHom.ext hχ'h₂
      have : IsLocalHom (χ'.comp (h₂ : Ã →+* F)) := by rw [this]; infer_instance
      exact isLocalHom_of_comp (h₂ : Ã →+* F) χ'
    have hres₂ : (residue F).comp (h₂ : Ã →+* F) =
        (ResidueField.map (h₂ : Ã →+* F)).comp (residue Ã) := by
      ext a; simp only [RingHom.comp_apply, ResidueField.map_residue]
    have hres₁ : (residue F).comp (h₁ : Ã →+* F) =
        (ResidueField.map (h₂ : Ã →+* F)).comp (residue Ã) := by
      rw [← hres₂]
      ext a
      apply hlinj
      simp only [RingHom.comp_apply, ResidueField.lift_residue_apply]
      exact (hχ'h₁ a).trans (hχ'h₂ a).symm
    have hφA : (ResidueField.map (h₂ : Ã →+* F)).comp ((residue Ã).comp (algebraMap A Ã)) =
        (residue F).comp (algebraMap A F) := by
      rw [← RingHom.comp_assoc, ← hres₂, RingHom.comp_assoc]
      ext a₀
      simp only [RingHom.comp_apply]
      exact congrArg (residue F) (h₂.commutes a₀)
    have hindA := IsHenselization.ind_etale (R := A) (L := residueSeparableClosure φ) (Rh := Ã)
    have e1 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hindA _ hφA h₁ hloc₁ hres₁
    have e2 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hindA _ hφA h₂
      ⟨fun x hx => hloc₂.map_nonunit x hx⟩ hres₂
    intro a
    exact (hh₁ a).symm.trans ((DFunLike.congr_fun (e1.trans e2.symm) a).trans (hh₂ a))
  have hαθ : (α : B' →+* F).comp θ = algebraMap T F := by
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        have : a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : B)) * ((1 : Ã) ⊗ₜ[A] b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [this, map_mul, map_mul, map_mul, hαθA, hαθB]
    | add x y hx hy =>
        simp only [RingHom.comp_apply] at hx hy ⊢
        rw [map_add, map_add, map_add, hx, hy]
  have hαβ : (α : B' →+* F).comp β₀ = RingHom.id F := by
    apply IsLocalization.ringHom_ext M.primeCompl
    rw [RingHom.comp_assoc, RingHom.id_comp]
    refine RingHom.ext fun t => ?_
    simp only [RingHom.comp_apply, hβ₀]
    exact RingHom.congr_fun hαθ t
  exact ⟨RingEquiv.ofRingHom β₀ (α : B' →+* F) hβα hαβ, hβ₀⟩

end IsLocalRing.IsHenselizationAlong
