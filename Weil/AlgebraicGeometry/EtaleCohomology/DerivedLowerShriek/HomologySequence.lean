module

public import Weil.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import Weil.Attr

/-!
# The long exact sequence of higher direct images with proper support

Let `f : X ⟶ S` be a quasi-compact morphism of schemes with a compactification `c`, let
`j : U ⟶ X` be an open immersion and `i : A ⟶ X` a closed immersion whose images are
complementary. For every sheaf `F` of `Λ`-modules on the small étale site of `X` there is a long
exact sequence, natural in `F`,
`0 ⟶ R⁰(f ∘ j)_!(j⁻¹ F) ⟶ R⁰f_! F ⟶ R⁰(f ∘ i)_!(i⁻¹ F) ⟶ ⋯`
`⋯ ⟶ Rᵛ(f ∘ j)_!(j⁻¹ F) ⟶ Rᵛf_! F ⟶ Rᵛ(f ∘ i)_!(i⁻¹ F) ⟶ Rᵛ⁺¹(f ∘ j)_!(j⁻¹ F) ⟶ ⋯`.

It is the long exact cohomology sequence of the open-closed triangle
`R(f ∘ j)_!(j⁻¹ F) ⟶ Rf_! F ⟶ R(f ∘ i)_!(i⁻¹ F) ⟶ R(f ∘ j)_!(j⁻¹ F)[1]` applied to `F` placed in
degree `0`; the triangle is natural in `F`, hence so are the three families of maps of the
sequence. The higher direct images with proper support of a sheaf vanish in negative degrees, so
the sequence starts with `0`.

## Main results

* `AlgebraicGeometry.exists_exact_higherDirectImageProperSupport_openClosed`: the long exact
  sequence, natural in `F`, with its first map injective.

## Implementation notes

The source states the result for torsion abelian sheaves. Neither hypothesis is used: the
statement is for sheaves of modules over an arbitrary ring `Λ`; the source's case is `Λ = ℤ`
restricted to torsion sheaves. The sheaves live on Mathlib's small étale sites, where
`AlgebraicGeometry.higherDirectImageProperSupport` is defined. `Rᵛ(f ∘ j)_!` and `Rᵛ(f ∘ i)_!`
are computed with the compactifications `AlgebraicGeometry.CompactificationOf.restrictOpen` and
`AlgebraicGeometry.CompactificationOf.restrictClosed` induced by `c`. Functoriality in `F` is the
naturality of the three families of maps.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 0GKP](https://stacks.math.columbia.edu/tag/0GKP)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

universe u r

namespace AlgebraicGeometry

/-- `F ↦ (F[0])` through bounded below complexes is the single functor into `D⁺`. -/
private def singlePlusCompQIso (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C] :
    singlePlus C ⋙ DerivedCategory.Plus.Q ≅ DerivedCategory.Plus.singleFunctor C 0 :=
  ((ObjectProperty.fullyFaithfulι
      (DerivedCategory.TStructure.t (C := C)).plus).whiskeringRight _).preimageIso
    (((SingleFunctors.evaluation C (DerivedCategory C) (0 : ℤ)).mapIso
      (DerivedCategory.singleFunctorsPostcompQIso C)).symm)

variable (Λ : Type r) [Ring Λ] {Z U X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] {f : X ⟶ S} [QuasiCompact f]
  (c : CompactificationOf (Over.mk f))

/-- **The long exact sequence of higher direct images with proper support.** Let `f : X ⟶ S`
be quasi-compact with compactification `c`, and let `j : U ⟶ X` be an open immersion and
`i : Z ⟶ X` a closed immersion with complementary images. Then there are maps, natural in the
sheaf `F` of `Λ`-modules on the small étale site of `X`,
`αᵛ : Rᵛ(f ∘ j)_!(j⁻¹ F) ⟶ Rᵛf_! F`, `βᵛ : Rᵛf_! F ⟶ Rᵛ(f ∘ i)_!(i⁻¹ F)` and
`δᵛ : Rᵛ(f ∘ i)_!(i⁻¹ F) ⟶ Rᵛ⁺¹(f ∘ j)_!(j⁻¹ F)`, forming a long exact sequence whose first map
`α⁰` is a monomorphism. -/
@[weil "thm_fk108_proper_direct_image_long_exact_sequence"]
theorem exists_exact_higherDirectImageProperSupport_openClosed
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (α : ∀ v : ℤ, etaleModuleInverseImage.{u, r} Λ j ⋙
          DerivedCategory.Plus.singleFunctor _ 0 ⋙
            higherDirectImageProperSupport (j ≫ f) (c.restrictOpen j) Λ v ⟶
          DerivedCategory.Plus.singleFunctor _ 0 ⋙ higherDirectImageProperSupport f c Λ v)
      (β : ∀ v : ℤ, DerivedCategory.Plus.singleFunctor _ 0 ⋙
          higherDirectImageProperSupport f c Λ v ⟶
          etaleModuleInverseImage.{u, r} Λ i ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
            higherDirectImageProperSupport (i ≫ f) (c.restrictClosed i) Λ v)
      (δ : ∀ v : ℤ, etaleModuleInverseImage.{u, r} Λ i ⋙
          DerivedCategory.Plus.singleFunctor _ 0 ⋙
            higherDirectImageProperSupport (i ≫ f) (c.restrictClosed i) Λ v ⟶
          etaleModuleInverseImage.{u, r} Λ j ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
            higherDirectImageProperSupport (j ≫ f) (c.restrictOpen j) Λ (v + 1))
      (hαβ : ∀ v F, (α v).app F ≫ (β v).app F = 0)
      (hβδ : ∀ v F, (β v).app F ≫ (δ v).app F = 0)
      (hδα : ∀ v F, (δ v).app F ≫ (α (v + 1)).app F = 0),
      (∀ v F, (ShortComplex.mk _ _ (hαβ v F)).Exact) ∧
      (∀ v F, (ShortComplex.mk _ _ (hβδ v F)).Exact) ∧
      (∀ v F, (ShortComplex.mk _ _ (hδα v F)).Exact) ∧
      ∀ F, Mono ((α 0).app F) := by
  let e₁ : singlePlus _ ⋙ DerivedCategory.Plus.Q ⋙
        (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategoryPlus ⋙
          derivedLowerShriek.{u, r} (j ≫ f) (c.restrictOpen j) Λ ≅
      etaleModuleInverseImage.{u, r} Λ j ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, r} (j ≫ f) (c.restrictOpen j) Λ :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (singlePlusCompQIso _) _ ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, r} Λ j) 0) _ ≪≫ Functor.associator _ _ _
  let e₂ : singlePlus _ ⋙ DerivedCategory.Plus.Q ⋙ derivedLowerShriek.{u, r} f c Λ ≅
      DerivedCategory.Plus.singleFunctor _ 0 ⋙ derivedLowerShriek.{u, r} f c Λ :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (singlePlusCompQIso _) _
  let e₃ : singlePlus _ ⋙ DerivedCategory.Plus.Q ⋙
        (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus ⋙
          derivedLowerShriek.{u, r} (i ≫ f) (c.restrictClosed i) Λ ≅
      etaleModuleInverseImage.{u, r} Λ i ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, r} (i ≫ f) (c.restrictClosed i) Λ :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (singlePlusCompQIso _) _ ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, r} Λ i) 0) _ ≪≫ Functor.associator _ _ _
  obtain ⟨a, b, d, hT⟩ :=
    ((existsNatDistTriang_derivedLowerShriek_openClosed Λ i j c hij).whiskerLeft
      (singlePlus _)).of_iso e₁ e₂ e₃
  let T : EtaleModules.{u, r} Λ X → Triangle (DerivedCategory (EtaleModules.{u, r} Λ S)) :=
    fun F => DerivedCategory.Plus.ι.mapTriangle.obj (Triangle.mk (a.app F) (b.app F) (d.app F))
  have hT' : ∀ F, T F ∈ distTriang _ := fun F =>
    DerivedCategory.Plus.ι.map_distinguished _ (hT F)
  let Tmap : ∀ {F G : EtaleModules.{u, r} Λ X} (φ : F ⟶ G), T F ⟶ T G := fun {F G} φ =>
    DerivedCategory.Plus.ι.mapTriangle.map (Triangle.homMk _ _ _ _ _ (a.naturality φ).symm
      (b.naturality φ).symm (d.naturality φ).symm)
  refine ⟨fun v => Functor.whiskerRight a (DerivedCategory.Plus.homologyFunctor _ v),
    fun v => Functor.whiskerRight b (DerivedCategory.Plus.homologyFunctor _ v),
    fun v =>
      { app F := DerivedCategory.HomologySequence.δ (T F) v (v + 1) rfl
        naturality F G φ :=
          Functor.homologySequenceδ_naturality (DerivedCategory.homologyFunctor _ 0)
            (Tmap φ) v (v + 1) rfl },
    fun v F => ?_, fun v F => DerivedCategory.HomologySequence.comp_δ _ (hT' F) v (v + 1) rfl,
    fun v F => DerivedCategory.HomologySequence.δ_comp _ (hT' F) v (v + 1) rfl,
    fun v F => DerivedCategory.HomologySequence.exact₂ _ (hT' F) v,
    fun v F => DerivedCategory.HomologySequence.exact₃ _ (hT' F) v (v + 1) rfl,
    fun v F => DerivedCategory.HomologySequence.exact₁ _ (hT' F) v (v + 1) rfl, fun F => ?_⟩
  · change (DerivedCategory.homologyFunctor _ v).map (T F).mor₁ ≫
      (DerivedCategory.homologyFunctor _ v).map (T F).mor₂ = 0
    rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ (hT' F), Functor.map_zero]
  · exact (DerivedCategory.HomologySequence.exact₁ _ (hT' F) (-1) 0 (by norm_num)).mono_g
      ((isZero_higherDirectImageProperSupport_singleFunctor_obj (i ≫ f) (c.restrictClosed i) Λ
        ((etaleModuleInverseImage.{u, r} Λ i).obj F) (by norm_num)).eq_of_src _ _)

end AlgebraicGeometry
