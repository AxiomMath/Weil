module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import Weil.Attr

/-!
# Restriction data for étale cohomology exist

Let `h : Y ⟶ X` be a morphism of schemes and `F` an abelian sheaf on the small étale site of `X`.
Given an injective resolution `F → I^•` and an injective resolution `h^* F → J^•`, there is a
morphism of complexes `ρ : h^* I^• ⟶ J^•` with `ρ⁰ ∘ h^*(ε) = ε'`, where `ε` and `ε'` are the
augmentations. Since `h^*` is exact, `h^* F → h^* I^•` is again a resolution, and the comparison
theorem for resolutions (a morphism from an object resolved by an exact augmented complex to an
object resolved by a complex of injectives extends to the complexes) gives `ρ`.

The comparison step holds in any abelian category and for any exact functor; it is proved here in
that generality.

## Main results

* `CochainComplex.exists_hom_to_injective_of_exact`: a morphism from the source of an exact
  augmented complex with mono augmentation into the kernel of the first differential of a complex
  of injectives extends to a morphism of complexes.
* `CategoryTheory.InjectiveResolution.exists_map_comp_eq_of_exact`: for an exact functor `G`,
  injective resolutions `I` of `F` and `J` of `G F`, there is `ρ : G I ⟶ J` compatible with the
  augmentations.
* `AlgebraicGeometry.exists_smallEtaleInverseImage_restriction_datum`: the restriction datum on
  the small étale sites `SmallEtale` of a big étale site.
* `Stacks.EtaleCohomology.exists_etaleAbelianInverseImage_restriction_datum`: the same on the
  small étale sites `X.smallEtaleTopology`, for the inverse image used by
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [C. Weibel, *An introduction to homological algebra*, 2.3.7][Weibel]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {D : Type*} [Category D] [Abelian D]

/-- **Comparison theorem for resolutions (dual form).** Let `K` be a cochain complex with an
augmentation `κ : Z ⟶ K⁰` such that `0 → Z → K⁰ → K¹ → ⋯` is exact, and let `L` be a complex of
injectives. Every `g : Z ⟶ L⁰` with `g ≫ d = 0` extends to a morphism of complexes `ρ : K ⟶ L`
with `κ ≫ ρ⁰ = g`. -/
theorem exists_hom_to_injective_of_exact (K L : CochainComplex D ℕ) [∀ n, Injective (L.X n)]
    {Z : D} (κ : Z ⟶ K.X 0) [Mono κ] (hκ : κ ≫ K.d 0 1 = 0)
    (h₀ : (ShortComplex.mk κ (K.d 0 1) hκ).Exact)
    (hsucc : ∀ n : ℕ, (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (g : Z ⟶ L.X 0) (hg : g ≫ L.d 0 1 = 0) :
    ∃ ρ : K ⟶ L, κ ≫ ρ.f 0 = g := by
  let ρ₀ : K.X 0 ⟶ L.X 0 := Injective.factorThru g κ
  have hρ₀ : κ ≫ ρ₀ = g := Injective.comp_factorThru g κ
  let ρ₁ : K.X 1 ⟶ L.X 1 :=
    h₀.descToInjective (ρ₀ ≫ L.d 0 1) (by
      change κ ≫ ρ₀ ≫ L.d 0 1 = 0
      rw [← Category.assoc, hρ₀, hg])
  have hρ₁ : K.d 0 1 ≫ ρ₁ = ρ₀ ≫ L.d 0 1 := h₀.comp_descToInjective _ _
  refine ⟨mkHom K L ρ₀ ρ₁ hρ₁.symm fun n p => ⟨(hsucc n).descToInjective
      (p.2.1 ≫ L.d (n + 1) (n + 2)) ?_, ((hsucc n).comp_descToInjective _ _).symm⟩, ?_⟩
  · change K.d n (n + 1) ≫ p.2.1 ≫ L.d (n + 1) (n + 2) = 0
    rw [← Category.assoc, ← p.2.2, Category.assoc, L.d_comp_d, comp_zero]
  · rw [mkHom_f_0]
    exact hρ₀

end CochainComplex

namespace CategoryTheory.InjectiveResolution

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- Let `G` be an exact additive functor, `I` an injective resolution of `F` and `J` an injective
resolution of `G F`. There is a morphism of complexes `ρ : G I ⟶ J` with `ρ⁰ ∘ G(ε) = ε'`, where
`ε : F ⟶ I⁰` and `ε' : G F ⟶ J⁰` are the augmentations. -/
theorem exists_map_comp_eq_of_exact (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] {F : C} (I : InjectiveResolution F)
    (J : InjectiveResolution (G.obj F)) :
    ∃ ρ : (G.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex,
      G.map ((singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0) ≫ ρ.f 0 =
        (singleObjXSelf (ComplexShape.up ℕ) 0 (G.obj F)).inv ≫ J.ι.f 0 := by
  let e := singleObjXSelf (ComplexShape.up ℕ) 0 F
  have hκ : G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0 := by
    rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]
  obtain ⟨ρ, hρ⟩ := CochainComplex.exists_hom_to_injective_of_exact
    ((G.mapHomologicalComplex _).obj I.cocomplex) J.cocomplex (G.map (I.ι.f 0)) hκ
    (I.exact₀.map G) (fun n => (I.exact_succ n).map G)
    (G.map e.hom ≫ (singleObjXSelf (ComplexShape.up ℕ) 0 (G.obj F)).inv ≫ J.ι.f 0)
    (by simp only [Category.assoc, J.ι_f_zero_comp_complex_d, comp_zero])
  refine ⟨ρ, ?_⟩
  rw [G.map_comp, Category.assoc]
  erw [hρ]
  rw [← Category.assoc, ← G.map_comp, e.inv_hom_id, G.map_id, Category.id_comp]

end CategoryTheory.InjectiveResolution

universe u

namespace AlgebraicGeometry

/-- **Restriction data exist** (small étale sites of a big étale site). Let `h : Y ⟶ X` be a
morphism of schemes of a big étale site `B`, `F` an abelian sheaf on the small étale site of `X`,
`F → I^•` an injective resolution and `h^* F → J^•` an injective resolution. There is a morphism
of complexes `ρ : h^* I^• ⟶ J^•` with `ρ⁰ ∘ h^*(ε) = ε'`. -/
@[weil "lem_fk106_cohomology_restriction_data_exist"]
theorem exists_smallEtaleInverseImage_restriction_datum (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (h : Y ⟶ X) (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F)) :
    ∃ ρ : ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
        I.cocomplex ⟶ J.cocomplex,
      (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map
          ((singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0) ≫ ρ.f 0 =
        (singleObjXSelf (ComplexShape.up ℕ) 0 _).inv ≫ J.ι.f 0 := by
  have : (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact InjectiveResolution.exists_map_comp_eq_of_exact _ I J

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **Restriction data exist** (small étale sites `X.smallEtaleTopology`). Let `h : Y ⟶ X` be a
morphism of schemes, `F` an abelian sheaf on the small étale site of `X`, `F → I^•` an injective
resolution and `h^* F → J^•` an injective resolution, `h^*` being the inverse image
`etaleAbelianInverseImage h`. There is a morphism of complexes `ρ : h^* I^• ⟶ J^•` with
`ρ⁰ ∘ h^*(ε) = ε'`. -/
@[weil "lem_fk106_cohomology_restriction_data_exist"]
theorem exists_etaleAbelianInverseImage_restriction_datum {X Y : AlgebraicGeometry.Scheme.{u}}
    (h : Y ⟶ X) [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (J : InjectiveResolution ((etaleAbelianInverseImage.{u, u + 1} h).obj F)) :
    ∃ ρ : ((etaleAbelianInverseImage.{u, u + 1} h).mapHomologicalComplex _).obj I.cocomplex ⟶
        J.cocomplex,
      (etaleAbelianInverseImage.{u, u + 1} h).map
          ((singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0) ≫ ρ.f 0 =
        (singleObjXSelf (ComplexShape.up ℕ) 0 _).inv ≫ J.ι.f 0 := by
  have : (etaleAbelianInverseImage.{u, u + 1} h).IsLeftAdjoint := inferInstance
  have : PreservesFiniteColimits (etaleAbelianInverseImage.{u, u + 1} h) := inferInstance
  exact InjectiveResolution.exists_map_comp_eq_of_exact _ I J

end Stacks.EtaleCohomology
