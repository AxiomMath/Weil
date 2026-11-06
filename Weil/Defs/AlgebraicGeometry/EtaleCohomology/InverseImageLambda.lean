module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.AlgebraicGeometry.Sites.Bridges.StalkColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.FreeModuleSheafSections
public import Weil.Attr

/-!
# The inverse image of sheaves of `Λ`-modules on the small étale site

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B` and let `Λ` be a ring. For a
sheaf `G` of `Λ`-modules on the small étale site of `S`, its inverse image `f^* G` is the inverse
image of the underlying abelian sheaf, with `λ ∈ Λ` acting by the inverse image `f^*(λ_G)` of
multiplication by `λ` on `G`; on a morphism of sheaves of `Λ`-modules `φ` it is `f^* φ`.

We take for `f^*` the inverse image of sheaves with values in `ModuleCat Λ`, the left adjoint of
the direct image of sheaves of `Λ`-modules, and identify it with the description above: forgetting
the module structure carries it to the inverse image of abelian sheaves, and, for commutative
`Λ`, the action of `λ` on `f^* G` is the inverse image of the action of `λ` on `G`, both as
morphisms of sheaves of `Λ`-modules and, through that identification, as morphisms of abelian
sheaves.

## Main definitions

* `AlgebraicGeometry.smallEtaleModuleSheafInverseImage` — the inverse image `f^*` of sheaves of
  `Λ`-modules on the small étale sites.
* `AlgebraicGeometry.smallEtaleModuleSheafInverseImageForgetIso` — the underlying abelian sheaf of
  `f^* G` is the inverse image of the underlying abelian sheaf of `G`, naturally in `G`.

## Main results

* `AlgebraicGeometry.smallEtaleModuleSheafInverseImage_map_smulEnd` — `f^*(λ_G) = λ_{f^* G}`.
* `AlgebraicGeometry.smallEtaleModuleSheafInverseImageForgetIso_hom_app_comp_map_smulEnd` — through
  the identification of the underlying abelian sheaves, the action of `λ` on `f^* G` is the
  abelian inverse image of the action of `λ` on `G`.

## Implementation notes

The coefficients are `ModuleCat.{w} Λ` for a ring `Λ` in any universe and any universe `w` of
modules containing the morphisms of the small étale sites (`UnivLE.{u + 1, w}`; for instance
`w = max (u + 1) r`, the universe of the Stacks project's results on sheaves of modules on small
étale sites). The comparison with the abelian inverse image is the Stacks project's
`Stacks.EtaleCohomology.coefficientSheafPullbackTwoSquare` for the forgetful functor, which is
invertible because the forgetful functor preserves the filtered colimits computing the left Kan
extension along base change and commutes with sheafification.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II][FreitagKiehl]
* [Stacks Project, Tag 03DD](https://stacks.math.columbia.edu/tag/03DD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u r

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (Λ : Type r) [Ring Λ]
  [UnivLE.{u + 1, w}]

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat preservesFilteredColimits_forget_moduleCat
  hasLimitsOfShape_walkingMulticospan_moduleCat

/-- **The inverse image `f^*` of sheaves of `Λ`-modules.** The inverse image
`AlgebraicGeometry.smallEtaleInverseImage` with values in `Λ`-modules, the left adjoint of the
direct image of sheaves of `Λ`-modules. Its underlying abelian sheaf is the inverse image of the
underlying abelian sheaf (`smallEtaleModuleSheafInverseImageForgetIso`), and `λ ∈ Λ` acts on it
by the inverse image of the action of `λ`
(`smallEtaleModuleSheafInverseImageForgetIso_hom_app_comp_map_smulEnd`). -/
@[weil "def_fka2_inverse_image_lambda"]
abbrev smallEtaleModuleSheafInverseImage :
    Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} Λ) ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ) :=
  smallEtaleInverseImage B f (ModuleCat.{w} Λ)

/-- **The adjunction `f^* ⊣ f_*` for sheaves of `Λ`-modules.** -/
abbrev smallEtaleModuleSheafInverseImageAdjunction :
    smallEtaleModuleSheafInverseImage.{w} B f Λ ⊣
      (smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) :=
  smallEtaleInverseImageAdjunction B f (ModuleCat.{w} Λ)

/-- Forgetting the module structure preserves the left Kan extensions along base change of small
étale sites: the comma categories computing them are filtered, base change being representably
flat, and the forgetful functor preserves filtered colimits. -/
lemma forget₂_moduleCat_preservesLeftKanExtensions_smallEtaleBaseChange :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions
      (smallEtaleBaseChange B f).op := by
  intro P
  have hfil : ∀ V : (SmallEtale B T.obj T.property)ᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V.unop)
  have : PreservesColimitsOfSize.{u, u + 1} (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, u, u + 1} Λ
  infer_instance

attribute [local instance] forget₂_moduleCat_preservesLeftKanExtensions_smallEtaleBaseChange

/-- **The underlying abelian sheaf of `f^* G`.** Forgetting the module structure carries the
inverse image of sheaves of `Λ`-modules to the inverse image of abelian sheaves:
`U(f^* G) ≅ f^*(U G)`, naturally in `G`. -/
@[weil "def_fka2_inverse_image_lambda"]
def smallEtaleModuleSheafInverseImageForgetIso :
    smallEtaleModuleSheafInverseImage.{w} B f Λ ⋙
        sheafCompose (SmallEtale.topology B T.obj T.property)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      sheafCompose (SmallEtale.topology B S.obj S.property)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙
        smallEtaleInverseImage B f AddCommGrpCat.{w} :=
  (asIso (Stacks.EtaleCohomology.coefficientSheafPullbackTwoSquare (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).natTrans).symm

/-- The identification of the underlying abelian sheaf of `f^* G` with `f^*(U G)` is natural in
`G`. -/
@[reassoc]
lemma smallEtaleModuleSheafInverseImageForgetIso_hom_naturality
    {G G' : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} Λ)} (φ : G ⟶ G') :
    (sheafCompose (SmallEtale.topology B T.obj T.property)
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((smallEtaleModuleSheafInverseImage.{w} B f Λ).map φ) ≫
        (smallEtaleModuleSheafInverseImageForgetIso.{w} B f Λ).hom.app G' =
      (smallEtaleModuleSheafInverseImageForgetIso.{w} B f Λ).hom.app G ≫
        (smallEtaleInverseImage B f AddCommGrpCat.{w}).map
          ((sheafCompose (SmallEtale.topology B S.obj S.property)
            (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ) :=
  (smallEtaleModuleSheafInverseImageForgetIso.{w} B f Λ).hom.naturality φ

section Commutative

variable {Λ : Type r} [CommRing Λ]

/-- **`f^*(λ_G) = λ_{f^* G}`.** The inverse image of multiplication by `λ` on a sheaf of
`Λ`-modules `G` is multiplication by `λ` on `f^* G`. -/
@[weil "def_fka2_inverse_image_lambda"]
lemma smallEtaleModuleSheafInverseImage_map_smulEnd (l : Λ)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} Λ)) :
    (smallEtaleModuleSheafInverseImage.{w} B f Λ).map
        (Sheaf.smulEnd (SmallEtale.topology B S.obj S.property) l G) =
      Sheaf.smulEnd (SmallEtale.topology B T.obj T.property) l
        ((smallEtaleModuleSheafInverseImage.{w} B f Λ).obj G) :=
  Sheaf.map_smulEnd_of_adjunction _ _ (smallEtaleModuleSheafInverseImageAdjunction.{w} B f Λ)
    (fun _ _ ↦ rfl) l G

/-- **`λ` acts on `f^* G` by `f^*(λ_G)`.** Through the identification of the underlying abelian
sheaf of `f^* G` with the inverse image `f^*(U G)` of the underlying abelian sheaf of `G`, the
action of `λ` on `f^* G` is the abelian inverse image of the action of `λ` on `G`. -/
@[weil "def_fka2_inverse_image_lambda"]
lemma smallEtaleModuleSheafInverseImageForgetIso_hom_app_comp_map_smulEnd (l : Λ)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} Λ)) :
    (sheafCompose (SmallEtale.topology B T.obj T.property)
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (Sheaf.smulEnd (SmallEtale.topology B T.obj T.property) l
          ((smallEtaleModuleSheafInverseImage.{w} B f Λ).obj G)) ≫
        (smallEtaleModuleSheafInverseImageForgetIso.{w} B f Λ).hom.app G =
      (smallEtaleModuleSheafInverseImageForgetIso.{w} B f Λ).hom.app G ≫
        (smallEtaleInverseImage B f AddCommGrpCat.{w}).map
          ((sheafCompose (SmallEtale.topology B S.obj S.property)
            (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
            (Sheaf.smulEnd (SmallEtale.topology B S.obj S.property) l G)) := by
  rw [← smallEtaleModuleSheafInverseImage_map_smulEnd]
  exact smallEtaleModuleSheafInverseImageForgetIso_hom_naturality B f Λ _

end Commutative

end AlgebraicGeometry

end
