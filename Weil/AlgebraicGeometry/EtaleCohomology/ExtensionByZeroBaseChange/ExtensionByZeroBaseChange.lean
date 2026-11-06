module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# Extension by zero commutes with inverse image

Let `B` be a big étale site, `Y` a scheme of `B`, `U` an object of the small étale site of `Y`,
i.e. an étale morphism `f : X ⟶ Y`, and `g : Z ⟶ Y` any morphism of schemes of `B`. Write
`X' = X ×_Y Z`, with projections `f' : X' ⟶ Z` (the base change of `U` along `g`, an object of
the small étale site of `Z`) and `g' : X' ⟶ X`. For every abelian sheaf `F` on the small étale
site of `X` there is an isomorphism `g^* (f_! F) ≅ f'_! (g'^* F)`, natural in `F`.

Both functors `F ↦ g^* (f_! F)` and `F ↦ f'_! (g'^* F)` are left adjoints, of `f^{-1} ∘ g_*` and
`g'_* ∘ f'^{-1}`, and these right adjoints agree; the isomorphism is the mate of that agreement.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageExtensionByZeroIso`: the isomorphism of functors
  `f'_! ∘ g'^* ≅ g^* ∘ f_!` on abelian sheaves.
* `AlgebraicGeometry.smallEtaleInverseImageExtensionByZeroObjIso`: its component at a sheaf `F`.
* `AlgebraicGeometry.smallEtaleInverseImageExtensionByZeroObjIso_hom_naturality`: naturality
  in `F`.
* `AlgebraicGeometry.smallEtaleInverseImageModuleExtensionByZeroIso`: the same for sheaves of
  `Λ`-modules.

## Implementation notes

The isomorphism is the Stacks Project's `AlgebraicGeometry.abelianExtensionByZeroBaseChangeIso`,
restated with the inverse image functor `AlgebraicGeometry.smallEtaleInverseImage`. The étale
morphism `f` is an object `U` of the small étale site of `Y`; its base change along `g` is
`(smallEtaleBaseChange B g).obj U`, and `g'` is
`AlgebraicGeometry.baseChangedEtaleProjection B g U`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 84.
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Y Z : B.Scheme} (g : Z ⟶ Y) (U : SmallEtale B Y.1 Y.property)

/-- **Extension by zero commutes with inverse image.** For an étale `f : X ⟶ Y` (an object `U`
of the small étale site of `Y`) and any `g : Z ⟶ Y`, with `f' : X ×_Y Z ⟶ Z` and
`g' : X ×_Y Z ⟶ X` the projections, `f'_! ∘ g'^* ≅ g^* ∘ f_!` on abelian sheaves. -/
@[weil "lem_fk108_extension_by_zero_base_change"]
def smallEtaleInverseImageExtensionByZeroIso :
    smallEtaleInverseImage B (baseChangedEtaleProjection B g U) AddCommGrpCat.{u + 1} ⋙
        abelianExtensionByZero B Z.1 Z.property ((smallEtaleBaseChange B g).obj U) ≅
      abelianExtensionByZero B Y.1 Y.property U ⋙
        smallEtaleInverseImage B g AddCommGrpCat.{u + 1} :=
  abelianExtensionByZeroBaseChangeIso B g U

/-- The isomorphism `f'_! (g'^* F) ≅ g^* (f_! F)` at an abelian sheaf `F` on the small étale
site of `X`. -/
def smallEtaleInverseImageExtensionByZeroObjIso
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    (abelianExtensionByZero B Z.1 Z.property ((smallEtaleBaseChange B g).obj U)).obj
        ((smallEtaleInverseImage B (baseChangedEtaleProjection B g U) AddCommGrpCat.{u + 1}).obj
          F) ≅
      (smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj
        ((abelianExtensionByZero B Y.1 Y.property U).obj F) :=
  (smallEtaleInverseImageExtensionByZeroIso B g U).app F

/-- The isomorphism `f'_! (g'^* F) ≅ g^* (f_! F)` is natural in `F`. -/
@[reassoc]
theorem smallEtaleInverseImageExtensionByZeroObjIso_hom_naturality
    {F F' : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}} (α : F ⟶ F') :
    (abelianExtensionByZero B Z.1 Z.property ((smallEtaleBaseChange B g).obj U)).map
        ((smallEtaleInverseImage B (baseChangedEtaleProjection B g U)
          AddCommGrpCat.{u + 1}).map α) ≫
        (smallEtaleInverseImageExtensionByZeroObjIso B g U F').hom =
      (smallEtaleInverseImageExtensionByZeroObjIso B g U F).hom ≫
        (smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).map
          ((abelianExtensionByZero B Y.1 Y.property U).map α) :=
  (smallEtaleInverseImageExtensionByZeroIso B g U).hom.naturality α

/-- Extension by zero of sheaves of `Λ`-modules commutes with inverse image:
`f'_! ∘ g'^* ≅ g^* ∘ f_!`. -/
def smallEtaleInverseImageModuleExtensionByZeroIso (Λ : Type v) [Ring Λ] :
    smallEtaleInverseImage B (baseChangedEtaleProjection B g U)
        (ModuleCat.{max (u + 1) v} Λ) ⋙
        moduleExtensionByZero B Z.1 Z.property ((smallEtaleBaseChange B g).obj U) Λ ≅
      moduleExtensionByZero B Y.1 Y.property U Λ ⋙
        smallEtaleInverseImage B g (ModuleCat.{max (u + 1) v} Λ) :=
  moduleExtensionByZeroBaseChangeIso B g U Λ

end AlgebraicGeometry

end
