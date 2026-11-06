module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import Weil.Attr

/-!
# The unit of extension by zero along an étale morphism

Let `j : U ⟶ X` be an étale morphism, `U` regarded as an object of the small étale site of `X`,
and `F` a sheaf of `Λ`-modules (or of abelian groups) on the small étale site of `U`. The unit
`η_F : F ⟶ (j_! F)|_U` of the adjunction `j_! ⊣ j^{-1}` sends a section `s ∈ F(V)`, over an
étale `U`-scheme `V`, to the image in `(j_! F)(V → U → X) = (j_! F)|_U (V)` of the class
`[V → U, s]` of `s` in the presheaf extension by zero `j_{p!} F`. Here `j_{p!} F` is the left Kan
extension of `F` along composition with `j`: its value at `V → U → X` is the colimit of the
`F(V')` over the étale `U`-schemes `V'` with an `X`-morphism `V → V'`, and the class
`[V → U, s]` is the image of `s` under the colimit injection of the index `(V, 𝟙)`.

The description holds for the unit of the pullback of sheaves along any continuous functor of
sites constructed as a sheafified left Kan extension, and is proved in that generality.

## Main definitions

* `AlgebraicGeometry.moduleExtensionByZeroUnit`: the unit `η_F : F ⟶ (j_! F)|_U` for sheaves
  of `Λ`-modules.
* `AlgebraicGeometry.abelianExtensionByZeroUnit`: the same for abelian sheaves.

## Main results

* `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom_app_eq_colimit_ι`:
  for a continuous functor `G` of sites, the unit of `G^* ⊣ G_*` at a sheaf `F` and an object
  `V` is the colimit injection of `F(V)` at the index `(V, 𝟙)` into `(G_{p!} F)(G V)`, followed by
  the map to the sheafification.
* `AlgebraicGeometry.moduleExtensionByZeroUnit_hom_app` and
  `AlgebraicGeometry.abelianExtensionByZeroUnit_hom_app`: the component of `η_F` at `V` sends
  `s` to `[V → U, s]` and then into `j_! F`.
* `AlgebraicGeometry.moduleExtensionByZeroUnit_naturality` and
  `AlgebraicGeometry.abelianExtensionByZeroUnit_naturality`: `η` is natural in `F`.

## Implementation notes

Extension by zero and restriction are those of the Stacks Project on the small étale sites
`SmallEtale B X hX` of a big étale site `B` (`moduleExtensionByZero`, `moduleRestriction`,
`abelianExtensionByZero`, `abelianRestriction`), and `η_F` is the unit of their defining
adjunction. The étale morphism is the structure morphism of an object `U` of the small étale
site of `X`. Restriction of a sheaf `G` on `X` to `U` is precomposition with `V ↦ (V → U → X)`,
so `(j_! F)|_U (V)` is literally `(j_! F)(V → U → X)`. The presheaf `j_{p!} F` is the left Kan
extension rather than the direct sum `⨁_φ F(V →^φ U)` over the `X`-morphisms `φ : V → U`; the
summand of `φ` is the colimit injection of the index `(V, φ)`, so `[φ, s]` for `φ` the structure
morphism of `V` is the class above.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ u v

namespace CategoryTheory.Functor.sheafPullbackConstruction

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D] (G : C ⥤ D)
  (A : Type u₁) [Category.{v₁} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [Functor.IsContinuous G J K] [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F] [HasWeakSheafify K A]

/-- The unit of the adjunction `G^* ⊣ G_*`, for `G^*` the sheafified left Kan extension, is the
unit of the left Kan extension followed by the map to the sheafification. -/
theorem sheafAdjunctionContinuous_unit_app_hom_app_eq_lanUnit (F : Sheaf J A) (V : C) :
    ((sheafAdjunctionContinuous G A J K).unit.app F).hom.app (op V) =
      (G.op.lanUnit.app F.obj).app (op V) ≫
        (toSheafify K (G.op.lan.obj F.obj)).app (op (G.obj V)) := by
  simp only [sheafAdjunctionContinuous, Adjunction.restrictFullyFaithful,
    Adjunction.comp_homEquiv, Functor.FullyFaithful.homEquiv]
  simp only [Functor.id_obj, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.whiskeringLeft_obj_obj, Equiv.trans_def, Equiv.symm_mk,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply, Equiv.coe_fn_mk, Functor.id_map,
    Iso.homCongr_apply, Iso.app_inv, Iso.refl_hom, Category.comp_id, Iso.refl_inv,
    Category.id_comp, ObjectProperty.homMk_hom, NatTrans.comp_app, Functor.op_obj]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, lanAdjunction_unit,
    ObjectProperty.ι_obj, sheafificationAdjunction_unit_app, ObjectProperty.ι_map,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_comp, NatTrans.comp_app, Functor.op_obj,
    Functor.whiskerLeft_app, Category.assoc]
  erw [Category.comp_id, Category.comp_id]
  rfl

/-- The unit of the adjunction `G^* ⊣ G_*` at a sheaf `F` and an object `V` is the colimit
injection of `F(V)` at the index `(V, 𝟙)` into the left Kan extension at `G V`, followed by the
map to the sheafification. -/
theorem sheafAdjunctionContinuous_unit_app_hom_app_eq_colimit_ι (F : Sheaf J A)
    [G.op.HasPointwiseLeftKanExtension F.obj] (V : C) :
    ((sheafAdjunctionContinuous G A J K).unit.app F).hom.app (op V) =
      colimit.ι (CostructuredArrow.proj G.op (op (G.obj V)) ⋙ F.obj)
          (CostructuredArrow.mk (𝟙 _)) ≫
        (G.op.leftKanExtensionObjIsoColimit F.obj (op (G.obj V))).inv ≫
        (toSheafify K (G.op.lan.obj F.obj)).app (op (G.obj V)) := by
  have h : (G.op.lanUnit.app F.obj).app (op V) =
      colimit.ι (CostructuredArrow.proj G.op (op (G.obj V)) ⋙ F.obj)
          (CostructuredArrow.mk (𝟙 _)) ≫
        (G.op.leftKanExtensionObjIsoColimit F.obj (op (G.obj V))).inv :=
    (Iso.eq_comp_inv _).mpr
      (Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom G.op F.obj (op V))
  rw [sheafAdjunctionContinuous_unit_app_hom_app_eq_lanUnit, h]
  exact Category.assoc _ _ _

end CategoryTheory.Functor.sheafPullbackConstruction

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

section Modules

variable (Λ : Type v) [Ring Λ]

/-- The unit `η_F : F ⟶ (j_! F)|_U` of extension by zero along the étale morphism `j : U ⟶ X`,
for a sheaf `F` of `Λ`-modules on the small étale site of `U`. -/
@[weil "def_fk108_extension_by_zero_unit"]
abbrev moduleExtensionByZeroUnit
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ)) :
    F ⟶ (moduleRestriction B X hX U Λ).obj ((moduleExtensionByZero B X hX U Λ).obj F) :=
  (moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F

/-- The component of `η_F` at `V` sends `s ∈ F(V)` to the class `[V → U, s]` in the presheaf
extension by zero at `V → U → X` (the colimit injection of the index `(V, 𝟙)`), then to its image
in the sheafification `(j_! F)(V → U → X)`. -/
@[weil "def_fk108_extension_by_zero_unit"]
theorem moduleExtensionByZeroUnit_hom_app
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ))
    (V : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (moduleExtensionByZeroUnit B X hX U Λ F).hom.app (op V) =
      colimit.ι (CostructuredArrow.proj (smallEtalePostcompose B X hX U).op
          (op ((smallEtalePostcompose B X hX U).obj V)) ⋙ F.obj)
          (CostructuredArrow.mk (𝟙 _)) ≫
        ((smallEtalePostcompose B X hX U).op.leftKanExtensionObjIsoColimit F.obj
          (op ((smallEtalePostcompose B X hX U).obj V))).inv ≫
        (toSheafify (SmallEtale.topology B X hX)
          ((smallEtalePostcompose B X hX U).op.lan.obj F.obj)).app
          (op ((smallEtalePostcompose B X hX U).obj V)) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom_app_eq_colimit_ι
    _ _ _ _ F V

/-- The unit `η` of extension by zero of sheaves of `Λ`-modules is natural in the sheaf. -/
theorem moduleExtensionByZeroUnit_naturality
    {F F' : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ)} (α : F ⟶ F') :
    α ≫ moduleExtensionByZeroUnit B X hX U Λ F' =
      moduleExtensionByZeroUnit B X hX U Λ F ≫
        (moduleRestriction B X hX U Λ).map ((moduleExtensionByZero B X hX U Λ).map α) :=
  (moduleExtensionByZeroAdjunction B X hX U Λ).unit.naturality α

end Modules

section Abelian

/-- The unit `η_F : F ⟶ (j_! F)|_U` of extension by zero along the étale morphism `j : U ⟶ X`,
for an abelian sheaf `F` on the small étale site of `U`. -/
@[weil "def_fk108_extension_by_zero_unit"]
abbrev abelianExtensionByZeroUnit
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    F ⟶ (abelianRestriction B X hX U).obj ((abelianExtensionByZero B X hX U).obj F) :=
  (abelianExtensionByZeroAdjunction B X hX U).unit.app F

/-- The component of `η_F` at `V`, for an abelian sheaf `F`, sends `s ∈ F(V)` to the class
`[V → U, s]` in the presheaf extension by zero at `V → U → X`, then to its image in
`(j_! F)(V → U → X)`. -/
@[weil "def_fk108_extension_by_zero_unit"]
theorem abelianExtensionByZeroUnit_hom_app
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (abelianExtensionByZeroUnit B X hX U F).hom.app (op V) =
      colimit.ι (CostructuredArrow.proj (smallEtalePostcompose B X hX U).op
          (op ((smallEtalePostcompose B X hX U).obj V)) ⋙ F.obj)
          (CostructuredArrow.mk (𝟙 _)) ≫
        ((smallEtalePostcompose B X hX U).op.leftKanExtensionObjIsoColimit F.obj
          (op ((smallEtalePostcompose B X hX U).obj V))).inv ≫
        (toSheafify (SmallEtale.topology B X hX)
          ((smallEtalePostcompose B X hX U).op.lan.obj F.obj)).app
          (op ((smallEtalePostcompose B X hX U).obj V)) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom_app_eq_colimit_ι
    _ _ _ _ F V

/-- The unit `η` of extension by zero of abelian sheaves is natural in the sheaf. -/
theorem abelianExtensionByZeroUnit_naturality
    {F F' : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}} (α : F ⟶ F') :
    α ≫ abelianExtensionByZeroUnit B X hX U F' =
      abelianExtensionByZeroUnit B X hX U F ≫
        (abelianRestriction B X hX U).map ((abelianExtensionByZero B X hX U).map α) :=
  (abelianExtensionByZeroAdjunction B X hX U).unit.naturality α

end Abelian

end AlgebraicGeometry
