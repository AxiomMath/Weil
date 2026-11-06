module

public import Weil.Defs.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# The value of the direct image of a presheaf on the small étale site

Let `B` be a big étale site, `f : X ⟶ Y` a morphism of it, `U` an étale `Y`-scheme and `F` a
presheaf on the small étale category of `X`, with values in any category `A`. The base change
`U ×_Y X`, with its projection to `X`, is an étale `X`-scheme, and `(U ×_Y X, pr₁)` is a terminal
object of the index category `I_U` of the direct image. Hence the projection of the limit
`lim_{(V, h) ∈ I_U} F(V)` to its factor at `(U ×_Y X, pr₁)` is an isomorphism
`lim_{I_U} F ≅ F(U ×_Y X)`. It is natural in `U` (for `g : U' ⟶ U` the right-hand side restricts
along the base change `U' ×_Y X ⟶ U ×_Y X` of `g`) and in `F`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.limitDirectImageDiagramIso`: the isomorphism
  `lim_{I_U} F ≅ F(U ×_Y X)`, given by the projection to the factor at the terminal object.

## Main results

* `AlgebraicGeometry.BigEtaleSite.limitDirectImageDiagramIso_hom`: its forward map is the
  projection of the limit.
* `BigEtaleSite.limit_pre_directImageIndexMap_comp_limitDirectImageDiagramIso_hom`:
  naturality in `U`.
* `AlgebraicGeometry.BigEtaleSite.limMap_comp_limitDirectImageDiagramIso_hom`: naturality in `F`.
* `AlgebraicGeometry.BigEtaleSite.presheafDirectImage_obj_obj`: the value of the presheaf direct
  image at `U` is `F(U ×_Y X)`.

## Implementation notes

The étale category is the small étale category `SmallEtale` of the big étale site, and the base
change is written `U ×_Y X` (the pullback of the structure morphism of `U` along `f`), as in
`AlgebraicGeometry.BigEtaleSite.smallEtaleBaseChange`; the source writes `X ×_Y U`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2]
* [Stacks Project, Tag 03PY](https://stacks.math.columbia.edu/tag/03PY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {A : Type w} [Category.{v} A]

/-- The value of the presheaf direct image `f_* F` at an étale `Y`-scheme `U` is `F(U ×_Y X)`. -/
theorem presheafDirectImage_obj_obj (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) :
    ((presheafDirectImage B f A).obj F).obj (op U) =
      F.obj (op ((smallEtaleBaseChange B f).obj U)) :=
  rfl

/-- The leg of the cone `presheafDirectImageCone` at the terminal object `(U ×_Y X, pr₁)` of
`I_U` is the identity. -/
theorem presheafDirectImageCone_π_app_directImageIndexBaseChange
    (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) (U : SmallEtale B Y.obj Y.property) :
    (presheafDirectImageCone (f := f) F U).π.app (op (directImageIndexBaseChange B f U)) =
      𝟙 _ := by
  change F.map ((CostructuredArrow.proj _ _).op.map
    ((isTerminalDirectImageIndexBaseChange B f U).op.to _)) = 𝟙 _
  rw [IsInitial.to_self, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- The projections of the chosen limit of `F` over `I_U`, through the identification
`presheafDirectImageObjIsoLimit` of `(f_* F)(U)` with that limit, are the legs of
`presheafDirectImageCone`. -/
theorem limit_π_eq_presheafDirectImageObjIsoLimit_inv_comp
    (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) (U : SmallEtale B Y.obj Y.property)
    (j : (DirectImageIndex B f U)ᵒᵖ) :
    limit.π (directImageDiagram (f := f) F U) j =
      (presheafDirectImageObjIsoLimit (f := f) F U).inv ≫
        (presheafDirectImageCone F U).π.app j := by
  exact (Iso.eq_inv_comp _).mpr (presheafDirectImageObjIsoLimit_hom_π F U j)

/-- **The value of the direct image is the value at the base change**: the projection of
`lim_{(V, h) ∈ I_U} F(V)` to its factor at the terminal object `(U ×_Y X, pr₁)` of `I_U` is an
isomorphism `lim_{I_U} F ≅ F(U ×_Y X)`. -/
@[weil "lem_fk102_direct_image_value"]
def limitDirectImageDiagramIso (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) :
    limit (directImageDiagram (f := f) F U) ≅ F.obj (op ((smallEtaleBaseChange B f).obj U)) :=
  @asIso _ _ _ _ (limit.π (directImageDiagram (f := f) F U) (op (directImageIndexBaseChange B f U)))
    (isIso_π_of_isInitial (isTerminalDirectImageIndexBaseChange B f U).op
      (directImageDiagram (f := f) F U))

/-- The isomorphism `lim_{I_U} F ≅ F(U ×_Y X)` is the projection of the limit. -/
@[weil "lem_fk102_direct_image_value", simp]
theorem limitDirectImageDiagramIso_hom (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) :
    (limitDirectImageDiagramIso f F U).hom =
      limit.π (directImageDiagram (f := f) F U) (op (directImageIndexBaseChange B f U)) :=
  rfl

/-- The inverse of `limitDirectImageDiagramIso` is the inverse of the identification
`presheafDirectImageObjIsoLimit` of `(f_* F)(U) = F(U ×_Y X)` with the limit. -/
theorem limitDirectImageDiagramIso_inv (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) :
    (limitDirectImageDiagramIso f F U).inv = (presheafDirectImageObjIsoLimit (f := f) F U).hom := by
  rw [← cancel_mono (limitDirectImageDiagramIso f F U).hom, Iso.inv_hom_id,
    limitDirectImageDiagramIso_hom]
  erw [presheafDirectImageObjIsoLimit_hom_π,
    presheafDirectImageCone_π_app_directImageIndexBaseChange]
  rfl

/-- The diagram of `F` over `I_{U'}`, pulled back from `I_U` along `I_{U'} ⥤ I_U`, is the
diagram of `F` over `I_{U'}`, so it has a limit. -/
instance (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) {U' U : SmallEtale B Y.obj Y.property}
    (g : U' ⟶ U) :
    HasLimit ((directImageIndexMap B f g).op ⋙ directImageDiagram (f := f) F U) :=
  inferInstanceAs (HasLimit (directImageDiagram (f := f) F U'))

/-- **Naturality in `U`**: for `g : U' ⟶ U`, the map of limits `lim_{I_U} F ⟶ lim_{I_{U'}} F`
induced by `I_{U'} ⥤ I_U` corresponds, under `lim_{I_U} F ≅ F(U ×_Y X)`, to the restriction of
`F` along the base change `U' ×_Y X ⟶ U ×_Y X` of `g`. -/
@[weil "lem_fk102_direct_image_value", reassoc]
theorem limit_pre_directImageIndexMap_comp_limitDirectImageDiagramIso_hom
    (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) {U' U : SmallEtale B Y.obj Y.property}
    (g : U' ⟶ U) :
    (limit.pre (directImageDiagram (f := f) F U) (directImageIndexMap B f g).op :
        limit (directImageDiagram (f := f) F U) ⟶ limit (directImageDiagram (f := f) F U')) ≫
      (limitDirectImageDiagramIso f F U').hom =
    (limitDirectImageDiagramIso f F U).hom ≫ F.map ((smallEtaleBaseChange B f).map g).op := by
  rw [limitDirectImageDiagramIso_hom, limitDirectImageDiagramIso_hom]
  erw [limit.pre_π]
  rw [limit_π_eq_presheafDirectImageObjIsoLimit_inv_comp,
    limit_π_eq_presheafDirectImageObjIsoLimit_inv_comp]
  have h := presheafDirectImage_map_comp_presheafDirectImageCone_π (f := f) F g
    (op (directImageIndexBaseChange B f U'))
  rw [presheafDirectImageCone_π_app_directImageIndexBaseChange] at h
  erw [Category.comp_id] at h
  rw [← h]
  erw [presheafDirectImageCone_π_app_directImageIndexBaseChange, Category.comp_id]
  rfl

/-- **Naturality in `F`**: for `α : F ⟶ G`, the map of limits `lim_{I_U} F ⟶ lim_{I_U} G`
induced by `α` corresponds, under the isomorphisms `lim_{I_U} F ≅ F(U ×_Y X)` and
`lim_{I_U} G ≅ G(U ×_Y X)`, to the component of `α` at `U ×_Y X`. -/
@[weil "lem_fk102_direct_image_value", reassoc]
theorem limMap_comp_limitDirectImageDiagramIso_hom
    {F G : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A} (α : F ⟶ G)
    (U : SmallEtale B Y.obj Y.property) :
    limMap (Functor.whiskerLeft
        (CostructuredArrow.proj (smallEtaleToOverMap B f) _).op α :
        directImageDiagram (f := f) F U ⟶ directImageDiagram (f := f) G U) ≫
      (limitDirectImageDiagramIso f G U).hom =
    (limitDirectImageDiagramIso f F U).hom ≫ α.app (op ((smallEtaleBaseChange B f).obj U)) := by
  rw [limitDirectImageDiagramIso_hom, limitDirectImageDiagramIso_hom]
  exact limMap_π _ _

end AlgebraicGeometry.BigEtaleSite
