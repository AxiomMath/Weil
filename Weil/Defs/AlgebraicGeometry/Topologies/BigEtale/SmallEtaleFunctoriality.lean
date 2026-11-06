module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
public import Weil.Attr

/-!
# The direct image of presheaves on small étale sites as a limit

Let `B` be a big étale site and `f : X ⟶ Y` a morphism of it. For an étale `Y`-scheme `U`, let
`I_U` be the category of pairs `(V, h)` with `V` étale over `X` and `h : V ⟶ U` a morphism of
`Y`-schemes, `V` being a `Y`-scheme through `f`; a morphism `(V, h) ⟶ (V', h')` is a morphism
`e : V ⟶ V'` of étale `X`-schemes with `h' ∘ e = h`. In Lean, `I_U` is the costructured arrow
category of the functor `V ↦ (V, f ∘ π_V)` from the small étale category of `X` to schemes over
`Y`, at `U`. A morphism `U' ⟶ U` induces by composition a functor `I_{U'} ⥤ I_U`.

The direct image of a presheaf `F` on the small étale category of `X` (with values in any
category `A`, for instance sets or abelian groups) is the presheaf on the small étale category
of `Y`
`(f_* F)(U) = lim_{(V, h) ∈ I_U} F(V)`.
The base change `U ×_Y X`, with its first projection, is a terminal object of `I_U`, so this
limit exists and is `F(U ×_Y X)`. We therefore define `f_*` as precomposition with base change,
`U ↦ F(U ×_Y X)` (which on sheaves is `AlgebraicGeometry.BigEtaleSite.smallPushforward`), and
prove that its value at `U` is the limit over `I_U` and that its restriction maps are the maps
of limits induced by the functors `I_{U'} ⥤ I_U`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.smallEtaleToOverMap`: an étale `X`-scheme regarded as a
  `Y`-scheme through `f`.
* `AlgebraicGeometry.BigEtaleSite.DirectImageIndex`: the category `I_U`.
* `AlgebraicGeometry.BigEtaleSite.directImageIndexMap`: the functor `I_{U'} ⥤ I_U` induced by
  a morphism `U' ⟶ U`.
* `AlgebraicGeometry.BigEtaleSite.presheafDirectImage`: the direct image `f_*` of presheaves.

## Main results

* `AlgebraicGeometry.BigEtaleSite.isTerminalDirectImageIndexBaseChange`: `(U ×_Y X, pr₁)` is
  terminal in `I_U`.
* `AlgebraicGeometry.BigEtaleSite.isLimitPresheafDirectImageCone`: `(f_* F)(U)` is the limit
  of `F` over `I_U`.
* `AlgebraicGeometry.BigEtaleSite.presheafDirectImage_map_comp_presheafDirectImageCone_π`: the
  restriction map of `f_* F` along `U' ⟶ U` is the map of limits induced by `I_{U'} ⥤ I_U`.
* `AlgebraicGeometry.BigEtaleSite.sheafToPresheaf_obj_smallPushforward_obj`: on sheaves, the
  direct image `smallPushforward` has underlying presheaf the presheaf direct image.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2]
* [Stacks Project, Tag 03PY](https://stacks.math.columbia.edu/tag/03PY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- An étale `X`-scheme `V`, regarded as a `Y`-scheme through `f`: the structure morphism is
`f ∘ π_V`. -/
abbrev smallEtaleToOverMap : SmallEtale B X.obj X.property ⥤ Over Y :=
  SmallEtale.inclusion B X.obj X.property ⋙ Over.map f

/-- **The index category `I_U`** of the direct image at an étale `Y`-scheme `U`: pairs `(V, h)`
of an étale `X`-scheme `V` and a morphism `h : V ⟶ U` with `π_U ∘ h = f ∘ π_V`; a morphism
`(V, h) ⟶ (V', h')` is a morphism `e : V ⟶ V'` of étale `X`-schemes with `h' ∘ e = h`. -/
@[weil "def_fk102_direct_image"]
abbrev DirectImageIndex (U : SmallEtale B Y.obj Y.property) :=
  CostructuredArrow (smallEtaleToOverMap B f) ((SmallEtale.inclusion B Y.obj Y.property).obj U)

/-- The functor `I_{U'} ⥤ I_U` induced by a morphism `g : U' ⟶ U` of étale `Y`-schemes,
sending `(V, h)` to `(V, g ∘ h)`. -/
@[weil "def_fk102_direct_image"]
abbrev directImageIndexMap {U' U : SmallEtale B Y.obj Y.property} (g : U' ⟶ U) :
    DirectImageIndex B f U' ⥤ DirectImageIndex B f U :=
  CostructuredArrow.map ((SmallEtale.inclusion B Y.obj Y.property).map g)

/-- The object `(U ×_Y X, pr₁)` of `I_U`. -/
def directImageIndexBaseChange (U : SmallEtale B Y.obj Y.property) : DirectImageIndex B f U :=
  CostructuredArrow.mk (Y := (smallEtaleBaseChange B f).obj U)
    (Over.homMk (pullback.fst U.obj.hom f) pullback.condition)

/-- The morphism from an object `(V, h)` of `I_U` to `(U ×_Y X, pr₁)`, given by `(h, π_V)`. -/
def directImageIndexToBaseChange {U : SmallEtale B Y.obj Y.property}
    (P : DirectImageIndex B f U) : P ⟶ directImageIndexBaseChange B f U :=
  CostructuredArrow.homMk
    (ObjectProperty.homMk (Over.homMk (pullback.lift P.hom.left P.left.obj.hom
      (Over.w P.hom)) (pullback.lift_snd _ _ _)))
    (Over.OverMorphism.ext (pullback.lift_fst _ _ _))

/-- The morphism to `(U ×_Y X, pr₁)` is compatible with the functors `I_{U'} ⥤ I_U`. -/
theorem directImageIndexToBaseChange_left_comp_map {U' U : SmallEtale B Y.obj Y.property}
    (P : DirectImageIndex B f U') (g : U' ⟶ U) :
    (directImageIndexToBaseChange B f P).left ≫ (smallEtaleBaseChange B f).map g =
      (directImageIndexToBaseChange B f ((directImageIndexMap B f g).obj P)).left := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change pullback.lift _ _ _ ≫ ((Over.pullback f).map g.hom).left = pullback.lift _ _ _
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    change pullback.lift _ _ _ ≫
      pullback.lift (pullback.fst _ f ≫ g.hom.left) (pullback.snd _ f) _ ≫
        pullback.fst _ f = _
    erw [pullback.lift_fst, pullback.lift_fst_assoc]
    rfl
  · rw [pullback.lift_snd, Category.assoc]
    change pullback.lift _ _ _ ≫
      pullback.lift (pullback.fst _ f ≫ g.hom.left) (pullback.snd _ f) _ ≫
        pullback.snd _ f = _
    erw [pullback.lift_snd, pullback.lift_snd]
    rfl

/-- **`(U ×_Y X, pr₁)` is a terminal object of `I_U`.** -/
def isTerminalDirectImageIndexBaseChange (U : SmallEtale B Y.obj Y.property) :
    IsTerminal (directImageIndexBaseChange B f U) :=
  IsTerminal.ofUniqueHom (directImageIndexToBaseChange B f) fun P m ↦ by
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (congrArg CommaMorphism.left (CostructuredArrow.w m)).trans
        (pullback.lift_fst _ _ _).symm
    · exact (Over.w m.left.hom).trans (pullback.lift_snd _ _ _).symm

/-- **The direct image `f_*` of presheaves** on the small étale category of `X`, with values in
any category `A`: `(f_* F)(U) = F(U ×_Y X)`, a morphism `U' ⟶ U` acting by the restriction of
`F` along its base change, and a morphism `F ⟶ G` inducing `f_* F ⟶ f_* G`. The value at `U` is
the limit of `F` over `I_U` (`isLimitPresheafDirectImageCone`). -/
@[weil "def_fk102_direct_image"]
abbrev presheafDirectImage (A : Type w) [Category.{v} A] :
    ((SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) ⥤ ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft _ _ A).obj (smallEtaleBaseChange B f).op

variable {B f} {A : Type w} [Category.{v} A]

/-- The diagram `(V, h) ↦ F(V)` on `I_Uᵒᵖ` whose limit is `(f_* F)(U)`. -/
abbrev directImageDiagram (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) : (DirectImageIndex B f U)ᵒᵖ ⥤ A :=
  (CostructuredArrow.proj (smallEtaleToOverMap B f) _).op ⋙ F

/-- The cone over `(V, h) ↦ F(V)` with apex `(f_* F)(U) = F(U ×_Y X)`, whose leg at `(V, h)` is
restriction along the morphism `V ⟶ U ×_Y X` determined by `h`. -/
def presheafDirectImageCone (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) : Cone (directImageDiagram (f := f) F U) :=
  coneOfDiagramInitial (isTerminalDirectImageIndexBaseChange B f U).op _

theorem presheafDirectImageCone_pt (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) :
    (presheafDirectImageCone (f := f) F U).pt = ((presheafDirectImage B f A).obj F).obj (op U) :=
  rfl

/-- **`(f_* F)(U) = lim_{(V, h) ∈ I_U} F(V)`.** -/
@[weil "def_fk102_direct_image"]
def isLimitPresheafDirectImageCone (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) : IsLimit (presheafDirectImageCone (f := f) F U) :=
  limitOfDiagramInitial _ _

instance (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) (U : SmallEtale B Y.obj Y.property) :
    HasLimit (directImageDiagram (f := f) F U) :=
  ⟨⟨⟨_, isLimitPresheafDirectImageCone F U⟩⟩⟩

/-- **The restriction maps of `f_*F` are induced by the functors `I_{U'} ⥤ I_U`**: for
`g : U' ⟶ U`, restricting along `g` and then projecting to the factor `(V, h)` of
`(f_* F)(U') = lim_{I_{U'}} F` is projecting to the factor `(V, g ∘ h)` of
`(f_* F)(U) = lim_{I_U} F`. -/
@[weil "def_fk102_direct_image", reassoc]
theorem presheafDirectImage_map_comp_presheafDirectImageCone_π
    (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A) {U' U : SmallEtale B Y.obj Y.property}
    (g : U' ⟶ U) (j : (DirectImageIndex B f U')ᵒᵖ) :
    ((presheafDirectImage B f A).obj F).map g.op ≫ (presheafDirectImageCone F U').π.app j =
      (presheafDirectImageCone F U).π.app ((directImageIndexMap B f g).op.obj j) := by
  change F.map _ ≫ F.map _ = F.map _
  erw [← F.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact directImageIndexToBaseChange_left_comp_map B f j.unop g

/-- The value of the direct image at `U` as the chosen limit of `F` over `I_U`. -/
def presheafDirectImageObjIsoLimit (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) :
    ((presheafDirectImage B f A).obj F).obj (op U) ≅ limit (directImageDiagram (f := f) F U) :=
  (isLimitPresheafDirectImageCone F U).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem presheafDirectImageObjIsoLimit_hom_π (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (U : SmallEtale B Y.obj Y.property) (j : (DirectImageIndex B f U)ᵒᵖ) :
    (presheafDirectImageObjIsoLimit F U).hom ≫ limit.π _ j =
      (presheafDirectImageCone F U).π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- On sheaves, the direct image `smallPushforward` along `f` has as underlying presheaf the
direct image of the underlying presheaf. -/
@[weil "def_fk102_direct_image"]
theorem sheafToPresheaf_obj_smallPushforward_obj
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    ((B.smallPushforward f A).obj F).obj = (presheafDirectImage B f A).obj F.obj :=
  rfl

end AlgebraicGeometry.BigEtaleSite
