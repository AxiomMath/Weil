module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import Weil.Attr

/-!
# The inverse image presheaf on the small étale site

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B`. For an étale `T`-scheme `V`,
let `J_V` be the category of pairs `(U, h)` with `U` étale over `S` and `h : V ⟶ U` a morphism of
schemes with `h ≫ π_U = π_V ≫ f`; a morphism `(U, h) ⟶ (U', h')` is a morphism `e : U ⟶ U'` of
étale `S`-schemes with `h ≫ e = h'`. For a presheaf `G` on the small étale site of `S` (of sets,
of abelian groups, or with values in any category with the relevant colimits), the inverse image
presheaf is
`(f⁻¹_pre G)(V) = colim_{(U, h) ∈ J_Vᵒᵖ} G(U)`,
a morphism `V' ⟶ V` acting through the functor `J_V ⥤ J_V'` given by precomposition.

By the universal property of the fibre product, a pair `(U, h)` is the same as an object `U`
together with a morphism `V ⟶ T ×_S U` of étale `T`-schemes, so `J_V` is the comma category
`StructuredArrow V (smallEtaleBaseChange B f)`. The presheaf `f⁻¹_pre G` is then the left Kan
extension of `G` along the opposite of base change, whose pointwise formula is exactly the
displayed colimit.

## Main definitions

* `AlgebraicGeometry.smallEtaleHomBaseChangeEquiv` — morphisms `V ⟶ T ×_S U` of étale
  `T`-schemes are the morphisms `h : V ⟶ U` with `h ≫ π_U = π_V ≫ f`.
* `AlgebraicGeometry.SmallEtaleInverseImageIndex` — the index category `J_V`.
* `AlgebraicGeometry.smallEtaleInverseImagePresheaf` — the inverse image presheaf functor
  `G ↦ f⁻¹_pre G`, the left Kan extension along `(smallEtaleBaseChange B f).op`.
* `AlgebraicGeometry.smallEtaleInverseImagePresheafObjIsoColimit` — its sections over `V` are
  the colimit of `G(U)` over `J_Vᵒᵖ`.

## Main results

* `AlgebraicGeometry.smallEtaleHomBaseChangeEquiv_comp` — under that bijection, composing with a
  morphism of `J_V` is composing with the underlying morphism of schemes.
* `AlgebraicGeometry.ι_smallEtaleInverseImagePresheafObjIsoColimit_inv_map` — restriction along
  `e : V' ⟶ V` sends the class of a section of `G(U)` indexed by `(U, h)` to the class of the
  same section indexed by `(U, e ≫ h)`.

## Implementation notes

The étale categories are Stacks' small étale categories `AlgebraicGeometry.SmallEtale` of a big
étale site; their objects live in `Type (u + 1)` and their morphisms in `Type u`, so the values
are taken in a category with colimits of that size (for instance `Type (u + 1)` or
`AddCommGrpCat.{u + 1}`). The inverse image presheaf is Mathlib's `CategoryTheory.Functor.lan`,
so the adjunction with restriction along base change and its universal property are Mathlib's.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 04I3](https://stacks.math.columbia.edu/tag/04I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- **Pairs `(U, h)` of `J_V`.** A morphism `V ⟶ T ×_S U` of étale `T`-schemes is the same as a
morphism `h : V ⟶ U` with `h ≫ π_U = π_V ≫ f`: the universal property of the fibre product,
i.e. the adjunction `Over.map f ⊣ Over.pullback f`. -/
@[weil "def_fk102_inverse_image_presheaf"]
def smallEtaleHomBaseChangeEquiv (V : SmallEtale B T.obj T.property)
    (U : SmallEtale B S.obj S.property) :
    (V ⟶ (smallEtaleBaseChange B f).obj U) ≃
      {h : V.obj.left ⟶ U.obj.left // h ≫ U.obj.hom = V.obj.hom ≫ f} :=
  ({ toFun := fun k => k.hom
     invFun := fun m => ObjectProperty.homMk m
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
      (V ⟶ (smallEtaleBaseChange B f).obj U) ≃ (V.obj ⟶ (Over.pullback f).obj U.obj)).trans
    ((((Over.mapPullbackAdj f).homEquiv V.obj U.obj).symm).trans
      { toFun := fun m => ⟨m.left, Over.w m⟩
        invFun := fun h => Over.homMk h.1 h.2
        left_inv := fun _ => Over.OverMorphism.ext rfl
        right_inv := fun _ => rfl })

lemma smallEtaleHomBaseChangeEquiv_apply_coe (V : SmallEtale B T.obj T.property)
    (U : SmallEtale B S.obj S.property) (g : V ⟶ (smallEtaleBaseChange B f).obj U) :
    (smallEtaleHomBaseChangeEquiv B f V U g).1 =
      (((Over.mapPullbackAdj f).homEquiv V.obj U.obj).symm
        (g.hom : V.obj ⟶ (Over.pullback f).obj U.obj)).left :=
  rfl

/-- Composing with a morphism `e : U ⟶ U'` of étale `S`-schemes corresponds, under
`smallEtaleHomBaseChangeEquiv`, to composing the morphism of schemes `h : V ⟶ U` with `e`. -/
lemma smallEtaleHomBaseChangeEquiv_comp {V : SmallEtale B T.obj T.property}
    {U U' : SmallEtale B S.obj S.property} (g : V ⟶ (smallEtaleBaseChange B f).obj U)
    (e : U ⟶ U') :
    (smallEtaleHomBaseChangeEquiv B f V U' (g ≫ (smallEtaleBaseChange B f).map e)).1 =
      (smallEtaleHomBaseChangeEquiv B f V U g).1 ≫ e.hom.left := by
  let g' : V.obj ⟶ (Over.pullback f).obj U.obj := g.hom
  let e' : U.obj ⟶ U'.obj := e.hom
  have h := congrArg Over.Hom.left
    ((Over.mapPullbackAdj f).homEquiv_naturality_right_symm g' e')
  rw [smallEtaleHomBaseChangeEquiv_apply_coe, smallEtaleHomBaseChangeEquiv_apply_coe]
  exact h

/-- Precomposing with a morphism `k : V' ⟶ V` of étale `T`-schemes corresponds, under
`smallEtaleHomBaseChangeEquiv`, to precomposing the morphism of schemes `h : V ⟶ U` with `k`. -/
lemma smallEtaleHomBaseChangeEquiv_comp_left {V V' : SmallEtale B T.obj T.property}
    {U : SmallEtale B S.obj S.property} (k : V' ⟶ V) (g : V ⟶ (smallEtaleBaseChange B f).obj U) :
    (smallEtaleHomBaseChangeEquiv B f V' U (k ≫ g)).1 =
      k.hom.left ≫ (smallEtaleHomBaseChangeEquiv B f V U g).1 := by
  let g' : V.obj ⟶ (Over.pullback f).obj U.obj := g.hom
  let k' : V'.obj ⟶ V.obj := k.hom
  have h := congrArg Over.Hom.left
    ((Over.mapPullbackAdj f).homEquiv_naturality_left_symm k' g')
  rw [smallEtaleHomBaseChangeEquiv_apply_coe, smallEtaleHomBaseChangeEquiv_apply_coe]
  exact h

/-- **The index category `J_V`.** Its objects are the pairs `(U, g)` of an étale `S`-scheme `U`
and a morphism `g : V ⟶ T ×_S U` of étale `T`-schemes — equivalently, by
`smallEtaleHomBaseChangeEquiv`, a morphism `h : V ⟶ U` with `h ≫ π_U = π_V ≫ f`; its morphisms
`(U, h) ⟶ (U', h')` are the morphisms `e : U ⟶ U'` with `h ≫ e = h'`
(`SmallEtaleInverseImageIndex.schemeHom_comp_right`). -/
@[weil "def_fk102_inverse_image_presheaf"]
abbrev SmallEtaleInverseImageIndex (V : SmallEtale B T.obj T.property) :=
  StructuredArrow V (smallEtaleBaseChange B f)

namespace SmallEtaleInverseImageIndex

variable {B f}

/-- The underlying morphism of schemes `h : V ⟶ U` of an object `(U, h)` of `J_V`. -/
abbrev schemeHom {V : SmallEtale B T.obj T.property} (P : SmallEtaleInverseImageIndex B f V) :
    V.obj.left ⟶ P.right.obj.left :=
  (smallEtaleHomBaseChangeEquiv B f V P.right P.hom).1

lemma schemeHom_comp {V : SmallEtale B T.obj T.property} (P : SmallEtaleInverseImageIndex B f V) :
    P.schemeHom ≫ P.right.obj.hom = V.obj.hom ≫ f :=
  (smallEtaleHomBaseChangeEquiv B f V P.right P.hom).2

/-- A morphism `e : (U, h) ⟶ (U', h')` of `J_V` satisfies `h ≫ e = h'`. -/
lemma schemeHom_comp_right {V : SmallEtale B T.obj T.property}
    {P P' : SmallEtaleInverseImageIndex B f V} (e : P ⟶ P') :
    P.schemeHom ≫ e.right.hom.left = P'.schemeHom := by
  rw [schemeHom, schemeHom, ← smallEtaleHomBaseChangeEquiv_comp, StructuredArrow.w e]

/-- A morphism `e : U ⟶ U'` of étale `S`-schemes with `h ≫ e = h'` is a morphism
`(U, h) ⟶ (U', h')` of `J_V`. -/
def homMk {V : SmallEtale B T.obj T.property} {P P' : SmallEtaleInverseImageIndex B f V}
    (e : P.right ⟶ P'.right) (he : P.schemeHom ≫ e.hom.left = P'.schemeHom) : P ⟶ P' :=
  StructuredArrow.homMk e ((smallEtaleHomBaseChangeEquiv B f V P'.right).injective
    (Subtype.ext (by rw [smallEtaleHomBaseChangeEquiv_comp]; exact he)))

@[simp]
lemma homMk_right {V : SmallEtale B T.obj T.property} {P P' : SmallEtaleInverseImageIndex B f V}
    (e : P.right ⟶ P'.right) (he : P.schemeHom ≫ e.hom.left = P'.schemeHom) :
    (homMk e he).right = e :=
  rfl

variable (B f)

/-- The functor `J_V ⥤ J_V'` induced by a morphism `k : V' ⟶ V`: precomposition with `k`. -/
abbrev map {V V' : SmallEtale B T.obj T.property} (k : V' ⟶ V) :
    SmallEtaleInverseImageIndex B f V ⥤ SmallEtaleInverseImageIndex B f V' :=
  StructuredArrow.map k

/-- The functor `J_V ⥤ J_V'` sends `(U, h)` to `(U, k ≫ h)`. -/
lemma schemeHom_map {V V' : SmallEtale B T.obj T.property} (k : V' ⟶ V)
    (P : SmallEtaleInverseImageIndex B f V) :
    ((map B f k).obj P).schemeHom = k.hom.left ≫ P.schemeHom :=
  smallEtaleHomBaseChangeEquiv_comp_left B f k P.hom

end SmallEtaleInverseImageIndex

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]

/-- **The inverse image presheaf `f⁻¹_pre`.** The functor sending a presheaf `G` on the small
étale site of `S` with values in `A` to the presheaf on the small étale site of `T` whose
sections over `V` are `colim_{(U, h) ∈ J_Vᵒᵖ} G(U)`
(`smallEtaleInverseImagePresheafObjIsoColimit`): the left Kan extension of `G` along the opposite
of base change. -/
@[weil "def_fk102_inverse_image_presheaf"]
abbrev smallEtaleInverseImagePresheaf :
    ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ A) ⥤ ((SmallEtale B T.obj T.property)ᵒᵖ ⥤ A) :=
  (smallEtaleBaseChange B f).op.lan

/-- **Sections of the inverse image presheaf.** The sections of `f⁻¹_pre G` over `V` are the
colimit of `G(U)` over `(U, h) ∈ J_Vᵒᵖ`. -/
@[weil "def_fk102_inverse_image_presheaf"]
def smallEtaleInverseImagePresheafObjIsoColimit
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ A) (V : SmallEtale B T.obj T.property) :
    ((smallEtaleInverseImagePresheaf B f A).obj G).obj (op V) ≅
      colimit ((StructuredArrow.proj V (smallEtaleBaseChange B f)).op ⋙ G) :=
  (smallEtaleBaseChange B f).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V).functor
      (CostructuredArrow.proj (smallEtaleBaseChange B f).op (op V) ⋙ G)).symm

/-- The colimit injection of the object `(U, h)` of `J_V`, followed by the identification with
the sections of `f⁻¹_pre G`, is the unit of the Kan extension at `U` followed by restriction
along `h : V ⟶ T ×_S U`. -/
@[reassoc]
lemma ι_smallEtaleInverseImagePresheafObjIsoColimit_inv
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ A) (V : SmallEtale B T.obj T.property)
    (P : SmallEtaleInverseImageIndex B f V) :
    colimit.ι ((StructuredArrow.proj V (smallEtaleBaseChange B f)).op ⋙ G) (op P) ≫
        (smallEtaleInverseImagePresheafObjIsoColimit B f A G V).inv =
      ((smallEtaleBaseChange B f).op.lanUnit.app G).app (op P.right) ≫
        ((smallEtaleInverseImagePresheaf B f A).obj G).map P.hom.op := by
  have h₁ := Functor.Final.ι_colimitIso_hom
    (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V).functor
    (CostructuredArrow.proj (smallEtaleBaseChange B f).op (op V) ⋙ G) (op P)
  have h₂ := (smallEtaleBaseChange B f).op.ι_leftKanExtensionObjIsoColimit_inv G (op V)
    ((structuredArrowOpEquivalence (smallEtaleBaseChange B f) V).functor.obj (op P))
  change colimit.ι ((structuredArrowOpEquivalence (smallEtaleBaseChange B f) V).functor ⋙
      CostructuredArrow.proj (smallEtaleBaseChange B f).op (op V) ⋙ G) (op P) ≫
      (Functor.Final.colimitIso (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V).functor
        (CostructuredArrow.proj (smallEtaleBaseChange B f).op (op V) ⋙ G)).hom ≫
      ((smallEtaleBaseChange B f).op.leftKanExtensionObjIsoColimit G (op V)).inv = _
  rw [reassoc_of% h₁, h₂]
  rfl

/-- **Restriction on the inverse image presheaf.** A morphism `k : V' ⟶ V` acts on
`f⁻¹_pre G` through the functor `J_V ⥤ J_V'` given by precomposition with `k`: the class of a
section of `G(U)` indexed by `(U, h)` is sent to the class of the same section indexed by
`(U, k ≫ h)`. -/
@[reassoc, weil "def_fk102_inverse_image_presheaf"]
lemma ι_smallEtaleInverseImagePresheafObjIsoColimit_inv_map
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ A) {V V' : SmallEtale B T.obj T.property}
    (k : V' ⟶ V) (P : SmallEtaleInverseImageIndex B f V) :
    colimit.ι ((StructuredArrow.proj V (smallEtaleBaseChange B f)).op ⋙ G) (op P) ≫
        (smallEtaleInverseImagePresheafObjIsoColimit B f A G V).inv ≫
        ((smallEtaleInverseImagePresheaf B f A).obj G).map k.op =
      colimit.ι ((StructuredArrow.proj V' (smallEtaleBaseChange B f)).op ⋙ G)
          (op ((SmallEtaleInverseImageIndex.map B f k).obj P)) ≫
        (smallEtaleInverseImagePresheafObjIsoColimit B f A G V').inv := by
  rw [ι_smallEtaleInverseImagePresheafObjIsoColimit_inv_assoc,
    ι_smallEtaleInverseImagePresheafObjIsoColimit_inv, ← Functor.map_comp]
  rfl

end AlgebraicGeometry

end
