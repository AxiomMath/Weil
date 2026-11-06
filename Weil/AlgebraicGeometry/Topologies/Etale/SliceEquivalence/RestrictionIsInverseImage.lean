module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian

/-!
# Restriction to an object of `Et(Y)` is the inverse image

Let `Y` be a scheme of a big étale site `B`, let `V = (V, j)` be an object of the étale category
`Et(Y)` of noetherian separated étale `Y`-schemes, and let `F` be a sheaf on the small étale site
of `Y`, for instance an abelian sheaf. Then the inverse image `j^* F` along the structure
morphism `j : V ⟶ Y` is isomorphic to the restriction `F|_V`, naturally in `F`: on `Et(V)` its
sections over `w : W ⟶ V` are `F(W, j ∘ w)`, with the restriction maps of `F`.

The proof is the uniqueness of left adjoints: both `j^*` and `F ↦ F|_V` are left adjoint to the
direct image `j_*`, whose sections over `W ⟶ Y` are those of the sheaf over `W ×_Y V`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.inverseImageIsoRestrict` — the natural
  isomorphism `(j^* F)|_{Et(V)} ≅ (F|_{Et(Y)})|_V` of presheaves on `Et(V)`, for sheaves `F`
  on the small étale site of `Y` with values in any category with the relevant colimits and
  sheafification.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.inverseImageObjIsoRestrict` — the same
  isomorphism for one sheaf `F`, with its naturality
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.inverseImageObjIsoRestrict_hom_naturality`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.inverseImageAbIsoRestrict` — the case of
  abelian sheaves.

## Implementation notes

Sheaves are taken on the small étale site `SmallEtale` of the big étale site `B`, and the
restriction `F|_V` is read on the noetherian separated objects as
`AlgebraicGeometry.EtalePresheaf.restrict`; the isomorphism is the restriction to `Et(V)` of
`AlgebraicGeometry.smallEtaleInverseImageIsoRestrict`, the isomorphism of sheaves on the whole
small étale site of `V`. No noetherian or separatedness hypothesis on `Y` is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {Y : Scheme.{u}} {hY : B.Contains Y}
  (V : SmallNoetherianSeparatedEtale B Y hY) (A : Type w) [Category.{v} A]
  [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B V.obj.obj.left.1 V.obj.obj.left.property) A]

/-- **The restriction to `V ∈ Et(Y)` is the inverse image.** For `V = (V, j)` an object of
`Et(Y)`, the presheaf on `Et(V)` underlying the inverse image `j^* F` of a sheaf `F` on the small
étale site of `Y` is isomorphic to the restriction `F|_V` of the presheaf on `Et(Y)` underlying
`F`, naturally in `F`. -/
@[weil "lem_fk104_restriction_is_inverse_image"]
def inverseImageIsoRestrict :
    smallEtaleInverseImage B (S := B.obj Y hY) V.obj.obj.hom A ⋙
        sheafToPresheaf _ A ⋙ (Functor.whiskeringLeft _ _ A).obj (inclusion _ _ _).op ≅
      sheafToPresheaf (SmallEtale.topology B Y hY) A ⋙
        (Functor.whiskeringLeft _ _ A).obj (inclusion B Y hY).op ⋙
          EtalePresheaf.restrictFunctor A V :=
  Functor.isoWhiskerRight (smallEtaleInverseImageIsoRestrict B Y hY V.obj A)
    (sheafToPresheaf _ A ⋙ (Functor.whiskeringLeft _ _ A).obj (inclusion _ _ _).op)

/-- **The isomorphism `j^* F ≅ F|_V`** on `Et(V)`, for one sheaf `F` on the small étale site of
`Y`. -/
@[weil "lem_fk104_restriction_is_inverse_image"]
def inverseImageObjIsoRestrict (F : Sheaf (SmallEtale.topology B Y hY) A) :
    (inclusion _ _ _).op ⋙
        ((smallEtaleInverseImage B (S := B.obj Y hY) V.obj.obj.hom A).obj F).obj ≅
      EtalePresheaf.restrict ((inclusion B Y hY).op ⋙ F.obj) V :=
  (inverseImageIsoRestrict V A).app F

/-- The isomorphism `j^* F ≅ F|_V` on `Et(V)` is natural in `F`. -/
@[reassoc]
lemma inverseImageObjIsoRestrict_hom_naturality
    {F G : Sheaf (SmallEtale.topology B Y hY) A} (α : F ⟶ G) :
    Functor.whiskerLeft (inclusion _ _ _).op
        ((smallEtaleInverseImage B (S := B.obj Y hY) V.obj.obj.hom A).map α).hom ≫
        (inverseImageObjIsoRestrict V A G).hom =
      (inverseImageObjIsoRestrict V A F).hom ≫
        (EtalePresheaf.restrictFunctor A V).map
          (Functor.whiskerLeft (inclusion B Y hY).op α.hom) :=
  (inverseImageIsoRestrict V A).hom.naturality α

/-- The component of `j^* F ≅ F|_V` at `W ∈ Et(V)` is that of the isomorphism of sheaves on the
whole small étale site of `V`. -/
lemma inverseImageObjIsoRestrict_hom_app (F : Sheaf (SmallEtale.topology B Y hY) A)
    (W : (Over' V)ᵒᵖ) :
    (inverseImageObjIsoRestrict V A F).hom.app W =
      (smallEtaleInverseImageObjIsoRestrict B Y hY V.obj A F).hom.hom.app
        (op ((inclusion _ _ _).obj W.unop)) :=
  rfl

/-- **Abelian sheaves.** For `V = (V, j) ∈ Et(Y)` and an abelian sheaf `F` on the small étale site
of `Y`, the inverse image `j^* F` restricted to `Et(V)` is isomorphic to `F|_V`, naturally in
`F`. -/
@[weil "lem_fk104_restriction_is_inverse_image"]
def inverseImageAbIsoRestrict :
    smallEtaleInverseImage B (S := B.obj Y hY) V.obj.obj.hom AddCommGrpCat.{u + 1} ⋙
        sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (inclusion _ _ _).op ≅
      sheafToPresheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ _).obj (inclusion B Y hY).op ⋙
          EtalePresheaf.restrictFunctor _ V :=
  inverseImageIsoRestrict V AddCommGrpCat.{u + 1}

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
