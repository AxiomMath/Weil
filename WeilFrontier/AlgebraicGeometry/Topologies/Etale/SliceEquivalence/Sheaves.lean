module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves

/-!
# The inverse image along an étale morphism is restriction

Let `X` be a scheme of a big étale site `B` and `U` an object of the small étale site of `X`, with
étale structure morphism `φ : U ⟶ X`. For a sheaf `F` on the small étale site of `X`, the
*restriction* `F|_U` is the sheaf `(V ⟶ U) ↦ F(V ⟶ U ⟶ X)` on the small étale site of `U`: the
restriction of `F` along the functor composing a structure morphism with `φ`. The inverse image
`φ^* F` is isomorphic to `F|_U`, naturally in `F`; in particular the inverse image along an
étale morphism needs no sheafification.

The proof is the uniqueness of left adjoints: `φ^*` is left adjoint to the direct image along
`φ`, which is restriction along base change `(W ⟶ X) ↦ (U ×_X W ⟶ U)`, and restriction along
composition with `φ` is left adjoint to restriction along base change, because composition with
`φ` is left adjoint to base change along `φ` on the étale objects.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageIsoRestrict` — `φ^* ≅ (·)|_U`, as an isomorphism of
  functors, for sheaves with values in any category `A` with the relevant colimits and
  sheafification (sets and abelian groups among them).
* `AlgebraicGeometry.smallEtaleInverseImageObjIsoRestrict` — the isomorphism `φ^* F ≅ F|_U` for
  one sheaf `F`, with its naturality
  `AlgebraicGeometry.smallEtaleInverseImageObjIsoRestrict_hom_naturality`.
* `AlgebraicGeometry.smallEtaleRestrictToObj_obj_obj` — `F|_U (V ⟶ U) = F(V ⟶ U ⟶ X)`.
* `AlgebraicGeometry.restrict_smallEtaleRestrictToObj_val` — on noetherian separated objects,
  `F|_U` is the restriction `AlgebraicGeometry.EtalePresheaf.restrict` of presheaves on `Et(X)`.

## Implementation notes

The statement is made on the small étale sites `SmallEtale` of a big étale site. The restriction
`F|_U` is the pushforward of sheaves along the continuous functor
`AlgebraicGeometry.smallEtalePostcompose` (Stacks, Tag 03S3), and the isomorphism is
`AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose`. On the étale category `Et(X)` of
noetherian separated étale `X`-schemes, the restriction of presheaves
`AlgebraicGeometry.EtalePresheaf.restrict` is the same functor read on the noetherian separated
objects, which is `AlgebraicGeometry.restrict_smallEtaleRestrictToObj_val`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
variable (A : Type w) [Category.{v} A]

/-- **Restriction of a sheaf to an étale `X`-scheme.** For an object `U` of the small étale site
of `X`, the functor sending a sheaf `F` on the small étale site of `X` to the sheaf
`F|_U : (V ⟶ U) ↦ F(V ⟶ U ⟶ X)` on the small étale site of `U`. -/
abbrev smallEtaleRestrictToObj :
    Sheaf (SmallEtale.topology B X hX) A ⥤
      Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A :=
  (smallEtalePostcompose B X hX U).sheafPushforwardContinuous A
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) (SmallEtale.topology B X hX)

/-- The sections of `F|_U` over `V ⟶ U` are the sections of `F` over `V ⟶ U ⟶ X`. -/
lemma smallEtaleRestrictToObj_obj_obj (F : Sheaf (SmallEtale.topology B X hX) A)
    (V : (SmallEtale B U.obj.left.1 U.obj.left.property)ᵒᵖ) :
    ((smallEtaleRestrictToObj B X hX U A).obj F).obj.obj V =
      F.obj.obj (op ((smallEtalePostcompose B X hX U).obj V.unop)) :=
  rfl

/-- The restriction maps of `F|_U` are those of `F`. -/
lemma smallEtaleRestrictToObj_obj_map (F : Sheaf (SmallEtale.topology B X hX) A)
    {V W : (SmallEtale B U.obj.left.1 U.obj.left.property)ᵒᵖ} (g : V ⟶ W) :
    ((smallEtaleRestrictToObj B X hX U A).obj F).obj.map g =
      F.obj.map ((smallEtalePostcompose B X hX U).map g.unop).op :=
  rfl

variable [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A]

/-- **The inverse image along an étale morphism is restriction.** For an object `U` of the small
étale site of `X`, with étale structure morphism `φ : U ⟶ X`, the inverse image `φ^*` of sheaves
is isomorphic to the restriction `F ↦ F|_U`, naturally in `F`. -/
@[weil "lem_fk104_inverse_image_etale_is_restriction"]
def smallEtaleInverseImageIsoRestrict :
    smallEtaleInverseImage B (S := B.obj X hX) U.obj.hom A ≅
      smallEtaleRestrictToObj B X hX U A :=
  smallEtaleSheafPullbackIsoPostcompose B X hX U A

/-- **The isomorphism `φ^* F ≅ F|_U`** for a sheaf `F` on the small étale site of `X`. -/
@[weil "lem_fk104_inverse_image_etale_is_restriction"]
def smallEtaleInverseImageObjIsoRestrict (F : Sheaf (SmallEtale.topology B X hX) A) :
    (smallEtaleInverseImage B (S := B.obj X hX) U.obj.hom A).obj F ≅
      (smallEtaleRestrictToObj B X hX U A).obj F :=
  (smallEtaleInverseImageIsoRestrict B X hX U A).app F

/-- The isomorphism `φ^* F ≅ F|_U` is natural in `F`. -/
@[reassoc]
lemma smallEtaleInverseImageObjIsoRestrict_hom_naturality
    {F G : Sheaf (SmallEtale.topology B X hX) A} (α : F ⟶ G) :
    (smallEtaleInverseImage B (S := B.obj X hX) U.obj.hom A).map α ≫
        (smallEtaleInverseImageObjIsoRestrict B X hX U A G).hom =
      (smallEtaleInverseImageObjIsoRestrict B X hX U A F).hom ≫
        (smallEtaleRestrictToObj B X hX U A).map α :=
  (smallEtaleInverseImageIsoRestrict B X hX U A).hom.naturality α

end AlgebraicGeometry

namespace AlgebraicGeometry

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {A : Type w} [Category.{v} A]

/-- **The restriction on `Et(X)`.** For `U` in the étale category `Et(X)` of noetherian separated
étale `X`-schemes and a sheaf `F` on the small étale site of `X`, the presheaf on `Et(U)`
underlying `F|_U` is the restriction `EtalePresheaf.restrict` to `U` of the presheaf on `Et(X)`
underlying `F`. -/
lemma restrict_smallEtaleRestrictToObj_val (U : SmallNoetherianSeparatedEtale B X hX)
    (F : Sheaf (SmallEtale.topology B X hX) A) :
    (inclusion _ _ _).op ⋙ ((smallEtaleRestrictToObj B X hX U.obj A).obj F).obj =
      EtalePresheaf.restrict ((inclusion B X hX).op ⋙ F.obj) U :=
  rfl

end AlgebraicGeometry

end
