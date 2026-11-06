module

public import Weil.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk
public import Weil.Attr

/-!
# Restriction to an étale scheme is the inverse image, and its stalks

Let `X` be a scheme of a big étale site `B`, let `φ : U ⟶ X` be an object of the small étale
site of `X`, and let `F` be a sheaf on the small étale site of `X`, with values in a category `A`
such as sets or abelian groups. The restriction `F|_U : V ↦ F(V → U → X)` is a sheaf on the
small étale site of `U`, and it is canonically isomorphic to the inverse image `φ^* F`, naturally
in `F`.

Consequently, for every geometric point `u` of `U`, the stalk of `F|_U` at `u` is canonically
isomorphic to the stalk of `F` at the image geometric point `φ ∘ u`, naturally in `F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafRestrictionIsoInverseImage` — the natural isomorphism
  `F|_U ≅ φ^* F`.
* `AlgebraicGeometry.SmallEtale.sheafRestrictionSheafFiberIso` — the natural isomorphism
  `(F|_U)_u ≅ F_{φ ∘ u}`.

## Main results

* `AlgebraicGeometry.SmallEtale.sheafRestrictionIsoInverseImage_hom_naturality` — the first
  isomorphism is natural in `F`.

## Implementation notes

The restriction is `AlgebraicGeometry.SmallEtale.sheafRestriction`, the direct image along
post-composition with `φ`. It is identified with the inverse image as two left adjoints of the
direct image along base change by `φ`; the initial object `(V, id_V)` of the index category of
the colimit defining the inverse image presheaf is the unit of the adjunction between
post-composition and base change. Stalks at a geometric point are the fibres of the point of the
site `AlgebraicGeometry.geometricPointSitePoint`, and the stalk isomorphism is the composite of
the first isomorphism with the stalk isomorphism of the inverse image.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
* [Stacks Project, Tag 03PM](https://stacks.math.columbia.edu/tag/03PM)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B U.obj.left.obj U.obj.left.property) A]

/-- **The restriction is the inverse image.** For an object `φ : U ⟶ X` of the small étale site
of `X`, the restriction `F|_U` of a sheaf `F` on the small étale site of `X` is isomorphic to the
inverse image `φ^* F`, naturally in `F`. -/
@[weil "lem_fk112_restriction_is_inverse_image"]
def sheafRestrictionIsoInverseImage :
    sheafRestriction B X hX U A ≅ smallEtaleInverseImage B U.obj.hom A :=
  (inverseImageIsoSheafRestriction B X hX U A).symm

/-- The isomorphism `F|_U ≅ φ^* F` is natural in `F`. -/
@[reassoc]
lemma sheafRestrictionIsoInverseImage_hom_naturality
    {F F' : Sheaf (SmallEtale.topology B X hX) A} (f : F ⟶ F') :
    (sheafRestriction B X hX U A).map f ≫
        (sheafRestrictionIsoInverseImage B X hX U A).hom.app F' =
      (sheafRestrictionIsoInverseImage B X hX U A).hom.app F ≫
        (smallEtaleInverseImage B U.obj.hom A).map f :=
  (sheafRestrictionIsoInverseImage B X hX U A).hom.naturality f

/-- Stalks on the small étale sites are colimits indexed by categories of size `u`. -/
lemma hasColimitsOfSize_sheafRestrictionSheafFiber :
    HasColimitsOfSize.{u, u} A :=
  hasColimitsOfSizeShrink.{u, u, u, u + 1} A

attribute [local instance] hasColimitsOfSize_sheafRestrictionSheafFiber

variable [HasProducts.{u} A]

/-- **Stalks of the restriction.** For an object `φ : U ⟶ X` of the small étale site of `X` and
a geometric point `u` of `U`, the stalk at `u` of the restriction `F|_U` of a sheaf `F` on the
small étale site of `X` is isomorphic to the stalk of `F` at the geometric point `φ ∘ u`,
naturally in `F`. -/
@[weil "lem_fk112_restriction_is_inverse_image"]
def sheafRestrictionSheafFiberIso (u : GeometricPoint U.obj.left.obj) :
    sheafRestriction B X hX U A ⋙
        (geometricPointSitePoint B U.obj.left.obj U.obj.left.property u).sheafFiber ≅
      (geometricPointSitePoint B X hX (u.map (B.inclusion.map U.obj.hom))).sheafFiber :=
  Functor.isoWhiskerRight (sheafRestrictionIsoInverseImage B X hX U A) _ ≪≫
    (smallEtaleInverseImageSheafFiberIso B U.obj.hom u A).symm

end AlgebraicGeometry.SmallEtale

end
