module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# The inverse image along a composite

Let `f : Z ⟶ Y` and `g : Y ⟶ X` be morphisms of schemes of a big étale site `B`, and let `F` be
a sheaf on the small étale site of `X` with values in a category `A` (sheaves of sets, of
abelian groups, of modules, …). Then there is an isomorphism
`(g ∘ f)^* F ≅ f^* (g^* F)` of sheaves on the small étale site of `Z`, natural in `F`.

Both sides are left adjoint to the same functor: the direct image along `g ∘ f` is the composite
of the direct images along `f` and `g`. The isomorphism is then the one given by uniqueness of
left adjoints, which is the Yoneda argument of the source.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageCompIso` — the natural isomorphism
  `(g ∘ f)^* ≅ g^* ⋙ f^*` of functors.
* `AlgebraicGeometry.smallEtaleInverseImageCompObjIso` — its component
  `(g ∘ f)^* F ≅ f^* (g^* F)` at a sheaf `F`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageCompObjIso_hom_naturality` — the component is
  natural in `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : Z ⟶ Y) (g : Y ⟶ X)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B Y.obj Y.property) A]
  [HasWeakSheafify (SmallEtale.topology B Z.obj Z.property) A]

/-- **Inverse image along a composite.** The inverse image along `f ≫ g` (that is, `g ∘ f`) is
the composite of the inverse image along `g` followed by the inverse image along `f`. -/
@[weil "lem_fk104_inverse_image_comp"]
def smallEtaleInverseImageCompIso :
    smallEtaleInverseImage B (f ≫ g) A ≅
      smallEtaleInverseImage B g A ⋙ smallEtaleInverseImage B f A :=
  (smallEtaleSheafPullbackCompIso B Z Y X f g A).symm

/-- **`(g ∘ f)^* F ≅ f^* (g^* F)`.** The component of `smallEtaleInverseImageCompIso` at a sheaf
`F` on the small étale site of `X`. -/
def smallEtaleInverseImageCompObjIso (F : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    (smallEtaleInverseImage B (f ≫ g) A).obj F ≅
      (smallEtaleInverseImage B f A).obj ((smallEtaleInverseImage B g A).obj F) :=
  (smallEtaleInverseImageCompIso B f g A).app F

/-- The isomorphism `(g ∘ f)^* F ≅ f^* (g^* F)` is natural in `F`. -/
@[reassoc]
lemma smallEtaleInverseImageCompObjIso_hom_naturality
    {F F' : Sheaf (SmallEtale.topology B X.obj X.property) A} (φ : F ⟶ F') :
    (smallEtaleInverseImage B (f ≫ g) A).map φ ≫
        (smallEtaleInverseImageCompObjIso B f g A F').hom =
      (smallEtaleInverseImageCompObjIso B f g A F).hom ≫
        (smallEtaleInverseImage B f A).map ((smallEtaleInverseImage B g A).map φ) :=
  (smallEtaleInverseImageCompIso B f g A).hom.naturality φ

end AlgebraicGeometry

end
