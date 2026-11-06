module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage

/-!
# Inverse image of a constructible étale sheaf

Let `g : X' ⟶ X` be a morphism of schemes and `F` a constructible sheaf of sets, or of abelian
groups, on the small étale site of `X`. Then the inverse image `g^* F` is constructible on the
small étale site of `X'`.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_smallEtaleInverseImage`: the inverse image of a
  constructible sheaf of sets is constructible.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_smallEtaleInverseImage`: the inverse image of a
  constructible sheaf of abelian groups is constructible.

## Implementation notes

Both statements are instances of `AlgebraicGeometry.isConstructibleFiniteSheaf_pullback`
(Stacks, Tag 095G), which holds for sheaves with values in any concrete category and for an
arbitrary morphism of schemes, with no Noetherian hypothesis. Constructibility is that of
Stacks, Tag 03RW, which agrees with the definition by a finite cover by locally closed
subschemes on a scheme with Noetherian underlying space
(`AlgebraicGeometry.isConstructibleSetSheaf_iff_exists_immersion_cover`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} (g : X' ⟶ X)

/-- **The inverse image of a constructible sheaf of sets is constructible.** For any morphism of
schemes `g : X' ⟶ X` and any constructible sheaf of sets `F` on the small étale site of `X`, the
inverse image `g^* F` is constructible. -/
@[weil "lem_fk104_inverse_image_constructible"]
theorem isConstructibleSetSheaf_smallEtaleInverseImage
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleSetSheaf B X' ((smallEtaleInverseImage B g (Type (u + 1))).obj F) :=
  isConstructibleFiniteSheaf_pullback B g F hF

/-- **The inverse image of a constructible sheaf of abelian groups is constructible.** For any
morphism of schemes `g : X' ⟶ X` and any constructible sheaf of abelian groups `F` on the small
étale site of `X`, the inverse image `g^* F` is constructible. -/
@[weil "lem_fk104_inverse_image_constructible"]
theorem isConstructibleAbelianSheaf_smallEtaleInverseImage
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleAbelianSheaf B X' ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F) :=
  isConstructibleFiniteSheaf_pullback B g F hF

end AlgebraicGeometry

end
