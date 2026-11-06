module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage

/-!
# The inverse image of a constructible sheaf is constructible

Let `f : X' ⟶ X` be a morphism of schemes and `F` a constructible sheaf of sets or of abelian
groups on the small étale site of `X`. Then the inverse image `f^* F` is constructible on the
small étale site of `X'`.

## Main results

* `AlgebraicGeometry.IsConstructibleSetSheaf.smallEtaleInverseImage`: the case of sheaves of sets.
* `AlgebraicGeometry.IsConstructibleAbelianSheaf.smallEtaleInverseImage`: the case of sheaves of
  abelian groups.

These are the dot-notation forms of
`AlgebraicGeometry.isConstructibleSetSheaf_smallEtaleInverseImage`
and `AlgebraicGeometry.isConstructibleAbelianSheaf_smallEtaleInverseImage`.

## Implementation notes

Constructibility is that of Stacks, Tag 03RW (`AlgebraicGeometry.IsConstructibleSetSheaf`,
`AlgebraicGeometry.IsConstructibleAbelianSheaf`), which on a scheme with Noetherian underlying
space is the definition of [FK]
(`AlgebraicGeometry.isConstructibleSetSheaf_iff_exists_immersion_cover`).
With this definition the statement holds for an arbitrary morphism of schemes, without the
Noetherian and separatedness assumptions of [FK]; it is Stacks, Tag 095G. The proof there pulls
back a constructible stratification of the target, rather than presenting `F` as a quotient of a
representable sheaf.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X' X : B.Scheme} (f : X' ⟶ X)

/-- **The inverse image of a constructible sheaf of sets is constructible.** For a morphism
`f : X' ⟶ X` of schemes and a constructible sheaf of sets `F` on the small étale site of `X`,
the inverse image `f^* F` is constructible. -/
@[weil "lem_fk105_inverse_image_constructible"]
theorem IsConstructibleSetSheaf.smallEtaleInverseImage
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleSetSheaf B X' ((AlgebraicGeometry.smallEtaleInverseImage B f
      (Type (u + 1))).obj F) :=
  isConstructibleSetSheaf_smallEtaleInverseImage B f F hF

/-- **The inverse image of a constructible sheaf of abelian groups is constructible.** For a
morphism `f : X' ⟶ X` of schemes and a constructible sheaf of abelian groups `F` on the small
étale site of `X`, the inverse image `f^* F` is constructible. -/
@[weil "lem_fk105_inverse_image_constructible"]
theorem IsConstructibleAbelianSheaf.smallEtaleInverseImage
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleAbelianSheaf B X'
      ((AlgebraicGeometry.smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj F) :=
  isConstructibleAbelianSheaf_smallEtaleInverseImage B f F hF

end AlgebraicGeometry

end
