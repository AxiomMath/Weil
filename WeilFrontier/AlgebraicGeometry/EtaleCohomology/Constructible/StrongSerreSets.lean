module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets

/-!
# Products of constructible sheaves of sets

The product `𝒜 × ℬ` of two constructible sheaves of sets on the small étale site of a scheme `X`
is constructible.

## Main results

* `AlgebraicGeometry.IsConstructibleSetSheaf.prod`: the binary product of two constructible
  sheaves of sets is constructible.

## Implementation notes

[FK] state the result for a Noetherian separated scheme and prove it by presenting each factor
as a quotient of a representable sheaf `Ỹ` with `Y` étale over `X`, the product then being a
quotient of the sheaf represented by `Y ×_X Y'`. With the definition of constructibility used
here (Stacks, Tag 03RW, which agrees with that of [FK] on a Noetherian scheme, see
`AlgebraicGeometry.isConstructibleSetSheaf_iff_exists_immersion_cover`) the result holds with
no hypothesis on `X`: it is the case of a binary product of the closure of constructible sheaves
under finite limits, `AlgebraicGeometry.isConstructibleSetSheaf_prod`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Products of constructible sheaves.** The product of two constructible sheaves of sets on
the small étale site of a scheme `X` is constructible. -/
@[weil "lem_fk104_product_of_constructible_constructible"]
theorem IsConstructibleSetSheaf.prod {B : BigEtaleSite.{u}} {X : B.Scheme}
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : IsConstructibleSetSheaf B X F) (hG : IsConstructibleSetSheaf B X G) :
    IsConstructibleSetSheaf B X (F ⨯ G) :=
  isConstructibleSetSheaf_prod B X hF hG

end AlgebraicGeometry
