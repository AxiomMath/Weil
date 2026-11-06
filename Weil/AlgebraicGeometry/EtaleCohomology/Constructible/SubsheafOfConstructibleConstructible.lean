module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets

/-!
# Subsheaves of constructible sheaves of sets

Let `X` be a Noetherian scheme. Every subsheaf `G ⊆ F` of a constructible sheaf of sets `F` on
the small étale site of `X` is constructible.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_of_mono_of_isNoetherian`: a subsheaf (the source of
  a monomorphism) of a constructible sheaf of sets on the small étale site of a Noetherian scheme
  is constructible.

## Implementation notes

This is Stacks 09BH (1), `AlgebraicGeometry.isConstructibleSetSheaf_of_mono`, with its two inputs
(Stacks 03S8 and the surjection half of Stacks 09Y9) supplied by
`AlgebraicGeometry.representableIsConstructibleSetSheaf` and
`AlgebraicGeometry.hasFiniteRepresentableCover`. A subsheaf is expressed as a monomorphism of
sheaves `G ⟶ F`; in the category of sheaves of sets these are exactly the sectionwise injective
morphisms. The source's argument (pull back an epimorphism `h_Y ⟶ F` to `G`, observe that the
pullback is a subsheaf of `h_Y`, hence representable) is replaced by the library's, which covers
`F` by a finite coproduct of representables.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl1988]
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Subsheaves of constructible sheaves are constructible.** On a Noetherian scheme `X`, if
`i : G ⟶ F` is a monomorphism of sheaves of sets on the small étale site of `X` and `F` is
constructible, then `G` is constructible. -/
@[weil "lem_fk104_subsheaf_of_constructible_constructible"]
theorem isConstructibleSetSheaf_of_mono_of_isNoetherian (B : BigEtaleSite.{u}) (X : B.Scheme)
    [IsNoetherian X.obj]
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleSetSheaf B X G :=
  isConstructibleSetSheaf_of_mono B X (representableIsConstructibleSetSheaf B X)
    (hasFiniteRepresentableCover B X) i hF

end AlgebraicGeometry
