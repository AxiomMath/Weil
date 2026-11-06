module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentationPushforwardModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentationPushforward

/-!
# Finite direct images of constructible sheaves

Let `f : X ⟶ Y` be a finite morphism of schemes with `Y` locally Noetherian. If `ℱ` is a
constructible sheaf of sets (resp. of abelian groups) on the small étale site of `X`, then the
direct image `f_* ℱ` is a constructible sheaf of sets (resp. of abelian groups) on the small
étale site of `Y`.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_smallPushforward_of_isFinite`: the case of sheaves
  of sets.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_smallPushforward_of_isFinite` (in
  `Weil.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentationPushforwardModules`):
  the case of sheaves of abelian groups.

## Implementation notes

Both statements are Stacks, Tag 095R, which holds for a finite morphism of finite presentation;
over a locally Noetherian base a finite morphism is of finite presentation. The Noetherian
hypothesis is the standing convention of [FreitagKiehl], I.2; without a finiteness condition of
this kind the statement fails (a closed immersion `i` that is not of finite presentation gives a
non-constructible `i_*` of a constant sheaf). [FreitagKiehl] argue instead by a reduction to the
generic case along irreducible components; Stacks' argument by descent along a surjection to a
finite étale thickening gives the result directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The direct image of a constructible sheaf of sets along a finite morphism.** Let
`f : X ⟶ Y` be a finite morphism to a locally Noetherian scheme and `ℱ` a constructible sheaf
of sets on the small étale site of `X`. Then `f_* ℱ` is constructible. -/
@[weil "lem_fk104_finite_pushforward_constructible"]
theorem isConstructibleSetSheaf_smallPushforward_of_isFinite
    [IsFinite (B.inclusion.map f)] [IsLocallyNoetherian Y.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleSetSheaf B Y ((B.smallPushforward f (Type (u + 1))).obj F) := by
  have : IsLocallyNoetherian (B.inclusion.obj Y) := ‹IsLocallyNoetherian Y.obj›
  exact isConstructibleSetSheaf_pushforward_of_isFinite B f
    ⟨inferInstance, inferInstance, inferInstance⟩ F hF

end AlgebraicGeometry

end
