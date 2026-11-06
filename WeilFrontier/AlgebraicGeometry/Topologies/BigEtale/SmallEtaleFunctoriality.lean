module

public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# The direct image of an étale sheaf is a sheaf

Let `B` be a big étale site and `f : X ⟶ Y` a morphism of it. The direct image of a presheaf
`F` on the small étale site of `X` is the presheaf `U ↦ F(U ×_Y X)` on the small étale site of
`Y`. If `F` is a sheaf, so is its direct image: base change along `f` sends étale coverings of
`U` to étale coverings of `U ×_Y X` and commutes with the fibre products occurring in the sheaf
condition, that is, it is a continuous functor of sites.

## Main results

* `AlgebraicGeometry.BigEtaleSite.isSheaf_presheafDirectImage_obj`: the direct image of a sheaf
  (with values in any category) is a sheaf.

## Implementation notes

The statement is made on the small étale sites `SmallEtale` of a big étale site, with values in
an arbitrary category `A` (sets and abelian groups being the cases of the source). The proof is
the continuity of `AlgebraicGeometry.BigEtaleSite.smallEtaleBaseChange`, through which the direct
image of sheaves `AlgebraicGeometry.BigEtaleSite.smallPushforward` is defined.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2]
* [Stacks Project, Tag 03PY](https://stacks.math.columbia.edu/tag/03PY)
-/

public section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} {A : Type w} [Category.{v} A]

/-- **The direct image of an étale sheaf is an étale sheaf**: if `F` is a sheaf on the small
étale site of `X` and `f : X ⟶ Y`, then `f_* F`, `U ↦ F(U ×_Y X)`, is a sheaf on the small
étale site of `Y`. -/
@[weil "lem_fk102_direct_image_is_sheaf"]
theorem isSheaf_presheafDirectImage_obj (f : X ⟶ Y)
    {F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A}
    (hF : Presheaf.IsSheaf (SmallEtale.topology B X.obj X.property) F) :
    Presheaf.IsSheaf (SmallEtale.topology B Y.obj Y.property)
      ((presheafDirectImage B f A).obj F) :=
  ((B.smallPushforward f A).obj ⟨F, hF⟩).property

end AlgebraicGeometry.BigEtaleSite
