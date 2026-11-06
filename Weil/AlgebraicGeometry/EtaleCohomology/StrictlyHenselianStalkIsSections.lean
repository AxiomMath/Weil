module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Attr

/-!
# Stalks over a strictly Henselian local ring at the closed point

Let `R` be a strictly Henselian local ring, `S = Spec R`, and `s` a geometric point of `S`
lying over the closed point. For every presheaf `P` on the small étale site of `S` (with values
in any category with the relevant colimits, e.g. abelian groups), the canonical map
`P(S) ⟶ P_s` from sections over the final object to the stalk at `s` is an isomorphism.

The reason is that the final object `S`, with its canonical lift of `s`, is initial among the
étale neighbourhoods of `s`: every étale neighbourhood `(U, u)` admits a unique section
`S ⟶ U` of its structure morphism sending `s` to `u`. So the colimit defining the stalk is
attained at `(S, s)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.isIso_toPresheafFiber_final_of_strictlyHenselian`: the germ
  map `P(S) ⟶ P_s` at the final neighbourhood is an isomorphism, for every presheaf `P`.
* `AlgebraicGeometry.GeometricPoint.bijective_toPresheafFiber_final_of_strictlyHenselian`: the
  same for presheaves of abelian groups, as a bijection.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale` inside a big étale site, the geometric
point is over an algebraically closed field, and the stalk is the fibre
`CategoryTheory.GrothendieckTopology.Point.presheafFiber` of the site point
`AlgebraicGeometry.geometricPointSitePoint` (which is `AlgebraicGeometry.etaleStalk`). The
source allows a separably closed field for the geometric point; the stalk does not change on
passing to its algebraic closure. The result holds for presheaves with values in any category
with colimits, not only abelian groups.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK], I.8
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.GeometricPoint

variable (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
  (hS : B.Contains (Spec (.of R))) (s : GeometricPoint (Spec (.of R)))

/-- Over a strictly Henselian local ring `R`, for a geometric point `s` of `Spec R` lying over
the closed point, the canonical map from sections over `Spec R` to the stalk at `s` is an
isomorphism, for every presheaf on the small étale site. -/
@[weil "lem_fk108_strictly_henselian_stalk_is_sections"]
theorem isIso_toPresheafFiber_final_of_strictlyHenselian [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (P : (SmallEtale B (Spec (.of R)) hS)ᵒᵖ ⥤ A) :
    IsIso ((geometricPointSitePoint B (Spec (.of R)) hS s).toPresheafFiber
      (SmallEtale.final B (Spec (.of R)) hS)
      (Stacks.StrictlyHenselian.finalNeighborhood B R hS s).2 P) := by
  obtain ⟨hinit⟩ := Stacks.StrictlyHenselian.nonempty_isInitial_finalNeighborhood B R hS s hs
  exact (colimit.isColimit _).isIso_ι_app_of_isTerminal _ hinit.op

/-- Over a strictly Henselian local ring `R`, for a geometric point `s` of `Spec R` lying over
the closed point and a presheaf of abelian groups `P` on the small étale site, the canonical
map `P(Spec R) ⟶ P_s` is bijective. -/
@[weil "lem_fk108_strictly_henselian_stalk_is_sections"]
theorem bijective_toPresheafFiber_final_of_strictlyHenselian [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    (P : (SmallEtale B (Spec (.of R)) hS)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Function.Bijective ((geometricPointSitePoint B (Spec (.of R)) hS s).toPresheafFiber
      (SmallEtale.final B (Spec (.of R)) hS)
      (Stacks.StrictlyHenselian.finalNeighborhood B R hS s).2 P) := by
  have := isIso_toPresheafFiber_final_of_strictlyHenselian B R hS s hs P
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.GeometricPoint

end
