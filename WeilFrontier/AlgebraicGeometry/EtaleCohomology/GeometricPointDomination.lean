module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# Stalk functors at geometric points over the same point

Let `S` be a scheme and `s`, `s'` geometric points of `S` with the same underlying point
`x₀ ∈ S`. Then the stalk functors at `s` and at `s'` are isomorphic: there are bijections
`F_s ≃ F_{s'}`, one for every presheaf `F` on the small étale site of `S`, compatible with every
morphism of presheaves. Both geometric points are dominated by a third one (an algebraic closure
of a residue field of a point of `Spec k ×_S Spec k'` over the pair), and a morphism of geometric
points induces an isomorphism of stalk functors, since restriction along it is an equivalence of
the categories of étale neighbourhoods, hence final.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.presheafFiberIsoOfPointEq`: the isomorphism of stalk
  functors at two geometric points with the same underlying point.

## Main results

* `AlgebraicGeometry.GeometricPoint.exists_presheafFiber_equiv_of_point_eq`: for presheaves of
  sets, a family of bijections of stalks commuting with the maps induced by every morphism of
  presheaves.

## Implementation notes

Geometric points take values in algebraically closed fields and the étale site is the small
étale site `AlgebraicGeometry.SmallEtale` of a big étale site, following the Stacks project; the
stalk at a geometric point is the fibre of the associated point of the site
(`AlgebraicGeometry.geometricPointSitePoint`), which is the étale stalk by
`AlgebraicGeometry.etaleStalk_eq_presheafFiber`. The isomorphism is the one of
`AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase`, and holds for presheaves with values in
any category with small colimits. The proof in the source passes through the separable closures
of the residue field inside the two fields; a common dominating geometric point serves the same
purpose.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

/- FK's Et(X) and separably closed geometric points are replaced by StacksFrontier's `SmallEtale`
and geometric points over algebraically closed fields (the Stacks project convention); the result is
stated for presheaves with values in any category with small colimits, which contains FK's
presheaves of sets. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace GeometricPoint

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

lemma hom_default_eq_of_point_eq {s s' : GeometricPoint S} (h : s.point = s'.point) :
    s.hom default = s'.hom default := by
  rw [← s.point_eq_hom_apply, ← s'.point_eq_hom_apply, h]

/-- **Stalk functors at geometric points over the same point.** For two geometric points `s`,
`s'` of `S` with the same underlying point, the stalk functors `F ↦ F_s` and `F ↦ F_{s'}` on
presheaves on the small étale site are isomorphic. -/
@[weil "lem_fk103_stalk_functors_isomorphic_same_point"]
def presheafFiberIsoOfPointEq {s s' : GeometricPoint S} (h : s.point = s'.point)
    (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A] :
    (geometricPointSitePoint B S hS s).presheafFiber (A := A) ≅
      (geometricPointSitePoint B S hS s').presheafFiber :=
  etaleStalkPresheafFunctorIsoOfEqBase B S hS (hom_default_eq_of_point_eq S h) A

/-- **Stalk functors at geometric points over the same point**, for presheaves of sets: there
are bijections `ζ_F : F_s ≃ F_{s'}`, one for each presheaf of sets `F`, with
`ζ_G ∘ w_s = w_{s'} ∘ ζ_F` for every morphism of presheaves `w : F ⟶ G`. -/
@[weil "lem_fk103_stalk_functors_isomorphic_same_point"]
theorem exists_presheafFiber_equiv_of_point_eq {s s' : GeometricPoint S}
    (h : s.point = s'.point) :
    ∃ ζ : ∀ F : (SmallEtale B S hS)ᵒᵖ ⥤ Type u,
        (geometricPointSitePoint B S hS s).presheafFiber.obj F ≃
          (geometricPointSitePoint B S hS s').presheafFiber.obj F,
      ∀ {F G : (SmallEtale B S hS)ᵒᵖ ⥤ Type u} (w : F ⟶ G),
        ζ G ∘ (geometricPointSitePoint B S hS s).presheafFiber.map w =
          (geometricPointSitePoint B S hS s').presheafFiber.map w ∘ ζ F := by
  let e := presheafFiberIsoOfPointEq B S hS h (Type u)
  refine ⟨fun F => (e.app F).toEquiv, fun {F G} w => ?_⟩
  funext x
  exact ConcreteCategory.congr_hom (e.hom.naturality w) x

end GeometricPoint

end AlgebraicGeometry

end

/-! ### The étale stalk depends only on the underlying point -/

/-!
# The étale stalk depends only on the underlying point

Let `S` be a scheme and `p`, `q` two geometric points of `S` with the same image in `S`. For
every presheaf `F` on the small étale site of `S`, with values in a category having small
colimits, the stalks `F_p` and `F_q` are isomorphic, naturally in `F`. The isomorphism of
stalk functors is `AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase`: both points are
dominated by a third geometric point, and a morphism of geometric points induces an
isomorphism of stalks.

## Main definitions

* `AlgebraicGeometry.presheafFiberIsoOfEqBase`: the isomorphism of the stalk functors
  `F ↦ F_p` and `F ↦ F_q` of the points `geometricPointSitePoint` of the small étale site.

## Main results

* `AlgebraicGeometry.nonempty_etaleStalk_iso_of_eq_base`: `F_p ≅ F_q` for every presheaf `F`.

## Implementation notes

Geometric points are `AlgebraicGeometry.GeometricPoint`, over algebraically closed fields, and
the site is the small étale site `AlgebraicGeometry.SmallEtale` of a bounded big étale site.
"The same underlying point" is the equality `p.hom default = q.hom default` of the images of
the unique point of the spectrum of the field.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2]
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stalk functors of the points of the small étale site attached to two geometric points
with the same image in `S` are isomorphic. -/
def presheafFiberIsoOfEqBase {p q : GeometricPoint S} (h : p.hom default = q.hom default)
    (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A] :
    (geometricPointSitePoint B S hS p).presheafFiber (A := A) ≅
      (geometricPointSitePoint B S hS q).presheafFiber :=
  etaleStalkPresheafFunctorIsoOfEqBase B S hS h A

/-- The stalks of a presheaf on the small étale site at two geometric points with the same
underlying point are isomorphic. -/
@[weil "lem_fk102_stalk_depends_on_point"]
theorem nonempty_etaleStalk_iso_of_eq_base {p q : GeometricPoint S}
    (h : p.hom default = q.hom default) {A : Type v} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    Nonempty (etaleStalk B S hS p F ≅ etaleStalk B S hS q F) :=
  ⟨(etaleStalkPresheafFunctorIsoOfEqBase B S hS h A).app F⟩

end AlgebraicGeometry
