module

public import WeilFrontier.AlgebraicGeometry.Sites.PointTestSheafIsSheaf
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleNeighborhoodsSeparableClosure
public import WeilFrontier.AlgebraicGeometry.Sites.GeometricPointComparison

/-!
# The point test sheaf and étale neighbourhoods on the bounded small étale site

Let `x` be a geometric point of a scheme `X` (with algebraically closed field) and let `B` be a
big étale site containing `X`. The point test sheaf `𝒮_{x,S} : U ↦ Map(U(x), S)` and the
category of étale neighbourhoods of a separably closed point are first constructed on Mathlib's
small étale site `X.Etale`. This file gives their forms on the bounded small étale site
`SmallEtale B X hX` of [Stacks, Tag 021B], whose point attached to `x` is
`AlgebraicGeometry.geometricPointSitePoint`.

* The set of lifts `U(x)` of `x` to an object `U` of the bounded site is the fibre of
  `geometricPointSitePoint B X hX x` at `U`.
* The point test sheaf on the bounded site is the skyscraper sheaf with value `S` at
  `geometricPointSitePoint B X hX x`; its sections over `U` are the maps `U(x) → S`, restriction
  being precomposition, and it is the restriction of the point test sheaf of Mathlib's site.
  More generally, for every coefficient category, restriction carries the skyscraper sheaf
  functor at the point of Mathlib's site to the skyscraper sheaf functor at
  `geometricPointSitePoint`.
* For a set `S` in any universe, the restriction of the presheaf `U ↦ Map(U(x), S)` to the
  bounded site is a sheaf.
* The étale neighbourhoods in the bounded site of a separably closed point `s` and of the point
  `s'` given by the separable closure of the residue field are isomorphic categories.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.liftsEquivGeometricPointFiber`
* `AlgebraicGeometry.GeometricPoint.pointTestSheafSmallEtale`
* `AlgebraicGeometry.GeometricPoint.pointTestSheafSmallEtaleObjEquiv`
* `AlgebraicGeometry.GeometricPoint.sheafEquivInversePointTestSheafIso`
* `AlgebraicGeometry.GeometricPoint.skyscraperSheafFunctorCompSheafEquivInverseIso`
* `AlgebraicGeometry.Scheme.neighborhoodsIsoResidueSeparableClosureSmallEtale`
* `AlgebraicGeometry.GeometricPoint.neighborhoodsEquivResidueSeparableClosureSmallEtale`

## Main results

* `AlgebraicGeometry.GeometricPoint.pointTestSheafSmallEtaleObjEquiv_map`
* `AlgebraicGeometry.GeometricPoint.isSheaf_pointTestPresheaf_smallEtale`

## Implementation notes

The stalk is unchanged under passage from a separably closed point to an algebraic closure on
the bounded site by `AlgebraicGeometry.GeometricPoint.sheafFiberSheafEquivOfIsSepClosedIso`;
nothing is added here for it. The étale neighbourhoods of the separably closed point `s'` on the
bounded site are the category of elements of the restriction of the fibre functor of
`AlgebraicGeometry.Scheme.pointSmallEtale s'`, since the bounded site has points only for
geometric points with algebraically closed fields.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2, I.4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' u

namespace AlgebraicGeometry.GeometricPoint

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (x : GeometricPoint X)

/-- Transport of `AlgebraicGeometry.GeometricPoint.Lifts`: the lifts of `x` to an object `U` of
the bounded small étale site are the fibre of `geometricPointSitePoint B X hX x` at `U`. -/
def liftsEquivGeometricPointFiber (U : SmallEtale B X hX) :
    x.Lifts ((SmallEtale.toEtaleSite B X hX).obj U) ≃ (geometricPointFiber B X hX x).obj U :=
  (x.liftsEquivFiber _).trans ((toEtaleSiteFiberIso B X hX x).app U).toEquiv

/-- Transport of `AlgebraicGeometry.GeometricPoint.Lifts.map`: under
`liftsEquivGeometricPointFiber`, `h_*` is the map of fibres of `geometricPointSitePoint`. -/
lemma liftsEquivGeometricPointFiber_map {U V : SmallEtale B X hX} (h : V ⟶ U)
    (v : x.Lifts ((SmallEtale.toEtaleSite B X hX).obj V)) :
    x.liftsEquivGeometricPointFiber B hX U (Lifts.map ((SmallEtale.toEtaleSite B X hX).map h) v) =
      (geometricPointFiber B X hX x).map h (x.liftsEquivGeometricPointFiber B hX V v) :=
  rfl

/-- Transport of `AlgebraicGeometry.GeometricPoint.pointTestSheaf`: the point test sheaf
`𝒮_{x,S}` on the bounded small étale site, the skyscraper sheaf with value `S` at
`geometricPointSitePoint B X hX x`. -/
abbrev pointTestSheafSmallEtale (S : Type u) : Sheaf (SmallEtale.topology B X hX) (Type u) :=
  (geometricPointSitePoint B X hX x).skyscraperSheafFunctor.obj S

/-- Transport of `AlgebraicGeometry.GeometricPoint.pointTestSheafObjEquiv`: the sections of the
point test sheaf on the bounded site over `U` are the maps `U(x) → S`. -/
def pointTestSheafSmallEtaleObjEquiv (S : Type u) (U : SmallEtale B X hX) :
    (x.pointTestSheafSmallEtale B hX S).obj.obj (op U) ≃
      ((geometricPointFiber B X hX x).obj U → S) :=
  (Types.productIso.{u, u} fun _ : (geometricPointFiber B X hX x).obj U => S).toEquiv

lemma pointTestSheafSmallEtaleObjEquiv_apply (S : Type u) (U : SmallEtale B X hX)
    (c : (x.pointTestSheafSmallEtale B hX S).obj.obj (op U))
    (v : (geometricPointFiber B X hX x).obj U) :
    x.pointTestSheafSmallEtaleObjEquiv B hX S U c v =
      Pi.π (fun _ : (geometricPointFiber B X hX x).obj U => S) v c := by
  rfl

/-- Transport of `AlgebraicGeometry.GeometricPoint.pointTestSheafObjEquiv_map`: restriction of a
section of the point test sheaf on the bounded site along `h : V ⟶ U` is `c ↦ c ∘ h_*`. -/
lemma pointTestSheafSmallEtaleObjEquiv_map (S : Type u) {U V : SmallEtale B X hX} (h : V ⟶ U)
    (c : (x.pointTestSheafSmallEtale B hX S).obj.obj (op U)) :
    x.pointTestSheafSmallEtaleObjEquiv B hX S V
        ((x.pointTestSheafSmallEtale B hX S).obj.map h.op c) =
      x.pointTestSheafSmallEtaleObjEquiv B hX S U c ∘ (geometricPointFiber B X hX x).map h := by
  funext v
  simp only [pointTestSheafSmallEtaleObjEquiv_apply, Function.comp_apply]
  have key : (x.pointTestSheafSmallEtale B hX S).obj.map h.op ≫
      Pi.π (fun _ : (geometricPointFiber B X hX x).obj V => S) v =
      Pi.π (fun _ : (geometricPointFiber B X hX x).obj U => S)
        ((geometricPointFiber B X hX x).map h v) := by
    change ((geometricPointSitePoint B X hX x).skyscraperPresheafFunctor.obj S).map h.op ≫ _ = _
    simp only [GrothendieckTopology.Point.skyscraperPresheafFunctor_obj_map]
    exact (Pi.map'_comp_π _ _ _).trans (Category.comp_id _)
  exact ConcreteCategory.congr_hom key c

/-- The componentwise identification of the restriction of `x.pointTestSheaf S` to the bounded
site with `x.pointTestSheafSmallEtale B hX S`: both sections are maps `U(x) → S`. -/
def sheafEquivInversePointTestSheafObjEquiv (S : Type u) (U : SmallEtale B X hX) :
    (x.pointTestSheaf S).obj.obj (op ((SmallEtale.toEtaleSite B X hX).obj U)) ≃
      (x.pointTestSheafSmallEtale B hX S).obj.obj (op U) :=
  (x.pointTestSheafObjEquiv S ((SmallEtale.toEtaleSite B X hX).obj U)).trans
    (((x.liftsEquivGeometricPointFiber B hX U).arrowCongr (Equiv.refl S)).trans
      (x.pointTestSheafSmallEtaleObjEquiv B hX S U).symm)

lemma pointTestSheafSmallEtaleObjEquiv_sheafEquivInversePointTestSheafObjEquiv (S : Type u)
    (U : SmallEtale B X hX)
    (c : (x.pointTestSheaf S).obj.obj (op ((SmallEtale.toEtaleSite B X hX).obj U))) :
    x.pointTestSheafSmallEtaleObjEquiv B hX S U
        (x.sheafEquivInversePointTestSheafObjEquiv B hX S U c) =
      x.pointTestSheafObjEquiv S ((SmallEtale.toEtaleSite B X hX).obj U) c ∘
        (x.liftsEquivGeometricPointFiber B hX U).symm := by
  rw [sheafEquivInversePointTestSheafObjEquiv, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

lemma sheafEquivInversePointTestSheafObjEquiv_naturality (S : Type u) {U V : SmallEtale B X hX}
    (h : V ⟶ U) (c : (x.pointTestSheaf S).obj.obj (op ((SmallEtale.toEtaleSite B X hX).obj U))) :
    x.sheafEquivInversePointTestSheafObjEquiv B hX S V
        ((x.pointTestSheaf S).obj.map ((SmallEtale.toEtaleSite B X hX).map h).op c) =
      (x.pointTestSheafSmallEtale B hX S).obj.map h.op
        (x.sheafEquivInversePointTestSheafObjEquiv B hX S U c) := by
  apply (x.pointTestSheafSmallEtaleObjEquiv B hX S V).injective
  rw [pointTestSheafSmallEtaleObjEquiv_map,
    pointTestSheafSmallEtaleObjEquiv_sheafEquivInversePointTestSheafObjEquiv,
    pointTestSheafSmallEtaleObjEquiv_sheafEquivInversePointTestSheafObjEquiv,
    pointTestSheafObjEquiv_map]
  funext v
  simp only [Function.comp_apply]
  congr 1

/-- Transport of `AlgebraicGeometry.GeometricPoint.pointTestSheaf` along the comparison of the
two small étale sites: the restriction of the point test sheaf of Mathlib's site to the bounded
site is the point test sheaf of the bounded site. -/
def sheafEquivInversePointTestSheafIso (S : Type u) :
    (SmallEtale.sheafEquiv B X hX (Type u)).inverse.obj (x.pointTestSheaf S) ≅
      x.pointTestSheafSmallEtale B hX S :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U => (x.sheafEquivInversePointTestSheafObjEquiv B hX S U.unop).toIso)
      fun {U V} h => by
        ext c
        exact x.sheafEquivInversePointTestSheafObjEquiv_naturality B hX S h.unop c)

/-- Under `sheafEquivInversePointTestSheafIso`, a section `c : U(x) → S` of the point test sheaf
of Mathlib's site goes to the same map, read on the fibre of `geometricPointSitePoint`. -/
lemma pointTestSheafSmallEtaleObjEquiv_sheafEquivInversePointTestSheafIso_hom (S : Type u)
    (U : SmallEtale B X hX)
    (c : (x.pointTestSheaf S).obj.obj (op ((SmallEtale.toEtaleSite B X hX).obj U))) :
    x.pointTestSheafSmallEtaleObjEquiv B hX S U
        ((x.sheafEquivInversePointTestSheafIso B hX S).hom.hom.app (op U) c) =
      x.pointTestSheafObjEquiv S ((SmallEtale.toEtaleSite B X hX).obj U) c ∘
        (x.liftsEquivGeometricPointFiber B hX U).symm :=
  x.pointTestSheafSmallEtaleObjEquiv_sheafEquivInversePointTestSheafObjEquiv B hX S U c

/-- Transport of `AlgebraicGeometry.GeometricPoint.pointTestSheaf`, for any coefficient category:
restriction to the bounded site carries the skyscraper sheaf functor at the point
`Scheme.pointSmallEtale x.hom` of Mathlib's site to the skyscraper sheaf functor at
`geometricPointSitePoint B X hX x`. Both are right adjoint to the stalk functor at `x`. -/
def skyscraperSheafFunctorCompSheafEquivInverseIso (A : Type u') [Category.{v'} A]
    [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A] :
    (Scheme.pointSmallEtale x.hom).skyscraperSheafFunctor ⋙
        (SmallEtale.sheafEquiv B X hX A).inverse ≅
      (geometricPointSitePoint B X hX x).skyscraperSheafFunctor :=
  (((SmallEtale.sheafEquiv B X hX A).toAdjunction.comp
      (Scheme.pointSmallEtale x.hom).skyscraperSheafAdjunction).ofNatIsoLeft
      (SmallEtale.sheafEquivFunctorCompSheafFiberIso B X hX A x)).rightAdjointUniq
    (geometricPointSitePoint B X hX x).skyscraperSheafAdjunction

/-- Transport of `AlgebraicGeometry.GeometricPoint.isSheaf_pointTestPresheaf`: for a set `S` in
any universe, the restriction of the presheaf `U ↦ Map(U(x), S)` to the bounded small étale site
is a sheaf. -/
theorem isSheaf_pointTestPresheaf_smallEtale (S : Type w) :
    Presheaf.IsSheaf (SmallEtale.topology B X hX)
      ((SmallEtale.toEtaleSite B X hX).op ⋙ x.pointTestPresheaf S) :=
  ((SmallEtale.sheafEquiv B X hX (Type (max u w))).inverse.obj
    ⟨_, x.isSheaf_pointTestPresheaf S⟩).property

end AlgebraicGeometry.GeometricPoint

namespace AlgebraicGeometry.Scheme

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {K : Type u} [Field K]
  [IsSepClosed K] (s : Spec (.of K) ⟶ X)

/-- Transport of `AlgebraicGeometry.Scheme.neighborhoodsIsoResidueSeparableClosure`: the étale
neighbourhoods in the bounded small étale site of `s' : Spec k' ⟶ X` and of `s : Spec K ⟶ X`
(the categories of elements of the restricted fibre functors) are isomorphic categories, by
`(U, u') ↦ (U, j ≫ u')`. -/
def neighborhoodsIsoResidueSeparableClosureSmallEtale :
    Cat.of (SmallEtale.toEtaleSite B X hX ⋙
        (pointSmallEtale (residueSeparableClosurePoint s)).fiber).Elements ≅
      Cat.of (SmallEtale.toEtaleSite B X hX ⋙ (pointSmallEtale s).fiber).Elements :=
  Functor.elementsFunctor.mapIso
    (Functor.isoWhiskerLeft (SmallEtale.toEtaleSite B X hX) (fiberIsoResidueSeparableClosure s))

/-- Transport of
`AlgebraicGeometry.Scheme.neighborhoodsIsoResidueSeparableClosure_hom_toFunctor_comp_π`: the
isomorphism commutes with the forgetful functors to the bounded small étale site. -/
lemma neighborhoodsIsoResidueSeparableClosureSmallEtale_hom_toFunctor_comp_π :
    (neighborhoodsIsoResidueSeparableClosureSmallEtale B hX s).hom.toFunctor ⋙
        CategoryOfElements.π _ =
      CategoryOfElements.π _ :=
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.GeometricPoint

open Scheme

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (x : GeometricPoint X)

/-- Transport of `AlgebraicGeometry.GeometricPoint.neighborhoodsEquivResidueSeparableClosure`:
the étale neighbourhoods of `x` in the bounded small étale site (the category of elements of the
fibre functor of `geometricPointSitePoint B X hX x`) are equivalent to those of
`x' : Spec k' ⟶ X`, `k'` the separable closure of the residue field of the underlying point. -/
def neighborhoodsEquivResidueSeparableClosureSmallEtale :
    (geometricPointSitePoint B X hX x).fiber.Elements ≌
      (SmallEtale.toEtaleSite B X hX ⋙
        (pointSmallEtale (residueSeparableClosurePoint x.hom)).fiber).Elements :=
  (Cat.equivOfIso (Functor.elementsFunctor.mapIso (toEtaleSiteFiberIso B X hX x).symm)).trans
    (Cat.equivOfIso (neighborhoodsIsoResidueSeparableClosureSmallEtale B hX x.hom).symm)

/-- The equivalence `neighborhoodsEquivResidueSeparableClosureSmallEtale` commutes with the
forgetful functors to the bounded small étale site. -/
lemma neighborhoodsEquivResidueSeparableClosureSmallEtale_functor_comp_π :
    (neighborhoodsEquivResidueSeparableClosureSmallEtale B hX x).functor ⋙
        CategoryOfElements.π _ =
      CategoryOfElements.π _ :=
  rfl

end AlgebraicGeometry.GeometricPoint

end
