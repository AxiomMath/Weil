module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Attr

/-!
# Étale cohomology of the direct image along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and `F` an abelian sheaf on the small étale site
of `X`. Then `H^q(X, F) ≅ H^q(Y, f_* F)` for every `q ≥ 0`. The higher direct images of a
finite (more generally, integral) morphism vanish, so `f_*` carries an injective resolution of
`F` to an injective resolution of `f_* F`, and `Γ(Y, f_* I) = Γ(X, I)`.

This file states the result on the size-bounded small étale sites
`AlgebraicGeometry.SmallEtale B X hX` of a big étale site `B`, with the direct image
`AlgebraicGeometry.BigEtaleSite.smallPushforward`, for every integral morphism `f`.

## Main definitions

* `CategoryTheory.Sheaf.H.mapAddEquiv`: an isomorphism of abelian sheaves induces an isomorphism
  of their cohomology groups.
* `AlgebraicGeometry.BigEtaleSite.cohomologySmallPushforwardAddEquiv`: for `f` integral,
  `H^q(Y, f_* F) ≃+ H^q(X, F)`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.nonempty_addEquiv_cohomology_smallPushforward_of_isFinite`:
  for `f` finite, `H^q(X, F) ≅ H^q(Y, f_* F)` for every `q`.

## Implementation notes

The isomorphism is transported from Mathlib's small étale sites, where it is
`Stacks.EtaleCohomology.etaleCohomologyDirectImageMap_bijective` (the map
`H^q(Y, f_* F) → H^q(X, F)` is bijective for `f` integral), along the comparison
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sites: cohomology is unchanged by
restriction to a dense subsite (`Stacks.Cohomology.DenseSubsite.hAddEquiv`), and the bounded
direct image is the conjugate of Mathlib's
(`AlgebraicGeometry.SmallEtale.smallPushforwardIsoSheafEquiv`).
The coefficients are `AddCommGrpCat.{u + 1}` for the scheme universe `u`; the `Ext`-groups
defining cohomology live in an arbitrary universe `w`, and, there being no global `HasExt`
instance, the four `HasExt.{w}` hypotheses (on both sites over `X` and over `Y`) are binders.
The result holds for integral `f`, which contains the finite case.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl], I.5
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u

/-- An isomorphism of abelian sheaves induces an isomorphism of their cohomology groups. -/
def CategoryTheory.Sheaf.H.mapAddEquiv {C : Type*} [Category* C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    {F G : Sheaf J AddCommGrpCat.{v}} (e : F ≅ G) (n : ℕ) : F.H n ≃+ G.H n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' := map_add _

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.obj.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The cohomology of a direct image along an integral morphism.** For a morphism
`f : X ⟶ Y` of a big étale site whose morphism of schemes is integral (finite, for instance)
and an abelian sheaf `F` on the small étale site of `X`, `H^q(Y, f_* F) ≃+ H^q(X, F)` for
every `q`. -/
@[weil "lem_fk105_finite_morphism_statements_equivalent"]
def cohomologySmallPushforwardAddEquiv [IsIntegralHom (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F).H q ≃+ F.H q :=
  haveI := smallEtaleSheaf_isGrothendieckAbelian B X
  haveI := smallEtaleSheaf_isGrothendieckAbelian B Y
  haveI : HasExt.{w} (Sheaf (B.inclusion.obj X).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ‹HasExt.{w} (Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})›
  haveI : HasExt.{w} (Sheaf (B.inclusion.obj Y).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ‹HasExt.{w} (Sheaf Y.obj.smallEtaleTopology AddCommGrpCat.{u + 1})›
  let EX := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  let G := (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} (B.inclusion.map f)).obj
    (EX.functor.obj F)
  (Sheaf.H.mapAddEquiv ((SmallEtale.smallPushforwardIsoSheafEquiv f).app F) q).trans <|
    (Stacks.Cohomology.DenseSubsite.hAddEquiv (SmallEtale.topology B Y.obj Y.property)
      Y.obj.smallEtaleTopology (SmallEtale.toEtaleSite B Y.obj Y.property) G q).symm.trans <|
    (AddEquiv.ofBijective _
      (Stacks.EtaleCohomology.etaleCohomologyDirectImageMap_bijective.{u, 0, w}
        (B.inclusion.map f) (EX.functor.obj F) q)).trans <|
    (Stacks.Cohomology.DenseSubsite.hAddEquiv (SmallEtale.topology B X.obj X.property)
      X.obj.smallEtaleTopology (SmallEtale.toEtaleSite B X.obj X.property)
        (EX.functor.obj F) q).trans
    (Sheaf.H.mapAddEquiv (EX.unitIso.app F).symm q)

/-- **Cohomology along a finite morphism.** For a finite morphism `f : X ⟶ Y` of a big étale
site and an abelian sheaf `F` on the small étale site of `X`, `H^q(X, F) ≅ H^q(Y, f_* F)` for
every `q ≥ 0`. -/
@[weil "lem_fk105_finite_morphism_statements_equivalent"]
theorem nonempty_addEquiv_cohomology_smallPushforward_of_isFinite
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (F.H q ≃+ ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F).H q) :=
  ⟨(cohomologySmallPushforwardAddEquiv f F q).symm⟩

end AlgebraicGeometry.BigEtaleSite
