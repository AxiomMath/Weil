module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleHigherDirectImageStalk
public import Weil.Attr

/-!
# The stalk of a higher direct image

Let `f : X ⟶ Y` be a morphism of schemes, `F` an abelian sheaf on the small étale site of `X`,
`F → J^•` an injective resolution and `P^i_J` the presheaf `U ↦ H^i((f_* J^•)(U))` on the small
étale site of `Y`. For every geometric point `a` of `Y`,

`(R^i f_* F)_a ≅ colim_{(U, u) ∈ N(a)^op} P^i_J(U)`,

the colimit being over the étale neighbourhoods of `a`, i.e. the stalk of the presheaf `P^i_J`
at `a`. Indeed `R^i f_* F` is the sheafification of `P^i_J`, and a stalk does not change under
sheafification. The values `P^i_J(U)` are the cohomology groups `H^i(X ×_Y U, F_U)`
(`Stacks.EtaleCohomology.directImageCohomologyPresheafObjIso`).

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.directImageCohomologyPresheaf`: the presheaf
  `U ↦ H^i((f_* J^•)(U))` on the size-bounded small étale site `AlgebraicGeometry.SmallEtale`
  of `Y`, for a morphism `f` of a big étale site.

## Main results

* `AlgebraicGeometry.BigEtaleSite.higherDirectImageStalkIso`: on the small étale sites
  `AlgebraicGeometry.SmallEtale`, the stalk at a geometric point `s` of `Y` of
  `R^i f_* F = (AlgebraicGeometry.BigEtaleSite.higherDirectImage B f i).obj F` is the stalk at
  `s` (the colimit over the étale neighbourhoods of `s`) of `P^i_J`.
* `Stacks.EtaleCohomology.smallEtaleStalkAbHigherDirectImageIso`: the same on Mathlib's small
  étale sites `AlgebraicGeometry.Scheme.Etale`, at a geometric point `Spec Ω ⟶ Y` with `Ω`
  separably closed, for the presheaf `Stacks.EtaleCohomology.directImageCohomologyPresheaf`.

## Implementation notes

The stalk of a presheaf at a point `Φ` of a site is `Φ.presheafFiber`, which is by definition the
colimit of the presheaf over the opposite of the category of elements of the fibre functor of
`Φ`; for the point attached to a geometric point this category of elements is the category of
étale neighbourhoods. The stalk of a sheaf is `Φ.sheafFiber`, the stalk of the underlying
presheaf.

Both results are stated for an arbitrary injective resolution `J`, as in the source: the
derived functors are computed with chosen resolutions, and the comparison with `J` is the
canonical isomorphism `CategoryTheory.InjectiveResolution.isoRightDerivedObj`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitagkiehl1988], I.2
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w}]
  {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}}

/-- The complex of abelian presheaves `f_* J^•` on the small étale site of `Y` obtained from a
resolution `F → J^•` by applying the direct image along `f` and forgetting the sheaf
condition. -/
abbrev directImagePresheafComplex (J : InjectiveResolution F) :
    CochainComplex ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ :=
  ((B.smallPushforward f AddCommGrpCat.{w} ⋙
    sheafToPresheaf (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{w}).mapHomologicalComplex _).obj J.cocomplex

/-- **The cohomology presheaf `P^i_J` of a direct image**, on the small étale site of `Y`: for
an injective resolution `F → J^•` and `i : ℕ`, the presheaf `U ↦ H^i((f_* J^•)(U))`, the
`i`-th cohomology of the complex of abelian groups of sections `(f_* J^•)(U)`. -/
def directImageCohomologyPresheaf (J : InjectiveResolution F) (i : ℕ) :
    (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (directImagePresheafComplex B f J).asFunctor ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.up ℕ) i

omit [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w}] in
/-- The value of `P^i_J` at `U` is the `i`-th cohomology of the complex of sections
`(f_* J^•)(U)`. -/
lemma directImageCohomologyPresheaf_obj (J : InjectiveResolution F) (i : ℕ)
    (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) :
    (directImageCohomologyPresheaf B f J i).obj U =
      ((directImagePresheafComplex B f J).asFunctor.obj U).homology i :=
  rfl

/-- `P^i_J` is the `i`-th right derived functor of `F ↦ f_* F`, viewed as a presheaf,
evaluated at `F`. -/
def directImageCohomologyPresheafIso
    [HasInjectiveResolutions (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})]
    (J : InjectiveResolution F) (i : ℕ) :
    directImageCohomologyPresheaf B f J i ≅
      ((B.smallPushforward f AddCommGrpCat.{w} ⋙
        sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w}).rightDerived
          i).obj F :=
  (directImagePresheafComplex B f J).asFunctorCompHomologyFunctorIso i ≪≫
    (J.isoRightDerivedObj _ i).symm

variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{w}] [HasProducts.{u} AddCommGrpCat.{w}]
  [HasInjectiveResolutions (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})]

/-- **The stalk of a higher direct image.** For a morphism `f : X ⟶ Y` of a big étale site, an
abelian sheaf `F` on the small étale site of `X` with an injective resolution `F → J^•`, a
geometric point `s` of `Y` and `i : ℕ`, the stalk at `s` of `R^i f_* F` is the stalk at `s` of
the presheaf `P^i_J : U ↦ H^i((f_* J^•)(U))`, that is, the colimit of the `P^i_J(U)` over the
étale neighbourhoods `(U, u)` of `s`. -/
@[weil "lem_fk102_higher_direct_image_stalk"]
def higherDirectImageStalkIso (s : GeometricPoint Y.obj) (J : InjectiveResolution F) (i : ℕ) :
    (geometricPointSitePoint B Y.obj Y.property s).sheafFiber.obj
        ((higherDirectImage B f i).obj F) ≅
      (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
        (directImageCohomologyPresheaf B f J i) :=
  (geometricPointSitePoint B Y.obj Y.property s).sheafFiber.mapIso
      ((Stacks.HigherDirectImage.higherDirectImageComparison B f i).iso.app F) ≪≫
    ((geometricPointSitePoint B Y.obj Y.property s).presheafToSheafCompSheafFiberIso
      AddCommGrpCat.{w}).app _ ≪≫
    (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.mapIso
      (directImageCohomologyPresheafIso B f J i).symm

end AlgebraicGeometry.BigEtaleSite

namespace Stacks.EtaleCohomology

attribute [local instance] smallEtalePushforward_additive

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The stalk of a higher direct image**, on Mathlib's small étale sites. For a morphism of
schemes `f : X ⟶ Y`, an abelian sheaf `F` on the small étale site of `X` with an injective
resolution `F → J^•`, a geometric point `x : Spec Ω ⟶ Y` with `Ω` separably closed and `i : ℕ`,
the stalk at `x` of `R^i f_* F` is the stalk at `x` of the presheaf
`P^i_J : U ↦ H^i((f_* J^•)(U))`, the colimit of the `P^i_J(U)` over the étale neighbourhoods
of `x`. -/
@[weil "lem_fk102_higher_direct_image_stalk"]
def smallEtaleStalkAbHigherDirectImageIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Y) {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (J : InjectiveResolution F) (i : ℕ) :
    (smallEtaleStalkAb x).obj (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived i).obj F) ≅
      (Scheme.pointSmallEtale x).presheafFiber.obj (directImageCohomologyPresheaf f J i) :=
  smallEtaleHigherDirectImageStalkIso f x F i ≪≫
    (Scheme.pointSmallEtale x).presheafFiber.mapIso (directImageCohomologyPresheafIso f J i).symm

end Stacks.EtaleCohomology
