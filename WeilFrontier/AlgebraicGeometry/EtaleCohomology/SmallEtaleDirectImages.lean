module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteDerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Attr

/-!
# Higher direct images of abelian sheaves on small étale sites

Let `B` be a big étale site and `f : X ⟶ Y` a morphism of it. The direct image
`f_* : Sh(X_ét, Ab) ⥤ Sh(Y_ét, Ab)`, `(f_* F)(V) = F(V ×_Y X)`, is an additive functor between
abelian categories, and abelian sheaves on `X_ét` have enough injectives. The higher direct
images `R^i f_*` are its right derived functors: `R^i f_* F = H^i(f_* I^•)` for an injective
resolution `F → I^•`.

Equivalently, `R^i f_* F` is the `i`-th cohomology of the total right derived functor
`R f_* : D⁺(X_ét) ⥤ D⁺(Y_ét)` evaluated at the complex `F[0]` concentrated in degree `0`; the two
descriptions are identified, naturally in `F`, by `higherDirectImageIsoRightDerivedPlus`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.higherDirectImage`: the higher direct image
  `R^i f_* : Sh(X_ét, Ab) ⥤ Sh(Y_ét, Ab)`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.higherDirectImageObjIsoHomology`: for an injective resolution
  `F → I^•`, `R^i f_* F ≅ H^i(f_* I^•)`.
* `AlgebraicGeometry.BigEtaleSite.higherDirectImageIsoRightDerivedPlus`: `R^i f_*` is the
  functor `F ↦ H^i(R f_*(F[0]))` defined through the bounded below derived categories.
* `AlgebraicGeometry.BigEtaleSite.higherDirectImageObjIsoRightDerivedFunctorPlusHomology`: the
  same, with the classical derived functor `R^i(f_*) = H^i ∘ R f_*` on `D⁺(X_ét)`.
* `AlgebraicGeometry.BigEtaleSite.etaleAbelianHigherDirectImageIso`: on Mathlib's small étale
  sites `Scheme.Etale`, the higher direct image
  `Stacks.EtaleCohomology.etaleAbelianHigherDirectImage` is `higherDirectImage` transported
  along the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` of the sheaf categories.
* `AlgebraicGeometry.BigEtaleSite.higherDirectImageZeroIso`: `R^0 f_* ≅ f_*`.
* `AlgebraicGeometry.BigEtaleSite.isZero_higherDirectImage_obj_succ_of_injective`: the higher
  direct images of an injective sheaf vanish in positive degrees.

## Implementation notes

The site of `X` is the size-bounded small étale site `AlgebraicGeometry.SmallEtale` of the big
étale site `B`, and `f_*` is `AlgebraicGeometry.BigEtaleSite.smallPushforward`, restriction of
sections along base change. The coefficients are `AddCommGrpCat.{w}` for an arbitrary universe
`w` in which the sheaf categories have sheafification and injective resolutions; for `w = u`,
the universe of the schemes of `B`, enough injectives is the instance
`AlgebraicGeometry.SmallEtale.enoughInjectives_sheaf_addCommGrpCat_schemeUniverse`.

The source defines `R^i f_*` through chosen injective resolutions of the complexes of
`D⁺(X_ét)`; the right derived functor `CategoryTheory.Functor.rightDerived` is computed with the
chosen injective resolutions of objects, and any two choices give canonically isomorphic
functors, which is how the identifications above are stated.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.2
* [Stacks Project, Tag 04I2](https://stacks.math.columbia.edu/tag/04I2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

namespace SmallEtale

/-- Abelian sheaves on the small étale site of a scheme of a big étale site, with coefficients
in `AddCommGrpCat.{u}` for the universe `u` of the schemes, have enough injectives: they form a
Grothendieck abelian category. -/
instance enoughInjectives_sheaf_addCommGrpCat_schemeUniverse (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    EnoughInjectives (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.enoughInjectives

end SmallEtale

namespace BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The direct image of abelian sheaves is additive. -/
instance additive_smallPushforward_addCommGrpCat :
    (B.smallPushforward f AddCommGrpCat.{w}).Additive where
  map_add := rfl

/-- The direct image of abelian sheaves preserves finite limits: limits of sheaves are computed
sectionwise, and the direct image is restriction of sections along base change. -/
instance preservesFiniteLimits_smallPushforward_addCommGrpCat :
    PreservesFiniteLimits (B.smallPushforward f AddCommGrpCat.{w}) := by
  have : PreservesFiniteLimits (B.smallPushforward f AddCommGrpCat.{w} ⋙
      sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w}) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w} ⋙
        (Functor.whiskeringLeft _ _ _).obj (smallEtaleBaseChange B f).op))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w})

section

variable [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w}]
  [HasInjectiveResolutions (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})]

/-- **The higher direct image `R^i f_*`** along a morphism `f : X ⟶ Y` of a big étale site: the
`i`-th right derived functor of the direct image `f_* : Sh(X_ét, Ab) ⥤ Sh(Y_ét, Ab)` of abelian
sheaves on the small étale sites. -/
@[weil "def_fk102_higher_direct_image"]
abbrev higherDirectImage (i : ℕ) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w} :=
  (B.smallPushforward f AddCommGrpCat.{w}).rightDerived i

/-- `R^i f_* F` is the `i`-th cohomology sheaf `H^i(f_* I^•)` of the direct image of an
injective resolution `F → I^•`. -/
@[weil "def_fk102_higher_direct_image"]
def higherDirectImageObjIsoHomology (i : ℕ)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}}
    (I : InjectiveResolution F) :
    (higherDirectImage B f i).obj F ≅
      (((B.smallPushforward f AddCommGrpCat.{w}).mapHomologicalComplex _).obj
        I.cocomplex).homology i :=
  I.isoRightDerivedObj _ i

/-- The higher direct images of an injective abelian sheaf vanish in positive degrees. -/
theorem isZero_higherDirectImage_obj_succ_of_injective (i : ℕ)
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}) [Injective I] :
    IsZero ((higherDirectImage B f (i + 1)).obj I) :=
  Functor.isZero_rightDerived_obj_injective_succ _ _ _

/-- `R^0 f_* ≅ f_*`: the direct image is left exact. -/
def higherDirectImageZeroIso :
    higherDirectImage B f 0 ≅ B.smallPushforward f AddCommGrpCat.{w} :=
  (B.smallPushforward f AddCommGrpCat.{w}).rightDerivedZeroIsoSelf

end

section Derived

variable [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w}]
  [EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})]
  [HasDerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})]
  [HasDerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{w})]

/-- `R^i f_*` is, naturally in the sheaf `F`, the `i`-th cohomology `H^i(R f_*(F[0]))` of the
total right derived functor `R f_* : D⁺(X_ét) ⥤ D⁺(Y_ét)` at the complex `F[0]`. -/
@[weil "def_fk102_higher_direct_image"]
def higherDirectImageIsoRightDerivedPlus (i : ℕ) :
    higherDirectImage B f i ≅ (B.smallPushforward f AddCommGrpCat.{w}).rightDerivedPlus i :=
  (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard _ i).symm

/-- `R^i f_* F` is the classical derived functor `R^i(f_*) = H^i ∘ R f_*` of `f_*` on the
bounded below derived category, evaluated at the complex `F[0]` concentrated in degree `0`. -/
@[weil "def_fk102_higher_direct_image"]
def higherDirectImageObjIsoRightDerivedFunctorPlusHomology (i : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}) :
    (higherDirectImage B f i).obj F ≅
      ((B.smallPushforward f AddCommGrpCat.{w}).rightDerivedFunctorPlusHomology i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
  (higherDirectImageIsoRightDerivedPlus B f i).app F

end Derived

section MathlibSite

universe v

variable [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasInjectiveResolutions (Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})]

/-- On Mathlib's small étale sites, the higher direct image
`Stacks.EtaleCohomology.etaleAbelianHigherDirectImage` along `f` is `higherDirectImage B f q`,
conjugated by the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` between sheaves on the
size-bounded small étale sites and sheaves on Mathlib's small étale sites. -/
def etaleAbelianHigherDirectImageIso (q : ℕ) :
    Stacks.EtaleCohomology.etaleAbelianHigherDirectImage.{u, v} (B.inclusion.map f) q ≅
      (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{max (u + 1) v}).inverse ⋙
        higherDirectImage.{max (u + 1) v} B f q ⋙
          (SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{max (u + 1) v}).functor :=
  SmallEtale.rightDerivedSheafEquivPushforwardBaseChangeIso.{v, u} B f q

end MathlibSite

end BigEtaleSite

end AlgebraicGeometry
