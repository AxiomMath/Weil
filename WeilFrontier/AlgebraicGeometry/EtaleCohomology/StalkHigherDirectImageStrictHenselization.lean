module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkHigherDirectImageStrictHenselization
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Attr

/-!
# Stalks of higher direct images via the strict localization

Let `f : Y ⟶ X` be a quasi-compact quasi-separated morphism of schemes (for instance a morphism
of finite type of noetherian schemes), `F` an abelian sheaf on the small étale site of `Y`, `x`
a geometric point of `X` with strict local ring `𝒪̃_{X,x}`, `Ỹ = Y ×_X Spec 𝒪̃_{X,x}` and `F̃`
the inverse image of `F` on `Ỹ`. For every `ν ≥ 0`,

`(R^ν f_* F)_x ≅ H^ν(Ỹ, F̃)`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.higherDirectImageStalkIsoCohomologyStrictHenselization`: for a
  quasi-compact quasi-separated morphism `f` of a big étale site, the stalk at `x` of
  `R^ν f_* F` on the size-bounded small étale site `AlgebraicGeometry.SmallEtale` is the
  `ν`-th étale cohomology of the inverse image of `F` on `Ỹ`.
* `BigEtaleSite.higherDirectImageStalkIsoCohomologyStrictHenselizationOfIsNoetherian`: the same
  for a morphism from a noetherian scheme, the setting of the source.

## Implementation notes

The isomorphism is [Stacks, Tag 03Q9] (`AlgebraicGeometry.stalkHigherDirectImageIso`), stated on
Mathlib's small étale sites `Scheme.smallEtaleTopology`, transported to the size-bounded sites:
the higher direct image along the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv`
(`AlgebraicGeometry.BigEtaleSite.etaleAbelianHigherDirectImageIso`), and the stalk at a
geometric point (`AlgebraicGeometry.SmallEtale.sheafFiber_sheafEquiv_functor_obj_iso`).

The scheme `Ỹ` is in general not a scheme of the big étale site, so its cohomology is taken on
Mathlib's small étale site of `Ỹ`, as the right derived functors of global sections; the sheaf
`F̃` is the inverse image along the projection `Ỹ ⟶ Y` of the sheaf corresponding to `F` on
Mathlib's small étale site of `Y`. The coefficients are `AddCommGrpCat.{u + 1}`, the universe
in which the Stacks isomorphism is available.

The source assumes `f` of finite type between noetherian separated schemes; only the
quasi-compactness and quasi-separatedness of `f` are used, and no torsion hypothesis on `F` is
needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.4, 4.19
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.BigEtaleSite

attribute [local instance] smallEtaleSheaf_hasInjectiveResolutions

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) (x : GeometricPoint X.obj)
  (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) (ν : ℕ)

/-- **The stalk of a higher direct image is the cohomology of the base change to the strict
localization.** For a quasi-compact quasi-separated morphism `f : Y ⟶ X` of a big étale site,
an abelian sheaf `F` on the small étale site of `Y`, a geometric point `x` of `X` and `ν : ℕ`,
the stalk at `x` of `R^ν f_* F` is `H^ν(Ỹ, F̃)`, where `Ỹ = Y ×_X Spec 𝒪̃_{X,x}` and `F̃` is the
inverse image of `F` along the projection `Ỹ ⟶ Y`. -/
@[weil "prop_fk104_stalk_higher_direct_image_cohomology_strict_localization"]
def higherDirectImageStalkIsoCohomologyStrictHenselization
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] :
    (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj
        ((higherDirectImage.{u + 1} B f ν).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology
          (strictHenselizationBaseChange B X.property (B.inclusion.map f) x))
          AddCommGrpCat.{u + 1}).rightDerived ν).obj
        ((smallEtalePullbackAb
          (strictHenselizationBaseChangeToSource B X.property (B.inclusion.map f) x)).obj
          ((SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{u + 1}).functor.obj F)) :=
  (SmallEtale.sheafFiber_sheafEquiv_functor_obj_iso B X.obj X.property _ x _).symm ≪≫
    (pointSmallEtale x.hom).sheafFiber.mapIso
      ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor.mapIso
        ((higherDirectImage.{u + 1} B f ν).mapIso
          ((SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{u + 1}).unitIso.app F)) ≪≫
        ((etaleAbelianHigherDirectImageIso.{u, 0} B f ν).app
          ((SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{u + 1}).functor.obj F)).symm) ≪≫
    stalkHigherDirectImageIso B X.property (B.inclusion.map f) x _ ν

/-- **The stalk of a higher direct image, for a noetherian source.** For a morphism `f : Y ⟶ X`
of a big étale site with `Y` noetherian, an abelian sheaf `F` on the small étale site of `Y`, a
geometric point `x` of `X` and `ν : ℕ`, `(R^ν f_* F)_x ≅ H^ν(Y ×_X Spec 𝒪̃_{X,x}, F̃)`. -/
@[weil "prop_fk104_stalk_higher_direct_image_cohomology_strict_localization"]
def higherDirectImageStalkIsoCohomologyStrictHenselizationOfIsNoetherian [IsNoetherian Y.obj] :
    (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj
        ((higherDirectImage.{u + 1} B f ν).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology
          (strictHenselizationBaseChange B X.property (B.inclusion.map f) x))
          AddCommGrpCat.{u + 1}).rightDerived ν).obj
        ((smallEtalePullbackAb
          (strictHenselizationBaseChangeToSource B X.property (B.inclusion.map f) x)).obj
          ((SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{u + 1}).functor.obj F)) :=
  haveI : QuasiCompact (B.inclusion.map f) :=
    @quasiCompact_of_noetherianSpace_source Y.obj X.obj _ (B.inclusion.map f)
  haveI : QuasiSeparated (B.inclusion.map f) :=
    @QuasiSeparated.of_quasiSeparatedSpace Y.obj X.obj (B.inclusion.map f) _
  higherDirectImageStalkIsoCohomologyStrictHenselization B f x F ν

end AlgebraicGeometry.BigEtaleSite

end
