module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDerived
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactSupportCohomologyDerived
public import Weil.Attr

/-!
# Base change for the derived direct image with proper support

Let `f : X ⟶ S` be a morphism of schemes with a compactification `c = (X̄, j, f̄)`, let
`g : T ⟶ S` be a morphism and `Z = T ×_S X`, with projections `f' : Z ⟶ T` and `g' : Z ⟶ X`.
Then `c_T = (T ×_S X̄, id_T × j, f̄')` is a compactification of `f'`
(`AlgebraicGeometry.CompactificationOf.baseChange`), and for every bounded below complex `K` with
torsion cohomology sheaves on the small étale site of `X` there is an isomorphism
`g⁻¹ Rf_! K ≅ Rf'_! (g'⁻¹ K)`, natural in `K`, where `Rf_!` is computed with `c` and `Rf'_!`
with `c_T`.

On Mathlib's small étale sites this is `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeIso`
([Stacks, Tag 0F7L]); this file gives it on the small étale sites `AlgebraicGeometry.SmallEtale`
of a big étale site, by transport along the equivalences of sheaf categories
`AlgebraicGeometry.SmallEtale.moduleSheafEquivEtaleModules`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivedInverseImage`: the inverse image `g⁻¹ : D⁺(S, Λ) ⥤ D⁺(T, Λ)`
  on the bounded below derived categories of sheaves of `Λ`-modules on the small étale sites.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekBaseChangeIso`: the natural isomorphism
  `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ g'⁻¹` on `D⁺_tors(X)`.

## Implementation notes

The source states the result for abelian sheaves; here the coefficients are an arbitrary ring
`Λ` (in `Type`), the case `Λ = ℤ` being the source's. The square is any cartesian square, not
only the chosen fibre product, and the base-changed compactification is the one of
`AlgebraicGeometry.CompactificationOf.baseChange`, whose ambient scheme is `pullback c.toBase g`,
whose open immersion has components `g' ≫ c.immersion` and `f'`
(`AlgebraicGeometry.CompactificationOf.baseChangeImmersion_fst`, `baseChangeImmersion_snd`) and
whose structure morphism is the second projection. The sheaf categories and the torsion
condition are those of `AlgebraicGeometry.SmallEtale.derivedLowerShriek` and
`AlgebraicGeometry.SmallEtale.isTorsionPlus`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} (Λ : Type r) [Ring Λ]

/-- **The derived inverse image** `g⁻¹ : D⁺(S, Λ) ⥤ D⁺(T, Λ)` along a morphism `g : T ⟶ S` of
objects of a big étale site, on the bounded below derived categories of sheaves of `Λ`-modules on
the small étale sites: the inverse image of Mathlib's small étale sites, which is exact, read
across the equivalences of sheaf categories. -/
def derivedInverseImage {S T : B.Scheme} (g : T.obj ⟶ S.obj) :
    DerivedCategory.Plus (ModuleSheaf.{u, r, r} B S Λ) ⥤
      DerivedCategory.Plus (ModuleSheaf.{u, r, r} B T Λ) :=
  (moduleSheafEquivEtaleModules B Λ S).functor.mapDerivedCategoryPlus ⋙
    Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlus.{u, r} Λ g ⋙
    (moduleSheafEquivEtaleModules B Λ T).inverse.mapDerivedCategoryPlus

/-- `g⁻¹` on the small étale sites of `B` is the derived inverse image of Mathlib's small étale
sites, across the equivalences `E` of the sheaf categories: `g⁻¹ ⋙ E_T ≅ E_S ⋙ g⁻¹`. -/
def derivedInverseImageCompIso {S T : B.Scheme} (g : T.obj ⟶ S.obj) :
    derivedInverseImage Λ g ⋙
        (moduleSheafEquivEtaleModules B Λ T).functor.mapDerivedCategoryPlus ≅
      (moduleSheafEquivEtaleModules B Λ S).functor.mapDerivedCategoryPlus ⋙
        Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlus.{u, r} Λ g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (mapDerivedCategoryPlusInverseCompFunctorIso Λ T) ≪≫
      Functor.rightUnitor _)

section BaseChange

attribute [-instance] hasSheafify_moduleCat_max hasSheafify_moduleSheaf

/-- Sheafification of presheaves of `Λ`-modules in the universe `u + 1` on the small étale site,
for `Λ : Type`: the instance `AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf` with its
coefficient universes fixed, so that instance search does not meet the universe constraint
`u + 1 = max (u + 1) ?v`. -/
local instance hasSheafify_moduleCat_succ (X : B.Scheme) (Λ : Type) [Ring Λ] :
    HasSheafify (topology B X.obj X.property) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleSheaf.{u, 0, 0} B X Λ

variable (Λ : Type) [Ring Λ] {X S T Z : B.Scheme} {f : X.obj ⟶ S.obj} {g : T.obj ⟶ S.obj}
  {g' : Z.obj ⟶ X.obj} {f' : Z.obj ⟶ T.obj} (sq : IsPullback g' f' f g) (c : f.Compactification)

/-- The functor `D⁺_tors(X) ⥤ D⁺_tors(X_étale)` from the torsion complexes on `SmallEtale B X`
to those on Mathlib's small étale site of `X`, induced by the equivalence of sheaf categories. -/
abbrev isTorsionPlusLift :
    (isTorsionPlus.{u, 0} B X.obj X.property Λ).FullSubcategory ⥤
      (Stacks.EtaleCohomology.isTorsionPlus.{u, 0} Λ X.obj).FullSubcategory :=
  ObjectProperty.lift (Stacks.EtaleCohomology.isTorsionPlus.{u, 0} Λ X.obj)
    ((isTorsionPlus.{u, 0} B X.obj X.property Λ).ι ⋙
      (moduleSheafEquivEtaleModules.{u, 0} B Λ X).functor.mapDerivedCategoryPlus)
    (fun K => K.property)

/-- **Base change for the derived direct image with proper support.** For a cartesian square
`g' ≫ f = f' ≫ g` of objects of a big étale site and a compactification `c` of `f`, the natural
isomorphism `g⁻¹ Rf_! K ≅ Rf'_! (g'⁻¹ K)` for `K` in `D⁺_tors(X)`, where `Rf_!` is computed with
`c` and `Rf'_!` with its base change `c.baseChange sq`, the compactification of `f'` with ambient
scheme `T ×_S X̄`. -/
@[weil "thm_fk108_proper_direct_image_base_change"]
def derivedLowerShriekBaseChangeIso :
    (isTorsionPlus.{u, 0} B X.obj X.property Λ).ι ⋙ derivedLowerShriek.{u, 0} Λ f c ⋙
        derivedInverseImage.{u, 0} Λ g ≅
      (isTorsionPlus.{u, 0} B X.obj X.property Λ).ι ⋙ derivedInverseImage.{u, 0} Λ g' ⋙
        derivedLowerShriek.{u, 0} Λ f' (c.baseChange sq) :=
  (Functor.isoWhiskerLeft
      ((isTorsionPlus.{u, 0} B X.obj X.property Λ).ι ⋙
        (moduleSheafEquivEtaleModules.{u, 0} B Λ X).functor.mapDerivedCategoryPlus ⋙
        Stacks.EtaleCohomology.derivedLowerShriek.{u, 0} f c Λ)
      (Functor.isoWhiskerRight (mapDerivedCategoryPlusInverseCompFunctorIso.{u, 0} Λ S)
        (Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlus.{u, 0} Λ g ⋙
          (moduleSheafEquivEtaleModules.{u, 0} B Λ T).inverse.mapDerivedCategoryPlus) ≪≫
        Functor.leftUnitor _) :
      (isTorsionPlus.{u, 0} B X.obj X.property Λ).ι ⋙ derivedLowerShriek.{u, 0} Λ f c ⋙
          derivedInverseImage.{u, 0} Λ g ≅ _) ≪≫
    (Functor.isoWhiskerLeft (isTorsionPlusLift Λ)
      (Functor.isoWhiskerRight (Stacks.EtaleCohomology.derivedLowerShriekBaseChangeIso Λ sq c)
        (moduleSheafEquivEtaleModules.{u, 0} B Λ T).inverse.mapDerivedCategoryPlus) :
      (isTorsionPlusLift Λ ⋙ (Stacks.EtaleCohomology.isTorsionPlus.{u, 0} Λ X.obj).ι ⋙
          Stacks.EtaleCohomology.derivedLowerShriek.{u, 0} f c Λ ⋙
          Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlus.{u, 0} Λ g ⋙
          (moduleSheafEquivEtaleModules.{u, 0} B Λ T).inverse.mapDerivedCategoryPlus) ≅ _) ≪≫
    (Functor.isoWhiskerLeft
      ((isTorsionPlus.{u, 0} B X.obj X.property Λ).ι ⋙
        (moduleSheafEquivEtaleModules.{u, 0} B Λ X).functor.mapDerivedCategoryPlus ⋙
        Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlus.{u, 0} Λ g')
      (Functor.isoWhiskerRight (mapDerivedCategoryPlusInverseCompFunctorIso.{u, 0} Λ Z)
        (Stacks.EtaleCohomology.derivedLowerShriek.{u, 0} f' (c.baseChange sq) Λ ⋙
          (moduleSheafEquivEtaleModules.{u, 0} B Λ T).inverse.mapDerivedCategoryPlus) ≪≫
        Functor.leftUnitor _)).symm

end BaseChange

end AlgebraicGeometry.SmallEtale
