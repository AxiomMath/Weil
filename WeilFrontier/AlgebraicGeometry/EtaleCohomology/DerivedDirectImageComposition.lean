module

public import WeilFrontier.Algebra.Homology.DerivedCategory.DerivedComposite
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import WeilFrontier.AlgebraicGeometry.Topologies.BigEtale.DirectImageLeftExact
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.AbelianSheaves
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import Weil.Attr

/-!
# The derived direct image of a composite

Let `B` be a big étale site and `f : X ⟶ Y`, `g : Y ⟶ Z` morphisms of it. For a bounded below
complex `𝓕^•` of abelian sheaves on the small étale site of `X`,
`Rg_*(Rf_* 𝓕^•) ≅ R(g ∘ f)_* 𝓕^•` in the derived category of abelian sheaves on `Z`.

Indeed `Rf_* 𝓕^• = f_*(I(𝓕^•))` is bounded below, so `Rg_*` applies to it. For an injective
sheaf `M` on `X`, the sheaf `f_* M` is injective, hence acyclic for `g_*`; so the derived functor
of the composite `g_* ∘ f_*` is the composite of the derived functors. Finally
`g_* ∘ f_* ≅ (g ∘ f)_*`, and isomorphic functors have isomorphic derived functors.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorMapIso`: isomorphic additive
  functors have isomorphic derived functors, for a fixed choice of injective resolutions.

## Main results

* `AlgebraicGeometry.BigEtaleSite.rightDerivedFunctorSmallPushforwardCompIso`: the isomorphism
  `R(g ∘ f)_* ≅ Rg_* ∘ Rf_*` for derived functors defined by choices of injective resolutions,
  on bounded below complexes, with values in `D(Sh(Z_ét, Ab))`.
* `AlgebraicGeometry.BigEtaleSite.rightDerivedFunctorPlusSmallPushforwardCompIso`: the same for
  Mathlib's choice-free total right derived functors `Functor.rightDerivedFunctorPlus` on the
  bounded below derived categories.
* `AlgebraicGeometry.BigEtaleSite.rightAcyclic_smallPushforward_obj_of_injective`: the direct
  image of an injective sheaf is acyclic for every direct image.

## Implementation notes

The sites are the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of `B`, with
coefficients `AddCommGrpCat.{u + 1}` for the universe `u` of the schemes of `B`; the direct image
is `AlgebraicGeometry.BigEtaleSite.smallPushforward`. In the presentation by injective
resolutions, `Rf_*` takes values in bounded below complexes
(`CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorPlusComplexes`), so the composite
`Rg_* ∘ Rf_*` makes sense on the nose. The choice-free form is
`Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso` applied to the underived composition
isomorphism `AlgebraicGeometry.smallEtaleSheafPushforwardCompIso`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.2
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace CochainComplex.InjectiveResolutionFunctor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)

/-- The derived functors of isomorphic functors for the same choice of injective resolutions
are isomorphic. -/
def rightDerivedFunctorMapIso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) :
    ρ.rightDerivedFunctor F ≅ ρ.rightDerivedFunctor G :=
  Functor.isoWhiskerLeft ρ.functor (Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
    DerivedCategory.Qh)

end CochainComplex.InjectiveResolutionFunctor

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u})

/-- Abelian sheaves on the small étale site of a scheme of `B`, with coefficients in
`AddCommGrpCat.{u + 1}`, have enough injectives. -/
instance enoughInjectives_sheaf_addCommGrpCat_succ (X : B.Scheme) :
    EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) where
  presentation F := by
    obtain ⟨I, i, hI, hi⟩ := SmallEtale.exists_mono_injective_sheaf B X.obj X.property F
    exact ⟨{ J := I, f := i, injective := hI, mono := hi }⟩

variable {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The direct image of abelian sheaves preserves injective objects. -/
instance preservesInjectiveObjects_smallPushforward_succ :
    (B.smallPushforward f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects where
  injective_obj {J} _ := injective_smallPushforward_obj B f J

variable [HasDerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})] in
/-- The direct image `f_* M` of an injective abelian sheaf `M` is acyclic for `g_*`: it is
injective. -/
theorem rightAcyclic_smallPushforward_obj_of_injective
    (M : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (hM : Injective M) :
    (B.smallPushforward g AddCommGrpCat.{u + 1}).rightAcyclic
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj M) :=
  have := injective_smallPushforward_obj B f M
  Functor.rightAcyclic_of_injective _ _

/-- **The derived direct image of a composite.** For choices of injective resolutions on the
bounded below derived categories of abelian sheaves on `X` and on `Y`, the derived functors of
the direct images satisfy `R(g ∘ f)_* 𝓕^• ≅ Rg_*(Rf_* 𝓕^•)` in `D(Sh(Z_ét, Ab))`, naturally in
the bounded below complex `𝓕^•`. -/
@[weil "thm_fk102_derived_direct_image_comp"]
def rightDerivedFunctorSmallPushforwardCompIso
    {cX : CochainComplex.ChoiceOfInjectiveResolutions
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})}
    (ρX : CochainComplex.InjectiveResolutionFunctor cX)
    {cY : CochainComplex.ChoiceOfInjectiveResolutions
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})}
    (ρY : CochainComplex.InjectiveResolutionFunctor cY) :
    ρX.rightDerivedFunctor (B.smallPushforward (f ≫ g) AddCommGrpCat.{u + 1}) ≅
      ρX.rightDerivedFunctorPlusComplexes (B.smallPushforward f AddCommGrpCat.{u + 1}) ⋙
        ρY.rightDerivedFunctor (B.smallPushforward g AddCommGrpCat.{u + 1}) :=
  ρX.rightDerivedFunctorMapIso (smallEtaleSheafPushforwardCompIso B X Y Z f g _).symm ≪≫
    ρX.rightDerivedFunctorCompIso ρY _ _ (rightAcyclic_smallPushforward_obj_of_injective B f g)

/-- **The derived direct image of a composite**, for Mathlib's total right derived functors on
the bounded below derived categories: `R(g ∘ f)_* ≅ Rg_* ∘ Rf_*`. -/
@[weil "thm_fk102_derived_direct_image_comp"]
def rightDerivedFunctorPlusSmallPushforwardCompIso :
    (B.smallPushforward (f ≫ g) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (B.smallPushforward f AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⋙
        (B.smallPushforward g AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso _ _ _
    (smallEtaleSheafPushforwardCompIso B X Y Z f g _)

end AlgebraicGeometry.BigEtaleSite
