module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import Weil.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import Weil.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Attr

/-!
# Derived direct image along a closed immersion followed by a morphism

Let `i : Z ⟶ X` be a closed immersion and `f : X ⟶ S` a morphism of schemes. The direct image
`i_*` of étale sheaves is exact, because a closed immersion is finite, and it preserves injective
sheaves, because it is right adjoint to the exact inverse image `i^{-1}`. Applied to an
injective resolution `K → J` of a bounded below complex `K` on `Z`, it therefore gives an
injective resolution `i_* K → i_* J`, and

`R f_* (i_* K) = f_* i_* J = (f ∘ i)_* J = R (f ∘ i)_* K`

in the bounded below derived category of `S`, naturally in `K`. Taking cohomology of the
complex `G[0]` attached to a sheaf `G`, one gets `R^v f_* (i_* G) ≅ R^v (f ∘ i)_* G` for all
`v`.

The only property of `i` that is used is that `i_*` is exact, which holds for every integral
morphism; the results are stated in that generality.

## Main results

* `AlgebraicGeometry.mapDerivedCategoryPlusCompEtaleModuleDerivedDirectImageIso`:
  `i_* ⋙ R f_* ≅ R (i ≫ f)_*` on bounded below derived categories of sheaves of `Λ`-modules on
  the small étale sites, for `i` integral.
* `AlgebraicGeometry.etaleModuleDirectImageCompRightDerivedIso`:
  `i_* ⋙ R^v f_* ≅ R^v (i ≫ f)_*` on sheaves of `Λ`-modules.
* `AlgebraicGeometry.BigEtaleSite.mapDerivedCategoryPlusCompRightDerivedFunctorPlusIso` and
  `AlgebraicGeometry.BigEtaleSite.smallPushforwardCompHigherDirectImageIso`: the same two
  statements for abelian sheaves on the small étale sites `AlgebraicGeometry.SmallEtale` of a
  big étale site.

## Implementation notes

The source states the result for a closed embedding `i`; the statements here hold for every
morphism `i` whose underlying morphism of schemes is integral, which includes closed
immersions and finite morphisms.

The first two statements are on Mathlib's small étale sites, where the derived direct image
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImage` lives: in the application the source
has in mind, `X` is a compactification, which need not be an object of a fixed big étale site.
The last two are on the small étale sites of a big étale site, with the higher direct image
`AlgebraicGeometry.BigEtaleSite.higherDirectImage`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section MathlibSite

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) [IsIntegralHom i]

/-- **`R f_* (i_* K) ≅ R (f ∘ i)_* K`, naturally in `K`**, for an integral morphism `i : Z ⟶ X`
(for instance a closed immersion) and a morphism `f : X ⟶ S`: the exact functor `i_*` applied
to a bounded below complex of sheaves of `Λ`-modules on the small étale site of `Z`, followed by
the derived direct image along `f`, is the derived direct image along `i ≫ f`. -/
@[weil "lem_fk108_closed_pushforward_commutes_proper_pushforward"]
def mapDerivedCategoryPlusCompEtaleModuleDerivedDirectImageIso :
    (etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategoryPlus ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ f ≅
      etaleModuleDerivedDirectImage.{u, r} Λ (i ≫ f) :=
  Functor.isoWhiskerRight
      (etaleModuleDirectImage.{u, r} Λ i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
      _ ≪≫
    (etaleModuleDerivedDirectImageComp.{u, r} Λ i f (i ≫ f) rfl).symm

/-- **`R^v f_* (i_* G) ≅ R^v (f ∘ i)_* G`, naturally in `G`**, for an integral morphism
`i : Z ⟶ X` (for instance a closed immersion), a morphism `f : X ⟶ S`, a sheaf `G` of
`Λ`-modules on the small étale site of `Z` and every `v`. -/
@[weil "lem_fk108_closed_pushforward_commutes_proper_pushforward"]
def etaleModuleDirectImageCompRightDerivedIso (v : ℕ) :
    etaleModuleDirectImage.{u, r} Λ i ⋙ (etaleModuleDirectImage.{u, r} Λ f).rightDerived v ≅
      (etaleModuleDirectImage.{u, r} Λ (i ≫ f)).rightDerived v :=
  (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso _ _ v).symm ≪≫
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (etaleModuleDirectImageComp.{u, r} Λ i f (i ≫ f) rfl) v

end MathlibSite

namespace BigEtaleSite

variable {B : BigEtaleSite.{u}} {Z X S : B.Scheme} (i : Z ⟶ X) (f : X ⟶ S)
  [IsIntegralHom (B.inclusion.map i)]

instance preservesFiniteColimits_smallPushforward_of_isIntegralHom :
    PreservesFiniteColimits (B.smallPushforward i AddCommGrpCat.{u + 1}) :=
  ((exactFunctor_iff _).mp (smallPushforward_exact_of_isIntegralHom i)).2

omit [IsIntegralHom (B.inclusion.map i)] in
instance preservesInjectiveObjects_smallPushforward :
    (B.smallPushforward i AddCommGrpCat.{u + 1}).PreservesInjectiveObjects :=
  ⟨fun {J} _ ↦ injective_smallPushforward_obj B i J⟩

/-- Abelian sheaves with values in `AddCommGrpCat.{u + 1}` on the small étale site of an object
of `B` form a Grothendieck abelian category; in particular they have enough injectives. -/
local instance (Y : B.Scheme) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **`R f_* (i_* K) ≅ R (f ∘ i)_* K`, naturally in `K`**, for abelian sheaves on the small
étale sites of a big étale site, a morphism `i : Z ⟶ X` whose underlying morphism of schemes is
integral (for instance a closed immersion) and a morphism `f : X ⟶ S`. -/
@[weil "lem_fk108_closed_pushforward_commutes_proper_pushforward"]
def mapDerivedCategoryPlusCompRightDerivedFunctorPlusIso :
    (B.smallPushforward i AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ⋙
        (B.smallPushforward f AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (B.smallPushforward (i ≫ f) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (B.smallPushforward i AddCommGrpCat.{u + 1})).symm _ ≪≫
    (rightDerivedFunctorPlusCompIsoOfIso _ _ _
      (smallEtaleSheafPushforwardCompIso B Z X S i f AddCommGrpCat.{u + 1})).symm

end Derived

/-- **`R^v f_* (i_* G) ≅ R^v (f ∘ i)_* G`, naturally in `G`**, for abelian sheaves on the small
étale sites of a big étale site, a morphism `i : Z ⟶ X` whose underlying morphism of schemes is
integral (for instance a closed immersion), a morphism `f : X ⟶ S` and every `v`. -/
@[weil "lem_fk108_closed_pushforward_commutes_proper_pushforward"]
def smallPushforwardCompHigherDirectImageIso (v : ℕ) :
    B.smallPushforward i AddCommGrpCat.{u + 1} ⋙ higherDirectImage B f v ≅
      higherDirectImage B (i ≫ f) v :=
  (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso _ _ v).symm ≪≫
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (smallEtaleSheafPushforwardCompIso B Z X S i f AddCommGrpCat.{u + 1}) v

end BigEtaleSite

end AlgebraicGeometry
