module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import Weil.Attr

/-!
# The derived direct image preserves torsion

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. The total right
derived functor `R f_* : D⁺(X_ét) ⥤ D⁺(Y_ét)` of the direct image of abelian sheaves carries the
full subcategory `D_{+,tor}(X)` of complexes with torsion cohomology sheaves into `D_{+,tor}(Y)`.

The torsion sheaves form a weak Serre class, so by the spectral sequence of a Cartan–Eilenberg
resolution it suffices that every higher direct image `R^q f_* F` of a torsion sheaf `F` is a
torsion sheaf ([Stacks, Tag 0DDD] (1)).

## Main results

* `AlgebraicGeometry.BigEtaleSite.torsionSheafProperty_higherDirectImage`: the higher direct
  images of a torsion sheaf are torsion sheaves.
* `AlgebraicGeometry.BigEtaleSite.torsionPlusCohomologyProperty_rightDerivedFunctorPlus_obj`:
  `R f_*` carries `D_{+,tor}(X)` into `D_{+,tor}(Y)`.
* `AlgebraicGeometry.BigEtaleSite.torsionPlusDerivedDirectImage`: the induced functor
  `D_{+,tor}(X) ⥤ D_{+,tor}(Y)`.

## Implementation notes

The schemes are those of a big étale site `B` and the sites are the size-bounded small étale
sites `AlgebraicGeometry.SmallEtale`, with coefficients `AddCommGrpCat.{u}` in the universe of the
schemes, as in `AlgebraicGeometry.SmallEtale.TorsionPlusDerivedCategory`. The torsion of higher
direct images is known with coefficients `AddCommGrpCat.{u + 1}`
(`AlgebraicGeometry.SmallEtale.torsionSheafProperty_rightDerived_smallPushforward`); it is brought
down along the universe lift of abelian sheaves, which commutes with higher direct images and
detects torsion.

The source states the result for an arbitrary morphism under its standing assumption that all
schemes are noetherian; only quasi-compactness and quasi-separatedness of `f` are used, and both
hold for a morphism whose source is noetherian.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe s t v u

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The universe lift detects torsion sheaves**: an abelian sheaf is a torsion sheaf if and
only if its universe lift is. -/
theorem torsionSheafProperty_uliftSheafFunctor_obj_iff (F : Sheaf J AddCommGrpCat.{t}) :
    Stacks.Torsion.torsionSheafProperty J ((uliftSheafFunctor.{s, t} J).obj F) ↔
      Stacks.Torsion.torsionSheafProperty J F := by
  refine forall_congr' fun U ↦ ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨R, hR, hx⟩ := h (ULift.up x)
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨n, hn, hnx⟩ := hx V f hf
    exact ⟨n, hn, congrArg ULift.down hnx⟩
  · obtain ⟨R, hR, hx⟩ := h x.down
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨n, hn, hnx⟩ := hx V f hf
    exact ⟨n, hn, congrArg ULift.up hnx⟩

end Stacks.Sheaves.UniverseLift

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)

/-- **Higher direct images of torsion sheaves are torsion** ([Stacks, Tag 0DDD] (1)). For a
quasi-compact and quasi-separated morphism `f : X ⟶ Y` of a big étale site and a torsion abelian
sheaf `F` on the small étale site of `X`, every `R^q f_* F` is a torsion sheaf on the small étale
site of `Y`. -/
theorem torsionSheafProperty_higherDirectImage
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] (q : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u})
    (hF : SmallEtale.IsTorsionSheaf B X.obj X.property F) :
    SmallEtale.IsTorsionSheaf B Y.obj Y.property ((higherDirectImage B f q).obj F) := by
  have := smallEtaleSheaf_isGrothendieckAbelian B X
  have := smallEtaleSheaf_hasInjectiveResolutions (B := B) (S := X.obj) (hS := X.property)
  have : HasSeparator (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasSeparator.{u}
  have : (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
      (SmallEtale.topology B X.obj X.property)).PreservesInjectiveObjects :=
    Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1,
      u + 1, u} _
  let e := (Stacks.Sheaves.UniverseLift.rightDerivedSheafPushforwardContinuousULiftIso.{u + 1, u}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (smallEtaleBaseChange B f) q).app F
  rw [SmallEtale.IsTorsionSheaf,
    ← Stacks.Sheaves.UniverseLift.torsionSheafProperty_uliftSheafFunctor_obj_iff.{u + 1}]
  refine (Stacks.Torsion.torsionSheafProperty _).prop_of_iso e.symm ?_
  exact SmallEtale.torsionSheafProperty_rightDerived_smallPushforward f q _
    ((Stacks.Sheaves.UniverseLift.torsionSheafProperty_uliftSheafFunctor_obj_iff.{u + 1} _ F).2 hF)

attribute [local instance] HasDerivedCategory.standard

/-- **The derived direct image preserves torsion** (FK I.8). For a quasi-compact and
quasi-separated morphism `f : X ⟶ Y` of a big étale site (for instance any morphism with
noetherian source) and a complex `K` of `D⁺(X_ét)` lying in `D_{+,tor}(X)`, the derived direct
image `R f_* K` lies in `D_{+,tor}(Y)`. -/
@[weil "lem_fk108_derived_direct_image_preserves_torsion"]
theorem torsionPlusCohomologyProperty_rightDerivedFunctorPlus_obj
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)]
    (K : DerivedCategory.Plus (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u}))
    (hK : Stacks.Torsion.torsionPlusCohomologyProperty (SmallEtale.topology B X.obj X.property)
      K.obj) :
    Stacks.Torsion.torsionPlusCohomologyProperty (SmallEtale.topology B Y.obj Y.property)
      ((B.smallPushforward f AddCommGrpCat.{u}).rightDerivedFunctorPlus.obj K).obj := by
  refine ⟨?_, ((B.smallPushforward f AddCommGrpCat.{u}).rightDerivedFunctorPlus.obj K).property⟩
  exact ((B.smallPushforward f AddCommGrpCat.{u}).derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    (SmallEtale.IsTorsionSheaf B X.obj X.property) (SmallEtale.IsTorsionSheaf B Y.obj Y.property)
    (fun M hM q ↦ torsionSheafProperty_higherDirectImage f q M hM) K (fun q ↦ hK.1 q)).2

/-- The derived direct image `R f_* : D_{+,tor}(X) ⥤ D_{+,tor}(Y)` for a quasi-compact and
quasi-separated morphism `f` of a big étale site. -/
def torsionPlusDerivedDirectImage
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] :
    SmallEtale.TorsionPlusDerivedCategory B X.obj X.property ⥤
      SmallEtale.TorsionPlusDerivedCategory B Y.obj Y.property :=
  ObjectProperty.lift _
    (Stacks.Torsion.TorsionPlusDerivedCategory.ιPlus (SmallEtale.topology B X.obj X.property) ⋙
      (B.smallPushforward f AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (fun K ↦ torsionPlusCohomologyProperty_rightDerivedFunctorPlus_obj f
      ((Stacks.Torsion.TorsionPlusDerivedCategory.ιPlus _).obj K) K.property)

end AlgebraicGeometry.BigEtaleSite
