module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Finite local constancy and inverse image along a purely inseparable morphism

Let `f : Z ⟶ X` be a purely inseparable morphism of schemes (finite, universally injective and
surjective), and let `F` be a sheaf of sets on the small étale site of `X`. Then `F` is finite
locally constant if and only if its inverse image `f^* F` on the small étale site of `Z` is.

More generally this holds for any universal homeomorphism `f`. Base change along a universal
homeomorphism exhibits the small étale site of `X` as a dense subsite of that of `Z` (part (1)
of Stacks, Tag 03SI), so the direct image `f_*`, which is restriction along base change, is an
equivalence of sheaf categories which preserves and reflects finite local constancy; the inverse
image `f^*`, its left adjoint, is then a quasi-inverse, and `F ≅ f_* f^* F`.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_smallEtaleDirectImage_iff`: for a
  universal homeomorphism `f`, a sheaf of sets `G` on the small étale site of `Z` is finite
  locally constant if and only if its direct image `f_* G` is.
* `AlgebraicGeometry.SmallEtale.isEquivalence_smallEtaleDirectImage`: for a universal
  homeomorphism `f`, the direct image `f_*` is an equivalence of sheaf categories.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_smallEtaleInverseImage_iff`: for a
  universal homeomorphism `f`, `F` is finite locally constant iff `f^* F` is.
* `SmallEtale.isFiniteLocallyConstant_iff_smallEtaleInverseImage_of_isPurelyInseparable`
  — the case of a purely inseparable morphism.

## Implementation notes

The source argues with an étale covering of `Z` on which `f^* F` is constant, transports it to
`X` by the equivalence of étale sites of a purely inseparable morphism, and checks constancy on
each member. Here the same input, the isomorphism of the small étale sites of a universal
homeomorphism, is used once on sheaf categories: finite local constancy is invariant under
restriction along a dense subsite inclusion. The dense subsite statement is available for
Mathlib's small étale sites `AlgebraicGeometry.Scheme.Etale`; it is carried to the size-bounded
sites `AlgebraicGeometry.SmallEtale` by the comparison of the two base changes on direct images,
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`, and by the invariance of
finite local constancy under the equivalence of the two presentations,
`AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_iff_toEtaleSite`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X Z : B.Scheme} (f : Z ⟶ X)

/-- Finite local constancy of a sheaf of sets on a site is invariant under isomorphism. -/
theorem isFiniteLocallyConstant_iff_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    [∀ U : C, HasWeakSheafify (J.over U) (Type (u + 1))] {F G : Sheaf J (Type (u + 1))}
    (e : F ≅ G) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J F ↔
      Stacks.ConstantSheaf.IsFiniteLocallyConstant J G :=
  ⟨fun h ↦ Stacks.ConstantSheaf.isFiniteLocallyConstant_congr J e (hF := h),
    fun h ↦ Stacks.ConstantSheaf.isFiniteLocallyConstant_congr J e.symm (hF := h)⟩

/-- **Direct image along a universal homeomorphism detects finite local constancy.** Let
`f : Z ⟶ X` be a universal homeomorphism. A sheaf of sets `G` on the small étale site of `Z` is
finite locally constant if and only if its direct image `f_* G`, `U ↦ G(U ×_X Z)`, is. -/
theorem isFiniteLocallyConstant_smallEtaleDirectImage_iff
    [UniversalHomeomorphism (B.inclusion.map f)]
    (G : Sheaf (topology B Z.obj Z.property) (Type (u + 1))) :
    IsFiniteLocallyConstant B X.obj X.property
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (topology B X.obj X.property) (topology B Z.obj Z.property)).obj G) ↔
      IsFiniteLocallyConstant B Z.obj Z.property G := by
  let EZ := sheafEquiv B Z.obj Z.property (Type (u + 1))
  let G' := EZ.functor.obj G
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsDenseSubsite
      X.obj.smallEtaleTopology Z.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism _
  let e₁ : G ≅ ((toEtaleSite B Z.obj Z.property).sheafPushforwardContinuous (Type (u + 1))
      (topology B Z.obj Z.property) Z.obj.smallEtaleTopology).obj G' := EZ.unitIso.app G
  let e₂ := (toEtaleSitePushforwardBaseChangeIso B f (Type (u + 1))).app G'
  exact (isFiniteLocallyConstant_iff_of_iso
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (topology B X.obj X.property) (topology B Z.obj Z.property)).mapIso e₁)).trans <|
    (isFiniteLocallyConstant_iff_of_iso e₂).symm.trans <|
    (isFiniteLocallyConstant_iff_toEtaleSite B X.obj X.property _).symm.trans <|
    (Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_sheafPushforwardContinuous.{u + 1}
      (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)) G').symm.trans <|
    (isFiniteLocallyConstant_iff_toEtaleSite B Z.obj Z.property G').trans <|
    (isFiniteLocallyConstant_iff_of_iso e₁).symm

/-- **Direct image along a universal homeomorphism is an equivalence.** For a universal
homeomorphism `f : Z ⟶ X`, the direct image `f_*` from sheaves of sets on the small étale site
of `Z` to sheaves of sets on the small étale site of `X` is an equivalence of categories. -/
theorem isEquivalence_smallEtaleDirectImage [UniversalHomeomorphism (B.inclusion.map f)] :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (topology B X.obj X.property) (topology B Z.obj Z.property)).IsEquivalence := by
  let EZ := sheafEquiv B Z.obj Z.property (Type (u + 1))
  let EX := sheafEquiv B X.obj X.property (Type (u + 1))
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsDenseSubsite
      X.obj.smallEtaleTopology Z.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism _
  have : ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous (Type (u + 1))
        X.obj.smallEtaleTopology Z.obj.smallEtaleTopology).IsEquivalence :=
    inferInstance
  have : ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous (Type (u + 1))
      (topology B X.obj X.property) X.obj.smallEtaleTopology).IsEquivalence :=
    inferInstanceAs EX.inverse.IsEquivalence
  let e : (smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (topology B X.obj X.property) (topology B Z.obj Z.property) ≅
      EZ.functor ⋙ (Stacks.EtaleCohomology.smallEtaleBaseChange
          (B.inclusion.map f)).sheafPushforwardContinuous (Type (u + 1))
          X.obj.smallEtaleTopology Z.obj.smallEtaleTopology ⋙
        (toEtaleSite B X.obj X.property).sheafPushforwardContinuous (Type (u + 1))
          (topology B X.obj X.property) X.obj.smallEtaleTopology :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight EZ.unitIso _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EZ.functor
        (toEtaleSitePushforwardBaseChangeIso B f (Type (u + 1))).symm
  exact Functor.isEquivalence_of_iso e.symm

/-- **Finite local constancy and inverse image along a universal homeomorphism.** Let
`f : Z ⟶ X` be a universal homeomorphism and `F` a sheaf of sets on the small étale site of `X`.
Then `F` is finite locally constant if and only if `f^* F` is. -/
theorem isFiniteLocallyConstant_smallEtaleInverseImage_iff
    [UniversalHomeomorphism (B.inclusion.map f)]
    (F : Sheaf (topology B X.obj X.property) (Type (u + 1))) :
    IsFiniteLocallyConstant B Z.obj Z.property ((smallEtaleInverseImage B f (Type (u + 1))).obj F) ↔
      IsFiniteLocallyConstant B X.obj X.property F := by
  have := isEquivalence_smallEtaleDirectImage f
  have adj := smallEtaleInverseImageAdjunction B f (Type (u + 1))
  have := adj.isEquivalence_left_of_isEquivalence_right
  rw [← isFiniteLocallyConstant_smallEtaleDirectImage_iff f]
  exact isFiniteLocallyConstant_iff_of_iso (asIso (adj.unit.app F)).symm

/-- **A sheaf is finite locally constant if and only if its inverse image along a purely
inseparable morphism is.** Let `f : Z ⟶ X` be a purely inseparable morphism (finite,
universally injective and surjective) and `F` a sheaf of sets on the small étale site of `X`.
Then `F` is finite locally constant if and only if `f^* F` is finite locally constant. -/
@[weil "lem_fk104_flc_iff_purely_inseparable_pullback_flc"]
theorem isFiniteLocallyConstant_iff_smallEtaleInverseImage_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (F : Sheaf (topology B X.obj X.property) (Type (u + 1))) :
    IsFiniteLocallyConstant B X.obj X.property F ↔
      IsFiniteLocallyConstant B Z.obj Z.property
        ((smallEtaleInverseImage B f (Type (u + 1))).obj F) := by
  have : IsFinite (B.inclusion.map f) := hf.1
  have : UniversallyInjective (B.inclusion.map f) := hf.2.1
  have : Surjective (B.inclusion.map f) := hf.2.2
  have : UniversalHomeomorphism (B.inclusion.map f) :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact (isFiniteLocallyConstant_smallEtaleInverseImage_iff f F).symm

end AlgebraicGeometry.SmallEtale
