/-
Copyright (c) 2026 Weil project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import WeilFrontier.CategoryTheory.Sites.Pullback

/-!
# Inverse and direct image along a universal homeomorphism are inverse equivalences

Let `f : T ⟶ S` be a universal homeomorphism of schemes, for instance a purely inseparable
morphism (finite, universally injective and surjective). Then for sheaves on the small étale
sites with values in any category `A` with enough limits and colimits, in particular for sheaves
of abelian groups, the unit `G ⟶ f_* f^* G` and the counit `f^* f_* F ⟶ F` of the adjunction
`f^* ⊣ f_*` are isomorphisms: `f^*` and `f_*` are mutually quasi-inverse equivalences.

Base change along a universal homeomorphism exhibits the small étale site of `S` as a dense
subsite of that of `T`, so the direct image `f_*`, which is restriction along base change, is an
equivalence of sheaf categories. A right adjoint which is an equivalence has invertible unit and
counit.

## Main results

* `AlgebraicGeometry.SmallEtale.isEquivalence_smallPushforward_of_universalHomeomorphism`: for a
  universal homeomorphism `f`, the direct image `f_*` is an equivalence.
* `AlgebraicGeometry.SmallEtale.isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable`:
  for a purely inseparable `f`, the unit `G ⟶ f_* f^* G` is an isomorphism.
* `SmallEtale.isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable`:
  for a purely inseparable `f`, the counit `f^* f_* F ⟶ F` is an isomorphism.
* `AlgebraicGeometry.SmallEtale.smallEtaleInverseImageEquivOfIsPurelyInseparable`: the
  equivalence `f^*` with quasi-inverse `f_*`.

## Implementation notes

The source deduces the abelian statement from the statement for sheaves of sets by transporting
the group structure along the equivalence. Here the dense subsite argument applies verbatim to
any coefficient category, so the abelian case (`A = AddCommGrpCat.{u + 1}`) is a special case of
the general statement and no transport of structure is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} (f : T ⟶ S)
variable (A : Type w) [Category.{v} A] [HasLimitsOfSize.{u, u + 1} A]

/-- **Direct image along a universal homeomorphism is an equivalence.** For a universal
homeomorphism `f : T ⟶ S`, the direct image `f_*`, `F ↦ (U ↦ F(T ×_S U))`, from sheaves on the
small étale site of `T` to sheaves on the small étale site of `S` with values in `A`, is an
equivalence of categories. -/
theorem isEquivalence_smallPushforward_of_universalHomeomorphism
    [UniversalHomeomorphism (B.inclusion.map f)] :
    (B.smallPushforward f A).IsEquivalence := by
  have : HasLimitsOfSize.{u, u} A := hasLimitsOfSizeShrink.{u, u, u, u + 1} A
  let ET := sheafEquiv B T.obj T.property A
  let ES := sheafEquiv B S.obj S.property A
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsDenseSubsite
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism _
  have : ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous A
        S.obj.smallEtaleTopology T.obj.smallEtaleTopology).IsEquivalence :=
    inferInstance
  have : ((toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
      (topology B S.obj S.property) S.obj.smallEtaleTopology).IsEquivalence :=
    inferInstanceAs ES.inverse.IsEquivalence
  let e : (smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (topology B S.obj S.property) (topology B T.obj T.property) ≅
      ET.functor ⋙ (Stacks.EtaleCohomology.smallEtaleBaseChange
          (B.inclusion.map f)).sheafPushforwardContinuous A
          S.obj.smallEtaleTopology T.obj.smallEtaleTopology ⋙
        (toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
          (topology B S.obj S.property) S.obj.smallEtaleTopology :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight ET.unitIso _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ET.functor (toEtaleSitePushforwardBaseChangeIso B f A).symm
  exact Functor.isEquivalence_of_iso e.symm

/-- A purely inseparable morphism of schemes is a universal homeomorphism. -/
theorem universalHomeomorphism_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable) :
    UniversalHomeomorphism (B.inclusion.map f) := by
  have : IsFinite (B.inclusion.map f) := hf.1
  have : UniversallyInjective (B.inclusion.map f) := hf.2.1
  have : Surjective (B.inclusion.map f) := hf.2.2
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

variable [HasColimitsOfSize.{u, u + 1} A] [HasWeakSheafify (topology B T.obj T.property) A]

/-- **The unit of `f^* ⊣ f_*` is an isomorphism for a purely inseparable morphism.** Let
`f : T ⟶ S` be purely inseparable. For every sheaf `G` on the small étale site of `S` with values
in `A` (for instance an abelian sheaf, `A = AddCommGrpCat.{u + 1}`), the adjunction map
`G ⟶ f_* f^* G` is an isomorphism. -/
@[weil "lem_fk103_purely_inseparable_abelian_sheaves_equivalence"]
theorem isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (G : Sheaf (topology B S.obj S.property) A) :
    IsIso ((smallEtaleInverseImageUnit B f A).app G) := by
  have := universalHomeomorphism_of_isPurelyInseparable f hf
  have := isEquivalence_smallPushforward_of_universalHomeomorphism f A
  have := (smallEtaleInverseImageAdjunction B f A).isEquivalence_left_of_isEquivalence_right
  infer_instance

/-- **The counit of `f^* ⊣ f_*` is an isomorphism for a purely inseparable morphism.** Let
`f : T ⟶ S` be purely inseparable. For every sheaf `F` on the small étale site of `T` with values
in `A` (for instance an abelian sheaf, `A = AddCommGrpCat.{u + 1}`), the adjunction map
`f^* f_* F ⟶ F` is an isomorphism. -/
@[weil "lem_fk103_purely_inseparable_abelian_sheaves_equivalence"]
theorem isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (F : Sheaf (topology B T.obj T.property) A) :
    IsIso ((smallEtaleInverseImageAdjunction B f A).counit.app F) := by
  have := universalHomeomorphism_of_isPurelyInseparable f hf
  have := isEquivalence_smallPushforward_of_universalHomeomorphism f A
  have := (smallEtaleInverseImageAdjunction B f A).isEquivalence_left_of_isEquivalence_right
  infer_instance

/-- **`f^*` and `f_*` are mutually quasi-inverse equivalences** for a purely inseparable
morphism `f : T ⟶ S`: the equivalence of sheaf categories whose functor is the inverse image
`f^*`, whose inverse is the direct image `f_*`, and whose unit and counit are those of the
adjunction `f^* ⊣ f_*`. -/
@[weil "lem_fk103_purely_inseparable_abelian_sheaves_equivalence"]
def smallEtaleInverseImageEquivOfIsPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable) :
    Sheaf (topology B S.obj S.property) A ≌ Sheaf (topology B T.obj T.property) A :=
  have := fun G ↦ isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable f A hf G
  have := fun F ↦
    isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable f A hf F
  (smallEtaleInverseImageAdjunction B f A).toEquivalence

@[simp]
lemma smallEtaleInverseImageEquivOfIsPurelyInseparable_functor
    (hf : (B.inclusion.map f).IsPurelyInseparable) :
    (smallEtaleInverseImageEquivOfIsPurelyInseparable f A hf).functor =
      smallEtaleInverseImage B f A :=
  rfl

@[simp]
lemma smallEtaleInverseImageEquivOfIsPurelyInseparable_inverse
    (hf : (B.inclusion.map f).IsPurelyInseparable) :
    (smallEtaleInverseImageEquivOfIsPurelyInseparable f A hf).inverse =
      B.smallPushforward f A :=
  rfl

end AlgebraicGeometry.SmallEtale

end
