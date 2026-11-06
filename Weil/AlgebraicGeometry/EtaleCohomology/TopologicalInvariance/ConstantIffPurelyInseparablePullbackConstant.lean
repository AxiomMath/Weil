/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import Weil.Attr

/-!
# Constant sheaves and inverse image along a purely inseparable morphism

Let `f : T ⟶ S` be a morphism of schemes. The inverse image `f^*` of sheaves on the small étale
sites carries the constant sheaf `M_S` to the constant sheaf `M_T`. When `f` is (finite and)
purely inseparable, `f` is a universal homeomorphism, so by topological invariance of the étale
site the inverse image `f^*` is an equivalence of the categories of sheaves. Consequently a sheaf
`F` on the small étale site of `S` is constant if and only if `f^* F` is constant.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsPurelyInseparable.universalHomeomorphism`: a purely
  inseparable morphism is a universal homeomorphism.
* `AlgebraicGeometry.isConstant_smallEtaleInverseImage_obj`: the inverse image of a constant
  sheaf is constant.
* `AlgebraicGeometry.isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism`: inverse
  image along a universal homeomorphism is an equivalence of sheaf categories.
* `AlgebraicGeometry.isConstant_iff_isConstant_smallEtaleInverseImage`: for `f` purely
  inseparable, a sheaf `F` is constant if and only if `f^* F` is constant, for sheaves with
  values in any category with enough limits and colimits;
  `AlgebraicGeometry.isConstant_iff_isConstant_smallEtaleInverseImage_type` is the case of
  sheaves of sets.

## Implementation notes

The source proves the converse direction by showing `f_* M_T ≅ M_S` and that the unit
`F ⟶ f_* f^* F` is an isomorphism. Here both facts are subsumed by the statement that `f^*` is
an equivalence: it is left adjoint to the direct image `f_*`, and `f_*` is an equivalence because
it is conjugate, through the equivalence between sheaves on the size-bounded small étale site
and on all étale schemes, to the direct image along the base change functor of small étale
sites, which exhibits a dense subsite for a universal homeomorphism (Stacks Project, Tag 03SI).
A sheaf `F` with `f^* F ≅ M_T ≅ f^* M_S` is then isomorphic to `M_S`, `f^*` being fully
faithful.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-- A (finite) purely inseparable morphism of schemes is a universal homeomorphism: it is
integral, universally injective and surjective (Stacks Project, Tag 04DF). -/
theorem Scheme.Hom.IsPurelyInseparable.universalHomeomorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : f.IsPurelyInseparable) : UniversalHomeomorphism f := by
  have := hf.isFinite
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mpr
    ⟨inferInstance, hf.universallyInjective, hf.surjective⟩

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

section Constant

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **The inverse image of a constant sheaf is constant.** For a morphism `f : T ⟶ S`, the
inverse image `f^* M_S` of the constant sheaf on an object `M` is the constant sheaf `M_T`,
naturally in `M`. -/
private def constantSheafCompSmallEtaleInverseImageIsoAux :
    constantSheaf (SmallEtale.topology B S.obj S.property) A ⋙ smallEtaleInverseImage B f A ≅
      constantSheaf (SmallEtale.topology B T.obj T.property) A :=
  Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso (smallEtaleBaseChange B f) _ _ A
    terminalIsTerminal (terminalIsTerminal.isTerminalObj (smallEtaleBaseChange B f) _)
    (Iso.refl _)

/-- The inverse image of a constant sheaf is constant. -/
theorem isConstant_smallEtaleInverseImage_obj
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    [F.IsConstant (SmallEtale.topology B S.obj S.property)] :
    ((smallEtaleInverseImage B f A).obj F).IsConstant (SmallEtale.topology B T.obj T.property) := by
  obtain ⟨M, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant _ F
  exact Sheaf.isConstant_of_iso _
    ((smallEtaleInverseImage B f A).mapIso e.symm ≪≫
      (constantSheafCompSmallEtaleInverseImageIsoAux B f A).app M)

end Constant

section Equivalence

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasLimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **Topological invariance of the étale topos.** If `f : T ⟶ S` is a universal
homeomorphism, the inverse image `f^*` from sheaves on the small étale site of `S` to sheaves on
the small étale site of `T` is an equivalence of categories. -/
theorem isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism
    [UniversalHomeomorphism (B.inclusion.map f)] :
    (smallEtaleInverseImage B f A).IsEquivalence := by
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsDenseSubsite
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism (B.inclusion.map f)
  have : ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous
      A S.obj.smallEtaleTopology T.obj.smallEtaleTopology).IsEquivalence := inferInstance
  have : HasLimitsOfSize.{u, u} A := hasLimitsOfSizeShrink.{u, u, u, u + 1} A
  have : ((SmallEtale.toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology).IsEquivalence :=
    (SmallEtale.sheafEquiv B S.obj S.property A).isEquivalence_inverse
  have : ((SmallEtale.toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
      (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology).IsEquivalence :=
    (SmallEtale.sheafEquiv B T.obj T.property A).isEquivalence_inverse
  have := Functor.isEquivalence_of_iso (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f A)
  have := Functor.isEquivalence_of_comp_left
    ((SmallEtale.toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
      (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology)
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property))
  exact (smallEtaleInverseImageAdjunction B f A).isEquivalence_left_of_isEquivalence_right

variable [HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **A sheaf is constant if and only if its inverse image along a purely inseparable morphism
is constant.** Let `f : T ⟶ S` be a purely inseparable morphism and `F` a sheaf on the small
étale site of `S`. Then `F` is constant if and only if `f^* F` is constant. -/
@[weil "lem_fk104_constant_iff_purely_inseparable_pullback_constant"]
theorem isConstant_iff_isConstant_smallEtaleInverseImage
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    F.IsConstant (SmallEtale.topology B S.obj S.property) ↔
      ((smallEtaleInverseImage B f A).obj F).IsConstant
        (SmallEtale.topology B T.obj T.property) := by
  refine ⟨fun _ ↦ isConstant_smallEtaleInverseImage_obj B f A F, fun h ↦ ?_⟩
  have := hf.universalHomeomorphism
  have := isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism B f A
  obtain ⟨M, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant _ ((smallEtaleInverseImage B f A).obj F)
  exact Sheaf.isConstant_of_iso _ ((smallEtaleInverseImage B f A).preimageIso
    (e.symm ≪≫ ((constantSheafCompSmallEtaleInverseImageIsoAux B f A).app M).symm))

end Equivalence

/-- **A sheaf of sets is constant if and only if its inverse image along a purely inseparable
morphism is constant.** The case of sheaves of sets of
`AlgebraicGeometry.isConstant_iff_isConstant_smallEtaleInverseImage`. -/
@[weil "lem_fk104_constant_iff_purely_inseparable_pullback_constant"]
theorem isConstant_iff_isConstant_smallEtaleInverseImage_type
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    F.IsConstant (SmallEtale.topology B S.obj S.property) ↔
      ((smallEtaleInverseImage B f (Type (u + 1))).obj F).IsConstant
        (SmallEtale.topology B T.obj T.property) :=
  isConstant_iff_isConstant_smallEtaleInverseImage B f _ hf F

end AlgebraicGeometry

end
