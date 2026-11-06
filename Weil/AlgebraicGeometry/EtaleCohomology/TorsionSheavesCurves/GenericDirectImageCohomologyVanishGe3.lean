module

public import Weil.Attr
public import Weil.AlgebraicGeometry.FunctionField
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NonseparatedCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.IrreducibleOpenSubobject
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering

/-!
# Cohomology of the direct image from the generic point of a curve

Let `k` be an algebraically closed field, `X` an integral curve over `k` with function field `K`,
`η : Spec K ⟶ X` the canonical morphism onto the generic point, and `𝒢` a torsion abelian sheaf
on `(Spec K)_ét`. Then `H^p(X, η_* 𝒢) = 0` for every `p ≥ 3`.

The direct image `η_* 𝒢` is again a torsion sheaf: a section of `η_* 𝒢` over an étale
`X`-scheme `U` is a section of `𝒢` over `U ×_X Spec K`, which is quasi-compact when `U` is,
because `η` is quasi-compact (`X` is noetherian). The statement is then the vanishing of
`H^p(X, ℱ)`, `p ≥ 3`, for every torsion sheaf `ℱ` on a scheme of finite type and dimension at
most one over `k` ([Stacks, Tag 03RT]).

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_smallPushforward_genericPointHom`: `H^p(X, η_* 𝒢) = 0`
  for `p ≥ 3`.
* `AlgebraicGeometry.BigEtaleSite.isTorsionSheaf_smallPushforward`: direct image along a
  quasi-compact morphism preserves torsion sheaves.

## Implementation notes

Sheaves live on the small étale sites `SmallEtale B S hS` of a big étale site `B`, with
coefficients `AddCommGrpCat.{u}`. Freitag and Kiehl deduce the vanishing from the Leray spectral
sequence of `X ⟶ Spec k` and `η`, the bound `cd(K) ≤ 1` and the vanishing of `R^q η_* 𝒢` for
`q ≥ 2` and of `H^p(X, R^1 η_* 𝒢)` for `p > 0`. Here it is instead the case `ℱ = η_* 𝒢` of
Tag 03RT (`Stacks.EtaleCohomology.subsingleton_sheafH_of_three_le`), which is stated on Mathlib's
small étale site at coefficients of the object universe: the cohomology is moved there along
`AlgebraicGeometry.SmallEtale.cohomologyAddEquivOfSmallEtale` and lifted from coefficients
`AddCommGrpCat.{u}` to `AddCommGrpCat.{u + 1}` by
`AlgebraicGeometry.subsingleton_smallEtaleSheafH_ulift_iff`. The curve hypothesis is that the
structure morphism `X ⟶ Spec k` is of finite type and `dim X ≤ 1`; no separatedness is used.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.5
* [Stacks Project, Tag 03RT](https://stacks.math.columbia.edu/tag/03RT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

/-- **Direct image along a quasi-compact morphism preserves torsion sheaves.** A section of
`f_* 𝒢` over an affine open `W` of an étale `S`-scheme is a section of `𝒢` over the
quasi-compact `W ×_S T`, hence is killed by a positive integer, and these opens cover. -/
theorem BigEtaleSite.isTorsionSheaf_smallPushforward (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (f : T ⟶ S) [QuasiCompact (B.inclusion.map f)]
    {G : Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{w}}
    (hG : SmallEtale.IsTorsionSheaf B T.obj T.property G) :
    SmallEtale.IsTorsionSheaf B S.obj S.property
      ((B.smallPushforward f AddCommGrpCat.{w}).obj G) := by
  intro U x
  let F := (B.smallPushforward f AddCommGrpCat.{w}).obj G
  let R : Sieve U :=
    { arrows := fun V g => ∃ n : ℕ, 0 < n ∧ n • (F.obj.map g.op x) = 0
      downward_closed := by
        rintro V W g ⟨n, hn, hx⟩ h
        refine ⟨n, hn, ?_⟩
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul, hx, map_zero] }
  refine ⟨R, ?_, fun V g hg => hg⟩
  refine SmallEtale.mem_topology_of_jointlySurjective fun y => ?_
  obtain ⟨W, hW, hyW⟩ : ∃ W : ((SmallEtale.toScheme B S.obj S.property).obj U).Opens,
      IsAffineOpen W ∧ y ∈ W := by
    obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      ((SmallEtale.toScheme B S.obj S.property).obj U).isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top y)
    exact ⟨W, hW, hyW⟩
  have hWc : B.Contains W.toScheme :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit W.ι U.obj.left.property
  refine ⟨SmallEtale.openObj U W hWc, SmallEtale.openObjHom U W hWc, ?_, ?_⟩
  · have : IsAffine W.toScheme := hW
    have hc : CompactSpace ((SmallEtale.toScheme B T.obj T.property).obj
        ((smallEtaleBaseChange B f).obj (SmallEtale.openObj U W hWc))) := by
      let V := SmallEtale.openObj U W hWc
      have hsq := (IsPullback.of_hasPullback V.obj.hom f).map B.inclusion
      have hq : QuasiCompact (B.inclusion.map (pullback.fst V.obj.hom f)) :=
        MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip ‹_›
      have hV : CompactSpace (B.inclusion.obj V.obj.left) :=
        inferInstanceAs (CompactSpace W.toScheme)
      exact @QuasiCompact.compactSpace_of_compactSpace _ _
        (B.inclusion.map (pullback.fst V.obj.hom f)) hq hV
    obtain ⟨n, hn, hx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero.mp
      (hG.isAddTorsion_of_compactSpace _ (F.obj.map (SmallEtale.openObjHom U W hWc).op x)))
    exact ⟨n, hn, hx⟩
  · exact ⟨⟨y, hyW⟩, rfl⟩

end AlgebraicGeometry

namespace CategoryTheory

/-- Raising the coefficient universe of an abelian sheaf preserves torsion sheaves. -/
theorem torsionSheafProperty_sheafCompose_uliftFunctor {C : Type*} [Category C]
    (J : GrothendieckTopology C) [J.HasSheafCompose AddCommGrpCat.uliftFunctor.{u + 1, u}]
    {F : Sheaf J AddCommGrpCat.{u}} (hF : Stacks.Torsion.torsionSheafProperty J F) :
    Stacks.Torsion.torsionSheafProperty J
      ((sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F) := by
  intro U x
  obtain ⟨R, hR, hk⟩ := hF U x.down
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨n, hn, hx⟩ := hk V g hg
  refine ⟨n, hn, ULift.ext _ _ ?_⟩
  exact hx

end CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {X : AlgebraicGeometry.Scheme.{u}} [IsIntegral X]
  (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π]
  (hdim : topologicalKrullDim X ≤ 1)
  (B : BigEtaleSite.{u}) (hX : B.Contains X) (hK : B.Contains (Spec X.functionField))

variable (X) in
/-- The canonical morphism `η : Spec K ⟶ X` of an integral scheme onto its generic point, as a
morphism of the big étale site `B`. -/
abbrev BigEtaleSite.genericPointHom : B.obj (Spec X.functionField) hK ⟶ B.obj X hX :=
  ObjectProperty.homMk (Stacks.EtaleCohomology.genericPointInclusion X)

include π hdim in
/-- **Freitag–Kiehl I.5.** Let `k` be an algebraically closed field, `X` an integral curve over
`k` with function field `K`, `η : Spec K ⟶ X` the canonical morphism onto the generic point, and
`𝒢` a torsion sheaf on `(Spec K)_ét`. Then `H^p(X, η_* 𝒢) = 0` for every `p ≥ 3`. -/
@[weil "lem_fk105_generic_direct_image_cohomology_vanish_ge_3"]
theorem subsingleton_sheafH_smallPushforward_genericPointHom
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]
    (G : Sheaf (SmallEtale.topology B (Spec X.functionField) hK) AddCommGrpCat.{u})
    (hG : SmallEtale.IsTorsionSheaf B (Spec X.functionField) hK G) (p : ℕ) (hp : 3 ≤ p) :
    Subsingleton (Sheaf.H.{w} ((B.smallPushforward (B.genericPointHom X hX hK)
      AddCommGrpCat.{u}).obj G) p) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsNoetherian X := ⟨⟩
  have hqc : QuasiCompact (B.inclusion.map (B.genericPointHom X hX hK)) :=
    quasiCompact_of_compactSpace (Stacks.EtaleCohomology.genericPointInclusion X)
  set F := (B.smallPushforward (B.genericPointHom X hX hK) AddCommGrpCat.{u}).obj G
  have hF : SmallEtale.IsTorsionSheaf B X hX F :=
    BigEtaleSite.isTorsionSheaf_smallPushforward B (B.genericPointHom X hX hK) hG
  have := SmallEtale.hasExt_sheaf B X hX
  refine @Equiv.subsingleton _ _ (Abelian.Ext.chgUniv.{u} : Sheaf.H.{w} F p ≃ Sheaf.H.{u} F p) ?_
  have : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    haveI : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
    IsGrothendieckAbelian.hasExt _
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u}
  refine @Equiv.subsingleton _ _ (SmallEtale.cohomologyAddEquivOfSmallEtale B X hX F p).toEquiv ?_
  have hFM : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (E.functor.obj F) :=
    Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward _ _ (SmallEtale.toEtaleSite B X hX)
      _ ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso (E.unitIso.app F) hF)
  refine (subsingleton_smallEtaleSheafH_ulift_iff X (E.functor.obj F) p).mp ?_
  have := Stacks.EtaleCohomology.hasExt_sheaf_smallEtale_succ X
  exact Stacks.EtaleCohomology.subsingleton_sheafH_of_three_le.{u + 1, 0} π hdim _
    (torsionSheafProperty_sheafCompose_uliftFunctor _ hFM) p hp

end AlgebraicGeometry
