/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import Weil.AlgebraicGeometry.ComplexPoints.FiniteMorphismBranchedCover
public import Weil.AlgebraicGeometry.ComplexPoints.ProjectiveLineCharts
public import Weil.AlgebraicGeometry.Morphisms.EtaleLocusCurve
public import Weil.AlgebraicGeometry.Morphisms.NoetherNormalizationProjective
public import Weil.Topology.Sheaves.Cohomology.BranchedCoverVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic

/-!
# Cohomological dimension of the complex points of a projective curve

Let `C` be a projective scheme of dimension one over `ℂ`, smooth over `ℂ` (not necessarily
connected), or an integral projective curve over `ℂ`. Then the sheaf cohomology of the constant
sheaf `A` on the complex points `C(ℂ)`, with the analytic topology, vanishes in every degree
`n ≥ 3`, for every abelian group `A`.

The proof is topological. Noether normalization gives a finite surjective morphism
`π : C ⟶ ℙ¹_ℂ` over `ℂ`. In characteristic zero, `π` is étale outside a finite set `Z` of
points of `C`: on each connected component of `C` (an integral curve, `C` being smooth), the
étale locus is open and contains the generic point, and a connected component of dimension zero
is a single point. On complex points `π` is then a finite branched cover of the Riemann sphere
`ℙ¹(ℂ)` with finite branch locus, the image of `Z(ℂ)`, and `C(ℂ)` is compact Hausdorff; a
compact Hausdorff finite branched cover of the Riemann sphere has cohomological dimension at
most two.

## Main results

* `AlgebraicGeometry.Scheme.subsingleton_analyticCohomologyConstant_of_isFinite`: if
  `π : C ⟶ ℙ¹_ℂ` is a finite morphism over `ℂ` from a projective scheme, étale outside a finite
  set, then `Hⁿ(C(ℂ), A) = 0` for `n ≥ 3`.
* `AlgebraicGeometry.Scheme.finite_setOf_not_exists_etale_of_smooth`: a finite morphism
  `C ⟶ ℙ¹_ℂ` over `ℂ` from a smooth projective scheme of dimension one is étale outside a finite
  set.
* `AlgebraicGeometry.Scheme.subsingleton_analyticCohomologyConstant_of_smooth_of_isProjective`:
  `Hⁿ(C(ℂ), A) = 0` for `n ≥ 3` and `C` smooth projective of dimension one over `ℂ`.
* `AlgebraicGeometry.IsCurve.subsingleton_analyticCohomologyConstant`: the same for an integral
  projective curve over `ℂ`, smooth or not.

## Implementation notes

Dimension one is `topologicalKrullDim C = 1`, as in projective Noether normalization
(`AlgebraicGeometry.exists_isFinite_surjective_projectiveSpaceOver`). The smooth statement
assumes neither connectedness nor equidimensionality: a connected component of dimension zero
is a point, put into the exceptional set. The cohomology is
`AlgebraicGeometry.Scheme.analyticCohomologyConstant`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
* [Stacks Project, Tag 0C1C](https://stacks.math.columbia.edu/tag/0C1C)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

/-- An irreducible `T₀` space of Krull dimension at most zero has at most one point: every
point is a generic point. -/
theorem subsingleton_of_irreducibleSpace_of_topologicalKrullDim_nonpos {X : Type*}
    [TopologicalSpace X] [IrreducibleSpace X] [T0Space X] (h : topologicalKrullDim X ≤ 0) :
    Subsingleton X := by
  rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMax] at h
  have key : ∀ z : X, IsGenericPoint z Set.univ := fun z => by
    let c : IrreducibleCloseds X :=
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let t : IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have : t ≤ c := h c (show c ≤ t from fun _ _ => trivial)
    exact Set.eq_univ_of_univ_subset this
  exact ⟨fun a b => (key a).eq (key b)⟩

namespace AlgebraicGeometry

private theorem withBot_enat_le_zero_of_le_one_of_ne {x : WithBot ℕ∞} (h : x ≤ 1)
    (h' : x ≠ 1) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe m =>
      have h1 : m ≤ 1 := by exact_mod_cast h
      have h2 : m ≠ 1 := fun e => h' (by simp [e])
      have : m = 0 := by omega
      simp [this]

namespace Scheme

variable {C : Scheme.{0}} (y : C ⟶ Spec (.of ℂ))

/-- **Cohomological dimension of a finite cover of the projective line.** Let `C` be projective
over `ℂ` and `π : C ⟶ ℙ¹_ℂ` a finite morphism over `ℂ`, every point outside a finite set `Z`
having an open neighbourhood on which `π` is étale. Then `Hⁿ(C(ℂ), A) = 0` for every abelian
group `A` and every `n ≥ 3`. -/
theorem subsingleton_analyticCohomologyConstant_of_isFinite (hy : IsProjective y)
    (π : C ⟶ projectiveSpaceOver 1 (Spec (.of ℂ))) [IsFinite π]
    (hπ : π ≫ (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ)) = y) (Z : Set C)
    (hZ : Z.Finite) (hZet : ∀ x ∉ Z, ∃ U : C.Opens, x ∈ U ∧ Etale (U.ι ≫ π))
    (A : AddCommGrpCat.{0}) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (analyticCohomologyConstant y A n) := by
  have := ComplexPoints.compactSpace_of_isProjective hy
  have := ComplexPoints.t2Space_of_isProjective hy
  exact TopCat.SheafCohomology.subsingleton_H_constantSheaf_of_isBranchedCover
    (TopCat.of (ComplexPoints y)) ComplexPoints.projectiveLineCharts
    (ComplexPoints.finite_image_pointsOver π hπ hZ)
    (ComplexPoints.isBranchedCover_map π hπ Z hZet) A hn

/-- **A finite cover of the projective line by a smooth projective curve is étale off finitely
many points.** Let `C` be smooth and projective over `ℂ` of dimension one, not necessarily
connected, and `π : C ⟶ ℙ¹_ℂ` finite over `ℂ`. Then all but finitely many points of `C` have an
open neighbourhood on which `π` is étale. -/
theorem finite_setOf_not_exists_etale_of_smooth [Smooth y] (hy : IsProjective y)
    (hdim : topologicalKrullDim C = 1)
    (π : C ⟶ projectiveSpaceOver 1 (Spec (.of ℂ))) [IsFinite π]
    (hπ : π ≫ (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ)) = y) :
    {x : C | ¬ ∃ U : C.Opens, x ∈ U ∧ Etale (U.ι ≫ π)}.Finite := by
  set Z := {x : C | ¬ ∃ U : C.Opens, x ∈ U ∧ Etale (U.ι ≫ π)}
  have : IsIntegral (projectiveSpaceOver 1 (Spec (.of ℂ))) := isIntegral_projectiveSpace_one ℂ
  have : IsLocallyNoetherian (projectiveSpaceOver 1 (Spec (.of ℂ))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ))
  have : CompactSpace (projectiveSpaceOver 1 (Spec (.of ℂ))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ))
  have : IsNoetherian (projectiveSpaceOver 1 (Spec (.of ℂ))) := {}
  have : QuasiCompact y := hπ ▸ inferInstance
  have : IsSeparated y := hy.isSeparated
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian y
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace y
  have : LocallyConnectedSpace C := IsLocallyNoetherianSpace.locallyConnectedSpace _
    (isLocallyNoetherianSpace_of_isLocallyNoetherian C)
  -- on each connected component the exceptional set is finite
  have hfin : ∀ x : C, (Z ∩ connectedComponent x).Finite := by
    intro x
    have hK := Stacks.Chow.isOpen_connectedComponent_of_smooth y x
    let U : C.Opens := ⟨connectedComponent x, hK⟩
    have : IsIntegral U := Stacks.Chow.isIntegral_connectedComponent_of_smooth y x hK
    have : IsClosedImmersion U.ι :=
      ⟨⟨U.ι.isOpenEmbedding.isEmbedding, by
        rw [U.range_ι]
        exact isClosed_connectedComponent⟩⟩
    have hle : topologicalKrullDim U ≤ 1 :=
      (topologicalKrullDim_subspace_le C (U : Set C)).trans hdim.le
    by_cases h1 : topologicalKrullDim U = 1
    · -- a component of dimension one is an integral curve, finite and dominant over `ℙ¹`
      have : IsCurve ℂ (U.ι ≫ y) := (isCurve_iff ℂ _).2 ⟨{}, h1⟩
      have : IsVariety ℂ (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ)) := {}
      have : Surjective (U.ι ≫ π) :=
        surjective_of_isFinite_of_topologicalKrullDim_eq ℂ (U.ι ≫ y)
          (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ))
          (U.ι ≫ π) (by rw [Category.assoc, hπ]) (d := 1) (by exact_mod_cast h1)
          (by exact_mod_cast topologicalKrullDim_projectiveSpace_one ℂ)
      have : IsDominant (U.ι ≫ π) := ⟨(U.ι ≫ π).surjective.denseRange⟩
      obtain ⟨Z', -, hZ'fin, -, -, hZ'⟩ :=
        IsCurve.exists_finite_setOf_not_etaleAt_of_isFinite (k := ℂ) (U.ι ≫ y)
          (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ)) (U.ι ≫ π)
      refine (hZ'fin.image U.ι.base).subset ?_
      rintro z ⟨hzZ, hzK⟩
      by_contra hz
      apply hzZ
      have hu : (⟨z, hzK⟩ : U) ∉ Z' := fun h => hz ⟨_, h, rfl⟩
      obtain ⟨-, V, -, hzV, hV⟩ := hZ' _ hu
      refine ⟨U.ι ''ᵁ V, ⟨_, hzV, rfl⟩, ?_⟩
      have e : (U.ι ''ᵁ V).ι ≫ π = (U.ι.isoImage V).inv ≫ V.ι ≫ U.ι ≫ π := by
        rw [← Category.assoc V.ι, ← Scheme.Hom.isoImage_hom_ι U.ι V, Category.assoc,
          Iso.inv_hom_id_assoc]
      rw [e]
      infer_instance
    · -- a component of dimension zero is a single point
      have h0 : topologicalKrullDim U ≤ 0 := withBot_enat_le_zero_of_le_one_of_ne hle h1
      have := subsingleton_of_irreducibleSpace_of_topologicalKrullDim_nonpos h0
      exact ((Set.subsingleton_coe _).1 this).finite.subset Set.inter_subset_right
  -- there are finitely many connected components
  refine (Set.finite_iUnion fun c : _root_.ConnectedComponents C =>
    hfin (_root_.ConnectedComponents.surjective_coe c).choose).subset ?_
  intro z hz
  refine Set.mem_iUnion.2 ⟨(z : _root_.ConnectedComponents C), hz, ?_⟩
  rw [_root_.ConnectedComponents.coe_eq_coe.1
    (_root_.ConnectedComponents.surjective_coe (z : _root_.ConnectedComponents C)).choose_spec]
  exact mem_connectedComponent

/-- **Cohomological dimension of a smooth projective curve over `ℂ`.** Let `C` be smooth and
projective over `ℂ` of dimension one, not necessarily connected. Then the cohomology
`Hⁿ(C(ℂ), A)` of the constant sheaf `A` on the complex points vanishes for every abelian group
`A` and every `n ≥ 3`. -/
theorem subsingleton_analyticCohomologyConstant_of_smooth_of_isProjective [Smooth y]
    (hy : IsProjective y) (hdim : topologicalKrullDim C = 1) (A : AddCommGrpCat.{0}) {n : ℕ}
    (hn : 3 ≤ n) : Subsingleton (analyticCohomologyConstant y A n) := by
  obtain ⟨π, hπfin, -, hπ⟩ :=
    exists_isFinite_surjective_projectiveSpaceOver y hy (d := 1) (by exact_mod_cast hdim)
  exact subsingleton_analyticCohomologyConstant_of_isFinite y hy π hπ _
    (finite_setOf_not_exists_etale_of_smooth y hy hdim π hπ) (fun x hx => not_not.1 hx) A hn

end Scheme

/-- **Cohomological dimension of an integral projective curve over `ℂ`.** For a projective
curve `C` over `ℂ` (integral, of dimension one, possibly singular), the cohomology
`Hⁿ(C(ℂ), A)` of the constant sheaf `A` on the complex points vanishes for every abelian group
`A` and every `n ≥ 3`. -/
theorem IsCurve.subsingleton_analyticCohomologyConstant {C : Scheme.{0}}
    (y : C ⟶ Spec (.of ℂ)) [IsCurve ℂ y] (hy : IsProjective y) (A : AddCommGrpCat.{0}) {n : ℕ}
    (hn : 3 ≤ n) : Subsingleton (Scheme.analyticCohomologyConstant y A n) := by
  obtain ⟨π, hπfin, hπsurj, hπ⟩ := exists_isFinite_surjective_projectiveSpaceOver y hy (d := 1)
    (by exact_mod_cast IsCurve.topologicalKrullDim_eq_one (k := ℂ) (f := y))
  have : IsIntegral (projectiveSpaceOver 1 (Spec (.of ℂ))) := isIntegral_projectiveSpace_one ℂ
  have : IsVariety ℂ (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ)) := {}
  obtain ⟨Z, -, hZ, -, -, hZet⟩ := IsCurve.exists_finite_setOf_not_etaleAt_of_isFinite (k := ℂ) y
    (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ)) π
  exact Scheme.subsingleton_analyticCohomologyConstant_of_isFinite y hy π hπ Z hZ
    (fun x hx => by
      obtain ⟨-, U, -, hxU, hU⟩ := hZet x hx
      exact ⟨U, hxU, hU⟩) A hn

end AlgebraicGeometry
