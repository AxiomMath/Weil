module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.AffineTransitionLimit
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.AbelianLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFullness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageRealization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleSetsViaPresentation

/-!
# Maps of sheaves of sets out of a constructible sheaf along a projective limit

Let `X = lim X_α` be a projective system of schemes with limit, `α` an index, `F_α` a
constructible sheaf of sets and `G_α` an arbitrary sheaf of sets on the small étale site of
`X_α`; write `F_β, G_β` for their inverse images to `X_β`, `β ≥ α`, and `F, G` for their inverse
images to `X`. Then the canonical map

`colim_{β ≥ α} Hom(F_β, G_β) ⟶ Hom(F, G)`

is bijective. Bijectivity of a map out of a filtered colimit of sets is stated elementwise:
injectivity says that two maps at a stage with equal inverse images on `X` agree at a later
stage, surjectivity that every map on `X` is the inverse image of a map at some stage.

The proof reduces the statement to the case of a constructible target, which is [Stacks, Tag
09YU], clause (1) (`AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleSetSheaf`). On the
Noetherian scheme `X_α` the sheaf `G_α` is the filtered colimit of its constructible subsheaves
(`AlgebraicGeometry.isColimitConstructibleSubsheaves`); inverse image preserves this colimit,
being a left adjoint; and a constructible sheaf of sets on a quasi-compact quasi-separated
scheme is a compact object ([Stacks, Tag 09Z4]). So every map out of `F_α` (or out of `F`) into
`G_α` (or into `G`) factors through one of the constructible subsheaves (or its inverse image),
two such factorizations become equal further along the colimit, and the constructible case
applies.

## Main results

* `AlgebraicGeometry.exists_smallEtaleStageTransition_map_eq_of_isConstructibleSetSheaf`,
  `AlgebraicGeometry.exists_smallEtaleStageProjection_map_eq_of_isConstructibleSetSheaf` —
  injectivity and surjectivity for a directed system of Noetherian schemes with affine
  transition morphisms.
* `IsProjectiveSystemWithLimit.exists_stageTransition_map_eq_of_isConstructibleSetSheaf`
  and
  `IsProjectiveSystemWithLimit.exists_stageProjection_map_eq_of_isConstructibleSetSheaf`
  — the same for a projective system of schemes with limit.

## Implementation notes

The schemes of the system live in a big étale site `B` and sheaves of sets are sheaves of
`Type (u + 1)` on the small étale sites `SmallEtale.topology B X`. The index set is a preorder
`I`, the system a functor `Iᵒᵖ ⥤ B.Scheme`. Inverse images along the system and to the limit are
`AlgebraicGeometry.smallEtaleStageTransition` and `AlgebraicGeometry.smallEtaleStageProjection`,
and a map at the stage `β` is compared with maps on `X` through the canonical identification
`AlgebraicGeometry.smallEtaleStageComparison` of `p_β^* F_β` with `p_α^* F_α`.

The source proves the case of a constructible target by presenting `F_α` as a cokernel of a pair
of representable sheaves and using the description of sections of an inverse image over a
representable object; here that case is [Stacks, Tag 09YU], clause (1). The passage to an
arbitrary target is the source's.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isRightAdjointPushforward_type

section Stages

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- Inverse image of sheaves of sets along a morphism of the big étale site preserves colimits,
being a left adjoint. -/
theorem preservesColimitsOfSize_smallEtaleSheafPullback_type {S T : B.Scheme} (f : T ⟶ S) :
    PreservesColimitsOfSize.{u + 1, u + 1} (smallEtaleSheafPullback B (Type (u + 1)) f) :=
  (smallEtaleSheafAdjunction B (Type (u + 1)) f).leftAdjoint_preservesColimits

/-- **Maps out of a constructible sheaf of sets into an arbitrary sheaf of sets: injectivity of
`colim_j Hom(F_j, G_j) → Hom(F, G)`.** Two maps from a constructible sheaf of sets `F` at a stage
into an arbitrary sheaf of sets `G` at that stage which agree after inverse image to the limit
already agree at some later stage. -/
theorem exists_smallEtaleStageTransition_map_eq_of_isConstructibleSetSheaf
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hnoeth : ∀ p : I, IsNoetherian (Dg.obj (op p)).obj) (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B (Dg.obj (op i)) F) (a b : F ⟶ G)
    (hab : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).map a =
      (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).map b) :
    ∃ (j : I) (h : i ≤ j),
      (smallEtaleStageTransition B (Type (u + 1)) Dg h).map a =
        (smallEtaleStageTransition B (Type (u + 1)) Dg h).map b := by
  have hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj := fun p =>
    have := hnoeth p; inferInstance
  have hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj := fun p =>
    have := hnoeth p; inferInstance
  have : Nonempty I := ⟨i⟩
  have := hnoeth i
  have := hqc i
  have := hqs i
  obtain ⟨hXc, hXq⟩ :=
    compactSpace_quasiSeparatedSpace_cone_pt_of_isLimit B Dg c hX hc haff hqc hqs i
  let Pr := smallEtaleStageProjection B (Type (u + 1)) Dg c hX i
  have := preservesColimitsOfSize_smallEtaleSheafPullback_type B
    (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))
  have := isFiltered_constructibleSubsheaves B (Dg.obj (op i)) G
  let hcol := isColimitConstructibleSubsheaves B (Dg.obj (op i)) G
  have := IsConstructibleSetSheaf.isFinitelyPresentable B (Dg.obj (op i)) F hF
  have := IsConstructibleSetSheaf.isFinitelyPresentable B (B.obj c.pt hX) (Pr.obj F)
    (isConstructibleFiniteSheaf_pullback B _ F hF)
  obtain ⟨k₁, a', ha'⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcol a
  obtain ⟨k₂, b', hb'⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcol b
  have hcolPr := isColimitOfPreserves Pr hcol
  obtain ⟨k, u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hcolPr
    (Pr.map a') (Pr.map b') (by
      simp only [Functor.mapCocone_ι_app, ← Pr.map_comp, ha', hb']
      exact hab)
  obtain ⟨j, h, hj⟩ := smallEtaleStagesFaithful_isConstructibleSetSheaf B Dg c hX hc haff hqc
    hqs i F _ hF (k.2.2) (a' ≫ (Subfunctor.sheafDiagram _ _).map u)
    (b' ≫ (Subfunctor.sheafDiagram _ _).map v) (by
      simp only [Functor.comp_map] at huv
      exact (Pr.map_comp _ _).trans (huv.trans (Pr.map_comp _ _).symm))
  have hka : a = (a' ≫ (Subfunctor.sheafDiagram _ _).map u) ≫
      (Subfunctor.sheafCocone _ _).ι.app k := by
    rw [Category.assoc, (Subfunctor.sheafCocone _ _).w, ha']
  have hkb : b = (b' ≫ (Subfunctor.sheafDiagram _ _).map v) ≫
      (Subfunctor.sheafCocone _ _).ι.app k := by
    rw [Category.assoc, (Subfunctor.sheafCocone _ _).w, hb']
  refine ⟨j, h, ?_⟩
  rw [hka, hkb]
  exact (Functor.map_comp _ _ _).trans
    ((congrArg (· ≫ _) hj).trans (Functor.map_comp _ _ _).symm)

/-- **Maps out of a constructible sheaf of sets into an arbitrary sheaf of sets: surjectivity of
`colim_j Hom(F_j, G_j) → Hom(F, G)`.** Every map between the inverse images to the limit of a
constructible sheaf of sets `F` and an arbitrary sheaf of sets `G` at a stage is the inverse
image of a map at some later stage, read through the canonical comparison. -/
theorem exists_smallEtaleStageProjection_map_eq_of_isConstructibleSetSheaf
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hnoeth : ∀ p : I, IsNoetherian (Dg.obj (op p)).obj) (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B (Dg.obj (op i)) F)
    (a : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G) :
    ∃ (j : I) (h : i ≤ j) (b : (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj F ⟶
        (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G),
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h F).inv ≫
          (smallEtaleStageProjection B (Type (u + 1)) Dg c hX j).map b ≫
          (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom = a := by
  have hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj := fun p =>
    have := hnoeth p; inferInstance
  have hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj := fun p =>
    have := hnoeth p; inferInstance
  have : Nonempty I := ⟨i⟩
  have := hnoeth i
  obtain ⟨hXc, hXq⟩ :=
    compactSpace_quasiSeparatedSpace_cone_pt_of_isLimit B Dg c hX hc haff hqc hqs i
  let Pr := smallEtaleStageProjection B (Type (u + 1)) Dg c hX i
  have := preservesColimitsOfSize_smallEtaleSheafPullback_type B
    (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))
  have := isFiltered_constructibleSubsheaves B (Dg.obj (op i)) G
  let hcol := isColimitConstructibleSubsheaves B (Dg.obj (op i)) G
  have := IsConstructibleSetSheaf.isFinitelyPresentable B (B.obj c.pt hX) (Pr.obj F)
    (isConstructibleFiniteSheaf_pullback B _ F hF)
  obtain ⟨k, a', ha'⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (isColimitOfPreserves Pr hcol) a
  obtain ⟨j, h, b', hb'⟩ := smallEtaleStagesFull_isConstructibleSetSheaf B Dg c hX hc haff hqc
    hqs i F _ hF k.2.2 a'
  refine ⟨j, h, b' ≫ (smallEtaleStageTransition B (Type (u + 1)) Dg h).map
    ((Subfunctor.sheafCocone (constructibleSubsheaves B (Dg.obj (op i)) G)
      (fun _ hG => isSheaf_of_mem_constructibleSubsheaves hG)).ι.app k), ?_⟩
  rw [Functor.map_comp, Category.assoc]
  have hn := smallEtaleStageComparison_hom_naturality B (Type (u + 1)) Dg c hX h (G := G)
    ((Subfunctor.sheafCocone (constructibleSubsheaves B (Dg.obj (op i)) G)
      (fun _ hG => isSheaf_of_mem_constructibleSubsheaves hG)).ι.app k)
  refine (congrArg (fun t => _ ≫ _ ≫ t) hn).trans ?_
  rw [← ha', ← hb']
  exact ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm

end Stages

section ProjectiveSystem

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)
  (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Hom of sheaves of sets out of a constructible sheaf along a projective limit,
injectivity.** Let `X = lim X_α` be a projective system of schemes with limit, `F_α` a
constructible sheaf of sets and `G_α` an arbitrary sheaf of sets on the small étale site of
`X_α`. Two maps `F_α ⟶ G_α` with the same inverse image `p_α^* F_α ⟶ p_α^* G_α` on `X` have the
same inverse image on some `X_β`, `β ≥ α`: the map `colim_{β ≥ α} Hom(F_β, G_β) ⟶ Hom(F, G)` is
injective. -/
@[weil "prop_fk104_hom_from_constructible_colimit"]
theorem IsProjectiveSystemWithLimit.exists_stageTransition_map_eq_of_isConstructibleSetSheaf
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (α : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op α)).obj (Dg.obj (op α)).property)
      (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B (Dg.obj (op α)) F) (a b : F ⟶ G)
    (hab : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX α).map a =
      (smallEtaleStageProjection B (Type (u + 1)) Dg c hX α).map b) :
    ∃ (β : I) (h : α ≤ β),
      (smallEtaleStageTransition B (Type (u + 1)) Dg h).map a =
        (smallEtaleStageTransition B (Type (u + 1)) Dg h).map b := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  exact exists_smallEtaleStageTransition_map_eq_of_isConstructibleSetSheaf B Dg c hX hc
    (fun e => hD.isAffineHom_map e) (fun p => hD.isNoetherian_obj (op p)) α F G hF a b hab

/-- **Hom of sheaves of sets out of a constructible sheaf along a projective limit,
surjectivity.** Let `X = lim X_α` be a projective system of schemes with limit, `F_α` a
constructible sheaf of sets and `G_α` an arbitrary sheaf of sets on the small étale site of
`X_α`. Every map `p_α^* F_α ⟶ p_α^* G_α` on `X` is, through the canonical identifications
`p_β^* F_β ≅ p_α^* F_α`, the inverse image of a map `F_β ⟶ G_β` for some `β ≥ α`: the map
`colim_{β ≥ α} Hom(F_β, G_β) ⟶ Hom(F, G)` is surjective. -/
@[weil "prop_fk104_hom_from_constructible_colimit"]
theorem IsProjectiveSystemWithLimit.exists_stageProjection_map_eq_of_isConstructibleSetSheaf
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (α : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op α)).obj (Dg.obj (op α)).property)
      (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B (Dg.obj (op α)) F)
    (a : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX α).obj F ⟶
      (smallEtaleStageProjection B (Type (u + 1)) Dg c hX α).obj G) :
    ∃ (β : I) (h : α ≤ β) (b : (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj F ⟶
        (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G),
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h F).inv ≫
          (smallEtaleStageProjection B (Type (u + 1)) Dg c hX β).map b ≫
          (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom = a := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  exact exists_smallEtaleStageProjection_map_eq_of_isConstructibleSetSheaf B Dg c hX hc
    (fun e => hD.isAffineHom_map e) (fun p => hD.isNoetherian_obj (op p)) α F G hF a

end ProjectiveSystem

end AlgebraicGeometry
