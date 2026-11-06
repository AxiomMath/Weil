module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.AbelianLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageRealization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelianViaShriekPresentation

/-!
# Maps of abelian sheaves out of a constructible sheaf along a projective limit

Let `X = lim X_α` be a projective system of schemes with limit, `α` an index, `F_α` a
constructible abelian sheaf and `G_α` an arbitrary abelian sheaf on the small étale site of
`X_α`; write `F_β, G_β` for their inverse images to `X_β`, `β ≥ α`, and `F, G` for their inverse
images to `X`. Then the canonical map

`colim_{β ≥ α} Hom(F_β, G_β) ⟶ Hom(F, G)`

is bijective. Bijectivity of a map out of a filtered colimit of sets is stated elementwise:
injectivity says that two maps at a stage with equal inverse images on `X` agree at a later
stage, surjectivity that every map on `X` is the inverse image of a map at some stage.

The proof reduces the statement to the case of a constructible target, which is [Stacks, Tag
09YU], clause (2)
(`AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleAbelianSheaf_unconditional`).
A constructible abelian sheaf `F_α` on a quasi-compact quasi-separated scheme is killed by some
`n > 0`, so every map out of `F_α` or out of `F` lands in the `n`-torsion: in the kernel `K` of
multiplication by `n` on `G_α`, respectively in its inverse image, inverse image being additive
and left exact. The torsion sheaf `K` is a filtered colimit of constructible abelian sheaves
([Stacks, Tag 03SA]), inverse image preserves that colimit, and a constructible abelian sheaf on a
quasi-compact quasi-separated scheme is a compact object ([Stacks, Tag 09Z4]). So every map into
`G_α` (or into `G`) out of `F_α` (or out of `F`) factors through one of the constructible sheaves
of the colimit (or its inverse image), and the constructible case applies.

## Main results

* `AlgebraicGeometry.exists_smallEtaleStageTransition_map_eq_of_isConstructibleAbelianSheaf`,
  `AlgebraicGeometry.exists_smallEtaleStageProjection_map_eq_of_isConstructibleAbelianSheaf` —
  injectivity and surjectivity for a directed system of quasi-compact quasi-separated schemes
  with affine transition morphisms.
* `AlgebraicGeometry.IsProjectiveSystemWithLimit.exists_stageTransition_map_eq_of_isConstructible`,
  `AlgebraicGeometry.IsProjectiveSystemWithLimit.exists_stageProjection_map_eq_of_isConstructible` —
  the same for a projective system of schemes with limit.

## Implementation notes

The schemes of the system live in a big étale site `B` and abelian sheaves are sheaves of
`AddCommGrpCat.{u + 1}` on the small étale sites `SmallEtale.topology B X`. The index set is a
preorder `I`, the system a functor `Iᵒᵖ ⥤ B.Scheme`. Inverse images along the system and to the
limit are `AlgebraicGeometry.smallEtaleStageTransition` and
`AlgebraicGeometry.smallEtaleStageProjection`, and a map at the stage `β` is compared with maps on
`X` through the canonical identification `AlgebraicGeometry.smallEtaleStageComparison` of
`p_β^* F_β` with `p_α^* F_α`.

The source deduces the statement from the corresponding one for sheaves of sets, through the
description of an abelian sheaf as a sheaf of sets with an addition. The argument above goes
through the torsion of the target instead, which needs only the constructible case and no
statement about sheaves of sets.

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

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

attribute [local instance] SmallEtale.isRightAdjointPushforward_addCommGrpCat

section Factor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- A map from an object killed by `n` into `Φ G` factors through `Φ` of the kernel of `n` on
`G`, as soon as `Φ` is additive and preserves that kernel. -/
theorem exists_factor_kernel_nsmul (Φ : C ⥤ D) [Φ.Additive] {G : C} (n : ℕ)
    [HasKernel (n • 𝟙 G)] [HasKernel (Φ.map (n • 𝟙 G))]
    [PreservesLimit (parallelPair (n • 𝟙 G) 0) Φ] {E : D} (hE : n • 𝟙 E = 0)
    (a : E ⟶ Φ.obj G) :
    ∃ a₁ : E ⟶ Φ.obj (kernel (n • 𝟙 G)), a₁ ≫ Φ.map (kernel.ι (n • 𝟙 G)) = a := by
  have h : a ≫ Φ.map (n • 𝟙 G) = 0 := by
    rw [Φ.map_nsmul, Φ.map_id, Preadditive.comp_nsmul, Category.comp_id,
      ← Category.id_comp a, ← Preadditive.nsmul_comp, hE, zero_comp]
  refine ⟨kernel.lift _ a h ≫ (PreservesKernel.iso Φ (n • 𝟙 G)).inv, ?_⟩
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

end Factor

section Torsion

/-- The kernel of multiplication by `n > 0` on an abelian sheaf is a torsion sheaf. -/
theorem torsionSheafProperty_kernel_nsmul {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    (G : Sheaf J AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n) :
    Stacks.Torsion.torsionSheafProperty J (kernel (n • 𝟙 G)) := by
  have hK : n • 𝟙 (kernel (n • 𝟙 G)) = 0 := by
    rw [← cancel_mono (kernel.ι (n • 𝟙 G)), Preadditive.nsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]
  have happ : ∀ (P : Sheaf J AddCommGrpCat.{u + 1}) (m : ℕ) (V : Cᵒᵖ) (y : P.obj.obj V),
      ((m • 𝟙 P).hom.app V) y = m • y := by
    intro P m V y
    induction m with
    | zero => simp
    | succ m ih =>
      rw [succ_nsmul, Sheaf.Hom.add_app, AddCommGrpCat.hom_add_apply, ih, succ_nsmul]
      rfl
  intro U x
  refine ⟨⊤, J.top_mem U, fun V f _ => ⟨n, hn, ?_⟩⟩
  rw [← happ, hK]
  rfl

end Torsion

section Stages

variable (B : BigEtaleSite.{u})

/-- Inverse image of abelian sheaves (in the universe `u + 1`) is left exact. -/
instance preservesFiniteLimits_smallEtaleSheafPullback_addCommGrpCat {S T : B.Scheme}
    (f : T ⟶ S) :
    PreservesFiniteLimits (smallEtaleSheafPullback B AddCommGrpCat.{u + 1} f) :=
  preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp.{0} B f

/-- Inverse image of abelian sheaves (in the universe `u + 1`) is additive. -/
instance additive_smallEtaleSheafPullback_addCommGrpCat {S T : B.Scheme} (f : T ⟶ S) :
    (smallEtaleSheafPullback B AddCommGrpCat.{u + 1} f).Additive :=
  additive_smallEtaleSheafPullback_addCommGrp.{0} B f

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- Inverse image of abelian sheaves along a morphism of the big étale site preserves colimits,
being a left adjoint. -/
theorem preservesColimitsOfSize_smallEtaleSheafPullback_addCommGrp {S T : B.Scheme}
    (f : T ⟶ S) :
    PreservesColimitsOfSize.{u + 1, u + 1} (smallEtaleSheafPullback B AddCommGrpCat.{u + 1} f) :=
  (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f).leftAdjoint_preservesColimits

/-- The limit of a nonempty directed system of quasi-compact quasi-separated schemes with affine
transition morphisms is quasi-compact and quasi-separated. -/
theorem compactSpace_quasiSeparatedSpace_cone_pt_of_isLimit (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (i : I) :
    CompactSpace (B.obj c.pt hX).obj ∧ QuasiSeparatedSpace (B.obj c.pt hX).obj := by
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) := haff
  have : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have : Nonempty I := ⟨i⟩
  refine ⟨Scheme.compactSpace_of_isLimit (Dg ⋙ B.inclusion) c hc, ?_⟩
  have := isAffineHom_π_app (Dg ⋙ B.inclusion) c hc (op i)
  have : QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj (op i)) := hqs _
  exact quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i))

/-- **Maps out of a constructible abelian sheaf into an arbitrary abelian sheaf: injectivity of
`colim_j Hom(F_j, G_j) → Hom(F, G)`.** Two maps from a constructible abelian sheaf `F` at a stage
into an arbitrary abelian sheaf `G` at that stage which agree after inverse image to the limit
already agree at some later stage. -/
theorem exists_smallEtaleStageTransition_map_eq_of_isConstructibleAbelianSheaf
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B (Dg.obj (op i)) F) (a b : F ⟶ G)
    (hab : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map a =
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map b) :
    ∃ (j : I) (h : i ≤ j),
      (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).map a =
        (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).map b := by
  have : Nonempty I := ⟨i⟩
  obtain ⟨hXc, hXq⟩ :=
    compactSpace_quasiSeparatedSpace_cone_pt_of_isLimit B Dg c hX hc haff hqc hqs i
  have := hqc i
  have := hqs i
  let Pr := smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i
  have : Pr.Additive := additive_smallEtaleSheafPullback_addCommGrpCat B _
  have : PreservesFiniteLimits Pr := preservesFiniteLimits_smallEtaleSheafPullback_addCommGrpCat B _
  have := preservesColimitsOfSize_smallEtaleSheafPullback_addCommGrp B
    (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))
  obtain ⟨n, hn, hFn⟩ := exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B
    (Dg.obj (op i)) (hqc i) (hqs i) F hF
  obtain ⟨J, _, _, D, ι, ⟨hcol⟩, hD⟩ := exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs
    B (Dg.obj (op i)) (kernel (n • 𝟙 G)) (torsionSheafProperty_kernel_nsmul _ G hn)
  have := IsConstructibleAbelianSheaf.isFinitelyPresentable B (Dg.obj (op i)) F hF
  have hPrF := IsConstructibleAbelianSheaf.isFinitelyPresentable B (B.obj c.pt hX) (Pr.obj F)
    (isConstructibleFiniteSheaf_pullback B _ F hF)
  -- the difference `a - b` factors through the kernel of `n` on `G`, then through a stage of
  -- the colimit
  obtain ⟨d₁, hd₁⟩ := exists_factor_kernel_nsmul (𝟭 _) n hFn (a - b)
  obtain ⟨k, d', hd'⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcol d₁
  have hPr : Pr.map d' ≫ Pr.map (ι.app k) = 0 ≫ Pr.map (ι.app k) := by
    rw [← cancel_mono (Pr.map (kernel.ι (n • 𝟙 G))), Category.assoc, ← Pr.map_comp,
      ← Pr.map_comp, ← Category.assoc, hd']
    simp only [Functor.id_map, zero_comp] at hd₁ ⊢
    rw [hd₁, Pr.map_sub, hab, sub_self]
  have hcolPr := isColimitOfPreserves Pr hcol
  obtain ⟨k', u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hcolPr
    (Pr.map d') (0 : Pr.obj F ⟶ Pr.obj (D.obj k)) hPr
  obtain ⟨j, h, hj⟩ := smallEtaleStagesFaithful_isConstructibleAbelianSheaf B Dg c hX hc haff hqc
    hqs i F (D.obj k') hF (hD k') (d' ≫ D.map u) 0 (by
      simpa only [Functor.map_comp, Functor.mapCocone_pt, Functor.comp_map, zero_comp,
        Functor.map_zero] using huv)
  have hab' : a - b = (d' ≫ D.map u) ≫ ι.app k' ≫ kernel.ι _ := by
    have hn := ι.naturality u
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hn
    rw [Category.assoc, ← Category.assoc (D.map u), hn, ← hd₁, ← hd']
    rfl
  refine ⟨j, h, ?_⟩
  rw [← sub_eq_zero, ← Functor.map_sub, hab', Functor.map_comp, hj]
  simp

/-- **Maps out of a constructible abelian sheaf into an arbitrary abelian sheaf: surjectivity of
`colim_j Hom(F_j, G_j) → Hom(F, G)`.** Every map between the inverse images to the limit of a
constructible abelian sheaf `F` and an arbitrary abelian sheaf `G` at a stage is the inverse image
of a map at some later stage, read through the canonical comparison. -/
theorem exists_smallEtaleStageProjection_map_eq_of_isConstructibleAbelianSheaf
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B (Dg.obj (op i)) F)
    (a : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).obj G) :
    ∃ (j : I) (h : i ≤ j) (b : (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj F ⟶
        (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj G),
      (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).inv ≫
          (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX j).map b ≫
          (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h G).hom = a := by
  have : Nonempty I := ⟨i⟩
  obtain ⟨hXc, hXq⟩ :=
    compactSpace_quasiSeparatedSpace_cone_pt_of_isLimit B Dg c hX hc haff hqc hqs i
  let Pr := smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i
  have : Pr.Additive := additive_smallEtaleSheafPullback_addCommGrpCat B _
  have : PreservesFiniteLimits Pr := preservesFiniteLimits_smallEtaleSheafPullback_addCommGrpCat B _
  have := preservesColimitsOfSize_smallEtaleSheafPullback_addCommGrp B
    (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))
  obtain ⟨n, hn, hFn⟩ := exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B
    (Dg.obj (op i)) (hqc i) (hqs i) F hF
  obtain ⟨J, _, _, D, ι, ⟨hcol⟩, hD⟩ := exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs
    B (Dg.obj (op i)) (kernel (n • 𝟙 G)) (torsionSheafProperty_kernel_nsmul _ G hn)
  have := IsConstructibleAbelianSheaf.isFinitelyPresentable B (B.obj c.pt hX) (Pr.obj F)
    (isConstructibleFiniteSheaf_pullback B _ F hF)
  have hPrFn : n • 𝟙 (Pr.obj F) = 0 := by
    rw [← Pr.map_id, ← Functor.map_nsmul, hFn, Functor.map_zero]
  obtain ⟨a₁, ha₁⟩ := exists_factor_kernel_nsmul Pr n hPrFn a
  obtain ⟨k, a', ha'⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (isColimitOfPreserves Pr hcol) a₁
  obtain ⟨j, h, b', hb'⟩ := smallEtaleStagesFull_isConstructibleAbelianSheaf_unconditional B Dg c hX
    hc haff hqc hqs i F (D.obj k) hF (hD k) a'
  refine ⟨j, h, b' ≫ (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).map
    (ι.app k ≫ kernel.ι _), ?_⟩
  rw [Functor.map_comp, Category.assoc, smallEtaleStageComparison_hom_naturality, ← ha₁, ← ha',
    ← hb']
  simp [Pr]

end Stages

section ProjectiveSystem

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)
  (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Hom of abelian sheaves out of a constructible sheaf along a projective limit,
injectivity.** Let `X = lim X_α` be a projective system of schemes with limit, `F_α` a
constructible abelian sheaf and `G_α` an arbitrary abelian sheaf on the small étale site of `X_α`.
Two maps `F_α ⟶ G_α` with the same inverse image `p_α^* F_α ⟶ p_α^* G_α` on `X` have the same
inverse image on some `X_β`, `β ≥ α`: the map
`colim_{β ≥ α} Hom(F_β, G_β) ⟶ Hom(F, G)` is injective. -/
@[weil "lem_fk104_hom_abelian_from_constructible_colimit"]
theorem IsProjectiveSystemWithLimit.exists_stageTransition_map_eq_of_isConstructible
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (α : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op α)).obj (Dg.obj (op α)).property)
      AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B (Dg.obj (op α)) F) (a b : F ⟶ G)
    (hab : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX α).map a =
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX α).map b) :
    ∃ (β : I) (h : α ≤ β),
      (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).map a =
        (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).map b := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  have hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  have hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  exact AlgebraicGeometry.exists_smallEtaleStageTransition_map_eq_of_isConstructibleAbelianSheaf
    B Dg c hX hc (fun e => hD.isAffineHom_map e) hqc hqs α F G hF a b hab

/-- **Hom of abelian sheaves out of a constructible sheaf along a projective limit,
surjectivity.** Let `X = lim X_α` be a projective system of schemes with limit, `F_α` a
constructible abelian sheaf and `G_α` an arbitrary abelian sheaf on the small étale site of `X_α`.
Every map `p_α^* F_α ⟶ p_α^* G_α` on `X` is, through the canonical identifications
`p_β^* F_β ≅ p_α^* F_α`, the inverse image of a map `F_β ⟶ G_β` for some `β ≥ α`: the map
`colim_{β ≥ α} Hom(F_β, G_β) ⟶ Hom(F, G)` is surjective. -/
@[weil "lem_fk104_hom_abelian_from_constructible_colimit"]
theorem IsProjectiveSystemWithLimit.exists_stageProjection_map_eq_of_isConstructible
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (α : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op α)).obj (Dg.obj (op α)).property)
      AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B (Dg.obj (op α)) F)
    (a : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX α).obj F ⟶
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX α).obj G) :
    ∃ (β : I) (h : α ≤ β) (b : (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj F ⟶
        (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg h).obj G),
      (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h F).inv ≫
          (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX β).map b ≫
          (smallEtaleStageComparison B AddCommGrpCat.{u + 1} Dg c hX h G).hom = a := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  have hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  have hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  exact AlgebraicGeometry.exists_smallEtaleStageProjection_map_eq_of_isConstructibleAbelianSheaf
    B Dg c hX hc (fun e => hD.isAffineHom_map e) hqc hqs α F G hF a

end ProjectiveSystem

end AlgebraicGeometry
