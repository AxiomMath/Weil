module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.Constructible.StageFullness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm

/-!
# Sections of a constructible sheaf along a limit of schemes

Let `X = lim Xⱼ` be the limit of a directed inverse system of quasi-compact quasi-separated
schemes with affine transition morphisms, inside a big étale site, let `i` be an index, `G` a
constructible sheaf of sets on the small étale site of `Xᵢ` and `U` a quasi-compact
quasi-separated scheme étale over `Xᵢ`. Write `Gⱼ`, `Uⱼ` (for `j ≥ i`) and `G|_X`, `U_X` for the
inverse images of `G` and the base changes of `U`. Restriction of sections along `Xₖ ⟶ Xⱼ` and
`X ⟶ Xⱼ` gives transition maps `Gⱼ(Uⱼ) ⟶ Gₖ(Uₖ)` and maps `Gⱼ(Uⱼ) ⟶ G|_X(U_X)` compatible with
them, and the induced map
`colim_{j ≥ i} Gⱼ(Uⱼ) ⟶ G|_X(U_X)`
is bijective: every section over `U_X` comes from a stage, and two sections at a stage with the
same image over `U_X` agree at a later stage.

Surjectivity is `AlgebraicGeometry.exists_smallEtaleStageSectionsMap_eq` (the fullness assertion
of [Stacks, Tag 09YU] for the representable source `h_U`). Injectivity is the faithfulness
assertion of [Stacks, Tag 09YU]: a section `t` of `Gⱼ` over `Uⱼ` is a map `h_{Uⱼ} ⟶ Gⱼ`, its
image over `U_X` is the inverse image of that map, and two maps between constructible sheaves of
sets with the same inverse image to `X` already agree at a later stage.

## Main definitions

* `AlgebraicGeometry.smallEtaleStageSectionsTransition`: the transition map `Gⱼ(Uⱼ) ⟶ Gₖ(Uₖ)`.
* `AlgebraicGeometry.smallEtaleStageSectionsToLimit`: the map `Gⱼ(Uⱼ) ⟶ G|_X(U_X)`.

## Main results

* `AlgebraicGeometry.smallEtaleStageSectionsToLimit_transition`: the maps to `G|_X(U_X)` are
  compatible with the transition maps, so they induce `colim_{j ≥ i} Gⱼ(Uⱼ) ⟶ G|_X(U_X)`.
* `AlgebraicGeometry.exists_smallEtaleStageSectionsToLimit_eq`: this map is surjective.
* `exists_smallEtaleStageSectionsTransition_eq_of_smallEtaleStageSectionsToLimit_eq`
  (in the namespace `AlgebraicGeometry`): this map is injective.

## Implementation notes

The colimit over `j ≥ i` is stated elementwise, by the compatibility of the maps to the limit with
the transition maps together with surjectivity and injectivity. The transition maps and the maps
to the limit are the units of the inverse image adjunctions, read through the canonical
identifications of iterated inverse images (`AlgebraicGeometry.smallEtaleStageComparison`,
`AlgebraicGeometry.smallEtaleStageTransitionComp`) and of iterated base changes
(`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`). Freitag and Kiehl assume the schemes
noetherian and `U` of finite type over `Xᵢ`; only quasi-compactness and quasi-separatedness are
used. The étale sites are the small étale sites `AlgebraicGeometry.SmallEtale` of a big étale
site, and sheaves of sets take values in `Type (u + 1)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.17 2), p. 50;
  proof pp. 51–52.
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The unit of the inverse image adjunction, on sections over `V`, read through the
corepresentability bijections. -/
theorem smallEtale_unit_sheafifiedYonedaEquiv (B : BigEtaleSite.{u})
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (V : SmallEtale B S.obj S.property)
    (b : (Sheaf.sheafifiedYoneda (SmallEtale.topology B S.obj S.property)).obj V ⟶ F) :
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V)
        (Sheaf.sheafifiedYonedaEquiv _ V F b) =
      Sheaf.pullbackSheafifiedYonedaEquiv (smallEtaleBaseChange B f)
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) V
        ((smallEtaleSheafPullback B (Type (u + 1)) f).obj F)
        ((smallEtaleSheafPullback B (Type (u + 1)) f).map b) := by
  have hn : b ≫ ((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F =
      ((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).homEquiv _ _
        ((smallEtaleSheafPullback B (Type (u + 1)) f).map b) := by
    rw [Adjunction.homEquiv_unit]
    exact (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.naturality b)
  exact (Sheaf.sheafifiedYonedaEquiv_naturality _ V _ b).symm.trans
    (congrArg (Sheaf.sheafifiedYonedaEquiv _ V _) hn)

/-- **Units of inverse images along a composite.** For `f : X ⟶ Y`, `g : Y ⟶ Z` with
`f ≫ g = fg`, a section `x` of a sheaf `F` on `Z` over `V`, restricted first to `g⁻¹F` and then to
`f⁻¹g⁻¹F`, is carried by the composition comparison `f⁻¹g⁻¹F ≅ fg⁻¹F` to the restriction of `x`
to `fg⁻¹F`, read through the canonical isomorphism `V_Y ×_Y X ≅ V_X`. -/
theorem smallEtaleSheafPullbackCompIso'_hom_unit_unit (B : BigEtaleSite.{u})
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (e : f ≫ g = fg)
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) (Type (u + 1)))
    (V : SmallEtale B Z.obj Z.property) (x : F.obj.obj (op V)) :
    ((smallEtaleSheafPullbackCompIso' B (Type (u + 1)) f g fg e).hom.app F).hom.app
        (op ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V)))
      ((((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).unit.app
            ((smallEtaleSheafPullback B (Type (u + 1)) g).obj F)).hom.app
          (op ((smallEtaleBaseChange B g).obj V))
        ((((smallEtaleBaseChange B g).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B Y.obj Y.property)).unit.app
            F).hom.app (op V) x)) =
      ((smallEtaleSheafPullback B (Type (u + 1)) fg).obj F).obj.map
        ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg e).hom.app V).op
        ((((smallEtaleBaseChange B fg).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B X.obj X.property)).unit.app
            F).hom.app (op V) x) := by
  have h := congrArg (fun φ => φ.hom.app (op V) x)
    (unit_sheafPullbackFactoredCompIso B f g fg e (Type (u + 1)) F)
  rw [smallEtaleSheafPullbackCompIso'_eq]
  exact h.symm

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- The restriction map `Gⱼ(V) ⟶ Gₖ(Vₖ)`, for `j ≤ k`, of a sheaf `Gⱼ` on the stage `Xⱼ`: the
unit of the inverse image adjunction along `Xₖ ⟶ Xⱼ`. -/
abbrev smallEtaleStageUnit {j k : I} (h : j ≤ k)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      (Type (u + 1)))
    (V : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property) :
    F.obj.obj (op V) →
      ((smallEtaleStageTransition B (Type (u + 1)) Dg h).obj F).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj V)) :=
  (((smallEtaleBaseChange B (systemStageHom B Dg h)).sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
    (SmallEtale.topology B (Dg.obj (op k)).obj (Dg.obj (op k)).property)).unit.app F).hom.app
      (op V)


/-- The unit of the inverse image adjunction is natural in the étale object. -/
theorem smallEtale_unit_map_apply {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {V V' : SmallEtale B S.obj S.property} (ψ : V ⟶ V') (z : F.obj.obj (op V')) :
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V) (F.obj.map ψ.op z) =
      ((smallEtaleSheafPullback B (Type (u + 1)) f).obj F).obj.map
        ((smallEtaleBaseChange B f).map ψ).op
        ((((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V') z) :=
  NatTrans.naturality_apply (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F).hom ψ.op z

/-- The unit of the inverse image adjunction is natural in the sheaf. -/
theorem smallEtale_unit_app_apply {S T : B.Scheme} (f : T ⟶ S)
    {F F' : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))} (α : F ⟶ F')
    (V : SmallEtale B S.obj S.property) (x : F.obj.obj (op V)) :
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F').hom.app (op V) (α.hom.app (op V) x) =
      ((smallEtaleSheafPullback B (Type (u + 1)) f).map α).hom.app
        (op ((smallEtaleBaseChange B f).obj V))
        ((((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V) x) :=
  congrArg (fun φ => φ.hom.app (op V) x)
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.naturality α)


/-- The cocycle law of the comparisons, on sections. -/
theorem smallEtaleStageComparison_trans_apply {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1))) (W : (SmallEtale B c.pt hX)ᵒᵖ) (v) :
    (smallEtaleStageComparison B (Type (u + 1)) Dg c hX (hij.trans hjk) G).hom.hom.app W
        (((smallEtaleStageProjection B (Type (u + 1)) Dg c hX k).map
          (smallEtaleStageTransitionComp B (Type (u + 1)) Dg hij hjk G).hom).hom.app W v) =
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX hij G).hom.hom.app W
        ((smallEtaleStageComparison B (Type (u + 1)) Dg c hX hjk
          ((smallEtaleStageTransition B (Type (u + 1)) Dg hij).obj G)).hom.hom.app W v) :=
  (congrArg (fun φ => φ.hom.app W v)
    (smallEtaleStageComparison_trans B (Type (u + 1)) Dg c hX hij hjk G)).symm

/-- The comparison `(Fₖ)_X ≅ F|_X` of a sheaf `F` on the stage `Xⱼ` carries the restriction of a
section along `Xₖ ⟶ Xⱼ` and then along `X ⟶ Xₖ` to its restriction along `X ⟶ Xⱼ`, read through
`(Vₖ)_X ≅ V_X`. -/
theorem smallEtaleStageComparison_hom_unit_unit {j k : I} (hjk : j ≤ k)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      (Type (u + 1)))
    (V : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property) (x : F.obj.obj (op V)) :
    (smallEtaleStageComparison B (Type (u + 1)) Dg c hX hjk F).hom.hom.app _
      ((((smallEtaleBaseChange B (coneStageHom B Dg c hX k)).sheafAdjunctionContinuous
        (Type (u + 1)) (SmallEtale.topology B (Dg.obj (op k)).obj (Dg.obj (op k)).property)
        (SmallEtale.topology B c.pt hX)).unit.app
          ((smallEtaleStageTransition B (Type (u + 1)) Dg hjk).obj F)).hom.app _
        (smallEtaleStageUnit B Dg hjk F V x)) =
      ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX j).obj F).obj.map
        ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op k)) (Dg.obj (op j))
          (coneStageHom B Dg c hX k) (systemStageHom B Dg hjk) (coneStageHom B Dg c hX j)
          (coneStageHom_comp B Dg c hX hjk)).hom.app V).op
        ((((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).sheafAdjunctionContinuous
          (Type (u + 1)) (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
          (SmallEtale.topology B c.pt hX)).unit.app F).hom.app (op V) x) := by
  rw [smallEtaleStageComparison_eq]
  exact smallEtaleSheafPullbackCompIso'_hom_unit_unit B _ _ _ _ F V x

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- The base change comparisons along `X ⟶ Xₖ ⟶ Xⱼ ⟶ Xᵢ` are coherent. -/
theorem smallEtaleBaseChange_factoredCompIso_stage_coherence {i j k : I} (hij : i ≤ j)
    (hjk : j ≤ k) (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property) :
    (smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op k)) (Dg.obj (op i))
      (coneStageHom B Dg c hX k) (systemStageHom B Dg (hij.trans hjk))
      (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX (hij.trans hjk))).inv.app U ≫
      (smallEtaleBaseChange B (coneStageHom B Dg c hX k)).map
        ((smallEtaleBaseChange_factoredCompIso B (Dg.obj (op k)) (Dg.obj (op j)) (Dg.obj (op i))
          (systemStageHom B Dg hjk) (systemStageHom B Dg hij)
          (systemStageHom B Dg (hij.trans hjk)) (systemStageHom_comp B Dg hij hjk)).inv.app U) ≫
      (smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op k)) (Dg.obj (op j))
        (coneStageHom B Dg c hX k) (systemStageHom B Dg hjk) (coneStageHom B Dg c hX j)
        (coneStageHom_comp B Dg c hX hjk)).hom.app
          ((smallEtaleBaseChange B (systemStageHom B Dg hij)).obj U) =
    (smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
      (coneStageHom B Dg c hX j) (systemStageHom B Dg hij) (coneStageHom B Dg c hX i)
      (coneStageHom_comp B Dg c hX hij)).inv.app U := by
  rw [reassoc_of% (smallEtaleBaseChange_factoredCompIso_inv_assoc B (coneStageHom B Dg c hX k)
    (systemStageHom B Dg hjk) (systemStageHom B Dg hij) (coneStageHom B Dg c hX j)
    (systemStageHom B Dg (hij.trans hjk)) (coneStageHom B Dg c hX i)
    (coneStageHom_comp B Dg c hX hjk) (systemStageHom_comp B Dg hij hjk)
    (coneStageHom_comp B Dg c hX hij) (coneStageHom_comp B Dg c hX (hij.trans hjk)) U),
    Iso.inv_hom_id_app, Category.comp_id]

/-- **The restriction maps to the limit are injective up to a later stage**, in the form
of the unit: two sections of `Gⱼ` over `Uⱼ` with the same image in `G|_X(U_X)` already have the
same restriction to a later stage. -/
theorem exists_smallEtaleStageUnit_eq_of_smallEtaleStageSectionsMap_eq
    [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) {i j : I} (h : i ≤ j)
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1)))
    (hG : IsConstructibleSetSheaf B (Dg.obj (op i)) G)
    (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hU : IsQCQSEtaleObject B (Dg.obj (op i)) U)
    (t t' : ((smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj U)))
    (heq : smallEtaleStageSectionsMap B Dg c hX h G _ t =
      smallEtaleStageSectionsMap B Dg c hX h G _ t') :
    ∃ (k : I) (hjk : j ≤ k), smallEtaleStageUnit B Dg hjk _ _ t =
      smallEtaleStageUnit B Dg hjk _ _ t' := by
  have : Nonempty I := ⟨i⟩
  have : CompactSpace (Dg.obj (op j)).obj := hqc j
  have : QuasiSeparatedSpace (Dg.obj (op j)).obj := hqs j
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  let F' := (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G
  let V := (smallEtaleBaseChange B (systemStageHom B Dg h)).obj U
  have hF' : IsConstructibleSetSheaf B (Dg.obj (op j)) F' :=
    isConstructibleFiniteSheaf_pullback B _ G hG
  have hV : IsQCQSEtaleObject B (Dg.obj (op j)) V :=
    isQCQSEtaleObject_smallEtaleBaseChange B _ U hU
  have : CompactSpace V.obj.left.obj := hV.1
  have : QuasiSeparatedSpace V.obj.left.obj := hV.2
  let Jj := SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property
  let a := (Sheaf.sheafifiedYonedaEquiv Jj V F').symm t
  let a' := (Sheaf.sheafifiedYonedaEquiv Jj V F').symm t'
  have hu : ∀ {S : B.Scheme} (f : S ⟶ Dg.obj (op j)) (x : F'.obj.obj (op V)),
      (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1)) Jj
        (SmallEtale.topology B S.obj S.property)).unit.app F').hom.app (op V) x =
      Sheaf.pullbackSheafifiedYonedaEquiv (smallEtaleBaseChange B f) Jj
        (SmallEtale.topology B S.obj S.property) V
        ((smallEtaleSheafPullback B (Type (u + 1)) f).obj F')
        ((smallEtaleSheafPullback B (Type (u + 1)) f).map
          ((Sheaf.sheafifiedYonedaEquiv Jj V F').symm x)) := fun f x => by
    have := smallEtale_unit_sheafifiedYonedaEquiv B f F' V
      ((Sheaf.sheafifiedYonedaEquiv Jj V F').symm x)
    rwa [Equiv.apply_symm_apply] at this
  have hX' : (((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).sheafAdjunctionContinuous
      (Type (u + 1)) Jj (SmallEtale.topology B c.pt hX)).unit.app F').hom.app (op V) t =
      (((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).sheafAdjunctionContinuous
      (Type (u + 1)) Jj (SmallEtale.topology B c.pt hX)).unit.app F').hom.app (op V) t' := by
    have key : ∀ x, (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).inv.hom.app _
        ((smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom.hom.app
          (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj V)) x) = x := fun x => by
      have e := congrArg (fun φ => φ.hom.app
        (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj V)) x)
        (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom_inv_id
      exact e
    exact Function.LeftInverse.injective key heq
  rw [hu, hu] at hX'
  have hP := (Sheaf.pullbackSheafifiedYonedaEquiv _ _ _ _ _).injective hX'
  obtain ⟨k, hjk, hk⟩ := smallEtaleStagesFaithful_isConstructibleSetSheaf B Dg c hX hc haff hqc
    hqs j _ F' (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B _ V) hF' a a' hP
  refine ⟨k, hjk, ?_⟩
  change (((smallEtaleBaseChange B (systemStageHom B Dg hjk)).sheafAdjunctionContinuous
      (Type (u + 1)) Jj _).unit.app F').hom.app (op V) t = (((smallEtaleBaseChange B
        (systemStageHom B Dg hjk)).sheafAdjunctionContinuous (Type (u + 1)) Jj _).unit.app
          F').hom.app (op V) t'
  rw [hu, hu]
  exact congrArg _ hk

variable {i : I} (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (Type (u + 1))) (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)

/-- **The transition map `Gⱼ(Uⱼ) ⟶ Gₖ(Uₖ)`**, for `i ≤ j ≤ k`, of the sections of the inverse
images `Gⱼ` of a sheaf `G` on the stage `Xᵢ` over the base changes `Uⱼ` of an étale `Xᵢ`-scheme
`U`: restriction along `Xₖ ⟶ Xⱼ`, read through the canonical identifications
`(Gⱼ)ₖ ≅ Gₖ` and `(Uⱼ)ₖ ≅ Uₖ`. -/
def smallEtaleStageSectionsTransition {j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    ((smallEtaleStageTransition B (Type (u + 1)) Dg hij).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg hij)).obj U)) →
      ((smallEtaleStageTransition B (Type (u + 1)) Dg (hij.trans hjk)).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg (hij.trans hjk))).obj U)) := fun t =>
  ((smallEtaleStageTransition B (Type (u + 1)) Dg (hij.trans hjk)).obj G).obj.map
    ((smallEtaleBaseChange_factoredCompIso B (Dg.obj (op k)) (Dg.obj (op j)) (Dg.obj (op i))
      (systemStageHom B Dg hjk) (systemStageHom B Dg hij) (systemStageHom B Dg (hij.trans hjk))
      (systemStageHom_comp B Dg hij hjk)).inv.app U).op
    ((smallEtaleStageTransitionComp B (Type (u + 1)) Dg hij hjk G).hom.hom.app _
      (smallEtaleStageUnit B Dg hjk _ _ t))

/-- **The map `Gⱼ(Uⱼ) ⟶ G(U)`**, for `i ≤ j`, from the sections of the inverse image `Gⱼ` to
the stage `Xⱼ` of a sheaf `G` on `Xᵢ` over the base change `Uⱼ` of an étale `Xᵢ`-scheme `U`, to
the sections of the inverse image `G` to the limit `X` over the base change `U_X`: restriction
along `X ⟶ Xⱼ`, read through the canonical identifications `(Gⱼ)_X ≅ G|_X` and
`(Uⱼ)_X ≅ U_X`. -/
def smallEtaleStageSectionsToLimit {j : I} (hij : i ≤ j) :
    ((smallEtaleStageTransition B (Type (u + 1)) Dg hij).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg hij)).obj U)) →
      ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.obj
        (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj U)) := fun t =>
  ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map
    ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
      (coneStageHom B Dg c hX j) (systemStageHom B Dg hij) (coneStageHom B Dg c hX i)
      (coneStageHom_comp B Dg c hX hij)).inv.app U).op
    (smallEtaleStageSectionsMap B Dg c hX hij G _ t)

/-- **The maps `Gⱼ(Uⱼ) ⟶ G(U)` are compatible with the transition maps**, so they induce a map
`colim_{j ≥ i} Gⱼ(Uⱼ) ⟶ G(U)`. -/
@[weil "lem_fk104_sections_of_constructible_colimit_representable"]
theorem smallEtaleStageSectionsToLimit_transition {j k : I} (hij : i ≤ j) (hjk : j ≤ k) (t) :
    smallEtaleStageSectionsToLimit B Dg c hX G U (hij.trans hjk)
        (smallEtaleStageSectionsTransition B Dg G U hij hjk t) =
      smallEtaleStageSectionsToLimit B Dg c hX G U hij t := by
  dsimp only [smallEtaleStageSectionsToLimit, smallEtaleStageSectionsTransition,
    smallEtaleStageSectionsMap, smallEtaleStageUnit]
  rw [smallEtale_unit_map_apply]
  erw [smallEtale_unit_app_apply]
  simp only [NatTrans.naturality_apply]
  refine Eq.trans (congrArg (fun y => ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj
    G).obj.map _ (((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map _ y))
    (smallEtaleStageComparison_trans_apply B Dg c hX hij hjk G _ _)) ?_
  refine Eq.trans (congrArg (fun y => ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj
    G).obj.map _ (((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map _
      ((smallEtaleStageComparison B (Type (u + 1)) Dg c hX hij G).hom.hom.app _ y)))
    (smallEtaleStageComparison_hom_unit_unit B Dg c hX hjk _ _ t)) ?_
  refine Eq.trans (congrArg (fun y => ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj
    G).obj.map _ (((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map _ y))
    (NatTrans.naturality_apply (smallEtaleStageComparison B (Type (u + 1)) Dg c hX hij G).hom.hom
      _ _)) ?_
  have hm : ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op k))
      (Dg.obj (op j)) (coneStageHom B Dg c hX k) (systemStageHom B Dg hjk)
      (coneStageHom B Dg c hX j) (coneStageHom_comp B Dg c hX hjk)).hom.app
        ((smallEtaleBaseChange B (systemStageHom B Dg hij)).obj U)).op ≫
      ((smallEtaleBaseChange B (coneStageHom B Dg c hX k)).map
        ((smallEtaleBaseChange_factoredCompIso B (Dg.obj (op k)) (Dg.obj (op j)) (Dg.obj (op i))
          (systemStageHom B Dg hjk) (systemStageHom B Dg hij)
          (systemStageHom B Dg (hij.trans hjk)) (systemStageHom_comp B Dg hij hjk)).inv.app U)).op ≫
      ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op k)) (Dg.obj (op i))
        (coneStageHom B Dg c hX k) (systemStageHom B Dg (hij.trans hjk))
        (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX (hij.trans hjk))).inv.app U).op =
      ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
        (coneStageHom B Dg c hX j) (systemStageHom B Dg hij) (coneStageHom B Dg c hX i)
        (coneStageHom_comp B Dg c hX hij)).inv.app U).op := by
    rw [← op_comp, ← op_comp, Category.assoc,
      smallEtaleBaseChange_factoredCompIso_stage_coherence B Dg c hX hij hjk U]
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  simp only [hm]

/-- **Sections of a constructible sheaf over a limit: the colimit map is surjective.** Let
`X = lim Xⱼ` be a directed limit of quasi-compact quasi-separated schemes with affine transition
morphisms, `G` a constructible sheaf of sets on the small étale site of `Xᵢ` and `U` a
quasi-compact quasi-separated scheme étale over `Xᵢ`. Every section of `G|_X` over `U_X` is the
image of a section of `Gⱼ` over `Uⱼ` for some `j ≥ i`. -/
@[weil "lem_fk104_sections_of_constructible_colimit_representable"]
theorem exists_smallEtaleStageSectionsToLimit_eq [Nonempty I] [IsDirected I (· ≤ ·)]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (hG : IsConstructibleSetSheaf B (Dg.obj (op i)) G) (hU : IsQCQSEtaleObject B (Dg.obj (op i)) U)
    (s : ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.obj
      (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj U))) :
    ∃ (j : I) (hij : i ≤ j) (t : ((smallEtaleStageTransition B (Type (u + 1)) Dg hij).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg hij)).obj U))),
      smallEtaleStageSectionsToLimit B Dg c hX G U hij t = s := by
  obtain ⟨j, hij, t, ht⟩ := exists_smallEtaleStageSectionsMap_eq B Dg c hX hc haff hqc hqs G hG U
    hU s
  refine ⟨j, hij, t, ?_⟩
  have hm : ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
      (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg hij)
      (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)).hom.app U).op ≫
      ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
      (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg hij)
      (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)).inv.app U).op = 𝟙 _ := by
    rw [← op_comp, Iso.inv_hom_id_app, op_id]
  dsimp only [smallEtaleStageSectionsToLimit]
  rw [ht, ← Functor.map_comp_apply]
  simp only [hm, Functor.map_id_apply]

/-- **Sections of a constructible sheaf over a limit: the colimit map is injective.** In the
situation of `AlgebraicGeometry.exists_smallEtaleStageSectionsToLimit_eq`, two sections of `Gⱼ`
over `Uⱼ` with the same image in `G|_X(U_X)` have the same image in `Gₖ(Uₖ)` for some `k ≥ j`. -/
@[weil "lem_fk104_sections_of_constructible_colimit_representable"]
theorem exists_smallEtaleStageSectionsTransition_eq_of_smallEtaleStageSectionsToLimit_eq
    [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (hG : IsConstructibleSetSheaf B (Dg.obj (op i)) G) (hU : IsQCQSEtaleObject B (Dg.obj (op i)) U)
    {j : I} (hij : i ≤ j)
    (t t' : ((smallEtaleStageTransition B (Type (u + 1)) Dg hij).obj G).obj.obj
      (op ((smallEtaleBaseChange B (systemStageHom B Dg hij)).obj U)))
    (heq : smallEtaleStageSectionsToLimit B Dg c hX G U hij t =
      smallEtaleStageSectionsToLimit B Dg c hX G U hij t') :
    ∃ (k : I) (hjk : j ≤ k), smallEtaleStageSectionsTransition B Dg G U hij hjk t =
      smallEtaleStageSectionsTransition B Dg G U hij hjk t' := by
  have hm : ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
      (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg hij)
      (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)).inv.app U).op ≫
      ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
      (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg hij)
      (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)).hom.app U).op = 𝟙 _ := by
    rw [← op_comp, Iso.hom_inv_id_app, op_id]
  have key : ∀ y, ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map
      ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
      (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg hij)
      (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)).hom.app U).op
      (((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map
        ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
        (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg hij)
        (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)).inv.app U).op y) = y :=
    fun y => by
      rw [← Functor.map_comp_apply]
      simp only [hm, Functor.map_id_apply]
  have heq' : smallEtaleStageSectionsMap B Dg c hX hij G _ t =
      smallEtaleStageSectionsMap B Dg c hX hij G _ t' :=
    Function.LeftInverse.injective key heq
  obtain ⟨k, hjk, hk⟩ := exists_smallEtaleStageUnit_eq_of_smallEtaleStageSectionsMap_eq B Dg c hX
    hc haff hqc hqs hij G hG U hU t t' heq'
  refine ⟨k, hjk, ?_⟩
  dsimp only [smallEtaleStageSectionsTransition]
  rw [hk]

end AlgebraicGeometry
