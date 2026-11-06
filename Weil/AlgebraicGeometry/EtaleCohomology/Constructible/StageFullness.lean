module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFullness

/-!
# Sections of a constructible sheaf over a limit come from a finite stage

Let `X = lim Xᵢ` be the limit of a directed inverse system of quasi-compact quasi-separated
schemes with affine transition morphisms, inside a big étale site. Let `G` be a constructible
sheaf of sets on the small étale site of a stage `Xᵢ`, let `U` be a quasi-compact quasi-separated
scheme étale over `Xᵢ`, and write `Gⱼ`, `Uⱼ` (for `j ≥ i`) and `G|_X`, `U_X` for the inverse
images and base changes. Then every section of `G|_X` over `U_X` comes from a section of `Gⱼ`
over `Uⱼ` for some `j ≥ i`: the canonical map `colim_{j ≥ i} Gⱼ(Uⱼ) ⟶ G|_X(U_X)` is surjective.

Sections over `U_X` are maps out of the sheaf represented by `U_X`, which is the inverse image of
the sheaf represented by `U`; since that sheaf is constructible, the statement is the special case
of fullness in Tag 09YU, clause (1), in which the source is a representable sheaf.

The case of Freitag–Kiehl is the one where `G` is the cokernel of a pair of morphisms `R ⇉ H`
between quasi-compact quasi-separated étale `Xᵢ`-schemes, i.e. a coequalizer of two representable
sheaves; such a coequalizer is constructible (Tag 03RZ).

## Main definitions

* `AlgebraicGeometry.smallEtaleStageSectionsMap`: the canonical map `Gⱼ(V) ⟶ G|_X(V_X)` for a
  scheme `V` étale over `Xⱼ`, the unit of the inverse image adjunction followed by the comparison
  of inverse images through `Xⱼ` with inverse images through `Xᵢ`.

## Main results

* `AlgebraicGeometry.exists_smallEtaleStageSectionsMap_eq`: every section of `G|_X` over `U_X`
  comes from a stage, for a constructible sheaf of sets `G`.
* `AlgebraicGeometry.exists_smallEtaleStageSectionsMap_eq_of_isColimit_cofork`: the case of a
  cokernel of a pair of morphisms between representable sheaves.

## Implementation notes

A section `t ∈ Gⱼ(Uⱼ)` maps to `G|_X((Uⱼ)_X)`, and `(Uⱼ)_X` is identified with `U_X` by the
canonical isomorphism `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`; the statement says
that the image of `t` is the restriction of the given section along this isomorphism. Freitag–Kiehl
assume the stages noetherian and the étale schemes of finite type, hence quasi-compact and
quasi-separated; only the latter is used. Their hypothesis that `R ⇉ H` is an equivalence
relation is not needed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.4.17 2).
* [Stacks] Stacks Project, Tags 09YU, 03RZ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- The canonical map `Gⱼ(V) ⟶ G|_X(V_X)` from the sections over `V` of the inverse image `Gⱼ` to
the stage `Xⱼ` of a sheaf `G` on `Xᵢ` (`i ≤ j`) to the sections over the base change `V_X` of the
inverse image of `G` to the limit `X`: the unit of the inverse image adjunction along `X ⟶ Xⱼ`,
followed by the comparison of inverse image to `X` through `Xⱼ` with inverse image along
`X ⟶ Xᵢ`. -/
def smallEtaleStageSectionsMap {i j : I} (h : i ≤ j)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1)))
    (V : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property) :
    ((smallEtaleStageTransition B (Type (u + 1)) Dg h).obj F).obj.obj (op V) →
      ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj F).obj.obj
        (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj V)) := fun t =>
  (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h F).hom.hom.app _
    ((((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).sheafAdjunctionContinuous
      (Type (u + 1)) (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      (SmallEtale.topology B c.pt hX)).unit.app
        ((smallEtaleStageTransition B (Type (u + 1)) Dg h).obj F)).hom.app (op V) t)

/-- **Sections of a constructible sheaf over a limit come from a stage.** Let `X = lim Xᵢ` be a
directed limit of quasi-compact quasi-separated schemes with affine transition morphisms, `G` a
constructible sheaf of sets on the small étale site of `Xᵢ` and `U` a quasi-compact
quasi-separated scheme étale over `Xᵢ`. Every section `s` of the inverse image of `G` to `X` over
`U_X` comes from a section `t` of `Gⱼ` over `Uⱼ` for some `j ≥ i`: the image of `t` in the
sections over `(Uⱼ)_X` is the restriction of `s` along the canonical isomorphism
`(Uⱼ)_X ≅ U_X`. In other words `colim_{j ≥ i} Gⱼ(Uⱼ) ⟶ G|_X(U_X)` is surjective. -/
@[weil "lem_fk104_sections_colimit_surjective"]
theorem exists_smallEtaleStageSectionsMap_eq [Nonempty I] [IsDirected I (· ≤ ·)]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) {i : I}
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1)))
    (hG : IsConstructibleSetSheaf B (Dg.obj (op i)) G)
    (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hU : IsQCQSEtaleObject B (Dg.obj (op i)) U)
    (s : ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.obj
      (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj U))) :
    ∃ (j : I) (h : i ≤ j)
      (t : ((smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj U))),
      smallEtaleStageSectionsMap B Dg c hX h G _ t =
        ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map
          ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
            (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
            (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h)).hom.app U).op s := by
  have : CompactSpace (Dg.obj (op i)).obj := hqc i
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  have : CompactSpace U.obj.left.obj := hU.1
  have : QuasiSeparatedSpace U.obj.left.obj := hU.2
  let a := (Sheaf.pullbackSheafifiedYonedaEquiv (smallEtaleBaseChange B (coneStageHom B Dg c hX i))
    (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (SmallEtale.topology B c.pt hX) U _).symm s
  obtain ⟨j, h, b, hb⟩ := smallEtaleStagesFull_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs
    i _ G (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B _ U) hG a
  refine ⟨j, h, Sheaf.pullbackSheafifiedYonedaEquiv (smallEtaleBaseChange B (systemStageHom B Dg h))
    (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) U _ b, ?_⟩
  -- notation
  let Jj := SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property
  let Ji := SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property
  let JX := SmallEtale.topology B c.pt hX
  let uj := smallEtaleBaseChange B (coneStageHom B Dg c hX j)
  let ui := smallEtaleBaseChange B (coneStageHom B Dg c hX i)
  let uh := smallEtaleBaseChange B (systemStageHom B Dg h)
  let Pj := smallEtaleStageProjection B (Type (u + 1)) Dg c hX j
  let TG := (smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G
  let PG := (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G
  let V := uh.obj U
  let φ := (smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
    (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
    (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h)).hom.app U
  let isoT := smallEtaleSheafifiedYonedaPullbackIso B (systemStageHom B Dg h) U
  let isoPj := smallEtaleSheafifiedYonedaPullbackIso B (coneStageHom B Dg c hX j) V
  let isoPi := smallEtaleSheafifiedYonedaPullbackIso B (coneStageHom B Dg c hX i) U
  let adj := uj.sheafAdjunctionContinuous (Type (u + 1)) Jj JX
  let b' := isoT.inv ≫ b
  -- the comparison on a representable sheaf
  have hK : (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
      ((Sheaf.sheafifiedYoneda Ji).obj U)).hom =
      Pj.map isoT.hom ≫ isoPj.hom ≫ (Sheaf.sheafifiedYoneda JX).map φ ≫ isoPi.inv := by
    rw [smallEtaleStageComparison_eq, smallEtaleSheafPullbackCompIso'_eq]
    exact Sheaf.sheafPullbackComp'_hom_app_sheafifiedYoneda _ _ _ _ U
  have e1 : Sheaf.pullbackSheafifiedYonedaEquiv uh Ji Jj U TG b =
      Sheaf.sheafifiedYonedaEquiv Jj V TG b' := by
    have hb' : b = isoT.hom ≫ b' := (Iso.hom_inv_id_assoc _ _).symm
    exact (congrArg (Sheaf.pullbackSheafifiedYonedaEquiv uh Ji Jj U TG) hb').trans
      (Sheaf.sheafPullbackSheafifiedYonedaIso_hom_comp uh Ji Jj U TG b')
  have e2 : (adj.unit.app TG).hom.app (op V) (Sheaf.sheafifiedYonedaEquiv Jj V TG b') =
      Sheaf.pullbackSheafifiedYonedaEquiv uj Jj JX V (Pj.obj TG) (Pj.map b') := by
    have hn : b' ≫ adj.unit.app TG = adj.homEquiv _ _ (Pj.map b') := by
      rw [Adjunction.homEquiv_unit]
      exact adj.unit.naturality b'
    exact (Sheaf.sheafifiedYonedaEquiv_naturality Jj V (adj.unit.app TG) b').symm.trans
      (congrArg (Sheaf.sheafifiedYonedaEquiv Jj V _) hn)
  have e4 : (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom.hom.app _
      (Sheaf.pullbackSheafifiedYonedaEquiv uj Jj JX V (Pj.obj TG) (Pj.map b')) =
      Sheaf.pullbackSheafifiedYonedaEquiv uj Jj JX V PG
        (Pj.map b' ≫ (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom) :=
    (Sheaf.pullbackSheafifiedYonedaEquiv_naturality uj Jj JX V _ _).symm
  have e5 : Pj.map b' ≫ (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom =
      isoPj.hom ≫ (Sheaf.sheafifiedYoneda JX).map φ ≫ isoPi.inv ≫ a := by
    have hK' : isoPj.hom ≫ (Sheaf.sheafifiedYoneda JX).map φ ≫ isoPi.inv =
        Pj.map isoT.inv ≫ (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((Sheaf.sheafifiedYoneda Ji).obj U)).hom := by
      rw [hK, ← Pj.map_comp_assoc, Iso.inv_hom_id, Pj.map_id, Category.id_comp]
    rw [← hb, reassoc_of% hK', Iso.hom_inv_id_assoc, Pj.map_comp, Category.assoc]
  have e6 := Sheaf.sheafPullbackSheafifiedYonedaIso_hom_comp uj Jj JX V PG
    ((Sheaf.sheafifiedYoneda JX).map φ ≫ isoPi.inv ≫ a)
  have e7 := Sheaf.sheafifiedYonedaEquiv_naturality_obj JX φ PG (isoPi.inv ≫ a)
  have e8 : Sheaf.sheafifiedYonedaEquiv JX (ui.obj U) PG (isoPi.inv ≫ a) = s := by
    have ha : a = isoPi.hom ≫ isoPi.inv ≫ a := (Iso.hom_inv_id_assoc _ _).symm
    refine (Sheaf.sheafPullbackSheafifiedYonedaIso_hom_comp ui Ji JX U PG
      (isoPi.inv ≫ a)).symm.trans ?_
    refine (congrArg (Sheaf.pullbackSheafifiedYonedaEquiv ui Ji JX U PG) ha.symm).trans ?_
    exact Equiv.apply_symm_apply _ _
  change (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h G).hom.hom.app _
    ((adj.unit.app TG).hom.app (op V) (Sheaf.pullbackSheafifiedYonedaEquiv uh Ji Jj U TG b)) = _
  rw [e1, e2, e4]
  refine (congrArg (Sheaf.pullbackSheafifiedYonedaEquiv uj Jj JX V PG) e5).trans ?_
  refine e6.trans ?_
  refine e7.trans ?_
  rw [e8]

/-- **The presentation case.** Let `r₁, r₂ : R ⟶ H` be morphisms of quasi-compact
quasi-separated schemes étale over the stage `Xᵢ` of a directed limit `X = lim Xᵢ` of
quasi-compact quasi-separated schemes with affine transition morphisms, and let `G` be the
cokernel of the pair of morphisms `h_R ⇉ h_H` of represented sheaves. For every quasi-compact
quasi-separated `U` étale over `Xᵢ`, the canonical map `colim_{j ≥ i} Gⱼ(Uⱼ) ⟶ G|_X(U_X)` is
surjective. -/
@[weil "lem_fk104_sections_colimit_surjective"]
theorem exists_smallEtaleStageSectionsMap_eq_of_isColimit_cofork [Nonempty I]
    [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) {i : I}
    {R H : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property}
    (hR : IsQCQSEtaleObject B (Dg.obj (op i)) R) (hH : IsQCQSEtaleObject B (Dg.obj (op i)) H)
    (r₁ r₂ : R ⟶ H)
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (Type (u + 1))}
    (π : (Sheaf.sheafifiedYoneda (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property)).obj H ⟶ G)
    (w : (Sheaf.sheafifiedYoneda _).map r₁ ≫ π = (Sheaf.sheafifiedYoneda _).map r₂ ≫ π)
    (hπ : IsColimit (Cofork.ofπ π w))
    (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hU : IsQCQSEtaleObject B (Dg.obj (op i)) U)
    (s : ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.obj
      (op ((smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj U))) :
    ∃ (j : I) (h : i ≤ j)
      (t : ((smallEtaleStageTransition B (Type (u + 1)) Dg h).obj G).obj.obj
        (op ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj U))),
      smallEtaleStageSectionsMap B Dg c hX h G _ t =
        ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj G).obj.map
          ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
            (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
            (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h)).hom.app U).op s := by
  have : CompactSpace (Dg.obj (op i)).obj := hqc i
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  let : HasFiniteColimits (Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) (Type (u + 1))) := CategoryTheory.Sheaf.instHasFiniteColimits
  have hG : IsConstructibleSetSheaf B (Dg.obj (op i)) G := by
    refine isConstructibleSetSheaf_congr B _
      ((colimit.isColimit _).coconePointUniqueUpToIso hπ)
      (isConstructibleSetSheaf_colimit B _ _ ?_)
    rintro (_ | _)
    · have : CompactSpace R.obj.left.obj := hR.1
      have : QuasiSeparatedSpace R.obj.left.obj := hR.2
      exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B _ R
    · have : CompactSpace H.obj.left.obj := hH.1
      have : QuasiSeparatedSpace H.obj.left.obj := hH.2
      exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B _ H
  exact exists_smallEtaleStageSectionsMap_eq B Dg c hX hc haff hqc hqs G hG U hU s

end AlgebraicGeometry
