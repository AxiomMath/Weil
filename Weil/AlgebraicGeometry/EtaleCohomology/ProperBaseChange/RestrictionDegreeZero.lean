module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DegreeZeroTerminal
public import Weil.AlgebraicGeometry.EtaleCohomology.RestrictionOnSections
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.Attr

/-!
# The restriction map on étale cohomology in degree zero

Let `h : Y ⟶ X` be a morphism of schemes of a big étale site and `F` an abelian sheaf on the
small étale site of `X`. Under the identifications `H⁰(X, F) ≅ F(X)` and
`H⁰(Y, h^* F) ≅ (h^* F)(Y)` of degree-zero cohomology with sections over the final objects
(`CategoryTheory.Sheaf.H.equiv₀`), the restriction map
`h^* : H⁰(X, F) ⟶ H⁰(Y, h^* F)` (`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`) is the
restriction of global sections `r^h_F : F(X) ⟶ (h^* F)(Y)`
(`AlgebraicGeometry.smallEtaleRestrictionOnGlobalSections`).

A degree-zero class is a morphism `φ : ℤ_X ⟶ F`, and its image in `F(X)` is `φ` evaluated at the
section `1` of `ℤ_X` over the final object. Its restriction is `c⁻¹ ≫ h^* φ`, with
`c : h^* ℤ_X ≅ ℤ_Y` the canonical isomorphism. The statement then reduces, by naturality of the
restriction of sections in the sheaf, to the case `F = ℤ_X`, `φ = 𝟙`: the section `1` of `ℤ_Y`
corresponds under `c` to the restriction of the section `1` of `ℤ_X`. That holds because `c` is
built from the uniqueness of left adjoints of sections over a final object, which matches the
units of the two adjunctions.

## Main results

* `AlgebraicGeometry.constantSheafAdj_unit_comp_smallEtaleInverseImageConstantSheafIso_inv`:
  the isomorphism `h^* M_X ≅ M_Y` carries the canonical section of `M_Y` over the base change of
  the final object to the restriction of the canonical section of `M_X`.
* `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_zero_equiv₀`: in degree zero the
  restriction map on cohomology is the restriction of global sections.

## Implementation notes

The cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ`, and
the restriction map is the action of the exact inverse image on `Ext`; the statement is proved
directly from these definitions, without injective resolutions. The identification of
`smallEtaleCohomologyRestrictionMap` with the map induced by a restriction datum of injective
resolutions is `AlgebraicGeometry.smallEtaleRestrictionHomologyMap_comp_homologyIso_hom`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (h : Y ⟶ X)

/-- **The inverse image of a constant sheaf on sections.** The isomorphism
`h^* M_X ≅ M_Y` (`smallEtaleInverseImageConstantSheafIso`) carries the canonical map
`M ⟶ M_Y(T')`, over the base change `T'` of the final object of the small étale site of `X`, to
the canonical map `M ⟶ M_X(X)` followed by the restriction of sections `r^h`. -/
@[reassoc]
theorem constantSheafAdj_unit_comp_smallEtaleInverseImageConstantSheafIso_inv
    (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
    [HasWeakSheafify (SmallEtale.topology B Y.obj Y.property) A] (M : A) :
    (constantSheafAdj (SmallEtale.topology B Y.obj Y.property) A
        (smallEtaleBaseChange_finalIsTerminal B h)).unit.app M ≫
      (smallEtaleInverseImageConstantSheafIso B h A M).inv.hom.app
        (op ((smallEtaleBaseChange B h).obj (SmallEtale.final B X.obj X.property))) =
    (constantSheafAdj (SmallEtale.topology B X.obj X.property) A
        (SmallEtale.finalIsTerminal B X.obj X.property)).unit.app M ≫
      smallEtaleRestrictionOnSections B h A
        ((constantSheaf (SmallEtale.topology B X.obj X.property) A).obj M)
        (SmallEtale.final B X.obj X.property) := by
  simp only [smallEtaleInverseImageConstantSheafIso, constantSheafCompSmallEtaleInverseImageIso,
    Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso, Iso.app_inv, Iso.symm_inv]
  refine (Adjunction.unit_leftAdjointUniq_hom_app _ _ M).trans ?_
  simp only [smallEtaleRestrictionOnSections, Functor.id_obj, Functor.comp_obj,
    Functor.flip_obj_obj, ObjectProperty.ι_obj, Functor.op_obj, Iso.op_refl, Iso.refl_symm,
    Functor.mapIso_refl, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, Functor.flip_obj_map, ObjectProperty.ι_map,
    Functor.whiskerLeft_app, Category.assoc]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- **Restriction in degree zero is the restriction of global sections.** For a morphism
`h : Y ⟶ X` of schemes of a big étale site and an abelian sheaf `F` on the small étale site of
`X`, under the identifications `H⁰(X, F) ≅ F(X)` and `H⁰(Y, h^* F) ≅ (h^* F)(Y)`
(`CategoryTheory.Sheaf.H.equiv₀` at the final objects), the restriction map
`h^* : H⁰(X, F) ⟶ H⁰(Y, h^* F)` is the restriction of global sections `r^h_F`. -/
@[weil "lem_fk106_cohomology_restriction_degree_zero"]
theorem smallEtaleCohomologyRestrictionMap_zero_equiv₀
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (x : Sheaf.H.{w} F 0) :
    Sheaf.H.equiv₀ ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F)
        (SmallEtale.finalIsTerminal B Y.obj Y.property)
        (smallEtaleCohomologyRestrictionMap B h F 0 x) =
      smallEtaleRestrictionOnGlobalSections B h AddCommGrpCat.{u + 1} F
        (Sheaf.H.equiv₀ F (SmallEtale.finalIsTerminal B X.obj X.property) x) := by
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  have hR : smallEtaleCohomologyRestrictionMap B h F 0 (Ext.mk₀ φ) =
      Ext.mk₀ ((smallEtaleInverseImageConstantSheafIso B h AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift ℤ))).inv ≫
          (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ) := by
    rw [smallEtaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  rw [hR, Sheaf.H.equiv₀_mk₀, Sheaf.H.equiv₀_mk₀]
  have key : (constantSheafAdj (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}
        (SmallEtale.finalIsTerminal B Y.obj Y.property)).unit.app (AddCommGrpCat.of (ULift ℤ)) ≫
        ((smallEtaleInverseImageConstantSheafIso B h AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift ℤ))).inv ≫
            (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ).hom.app
          (op (SmallEtale.final B Y.obj Y.property)) =
      (constantSheafAdj (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
        (SmallEtale.finalIsTerminal B X.obj X.property)).unit.app (AddCommGrpCat.of (ULift ℤ)) ≫
        φ.hom.app (op (SmallEtale.final B X.obj X.property)) ≫
          smallEtaleRestrictionOnGlobalSections B h AddCommGrpCat.{u + 1} F := by
    rw [← constantSheafAdj_unit_app_comp_map (smallEtaleBaseChange_finalIsTerminal B h)
      (SmallEtale.finalIsTerminal B Y.obj Y.property)]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    rw [Category.assoc, (smallEtaleInverseImageConstantSheafIso B h AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift ℤ))).inv.hom.naturality_assoc]
    have e := constantSheafAdj_unit_comp_smallEtaleInverseImageConstantSheafIso_inv
      B h AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift ℤ))
    rw [reassoc_of% e, ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ).hom.naturality]
    have e' := smallEtaleRestrictionOnSections_naturality_sheaf B h AddCommGrpCat.{u + 1} φ
      (SmallEtale.final B X.obj X.property)
    rw [reassoc_of% e']
    rfl
  have hk := ConcreteCategory.congr_hom key (ULift.up 1)
  simp only [ConcreteCategory.comp_apply] at hk
  exact hk

end AlgebraicGeometry

end
