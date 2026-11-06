module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import Weil.Attr

/-!
# Restriction of sections along a morphism of schemes

Let `h : T ⟶ S` be a morphism of schemes of a big étale site `B`, let `G` be a sheaf on the small
étale site of `S` (of abelian groups, or with values in any category `A` with the relevant
colimits and sheafification) and let `V` be an étale `S`-scheme, with base change
`V_T = T ×_S V`. The *restriction of sections* `r^h_{G,V} : G(V) ⟶ (h^* G)(V_T)` sends a section
`s` to the image, under the sheafification map `h⁻¹_pre G ⟶ h^* G`, of the class of `s` at the
index `(V, 𝟙 : V_T ⟶ V_T)` of the colimit defining `(h⁻¹_pre G)(V_T)`.

Equivalently, `r^h_{G,V}` is the component at `V` of the unit `G ⟶ h_* h^* G` of the adjunction
`h^* ⊣ h_*`, since `(h_* h^* G)(V) = (h^* G)(V_T)`. For `V = S` it gives the restriction of
global sections `r^h_G : G(S) ⟶ (h^* G)(T)`.

## Main definitions

* `AlgebraicGeometry.smallEtaleRestrictionOnSections` — `r^h_{G,V}`, the unit of
  `h^* ⊣ h_*` at `G`, evaluated at `V`.
* `AlgebraicGeometry.smallEtaleRestrictionOnGlobalSections` — `r^h_G : G(S) ⟶ (h^* G)(T)`.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionOnSections_eq` — `r^h_{G,V}` is the colimit injection
  at the index `(V, 𝟙)` followed by the sheafification map, transported along the identification
  `h^* G ≅ (h⁻¹_pre G)^#` (`AlgebraicGeometry.smallEtaleInverseImageObjIso`).

## Implementation notes

The definition is the unit of the adjunction `AlgebraicGeometry.smallEtaleInverseImageAdjunction`,
so that it is natural in `V` and in `G` as the component of a natural transformation; the
description by the colimit is `AlgebraicGeometry.smallEtaleRestrictionOnSections_eq`. The values
are in a general category `A`; for `A = AddCommGrpCat` a morphism is a group homomorphism. The
global version uses the canonical identification of the base change of the final object `S / S` with
the final object `T / T`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [Stacks Project, Tag 03Q0](https://stacks.math.columbia.edu/tag/03Q0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (h : T ⟶ S)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **Restriction of sections** `r^h_{G,V} : G(V) ⟶ (h^* G)(T ×_S V)` for a sheaf `G` on the small
étale site of `S` and an étale `S`-scheme `V`: the unit `G ⟶ h_* h^* G` of the adjunction
`h^* ⊣ h_*`, evaluated at `V`. Its description through the inverse image presheaf is
`smallEtaleRestrictionOnSections_eq`. -/
@[weil "def_fk106_restriction_on_sections"]
def smallEtaleRestrictionOnSections (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (V : SmallEtale B S.obj S.property) :
    G.obj.obj (op V) ⟶
      ((smallEtaleInverseImage B h A).obj G).obj.obj (op ((smallEtaleBaseChange B h).obj V)) :=
  ((smallEtaleInverseImageAdjunction B h A).unit.app G).hom.app (op V)

/-- **The description of `r^h_{G,V}` by the inverse image presheaf.** The restriction of
sections is the class of a section at the index `(V, 𝟙)` of the colimit defining
`(h⁻¹_pre G)(T ×_S V)`, followed by the sheafification map `h⁻¹_pre G ⟶ (h⁻¹_pre G)^#` and the
identification `(h⁻¹_pre G)^# ≅ h^* G`. -/
@[weil "def_fk106_restriction_on_sections"]
theorem smallEtaleRestrictionOnSections_eq
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) (V : SmallEtale B S.obj S.property) :
    smallEtaleRestrictionOnSections B h A G V =
      colimit.ι ((StructuredArrow.proj ((smallEtaleBaseChange B h).obj V)
          (smallEtaleBaseChange B h)).op ⋙ G.obj)
          (op (StructuredArrow.mk (𝟙 ((smallEtaleBaseChange B h).obj V)))) ≫
        (smallEtaleInverseImagePresheafObjIsoColimit B h A G.obj
          ((smallEtaleBaseChange B h).obj V)).inv ≫
        (toSheafify (SmallEtale.topology B T.obj T.property)
          ((smallEtaleInverseImagePresheaf B h A).obj G.obj)).app
            (op ((smallEtaleBaseChange B h).obj V)) ≫
        (smallEtaleInverseImageObjIso B h A G).inv.hom.app
          (op ((smallEtaleBaseChange B h).obj V)) := by
  rw [ι_smallEtaleInverseImagePresheafObjIsoColimit_inv_assoc]
  have key := (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B h) A
      (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).unit_leftAdjointUniq_hom_app
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange B h) A
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) G
  have key' := congrArg (fun φ => φ.hom.app (op V)) key
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at key'
  have hid : ((smallEtaleInverseImageObjIso B h A G).hom.hom.app
        (op ((smallEtaleBaseChange B h).obj V))) ≫
      (smallEtaleInverseImageObjIso B h A G).inv.hom.app
        (op ((smallEtaleBaseChange B h).obj V)) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id]
    rfl
  have e : ((smallEtaleBaseChange B h).op.lanUnit.app G.obj).app
        (op (StructuredArrow.mk (𝟙 ((smallEtaleBaseChange B h).obj V))).right) ≫
      ((smallEtaleInverseImagePresheaf B h A).obj G.obj).map
          (StructuredArrow.mk (𝟙 ((smallEtaleBaseChange B h).obj V))).hom.op ≫
        (toSheafify (SmallEtale.topology B T.obj T.property)
          ((smallEtaleInverseImagePresheaf B h A).obj G.obj)).app
            (op ((smallEtaleBaseChange B h).obj V)) =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange B h) A
        (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).unit.app G).hom.app (op V) := by
    change _ = ((sheafToPresheaf (SmallEtale.topology B S.obj S.property) A).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange B h) A
        (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).unit.app G)).app (op V)
    rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    erw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Functor.id_obj, ObjectProperty.ι_obj, Functor.comp_obj, StructuredArrow.mk_right,
      Functor.whiskeringLeft_obj_obj, Functor.op_obj, StructuredArrow.mk_hom_eq_self, op_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.comp_unit_app,
      Functor.lanAdjunction_unit, sheafificationAdjunction_unit_app,
      Functor.whiskeringLeft_obj_map, Iso.refl_hom, NatTrans.id_app, Category.assoc,
      NatTrans.comp_app, Functor.whiskerLeft_app]
    congr 1
    have gen : ∀ {a b : A} (f : a ⟶ b) (g : b ⟶ b), g = 𝟙 b → f = f ≫ g := by
      rintro _ _ f g rfl; simp
    refine gen _ _ ?_
    exact Category.id_comp (𝟙 _)
  rw [reassoc_of% e]
  refine (Category.comp_id _).symm.trans ?_
  refine (congrArg (smallEtaleRestrictionOnSections B h A G V ≫ ·) hid.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) key'

/-- **Restriction of global sections** `r^h_G : G(S) ⟶ (h^* G)(T)`: the restriction of sections
`smallEtaleRestrictionOnSections` at the final object `S / S`, followed by restriction along the
canonical identification of `T` with the base change `T ×_S S`. -/
@[weil "def_fk106_restriction_on_sections"]
def smallEtaleRestrictionOnGlobalSections
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    G.obj.obj (op (SmallEtale.final B S.obj S.property)) ⟶
      ((smallEtaleInverseImage B h A).obj G).obj.obj (op (SmallEtale.final B T.obj T.property)) :=
  smallEtaleRestrictionOnSections B h A G (SmallEtale.final B S.obj S.property) ≫
    ((smallEtaleInverseImage B h A).obj G).obj.map
      ((smallEtaleBaseChange_finalIsTerminal B h).from (SmallEtale.final B T.obj T.property)).op

end AlgebraicGeometry

end
