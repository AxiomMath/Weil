module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.GermOfSection
public import Weil.Attr

/-!
# Germs of sections of the inverse image of an étale sheaf

Let `g : Y ⟶ X` be a morphism of schemes of a big étale site, `𝒢` a sheaf on the small étale
site of `X`, `V` étale over `Y`, `U` étale over `X`, and `h : V ⟶ U` a morphism of schemes with
`h ≫ π_U = π_V ≫ g`. A section `a ∈ 𝒢(U)` gives, through the class of `(U, h, a)` in the inverse
image presheaf `g⁻¹_pre 𝒢` and the canonical map to its sheafification, a section
`[a] ∈ (g^* 𝒢)(V)`.

For every geometric point `w̄` of `V`, the canonical isomorphism `𝒢_{g ∘ w̄} ≅ (g^* 𝒢)_{w̄}` of
stalks sends the germ of `a` at the étale neighbourhood `(U, h ∘ w̄)` of `g ∘ w̄` to the germ
`[a]_{w̄}`.

## Main definitions

* `AlgebraicGeometry.SmallEtaleInverseImageIndex.ofHom` — the object `(U, h)` of the index
  category of the inverse image presheaf attached to a morphism `h : V ⟶ U` over `g`.
* `AlgebraicGeometry.smallEtaleInverseImageClass` — the map `a ↦ [a]`, `𝒢(U) ⟶ (g^* 𝒢)(V)`.
* `AlgebraicGeometry.geometricPointLiftOfHom` — the lift `h ∘ w̄` of `g ∘ w̄` to `U`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageClass_eq_pullbackSectionAlongHom` — the map
  `a ↦ [a]` is the unit of the adjunction `g^* ⊣ g_*` at `U` followed by restriction along the
  morphism `V ⟶ Y ×_X U` given by `h`.
* `AlgebraicGeometry.smallEtaleInverseImageSheafFiberIso_hom_germ` — the stalk isomorphism
  `𝒢_{g ∘ w̄} ≅ (g^* 𝒢)_{w̄}` sends the germ of `a` at `(U, h ∘ w̄)` to `[a]_{w̄}`.

## Implementation notes

The étale sites are the small étale sites `AlgebraicGeometry.SmallEtale` of a big étale site,
and geometric points are spectra of algebraically closed fields. Sheaves of sets take values in
`Type (u + 1)`, the universe in which the small étale sites have the colimits defining the
inverse image presheaf; the map `a ↦ [a]` and its identification are stated for any coefficient
category. The germ of `a` is the germ at the étale neighbourhood `(U, h ∘ w̄)` of the geometric
point `g ∘ w̄`, read in the stalk `𝒢_{g ∘ w̄}`, which is where the stalk isomorphism starts.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (g : T ⟶ S)

namespace SmallEtaleInverseImageIndex

variable {B g}

/-- The object `(U, h)` of the index category `J_V` of the inverse image presheaf attached to a
morphism of schemes `h : V ⟶ U` with `h ≫ π_U = π_V ≫ g`. -/
abbrev ofHom {V : SmallEtale B T.obj T.property} {U : SmallEtale B S.obj S.property}
    (h : V.obj.left ⟶ U.obj.left) (hh : h ≫ U.obj.hom = V.obj.hom ≫ g) :
    SmallEtaleInverseImageIndex B g V :=
  StructuredArrow.mk ((smallEtaleHomBaseChangeEquiv B g V U).symm ⟨h, hh⟩)

end SmallEtaleInverseImageIndex

section Coefficients

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- The unit of the adjunction `g^* ⊣ g_*` built from the left Kan extension is the unit of the
Kan extension followed by the canonical map to the sheafification. -/
lemma sheafPullbackConstruction_unit_app_hom_app
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) (U : SmallEtale B S.obj S.property) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange B g) A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app G).hom.app (op U) =
    ((smallEtaleBaseChange B g).op.lanUnit.app G.obj).app (op U) ≫
      (toSheafify (SmallEtale.topology B T.obj T.property)
        ((smallEtaleInverseImagePresheaf B g A).obj G.obj)).app
          (op ((smallEtaleBaseChange B g).obj U)) := by
  change ((sheafToPresheaf _ A).map ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange B g) A (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).unit.app G)).app (op U) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  erw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.id_obj, ObjectProperty.ι_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    Adjunction.comp_unit_app, Functor.lanAdjunction_unit, sheafificationAdjunction_unit_app,
    Functor.whiskeringLeft_obj_map, Iso.refl_hom, NatTrans.id_app, Category.assoc,
    NatTrans.comp_app, Functor.op_obj, Functor.whiskerLeft_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, NatTrans.id_app, Category.comp_id]
  rfl

/-- The unit of the Kan extension, followed by the canonical map to the sheafification and the
identification `smallEtaleInverseImageObjIso`, is the unit of the adjunction `g^* ⊣ g_*`. -/
lemma lanUnit_app_comp_toSheafify_comp_smallEtaleInverseImageObjIso_inv
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) (U : SmallEtale B S.obj S.property) :
    ((smallEtaleBaseChange B g).op.lanUnit.app G.obj).app (op U) ≫
      (toSheafify (SmallEtale.topology B T.obj T.property)
        ((smallEtaleInverseImagePresheaf B g A).obj G.obj)).app
          (op ((smallEtaleBaseChange B g).obj U)) ≫
      (smallEtaleInverseImageObjIso B g A G).inv.hom.app (op ((smallEtaleBaseChange B g).obj U)) =
    ((smallEtaleInverseImageAdjunction B g A).unit.app G).hom.app (op U) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange B g) A
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property))
    (smallEtaleInverseImageAdjunction B g A) G
  have h' := congrArg (fun φ => φ.hom.app (op U)) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h'
  rw [← h', sheafPullbackConstruction_unit_app_hom_app]
  erw [Category.assoc]
  rfl

variable {B g A} in
/-- **The section `[a]` of the inverse image.** For a morphism of schemes `h : V ⟶ U` with
`h ≫ π_U = π_V ≫ g`, the map `𝒢(U) ⟶ (g^* 𝒢)(V)` sending `a` to the image of the class of
`(U, h, a)` in the inverse image presheaf `g⁻¹_pre 𝒢` under the canonical map to its
sheafification `g^* 𝒢`. -/
def smallEtaleInverseImageClass (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    {V : SmallEtale B T.obj T.property} {U : SmallEtale B S.obj S.property}
    (h : V.obj.left ⟶ U.obj.left) (hh : h ≫ U.obj.hom = V.obj.hom ≫ g) :
    G.obj.obj (op U) ⟶ ((smallEtaleInverseImage B g A).obj G).obj.obj (op V) :=
  colimit.ι ((StructuredArrow.proj V (smallEtaleBaseChange B g)).op ⋙ G.obj)
      (op (SmallEtaleInverseImageIndex.ofHom h hh)) ≫
    (smallEtaleInverseImagePresheafObjIsoColimit B g A G.obj V).inv ≫
    (toSheafify (SmallEtale.topology B T.obj T.property)
      ((smallEtaleInverseImagePresheaf B g A).obj G.obj)).app (op V) ≫
    (smallEtaleInverseImageObjIso B g A G).inv.hom.app (op V)

/-- The section `[a]` is obtained from `a` through the unit of the adjunction `g^* ⊣ g_*` at
`U`, followed by restriction along the morphism `V ⟶ Y ×_X U` determined by `h`. -/
lemma smallEtaleInverseImageClass_eq_pullbackSectionAlongHom
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    {V : SmallEtale B T.obj T.property} {U : SmallEtale B S.obj S.property}
    (h : V.obj.left ⟶ U.obj.left) (hh : h ≫ U.obj.hom = V.obj.hom ≫ g) :
    smallEtaleInverseImageClass G h hh =
      pullbackSectionAlongHom B g A G U V
        ((smallEtaleHomBaseChangeEquiv B g V U).symm ⟨h, hh⟩) := by
  set k := (smallEtaleHomBaseChangeEquiv B g V U).symm ⟨h, hh⟩
  rw [smallEtaleInverseImageClass, ι_smallEtaleInverseImagePresheafObjIsoColimit_inv_assoc]
  have h₁ := (toSheafify (SmallEtale.topology B T.obj T.property)
    ((smallEtaleInverseImagePresheaf B g A).obj G.obj)).naturality k.op
  have h₂ := (smallEtaleInverseImageObjIso B g A G).inv.hom.naturality k.op
  change _ ≫ _ ≫ _ ≫ _ = _
  erw [reassoc_of% h₁]
  erw [h₂]
  rw [← Category.assoc, ← Category.assoc, Category.assoc _ _
    ((smallEtaleInverseImageObjIso B g A G).inv.hom.app _)]
  erw [lanUnit_app_comp_toSheafify_comp_smallEtaleInverseImageObjIso_inv]
  rfl

end Coefficients

variable {B g} in
/-- The lift `h ∘ w̄` to `U` of the geometric point `g ∘ w̄` of `X`, for a geometric point `w̄` of
`V` and a morphism `h : V ⟶ U` over `g`: the étale neighbourhood `(U, h ∘ w̄)` of `g ∘ w̄`. -/
def geometricPointLiftOfHom {V : SmallEtale B T.obj T.property}
    {U : SmallEtale B S.obj S.property} (h : V.obj.left ⟶ U.obj.left)
    (hh : h ≫ U.obj.hom = V.obj.hom ≫ g)
    (w : GeometricPoint ((SmallEtale.toScheme B T.obj T.property).obj V)) :
    (geometricPointFiber B S.obj S.property
      ((SmallEtale.toBaseGeometricPoint V w).map (B.inclusion.map g))).obj U :=
  ⟨w.hom ≫ B.inclusion.map h, by
    simp only [GeometricPoint.map_hom, Category.assoc, ← Functor.map_comp, hh]⟩

/-- **Germs and the stalks of the inverse image.** Let `𝒢` be a sheaf of sets on the small
étale site of `X`, `h : V ⟶ U` a morphism over `g : Y ⟶ X` from an étale `Y`-scheme to an étale
`X`-scheme, `a ∈ 𝒢(U)` and `[a] ∈ (g^* 𝒢)(V)` its image (`smallEtaleInverseImageClass`). For
every geometric point `w̄` of `V`, the canonical isomorphism `𝒢_{g ∘ w̄} ≅ (g^* 𝒢)_{w̄}` sends
the germ of `a` at the étale neighbourhood `(U, h ∘ w̄)` of `g ∘ w̄` to the germ `[a]_{w̄}`. -/
@[weil "lem_fk103_inverse_image_germ_compatible"]
theorem smallEtaleInverseImageSheafFiberIso_hom_germ
    (G : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {V : SmallEtale B T.obj T.property} {U : SmallEtale B S.obj S.property}
    (h : V.obj.left ⟶ U.obj.left) (hh : h ≫ U.obj.hom = V.obj.hom ≫ g)
    (a : G.obj.obj (op U))
    (w : GeometricPoint ((SmallEtale.toScheme B T.obj T.property).obj V)) :
    (smallEtaleInverseImageSheafFiberIso B g (SmallEtale.toBaseGeometricPoint V w)
        (Type (u + 1))).hom.app G
      ((geometricPointSitePoint B S.obj S.property
        ((SmallEtale.toBaseGeometricPoint V w).map (B.inclusion.map g))).toPresheafFiber U
          (geometricPointLiftOfHom h hh w) G.obj a) =
      SmallEtale.germ ((smallEtaleInverseImage B g (Type (u + 1))).obj G).obj
        (smallEtaleInverseImageClass G h hh a) w := by
  have key := smallEtaleInverseImageSheafFiberIso_germ B g (SmallEtale.toBaseGeometricPoint V w)
    (Type (u + 1)) G ⟨V, SmallEtale.geometricPointLift V w⟩ ⟨U, geometricPointLiftOfHom h hh w⟩
    ((smallEtaleHomBaseChangeEquiv B g V U).symm ⟨h, hh⟩) (by
      have e : ((smallEtaleHomBaseChangeEquiv B g V U)
          ((smallEtaleHomBaseChangeEquiv B g V U).symm ⟨h, hh⟩)).1 = h := by
        rw [Equiv.apply_symm_apply]
      change w.hom ≫ _ = w.hom ≫ B.inclusion.map h
      refine congrArg (w.hom ≫ ·) ?_
      conv_rhs => rw [← e, smallEtaleHomBaseChangeEquiv_apply_coe]
      refine (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map ?_)
      rfl)
  rw [SmallEtale.germ_eq_colimit_ι, smallEtaleInverseImageClass_eq_pullbackSectionAlongHom]
  exact ConcreteCategory.congr_hom key a

end AlgebraicGeometry

end
