module

public import Weil.Attr
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Fibre products of sheaves of sets are computed sectionwise

Let `α : F ⟶ H` and `β : G ⟶ H` be morphisms of sheaves of sets on a site `(C, J)`. The
presheaf `P` with `P(U) = F(U) ×_{H(U)} G(U)`, with the restriction maps induced by those of
`F` and `G`, is a sheaf, and together with its two projections it is a fibre product
`F ×_H G` in the category of sheaves of sets.

The presheaf `P` with its projections is a pullback in the category of presheaves, since limits
of presheaves are computed sectionwise. A limit of sheaves computed in presheaves is a sheaf
(`CategoryTheory.Sheaf.isSheaf_of_isLimit`), and since the inclusion of sheaves into presheaves
is fully faithful it reflects limits, so the cone is also a pullback of sheaves.

## Main definitions

* `CategoryTheory.Sheaf.sectionwisePullback α β`: the presheaf `U ↦ F(U) ×_{H(U)} G(U)`.
* `CategoryTheory.Sheaf.sectionwisePullbackSheaf α β`: the same presheaf, as a sheaf.
* `CategoryTheory.Sheaf.sectionwisePullbackCone α β`: its two projections, as a pullback cone
  over `α` and `β` in sheaves.

## Main results

* `CategoryTheory.Sheaf.isSheaf_sectionwisePullback`: the presheaf `P` is a sheaf.
* `CategoryTheory.Sheaf.isLimitSectionwisePullbackCone`: `P` with its projections is a fibre
  product `F ×_H G` in the category of sheaves of sets.

## Implementation notes

The statement is proved for an arbitrary Grothendieck topology; the étale site of a scheme is a
special case.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G H : Sheaf J (Type w)} (α : F ⟶ H) (β : G ⟶ H)

/-- The presheaf of sectionwise fibre products `U ↦ F(U) ×_{H(U)} G(U)` of two morphisms of
sheaves of sets `α : F ⟶ H` and `β : G ⟶ H`, with the restriction maps induced by those of
`F` and `G`. -/
def sectionwisePullback : Cᵒᵖ ⥤ Type w where
  obj U := Types.PullbackObj (α.hom.app U) (β.hom.app U)
  map f := TypeCat.ofHom fun p => ⟨(F.obj.map f p.1.1, G.obj.map f p.1.2), by
    rw [← types_comp_apply (F.obj.map f) (α.hom.app _), ← types_comp_apply (G.obj.map f),
      α.hom.naturality, β.hom.naturality, types_comp_apply, types_comp_apply, p.2]⟩
  map_id U := by ext p <;> simp
  map_comp f g := by ext p <;> simp

/-- The first projection `P ⟶ F` of the sectionwise fibre product. -/
def sectionwisePullbackFst : sectionwisePullback α β ⟶ F.obj where
  app _ := TypeCat.ofHom fun p => p.1.1

/-- The second projection `P ⟶ G` of the sectionwise fibre product. -/
def sectionwisePullbackSnd : sectionwisePullback α β ⟶ G.obj where
  app _ := TypeCat.ofHom fun p => p.1.2

@[simp]
lemma sectionwisePullbackFst_app (U : Cᵒᵖ) (p : (sectionwisePullback α β).obj U) :
    (sectionwisePullbackFst α β).app U p = p.1.1 := rfl

@[simp]
lemma sectionwisePullbackSnd_app (U : Cᵒᵖ) (p : (sectionwisePullback α β).obj U) :
    (sectionwisePullbackSnd α β).app U p = p.1.2 := rfl

lemma sectionwisePullback_condition :
    sectionwisePullbackFst α β ≫ α.hom = sectionwisePullbackSnd α β ≫ β.hom := by
  ext U p
  exact p.2

/-- The sectionwise fibre product with its projections, as a pullback cone of presheaves. -/
def sectionwisePullbackPresheafCone : PullbackCone α.hom β.hom :=
  PullbackCone.mk _ _ (sectionwisePullback_condition α β)

/-- The sectionwise fibre product is a pullback in the category of presheaves. -/
def isLimitSectionwisePullbackPresheafCone :
    IsLimit (sectionwisePullbackPresheafCone α β) :=
  PullbackCone.IsLimit.mk (sectionwisePullback_condition α β)
    (fun s =>
      { app := fun U => TypeCat.ofHom fun t => ⟨(s.fst.app U t, s.snd.app U t),
          ConcreteCategory.congr_hom (NatTrans.congr_app s.condition U) t⟩
        naturality := fun U V f => by
          ext t
          refine Subtype.ext (Prod.ext ?_ ?_)
          · simp [sectionwisePullback]
          · simp [sectionwisePullback] })
    (fun s => rfl) (fun s => rfl)
    (fun s m h₁ h₂ => by
      ext U t
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact (ConcreteCategory.congr_hom (NatTrans.congr_app h₁ U) t).trans rfl
      · exact (ConcreteCategory.congr_hom (NatTrans.congr_app h₂ U) t).trans rfl)

/-- **The sectionwise fibre product of sheaves of sets is a sheaf.** -/
@[weil "lem_fk104_sheaf_fiber_product_sectionwise"]
theorem isSheaf_sectionwisePullback : Presheaf.IsSheaf J (sectionwisePullback α β) :=
  isSheaf_of_isLimit (cospan α β) _
    ((IsLimit.postcomposeInvEquiv (cospanCompIso (sheafToPresheaf J (Type w)) α β) _).symm
      (isLimitSectionwisePullbackPresheafCone α β))

/-- The sectionwise fibre product `U ↦ F(U) ×_{H(U)} G(U)`, as a sheaf. -/
def sectionwisePullbackSheaf : Sheaf J (Type w) :=
  ⟨sectionwisePullback α β, isSheaf_sectionwisePullback α β⟩

/-- The sectionwise fibre product with its two projections, as a pullback cone of sheaves. -/
def sectionwisePullbackCone : PullbackCone α β :=
  PullbackCone.mk (W := sectionwisePullbackSheaf α β)
    (ObjectProperty.homMk (sectionwisePullbackFst α β))
    (ObjectProperty.homMk (sectionwisePullbackSnd α β))
    (Sheaf.hom_ext (sectionwisePullback_condition α β))

/-- **The sectionwise fibre product of sheaves of sets, with its two projections, is a fibre
product `F ×_H G` in the category of sheaves of sets.** -/
@[weil "lem_fk104_sheaf_fiber_product_sectionwise"]
noncomputable def isLimitSectionwisePullbackCone : IsLimit (sectionwisePullbackCone α β) :=
  isLimitOfIsLimitPullbackConeMap (sheafToPresheaf J (Type w)) _
    (isLimitSectionwisePullbackPresheafCone α β)

end CategoryTheory.Sheaf
