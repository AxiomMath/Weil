module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ArCategorySheaves
public import Weil.Attr

/-!
# The canonical functor to the Artin–Rees category of `l`-torsion sheaves

Let `P_S` be the category of projective systems of `l`-torsion sheaves on the small étale site
of a scheme `S`, and `AR_S` its Artin–Rees category, a preadditive category
(`AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.preadditive`). Sending a morphism
`f : F ⟶ G` of `P_S` to its class `[0, f]` at level `0` (that is, `[0, f ∘ ε_0^F]`) is an additive
functor `P_S ⥤ AR_S`. For every `F` and `r ≥ 0`, the image of the natural morphism
`ε_r^F : F[r] ⟶ F` is an isomorphism of `AR_S`, whose inverse is the class `[r, id]` of the
identity of `F[r]` in `Hom_AR(F, F[r])`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.toAr`: the functor `P_S ⥤ AR_S`,
  `f ↦ [0, f ∘ ε_0]`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.shiftιIso F r`: the isomorphism
  `F[r] ≅ F` of `AR_S` whose morphism is the image of `ε_r^F`.

## Main results

* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.toAr_additive`: the functor is additive.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.shiftιIso_hom`,
  `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.shiftιIso_inv`: the morphism of the
  isomorphism is the image of `ε_r^F`, its inverse is `[r, id]`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.isIso_toAr_map_shiftι`: the image of
  `ε_r^F` is an isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem

open LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

variable (B S hS l) in
/-- **The canonical functor `P_S ⥤ AR_S`**: a morphism `f : F ⟶ G` of projective systems of
`l`-torsion sheaves goes to its class `[0, f]` at level `0`, that is `[0, f ∘ ε_0^F]`, where
`ε_0^F : F[0] ⟶ F` identifies `F[0]` with `F`. -/
@[weil "lem_fk112_ar_category_sheaves_well_defined"]
def toAr : LTorsionProjectiveSystem.{w} B S hS l ⥤ ArLTorsionProjectiveSystem.{w} B S hS l where
  obj := of
  map {F G} f := homMk 0 ((shiftι B S hS l 0).app F ≫ f)
  map_id F := (congrArg (homMk 0) (Category.comp_id _)).trans (id_eq F).symm
  map_comp {F G H} f g := by
    rw [homMk_comp_homMk, shiftι_naturality_assoc, shiftShift_comp_shiftι_zero_assoc,
      homMk_shiftMap_comp, Category.assoc]

lemma toAr_obj (F : LTorsionProjectiveSystem.{w} B S hS l) : (toAr B S hS l).obj F = of F :=
  rfl

lemma toAr_map {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G) :
    (toAr B S hS l).map f = homMk 0 ((shiftι B S hS l 0).app F ≫ f) :=
  rfl

/-- The canonical functor `P_S ⥤ AR_S` is additive. -/
@[weil "lem_fk112_ar_category_sheaves_well_defined"]
instance toAr_additive : (toAr.{w} B S hS l).Additive where
  map_add {F G f g} := by
    have h := homMk_add_homMk 0 le_rfl le_rfl ((shiftι B S hS l 0).app F ≫ f)
      ((shiftι B S hS l 0).app F ≫ g)
    rw [shiftMap_refl, Category.id_comp, Category.id_comp, ← Preadditive.comp_add] at h
    exact h.symm

/-- The class `[t, ε_t^F]` is the identity of `F` in the A–R category. -/
lemma homMk_shiftι_app (F : LTorsionProjectiveSystem.{w} B S hS l) (t : ℕ) :
    homMk t ((shiftι B S hS l t).app F) = 𝟙 (of F) := by
  rw [id_eq, ← shiftMap_comp_shiftι F (Nat.zero_le t), homMk_shiftMap_comp]

/-- Shifting `ε_r^F` by `r` gives `ε_r^{F[r]}`. -/
lemma shift_map_shiftι_app (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    (shift B S hS l (r : ℤ)).map ((shiftι B S hS l r).app F) =
      (shiftι B S hS l r).app ((shift B S hS l (r : ℤ)).obj F) :=
  hom_ext fun _ => rfl

/-- **The natural morphism `ε_r^F : F[r] ⟶ F` is an isomorphism of the A–R category**: its image
`[0, ε_r^F]` under the canonical functor has inverse `[r, id_{F[r]}] : F ⟶ F[r]`. -/
@[weil "lem_fk112_ar_category_sheaves_well_defined"]
def shiftιIso (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    of ((shift B S hS l (r : ℤ)).obj F) ≅ of F where
  hom := (toAr B S hS l).map ((shiftι B S hS l r).app F)
  inv := homMk r (𝟙 _)
  hom_inv_id := by
    change homMk 0 _ ≫ homMk r _ = _
    rw [homMk_comp_homMk, Functor.map_comp, Category.assoc,
      shiftShift_comp_shift_map_shiftι_zero_assoc, Category.comp_id, shift_map_shiftι_app,
      shiftMap_comp_shiftι, homMk_shiftι_app]
  inv_hom_id := by
    change homMk r _ ≫ homMk 0 _ = _
    rw [homMk_comp_homMk, CategoryTheory.Functor.map_id, Category.id_comp,
      shiftShift_comp_shiftι_zero_assoc, shiftMap_comp_shiftι, homMk_shiftι_app]

@[weil "lem_fk112_ar_category_sheaves_well_defined"]
lemma shiftιIso_hom (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    (shiftιIso F r).hom = (toAr B S hS l).map ((shiftι B S hS l r).app F) :=
  rfl

@[weil "lem_fk112_ar_category_sheaves_well_defined"]
lemma shiftιIso_inv (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    (shiftιIso F r).inv = homMk r (𝟙 ((shift B S hS l (r : ℤ)).obj F)) :=
  rfl

/-- The image of `ε_r^F : F[r] ⟶ F` in the A–R category is an isomorphism. -/
@[weil "lem_fk112_ar_category_sheaves_well_defined"]
instance isIso_toAr_map_shiftι (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    IsIso ((toAr B S hS l).map ((shiftι B S hS l r).app F)) :=
  (shiftιIso F r).isIso_hom

end AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem

end
