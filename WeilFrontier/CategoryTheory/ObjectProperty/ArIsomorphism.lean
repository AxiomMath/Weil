module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.ObjectProperty.ShiftNaturalMap
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArCanonicalFunctor
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArIsomorphism

/-!
# The natural map of a shifted system is an Artin–Rees isomorphism

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules, `AR` its
Artin–Rees category and `q : 𝒫 ⥤ AR` the canonical functor. For `F` in `𝒫` and `r ≥ 0`, the
natural map `ε^r_F : F[r] ⟶ F` becomes an isomorphism `q(ε^r_F) : F[r] ⟶ F` of the A–R category,
whose inverse is the class `[r, id_{F[r]}] : F ⟶ F[r]`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.natMapArIso F r`: the A–R isomorphism `F[r] ≅ F` with
  `hom = q(ε^r_F)` and `inv = [r, id_{F[r]}]`.

## Main results

* `CategoryTheory.ProjectiveSystem.shift_map_natMap`: `ε^r_F[r] = ε^r_{F[r]}`.
* `CategoryTheory.ProjectiveSystem.isIso_toArCategory_map_natMap`: `q(ε^r_F)` is an isomorphism
  of the A–R category.
* `CategoryTheory.ProjectiveSystem.inv_toArCategory_map_natMap`: its inverse is
  `[r, id_{F[r]}]`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The shift of the natural map is the natural map of the shift: `ε^r_F[r] = ε^r_{F[r]}`, both
morphisms `F[r][r] ⟶ F[r]`. -/
lemma shift_map_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (shift (r : ℤ)).map (natMap F r) = natMap ((shift (r : ℤ)).obj F) r :=
  hom_ext fun n => by
    rw [shift_map_app, natMap_app, natMap_app]
    exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The A–R isomorphism `F[r] ≅ F` given by the natural map: its morphism is `q(ε^r_F)` and its
inverse is `[r, id_{F[r]}]`. -/
noncomputable def natMapArIso (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    ArCategory.of ((shift (r : ℤ)).obj F) ≅ ArCategory.of F where
  hom := (toArCategory Λ l).map (natMap F r)
  inv := ArCategory.homMk r (𝟙 ((shift (r : ℤ)).obj F))
  hom_inv_id := by
    rw [toArCategory_map, ArCategory.homMk_comp_homMk, Category.comp_id, Functor.map_comp,
      shiftShift_comp_shift_map_natMap_zero_assoc, ArCategory.homMk_shiftMap_comp,
      shift_map_natMap, ArCategory.homMk_natMap]
  inv_hom_id := by
    rw [toArCategory_map, ArCategory.homMk_comp_homMk, Functor.map_id, Category.id_comp,
      shiftShift_comp_natMap_zero_assoc, ArCategory.homMk_shiftMap_comp,
      ArCategory.homMk_natMap]

@[simp]
lemma natMapArIso_hom (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (natMapArIso F r).hom = (toArCategory Λ l).map (natMap F r) := rfl

@[simp]
lemma natMapArIso_inv (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (natMapArIso F r).inv = ArCategory.homMk r (𝟙 ((shift (r : ℤ)).obj F)) := rfl

/-- For `r ≥ 0`, the image `q(ε^r_F) : F[r] ⟶ F` of the natural map under the canonical functor
is an isomorphism of the A–R category. -/
@[weil "lem_fk112_shift_map_ar_isomorphism"]
instance isIso_toArCategory_map_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    IsIso ((toArCategory Λ l).map (natMap F r)) :=
  (natMapArIso F r).isIso_hom

/-- The inverse of the A–R isomorphism `q(ε^r_F) : F[r] ⟶ F` is the class
`[r, id_{F[r]}] : F ⟶ F[r]`. -/
@[weil "lem_fk112_shift_map_ar_isomorphism"]
theorem inv_toArCategory_map_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    inv ((toArCategory Λ l).map (natMap F r)) =
      ArCategory.homMk r (𝟙 ((shift (r : ℤ)).obj F)) :=
  IsIso.inv_eq_of_hom_inv_id (natMapArIso F r).hom_inv_id

end ProjectiveSystem

end CategoryTheory
