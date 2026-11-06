module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ArCategory

/-!
# The canonical functor to the Artin–Rees category

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules. The *canonical
functor* `q : 𝒫 ⥤ AR` to the Artin–Rees category is the identity on objects and sends a
morphism `f : F ⟶ G` of `𝒫` to the A–R morphism `q(f) = [0, f]`, the class of `f` viewed as a
morphism `F[0] ⟶ G` through the canonical identification `ε⁰_F : F[0] ⟶ F`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.toArCategory Λ l`: the canonical functor `q`.

## Main results

* `CategoryTheory.ProjectiveSystem.toArCategory_obj`: `q(F)` is `F`.
* `CategoryTheory.ProjectiveSystem.toArCategory_map`: `q(f) = [0, f ∘ ε⁰_F]`.
* `CategoryTheory.ProjectiveSystem.toArCategory_map_eq_homMk_shiftZero`:
  `q(f) = [0, f ∘ (F[0] ≅ F)]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_zero_eq_toArCategory_map`: every A–R morphism
  `[0, g]` is `q(g ∘ (F ≅ F[0]))`.

## Implementation notes

The shifted system `F[0]` is not definitionally `F`, so the representative of `q(f)` is
`f ∘ ε⁰_F : F[0] ⟶ G`, with `ε⁰_F = natMap F 0` the canonical identification
(`natMap_zero`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable (Λ : Type u) [CommRing Λ] (l : Λ)

/-- The *canonical functor* `q` from projective systems to the Artin–Rees category: the identity
on objects, sending `f : F ⟶ G` to the A–R morphism `[0, f]`, whose representative is
`f ∘ ε⁰_F : F[0] ⟶ G`. -/
@[weil "def_fk112_ar_canonical_functor"]
def toArCategory : ProjectiveSystem.{v} Λ l ⥤ ArCategory.{v} Λ l where
  obj F := ArCategory.of F
  map {F _} f := ArCategory.homMk 0 (natMap F 0 ≫ f)
  map_id F := by
    rw [Category.comp_id]
    exact (ArCategory.id_eq F).symm
  map_comp {F G _} f g := by
    rw [ArCategory.homMk_comp_homMk, Functor.map_comp, Category.assoc, natMap_naturality_assoc,
      natMap_naturality_assoc, shiftShift_comp_natMap_zero_assoc, ArCategory.homMk_shiftMap_comp]

variable {Λ l}

@[simp]
lemma toArCategory_obj (F : ProjectiveSystem.{v} Λ l) :
    (toArCategory Λ l).obj F = ArCategory.of F := rfl

/-- `q(f) = [0, f ∘ ε⁰_F]`. -/
lemma toArCategory_map {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) :
    (toArCategory Λ l).map f = ArCategory.homMk 0 (natMap F 0 ≫ f) := rfl

/-- `q(f) = [0, f ∘ (F[0] ≅ F)]`. -/
lemma toArCategory_map_eq_homMk_shiftZero {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) :
    (toArCategory Λ l).map f = ArCategory.homMk 0 (shiftZero.hom.app F ≫ f) := by
  rw [toArCategory_map, natMap_zero]

/-- Every A–R morphism `[0, g]` with `g : F[0] ⟶ G` is the image under `q` of
`g ∘ (F ≅ F[0])`. -/
lemma ArCategory.homMk_zero_eq_toArCategory_map {F G : ProjectiveSystem.{v} Λ l}
    (g : (shift ((0 : ℕ) : ℤ)).obj F ⟶ G) :
    ArCategory.homMk 0 g = (toArCategory Λ l).map (shiftZero.inv.app F ≫ g) := by
  rw [toArCategory_map_eq_homMk_shiftZero]
  exact congrArg _ (Iso.hom_inv_id_app_assoc shiftZero F g).symm

end ProjectiveSystem

end CategoryTheory
