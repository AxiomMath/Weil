module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Preadditive.Biproducts

/-!
# The canonical functor to the Artin–Rees category is an additive functor

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules and
`q : 𝒫 ⥤ AR` the canonical functor to the Artin–Rees category, `q(f) = [0, f]`. Then `q` is an
additive functor: `q(g ∘ f) = q(g) ∘ q(f)`, `q(id_F) = id_F` and `q(f + g) = q(f) + q(g)`.

## Main results

* `CategoryTheory.ProjectiveSystem.toArCategory_map_comp`: `q(g ∘ f) = q(g) ∘ q(f)`.
* `CategoryTheory.ProjectiveSystem.toArCategory_map_id`: `q(id_F) = id_F`.
* `CategoryTheory.ProjectiveSystem.toArCategory_map_add`: `q(f + g) = q(f) + q(g)`.
* `CategoryTheory.ProjectiveSystem.toArCategory_map_neg`,
  `CategoryTheory.ProjectiveSystem.toArCategory_map_sub`,
  `CategoryTheory.ProjectiveSystem.toArCategory_map_zero`: consequences for negatives,
  differences and zero morphisms.

## Implementation notes

The additivity of `q` is the instance `CategoryTheory.ProjectiveSystem.toArCategory_additive`
(`Functor.Additive`); the lemmas here state its content on morphisms.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ} {F G H : ProjectiveSystem.{v} Λ l}

/-- **`q` respects composition**: `q(g ∘ f) = q(g) ∘ q(f)`. -/
@[weil "lem_fk112_ar_canonical_functor_additive"]
theorem toArCategory_map_comp (f : F ⟶ G) (g : G ⟶ H) :
    (toArCategory Λ l).map (f ≫ g) = (toArCategory Λ l).map f ≫ (toArCategory Λ l).map g :=
  (toArCategory Λ l).map_comp f g

/-- **`q` respects identities**: `q(id_F) = id_F`. -/
@[weil "lem_fk112_ar_canonical_functor_additive"]
theorem toArCategory_map_id (F : ProjectiveSystem.{v} Λ l) :
    (toArCategory Λ l).map (𝟙 F) = 𝟙 ((toArCategory Λ l).obj F) :=
  (toArCategory Λ l).map_id F

/-- **`q` is additive**: `q(f + g) = q(f) + q(g)`. -/
@[weil "lem_fk112_ar_canonical_functor_additive"]
theorem toArCategory_map_add (f g : F ⟶ G) :
    (toArCategory Λ l).map (f + g) = (toArCategory Λ l).map f + (toArCategory Λ l).map g :=
  (toArCategory Λ l).map_add

/-- `q(-f) = -q(f)`. -/
lemma toArCategory_map_neg (f : F ⟶ G) :
    (toArCategory Λ l).map (-f) = -(toArCategory Λ l).map f :=
  (toArCategory Λ l).map_neg

/-- `q(f - g) = q(f) - q(g)`. -/
lemma toArCategory_map_sub (f g : F ⟶ G) :
    (toArCategory Λ l).map (f - g) = (toArCategory Λ l).map f - (toArCategory Λ l).map g :=
  (toArCategory Λ l).map_sub

/-- `q(0) = 0`. -/
lemma toArCategory_map_zero :
    (toArCategory Λ l).map (0 : F ⟶ G) = 0 :=
  (toArCategory Λ l).map_zero F G

end ProjectiveSystem

end CategoryTheory
