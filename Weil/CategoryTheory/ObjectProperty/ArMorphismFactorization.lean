module

public import Weil.Attr
public import Weil.CategoryTheory.ObjectProperty.ArIsomorphism

/-!
# Factorization of Artin–Rees morphisms

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules, `AR` its
Artin–Rees category and `q : 𝒫 ⥤ AR` the canonical functor. Every A–R morphism
`φ : F ⟶ G` is of the form `φ = q(f) ∘ [r, id_{F[r]}] = q(f) ∘ q(ε^r_F)⁻¹` for some `r ≥ 0` and
some morphism `f : F[r] ⟶ G` of `𝒫`; namely for any representative `(r, f)` of `φ`.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_eq_homMk_id_comp_toArCategory_map`:
  `[r, f] = q(f) ∘ [r, id_{F[r]}]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_eq_inv_comp_toArCategory_map`:
  `[r, f] = q(f) ∘ q(ε^r_F)⁻¹`.
* `CategoryTheory.ProjectiveSystem.ArCategory.exists_eq_inv_comp_toArCategory_map`: every A–R
  morphism is `q(f) ∘ q(ε^r_F)⁻¹` for some `r` and `f : F[r] ⟶ G`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

namespace ArCategory

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- For any representative `(r, f)` of an A–R morphism, `[r, f] = q(f) ∘ [r, id_{F[r]}]`. -/
@[weil "lem_fk112_ar_morphism_factorization"]
theorem homMk_eq_homMk_id_comp_toArCategory_map {F G : ProjectiveSystem.{v} Λ l} (r : ℕ)
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    homMk r f = homMk r (𝟙 ((shift (r : ℤ)).obj F)) ≫ (toArCategory Λ l).map f := by
  change homMk r f = homMk r (𝟙 ((shift (r : ℤ)).obj F)) ≫
    homMk 0 (natMap ((shift (r : ℤ)).obj F) 0 ≫ f)
  rw [homMk_comp_homMk, Functor.map_id, Category.id_comp,
    shiftShift_comp_natMap_zero_assoc, homMk_shiftMap_comp]

/-- For any representative `(r, f)` of an A–R morphism, `[r, f] = q(f) ∘ q(ε^r_F)⁻¹`. -/
@[weil "lem_fk112_ar_morphism_factorization"]
theorem homMk_eq_inv_comp_toArCategory_map {F G : ProjectiveSystem.{v} Λ l} (r : ℕ)
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    homMk r f = inv ((toArCategory Λ l).map (natMap F r)) ≫ (toArCategory Λ l).map f := by
  rw [inv_toArCategory_map_natMap]
  exact homMk_eq_homMk_id_comp_toArCategory_map r f

/-- Every A–R morphism `φ : F ⟶ G` is `q(f) ∘ [r, id_{F[r]}] = q(f) ∘ q(ε^r_F)⁻¹` for some
`r ≥ 0` and some morphism `f : F[r] ⟶ G` of projective systems, with `φ = [r, f]`. -/
@[weil "lem_fk112_ar_morphism_factorization"]
theorem exists_eq_inv_comp_toArCategory_map {F G : ProjectiveSystem.{v} Λ l}
    (φ : of F ⟶ of G) :
    ∃ (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G), φ = homMk r f ∧
      φ = homMk r (𝟙 ((shift (r : ℤ)).obj F)) ≫ (toArCategory Λ l).map f ∧
      φ = inv ((toArCategory Λ l).map (natMap F r)) ≫ (toArCategory Λ l).map f := by
  obtain ⟨r, f, rfl⟩ := homMk_surjective φ
  exact ⟨r, f, rfl, homMk_eq_homMk_id_comp_toArCategory_map r f,
    homMk_eq_inv_comp_toArCategory_map r f⟩

end ArCategory

end ProjectiveSystem

end CategoryTheory
