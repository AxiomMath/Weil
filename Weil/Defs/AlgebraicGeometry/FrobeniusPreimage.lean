module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
public import Weil.Defs.AlgebraicGeometry.Frobenius
public import Weil.Attr

/-!
# The Frobenius preimage of a scheme over a scheme over a finite field

Let `κ` be a finite field with `q` elements, `X` a scheme over `κ` and `Fr_X : X ⟶ X` its
Frobenius endomorphism with respect to `κ`. For a scheme `u : U ⟶ X` over `X`, the
*Frobenius preimage* `Fr_X⁻¹(U)` is the fibre product of `Fr_X` and `u`, that is, `X` considered
as a scheme over `X` through `Fr_X`, base changed to `U`. It is a scheme over `X` through the
projection to `X`, and it comes with the projection `Fr_X⁻¹(U) ⟶ U`. For a morphism
`h : U' ⟶ U` over `X`, the morphism `Fr_X⁻¹(h)` is `id_X × h`.

Thus `Fr_X⁻¹` is the pullback functor `Over X ⥤ Over X` along `Fr_X`. Writing `q = p ^ f`
with `p` the characteristic of `κ`, the Frobenius `Fr_X` is the `f`-fold absolute Frobenius of
`X`, so `Fr_X⁻¹(U)` is the `f`-fold Frobenius twist of `U` over `X` of the Stacks Project.

## Main definitions

* `AlgebraicGeometry.frobeniusPreimage κ X`: the functor `U ↦ Fr_X⁻¹(U)` on schemes over `X`.

## Main results

* `AlgebraicGeometry.frobeniusPreimage_obj_left`, `AlgebraicGeometry.frobeniusPreimage_obj_hom`:
  `Fr_X⁻¹(U)` is the fibre product of `u` and `Fr_X`, a scheme over `X` through the projection to
  `X`.
* `AlgebraicGeometry.frobeniusPreimage_map_left_fst`,
  `AlgebraicGeometry.frobeniusPreimage_map_left_snd`: `Fr_X⁻¹(h)` is `id_X × h`.
* `AlgebraicGeometry.frobeniusPreimage_obj_eq_nFoldFrobeniusTwist`: `Fr_X⁻¹(U)` is the
  `f`-fold Frobenius twist `AlgebraicGeometry.nFoldFrobeniusTwist` for `q = p ^ f`.

## Implementation notes

The fibre product is written `pullback u Fr_X`, with the factor `U` first, following Mathlib's
`CategoryTheory.Over.pullback`. Hence the projection `Fr_X⁻¹(U) ⟶ X` (the structure morphism)
is `pullback.snd` and the projection `Fr_X⁻¹(U) ⟶ U` is `pullback.fst`; in [FK] they are the
second and the first projection of `X ×_{Fr_X, X, u} U` respectively, with the factors in the
other order.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter II, §3, p. 163.
* [Stacks] The Stacks Project, Tags 0CC9 and 0CCG.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (κ : Type u) [Field κ] [Fintype κ] (X : Over (Spec (.of κ)))

/-- **The Frobenius preimage** `Fr_X⁻¹(U)` of a scheme `U` over a scheme `X` over the finite
field `κ`: the base change of `U ⟶ X` along the Frobenius `Fr_X` of `X` with respect to `κ`,
regarded as a scheme over `X` through the projection to `X`; on a morphism `h` over `X` it is
`id_X × h`. -/
@[weil "not_fk203_frobenius_preimage"]
noncomputable abbrev frobeniusPreimage : Over X.left ⥤ Over X.left :=
  Over.pullback (frobeniusOver κ X).left

variable {κ X}

/-- The underlying scheme of `Fr_X⁻¹(U)` is the fibre product of `U ⟶ X` and `Fr_X`. -/
@[weil "not_fk203_frobenius_preimage", simp]
lemma frobeniusPreimage_obj_left (U : Over X.left) :
    ((frobeniusPreimage κ X).obj U).left = pullback U.hom (frobeniusOver κ X).left :=
  rfl

/-- `Fr_X⁻¹(U)` is a scheme over `X` through the projection to `X`. -/
@[weil "not_fk203_frobenius_preimage", simp]
lemma frobeniusPreimage_obj_hom (U : Over X.left) :
    ((frobeniusPreimage κ X).obj U).hom = pullback.snd U.hom (frobeniusOver κ X).left :=
  rfl

/-- The projection of `Fr_X⁻¹(U)` to `U` lies over the Frobenius of `X`. -/
lemma frobeniusPreimage_fst_comp_hom (U : Over X.left) :
    pullback.fst U.hom (frobeniusOver κ X).left ≫ U.hom =
      ((frobeniusPreimage κ X).obj U).hom ≫ (frobeniusOver κ X).left :=
  pullback.condition

/-- `Fr_X⁻¹(h)` is compatible with the projections to `U'` and `U`: it is `h` on the factor `U`. -/
@[weil "not_fk203_frobenius_preimage", reassoc (attr := simp)]
lemma frobeniusPreimage_map_left_fst {U' U : Over X.left} (h : U' ⟶ U) :
    ((frobeniusPreimage κ X).map h).left ≫ pullback.fst U.hom (frobeniusOver κ X).left =
      pullback.fst U'.hom (frobeniusOver κ X).left ≫ h.left :=
  pullback.lift_fst _ _ _

/-- `Fr_X⁻¹(h)` is the identity on the factor `X`. -/
@[weil "not_fk203_frobenius_preimage", reassoc (attr := simp)]
lemma frobeniusPreimage_map_left_snd {U' U : Over X.left} (h : U' ⟶ U) :
    ((frobeniusPreimage κ X).map h).left ≫ pullback.snd U.hom (frobeniusOver κ X).left =
      pullback.snd U'.hom (frobeniusOver κ X).left :=
  pullback.lift_snd _ _ _

/-- `Fr_X⁻¹(h)` is `id_X × h`, the map of fibre products induced by `h` and the identities. -/
lemma frobeniusPreimage_map_left {U' U : Over X.left} (h : U' ⟶ U) :
    ((frobeniusPreimage κ X).map h).left =
      pullback.map U'.hom (frobeniusOver κ X).left U.hom (frobeniusOver κ X).left h.left
        (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext
  · rw [frobeniusPreimage_map_left_fst, pullback.lift_fst]
  · rw [frobeniusPreimage_map_left_snd, pullback.lift_snd, Category.comp_id]

/-- For `q = p ^ f`, the Frobenius preimage `Fr_X⁻¹(U)` is the `f`-fold Frobenius twist of `U`
over `X` of the Stacks Project. -/
@[weil "not_fk203_frobenius_preimage"]
theorem frobeniusPreimage_obj_eq_nFoldFrobeniusTwist (p f : ℕ) [Fact p.Prime] [CharP κ p]
    (hcard : Fintype.card κ = p ^ f) (U : Over X.left) :
    (frobeniusPreimage κ X).obj U =
      nFoldFrobeniusTwist X.left p (Stacks.Frobenius.isInCharacteristic_of_over X) f U := by
  simp only [frobeniusPreimage, frobeniusOver_left_eq X p f hcard]

end AlgebraicGeometry
