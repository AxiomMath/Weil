module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Weil.Attr

/-!
# The projection from the mapping cone onto the shifted source

For a morphism of cochain complexes `φ : F ⟶ G`, the mapping cone `mappingCone φ` has
`(mappingCone φ).X n = F.X (n + 1) ⊞ G.X n`. The *cone projection*
`π_φ : mappingCone φ ⟶ F⟦1⟧` is the morphism of complexes whose degree `n` component is the
first projection `F.X (n + 1) ⊞ G.X n ⟶ F.X (n + 1) = (F⟦1⟧).X n`, `(x, y) ↦ x`.

## Main definitions

* `CochainComplex.mappingCone.projection φ : mappingCone φ ⟶ F⟦1⟧`: the cone projection,
  induced by the `1`-cocycle `CochainComplex.mappingCone.fst φ`.

## Main results

* `CochainComplex.mappingCone.projection_f`: its components are those of `fst φ`.
* `CochainComplex.mappingCone.inl_v_projection_f`, `CochainComplex.mappingCone.inr_f_projection_f`,
  `CochainComplex.mappingCone.inr_projection`: it is `(x, y) ↦ x`.
* `CochainComplex.mappingCone.projection_eq_neg_triangle_mor₃`: it is the negative of the third
  morphism of Mathlib's standard triangle `CochainComplex.mappingCone.triangle φ`.

## Implementation notes

Mathlib's standard triangle follows the convention of the Stacks project (Tag 014D), whose third
morphism is induced by `-fst φ`; the cone projection `(x, y) ↦ x` used here has the opposite
sign.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex

namespace CochainComplex.mappingCone

section Projection

variable {C : Type*} [Category C] [Preadditive C] {F G : CochainComplex C ℤ} (φ : F ⟶ G)
  [HasHomotopyCofiber φ]

/-- The cone projection `mappingCone φ ⟶ F⟦1⟧`, given in degree `n` by the first projection
`F.X (n + 1) ⊞ G.X n ⟶ F.X (n + 1)`. -/
@[weil "def_fka2_cone_projection"]
noncomputable def projection : mappingCone φ ⟶ F⟦(1 : ℤ)⟧ :=
  Cocycle.homOf ((fst φ).rightShift 1 0 (zero_add 1))

lemma projection_f (p : ℤ) :
    (projection φ).f p =
      (fst φ).1.v p (p + 1) rfl ≫ (F.shiftFunctorObjXIso 1 p (p + 1) rfl).inv := by
  simp [projection, Cochain.rightShift_v _ 1 0 (zero_add 1) p p (add_zero p) (p + 1) rfl]

@[reassoc (attr := simp)]
lemma inl_v_projection_f (p q : ℤ) (hpq : p + 1 = q) :
    (inl φ).v q p (by omega) ≫ (projection φ).f p =
      (F.shiftFunctorObjXIso 1 p q hpq.symm).inv := by
  subst hpq
  simp [projection_f]

@[reassoc (attr := simp)]
lemma inr_f_projection_f (p : ℤ) :
    (inr φ).f p ≫ (projection φ).f p = 0 := by
  simp [projection_f]

@[reassoc (attr := simp)]
lemma inr_projection : inr φ ≫ projection φ = 0 := by
  ext p
  simp

end Projection

section Triangle

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {F G : CochainComplex C ℤ} (φ : F ⟶ G)

lemma triangle_mor₃_eq_neg_projection : (triangle φ).mor₃ = -projection φ := by
  ext p
  dsimp [projection, triangle]
  simp

lemma projection_eq_neg_triangle_mor₃ : projection φ = -(triangle φ).mor₃ := by
  have h : (triangle φ).mor₃ = -projection φ := triangle_mor₃_eq_neg_projection φ
  exact (neg_neg (projection φ)).symm.trans (congrArg Neg.neg h).symm

end Triangle

end CochainComplex.mappingCone
