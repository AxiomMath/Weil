module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Weil.Algebra.Homology.HomotopyCategory.Shift
public import Weil.Attr
public import Weil.Defs.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy

/-!
# The componentwise extension of an additive functor commutes with mapping cones

Let `H : C ⥤ D` be an additive functor between preadditive categories and let
`φ : K ⟶ L` be a morphism of cochain complexes in `C`. In degree `n` the mapping cone
`mappingCone φ` is the biproduct `K^{n+1} ⊞ L^n`, so applying `H` termwise gives
`H(K^{n+1} ⊞ L^n)`, which `H` identifies with `H(K^{n+1}) ⊞ H(L^n)`, the term of degree
`n` of `mappingCone (H φ)`. Under this identification the differentials agree, the
inclusion `inr φ : L ⟶ mappingCone φ` goes to `inr (H φ)`, and the third morphism of the
standard triangle, `mappingCone φ ⟶ K⟦1⟧`, goes to the one of `H φ`, once `H(K⟦1⟧)` is
identified with `(H K)⟦1⟧`.

## Main results

* `CochainComplex.mappingCone.mapHomologicalComplexIso_hom_f_fst_v`,
  `CochainComplex.mappingCone.mapHomologicalComplexIso_hom_f_snd_v`: Mathlib's comparison
  isomorphism `mapHomologicalComplexIso φ H : H(mappingCone φ) ≅ mappingCone (H φ)` is, in
  every degree, the identification of `H(K^{n+1} ⊞ L^n)` with `H(K^{n+1}) ⊞ H(L^n)`: its
  components are the images under `H` of the two projections.
* `CochainComplex.mappingCone.map_inl_v_mapHomologicalComplexIso_hom_f`,
  `CochainComplex.mappingCone.map_inr_f_mapHomologicalComplexIso_hom_f`: it carries the
  images of the two inclusions to the inclusions.
* `CochainComplex.mappingCone.map_inr_mapHomologicalComplexIso_hom`: `H(ι_φ) = ι_{H φ}`.
* `CochainComplex.mappingCone.map_triangle_mor₃_eqToHom`: `H(π_φ) = π_{H φ}`, with
  `H(K⟦1⟧) = (H K)⟦1⟧` the on-the-nose identification of
  `CategoryTheory.Functor.mapHomologicalComplex_obj_shift`.

## Implementation notes

The source states the equalities `H(C(φ)) = C(H φ)`, `H(ι_φ) = ι_{H φ}`,
`H(π_φ) = π_{H φ}` after identifying `H(X ⊕ Y)` with `H X ⊕ H Y`. Here this identification
is Mathlib's isomorphism of complexes `CochainComplex.mappingCone.mapHomologicalComplexIso`
(being a morphism of complexes is the compatibility with the differentials), and the
first two lemmas show that it is the canonical biproduct identification in each degree.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Category Limits CochainComplex.HomComplex

namespace CochainComplex.mappingCone

section

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]
  (H : C ⥤ D) [H.Additive]
  [HomologicalComplex.HasHomotopyCofiber ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)]

/-- In degree `p`, the comparison isomorphism followed by the first projection of
`mappingCone (H φ)` is the image under `H` of the first projection of `mappingCone φ`. -/
@[weil "lem_fka2_componentwise_extension_commutes_with_cone", reassoc (attr := simp)]
theorem mapHomologicalComplexIso_hom_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (mapHomologicalComplexIso φ H).hom.f p ≫
        (fst ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).1.v p q hpq =
      H.map ((fst φ).1.v p q hpq) := by
  dsimp [mapHomologicalComplexIso]
  rw [mapHomologicalComplexXIso_eq φ H p q hpq, mapHomologicalComplexXIso'_hom]
  simp

/-- In degree `p`, the comparison isomorphism followed by the second projection of
`mappingCone (H φ)` is the image under `H` of the second projection of `mappingCone φ`. -/
@[weil "lem_fka2_componentwise_extension_commutes_with_cone", reassoc (attr := simp)]
theorem mapHomologicalComplexIso_hom_f_snd_v (p : ℤ) :
    (mapHomologicalComplexIso φ H).hom.f p ≫
        (snd ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).v p p (add_zero p) =
      H.map ((snd φ).v p p (add_zero p)) := by
  dsimp [mapHomologicalComplexIso]
  rw [mapHomologicalComplexXIso_eq φ H p (p + 1) rfl, mapHomologicalComplexXIso'_hom]
  simp

/-- The comparison isomorphism carries the image of the first inclusion
`K^{q+1} ⟶ (mappingCone φ)^q` to the first inclusion of `mappingCone (H φ)`. -/
@[reassoc (attr := simp)]
theorem map_inl_v_mapHomologicalComplexIso_hom_f (p q : ℤ) (hpq : p + (-1) = q) :
    H.map ((inl φ).v p q hpq) ≫ (mapHomologicalComplexIso φ H).hom.f q =
      (inl ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).v p q hpq := by
  rw [ext_to_iff _ q p (by lia)]
  simp only [assoc, mapHomologicalComplexIso_hom_f_fst_v, mapHomologicalComplexIso_hom_f_snd_v,
    ← H.map_comp, inl_v_fst_v, inl_v_snd_v, H.map_id, H.map_zero]
  simp

/-- The comparison isomorphism carries the image of the second inclusion
`L^p ⟶ (mappingCone φ)^p` to the second inclusion of `mappingCone (H φ)`. -/
@[reassoc (attr := simp)]
theorem map_inr_f_mapHomologicalComplexIso_hom_f (p : ℤ) :
    H.map ((inr φ).f p) ≫ (mapHomologicalComplexIso φ H).hom.f p =
      (inr ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).f p := by
  rw [ext_to_iff _ p (p + 1) rfl]
  simp only [assoc, mapHomologicalComplexIso_hom_f_fst_v, mapHomologicalComplexIso_hom_f_snd_v,
    ← H.map_comp, inr_f_fst_v, inr_f_snd_v, H.map_id, H.map_zero]
  simp

/-- `H(ι_φ) = ι_{H φ}`: the image under `H` of `inr φ : L ⟶ mappingCone φ`, followed by the
comparison isomorphism, is `inr (H φ)`. -/
@[weil "lem_fka2_componentwise_extension_commutes_with_cone"]
theorem map_inr_mapHomologicalComplexIso_hom :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (inr φ) ≫
        (mapHomologicalComplexIso φ H).hom =
      inr ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
  map_inr φ H

end

section

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L) (H : C ⥤ D) [H.Additive]

/-- `H(π_φ) = π_{H φ}`: the image under `H` of the third morphism
`mappingCone φ ⟶ K⟦1⟧` of the standard triangle, followed by the identification
`H(K⟦1⟧) = (H K)⟦1⟧`, is the comparison isomorphism followed by the third morphism of the
standard triangle of `H φ`. -/
@[weil "lem_fka2_componentwise_extension_commutes_with_cone"]
theorem map_triangle_mor₃_eqToHom :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (triangle φ).mor₃ ≫
        eqToHom (H.mapHomologicalComplex_obj_shift K 1) =
      (mapHomologicalComplexIso φ H).hom ≫
        (triangle ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).mor₃ := by
  have h := map_δ φ H
  rw [H.mapHomologicalComplex_commShiftIso_hom_app_eq_eqToHom K 1] at h
  exact h

end

end CochainComplex.mappingCone

/-! ### The shift of a mapping cone -/

/-!
# The shift of a mapping cone

Let `φ : F ⟶ G` be a morphism of cochain complexes and `n : ℤ`. Put
`v = (-1)ⁿ • φ⟦n⟧' : F⟦n⟧ ⟶ G⟦n⟧`. In every degree `p` both `(mappingCone φ)⟦n⟧` and
`mappingCone v` are `F^{p+n+1} ⊞ G^{p+n}`, and their differentials agree:
`(x, y) ↦ (-1)ⁿ(-dx, φx + dy)`. Hence the identity in each degree is an isomorphism of
complexes `(mappingCone φ)⟦n⟧ ≅ mappingCone v`; it carries `(inr φ)⟦n⟧'` to `inr v` and
`(projection φ)⟦n⟧'` to `projection v`, the latter up to the canonical identification
`F⟦1⟧⟦n⟧ ≅ F⟦n⟧⟦1⟧`.

## Main definitions

* `CochainComplex.mappingCone.shiftNegOnePowIso φ n :
    (mappingCone φ)⟦n⟧ ≅ mappingCone (n.negOnePow • φ⟦n⟧')`.

## Main results

* `CochainComplex.mappingCone.shiftNegOnePowIso_hom_f_fst_v`,
  `CochainComplex.mappingCone.shiftNegOnePowIso_hom_f_snd_v`: the isomorphism is the identity
  on both summands in every degree.
* `CochainComplex.mappingCone.shift_inr_comp_shiftNegOnePowIso_hom`: `T^n(ι_φ) = ι_v`.
* `CochainComplex.mappingCone.shiftNegOnePowIso_hom_comp_projection`: `T^n(π_φ) = π_v`.

## Implementation notes

The source states an equality of complexes. In Lean the degree `p` terms
`F.X (p + n + 1) ⊞ G.X (p + n)` and `F.X (p + 1 + n) ⊞ G.X (p + n)` are not definitionally
equal, so the equality is stated as an isomorphism whose components are the identity
(`shiftNegOnePowIso_hom_f_fst_v`, `shiftNegOnePowIso_hom_f_snd_v`). Mathlib's
`CochainComplex.mappingCone.shiftIso` is the same comparison for the unsigned morphism
`φ⟦n⟧'`, with the sign `(-1)ⁿ` placed on the first summand instead.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex CochainComplex.HomComplex

namespace CochainComplex.mappingCone

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {F G : CochainComplex C ℤ} (φ : F ⟶ G)

/-- The isomorphism `(mappingCone φ)⟦n⟧ ≅ mappingCone ((-1)ⁿ • φ⟦n⟧')`, the identity on both
summands `F^{p+n+1} ⊞ G^{p+n}` in every degree `p`. -/
@[weil "lem_fka2_shift_of_cone"]
noncomputable def shiftNegOnePowIso (n : ℤ) :
    (mappingCone φ)⟦n⟧ ≅ mappingCone (n.negOnePow • φ⟦n⟧') where
  hom := lift _ ((fst φ).shift n) ((snd φ).shift n) (by
    ext p q hpq
    simp [Cochain.δ_shift, Cochain.shift_v', Cochain.comp_zero_cochain_v])
  inv := desc _ ((inl φ).shift n) ((inr φ)⟦n⟧') (by
    ext p
    simp [Cochain.δ_shift, Cochain.shift_v', Cochain.comp_zero_cochain_v])
  hom_inv_id := by
    ext p
    simp only [lift_desc_f _ _ _ _ _ _ _ _ (p + 1) rfl, shiftFunctor_obj_X', Int.reduceNeg, comp_f,
      id_f, Cocycle.shift_coe, Cochain.shift_v', shiftFunctor_map_f']
    exact id_X φ (p + n) (p + 1 + n) (by omega)
  inv_hom_id := by
    ext p
    simp [ext_from_iff _ (p + 1) _ rfl, ext_to_iff _ _ (p + 1) rfl, Cochain.shift_v']

/-- In degree `p`, the first summand of `shiftNegOnePowIso φ n` is the identity of
`F^{p+n+1}`: `(x, y) ↦ x`. -/
@[weil "lem_fka2_shift_of_cone", reassoc (attr := simp)]
lemma shiftNegOnePowIso_hom_f_fst_v (n p q : ℤ) (hpq : p + 1 = q) :
    (shiftNegOnePowIso φ n).hom.f p ≫ (fst (n.negOnePow • φ⟦n⟧')).1.v p q hpq =
      (fst φ).1.v (p + n) (q + n) (by omega) := by
  simp [shiftNegOnePowIso, Cochain.shift_v']

/-- In degree `p`, the second summand of `shiftNegOnePowIso φ n` is the identity of
`G^{p+n}`: `(x, y) ↦ y`. -/
@[weil "lem_fka2_shift_of_cone", reassoc (attr := simp)]
lemma shiftNegOnePowIso_hom_f_snd_v (n p : ℤ) :
    (shiftNegOnePowIso φ n).hom.f p ≫ (snd (n.negOnePow • φ⟦n⟧')).v p p (add_zero p) =
      (snd φ).v (p + n) (p + n) (add_zero _) := by
  simp [shiftNegOnePowIso, Cochain.shift_v']

/-- The inverse of `shiftNegOnePowIso φ n` is the identity on the first summand. -/
@[reassoc (attr := simp)]
lemma inl_v_shiftNegOnePowIso_inv_f (n p q : ℤ) (hpq : q + 1 = p) :
    (inl (n.negOnePow • φ⟦n⟧')).v p q (by omega) ≫ (shiftNegOnePowIso φ n).inv.f q =
      (inl φ).v (p + n) (q + n) (by omega) := by
  simp [shiftNegOnePowIso, Cochain.shift_v']

/-- The inverse of `shiftNegOnePowIso φ n` is the identity on the second summand. -/
@[reassoc (attr := simp)]
lemma inr_f_shiftNegOnePowIso_inv_f (n p : ℤ) :
    (inr (n.negOnePow • φ⟦n⟧')).f p ≫ (shiftNegOnePowIso φ n).inv.f p =
      (inr φ).f (p + n) := by
  simp [shiftNegOnePowIso]

/-- The shift of the cone inclusion is the cone inclusion of the shifted morphism:
`T^n(ι_φ) = ι_v` for `v = (-1)ⁿ • φ⟦n⟧'`. -/
@[weil "lem_fka2_shift_of_cone", reassoc (attr := simp)]
theorem shift_inr_comp_shiftNegOnePowIso_hom (n : ℤ) :
    (inr φ)⟦n⟧' ≫ (shiftNegOnePowIso φ n).hom = inr (n.negOnePow • φ⟦n⟧') := by
  ext p
  simp [ext_to_iff _ _ (p + 1) rfl]

/-- The shift of the cone projection is the cone projection of the shifted morphism:
`T^n(π_φ) = π_v` for `v = (-1)ⁿ • φ⟦n⟧'`, as morphisms to `F⟦n⟧⟦1⟧ ≅ F⟦1⟧⟦n⟧`. -/
@[weil "lem_fka2_shift_of_cone", reassoc]
theorem shiftNegOnePowIso_hom_comp_projection (n : ℤ) :
    (shiftNegOnePowIso φ n).hom ≫ projection (n.negOnePow • φ⟦n⟧') =
      (projection φ)⟦n⟧' ≫ (shiftFunctorComm (CochainComplex C ℤ) 1 n).hom.app F := by
  ext p
  simp [projection_f, shiftFunctorComm_hom_app_f, Cochain.v_comp_XIsoOfEq_hom]

end CochainComplex.mappingCone

/-! ### The rotated standard triangle is admissible -/

/-!
# The rotated standard triangle is admissible

Let `C` be a preadditive category with binary biproducts and `K(C)` the homotopy category of
`ℤ`-indexed cochain complexes in `C`. For a morphism of complexes `u : X ⟶ Y`, with mapping
cone `C(u)`, inclusion `ι_u : Y ⟶ C(u)` and projection `π_u : C(u) ⟶ X⟦1⟧`, the triangle
`(Y, C(u), X⟦1⟧; [ι_u], [π_u], -[u]⟦1⟧')` is admissible in `K(C)`, i.e. isomorphic to a
standard triangle. This triangle is the rotation of the standard triangle of `u`.

## Main results

* `HomotopyCategory.rotate_standardTriangleh_mem_admissibleTriangles`: the triangle
  `(Y, C(u), X⟦1⟧; [ι_u], [π_u], -[u]⟦1⟧')` is admissible.
* `HomotopyCategory.standardTriangleh_rotate_mem_admissibleTriangles`: the same statement for
  `(standardTriangleh u).rotate`.

## Implementation notes

The proof goes through Mathlib's pretriangulated structure on `K(C)`: a triangle is admissible
if and only if the triangle with its third morphism negated is distinguished in Mathlib's sense
(`HomotopyCategory.mem_admissibleTriangles_iff`). The rotation of Mathlib's triangle
`triangleh u` is `([ι_u], -[π_u], -[u]⟦1⟧')`, distinguished by
`HomotopyCategory.Pretriangulated.rotate_distinguished_triangle'`, and the triangle
isomorphism `(𝟙, 𝟙, -𝟙)` identifies it with `([ι_u], [π_u], [u]⟦1⟧')`. Mathlib's
`CochainComplex.mappingCone.rotateTrianglehIso` encodes the explicit homotopy equivalence
`X⟦1⟧ ≃ C(ι_u)` used in the classical argument.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Pretriangulated.Triangle

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]

/-- The isomorphism of triangles `(𝟙, 𝟙, -𝟙) : (A, B, E; f, g, -h) ≅ (A, B, E; f, -g, h)`. -/
noncomputable def negMor₂Mor₃Iso {A B E : D} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ A⟦(1 : ℤ)⟧) :
    Triangle.mk f g (-h) ≅ Triangle.mk f (-g) h :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    { hom := -𝟙 E, inv := -𝟙 E, hom_inv_id := by simp, inv_hom_id := by simp }
    (by simp) (by simp) (by simp)

end CategoryTheory.Pretriangulated.Triangle

namespace HomotopyCategory

open CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- For a morphism of cochain complexes `u : X ⟶ Y`, the triangle
`(Y, C(u), X⟦1⟧; [ι_u], [π_u], -[u]⟦1⟧')` is admissible in the homotopy category. -/
@[weil "lem_fka2_rotated_standard_triangle_admissible"]
theorem rotate_standardTriangleh_mem_admissibleTriangles {X Y : CochainComplex C ℤ}
    (u : X ⟶ Y) :
    Triangle.mk ((quotient C (ComplexShape.up ℤ)).map (mappingCone.inr u))
      ((quotient C (ComplexShape.up ℤ)).map (mappingCone.projection u) ≫
        ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app X)
      (-((quotient C (ComplexShape.up ℤ)).map u)⟦(1 : ℤ)⟧') ∈ admissibleTriangles C := by
  rw [mem_admissibleTriangles_iff]
  have h₁ : Triangle.mk (mappingCone.triangleh u).mor₂
      (-((quotient C (ComplexShape.up ℤ)).map (mappingCone.projection u) ≫
        ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app X))
      (-(mappingCone.triangleh u).mor₁⟦(1 : ℤ)⟧') ∈
        Pretriangulated.distinguishedTriangles C := by
    rw [← mappingCone.triangleh_mor₃_eq_neg]
    exact Pretriangulated.rotate_distinguished_triangle' _ ⟨X, Y, u, ⟨Iso.refl _⟩⟩
  have h₂ : Triangle.mk ((quotient C (ComplexShape.up ℤ)).map (mappingCone.inr u))
      (-((quotient C (ComplexShape.up ℤ)).map (mappingCone.projection u) ≫
        ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app X))
      (-((quotient C (ComplexShape.up ℤ)).map u)⟦(1 : ℤ)⟧') ∈
        Pretriangulated.distinguishedTriangles C := by
    dsimp only [mappingCone.triangleh, Functor.mapTriangle, mappingCone.triangle,
      Triangle.mk_mor₁, Triangle.mk_mor₂] at h₁
    exact h₁
  exact Pretriangulated.isomorphic_distinguished _ h₂ _ (Triangle.negMor₂Mor₃Iso _ _ _)

/-- The rotation of the standard triangle of a morphism of cochain complexes is admissible. -/
theorem standardTriangleh_rotate_mem_admissibleTriangles {X Y : CochainComplex C ℤ}
    (u : X ⟶ Y) : (mappingCone.standardTriangleh u).rotate ∈ admissibleTriangles C :=
  rotate_standardTriangleh_mem_admissibleTriangles u

end HomotopyCategory

/-! ### Shifts of admissible triangles -/

/-!
# Shifts of admissible triangles

Let `C` be a preadditive category with binary biproducts and `K(C)` its homotopy category of
`ℤ`-indexed cochain complexes. If `(M, N, R; f, g, h)` is an admissible triangle of `K(C)` and
`i : ℤ`, then the shifted triangle
`(M⟦i⟧, N⟦i⟧, R⟦i⟧; (-1)^i f⟦i⟧, (-1)^i g⟦i⟧, (-1)^i h⟦i⟧)` is admissible, where the third
morphism is composed with the canonical isomorphism `M⟦1⟧⟦i⟧ ≅ M⟦i⟧⟦1⟧`. This shifted triangle
is Mathlib's `Triangle.shiftFunctor _ i` applied to the triangle.

## Main results

* `HomotopyCategory.shift_mem_admissibleTriangles`: the shift of an admissible triangle is
  admissible.

## Implementation notes

The proof translates admissibility into Mathlib's distinguished triangles of `K(C)` by negating
the third morphism (`HomotopyCategory.mem_admissibleTriangles_iff`); negating the third
morphism commutes with `Triangle.shiftFunctor`, and Mathlib's
`HomotopyCategory.Pretriangulated.shift_distinguished_triangle` (which needs no zero object)
concludes.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.Pretriangulated.Triangle

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

/-- Negating the third morphism of a triangle commutes with shifting it. -/
lemma shiftFunctor_obj_mk_neg_mor₃ (T : Triangle D) (i : ℤ) :
    (Triangle.shiftFunctor D i).obj (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) =
      Triangle.mk ((Triangle.shiftFunctor D i).obj T).mor₁
        ((Triangle.shiftFunctor D i).obj T).mor₂ (-((Triangle.shiftFunctor D i).obj T).mor₃) := by
  dsimp [Triangle.shiftFunctor]
  congr 1
  simp only [Functor.map_neg, smul_neg, Preadditive.neg_comp]
  rfl

end CategoryTheory.Pretriangulated.Triangle

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The shift `(M⟦i⟧, N⟦i⟧, R⟦i⟧; (-1)^i f⟦i⟧, (-1)^i g⟦i⟧, (-1)^i h⟦i⟧)` of an admissible
triangle `(M, N, R; f, g, h)` of the homotopy category `K(C)` is admissible. -/
@[weil "lem_fka2_shifted_triangle_admissible"]
theorem shift_mem_admissibleTriangles
    {T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))} (hT : T ∈ admissibleTriangles C)
    (i : ℤ) : (Triangle.shiftFunctor _ i).obj T ∈ admissibleTriangles C := by
  rw [mem_admissibleTriangles_iff] at hT ⊢
  rw [← Triangle.shiftFunctor_obj_mk_neg_mor₃]
  exact Pretriangulated.shift_distinguished_triangle _ hT i

end HomotopyCategory
