module

public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Weil.Attr

/-!
# Triangles with respect to an endofunctor

Let `C` be a category with an endofunctor `T : C ⥤ C`. A *triangle* in `C` with respect to `T`
is a system `(M, N, R; f, g, h)` of objects `M, N, R` of `C` and morphisms `f : M ⟶ N`,
`g : N ⟶ R` and `h : R ⟶ T(M)`.

When `C` carries a shift by `ℤ` and `T` is the shift functor `X ↦ X⟦1⟧`, these are exactly
Mathlib's triangles `CategoryTheory.Pretriangulated.Triangle C`, which are the triangles used
in the homotopy category `K(A)` and in the derived category `D(A)`. In `K(A)`, the third
morphism `h : R ⟶ M⟦1⟧` of a triangle is a morphism of degree `1` from `R` to `M`; it is the
same as the homotopy class of a degree `1` cocycle of the Hom complex from `R` to `M`.

## Main definitions

* `CategoryTheory.EndoTriangle T`: triangles in `C` with respect to an endofunctor `T`.
* `CategoryTheory.Pretriangulated.Triangle.equivEndoTriangleShift`: Mathlib's triangles in a
  category with a shift by `ℤ` are the triangles with respect to the shift functor
  `shiftFunctor C 1`.
* `HomotopyCategory.homShiftOneAddEquivCohomologyClass`: in the homotopy category, morphisms
  `R ⟶ M⟦1⟧` are the cohomology classes of degree `1` of the Hom complex from `R` to `M`.

## Implementation notes

The source asks for an additive category and an additive endofunctor; neither hypothesis is
needed to define triangles, so `EndoTriangle` is stated for any category and any endofunctor.
All later constructions on `K(A)` and `D(A)` use Mathlib's `Pretriangulated.Triangle`, to which
`Pretriangulated.Triangle.equivEndoTriangleShift` identifies `EndoTriangle` for the shift.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II, p. 293.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A triangle in `C` with respect to an endofunctor `T : C ⥤ C`: objects `obj₁, obj₂, obj₃`
with morphisms `obj₁ ⟶ obj₂`, `obj₂ ⟶ obj₃` and `obj₃ ⟶ T.obj obj₁`. -/
@[weil "def_fka2_triangle"]
structure EndoTriangle (T : C ⥤ C) where
  /-- the first object of a triangle -/
  obj₁ : C
  /-- the second object of a triangle -/
  obj₂ : C
  /-- the third object of a triangle -/
  obj₃ : C
  /-- the first morphism of a triangle -/
  mor₁ : obj₁ ⟶ obj₂
  /-- the second morphism of a triangle -/
  mor₂ : obj₂ ⟶ obj₃
  /-- the third morphism of a triangle -/
  mor₃ : obj₃ ⟶ T.obj obj₁

namespace Pretriangulated.Triangle

variable [HasShift C ℤ]

/-- Mathlib's triangles in a category with a shift by `ℤ` are the triangles with respect to
the shift functor `X ↦ X⟦1⟧`. -/
@[weil "def_fka2_triangle", simps]
def equivEndoTriangleShift : Triangle C ≃ EndoTriangle (shiftFunctor C (1 : ℤ)) where
  toFun T := ⟨T.obj₁, T.obj₂, T.obj₃, T.mor₁, T.mor₂, T.mor₃⟩
  invFun T := Triangle.mk T.mor₁ T.mor₂ T.mor₃
  left_inv _ := rfl
  right_inv _ := rfl

end Pretriangulated.Triangle

end CategoryTheory

namespace HomotopyCategory

open CochainComplex HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- In the homotopy category `K(C)`, a morphism `R ⟶ M⟦1⟧` (a morphism of degree `1` from `R`
to `M`) is the same as a cohomology class of degree `1` of the Hom complex from `R` to `M`,
i.e. the homotopy class of a family of maps `R^p ⟶ M^(p+1)` forming a degree `1` cocycle. -/
@[weil "def_fka2_triangle"]
noncomputable def homShiftOneAddEquivCohomologyClass (R M : CochainComplex C ℤ) :
    ((quotient C (ComplexShape.up ℤ)).obj R ⟶
        ((quotient C (ComplexShape.up ℤ)).obj M)⟦(1 : ℤ)⟧) ≃+ CohomologyClass R M 1 :=
  (AddEquiv.mk ((Iso.refl _).homCongr (((quotient C (ComplexShape.up ℤ)).commShiftIso
      (1 : ℤ)).app M).symm) (fun f g => by simp [Iso.homCongr_apply])).trans
    (CohomologyClass.homAddEquiv (K := R) (L := M) (n := 1)).symm

/-- The morphism `R ⟶ M⟦1⟧` of the homotopy category given by the class of a degree `1`
cocycle `x` is the image of the morphism of complexes `R ⟶ M⟦1⟧` attached to `x`. -/
lemma homShiftOneAddEquivCohomologyClass_symm_mk {R M : CochainComplex C ℤ}
    (x : Cocycle R M 1) :
    (homShiftOneAddEquivCohomologyClass R M).symm (CohomologyClass.mk x) =
      (quotient C (ComplexShape.up ℤ)).map (Cocycle.equivHomShift.symm x) ≫
        ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app M := by
  simp [homShiftOneAddEquivCohomologyClass, Iso.homCongr_apply, CohomologyClass.toHom_mk]

end HomotopyCategory
