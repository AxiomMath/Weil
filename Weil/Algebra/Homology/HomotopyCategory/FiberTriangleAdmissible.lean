module

public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy
public import Weil.Attr

/-!
# The fiber triangle of a morphism of complexes is admissible

Let `k : X ⟶ Y` be a morphism of cochain complexes and `C(k)` its mapping cone. In the homotopy
category `K(C)`, the triangle
`(C(k)⟦-1⟧, X, Y; -[π_k]⟦-1⟧, [k], [ι_k])`
is admissible, i.e. isomorphic to a standard triangle. Here the first morphism is
`-[π_k]⟦-1⟧ : C(k)⟦-1⟧ ⟶ X⟦1⟧⟦-1⟧ ≅ X` and the third morphism is
`[ι_k] : Y ⟶ C(k) ≅ C(k)⟦-1⟧⟦1⟧`.

## Main results

* `CategoryTheory.Pretriangulated.Triangle.negMor₃InvRotateIso`: negating the third morphism
  commutes with inverse rotation, up to the isomorphism with components `(-𝟙, 𝟙, 𝟙)`.
* `HomotopyCategory.fiberTriangle_mem_admissibleTriangles`: the fiber triangle is admissible.

## Implementation notes

The identifications `X⟦1⟧⟦-1⟧ = X` and `C(k) = C(k)⟦-1⟧⟦1⟧` are the canonical isomorphisms
`shiftShiftNeg` and `shiftNegShift`. With them, the fiber triangle is the inverse rotation of
the standard triangle of `k`. The proof passes through Mathlib's distinguished triangles: the
fiber triangle with its third morphism negated is isomorphic, by the triangle isomorphism with
components `(-𝟙, 𝟙, 𝟙)`, to the inverse rotation of Mathlib's distinguished triangle
`CochainComplex.mappingCone.triangleh k`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.Pretriangulated.Triangle

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

/-- Negating the third morphism commutes with inverse rotation, up to the triangle isomorphism
with components `(-𝟙, 𝟙, 𝟙)`. -/
noncomputable def negMor₃InvRotateIso (T : Triangle D) :
    Triangle.mk T.invRotate.mor₁ T.invRotate.mor₂ (-T.invRotate.mor₃) ≅
      (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)).invRotate :=
  Triangle.isoMk _ _
    (Iso.mk (-𝟙 (T.obj₃⟦(-1 : ℤ)⟧)) (-𝟙 (T.obj₃⟦(-1 : ℤ)⟧))
      (by change (-𝟙 _) ≫ (-𝟙 _) = 𝟙 (T.obj₃⟦(-1 : ℤ)⟧); simp)
      (by change (-𝟙 _) ≫ (-𝟙 _) = 𝟙 (T.obj₃⟦(-1 : ℤ)⟧); simp))
    (Iso.refl _) (Iso.refl _)
    (by simp [Triangle.invRotate, shiftEquiv, shiftFunctorCompIsoId])
    (by simp [Triangle.invRotate])
    (by
      change (-(T.mor₂ ≫ (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).inv.app T.obj₃)) ≫
          (CategoryTheory.shiftFunctor D (1 : ℤ)).map (-𝟙 (T.obj₃⟦(-1 : ℤ)⟧)) =
        𝟙 T.obj₂ ≫ T.mor₂ ≫ (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).inv.app T.obj₃
      simp)

end CategoryTheory.Pretriangulated.Triangle

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

namespace HomotopyCategory

open CochainComplex

/-- For a morphism of cochain complexes `k : X ⟶ Y`, the triangle
`(C(k)⟦-1⟧, X, Y; -[π_k]⟦-1⟧, [k], [ι_k])` of the homotopy category is admissible. -/
@[weil "lem_fka2_fiber_triangle_admissible"]
theorem fiberTriangle_mem_admissibleTriangles {X Y : CochainComplex C ℤ} (k : X ⟶ Y) :
    Triangle.mk
      (-((mappingCone.standardTriangleh k).mor₃⟦(-1 : ℤ)⟧' ≫
        (shiftShiftNeg ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) (1 : ℤ)).hom))
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map k)
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (mappingCone.inr k) ≫
        (shiftNegShift ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (mappingCone k)) (1 : ℤ)).inv) ∈ admissibleTriangles C := by
  change (mappingCone.standardTriangleh k).invRotate ∈ admissibleTriangles C
  rw [mem_admissibleTriangles_iff]
  refine Pretriangulated.isomorphic_distinguished _
    (Pretriangulated.invRotate_distinguished_triangle' _ ⟨X, Y, k, ⟨Iso.refl _⟩⟩) _ ?_
  rw [mappingCone.triangleh_eq_mk_neg_standardTriangleh_mor₃]
  exact Triangle.negMor₃InvRotateIso _

end HomotopyCategory
