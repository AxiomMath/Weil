module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Weil.Defs.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Weil.Attr

/-!
# Admissible triangles in the homotopy category

Let `C` be a preadditive category with binary biproducts and `K(C)` the homotopy category of
`ℤ`-indexed cochain complexes in `C`. For a morphism of complexes `u : X ⟶ Y`, the *standard
triangle* of `u` is `(X, Y, C(u); [u], [ι_u], [π_u])`, where `C(u)` is the mapping cone,
`ι_u : Y ⟶ C(u)` the inclusion `y ↦ (0, y)` and `π_u : C(u) ⟶ X⟦1⟧` the projection
`(x, y) ↦ x`. A triangle in `K(C)` is *admissible* if it is isomorphic to a standard triangle.

Mathlib's distinguished triangles in `K(C)` are the triangles isomorphic to
`CochainComplex.mappingCone.triangleh u`, whose third morphism is `-[π_u]` (the convention of
the Stacks project, Tag 014D). The two notions differ by the sign of the third morphism: a
triangle `(M, N, R; f, g, h)` is admissible if and only if `(M, N, R; f, g, -h)` is
distinguished in Mathlib's sense.

## Main definitions

* `CochainComplex.mappingCone.standardTriangleh u`: the standard triangle
  `(X, Y, C(u); [u], [ι_u], [π_u])` in the homotopy category.
* `HomotopyCategory.admissibleTriangles C`: the triangles of `K(C)` isomorphic to a standard
  triangle.

## Main results

* `CochainComplex.mappingCone.standardTriangleh_mor₃`: the third morphism of the standard
  triangle is the negative of that of Mathlib's `triangleh`.
* `HomotopyCategory.mem_admissibleTriangles_iff`: `T` is admissible if and only if the triangle
  with the third morphism negated is distinguished in Mathlib's sense.
* `HomotopyCategory.isomorphic_admissible`: admissible triangles are closed under isomorphism.
* `HomotopyCategory.standardTriangleh_mem_admissibleTriangles`: standard triangles are
  admissible.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

namespace CategoryTheory.Pretriangulated.Triangle

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]

/-- An isomorphism of triangles `T ≅ T'` induces, with the same components, an isomorphism
between the triangles obtained by negating the third morphisms. -/
noncomputable def negMor₃IsoOfIso {T T' : Triangle D} (e : T ≅ T') :
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ≅ Triangle.mk T'.mor₁ T'.mor₂ (-T'.mor₃) :=
  Triangle.isoMk _ _ (Triangle.π₁.mapIso e) (Triangle.π₂.mapIso e) (Triangle.π₃.mapIso e)
    (by simp) (by simp) (by simp)

/-- Negating the third morphism twice gives back the triangle. -/
lemma mk_neg_neg_mor₃ (T : Triangle D) : Triangle.mk T.mor₁ T.mor₂ (-(-T.mor₃)) = T :=
  congrArg (Triangle.mk T.mor₁ T.mor₂) (neg_neg T.mor₃)

end CategoryTheory.Pretriangulated.Triangle

namespace CochainComplex.mappingCone

variable {X Y : CochainComplex C ℤ} (u : X ⟶ Y)

/-- The standard triangle `(X, Y, C(u); [u], [ι_u], [π_u])` in the homotopy category attached
to a morphism of cochain complexes `u`, with the cone projection `π_u : (x, y) ↦ x` as third
morphism. -/
@[weil "def_fka2_admissible_triangle_homotopy"]
noncomputable def standardTriangleh : Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  Triangle.mk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map u)
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (inr u))
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (projection u) ≫
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app X)

@[simp]
lemma standardTriangleh_obj₁ :
    (standardTriangleh u).obj₁ = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X :=
  rfl

@[simp]
lemma standardTriangleh_obj₂ :
    (standardTriangleh u).obj₂ = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y :=
  rfl

@[simp]
lemma standardTriangleh_obj₃ :
    (standardTriangleh u).obj₃ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (mappingCone u) :=
  rfl

@[simp]
lemma standardTriangleh_mor₁ :
    (standardTriangleh u).mor₁ = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map u :=
  rfl

@[simp]
lemma standardTriangleh_mor₂ :
    (standardTriangleh u).mor₂ = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (inr u) :=
  rfl

lemma standardTriangleh_mor₃_eq :
    (standardTriangleh u).mor₃ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (projection u) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app X :=
  rfl

/-- The third morphism of Mathlib's triangle `triangleh u` is `-[π_u]`. -/
lemma triangleh_mor₃_eq_neg :
    (triangleh u).mor₃ =
      -((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (projection u) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app X) := by
  rw [← Preadditive.neg_comp, ← Functor.map_neg, ← triangle_mor₃_eq_neg_projection]
  rfl

/-- The third morphism of the standard triangle is the negative of the third morphism of
Mathlib's triangle `triangleh u`. -/
lemma standardTriangleh_mor₃ : (standardTriangleh u).mor₃ = -(triangleh u).mor₃ := by
  rw [triangleh_mor₃_eq_neg]
  exact (neg_neg _).symm

/-- Mathlib's triangle `triangleh u` is the standard triangle with the third morphism
negated. -/
lemma triangleh_eq_mk_neg_standardTriangleh_mor₃ :
    triangleh u = Triangle.mk (standardTriangleh u).mor₁ (standardTriangleh u).mor₂
      (-(standardTriangleh u).mor₃) :=
  congrArg (Triangle.mk (standardTriangleh u).mor₁ (standardTriangleh u).mor₂)
    (triangleh_mor₃_eq_neg u)

/-- The standard triangle is Mathlib's triangle `triangleh u` with the third morphism
negated. -/
lemma standardTriangleh_eq_mk_neg_triangleh_mor₃ :
    standardTriangleh u = Triangle.mk (triangleh u).mor₁ (triangleh u).mor₂
      (-(triangleh u).mor₃) :=
  congrArg (Triangle.mk (triangleh u).mor₁ (triangleh u).mor₂) (standardTriangleh_mor₃ u)

end CochainComplex.mappingCone

namespace HomotopyCategory

open CochainComplex

variable (C) in
/-- A triangle in the homotopy category `K(C)` is *admissible* if it is isomorphic to the
standard triangle `(X, Y, C(u); [u], [ι_u], [π_u])` of some morphism of cochain complexes
`u : X ⟶ Y`. -/
@[weil "def_fka2_admissible_triangle_homotopy"]
def admissibleTriangles : Set (Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :=
  {T | ∃ (X Y : CochainComplex C ℤ) (u : X ⟶ Y),
    Nonempty (T ≅ mappingCone.standardTriangleh u)}

lemma standardTriangleh_mem_admissibleTriangles {X Y : CochainComplex C ℤ} (u : X ⟶ Y) :
    mappingCone.standardTriangleh u ∈ admissibleTriangles C :=
  ⟨X, Y, u, ⟨Iso.refl _⟩⟩

/-- Admissible triangles are closed under isomorphism of triangles. -/
lemma isomorphic_admissible {T₁ T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (h : T₁ ∈ admissibleTriangles C) (e : T₂ ≅ T₁) : T₂ ∈ admissibleTriangles C := by
  obtain ⟨X, Y, u, ⟨e'⟩⟩ := h
  exact ⟨X, Y, u, ⟨e ≪≫ e'⟩⟩

/-- A triangle `(M, N, R; f, g, h)` of `K(C)` is admissible if and only if
`(M, N, R; f, g, -h)` is distinguished in Mathlib's sense. -/
lemma mem_admissibleTriangles_iff (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ admissibleTriangles C ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ Pretriangulated.distinguishedTriangles C := by
  constructor
  · rintro ⟨X, Y, u, ⟨e⟩⟩
    exact ⟨X, Y, u, ⟨Triangle.negMor₃IsoOfIso e ≪≫
      eqToIso (mappingCone.triangleh_eq_mk_neg_standardTriangleh_mor₃ u).symm⟩⟩
  · rintro ⟨X, Y, u, ⟨e⟩⟩
    exact ⟨X, Y, u, ⟨eqToIso (Triangle.mk_neg_neg_mor₃ T).symm ≪≫ Triangle.negMor₃IsoOfIso e ≪≫
      eqToIso (mappingCone.standardTriangleh_eq_mk_neg_triangleh_mor₃ u).symm⟩⟩

/-- A triangle `T` of `K(C)` is distinguished in Mathlib's sense if and only if the triangle
with the third morphism negated is admissible. -/
lemma mem_distinguishedTriangles_iff_admissible
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ Pretriangulated.distinguishedTriangles C ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ admissibleTriangles C := by
  rw [mem_admissibleTriangles_iff]
  exact ⟨fun h => Pretriangulated.isomorphic_distinguished _ h _
      (eqToIso (Triangle.mk_neg_neg_mor₃ T)),
    fun h => Pretriangulated.isomorphic_distinguished _ h _
      (eqToIso (Triangle.mk_neg_neg_mor₃ T).symm)⟩

end HomotopyCategory
