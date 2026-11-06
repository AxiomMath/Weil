module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy
public import Weil.Attr

/-!
# Admissible triangles in the derived category

Let `C` be an abelian category and `D(C)` its derived category, with the localization functor
`Qh : K(C) ⥤ D(C)` from the homotopy category. A triangle in `D(C)` is *admissible* if it is
isomorphic to the image under `Qh` of an admissible triangle of `K(C)`, that is, of a triangle
isomorphic to a standard triangle `(X, Y, C(u); [u], [ι_u], [π_u])`. Here the image of a triangle
`(X, Y, Z; u, v, w)` is `(Qh X, Qh Y, Qh Z; Qh u, Qh v, Qh w)`, the last morphism being composed
with the canonical isomorphism `Qh (X⟦1⟧) ≅ (Qh X)⟦1⟧`.

Mathlib's distinguished triangles in `D(C)` are the triangles isomorphic to the image under `Qh`
of a distinguished triangle of `K(C)`, whose third morphism carries the opposite sign. Hence a
triangle `(M, N, R; f, g, h)` of `D(C)` is admissible if and only if `(M, N, R; f, g, -h)` is
distinguished in Mathlib's sense.

## Main definitions

* `DerivedCategory.admissibleTriangles C`: the triangles of `D(C)` isomorphic to the image under
  `Qh` of an admissible triangle of `K(C)`.

## Main results

* `DerivedCategory.isomorphic_admissible`: admissible triangles are closed under isomorphism.
* `DerivedCategory.Qh_mapTriangle_mem_admissibleTriangles`: `Qh` sends admissible triangles to
  admissible triangles.
* `DerivedCategory.mem_admissibleTriangles_iff`: `T` is admissible if and only if the triangle
  with the third morphism negated is distinguished.
* `DerivedCategory.mem_distTriang_iff_admissible`: `T` is distinguished if and only if the
  triangle with the third morphism negated is admissible.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Preadditive A] [Preadditive B]
  [HasShift A ℤ] [HasShift B ℤ] (F : A ⥤ B) [F.CommShift ℤ] [F.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- The image under `F` of a triangle with negated third morphism is the image of the triangle
with negated third morphism. -/
noncomputable def mapTriangleNegMor₃Iso (T : Triangle A) :
    F.mapTriangle.obj (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) ≅
      Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
        (-(F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp; rfl)
    (by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.map_id]
      change F.map (-T.mor₃) ≫ _ = _
      rw [Functor.map_neg, Preadditive.neg_comp]
      rfl)

end CategoryTheory.Functor

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A triangle in the derived category `D(C)` is *admissible* if it is isomorphic to the image
under the localization functor `Qh : K(C) ⥤ D(C)` of an admissible triangle of the homotopy
category. -/
@[weil "def_fka2_admissible_triangle_derived"]
def admissibleTriangles : Set (Triangle (DerivedCategory C)) :=
  {T | ∃ T' ∈ HomotopyCategory.admissibleTriangles C, Nonempty (T ≅ Qh.mapTriangle.obj T')}

variable {C}

/-- The image under `Qh` of an admissible triangle of `K(C)` is admissible. -/
lemma Qh_mapTriangle_mem_admissibleTriangles
    {T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ HomotopyCategory.admissibleTriangles C) :
    Qh.mapTriangle.obj T ∈ admissibleTriangles C :=
  ⟨T, hT, ⟨Iso.refl _⟩⟩

/-- Admissible triangles of `D(C)` are closed under isomorphism of triangles. -/
lemma isomorphic_admissible {T₁ T₂ : Triangle (DerivedCategory C)}
    (h : T₁ ∈ admissibleTriangles C) (e : T₂ ≅ T₁) : T₂ ∈ admissibleTriangles C := by
  obtain ⟨T', hT', ⟨e'⟩⟩ := h
  exact ⟨T', hT', ⟨e ≪≫ e'⟩⟩

/-- A triangle `(M, N, R; f, g, h)` of `D(C)` is admissible if and only if `(M, N, R; f, g, -h)`
is distinguished in Mathlib's sense. -/
lemma mem_admissibleTriangles_iff (T : Triangle (DerivedCategory C)) :
    T ∈ admissibleTriangles C ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang (DerivedCategory C) := by
  constructor
  · rintro ⟨T', hT', ⟨e⟩⟩
    rw [HomotopyCategory.mem_admissibleTriangles_iff] at hT'
    exact isomorphic_distinguished _ (Qh.map_distinguished _ hT') _
      (Triangle.negMor₃IsoOfIso e ≪≫ (Qh.mapTriangleNegMor₃Iso T').symm)
  · rintro ⟨T'', e, hT''⟩
    refine ⟨Triangle.mk T''.mor₁ T''.mor₂ (-T''.mor₃), ?_, ⟨?_⟩⟩
    · exact (HomotopyCategory.mem_distinguishedTriangles_iff_admissible T'').1 hT''
    · exact eqToIso (Triangle.mk_neg_neg_mor₃ T).symm ≪≫ Triangle.negMor₃IsoOfIso e ≪≫
        (Qh.mapTriangleNegMor₃Iso T'').symm

/-- A triangle `T` of `D(C)` is distinguished in Mathlib's sense if and only if the triangle with
the third morphism negated is admissible. -/
lemma mem_distTriang_iff_admissible (T : Triangle (DerivedCategory C)) :
    T ∈ distTriang (DerivedCategory C) ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ admissibleTriangles C := by
  rw [mem_admissibleTriangles_iff]
  exact (distinguished_iff_of_iso (eqToIso (Triangle.mk_neg_neg_mor₃ T))).symm

end DerivedCategory
