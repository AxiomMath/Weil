/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy
public import Weil.Attr

/-!
# Rotation of admissible triangles in the homotopy category

Let `C` be a preadditive category with binary biproducts. A triangle `(X, Y, Z; u, v, w)` of
the homotopy category `K(C)` is admissible (isomorphic to a standard mapping-cone triangle
`(X, Y, C(u); [u], [ι_u], [π_u])`) if and only if its rotation `(Y, Z, X⟦1⟧; v, w, -u⟦1⟧')`
is admissible.

## Main results

* `HomotopyCategory.rotate_mem_admissibleTriangles_iff`: a triangle `T` of `K(C)` is
  admissible if and only if `T.rotate = (T.obj₂, T.obj₃, T.obj₁⟦1⟧; T.mor₂, T.mor₃, -T.mor₁⟦1⟧')`
  is admissible.

## Implementation notes

Admissible triangles are the triangles `(M, N, R; f, g, h)` with `(M, N, R; f, g, -h)`
distinguished in the pretriangulated structure of `K(C)`
(`HomotopyCategory.mem_admissibleTriangles_iff`). The rotation of `(X, Y, Z; u, v, -w)` is
`(Y, Z, X⟦1⟧; v, -w, -u⟦1⟧')`, which the triple `(𝟙, 𝟙, -𝟙)` identifies with
`(Y, Z, X⟦1⟧; v, w, u⟦1⟧')`, the sign change of the rotation of `(X, Y, Z; u, v, w)`. The
result then follows from the rotation axiom of pretriangulated categories,
`HomotopyCategory.Pretriangulated.rotate_distinguished_triangle`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The triangles `(Y, Z, X⟦1⟧; v, -w, -u⟦1⟧')` and `(Y, Z, X⟦1⟧; v, w, u⟦1⟧')` are isomorphic
via `(𝟙, 𝟙, -𝟙)`. -/
private noncomputable def rotateNegIso (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    Triangle.mk T.mor₂ (-T.mor₃) (-T.mor₁⟦(1 : ℤ)⟧') ≅
      Triangle.mk T.mor₂ T.mor₃ (-(-T.mor₁⟦(1 : ℤ)⟧')) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (-(Iso.refl _))
    (by simp) (by simp) (by simp)

/-- A triangle `(X, Y, Z; u, v, w)` of `K(C)` is admissible if and only if its rotation
`(Y, Z, X⟦1⟧; v, w, -u⟦1⟧')` is admissible. -/
@[weil "lem_fka2_triangle_rotation_homotopy"]
theorem rotate_mem_admissibleTriangles_iff
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ admissibleTriangles C ↔
      Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦(1 : ℤ)⟧') ∈ admissibleTriangles C := by
  rw [mem_admissibleTriangles_iff, mem_admissibleTriangles_iff,
    Pretriangulated.rotate_distinguished_triangle (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃))]
  exact ⟨fun h => Pretriangulated.isomorphic_distinguished _ h _ (rotateNegIso T).symm,
    fun h => Pretriangulated.isomorphic_distinguished _ h _ (rotateNegIso T)⟩

end HomotopyCategory
