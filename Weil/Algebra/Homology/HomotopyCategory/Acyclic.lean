module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Weil.Attr
public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy

/-!
# The mapping cone of a quasi-isomorphism is acyclic

Let `φ : K ⟶ L` be a morphism of cochain complexes indexed by `ℤ` in an abelian category.
The mapping cone `CochainComplex.mappingCone φ` is acyclic if and only if `φ` is a
quasi-isomorphism. The direction "quasi-isomorphism implies acyclic cone" is the statement
of [FK, Appendix A II]; the converse holds as well and is recorded alongside it.

The proof goes through the homotopy category: the image of the mapping-cone triangle
`CochainComplex.mappingCone.triangleh φ` is distinguished, quasi-isomorphisms in the homotopy
category are exactly the morphisms whose cone lies in the triangulated subcategory of acyclic
complexes (`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`), and the mapping cone of
`φ` lies there exactly when it is acyclic.

## Main results

* `CochainComplex.mappingCone_acyclic_iff_quasiIso`: `(mappingCone φ).Acyclic ↔ QuasiIso φ`.
* `CochainComplex.mappingCone_acyclic_of_quasiIso`: the mapping cone of a quasi-isomorphism
  is acyclic.

## Implementation notes

The argument uses the long exact cohomology sequence of a distinguished triangle in the form
packaged by Mathlib's triangulated subcategory `HomotopyCategory.subcategoryAcyclic`, rather
than chasing the exact sequence degree by degree.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℤ}

/-- The mapping cone of a morphism of cochain complexes is acyclic if and only if the
morphism is a quasi-isomorphism. -/
theorem mappingCone_acyclic_iff_quasiIso (φ : K ⟶ L) :
    (mappingCone φ).Acyclic ↔ QuasiIso φ := by
  have h := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  refine h.symm.trans ?_
  change (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient _ _).map φ) ↔ _
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  rfl

/-- The mapping cone of a quasi-isomorphism of cochain complexes is acyclic. -/
@[weil "lem_fka2_cone_of_qis_acyclic"]
theorem mappingCone_acyclic_of_quasiIso (φ : K ⟶ L) [QuasiIso φ] :
    (mappingCone φ).Acyclic :=
  (mappingCone_acyclic_iff_quasiIso φ).2 inferInstance

end CochainComplex

end

/-! ### Quasi-isomorphisms in admissible triangles -/

/-!
# Quasi-isomorphisms in admissible triangles

Let `A` be an abelian category and `(X, Y, Z; u, v, w)` an admissible triangle in the homotopy
category `K(A)`. Then `u` is a quasi-isomorphism if and only if `H^n(Z) = 0` for every `n : ℤ`.

## Main results

* `HomotopyCategory.mem_quasiIso_mor₁_iff_of_mem_admissibleTriangles`: for an admissible
  triangle `T` of `K(A)`, the first morphism of `T` is a quasi-isomorphism if and only if all
  the homology objects of the third object of `T` vanish.

## Implementation notes

The statement depends only on the first morphism and the third object of the triangle, so it
is insensitive to the sign of the third morphism. It is deduced from the corresponding
statement for Mathlib's distinguished triangles, through
`HomotopyCategory.mem_admissibleTriangles_iff`, together with
`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an admissible triangle `(X, Y, Z; u, v, w)` of `K(A)`, the morphism `u` is a
quasi-isomorphism if and only if `H^n(Z) = 0` for all `n`. -/
@[weil "lem_fka2_triangle_qis_iff_third_acyclic"]
theorem mem_quasiIso_mor₁_iff_of_mem_admissibleTriangles
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) (hT : T ∈ admissibleTriangles C) :
    quasiIso C (ComplexShape.up ℤ) T.mor₁ ↔
      ∀ n : ℤ, IsZero ((homologyFunctor C (ComplexShape.up ℤ) n).obj T.obj₃) := by
  rw [mem_admissibleTriangles_iff] at hT
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  exact ((subcategoryAcyclic C).trW_iff_of_distinguished _ hT).trans
    (mem_subcategoryAcyclic_iff T.obj₃)

end HomotopyCategory
