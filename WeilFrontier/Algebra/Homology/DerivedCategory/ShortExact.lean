module

public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.ShortExact
public import Weil.Attr
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.Basic

/-!
# Uniqueness of the connecting morphism in the derived category

Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes in an abelian
category. The cone-to-quotient map `φ : Cone(X₁ ⟶ X₂) ⟶ X₃` is a quasi-isomorphism, so its
image `Q(φ)` in the derived category is an isomorphism. A connecting morphism `w` of `S`
(`DerivedCategory.IsConnectingMorphism`) is determined by `w ∘ Q(φ)`, hence it is unique, and
`DerivedCategory.triangleOfSESδ` is one.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.existsUnique_isConnectingMorphism`: a short exact
  sequence of cochain complexes has exactly one connecting morphism in the derived category.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated DerivedCategory

universe w v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)}

/-- A short exact sequence of cochain complexes has exactly one connecting morphism in the
derived category, namely `DerivedCategory.triangleOfSESδ`. -/
@[weil "lem_fka2_ses_connecting_morphism_derived_unique"]
theorem existsUnique_isConnectingMorphism (hS : S.ShortExact) :
    ∃! w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧, IsConnectingMorphism S w := by
  refine ⟨triangleOfSESδ hS, descShortComplex_triangleOfSESδ hS, fun w hw => ?_⟩
  have : IsIso (Q.map (CochainComplex.mappingCone.descShortComplex S)) := by
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
    infer_instance
  rw [← cancel_epi (Q.map (CochainComplex.mappingCone.descShortComplex S))]
  exact hw.trans (descShortComplex_triangleOfSESδ hS).symm

end CategoryTheory.ShortComplex.ShortExact

end

/-! ### The triangle of a short exact sequence in the derived category is admissible -/

/-!
# The triangle of a short exact sequence in the derived category is admissible

Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes in an abelian
category `C`, with maps `u : X₁ ⟶ X₂` and `v : X₂ ⟶ X₃`, and let `φ : Cone(u) ⟶ X₃` be the
cone-to-quotient map. A morphism `w : Q(X₃) ⟶ Q(X₁)⟦1⟧` with `w ∘ Q(φ) = Q(π_u)`, where
`π_u : Cone(u) ⟶ X₁⟦1⟧` is the projection `(x, y) ↦ x`, makes `(X₁, X₂, X₃; Q(u), Q(v), w)` an
admissible triangle of the derived category: the triple `(id, id, Q(φ))` is an isomorphism from
the image of the standard triangle `(X₁, X₂, Cone(u); u, ι_u, π_u)` to it.

## Main results

* `DerivedCategory.mk_neg_triangleOfSESδ_mem_admissibleTriangles`: the triangle
  `(Q(u), Q(v), -triangleOfSESδ)` is admissible.
* `DerivedCategory.mk_mem_admissibleTriangles_of_comp_eq_fst`: the triangle `(Q(u), Q(v), w)` is
  admissible for every `w` with `w ∘ Q(φ) = Q(π_u)`.

## Implementation notes

Mathlib's connecting morphism `DerivedCategory.triangleOfSESδ` satisfies
`triangleOfSESδ ∘ Q(φ) = -Q(π_u)`, because the third arrow of Mathlib's cone triangle is
`-π_u`; the morphism `w` with `w ∘ Q(φ) = Q(π_u)` is therefore `-triangleOfSESδ`. Admissible
triangles carry the opposite sign of Mathlib's distinguished triangles
(`DerivedCategory.mem_admissibleTriangles_iff`), so the statement follows from
`DerivedCategory.triangleOfSES_distinguished`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Appendix A II.
-/

/- `DerivedCategory.IsConnectingMorphism` follows Mathlib's sign (it holds for `triangleOfSESδ`);
FK's connecting morphism `w` (`w ∘ Q(φ) = Q(π_u)`) is the `w` with
`IsConnectingMorphism S (-w)` (`isConnectingMorphism_iff_fst`). The theorem below states FK's
condition literally. -/

@[expose] public section

open CategoryTheory Limits Pretriangulated CochainComplex HomComplex

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)}

/-- The triangle `(Q(u), Q(v), -triangleOfSESδ)` of a short exact sequence of cochain complexes
is admissible. -/
lemma mk_neg_triangleOfSESδ_mem_admissibleTriangles (hS : S.ShortExact) :
    Triangle.mk (Q.map S.f) (Q.map S.g) (-triangleOfSESδ hS) ∈ admissibleTriangles C := by
  rw [mem_admissibleTriangles_iff]
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃, neg_neg]
  exact triangleOfSES_distinguished hS

/-- A morphism `w` with `w ∘ Q(φ) = Q(π_u)` is `-triangleOfSESδ`. -/
lemma eq_neg_triangleOfSESδ_of_comp_eq_fst (hS : S.ShortExact)
    {w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧}
    (hw : Q.map (mappingCone.descShortComplex S) ≫ w =
      Q.map (Cocycle.homOf ((mappingCone.fst S.f).rightShift 1 0 (zero_add 1))) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app S.X₁) :
    w = -triangleOfSESδ hS := by
  have h : IsConnectingMorphism S (-w) := by
    rw [isConnectingMorphism_iff_fst, neg_neg]
    exact hw
  rw [← (isConnectingMorphism_iff_eq_triangleOfSESδ hS _).1 h, neg_neg]

/-- **The triangle of a short exact sequence is admissible.** Let `S` be a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes and `w : Q(X₃) ⟶ Q(X₁)⟦1⟧` its connecting
morphism, `w ∘ Q(φ) = Q(π_u)` for the cone-to-quotient map `φ : Cone(X₁ ⟶ X₂) ⟶ X₃` and the
projection `π_u : Cone(X₁ ⟶ X₂) ⟶ X₁⟦1⟧`, `(x, y) ↦ x`. Then `(Q(u), Q(v), w)` is an admissible
triangle of the derived category. -/
@[weil "lem_fka2_ses_gives_triangle_derived"]
theorem mk_mem_admissibleTriangles_of_comp_eq_fst (hS : S.ShortExact)
    (w : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧)
    (hw : Q.map (mappingCone.descShortComplex S) ≫ w =
      Q.map (Cocycle.homOf ((mappingCone.fst S.f).rightShift 1 0 (zero_add 1))) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app S.X₁) :
    Triangle.mk (Q.map S.f) (Q.map S.g) w ∈ admissibleTriangles C := by
  rw [eq_neg_triangleOfSESδ_of_comp_eq_fst hS hw]
  exact mk_neg_triangleOfSESδ_mem_admissibleTriangles hS

end DerivedCategory

end
