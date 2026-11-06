module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilFrontier.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy
public import Weil.Attr
public import WeilFrontier.Algebra.Homology.DerivedCategory.Basic

/-!
# Two out of three for quasi-isomorphisms in a morphism of admissible triangles

Let `A` be an abelian category and `K(A)` the homotopy category of `ℤ`-indexed cochain
complexes in `A`. Let `(f, g, h)` be a morphism of triangles between two admissible triangles
of `K(A)`. If two of `f`, `g`, `h` are quasi-isomorphisms (that is, lie in
`HomotopyCategory.quasiIso A (ComplexShape.up ℤ)`), then so is the third.

## Main results

* `HomotopyCategory.quasiIso_hom₃_of_admissible`: if `f` and `g` are quasi-isomorphisms, so
  is `h`.
* `HomotopyCategory.quasiIso_hom₂_of_admissible`: if `f` and `h` are quasi-isomorphisms, so
  is `g`.
* `HomotopyCategory.quasiIso_hom₁_of_admissible`: if `g` and `h` are quasi-isomorphisms, so
  is `f`.

## Implementation notes

Instead of applying the five lemma to the long exact cohomology sequences directly, the
morphism of triangles is sent by the triangulated functor `DerivedCategory.Qh` to the derived
category, where the image triangles are distinguished; the five lemma for triangulated
categories (`Pretriangulated.isIso₃_of_isIso₁₂` and its variants) then applies, and
`DerivedCategory.isIso_Qh_map_iff` translates back to quasi-isomorphisms. An admissible
triangle `(M, N, R; u, v, w)` corresponds to the distinguished triangle `(M, N, R; u, v, -w)`
(`HomotopyCategory.mem_admissibleTriangles_iff`), and a morphism of triangles is also a
morphism between the triangles with negated third morphisms. A derived category is chosen
inside the proofs (`HasDerivedCategory.standard`), so the statements carry no
`HasDerivedCategory` assumption.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.Pretriangulated.TriangleMorphism

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- A morphism of triangles `T ⟶ T'` induces, with the same components, a morphism between the
triangles obtained by negating the third morphisms. -/
@[simps]
def negMor₃ {T T' : Triangle D} (φ : T ⟶ T') :
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ⟶ Triangle.mk T'.mor₁ T'.mor₂ (-T'.mor₃) where
  hom₁ := φ.hom₁
  hom₂ := φ.hom₂
  hom₃ := φ.hom₃
  comm₁ := φ.comm₁
  comm₂ := φ.comm₂
  comm₃ := by
    simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Preadditive.neg_comp,
      Preadditive.comp_neg, φ.comm₃]

end CategoryTheory.Pretriangulated.TriangleMorphism

namespace HomotopyCategory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The image under `DerivedCategory.Qh` of the triangle obtained from an admissible triangle by
negating its third morphism is distinguished. -/
private lemma Qh_mapTriangle_negMor₃_distinguished [HasDerivedCategory A]
    {T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))} (hT : T ∈ admissibleTriangles A) :
    DerivedCategory.Qh.mapTriangle.obj (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) ∈
      distTriang (DerivedCategory A) :=
  DerivedCategory.Qh.map_distinguished _ ((mem_admissibleTriangles_iff T).1 hT)

variable {T T' : Triangle (HomotopyCategory A (ComplexShape.up ℤ))}

/-- In a morphism `(f, g, h)` of admissible triangles of `K(A)`, if `f` and `g` are
quasi-isomorphisms, so is `h`. -/
@[weil "lem_fka2_qis_two_of_three_triangle"]
theorem quasiIso_hom₃_of_admissible (hT : T ∈ admissibleTriangles A)
    (hT' : T' ∈ admissibleTriangles A) (φ : T ⟶ T')
    (h₁ : quasiIso A (ComplexShape.up ℤ) φ.hom₁) (h₂ : quasiIso A (ComplexShape.up ℤ) φ.hom₂) :
    quasiIso A (ComplexShape.up ℤ) φ.hom₃ := by
  let := HasDerivedCategory.standard A
  rw [← DerivedCategory.isIso_Qh_map_iff] at h₁ h₂ ⊢
  exact isIso₃_of_isIso₁₂ (DerivedCategory.Qh.mapTriangle.map φ.negMor₃)
    (Qh_mapTriangle_negMor₃_distinguished hT) (Qh_mapTriangle_negMor₃_distinguished hT') h₁ h₂

/-- In a morphism `(f, g, h)` of admissible triangles of `K(A)`, if `f` and `h` are
quasi-isomorphisms, so is `g`. -/
@[weil "lem_fka2_qis_two_of_three_triangle"]
theorem quasiIso_hom₂_of_admissible (hT : T ∈ admissibleTriangles A)
    (hT' : T' ∈ admissibleTriangles A) (φ : T ⟶ T')
    (h₁ : quasiIso A (ComplexShape.up ℤ) φ.hom₁) (h₃ : quasiIso A (ComplexShape.up ℤ) φ.hom₃) :
    quasiIso A (ComplexShape.up ℤ) φ.hom₂ := by
  let := HasDerivedCategory.standard A
  rw [← DerivedCategory.isIso_Qh_map_iff] at h₁ h₃ ⊢
  exact isIso₂_of_isIso₁₃ (DerivedCategory.Qh.mapTriangle.map φ.negMor₃)
    (Qh_mapTriangle_negMor₃_distinguished hT) (Qh_mapTriangle_negMor₃_distinguished hT') h₁ h₃

/-- In a morphism `(f, g, h)` of admissible triangles of `K(A)`, if `g` and `h` are
quasi-isomorphisms, so is `f`. -/
@[weil "lem_fka2_qis_two_of_three_triangle"]
theorem quasiIso_hom₁_of_admissible (hT : T ∈ admissibleTriangles A)
    (hT' : T' ∈ admissibleTriangles A) (φ : T ⟶ T')
    (h₂ : quasiIso A (ComplexShape.up ℤ) φ.hom₂) (h₃ : quasiIso A (ComplexShape.up ℤ) φ.hom₃) :
    quasiIso A (ComplexShape.up ℤ) φ.hom₁ := by
  let := HasDerivedCategory.standard A
  rw [← DerivedCategory.isIso_Qh_map_iff] at h₂ h₃ ⊢
  exact isIso₁_of_isIso₂₃ (DerivedCategory.Qh.mapTriangle.map φ.negMor₃)
    (Qh_mapTriangle_negMor₃_distinguished hT) (Qh_mapTriangle_negMor₃_distinguished hT') h₂ h₃

end HomotopyCategory

/-! ### The cohomology functors factor through the derived category -/

/-!
# The cohomology functors factor through the derived category

Let `A` be an abelian category and `n : ℤ`. The `n`-th cohomology functor
`Hⁿ : K(A) ⥤ A` on the homotopy category of cochain complexes sends quasi-isomorphisms to
isomorphisms, so it factors through the localization functor `Qh : K(A) ⥤ D(A)`. The
factorization is `DerivedCategory.homologyFunctor A n`, with the canonical isomorphism
`DerivedCategory.homologyFunctorFactorsh A n : Qh ⋙ homologyFunctor A n ≅ Hⁿ`, and it is unique:
any functor `G' : D(A) ⥤ A` with an isomorphism `e : Qh ⋙ G' ≅ Hⁿ` is isomorphic to
`homologyFunctor A n` by exactly one natural isomorphism compatible with `e` and
`homologyFunctorFactorsh A n`.

## Main results

* `HomotopyCategory.quasiIso_isInvertedBy_homologyFunctor`: `Hⁿ` inverts quasi-isomorphisms.
* `DerivedCategory.existsUnique_iso_homologyFunctor`: uniqueness of the factorization.
* `DerivedCategory.homologyFunctor_factorization`: the statement, existence and uniqueness.

## Implementation notes

A factorization of `G : K(A) ⥤ E` through `D(A)` is a functor `G' : D(A) ⥤ E` with an
isomorphism `Qh ⋙ G' ≅ G` (`CategoryTheory.Localization.Lifting`), not an equality of functors,
and "exactly one" means unique up to a unique compatible isomorphism; see
`DerivedCategory.Qh_universal_property`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

/- FK ask for exactly one strict factorization
`G' ∘ Q = Hⁿ`; for Mathlib's `DerivedCategory` (fixed only up to equivalence) this is stated in
the standard meaning, unique up to unique compatible isomorphism, as for
`DerivedCategory.Qh_universal_property`. -/

@[expose] public section

open CategoryTheory

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Abelian C]

/-- The cohomology functor `Hⁿ : K(A) ⥤ A` sends quasi-isomorphisms to isomorphisms. -/
theorem quasiIso_isInvertedBy_homologyFunctor (n : ℤ) :
    (quasiIso C (ComplexShape.up ℤ)).IsInvertedBy (homologyFunctor C (ComplexShape.up ℤ) n) :=
  fun _ _ f hf => (mem_quasiIso_iff f).1 hf n

end HomotopyCategory

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Any factorization `G'` of `Hⁿ : K(A) ⥤ A` through `D(A)`, with `e : Qh ⋙ G' ≅ Hⁿ`, is
isomorphic to `homologyFunctor C n` by exactly one isomorphism compatible with `e` and
`homologyFunctorFactorsh C n`. -/
theorem existsUnique_iso_homologyFunctor (n : ℤ) {G' : DerivedCategory C ⥤ C}
    (e : Qh ⋙ G' ≅ HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n) :
    ∃! τ : G' ≅ homologyFunctor C n,
      Functor.isoWhiskerLeft Qh τ ≪≫ homologyFunctorFactorsh C n = e :=
  existsUnique_iso_of_lifting_Qh e (homologyFunctorFactorsh C n)

/-- The cohomology functor `Hⁿ : K(A) ⥤ A` has exactly one factorization through the derived
category: it inverts quasi-isomorphisms, `homologyFunctor C n` is a factorization (through
`homologyFunctorFactorsh C n`), and every factorization `(G', e)` is isomorphic to it by a
unique isomorphism compatible with the given ones. -/
@[weil "lem_fka2_cohomology_functor_on_derived"]
theorem homologyFunctor_factorization (n : ℤ) :
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy
        (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n) ∧
      Nonempty (Qh ⋙ homologyFunctor C n ≅
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n) ∧
      ∀ (G' : DerivedCategory C ⥤ C)
        (e : Qh ⋙ G' ≅ HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n),
        ∃! τ : G' ≅ homologyFunctor C n,
          Functor.isoWhiskerLeft Qh τ ≪≫ homologyFunctorFactorsh C n = e :=
  ⟨HomotopyCategory.quasiIso_isInvertedBy_homologyFunctor n, ⟨homologyFunctorFactorsh C n⟩,
    fun _ e => existsUnique_iso_homologyFunctor n e⟩

end DerivedCategory

end
