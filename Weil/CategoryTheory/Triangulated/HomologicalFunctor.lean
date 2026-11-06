module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Weil.Attr
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Weil.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy

/-!
# Checking that a functor on the homotopy category is homological on standard triangles

Let `C` be an additive category and `F : K(C) ⥤ B` an additive functor from the homotopy
category of `ℤ`-indexed cochain complexes to an abelian category. If for every morphism of
complexes `φ : X ⟶ Y` the sequence `F(X) ⟶ F(Y) ⟶ F(C(φ))`, given by `F[φ]` and the image of
the inclusion `inr φ : Y ⟶ C(φ)` into the mapping cone, is exact, then `F` is homological:
it carries every distinguished triangle to a sequence exact at its middle term.

The proof transports exactness along an isomorphism of triangles to a standard triangle
`CochainComplex.mappingCone.triangleh φ`, via `CategoryTheory.Functor.IsHomological.mk'`.

## Main results

* `HomotopyCategory.isHomological_of_exact_map_mappingCone_inr`: the criterion above.

## Implementation notes

Freitag–Kiehl call such a functor *cohomological*; this is Mathlib's
`CategoryTheory.Functor.IsHomological` on the pretriangulated category
`HomotopyCategory C (ComplexShape.up ℤ)`. Mathlib's standard triangle has third morphism
`-π`, while Freitag–Kiehl's has `π`; the third morphism does not enter the exactness condition,
so the two notions of admissible triangle give the same notion of cohomological functor.

## References

* [FK88] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace HomotopyCategory

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {B : Type*} [Category B] [Abelian B]

/-- A functor `F` from the homotopy category to an abelian category is homological as soon as,
for every morphism of complexes `φ : X ⟶ Y`, the sequence `F(X) ⟶ F(Y) ⟶ F(C(φ))` given by
`F[φ]` and `F[inr φ]` is exact. -/
@[weil "lem_fka2_cohomological_check_on_standard"]
theorem isHomological_of_exact_map_mappingCone_inr
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ B) [F.Additive]
    (hF : ∀ ⦃X Y : CochainComplex C ℤ⦄ (φ : X ⟶ Y),
      (ShortComplex.mk (F.map ((quotient C _).map φ))
        (F.map ((quotient C _).map (CochainComplex.mappingCone.inr φ)))
        (by
          rw [← F.map_comp]
          exact (congrArg F.map (comp_distTriang_mor_zero₁₂ _
            (mappingCone_triangleh_distinguished φ))).trans (F.map_zero _ _))).Exact) :
    F.IsHomological := by
  refine Functor.IsHomological.mk' F fun T hT => ?_
  obtain ⟨X, Y, φ, ⟨e⟩⟩ := hT
  exact ⟨_, e, hF φ⟩

end HomotopyCategory

/-! ### The long exact cohomology sequence of an admissible triangle -/

/-!
# The long exact cohomology sequence of an admissible triangle

Let `C` be an abelian category and `K(C)` the homotopy category of `ℤ`-indexed cochain
complexes. For an admissible triangle `(X, Y, Z; u, v, w)` in `K(C)` (a triangle isomorphic to
a standard cone triangle `(X, Y, C(u); [u], [ι_u], [π_u])`), the sequence
`⋯ → Hⁿ(X) → Hⁿ(Y) → Hⁿ(Z) → Hⁿ⁺¹(X) → Hⁿ⁺¹(Y) → ⋯`
is exact, where the maps are `Hⁿ(u)`, `Hⁿ(v)` and the composite of
`Hⁿ(w) : Hⁿ(Z) → Hⁿ(X⟦1⟧)` with the canonical identification `Hⁿ(X⟦1⟧) ≅ Hⁿ⁺¹(X)`.

## Main definitions

* `HomotopyCategory.homologyTriangleδ`: the connecting morphism `Hⁿ(Z) → Hⁿ⁺¹(X)`, namely
  `Hⁿ(w)` followed by `Hⁿ(X⟦1⟧) ≅ Hⁿ⁺¹(X)`.

## Main results

* `HomotopyCategory.homologyTriangleδ_eq_homologySequenceδ`: this connecting morphism is the
  connecting morphism of the homological functor `H⁰` with its shift sequence.
* `HomotopyCategory.shiftIso_hom_app_quotient_obj`: on a complex `K`, the identification
  `Hⁿ(K⟦1⟧) ≅ Hⁿ⁺¹(K)` used here is `CochainComplex.homologyShiftIso`.
* `HomotopyCategory.homology_exact₁_of_admissible`,
  `HomotopyCategory.homology_exact₂_of_admissible`,
  `HomotopyCategory.homology_exact₃_of_admissible`: exactness of the sequence at `Hⁿ⁺¹(X)`,
  `Hⁿ(Y)` and `Hⁿ(Z)` respectively.

## Implementation notes

Mathlib's distinguished triangles of `K(C)` have third morphism `-[π_u]`, so an admissible
triangle `(X, Y, Z; u, v, w)` is the distinguished triangle `(X, Y, Z; u, v, -w)` with the third
morphism negated. Its connecting morphism is therefore the negative of the one in Mathlib's
long exact sequence `CategoryTheory.Functor.homologySequence_exact₃`; negating one morphism of
a short complex does not change its exactness.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

universe v u

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The connecting morphism `Hⁿ⁰(Z) → Hⁿ¹(X)` of a triangle `(X, Y, Z; u, v, w)` in `K(C)`,
for `n₀ + 1 = n₁`: the morphism `Hⁿ⁰(w) : Hⁿ⁰(Z) → Hⁿ⁰(X⟦1⟧)` followed by the canonical
identification `Hⁿ⁰(X⟦1⟧) ≅ Hⁿ¹(X)`. -/
noncomputable def homologyTriangleδ (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (ComplexShape.up ℤ) n₀).obj T.obj₃ ⟶
      (homologyFunctor C (ComplexShape.up ℤ) n₁).obj T.obj₁ :=
  (homologyFunctor C (ComplexShape.up ℤ) n₀).map T.mor₃ ≫
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n₀ n₁ (by omega)).hom.app T.obj₁

/-- The connecting morphism `homologyTriangleδ` is Mathlib's connecting morphism of the
homological functor `H⁰` on `K(C)`. -/
lemma homologyTriangleδ_eq_homologySequenceδ
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    homologyTriangleδ T n₀ n₁ h =
      (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ T n₀ n₁ h :=
  rfl

/-- On the image of a cochain complex `K`, the identification `Hⁿ(K⟦i⟧) ≅ Hᵐ(K)` (`n + i = m`)
of the homotopy category is `CochainComplex.homologyShiftIso`, transported along the
identification of homology on `K(C)` with homology of complexes. -/
lemma shiftIso_hom_app_quotient_obj (K : CochainComplex C ℤ) (i n m : ℤ) (h : n + i = m) :
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso i n m (by omega)).hom.app
        ((quotient C (ComplexShape.up ℤ)).obj K) =
      (homologyFunctor C _ n).map (((quotient C _).commShiftIso i).inv.app K) ≫
        (homologyFunctorFactors C _ n).hom.app (K⟦i⟧) ≫
        (CochainComplex.homologyShiftIso i n m h).hom.app K ≫
        (homologyFunctorFactors C _ m).inv.app K :=
  homologyShiftIso_hom_app i n m _ K

variable (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
  (hT : T ∈ admissibleTriangles C)

include hT in
lemma distinguished_mk_neg_mor₃_of_admissible :
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (mem_admissibleTriangles_iff T).1 hT

lemma homologyTriangleδ_neg_eq (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) n₀ n₁ h = -homologyTriangleδ T n₀ n₁ h := by
  rw [homologyTriangleδ_eq_homologySequenceδ]
  simp only [Functor.homologySequenceδ, Functor.shiftMap, Triangle.mk_mor₃, Functor.map_neg,
    Preadditive.neg_comp]
  rfl

include hT in
@[reassoc]
lemma homology_map_mor₁_comp_map_mor₂_of_admissible (n : ℤ) :
    (homologyFunctor C (ComplexShape.up ℤ) n).map T.mor₁ ≫
      (homologyFunctor C (ComplexShape.up ℤ) n).map T.mor₂ = 0 :=
  (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_comp _
    (distinguished_mk_neg_mor₃_of_admissible T hT) n

include hT in
@[reassoc]
lemma homology_map_mor₂_comp_homologyTriangleδ_of_admissible (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (ComplexShape.up ℤ) n₀).map T.mor₂ ≫ homologyTriangleδ T n₀ n₁ h = 0 := by
  have := (homologyFunctor C (ComplexShape.up ℤ) 0).comp_homologySequenceδ _
    (distinguished_mk_neg_mor₃_of_admissible T hT) n₀ n₁ h
  refine neg_eq_zero.1 ?_
  rw [← Preadditive.comp_neg, ← homologyTriangleδ_neg_eq T]
  exact this

include hT in
@[reassoc]
lemma homologyTriangleδ_comp_homology_map_mor₁_of_admissible (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    homologyTriangleδ T n₀ n₁ h ≫ (homologyFunctor C (ComplexShape.up ℤ) n₁).map T.mor₁ = 0 := by
  have := (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ_comp _
    (distinguished_mk_neg_mor₃_of_admissible T hT) n₀ n₁ h
  refine neg_eq_zero.1 ?_
  rw [← Preadditive.neg_comp, ← homologyTriangleδ_neg_eq T]
  exact this

include hT in
/-- For an admissible triangle `(X, Y, Z; u, v, w)` in `K(C)`, the sequence
`Hⁿ(X) → Hⁿ(Y) → Hⁿ(Z)` given by `Hⁿ(u)` and `Hⁿ(v)` is exact. -/
@[weil "lem_fka2_triangle_cohomology_long_exact"]
theorem homology_exact₂_of_admissible (n : ℤ) :
    (ShortComplex.mk _ _ (homology_map_mor₁_comp_map_mor₂_of_admissible T hT n)).Exact :=
  (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₂ _
    (distinguished_mk_neg_mor₃_of_admissible T hT) n

include hT in
/-- For an admissible triangle `(X, Y, Z; u, v, w)` in `K(C)` and `n₀ + 1 = n₁`, the sequence
`Hⁿ⁰(Y) → Hⁿ⁰(Z) → Hⁿ¹(X)` given by `Hⁿ⁰(v)` and `Hⁿ⁰(w)` (followed by
`Hⁿ⁰(X⟦1⟧) ≅ Hⁿ¹(X)`) is exact. -/
@[weil "lem_fka2_triangle_cohomology_long_exact"]
theorem homology_exact₃_of_admissible (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (homology_map_mor₂_comp_homologyTriangleδ_of_admissible T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₃ _
      (distinguished_mk_neg_mor₃_of_admissible T hT) n₀ n₁ h)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (-(Iso.refl _))
    ((id_comp _).trans (comp_id _).symm)
    (by
      simp only [Iso.refl_hom, Preadditive.neg_iso_hom, homologyTriangleδ_neg_eq]
      erw [Preadditive.neg_comp_neg, id_comp, comp_id])

include hT in
/-- For an admissible triangle `(X, Y, Z; u, v, w)` in `K(C)` and `n₀ + 1 = n₁`, the sequence
`Hⁿ⁰(Z) → Hⁿ¹(X) → Hⁿ¹(Y)` given by `Hⁿ⁰(w)` (followed by `Hⁿ⁰(X⟦1⟧) ≅ Hⁿ¹(X)`) and
`Hⁿ¹(u)` is exact. -/
@[weil "lem_fka2_triangle_cohomology_long_exact"]
theorem homology_exact₁_of_admissible (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (homologyTriangleδ_comp_homology_map_mor₁_of_admissible T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₁ _
      (distinguished_mk_neg_mor₃_of_admissible T hT) n₀ n₁ h)
  refine ShortComplex.isoMk (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Preadditive.neg_iso_hom, homologyTriangleδ_neg_eq]
      erw [Preadditive.neg_comp, Preadditive.neg_comp, id_comp, comp_id])
    ((id_comp _).trans (comp_id _).symm)

end HomotopyCategory

end

/-! ### The long exact sequence of a cohomological functor on `K(C)` -/

/-!
# The long exact sequence of a cohomological functor on `K(C)`

Let `C` be a preadditive category with binary biproducts and a zero object, `K(C)` the homotopy
category of `ℤ`-indexed cochain complexes in `C`, `B` an abelian category and
`F : K(C) ⥤ B` a cohomological (in Mathlib: homological) functor. For an admissible triangle
`(X, Y, Z; u, v, w)` of `K(C)` the sequence
`⋯ → F(X⟦i⟧) → F(Y⟦i⟧) → F(Z⟦i⟧) → F(X⟦i+1⟧) → F(Y⟦i+1⟧) → ⋯`,
whose maps are `F(u⟦i⟧)`, `F(v⟦i⟧)` and `F(w⟦i⟧)` (the target `X⟦1⟧⟦i⟧` of `w⟦i⟧` being
identified with `X⟦i+1⟧`), is exact at every term.

A contravariant cohomological functor is a covariant one `K(C) ⥤ Bᵒᵖ`; since `Bᵒᵖ` is abelian,
the statements below apply to it verbatim and give the exactness of the sequence with all
arrows reversed.

## Main definitions

* `HomotopyCategory.shiftMor₃ T i`: the morphism `w⟦i⟧ : Z⟦i⟧ ⟶ X⟦i+1⟧`.

## Main results

* `CategoryTheory.ShortComplex.exact_mk_neg_f_iff`,
  `CategoryTheory.ShortComplex.exact_mk_neg_g_iff`: exactness of
  `P → Q → R` is insensitive to negating either map.
* `HomotopyCategory.mor₁_comp_mor₂_of_admissible` and its companions: consecutive morphisms of
  an admissible triangle compose to zero.
* `HomotopyCategory.exact_map_shift_mor₁_mor₂`: exactness at `F(Y⟦i⟧)`.
* `HomotopyCategory.exact_map_shift_mor₂_mor₃`: exactness at `F(Z⟦i⟧)`.
* `HomotopyCategory.exact_map_shift_mor₃_mor₁`: exactness at `F(X⟦i+1⟧)`.

## Implementation notes

Admissible triangles (`HomotopyCategory.admissibleTriangles`) differ from Mathlib's
distinguished triangles of `K(C)` by the sign of the third morphism. Exactness of a sequence
`P → Q → R` does not change when one of the two maps is negated, so the statements follow from
Mathlib's long exact sequence of a homological functor (`Functor.homologySequence_exact₁`,
`Functor.homologySequence_exact₂`, `Functor.homologySequence_exact₃`) for the tautological shift
sequence `F.shift n = shiftFunctor n ⋙ F`. The identification `X⟦1⟧⟦i⟧ ≅ X⟦i+1⟧` is
`(shiftFunctorAdd' _ 1 i (i + 1) _).inv.app X`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u v' u'

namespace CategoryTheory.ShortComplex

variable {B : Type u'} [Category.{v'} B] [Preadditive B]

/-- Exactness of `P → Q → R` is unchanged when the second morphism is negated. -/
lemma exact_mk_neg_g_iff {P Q R : B} (f : P ⟶ Q) (g : Q ⟶ R) (hfg : f ≫ g = 0) :
    (ShortComplex.mk f (-g) (by simp [hfg])).Exact ↔ (ShortComplex.mk f g hfg).Exact :=
  ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (-Iso.refl _ : R ≅ R).symm
      (by simp) (by simp))

/-- Exactness of `P → Q → R` is unchanged when the first morphism is negated. -/
lemma exact_mk_neg_f_iff {P Q R : B} (f : P ⟶ Q) (g : Q ⟶ R) (hfg : f ≫ g = 0) :
    (ShortComplex.mk (-f) g (by simp [hfg])).Exact ↔ (ShortComplex.mk f g hfg).Exact :=
  ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (-Iso.refl _ : P ≅ P) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp))

end CategoryTheory.ShortComplex

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ B) [F.IsHomological]
  {T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))}

/-- The morphism `w⟦i⟧ : Z⟦i⟧ ⟶ X⟦1⟧⟦i⟧ ≅ X⟦i+1⟧` of the shifted triangle, with its target
identified with `X⟦i+1⟧`. -/
noncomputable abbrev shiftMor₃ (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) (i : ℤ) :
    T.obj₃⟦i⟧ ⟶ T.obj₁⟦i + 1⟧ :=
  T.mor₃⟦i⟧' ≫ (shiftFunctorAdd' _ (1 : ℤ) i (i + 1) (add_comm 1 i)).inv.app T.obj₁

private lemma distinguished_of_admissible (hT : T ∈ admissibleTriangles C) :
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (mem_admissibleTriangles_iff T).1 hT

/-- The connecting morphism of the long exact sequence of the tautological shift sequence of `F`,
for the distinguished triangle `(X, Y, Z; u, v, -w)`, is `-F(w⟦i⟧)`. -/
private lemma homologySequenceδ_tautological (i : ℤ) :
    let _ := Functor.ShiftSequence.tautological F ℤ
    F.homologySequenceδ (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) i (i + 1) rfl =
      -F.map (shiftMor₃ T i) := by
  intro _
  simp only [Functor.homologySequenceδ, Functor.shiftMap]
  change F.map ((-T.mor₃)⟦i⟧') ≫
    (𝟙 _ ≫ F.map ((shiftFunctorAdd' _ (1 : ℤ) i (i + 1) (add_comm 1 i)).inv.app T.obj₁)) = _
  simp [shiftMor₃]

lemma mor₁_comp_mor₂_of_admissible (hT : T ∈ admissibleTriangles C) : T.mor₁ ≫ T.mor₂ = 0 := by
  simpa using comp_distTriang_mor_zero₁₂ _ (distinguished_of_admissible hT)

lemma mor₂_comp_mor₃_of_admissible (hT : T ∈ admissibleTriangles C) : T.mor₂ ≫ T.mor₃ = 0 := by
  simpa using comp_distTriang_mor_zero₂₃ _ (distinguished_of_admissible hT)

lemma mor₃_comp_mor₁_shift_of_admissible (hT : T ∈ admissibleTriangles C) :
    T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
  simpa using comp_distTriang_mor_zero₃₁ _ (distinguished_of_admissible hT)

lemma shiftMor₃_comp_mor₁_shift_of_admissible (hT : T ∈ admissibleTriangles C) (i : ℤ) :
    shiftMor₃ T i ≫ T.mor₁⟦i + 1⟧' = 0 := by
  have h := (shiftFunctorAdd' (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ) i (i + 1)
    (add_comm 1 i)).inv.naturality T.mor₁
  dsimp at h
  rw [shiftMor₃, Category.assoc, ← h, ← Functor.map_comp_assoc,
    mor₃_comp_mor₁_shift_of_admissible hT, Functor.map_zero, zero_comp]

/-- For a cohomological functor `F` and an admissible triangle `(X, Y, Z; u, v, w)` of `K(C)`,
the sequence `F(X⟦i⟧) → F(Y⟦i⟧) → F(Z⟦i⟧)` is exact. -/
@[weil "lem_fka2_cohomological_functor_long_exact"]
theorem exact_map_shift_mor₁_mor₂ (hT : T ∈ admissibleTriangles C) (i : ℤ) :
    (ShortComplex.mk (F.map (T.mor₁⟦i⟧')) (F.map (T.mor₂⟦i⟧'))
      (by rw [← F.map_comp, ← Functor.map_comp, mor₁_comp_mor₂_of_admissible hT,
        Functor.map_zero, F.map_zero])).Exact := by
  let _ := Functor.ShiftSequence.tautological F ℤ
  exact F.homologySequence_exact₂ _ (distinguished_of_admissible hT) i

/-- For a cohomological functor `F` and an admissible triangle `(X, Y, Z; u, v, w)` of `K(C)`,
the sequence `F(Y⟦i⟧) → F(Z⟦i⟧) → F(X⟦i+1⟧)` is exact. -/
@[weil "lem_fka2_cohomological_functor_long_exact"]
theorem exact_map_shift_mor₂_mor₃ (hT : T ∈ admissibleTriangles C) (i : ℤ) :
    (ShortComplex.mk (F.map (T.mor₂⟦i⟧')) (F.map (shiftMor₃ T i))
      (by rw [← F.map_comp, ← Functor.map_comp_assoc, mor₂_comp_mor₃_of_admissible hT,
        Functor.map_zero, zero_comp, F.map_zero])).Exact := by
  let _ := Functor.ShiftSequence.tautological F ℤ
  refine (ShortComplex.exact_mk_neg_g_iff _ _ _).1 ?_
  convert F.homologySequence_exact₃ _ (distinguished_of_admissible hT) i (i + 1) rfl using 2 <;>
    first | rfl | exact heq_of_eq (homologySequenceδ_tautological (T := T) F i).symm

/-- For a cohomological functor `F` and an admissible triangle `(X, Y, Z; u, v, w)` of `K(C)`,
the sequence `F(Z⟦i⟧) → F(X⟦i+1⟧) → F(Y⟦i+1⟧)` is exact. -/
@[weil "lem_fka2_cohomological_functor_long_exact"]
theorem exact_map_shift_mor₃_mor₁ (hT : T ∈ admissibleTriangles C) (i : ℤ) :
    (ShortComplex.mk (F.map (shiftMor₃ T i)) (F.map (T.mor₁⟦i + 1⟧'))
      (by rw [← F.map_comp, shiftMor₃_comp_mor₁_shift_of_admissible hT, F.map_zero])).Exact := by
  let _ := Functor.ShiftSequence.tautological F ℤ
  refine (ShortComplex.exact_mk_neg_f_iff _ _ _).1 ?_
  convert F.homologySequence_exact₁ _ (distinguished_of_admissible hT) i (i + 1) rfl using 2 <;>
    first | rfl | exact heq_of_eq (homologySequenceδ_tautological (T := T) F i).symm

end HomotopyCategory

end
