module

public import Weil.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Algebra.Homology.DerivedCategory.RightDerivedFunctorExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Weil.Attr

/-!
# The long exact sequence of the classical derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, let `(I(X), i_X)` be a choice
of injective resolutions on the bounded below derived category `D⁺(C)`, `ρ` an
injective-resolution functor for it, `RF` the associated derived functor and
`R^νF(X) = H^ν(F(I(X)))` the classical derived functors. Let `(X, Y, Z; u, v, w)` be an
admissible triangle of `D(C)` with vertices in `D⁺(C)`, and let `c^T_X : I(X[1]) ⟶ I(X)[1]` be
the morphism of the homotopy category with `c^T_X ∘ i_{X[1]} = i_X[1]`. Then the sequence
`⋯ ⟶ R^νF(X) ⟶ R^νF(Y) ⟶ R^νF(Z) ⟶ R^{ν+1}F(X) ⟶ R^{ν+1}F(Y) ⟶ ⋯`
is exact, where the first two maps are `R^νF(u)`, `R^νF(v)` and the connecting map is
`H^ν(F(c^T_X) ∘ RF(w))`, followed by `H^ν(T(RF X)) = H^{ν+1}(RF X)`.

The proof: the triangle `(RF X, RF Y, RF Z; RF u, RF v, F(c^T_X) ∘ RF w)` of `D(D)` is
admissible, so its cohomology sequence is exact, and the canonical isomorphisms
`H^ν(RF X) ≅ H^ν(F(I(X)))` identify this sequence with the displayed one.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.rightDerivedδ`: the connecting map
  `R^νF(Z) ⟶ R^{ν+1}F(X)`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerived_exact₂`: exactness at
  `R^νF(Y)`.
* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerived_exact₃`: exactness at
  `R^νF(Z)`.
* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerived_exact₁`: exactness at
  `R^{ν+1}F(X)`.

## Implementation notes

An admissible triangle `(M, N, R; f, g, h)` of `D(D)` corresponds to the distinguished
triangle `(M, N, R; f, g, -h)` in Mathlib's convention, whose connecting map is the negative of
the one above; negating a map does not change exactness.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- The shift map of the homology functors commutes with negation. -/
lemma homologyFunctor_shiftMap_neg {K L : DerivedCategory D} (f : K ⟶ L⟦(1 : ℤ)⟧)
    (a a' : ℤ) (h : 1 + a = a') :
    (homologyFunctor D 0).shiftMap (-f) a a' h = -(homologyFunctor D 0).shiftMap f a a' h := by
  have : ((homologyFunctor D 0).shift a).Additive := by
    rw [shift_homologyFunctor]; infer_instance
  simp only [Functor.shiftMap, Functor.map_neg, Preadditive.neg_comp]

end DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

/-- The connecting map `R^νF(Z) ⟶ R^{ν'}F(X)`, for `ν + 1 = ν'`, attached to
`w : Z ⟶ X[1]` and `c^T_X : I(X[1]) ⟶ I(X)[1]`: the map `H^ν(F(c^T_X) ∘ RF(w))` followed by
`H^ν(T(RF X)) = H^{ν'}(RF X)`, through the identifications `H^ν(RF X) ≅ R^νF(X)`. -/
noncomputable def rightDerivedδ {X Z : PlusComplexes C} (w : Z ⟶ X.shiftObj 1)
    (cT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          (X.shiftObj 1 : PlusComplexes C).2).cocomplex ⟶
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)⟦(1 : ℤ)⟧)
    (ν ν' : ℤ) (h : ν + 1 = ν') :
    (ρ.classicalRightDerived F ν).obj Z ⟶ (ρ.classicalRightDerived F ν').obj X :=
  ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Z).inv ≫
    (homologyFunctor D 0).shiftMap ((ρ.rightDerivedFunctor F).map w ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map cT) ≫
        ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh).commShiftIso (1 : ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex))
      ν ν' (by rw [add_comm 1, h]) ≫
    ((ρ.rightDerivedFunctorCompHomologyIso F ν').app X).hom

/-- The connecting map `rightDerivedδ` is the negative of the connecting map of the homology
sequence of the distinguished triangle `(RF X, RF Y, RF Z; RF u, RF v, -(F(c^T_X) ∘ RF w))`,
through the identifications `H^ν(RF X) ≅ R^νF(X)`. -/
lemma rightDerivedδ_eq_neg {X Y Z : PlusComplexes C} (u : X ⟶ Y) (v : Y ⟶ Z)
    (w : Z ⟶ X.shiftObj 1)
    (cT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          (X.shiftObj 1 : PlusComplexes C).2).cocomplex ⟶
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)⟦(1 : ℤ)⟧)
    (ν ν' : ℤ) (h : ν + 1 = ν') :
    ρ.rightDerivedδ F w cT ν ν' h =
      -(((ρ.rightDerivedFunctorCompHomologyIso F ν).app Z).inv ≫
        HomologySequence.δ (Triangle.mk ((ρ.rightDerivedFunctor F).map u)
          ((ρ.rightDerivedFunctor F).map v)
          (-((ρ.rightDerivedFunctor F).map w ≫
            Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map cT) ≫
            ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh).commShiftIso (1 : ℤ)).hom.app
              ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
                (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex))))
          ν ν' h ≫
        ((ρ.rightDerivedFunctorCompHomologyIso F ν').app X).hom) := by
  rw [rightDerivedδ, HomologySequence.δ]
  erw [homologyFunctor_shiftMap_neg]
  erw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  rfl

/-- An isomorphism negated is an isomorphism. -/
private noncomputable def negIso {A : Type*} [Category* A] [Preadditive A] {P Q : A}
    (e : P ≅ Q) : P ≅ Q where
  hom := -e.hom
  inv := -e.inv

section

variable {X Y Z : PlusComplexes C} {u : X ⟶ Y} {v : Y ⟶ Z} {w : Z ⟶ X.shiftObj 1}
  (hT : Triangle.mk u.hom v.hom (w.hom ≫
      Qh.map (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
        (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ≫
      (Qh.commShiftIso (1 : ℤ)).hom.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)) ∈ admissibleTriangles C)
  {cT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
        (X.shiftObj 1 : PlusComplexes C).2).cocomplex ⟶
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)⟦(1 : ℤ)⟧}
  (hcT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
        (X.shiftObj 1 : PlusComplexes C).2).ι ≫ cT =
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
        (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι)⟦(1 : ℤ)⟧')

include hT hcT

/-- The image triangle of `D(D)`, with the third morphism negated, is distinguished. -/
lemma rightDerived_negTriangle_distinguished :
    Triangle.mk ((ρ.rightDerivedFunctor F).map u) ((ρ.rightDerivedFunctor F).map v)
      (-((ρ.rightDerivedFunctor F).map w ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map cT) ≫
        ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh).commShiftIso (1 : ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex))) ∈
      distTriang (DerivedCategory D) :=
  (mem_admissibleTriangles_iff _).1
    (ρ.rightDerivedFunctor_triangle_mem_admissibleTriangles F u v w hT cT hcT)

/-- `R^νF(v) ∘ R^νF(u) = 0`. -/
@[reassoc]
lemma classicalRightDerived_map_comp_map (ν : ℤ) :
    (ρ.classicalRightDerived F ν).map u ≫ (ρ.classicalRightDerived F ν).map v = 0 := by
  have h := comp_distTriang_mor_zero₁₂ _ (ρ.rightDerived_negTriangle_distinguished F hT hcT)
  rw [← NatIso.naturality_1 (ρ.rightDerivedFunctorCompHomologyIso F ν) u,
    ← NatIso.naturality_1 (ρ.rightDerivedFunctorCompHomologyIso F ν) v]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  dsimp only [Triangle.mk] at h
  simp [h]

/-- `δ ∘ R^νF(v) = 0`. -/
@[reassoc]
lemma classicalRightDerived_map_comp_rightDerivedδ (ν ν' : ℤ) (h : ν + 1 = ν') :
    (ρ.classicalRightDerived F ν).map v ≫ ρ.rightDerivedδ F w cT ν ν' h = 0 := by
  have h' := HomologySequence.comp_δ _ (ρ.rightDerived_negTriangle_distinguished F hT hcT) ν ν' h
  rw [ρ.rightDerivedδ_eq_neg F u v w cT, ← NatIso.naturality_1
    (ρ.rightDerivedFunctorCompHomologyIso F ν) v]
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc,
    Preadditive.comp_neg, neg_eq_zero, Functor.comp_map]
  erw [reassoc_of% h']
  simp

/-- `R^{ν'}F(u) ∘ δ = 0`. -/
@[reassoc]
lemma rightDerivedδ_comp_classicalRightDerived_map (ν ν' : ℤ) (h : ν + 1 = ν') :
    ρ.rightDerivedδ F w cT ν ν' h ≫ (ρ.classicalRightDerived F ν').map u = 0 := by
  have h' := HomologySequence.δ_comp _ (ρ.rightDerived_negTriangle_distinguished F hT hcT) ν ν' h
  rw [ρ.rightDerivedδ_eq_neg F u v w cT, ← NatIso.naturality_1
    (ρ.rightDerivedFunctorCompHomologyIso F ν') u]
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc,
    Preadditive.neg_comp, neg_eq_zero, Functor.comp_map]
  erw [reassoc_of% h']
  simp

/-- Exactness of `R^νF(X) ⟶ R^νF(Y) ⟶ R^νF(Z)` for an admissible triangle
`(X, Y, Z; u, v, w)` of `D(C)` with vertices in `D⁺(C)`. -/
@[weil "lem_fka2_derived_functors_long_exact"]
theorem classicalRightDerived_exact₂ (ν : ℤ) :
    (ShortComplex.mk _ _ (ρ.classicalRightDerived_map_comp_map F hT hcT ν)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (HomologySequence.exact₂ _ (ρ.rightDerived_negTriangle_distinguished F hT hcT) ν)
  exact ShortComplex.isoMk ((ρ.rightDerivedFunctorCompHomologyIso F ν).app X)
    ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Y)
    ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Z)
    ((ρ.rightDerivedFunctorCompHomologyIso F ν).hom.naturality u).symm
    ((ρ.rightDerivedFunctorCompHomologyIso F ν).hom.naturality v).symm

/-- Exactness of `R^νF(Y) ⟶ R^νF(Z) ⟶ R^{ν'}F(X)`, for `ν + 1 = ν'`, the second map being
the connecting map `rightDerivedδ`. -/
@[weil "lem_fka2_derived_functors_long_exact"]
theorem classicalRightDerived_exact₃ (ν ν' : ℤ) (h : ν + 1 = ν') :
    (ShortComplex.mk _ _
      (ρ.classicalRightDerived_map_comp_rightDerivedδ F hT hcT ν ν' h)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (HomologySequence.exact₃ _ (ρ.rightDerived_negTriangle_distinguished F hT hcT) ν ν' h)
  refine ShortComplex.isoMk ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Y)
    ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Z)
    (negIso ((ρ.rightDerivedFunctorCompHomologyIso F ν').app X))
    ((ρ.rightDerivedFunctorCompHomologyIso F ν).hom.naturality v).symm ?_
  dsimp only [negIso]
  rw [ρ.rightDerivedδ_eq_neg F u v w cT]
  simp only [Iso.app_hom, Iso.app_inv, Preadditive.comp_neg, Iso.hom_inv_id_app_assoc]

/-- Exactness of `R^νF(Z) ⟶ R^{ν'}F(X) ⟶ R^{ν'}F(Y)`, for `ν + 1 = ν'`, the first map being
the connecting map `rightDerivedδ`. -/
@[weil "lem_fka2_derived_functors_long_exact"]
theorem classicalRightDerived_exact₁ (ν ν' : ℤ) (h : ν + 1 = ν') :
    (ShortComplex.mk _ _
      (ρ.rightDerivedδ_comp_classicalRightDerived_map F hT hcT ν ν' h)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (HomologySequence.exact₁ _ (ρ.rightDerived_negTriangle_distinguished F hT hcT) ν ν' h)
  refine ShortComplex.isoMk (negIso ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Z))
    ((ρ.rightDerivedFunctorCompHomologyIso F ν').app X)
    ((ρ.rightDerivedFunctorCompHomologyIso F ν').app Y) ?_
    ((ρ.rightDerivedFunctorCompHomologyIso F ν').hom.naturality u).symm
  dsimp only [negIso]
  rw [ρ.rightDerivedδ_eq_neg F u v w cT]
  simp only [Iso.app_hom, Iso.app_inv, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg,
    Iso.hom_inv_id_app_assoc]

end

end InjectiveResolutionFunctor

end CochainComplex
