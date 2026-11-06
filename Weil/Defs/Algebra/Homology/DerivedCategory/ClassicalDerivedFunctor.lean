module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Weil.Defs.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Attr

/-!
# The classical derived functors `R^νF` on the bounded below derived category

Let `F : C ⥤ D` be an additive functor between abelian categories. For `ν : ℤ` the `ν`-th
right derived functor of `F` on the bounded below derived category is
`R^νF = H^ν ∘ RF : D⁺(C) ⥤ D`, the composite of the total right derived functor
`F.rightDerivedFunctorPlus : D⁺(C) ⥤ D⁺(D)` with the `ν`-th cohomology functor.

Given a choice of injective resolutions `(I(X), i_X)` on `D⁺(C)` and an injective-resolution
functor `ρ` for it, the derived functor can be described concretely: `R^νF(X) = H^ν(F(I(X)))`,
and `R^νF(φ) = H^ν(F(r))` for any morphism of complexes `r` representing `ρ(φ)`. This concrete
functor is isomorphic to the choice-free one.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusHomology`: the functor
  `R^νF = RF ⋙ H^ν : D⁺(C) ⥤ D`.
* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerived`: the functor
  `X ↦ H^ν(F(I(X)))` defined by the injective-resolution functor `ρ`.
* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerivedIso`: the isomorphism
  `ρ.classicalRightDerived F ν ≅ toPlus ⋙ F.rightDerivedFunctorPlusHomology ν`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerived_obj`:
  `R^νF(X) = H^ν(F(I(X)))`, by definition.
* `CochainComplex.InjectiveResolutionFunctor.classicalRightDerived_map_eq`:
  `R^νF(φ) = H^ν(F(r))` for every representative `r` of `ρ(φ)`.

## Implementation notes

The functor `R^νF` on `DerivedCategory.Plus C` is defined from the total right derived
functor, which is characterized by a universal property and depends on no choice; the
concrete description through `ρ` is defined on `DerivedCategory.PlusComplexes C`, the bounded
below derived category presented by complexes, which is equivalent to `DerivedCategory.Plus C`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The `ν`-th right derived functor `R^νF = H^ν ∘ RF : D⁺(C) ⥤ D` of an additive functor
`F : C ⥤ D`, where `C` has enough injectives. -/
@[weil "def_fka2_classical_derived_functor"]
noncomputable abbrev rightDerivedFunctorPlusHomology (ν : ℤ) : DerivedCategory.Plus C ⥤ D :=
  F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D ν

end Functor

end CategoryTheory

namespace CochainComplex

namespace InjectiveResolutionFunctor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

omit [HasDerivedCategory C] in
/-- Homotopic morphisms of complexes have the same image under `H^ν ∘ F`. -/
lemma homologyMap_mapHomologicalComplex_eq {K L : CochainComplex C ℤ} (r r' : K ⟶ L)
    (h : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r') (ν : ℤ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) ν =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r') ν :=
  (F.mapHomotopy (HomotopyCategory.homotopyOfEq r r' h)).homologyMap_eq ν

/-- A morphism of complexes `I(X) ⟶ I(Y)` representing `ρ(φ)`, chosen arbitrarily. -/
noncomputable def mapRep {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex :=
  (ρ.map φ).out

@[simp]
lemma quotient_map_mapRep {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (ρ.mapRep φ) = ρ.map φ :=
  HomotopyCategory.quotient_map_out _

/-- The `ν`-th derived functor of `F` defined by the injective-resolution functor `ρ`:
`R^νF(X) = H^ν(F(I(X)))`, and `R^νF(φ) = H^ν(F(r))` for a morphism of complexes `r`
representing `ρ(φ)` (see `classicalRightDerived_map_eq`). -/
@[weil "def_fka2_classical_derived_functor"]
noncomputable def classicalRightDerived (ν : ℤ) : PlusComplexes C ⥤ D where
  obj X := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex).homology ν
  map φ := HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (ρ.mapRep φ)) ν
  map_id X :=
    (homologyMap_mapHomologicalComplex_eq F (ρ.mapRep (𝟙 X)) (𝟙 _)
      (by rw [quotient_map_mapRep, ρ.map_id, CategoryTheory.Functor.map_id]) ν).trans
      (by rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id])
  map_comp φ ψ :=
    (homologyMap_mapHomologicalComplex_eq F (ρ.mapRep (φ ≫ ψ)) (ρ.mapRep φ ≫ ρ.mapRep ψ)
      (by rw [CategoryTheory.Functor.map_comp, quotient_map_mapRep, quotient_map_mapRep,
        quotient_map_mapRep, ρ.map_comp]) ν).trans
      (by rw [CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp])

/-- `R^νF(X) = H^ν(F(I(X)))`. -/
lemma classicalRightDerived_obj (ν : ℤ) (X : PlusComplexes C) :
    (ρ.classicalRightDerived F ν).obj X =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex).homology ν :=
  rfl

/-- `R^νF(φ) = H^ν(F(r))` for every morphism of complexes `r` representing `ρ(φ)`. -/
@[weil "def_fka2_classical_derived_functor"]
lemma classicalRightDerived_map_eq (ν : ℤ) {X Y : PlusComplexes C} (φ : X ⟶ Y)
    (r : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map φ) :
    (ρ.classicalRightDerived F ν).map φ =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) ν :=
  homologyMap_mapHomologicalComplex_eq F _ _ (by rw [quotient_map_mapRep, hr]) ν

/-- The concrete functor `X ↦ H^ν(F(I(X)))` is the homology of `F` applied to `ρ`, computed
on the homotopy category. -/
noncomputable def classicalRightDerivedIsoHomotopyCategory (ν : ℤ) :
    ρ.classicalRightDerived F ν ≅
      ρ.functor ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) ν :=
  NatIso.ofComponents
    (fun X ↦ ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) ν).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)).symm)
    (fun {X Y} φ ↦ by
      have h := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) ν).inv.naturality
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (ρ.mapRep φ))
      dsimp at h ⊢
      rw [← ρ.quotient_map_mapRep φ]
      exact h)

variable [HasDerivedCategory D] [EnoughInjectives C]

/-- The concrete functor `X ↦ H^ν(F(I(X)))` defined by an injective-resolution functor `ρ` is
isomorphic to `R^νF = H^ν ∘ RF`, composed with the equivalence
`toPlus : PlusComplexes C ⥤ D⁺(C)`. -/
@[weil "def_fka2_classical_derived_functor"]
noncomputable def classicalRightDerivedIso (ν : ℤ) :
    ρ.classicalRightDerived F ν ≅
      PlusComplexes.toPlus C ⋙ F.rightDerivedFunctorPlusHomology ν :=
  ρ.classicalRightDerivedIsoHomotopyCategory F ν ≪≫
    Functor.isoWhiskerLeft (ρ.functor ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh D ν).symm ≪≫
    (Functor.isoWhiskerRight (ρ.rightDerivedFunctorIso F)
      (DerivedCategory.homologyFunctor D ν) :)

end InjectiveResolutionFunctor

end CochainComplex
