module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.ChoiceOfInjectiveResolutions
public import Weil.Attr

/-!
# Injective-resolution functors

Let `C` be an abelian category and let `(I(X), i_X)` be a choice of injective resolutions on the
bounded below derived category `D⁺(C)` (`CochainComplex.ChoiceOfInjectiveResolutions C`), indexed
by the cohomologically bounded below cochain complexes `X`. An *injective-resolution functor* for
this choice is a functor `ρ : D⁺(C) ⥤ K(C)` to the homotopy category with `ρ(X) = I(X)` on
objects, such that for every morphism `φ : X ⟶ Y` of `D⁺(C)` the square
`Q(i_X) ≫ Q(ρ φ) = φ ≫ Q(i_Y)` commutes in the derived category, where `Q : K(C) ⥤ D(C)` is the
localization functor.

## Main definitions

* `DerivedCategory.PlusComplexes C`: the bounded below derived category presented by its
  objects as complexes: the objects are the cohomologically bounded below cochain complexes `K`,
  and the morphisms `K ⟶ L` are the morphisms `Q K ⟶ Q L` of `DerivedCategory C`.
* `DerivedCategory.PlusComplexes.toPlus`: the functor to `DerivedCategory.Plus C`; it is an
  equivalence.
* `CochainComplex.InjectiveResolutionFunctor c`: an injective-resolution functor for a choice
  `c` of injective resolutions.
* `CochainComplex.InjectiveResolutionFunctor.functor`: the underlying functor
  `DerivedCategory.PlusComplexes C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.functor_obj`: `ρ(X) = I(X)`, by definition.
* `CochainComplex.InjectiveResolutionFunctor.comm_functor`: the compatibility square.

## Implementation notes

In Mathlib the objects of `DerivedCategory C` are not literally cochain complexes, so the
condition `ρ(X) = I(X)` has no meaning for a functor defined on `DerivedCategory.Plus C`. The
source category of `ρ` is therefore `DerivedCategory.PlusComplexes C`, whose objects are the
complexes indexing the choice of resolutions; it is equivalent to `DerivedCategory.Plus C`
(`DerivedCategory.PlusComplexes.toPlus`). The object of `PlusComplexes C` given by `K` sits
over `Qh (K)`, the image in `D(C)` of the class of `K` in the homotopy category, so that the
localization functor of the compatibility square is `DerivedCategory.Qh` throughout.

An injective-resolution functor is recorded by its action on morphisms, its object map being
`X ↦ I(X)` on the nose; this makes `ρ(X) = I(X)` a definitional equality rather than an
equality of objects to be transported along.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II,
  p. 296.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The bounded below derived category presented by complexes: the objects are the
cohomologically bounded below cochain complexes `K` (`K.IsGE n` for some `n`), and a morphism
`K ⟶ L` is a morphism `Qh K ⟶ Qh L` of the derived category. -/
abbrev PlusComplexes : Type _ :=
  InducedCategory (DerivedCategory C)
    (fun K : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n} ↦
      Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K.1))

namespace PlusComplexes

variable {C}

lemma plus_Qh_obj (K : PlusComplexes C) :
    TStructure.t.plus (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (K : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)) :=
  TStructure.t.plus.prop_of_iso ((quotientCompQhIso C).app _).symm
    ((CochainComplex.exists_isGE_iff_plus_Q_obj _).1 K.2)

variable (C) in
/-- The functor from the complexes model of the bounded below derived category to
`DerivedCategory.Plus C`. -/
noncomputable def toPlus : PlusComplexes C ⥤ Plus C :=
  TStructure.t.plus.lift (inducedFunctor _) plus_Qh_obj

instance : (toPlus C).Full := by
  dsimp only [toPlus]; infer_instance

instance : (toPlus C).Faithful := by
  dsimp only [toPlus]; infer_instance

instance : (toPlus C).EssSurj where
  mem_essImage X := by
    obtain ⟨n, hn⟩ := X.2
    have : X.obj.IsGE n := hn
    obtain ⟨K, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE X.obj n
    exact ⟨⟨K, n, inferInstance⟩,
      ⟨ObjectProperty.isoMk _ ((quotientCompQhIso C).app K ≪≫ e.symm)⟩⟩

instance : (toPlus C).IsEquivalence where

end PlusComplexes

end DerivedCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open DerivedCategory

/-- An injective-resolution functor for a choice `c` of injective resolutions `(I(X), i_X)` on
the bounded below derived category: a functor `ρ` from `D⁺(C)` (presented by complexes) to the
homotopy category `K(C)` with `ρ(X) = I(X)` on objects, such that
`Q(i_X) ≫ Q(ρ φ) = φ ≫ Q(i_Y)` for every morphism `φ : X ⟶ Y` of `D⁺(C)`. It is recorded by its
action `map` on morphisms; the functor is `InjectiveResolutionFunctor.functor`. -/
@[weil "def_fka2_injective_resolution_functor"]
structure InjectiveResolutionFunctor (c : ChoiceOfInjectiveResolutions C) where
  /-- The action `φ ↦ ρ(φ)` on morphisms. -/
  map {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex
  map_id (X : PlusComplexes C) : map (𝟙 X) = 𝟙 _ := by cat_disch
  map_comp {X Y Z : PlusComplexes C} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    map (φ ≫ ψ) = map φ ≫ map ψ := by cat_disch
  /-- The compatibility `Q(ρ φ) ∘ Q(i_X) = Q(i_Y) ∘ φ`. -/
  comm {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι) ≫ Qh.map (map φ) =
      φ.hom ≫ Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).ι)

namespace InjectiveResolutionFunctor

variable {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)

attribute [simp] map_id map_comp

/-- The functor `ρ : D⁺(C) ⥤ K(C)` of an injective-resolution functor. -/
noncomputable def functor : PlusComplexes C ⥤ HomotopyCategory C (ComplexShape.up ℤ) where
  obj X := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
    (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex
  map := ρ.map
  map_id := ρ.map_id
  map_comp := ρ.map_comp

/-- `ρ(X) = I(X)`. -/
@[simp]
lemma functor_obj (X : PlusComplexes C) :
    ρ.functor.obj X = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex :=
  rfl

@[simp]
lemma functor_map {X Y : PlusComplexes C} (φ : X ⟶ Y) : ρ.functor.map φ = ρ.map φ :=
  rfl

/-- The compatibility square `Q(ρ φ) ∘ Q(i_X) = Q(i_Y) ∘ φ` for the functor `ρ`. -/
@[reassoc]
lemma comm_functor {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι) ≫
        Qh.map (ρ.functor.map φ) =
      φ.hom ≫ Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).ι) :=
  ρ.comm φ

attribute [reassoc] comm

/-- Two injective-resolution functors with the same action on morphisms are equal. -/
@[ext]
lemma ext {ρ ρ' : InjectiveResolutionFunctor c}
    (h : ∀ {X Y : PlusComplexes C} (φ : X ⟶ Y), ρ.map φ = ρ'.map φ) : ρ = ρ' := by
  obtain ⟨m, _, _, _⟩ := ρ
  obtain ⟨m', _, _, _⟩ := ρ'
  have : @m = @m' := by
    funext X Y φ
    exact h φ
  subst this
  rfl

lemma functor_injective {ρ ρ' : InjectiveResolutionFunctor c} (h : ρ.functor = ρ'.functor) :
    ρ = ρ' := by
  ext X Y φ
  exact eq_of_heq (Functor.hcongr_hom h φ)

end InjectiveResolutionFunctor

end CochainComplex
