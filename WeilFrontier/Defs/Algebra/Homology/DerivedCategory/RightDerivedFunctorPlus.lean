module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.InjectiveResolutionFunctor
public import Weil.Attr

/-!
# The right derived functor defined by a choice of injective resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, let `(I(X), i_X)` be a choice
of injective resolutions on the bounded below derived category `D⁺(C)` and let `ρ` be an
injective-resolution functor for it. The derived functor (in the sense of Verdier)
`RF : D⁺(C) ⥤ D(D)` for this choice is the composite
`D⁺(C) ⥤ K(C) ⥤ K(D) ⥤ D(D)` of `ρ`, of the functor induced by `F` on homotopy categories and
of the localization functor. Thus `RF(X) = F(I(X))`, and `RF(φ)` is the image of `F(r)` for any
morphism of complexes `r` representing `ρ(φ)`.

We show that this functor is isomorphic to Mathlib's total right derived functor
`F.rightDerivedFunctorPlus : D⁺(C) ⥤ D⁺(D)` (followed by the inclusion `D⁺(D) ⥤ D(D)`), which is
defined by a universal property and does not depend on any choice.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctor`: the derived functor
  `RF : D⁺(C) ⥤ D(D)` of `F` for the injective-resolution functor `ρ`.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorIso`: the isomorphism
  `RF ≅ toPlus ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctor_obj`: `RF(X) = F(I(X))`.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctor_map_eq`:
  `RF(φ) = Q(F(r))` for every representative `r` of `ρ(φ)`.

## Implementation notes

The source category is `DerivedCategory.PlusComplexes C`, the bounded below derived category
presented by complexes, on which `ρ` is defined; it is equivalent to `DerivedCategory.Plus C`
via `DerivedCategory.PlusComplexes.toPlus`. The definition needs neither left exactness of `F`
nor enough injectives (the choice of resolutions is data); the comparison with
`Functor.rightDerivedFunctorPlus` uses enough injectives in `C`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4, p. 297.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

namespace InjectiveResolutionFunctor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

/-- The derived functor (in the sense of Verdier) `RF : D⁺(C) ⥤ D(D)` of an additive functor
`F` for an injective-resolution functor `ρ`: the composite of `ρ : D⁺(C) ⥤ K(C)`, of the functor
`K(C) ⥤ K(D)` induced by `F` and of the localization functor `K(D) ⥤ D(D)`. -/
@[weil "def_fka2_right_derived_functor"]
noncomputable def rightDerivedFunctor : PlusComplexes C ⥤ DerivedCategory D :=
  ρ.functor ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `RF(X) = F(I(X))`. -/
lemma rightDerivedFunctor_obj (X : PlusComplexes C) :
    (ρ.rightDerivedFunctor F).obj X =
      Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)) :=
  rfl

lemma rightDerivedFunctor_map {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    (ρ.rightDerivedFunctor F).map φ =
      Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ.map φ)) :=
  rfl

/-- `RF(φ) = Q(F(r))` for every morphism of complexes `r` representing `ρ(φ)`. -/
lemma rightDerivedFunctor_map_eq {X Y : PlusComplexes C} (φ : X ⟶ Y)
    (r : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map φ) :
    (ρ.rightDerivedFunctor F).map φ =
      Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r)) := by
  rw [rightDerivedFunctor_map, ← hr]
  rfl

/-- The injective-resolution functor `ρ`, with values in the bounded below homotopy category. -/
noncomputable def functorPlus : PlusComplexes C ⥤ HomotopyCategory.Plus C where
  obj X := ⟨ρ.functor.obj X, by
    rw [functor_obj, HomotopyCategory.plus_quotient_obj_iff]
    exact (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).exists_isStrictlyGE⟩
  map φ := ObjectProperty.homMk (ρ.map φ)

lemma functorPlus_comp_ι : ρ.functorPlus ⋙ HomotopyCategory.Plus.ι C = ρ.functor := rfl

instance (X : PlusComplexes C) (n : ℤ) : Injective ((ρ.functorPlus.obj X).obj.as.X n) :=
  inferInstanceAs (Injective
    ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex.X n))

lemma isIso_Qh_map_quotient_map_ι (X : PlusComplexes C) :
    IsIso (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι)) := by
  rw [← Functor.comp_map, NatIso.isIso_map_iff (quotientCompQhIso C), isIso_Q_map_iff_quasiIso]
  infer_instance

/-- The isomorphism `X ≅ ρ(X)` in `D⁺(C)` given by the chosen resolutions `i_X`. -/
noncomputable def toPlusIsoFunctorPlusCompQh :
    PlusComplexes.toPlus C ≅ ρ.functorPlus ⋙ Plus.Qh :=
  NatIso.ofComponents
    (fun X ↦ TStructure.t.plus.fullyFaithfulι.preimageIso
      (@asIso _ _ _ _ (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι))
        (isIso_Qh_map_quotient_map_ι X)))
    (fun {X Y} φ ↦ by
      apply TStructure.t.plus.fullyFaithfulι.map_injective
      exact (ρ.comm φ).symm)

variable [EnoughInjectives C]

instance : IsIso (Functor.whiskerLeft ρ.functorPlus F.rightDerivedFunctorPlusUnit) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp
  infer_instance

/-- The derived functor `RF` of a choice of injective resolutions is isomorphic to Mathlib's
total right derived functor `F.rightDerivedFunctorPlus`, composed with the equivalence
`toPlus : PlusComplexes C ⥤ D⁺(C)` and the inclusion `D⁺(D) ⥤ D(D)`. -/
@[weil "def_fka2_right_derived_functor"]
noncomputable def rightDerivedFunctorIso :
    ρ.rightDerivedFunctor F ≅
      PlusComplexes.toPlus C ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι :=
  (Iso.refl (ρ.functorPlus ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⋙ DerivedCategory.Plus.ι) :) ≪≫
    Functor.isoWhiskerRight
      (asIso (Functor.whiskerLeft ρ.functorPlus F.rightDerivedFunctorPlusUnit))
      DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerRight ρ.toPlusIsoFunctorPlusCompQh.symm
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)

end InjectiveResolutionFunctor

end CochainComplex
