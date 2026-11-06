module

public import WeilFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionUniqueUpToHomotopy
public import WeilFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.InjectiveResolutionFunctor
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Attr

/-!
# Naturality of the comparison between the right derived functor and any resolution

Let `F : C ⥤ D` be an additive functor between abelian categories, `ρ` an injective-resolution
functor for a choice `X ↦ (I(X), i_X)` of injective resolutions on `D⁺(C)`, and `RF` the
corresponding right derived functor. Let `φ : X ⟶ Y` be a morphism of `D⁺(C)`, let `(J, j)` and
`(J', j')` be injective resolutions of `X` and `Y`, let `c : I(X) ⟶ J` and `c' : I(Y) ⟶ J'` be
the morphisms of the homotopy category `K(C)` with `c ∘ i_X = j` and `c' ∘ i_Y = j'`, and let
`g : J ⟶ J'` be a morphism of `K(C)` with `Q(g) ∘ Q(j) = Q(j') ∘ φ`. Then the square
`Q(F(c')) ∘ RF(φ) = Q(F(g)) ∘ Q(F(c))` commutes in `D(D)`.

Indeed `ρ(φ) ≫ c'` and `c ≫ g` are morphisms `I(X) ⟶ J'` of `K(C)` with the same image in the
derived category after precomposition with the isomorphism `Q(i_X)`; since `J'` is a bounded
below complex of injectives, hence K-injective, the localization functor is injective on
morphisms into `J'`, so `ρ(φ) ≫ c' = c ≫ g` in `K(C)`. Applying `F` and `Q` gives the square.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.map_comp_eq_comp_of_comparison`: the square
  `ρ(φ) ≫ c' = c ≫ g` in the homotopy category.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctor_map_comp_comparison`: the
  square `RF(φ) ≫ Q(F(c')) = Q(F(c)) ≫ Q(F(g))` in the derived category of `D`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
-/

@[expose] public section

open CategoryTheory DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

omit [HasDerivedCategory D] in
/-- Let `φ : X ⟶ Y` be a morphism of `D⁺(C)`, `(J, j)` and `(J', j')` injective resolutions of
`X` and `Y`, `a : I(X) ⟶ J` and `a' : I(Y) ⟶ J'` the morphisms of `K(C)` with `a ∘ i_X = j`
and `a' ∘ i_Y = j'`, and `g : J ⟶ J'` with `Q(g) ∘ Q(j) = Q(j') ∘ φ`. Then
`a' ∘ ρ(φ) = g ∘ a` in `K(C)`. -/
theorem map_comp_eq_comp_of_comparison {X Y : PlusComplexes C} (φ : X ⟶ Y)
    (R : InjectiveResolutionPlus (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)
    (R' : InjectiveResolutionPlus (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)
    (a : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex)
    (ha : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι ≫ a =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι)
    (a' : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex)
    (ha' : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).ι ≫ a' =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι)
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex)
    (hg : Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι) ≫ Qh.map g =
      φ.hom ≫ Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι)) :
    ρ.map φ ≫ a' = a ≫ g := by
  apply (IsKInjective.Qh_map_bijective _ R'.cocomplex).injective
  have := isIso_Qh_map_quotient_map_ι (c := c) X
  rw [← cancel_epi (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι))]
  simp only [Functor.map_comp]
  rw [ρ.comm_assoc φ, ← Functor.map_comp, ha', ← Category.assoc, ← Functor.map_comp, ha, hg]

/-- Let `φ : X ⟶ Y` be a morphism of `D⁺(C)`, `(J, j)` and `(J', j')` injective resolutions of
`X` and `Y`, `a : I(X) ⟶ J` and `a' : I(Y) ⟶ J'` the morphisms of `K(C)` with `a ∘ i_X = j`
and `a' ∘ i_Y = j'`, and `g : J ⟶ J'` a morphism of `K(C)` with `Q(g) ∘ Q(j) = Q(j') ∘ φ`.
Then `Q(F(a')) ∘ RF(φ) = Q(F(g)) ∘ Q(F(a))` in the derived category of `D`. -/
@[weil "lem_fka2_right_derived_functor_comparison_natural"]
theorem rightDerivedFunctor_map_comp_comparison {X Y : PlusComplexes C} (φ : X ⟶ Y)
    (R : InjectiveResolutionPlus (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)
    (R' : InjectiveResolutionPlus (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)
    (a : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex)
    (ha : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι ≫ a =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι)
    (a' : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex)
    (ha' : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).ι ≫ a' =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι)
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex)
    (hg : Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι) ≫ Qh.map g =
      φ.hom ≫ Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι)) :
    (ρ.rightDerivedFunctor F).map φ ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map a') =
      Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map a) ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g) := by
  have h := congrArg (fun f ↦ Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map f))
    (ρ.map_comp_eq_comp_of_comparison φ R R' a ha a' ha' g hg)
  simp only [Functor.map_comp] at h
  rw [rightDerivedFunctor_map]
  exact h

end InjectiveResolutionFunctor

end CochainComplex
