module

public import Weil.Algebra.Homology.DerivedCategory.HomologySequence
public import Weil.Algebra.Homology.DerivedCategory.InjectiveResolutionUniqueUpToHomotopy
public import Weil.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Attr

/-!
# The derived functors of an object are computed by any injective resolution

Let `F : C ⥤ D` be an additive functor between abelian categories, `(I(X), i_X)` a choice of
injective resolutions on `D⁺(C)` with an injective-resolution functor `ρ`, and
`R^νF(X) = H^ν(F(I(X)))` the corresponding derived functors. An object `M` of `C` is viewed as
the complex `M[0]` concentrated in degree `0`. If `(J, j)` is an injective resolution of `M[0]`
(for instance a classical one `0 → M → J⁰ → J¹ → ⋯`) and `c : I(M[0]) ⟶ J` is the morphism of
the homotopy category with `c ∘ i_{M[0]} = j`, then `H^ν(F(c)) : R^νF(M[0]) ⟶ H^ν(F(J))` is an
isomorphism for every `ν`: `c` is an isomorphism of the homotopy category (the class of a
homotopy equivalence), hence so are `F(c)` and `H^ν(F(c))`.

## Main definitions

* `DerivedCategory.PlusComplexes.single₀`: the object `M[0]` of the bounded below derived
  category presented by complexes.

## Main results

* `CochainComplex.InjectiveResolutionPlus.isIso_homologyFunctor_map_mapHomotopyCategory_map`:
  `H^ν(F(c))` is an isomorphism, for `c` a morphism of the homotopy category.
* `CochainComplex.InjectiveResolutionFunctor.isIso_homologyMap_mapHomologicalComplex_map`:
  `H^ν(F(r)) : R^νF(M[0]) ⟶ H^ν(F(J))` is an isomorphism for every morphism of complexes `r`
  representing `c`.

## Implementation notes

The statement holds for every injective resolution `J` of `M[0]` in the sense of
`CochainComplex.InjectiveResolutionPlus` (a bounded below complex of injectives with a
quasi-isomorphism from `M[0]`); the classical condition `J^ν = 0` for `ν < 0` is not needed and
is not assumed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4, p. 298.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

namespace PlusComplexes

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The object `M[0]` of the bounded below derived category presented by complexes: the
complex with `M` in degree `0` and `0` elsewhere. -/
noncomputable abbrev single₀ (M : C) : PlusComplexes C :=
  ⟨(HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M, ⟨0, inferInstance⟩⟩

end PlusComplexes

end DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionPlus

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {c : ChoiceOfInjectiveResolutions C} (F : C ⥤ D) [F.Additive]

/-- Let `M` be an object of `C`, `(J, j)` an injective resolution of `M[0]` and
`g : I(M[0]) ⟶ J` the morphism of the homotopy category with `g ∘ i_{M[0]} = j`. Then
`H^ν(F(g)) : H^ν(F(I(M[0]))) ⟶ H^ν(F(J))` is an isomorphism for every `ν`. -/
@[weil "lem_fka2_derived_functor_object_classical"]
theorem isIso_homologyFunctor_map_mapHomotopyCategory_map (M : C)
    (R : InjectiveResolutionPlus ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)
          ⟨0, inferInstance⟩).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex)
    (hg : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ⟨0, inferInstance⟩).ι ≫
          g =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι) (ν : ℤ) :
    IsIso ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) ν).map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g)) := by
  have : IsIso g := InjectiveResolutionPlus.isIso_of_comp_eq _ R g hg
  infer_instance

end InjectiveResolutionPlus

namespace InjectiveResolutionFunctor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

omit [HasDerivedCategory C] in
/-- Let `M` be an object of `C`, `(J, j)` an injective resolution of `M[0]` and `r : I(M[0]) ⟶ J`
a morphism of complexes whose class `c` in the homotopy category satisfies `c ∘ i_{M[0]} = j`.
Then `H^ν(F(r)) : R^νF(M[0]) ⟶ H^ν(F(J))` is an isomorphism for every `ν`. -/
@[weil "lem_fka2_derived_functor_object_classical"]
theorem isIso_homologyMap_mapHomologicalComplex_map (M : C)
    (R : InjectiveResolutionPlus ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))
    (r : (c ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)
        ⟨0, inferInstance⟩).cocomplex ⟶ R.cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((c ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ⟨0, inferInstance⟩).ι ≫
          r) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι) (ν : ℤ) :
    IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) ν :
      (ρ.classicalRightDerived F ν).obj (PlusComplexes.single₀ M) ⟶
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex).homology ν) := by
  have h := InjectiveResolutionPlus.isIso_homologyFunctor_map_mapHomotopyCategory_map (c := c)
    F M R
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r)
    (by rw [← Functor.map_comp, hr]) ν
  have h' : IsIso ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) ν).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r)) := by
    rw [← NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) ν)]
    exact h
  exact h'

end InjectiveResolutionFunctor

end CochainComplex
