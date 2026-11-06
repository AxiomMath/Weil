module

public import Weil.Algebra.Homology.DerivedCategory.KInjective
public import Weil.Defs.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Weil.Attr

/-!
# Comparison morphisms between injective resolutions are isomorphisms

Let `C` be an abelian category, `K` a cochain complex in `C`, and `(I, i)`, `(I', i')` two
injective resolutions of `K`. If `g : I ⟶ I'` is a morphism of the homotopy category `K(C)`
with `g ∘ [i] = [i']`, then `g` is an isomorphism of `K(C)`, i.e. the class of a homotopy
equivalence.

The proof is the classical one: precomposition with the class of a quasi-isomorphism is a
bijection on morphisms into a bounded-below complex of injectives. Surjectivity for `[i']`
gives `g'` with `g' ∘ [i'] = [i]`, and injectivity for `[i]` and `[i']` gives
`g' ∘ g = 𝟙` and `g ∘ g' = 𝟙`.

## Main results

* `CochainComplex.InjectiveResolutionPlus.isIso_of_comp_eq`: a morphism of `K(C)` between two
  injective resolutions of `K` compatible with the resolution maps is an isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II.
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

namespace InjectiveResolutionPlus

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}

/-- Precomposition with the class of the resolution map `[R'.ι]` is a bijection on morphisms
of the homotopy category into the complex of injectives of an injective resolution `R`. -/
lemma bijective_precomp_quotient_map_ι (R' R : InjectiveResolutionPlus K) :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex =>
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι ≫ g) := by
  obtain ⟨d, hd⟩ := R.exists_isStrictlyGE
  exact bijective_precomp_quotient_map_of_quasiIso_of_injective R'.ι R.cocomplex d

/-- Let `R`, `R'` be injective resolutions of `K` and `g` a morphism of the homotopy category
from the complex of injectives of `R` to that of `R'` with `g ∘ [R.ι] = [R'.ι]`. Then `g` is an
isomorphism of the homotopy category (the class of a homotopy equivalence). -/
@[weil "lem_fka2_injective_resolution_comparison_is_iso"]
theorem isIso_of_comp_eq (R R' : InjectiveResolutionPlus K)
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex)
    (hg : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι ≫ g =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι) :
    IsIso g := by
  obtain ⟨g', hg'⟩ := (bijective_precomp_quotient_map_ι R' R).2
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι)
  simp only at hg'
  refine ⟨g', ?_, ?_⟩
  · apply (bijective_precomp_quotient_map_ι R R).1
    simp only [Category.comp_id]
    rw [reassoc_of% hg, hg']
  · apply (bijective_precomp_quotient_map_ι R' R').1
    simp only [Category.comp_id]
    rw [reassoc_of% hg', hg]

end InjectiveResolutionPlus

end CochainComplex

end
