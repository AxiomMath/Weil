module

public import WeilFrontier.Algebra.Homology.DerivedCategory.KInjective
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Weil.Attr

/-!
# Uniqueness of injective resolutions up to homotopy

Let `C` be an abelian category and let `(I, i)` and `(I', i')` be two injective resolutions of a
cochain complex `X`. Then there is exactly one morphism `g : I ⟶ I'` in the homotopy category
`K(C)` such that `g ∘ i = i'` in `K(C)`.

Since `i` is a quasi-isomorphism and `I'` is a bounded below complex of injective objects
(hence K-injective), precomposition with `i` is a bijection
`Hom_{K(C)}(I, I') → Hom_{K(C)}(X, I')`, and `g` is the preimage of `i'`.

## Main results

* `CochainComplex.InjectiveResolutionPlus.existsUnique_homotopyCategory_hom_comp_eq`: the unique
  morphism in `K(C)` between two injective resolutions compatible with the resolution maps.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II.
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

namespace InjectiveResolutionPlus

variable {C : Type*} [Category* C] [Abelian C] {X : CochainComplex C ℤ}

/-- Let `(I, i)` and `(I', i')` be injective resolutions of a cochain complex `X`. Then there is
exactly one morphism `g : I ⟶ I'` in the homotopy category with `[i] ≫ g = [i']`. -/
@[weil "lem_fka2_injective_resolution_unique_up_to_homotopy"]
theorem existsUnique_homotopyCategory_hom_comp_eq (R R' : InjectiveResolutionPlus X) :
    ∃! g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex,
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι ≫ g =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι := by
  obtain ⟨d, _⟩ := R'.exists_isStrictlyGE
  exact (bijective_precomp_quotient_map_of_quasiIso_of_injective R.ι R'.cocomplex d).existsUnique
    _

end InjectiveResolutionPlus

end CochainComplex

end
