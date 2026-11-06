module

public import Weil.Attr
public import StacksFrontier.Algebra.Homology.DerivedCategory.ResolutionFunctor

/-!
# The homotopy category of bounded-below complexes of injectives

For an abelian category `A`, `K⁺(Inj A)` is the full subcategory of the homotopy category
`K(A) = HomotopyCategory A (ComplexShape.up ℤ)` whose objects are the bounded-below cochain
complexes all of whose terms are injective objects of `A`; its morphisms are homotopy classes
of chain maps.

## Main definitions

* `HomotopyCategory.PlusInjective A`: the category `K⁺(Inj A)`, as a full subcategory of `K(A)`.
  It is the full subcategory `KPlusInj A` on the object property `homotopyInjPlus A`.

## Main results

* `HomotopyCategory.homotopyInjPlus_iff`: an object of `K(A)` lies in `K⁺(Inj A)` iff its
  underlying complex is bounded below with injective terms.
* `HomotopyCategory.PlusInjective.ι`: the inclusion `K⁺(Inj A) ⥤ K(A)`, fully faithful.

## Implementation notes

The objects of `K(A)` are cochain complexes, so the full subcategory is cut out by a property
of the underlying complex; it is not closed under isomorphism in `K(A)`. The full subcategory is
triangulated (`instHIPtriangulated`), which gives `PlusInjective A` its pretriangulated
structure. Mathlib's `HomotopyCategory.Plus (InjectiveObject A)`, with the fully faithful
functor `(InjectiveObject.ι A).mapHomotopyCategoryPlus`, is an equivalent category that is not
a full subcategory of `K(A)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopyCategory

variable (A : Type*) [Category A] [Abelian A]

/-- `K⁺(Inj A)`: the full subcategory of `K(A)` whose objects are the bounded-below cochain
complexes of injective objects of `A`. -/
@[weil "def_fka2_bounded_below_injective_homotopy_category"]
abbrev PlusInjective : Type _ := KPlusInj A

variable {A}

/-- An object of `K(A)` lies in `K⁺(Inj A)` iff its underlying cochain complex is bounded below
and has injective terms. -/
theorem homotopyInjPlus_iff (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    homotopyInjPlus A X ↔
      (∃ n : ℤ, CochainComplex.IsStrictlyGE X.as n) ∧ ∀ i, Injective (X.as.X i) :=
  homotopyInjPlus_quotient_obj_iff A X.as

/-- The inclusion functor `K⁺(Inj A) ⥤ K(A)`. -/
abbrev PlusInjective.ι : PlusInjective A ⥤ HomotopyCategory A (ComplexShape.up ℤ) :=
  (homotopyInjPlus A).ι

/-- The inclusion `K⁺(Inj A) ⥤ K(A)` is fully faithful. -/
def PlusInjective.fullyFaithfulι : (PlusInjective.ι (A := A)).FullyFaithful :=
  (homotopyInjPlus A).fullyFaithfulι

instance : (PlusInjective.ι (A := A)).Full := inferInstance

instance : (PlusInjective.ι (A := A)).Faithful := inferInstance

end HomotopyCategory

end
