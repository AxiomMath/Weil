module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import Weil.Algebra.Homology.DerivedCategory.AcyclicObjects
public import Weil.Attr

/-!
# Injective objects are `F`-acyclic

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `RF : D⁺(C) ⥤ D⁺(D)` be its right derived functor. Every injective object
`M` of `C` is `F`-acyclic: the complex `M[0]` is a bounded below complex of injectives, so it
computes `RF`, and `R^ν F(M) = H^ν(F(M)[0]) = 0` for `ν ≠ 0`.

## Main results

* `CategoryTheory.Functor.rightAcyclic_of_injective_of_enoughInjectives`: an injective object is
  right acyclic for `F`, i.e. `F`-acyclic.
* `CategoryTheory.Functor.forall_isZero_rightDerivedPlus_of_injective`: the same in the form of
  vanishing higher derived functors, `R^ν F(M) = 0` for all `ν > 0`.

## Implementation notes

`F`-acyclicity is `CategoryTheory.Functor.rightAcyclic`; for a left exact `F` it is equivalent
to the vanishing of `R^ν F(M)` for `ν > 0`
(`CategoryTheory.Functor.rightAcyclic_iff_forall_isZero_rightDerivedPlus`). Both results hold
for an arbitrary additive `F`, without left exactness.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
* [Stacks, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
-/

public section

open CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **Injective objects are `F`-acyclic.** For an additive functor `F` out of an abelian category
with enough injectives, every injective object `M` is right acyclic for `F`: the complex `M[0]`
computes the right derived functor `RF`. -/
@[weil "lem_fka2_injective_is_f_acyclic"]
theorem rightAcyclic_of_injective_of_enoughInjectives (F : C ⥤ D) [F.Additive] (M : C)
    [Injective M] : F.rightAcyclic M :=
  F.rightAcyclic_of_injective M

/-- For an additive functor `F` out of an abelian category with enough injectives, the higher
right derived functors vanish on an injective object: `R^ν F(M) = 0` for all `ν > 0`. -/
@[weil "lem_fka2_injective_is_f_acyclic"]
theorem forall_isZero_rightDerivedPlus_of_injective (F : C ⥤ D) [F.Additive] (M : C)
    [Injective M] : ∀ ν > 0, IsZero ((F.rightDerivedPlus ν).obj M) :=
  fun ν hν => F.isZero_rightDerivedPlus_obj_injective ν (ne_of_gt hν) M

end CategoryTheory.Functor

end
