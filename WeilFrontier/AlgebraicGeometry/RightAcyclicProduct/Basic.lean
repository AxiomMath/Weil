module

public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import WeilFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import Weil.Attr

/-!
# A direct sum of `F`-acyclic objects is `F`-acyclic

Let `F : C ⥤ D` be an additive, left exact functor between abelian categories, where `C` has
enough injectives. If `M` and `N` are `F`-acyclic, that is `R^ν F(M) = 0` and `R^ν F(N) = 0` for
all `ν > 0`, then so is the direct sum `M ⊞ N`.

## Main results

* `CategoryTheory.Functor.isZero_rightDerivedPlus_biprod`: if `R^ν F` vanishes on `M` and on `N`
  for all `ν > 0`, it vanishes on `M ⊞ N` for all `ν > 0`.

## Implementation notes

The argument is that of the source: the split short exact sequence `0 → M → M ⊞ N → N → 0` has
`F`-acyclic outer terms, hence an `F`-acyclic middle term. It is
`Stacks.RightAcyclicProduct.rightAcyclic_biprod` ([Stacks, Tag 015D]), stated there for right
acyclicity in the sense of `CategoryTheory.Functor.rightAcyclic`; for a left exact `F` this is the
vanishing condition, by `CategoryTheory.Functor.rightAcyclic_iff_forall_isZero_rightDerivedPlus`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
* [Stacks, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

public section

open CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **A direct sum of `F`-acyclic objects is `F`-acyclic.** For an additive left exact functor
`F` out of an abelian category with enough injectives, if `R^ν F(M) = 0` and `R^ν F(N) = 0` for
all `ν > 0`, then `R^ν F(M ⊞ N) = 0` for all `ν > 0`. -/
@[weil "lem_fka2_f_acyclic_direct_sum"]
theorem isZero_rightDerivedPlus_biprod (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {M N : C} (hM : ∀ ν > 0, IsZero ((F.rightDerivedPlus ν).obj M))
    (hN : ∀ ν > 0, IsZero ((F.rightDerivedPlus ν).obj N)) :
    ∀ ν > 0, IsZero ((F.rightDerivedPlus ν).obj (M ⊞ N)) :=
  (F.rightAcyclic_iff_forall_isZero_rightDerivedPlus _).1
    (Stacks.RightAcyclicProduct.rightAcyclic_biprod F
      ((F.rightAcyclic_iff_forall_isZero_rightDerivedPlus M).2 hM)
      ((F.rightAcyclic_iff_forall_isZero_rightDerivedPlus N).2 hN))

end CategoryTheory.Functor

end
