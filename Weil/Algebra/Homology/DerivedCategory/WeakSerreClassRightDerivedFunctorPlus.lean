module

public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import Weil.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Attr

/-!
# Right derived functors with values in a Serre subcategory

Let `F : A ⥤ B` be an additive functor between abelian categories, `A` with enough injectives,
and let `𝒞` be a full subcategory of `B` containing `0` and closed under isomorphisms, kernels,
cokernels and extensions (a weak Serre class; every Serre class, i.e. a class closed under
subobjects, quotients and extensions, is one). If `X` is an object of `D⁺(A)` such that
`R^q F(H^m(X))` lies in `𝒞` for all `q ≥ 0` and all `m`, then `R^v F(X)` lies in `𝒞` for all
`v ∈ ℤ`.

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlusHomology_obj_mem_of_isWeakSerreClass`: the
  statement above.

## Implementation notes

The hypothesis on the objects `H^m(X)` is stated with Mathlib's `Functor.rightDerived`, the
classical derived functors of `F` on `A`. Left exactness of `F` is not needed. The result is a
special case of the dévissage by the spectral sequence of a Cartan–Eilenberg resolution,
`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`, applied with the
class of all objects of `A` as the source class. The proof by descending induction on the
truncation degree given in the reference is replaced by this spectral sequence argument.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

/-- Let `F : A ⥤ B` be additive, `A` with enough injectives, and `𝒞` a weak Serre class of
objects of `B` (for instance a Serre class). If `X ∈ D⁺(A)` satisfies `R^q F(H^m(X)) ∈ 𝒞` for
all `q ≥ 0` and all `m`, then `R^v F(X) ∈ 𝒞` for all `v`. -/
@[weil "lem_fk108_derived_functor_serre_subcategory"]
theorem rightDerivedFunctorPlusHomology_obj_mem_of_isWeakSerreClass (F : A ⥤ B) [F.Additive]
    (𝒞 : ObjectProperty B) [𝒞.IsWeakSerreClass] (X : DerivedCategory.Plus A)
    (hX : ∀ (q : ℕ) (m : ℤ),
      𝒞 ((F.rightDerived q).obj ((DerivedCategory.Plus.homologyFunctor A m).obj X)))
    (v : ℤ) : 𝒞 ((F.rightDerivedFunctorPlusHomology v).obj X) := by
  let P : ObjectProperty A := fun M => ∀ p : ℕ, 𝒞 ((F.rightDerived p).obj M)
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e hM p => 𝒞.prop_of_iso ((F.rightDerived p).mapIso e) (hM p)⟩
  exact (F.derivedCategoryBPlus_rightDerivedFunctorPlus_obj P 𝒞 (fun _ hM => hM) X
    (fun q p => hX p q)).2 v

end CategoryTheory.Functor

end
