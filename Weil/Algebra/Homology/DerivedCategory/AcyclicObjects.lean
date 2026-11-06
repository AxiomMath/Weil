module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import Weil.Attr
public import StacksFrontier.Homology.CyclesShortComplex

/-!
# `F`-acyclic objects

Let `F : C ⥤ D` be an additive, left exact functor between abelian categories, where `C` has
enough injectives. An object `M` of `C` is *`F`-acyclic* when its higher right derived functors
vanish there: `R^ν F(M[0]) = 0` for all `ν > 0`, where `M[0]` is the complex with `M` in degree
zero and `R^ν F = H^ν ∘ RF` for the right derived functor `RF : D⁺(C) ⥤ D⁺(D)`.

The notion is `CategoryTheory.Functor.rightAcyclic`: the objects `M` such that the complex `M[0]`
computes `RF`, i.e. the canonical map `F(M[0]) ⟶ RF(M[0])` is an isomorphism. For a left exact
`F` the two conditions agree, which is the content of this file.

## Main results

* `CategoryTheory.Functor.rightAcyclic_iff_forall_isZero_rightDerivedPlus`: for a left exact
  additive `F`, `M` is right acyclic for `F` if and only if `R^ν F(M) = 0` for every `ν > 0`.

## Implementation notes

The statement is made with the instance of `HasRightDerivedFunctor` that `EnoughInjectives C`
provides; instance search is pointed at it first, since the general search times out.

The definition of `F`-acyclicity is not restated: the vanishing condition is a property of the
existing notion `CategoryTheory.Functor.rightAcyclic`, which is what downstream results use.
Outside the left exact case the vanishing condition alone does not force `M[0]` to compute `RF`
(the degree zero map `F(M) ⟶ R^0 F(M)` need not be invertible); the source only considers left
exact functors.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
* [Stacks, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

public section

open CategoryTheory.Limits

-- Instance search for the right derived functor otherwise times out; the cheap instance coming
-- from `EnoughInjectives` is tried first, as in StacksFrontier's derived-category files.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **`F`-acyclic objects.** For an additive left exact functor `F` out of an abelian category
with enough injectives, an object `M` is right acyclic for `F` (the complex `M[0]` computes the
right derived functor `RF`) if and only if `R^ν F(M[0]) = 0` for all `ν > 0`. -/
@[weil "def_fka2_f_acyclic_object"]
theorem rightAcyclic_iff_forall_isZero_rightDerivedPlus (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (M : C) :
    F.rightAcyclic M ↔ ∀ ν > 0, IsZero ((F.rightDerivedPlus ν).obj M) :=
  (F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus M).2 inferInstance

end CategoryTheory.Functor

end

/-! ### A left exact functor preserves bounded below acyclic complexes of acyclic objects -/

/-!
# A left exact functor preserves bounded below acyclic complexes of acyclic objects

Let `F : C ⥤ D` be an additive left exact functor between abelian categories, where `C` has
enough injectives. If `Z` is a cochain complex in `C` which is bounded below, acyclic, and all of
whose terms are right acyclic for `F`, then the termwise image `F(Z)` is again acyclic.

Writing `B^n` for the cycles of `Z` in degree `n`, acyclicity splices `Z` into the short exact
sequences `0 ⟶ B^n ⟶ Z^n ⟶ B^{n+1} ⟶ 0`. By induction from the bound, every `B^n` is right
acyclic for `F`, and `F` keeps each of these sequences short exact; a complex spliced from short
exact sequences is acyclic.

## Main results

* `CategoryTheory.Functor.rightAcyclic_cycles_of_acyclic`: the cycles of a bounded below acyclic
  complex of right acyclic objects are right acyclic.
* `CategoryTheory.Functor.acyclic_mapHomologicalComplex_of_rightAcyclic`: `F(Z)` is acyclic.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
* [Stacks, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

public section

open CategoryTheory.Limits

-- Instance search for the right derived functor otherwise times out; the cheap instance coming
-- from `EnoughInjectives` is tried first, as in StacksFrontier's derived-category files.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- The cycles of a bounded below acyclic cochain complex whose terms are right acyclic for a
left exact additive functor `F` are right acyclic for `F`, in every degree. -/
theorem rightAcyclic_cycles_of_acyclic (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (Z : CochainComplex C ℤ) (n₀ : ℤ) [Z.IsStrictlyGE n₀] (hZ : Z.Acyclic)
    (hF : ∀ n, F.rightAcyclic (Z.X n)) (n : ℤ) :
    F.rightAcyclic (Z.cycles n) := by
  have hlow : ∀ j < n₀, F.rightAcyclic (Z.cycles j) := fun j hj ↦ by
    have hzX : IsZero (Z.X j) := Z.isZero_of_isStrictlyGE n₀ j hj
    exact F.rightAcyclic.prop_of_iso (hzX.iso (IsZero.of_mono (Z.iCycles j) hzX)) (hF j)
  have hstep : ∀ k : ℕ, F.rightAcyclic (Z.cycles (n₀ - 1 + (k : ℤ))) := by
    intro k
    induction k with
    | zero => simpa using hlow (n₀ - 1) (by omega)
    | succ k ih =>
      have hrel : (ComplexShape.up ℤ).Rel (n₀ - 1 + (k : ℤ)) (n₀ - 1 + ((k + 1 : ℕ) : ℤ)) := by
        simp only [ComplexShape.up_Rel]; push_cast; ring
      exact ((F.rightAcyclic_and_shortExact_map_of_shortExact _
        (Z.cyclesShortComplex_shortExact hrel (hZ _))).2.1 ih (hF _)).1
  rcases lt_or_ge n n₀ with hn | hn
  · exact hlow n hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = n₀ - 1 + (k : ℤ) := ⟨(n - n₀ + 1).toNat, by omega⟩
    exact hstep k

/-- **A left exact functor preserves bounded below acyclic complexes of acyclic objects.** Let
`F` be an additive left exact functor out of an abelian category with enough injectives, and let
`Z` be a bounded below acyclic cochain complex all of whose terms are right acyclic for `F`. Then
the termwise image `F(Z)` is acyclic. -/
@[weil "lem_fka2_f_preserves_acyclic_of_acyclics"]
theorem acyclic_mapHomologicalComplex_of_rightAcyclic (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (Z : CochainComplex C ℤ) (n₀ : ℤ) [Z.IsStrictlyGE n₀]
    (hZ : Z.Acyclic) (hF : ∀ n, F.rightAcyclic (Z.X n)) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact F Z fun i j hij ↦
    ((F.rightAcyclic_and_shortExact_map_of_shortExact _
      (Z.cyclesShortComplex_shortExact hij (hZ j))).2.1
      (rightAcyclic_cycles_of_acyclic F Z n₀ hZ hF i) (hF i)).2

end CategoryTheory.Functor

end
